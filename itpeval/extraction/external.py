"""Collect a locked external extractor's version-one JSONL records."""

import json
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic

from itpeval.core.types import logical_path
from itpeval.corpus.storage import digest, encode, project_file

SCHEMA_VERSION = 1
_MAX_EVENT_BYTES = 8 * 1024 * 1024
_DECLARATION_FIELDS = {"type", "source_path", "name", "kind", "statement", "start_byte", "end_byte", "visible"}
_PROOF_FIELDS = {"proof_manifest", "proof_sha256", "proof_used"}


def _unique_fields(pairs):
    result = dict(pairs)
    if len(result) != len(pairs):
        raise ValueError("duplicate field in external extraction event")
    return result


def _events(path):
    with path.open("rb") as stream:
        while raw := stream.readline(_MAX_EVENT_BYTES + 1):
            if len(raw) > _MAX_EVENT_BYTES:
                raise ValueError("external extraction event exceeds 8 MiB")
            try:
                event = json.loads(raw.decode("utf-8"), object_pairs_hook=_unique_fields)
            except (json.JSONDecodeError, RecursionError) as exc:
                raise ValueError("invalid JSON in external extraction event") from exc
            if not isinstance(event, dict):
                raise ValueError("external extraction events must be objects")
            yield event


def _references(raw, declarations):
    if not isinstance(raw, list):
        raise ValueError("external extraction references must be a list")
    references = {}
    for ref in raw:
        if not isinstance(ref, list) or len(ref) != 2 or not all(isinstance(value, str) for value in ref):
            raise ValueError("external extraction references must name a source and declaration")
        key = tuple(ref)
        if key in references or key not in declarations:
            raise ValueError(f"duplicate or unknown preceding declaration {key!r}")
        references[key] = declarations[key]
    return references


def _verify_declaration(ctx, event, used, deadline):
    from itpeval.backends.external import detached_target
    from itpeval.backends.projects import build_task
    from itpeval.verification import candidate_from_bytes, verify
    from itpeval.verification.external import DetachedProofReceipt

    manifest = logical_path(event["proof_manifest"])
    target = detached_target(ctx.prepared, manifest)
    if ((event["source_path"], event["name"], event["statement"]) != (target.source_path, target.name, target.statement)
            or not event["start_byte"] <= target.start_byte < target.end_byte <= event["end_byte"]):
        raise ValueError("external extraction declaration does not match its reviewed proof target")
    task = build_task(ctx.prepared, manifest)
    proof = project_file(ctx.prepared.project, task.artifact.entrypoint).read_bytes()
    proof_digest = digest(proof)
    if (proof_digest != event["proof_sha256"]
            or project_file(ctx.root, task.artifact.entrypoint).read_bytes() != proof):
        raise ValueError("external extraction proof differs from the lock")
    remaining = deadline - monotonic()
    if remaining <= 0:
        raise ValueError("external extraction exhausted its verification time budget")
    limited = replace(task, budgets=replace(task.budgets, timeout_s=min(task.budgets.timeout_s, remaining)))
    checked = verify(limited, candidate_from_bytes(limited, proof), prepared=ctx.prepared)
    if (checked.task_success is not True or checked.target_preservation != "preserved"
            or checked.completion_status != "proved"):
        raise ValueError(f"external extraction proof check failed for {target.name!r}: "
                         f"{checked.execution_outcome}/{checked.checker_outcome}")
    receipt = DetachedProofReceipt.from_dict(json.loads(checked.stdout))
    used_names = [name for _, name in used]
    if sorted(used_names) != sorted(receipt.assumptions):
        raise ValueError(f"external extraction proof references differ from the checker receipt for {target.name!r}")
    # Use the reviewed identity and exact artifact hashes so a fresh extraction
    # produces the same evidence even when process timing and diagnostics differ.
    return ctx.evidence(encode({"task_id": task.task_id, "environment_id": checked.environment_id,
                               "artifact_id": checked.artifact_id, "source_sha256": target.source_sha256,
                               "statement_sha256": target.statement_sha256, "proof_sha256": proof_digest,
                               "checker_outcome": checked.checker_outcome,
                               "completion_status": checked.completion_status, "obligations": checked.obligations,
                               "assumptions": receipt.assumptions}))


def _collect(ctx, entrypoint, events, deadline):
    header = next(events, {})
    if header != {"schema_version": SCHEMA_VERSION} or type(header["schema_version"]) is not int:
        raise ValueError("unsupported external extraction event version")
    sources = {}
    declarations = {}
    for event in events:
        if event.get("type") == "source":
            if set(event) != {"type", "path", "sha256"} or not isinstance(event["path"], str):
                raise ValueError("invalid external extraction source event")
            path = logical_path(event["path"])
            if path in sources:
                raise ValueError(f"duplicate external extraction source {path!r}")
            raw = ctx.source(path)
            if ctx.sources[path] != event["sha256"] or project_file(ctx.root, path).read_bytes() != raw:
                raise ValueError(f"external extraction source differs from the lock: {path!r}")
            sources[path] = raw
            ctx.notes["succeeded"].append(path)
            continue
        extra = set(event) - _DECLARATION_FIELDS
        if (event.get("type") != "declaration" or _DECLARATION_FIELDS - event.keys()
                or extra and extra != _PROOF_FIELDS):
            raise ValueError("invalid external extraction declaration event")

        path, name, kind, statement = (event[field] for field in ("source_path", "name", "kind", "statement"))
        if any(not isinstance(value, str) or not value.strip() for value in (path, name, kind, statement)):
            raise ValueError("external extraction declarations require a source, name, kind and statement")
        if path not in sources or (path, name) in declarations:
            raise ValueError(f"unknown source or duplicate external declaration {path!r}/{name!r}")
        start, end = event["start_byte"], event["end_byte"]
        if type(start) is not int or type(end) is not int or not 0 <= start < end <= len(sources[path]):
            raise ValueError(f"invalid external extraction source range for {name!r}")
        visible = _references(event["visible"], declarations)
        evidence = ()
        used = {}
        status = "hypothesis" if kind == "hypothesis" else "unverified"
        if extra:
            if not isinstance(event["proof_manifest"], str):
                raise ValueError("external extraction proof_manifest must name a reviewed task manifest")
            used = _references(event["proof_used"], declarations)
            if used.keys() - visible.keys():
                raise ValueError(f"proof references outside the visible context for {name!r}")
            used_names = {target_name for _, target_name in used}
            if sum(target_name in used_names for _, target_name in visible) != len(used_names):
                raise ValueError(f"ambiguous checker assumption names for {name!r}")
            evidence = (_verify_declaration(ctx, event, used, deadline),)
            status = "proof_verified"
            ctx.availability["proof_used_premises"] = "observed"
        context = ctx.context(path, visible=visible.values())
        declaration = ctx.declare(path, name, kind, statement, start, end, context, status, evidence=evidence)
        declarations[path, name] = declaration
        for (_, target_name), target_id in used.items():
            ctx.edge(declaration, "proof_used_premise", target_name, target_id)

    if entrypoint not in sources:
        raise ValueError("external extractor omitted the requested source")
    for field in ("names", "kinds", "source_mapping", "statements", "context"):
        ctx.availability[field] = "observed"


def extract(ctx, entrypoint):
    adapter = ctx.prepared.adapter
    deadline = monotonic() + ctx.timeout_s
    with TemporaryDirectory(dir=ctx.root.parent) as temporary:
        work = Path(temporary)
        output, home, scratch = work / "events.jsonl", work / "home", work / "tmp"
        home.mkdir()
        scratch.mkdir()
        ctx.run(adapter.command(adapter.extractor, "--entrypoint", entrypoint, "--output", output, scratch=scratch),
                env={"HOME": str(home), "TMPDIR": str(scratch)})
        if output.is_symlink() or not output.is_file():
            raise ValueError("external extractor did not produce a regular event file")
        events = _events(output)
        try:
            _collect(ctx, entrypoint, events, deadline)
        finally:
            events.close()
        ctx.prepared.validate()

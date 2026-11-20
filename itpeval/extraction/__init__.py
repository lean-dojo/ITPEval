"""Extract native declaration data from a prepared project's immutable sources."""

import fcntl
import importlib
import json
import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path

from itpeval.corpus.storage import digest, encode, jsonl, object_id, project_file
from itpeval.extraction.protocol import Extraction
from itpeval.retrieval import CorpusIndex

ADAPTERS = {p: p for p in ("lean4", "rocq", "metamath", "mizar", "acl2", "agda", "pvs", "isabelle", "hol4")}
ADAPTERS["hol-light"] = "hol_light"
SCHEMA_VERSION = 1


@dataclass(frozen=True)
class ExtractionResult:
    path: Path
    report: dict
    cache_hit: bool


class ExtractionError(ValueError):
    def __init__(self, report_path):
        self.report_path = report_path
        report = json.loads(report_path.read_bytes())
        super().__init__(report["failed"][0]["reason"])


def extract_project(prepared, entrypoint: str, destination, *, timeout_s=180, context_storage="expanded"):
    """Return an immutable bundle or raise ExtractionError carrying the failure report."""
    prover = prepared.spec.prover
    external = prover not in ADAPTERS
    adapter = prepared.adapter if external else None
    if external and (adapter is None or adapter.extractor is None):
        raise NotImplementedError(f"declaration extraction is unavailable for {prover}")
    if context_storage not in {"expanded", "compact"}:
        raise ValueError("expected expanded or compact context storage")
    if context_storage == "compact" and prover != "metamath":
        raise ValueError("compact extraction contexts are currently supported for Metamath")
    if timeout_s <= 0:
        raise ValueError("timeout_s must be positive")
    prepared.validate()
    entry = project_file(prepared.project, entrypoint).relative_to(prepared.project.resolve()).as_posix()
    destination = Path(destination).resolve()
    if destination.is_relative_to(prepared.project.resolve()):
        raise ValueError("place extraction results outside the prepared project")
    destination.mkdir(parents=True, exist_ok=True)
    module = importlib.import_module("." + ADAPTERS.get(prover, "external"), __name__)
    implementation = {name: digest(Path(p).read_bytes()) for name, p in (
        ("adapter", module.__file__), ("service", __file__), ("collector", Path(__file__).with_name("protocol.py")),
        ("records", Path(__file__).resolve().parents[1] / "core" / "declarations.py"),
        ("index", importlib.import_module("itpeval.retrieval").__file__),
        ("contexts", importlib.import_module("itpeval.corpus.contexts").__file__),
        ("storage", importlib.import_module("itpeval.corpus.storage").__file__),
        ("executor", importlib.import_module("itpeval.runtime.process").__file__))}
    root = Path(__file__).parent
    if external:
        from itpeval.verification.cache import verifier_revision

        implementation["external_extractor"] = digest(adapter.extractor.read_bytes())
        implementation["external_verifier"] = verifier_revision(prover)
        profile = importlib.import_module("itpeval.backends.external")
        implementation["external_task_profile"] = digest(Path(profile.__file__).read_bytes())
    if prover in {"metamath", "acl2"}:
        syntax = importlib.import_module(f"itpeval.backends.{prover}.syntax")
        implementation["native_source_syntax"] = digest(Path(syntax.__file__).read_bytes())
    probes = [] if external else sorted((root / "native").glob(ADAPTERS[prover] + ".*"))
    if probes:
        probes.append(root / "native_io.py")
    for probe in probes:
        implementation[str(probe.relative_to(root))] = digest(probe.read_bytes())
    if context_storage == "compact":
        implementation["context_storage"] = digest(context_storage.encode())
    inputs = {p.relative_to(prepared.project).as_posix(): digest(p.read_bytes())
              for p in sorted(prepared.project.rglob("*")) if p.is_file()}
    key = object_id(SCHEMA_VERSION, implementation, prepared.environment_id, inputs, entry)
    bundle = destination / key
    with (destination / (key + ".lock")).open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if bundle.is_dir():
            return ExtractionResult(bundle, json.loads((bundle / "report.json").read_bytes()), True)
        with tempfile.TemporaryDirectory(dir=destination) as tmp:
            stage = Path(tmp) / "bundle"
            root = Path(tmp) / "project"
            # copyfile avoids inheriting read-only permissions from the snapshot.
            root.mkdir()
            for name, expected in inputs.items():
                source = project_file(prepared.project, name)
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
                if digest(target.read_bytes()) != expected:
                    raise ValueError(f"prepared source changed during extraction: {name}")
            stage.mkdir()
            ctx = Extraction(prepared, root, stage / "blobs", timeout_s, context_storage=context_storage)
            report = {"schema_version": SCHEMA_VERSION, "environment_id": prepared.environment_id,
                      "extractor_revision": implementation, "project_inputs": inputs, "prover": prover,
                      "entrypoint": entry, "succeeded": [], "skipped": [], "failed": []}
            if external:
                report["adapter_protocol"] = module.SCHEMA_VERSION
            if context_storage == "compact":
                report["context_storage"] = context_storage
            try:
                module.extract(ctx, entry)
            except (OSError, UnicodeError, ValueError, KeyError) as exc:
                report.update(succeeded=ctx.notes["succeeded"], skipped=ctx.notes["skipped"],
                              failed=[{"source": entry, "reason": str(exc)}],
                              counts={"successful_source_units": len(set(ctx.notes["succeeded"])),
                                      "skipped_entries": len(ctx.notes["skipped"]), "failed_invocations": 1})
                failures = destination / "failures"
                failures.mkdir(exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=failures, suffix=".json", delete=False) as failure:
                    failure.write(encode(report))
                raise ExtractionError(Path(failure.name)) from exc
            ids = {d.declaration_id for d in ctx.declarations}
            if len(ids) != len(ctx.declarations):
                raise ValueError("extractor emitted duplicate declaration identities")
            jsonl(stage / "declarations.jsonl", (d.to_dict() for d in ctx.declarations))
            jsonl(stage / "contexts.jsonl", (v.to_dict() for v in ctx.contexts.values()))
            jsonl(stage / "dependencies.jsonl", (e.to_dict() for e in ctx.edges))
            report.update({"declarations": len(ids), "fields": ctx.availability,
                           "counts": {"successful_source_units": len(set(ctx.notes["succeeded"])),
                                      "skipped_entries": len(ctx.notes["skipped"]), "failed_invocations": 0},
                           "succeeded": ctx.notes["succeeded"], "skipped": ctx.notes["skipped"],
                           "sources": ctx.sources, "structures": ctx.structures,
                           "unresolved_edges": sum(e.target_id is None for e in ctx.edges)})
            (stage / "report.json").write_bytes(encode(report))
            CorpusIndex.build(stage)
            stage.rename(bundle)
            return ExtractionResult(bundle, report, False)

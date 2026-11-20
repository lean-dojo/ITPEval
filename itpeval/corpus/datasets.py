"""Dataset exports, premise-selection records and grouped benchmark partitions."""

import json
from collections import defaultdict
from hashlib import sha256
from itertools import groupby
from pathlib import Path

from itpeval.corpus.contexts import ContextTable
from itpeval.corpus.storage import jsonl, object_id, read_jsonl
from itpeval.extraction import extract_project


def partition_items(members, *, groups=(), seed="itpeval-v1"):
    """Keep alignments, same-source obligations and reviewed duplicates together."""
    parent = {row["theorem_id"]: row["theorem_id"] for row in members}

    def root(node):
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    for group in groups:
        ids = list(group)
        if ids:
            for ident in ids[1:]:
                a, b = root(ids[0]), root(ident)
                parent[max(a, b)] = min(a, b)

    families = defaultdict(list)
    for row in members:
        families[root(row["theorem_id"])].append(row)
    partitions = {}
    for key, family in families.items():
        explicit = {row["split"] for row in family if row.get("split")}
        if len(explicit) > 1:
            raise ValueError(f"conflicting upstream splits in group {key}: {sorted(explicit)}")
        bucket = int.from_bytes(sha256(f"{seed}/{key}".encode()).digest()[:8], "big") % 10
        split = next(iter(explicit), "train" if bucket < 8 else "valid" if bucket == 8 else "test")
        for row in family:
            partitions[row["theorem_id"]] = {"partition": split, "group_id": key,
                                             "upstream_split": row.get("split")}
    return partitions


def _declarations_and_premises(bundle, *, ordered):
    declarations = read_jsonl(bundle / "declarations.jsonl")
    edges = (edge for edge in read_jsonl(bundle / "dependencies.jsonl")
             if edge["relation"] in {"proof_used_premise", "rewrite_rule_used"})
    if not ordered:
        by_origin = defaultdict(list)
        for edge in edges:
            by_origin[edge["origin"]].append(edge)
        for declaration in declarations:
            yield declaration, by_origin.get(declaration["declaration_id"], [])
        return

    # Compact Metamath writes proof edges in declaration order. Only hold the
    # current proof's edges while joining them to its declaration.
    groups = groupby(edges, key=lambda edge: edge["origin"])
    origin, group = next(groups, (None, ()))
    for declaration in declarations:
        observed = []
        if origin == declaration["declaration_id"]:
            observed = list(group)
            origin, group = next(groups, (None, ()))
        yield declaration, observed
    if origin is not None:
        raise ValueError("compact proof dependencies must follow declaration order")


def premise_rows(bundle, *, visibility="expanded", contexts=None):
    if visibility not in {"expanded", "reference"}:
        raise ValueError("expected expanded or reference premise visibility")
    report = json.loads((bundle / "report.json").read_bytes())
    availability = report["fields"]["proof_used_premises"]
    if contexts is None:
        contexts = ContextTable(bundle)
    for decl, observed in _declarations_and_premises(bundle, ordered=contexts.compact):
        target = {k: decl[k] for k in (
            "declaration_id", "environment_id", "prover", "name", "kind", "statement", "context_id")}
        # A model sees the target statement and preceding context. Native proof
        # evidence and the completed source remain only in the extraction bundle.
        label_status = availability
        if decl["prover"] == "acl2" and decl["source_path"] != report["entrypoint"]:
            # Live world queries can inspect certified exports, while last-event-data
            # only reports rule use for the source events replayed by this extractor.
            label_status = "unavailable"
        if decl["kind"] in {"$a", "$e", "$f", "axiom", "definition", "defun"}:
            label_status = "inapplicable"
        if report.get("adapter_protocol") == 1:
            if decl["kind"] == "hypothesis":
                label_status = "inapplicable"
            elif decl["checking_status"] == "unverified" and label_status != "inapplicable":
                label_status = "unavailable"
        context_id = decl["context_id"]
        if contexts.environment_id(context_id) != decl["environment_id"]:
            raise ValueError(f"declaration and context environments differ for {context_id}")
        available = contexts.visible_ids(context_id) if visibility == "expanded" else None
        yield {"declaration": target, "available": available,
               "proof_used": observed, "retrieved": [], "proof_used_availability": label_status}


def match_target(bundle, task, *, prepared):
    """Resolve a reviewed completion to one native occurrence in the same source."""
    from dataclasses import replace

    from itpeval.backends.projects import CompletionManifest, build_task, project_file
    from itpeval.core.declarations import FormalObject
    from itpeval.corpus.storage import digest

    report = json.loads((Path(bundle) / "report.json").read_bytes())
    prepared.validate()
    if not (task.manifest_path and prepared.environment_id == task.environment_id == report["environment_id"]
            and report["prover"] == task.prover == prepared.spec.prover):
        raise ValueError("a reviewed task and matching prepared extraction environment are required")
    reference = build_task(prepared, task.manifest_path)
    if task != replace(reference, budgets=task.budgets):
        raise ValueError("task differs from its reviewed manifest")
    if getattr(prepared, "adapter", None) is None:
        manifest = CompletionManifest.from_dict(
            json.loads(project_file(prepared.project, task.manifest_path).read_bytes()))
        path, name = manifest.entrypoint, manifest.target
        source = project_file(prepared.project, path).read_bytes()
        source_hash = digest(source)
        anchor = manifest.anchor.encode()
        start = source.index(anchor)
        end = start + len(anchor)
        statement = None
    else:
        from itpeval.backends.external import detached_target

        target = detached_target(prepared, task.manifest_path)
        path, name, source_hash = target.source_path, target.name, target.source_sha256
        start, end, statement = target.start_byte, target.end_byte, target.statement
    if report["sources"].get(path) != source_hash:
        raise ValueError("declaration source differs from the prepared project")
    normalize = str.casefold if task.prover in {"acl2", "mizar"} else str
    name = normalize(name)
    matches = []
    for row in read_jsonl(Path(bundle) / "declarations.jsonl"):
        qualified = normalize(row["name"])
        if (row["source_path"] != path or row["source_hash"] != source_hash
                or row["environment_id"] != task.environment_id or row["prover"] != task.prover):
            continue
        if statement is None:
            found = ((qualified == name or qualified.endswith("." + name))
                     and max(row["start_byte"], start) < min(row["end_byte"], end))
        else:
            found = (qualified == name and row["statement"] == statement
                     and row["start_byte"] <= start < end <= row["end_byte"])
        if found:
            matches.append(FormalObject.from_dict(row))
    if len(matches) != 1:
        raise ValueError(f"expected one native occurrence for {task.targets[0]} in {path}, found {len(matches)}")
    return matches[0]


def export_dataset(prepared, entrypoint, output, *, timeout_s=180, context_storage="expanded",
                   premise_visibility=None):
    """Extract a project entrypoint and return its bundle and premise-selection JSONL path."""
    if premise_visibility is None:
        premise_visibility = "reference" if context_storage == "compact" else "expanded"
    if premise_visibility not in {"expanded", "reference"}:
        raise ValueError("expected expanded or reference premise visibility")
    result = extract_project(prepared, entrypoint, Path(output) / "extractions", timeout_s=timeout_s,
                             context_storage=context_storage)
    suffix = ".premises.jsonl" if premise_visibility == "expanded" else ".premises-referenced.jsonl"
    path = Path(output) / (result.path.name + suffix)

    def tasks():
        for row in premise_rows(result.path, visibility=premise_visibility):
            decl = row["declaration"]
            # The context is the input; proof references, when available, form
            # the labels. A missing label set must remain unknown in training.
            yield {"schema_version": 1, "operation": "premise_selection",
                   "task_id": object_id("premise_selection", result.path.name, decl["declaration_id"]),
                   **row}

    jsonl(path, tasks())
    return result, path

"""Extract a named declaration, construct its task, repair a proof and replay the episode."""

from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path
import sys

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, prover_ids
from itpeval.cli.lib import default_prefix
from itpeval.core.episodes import Action, Episode
from itpeval.core.records import digest
from itpeval.core.types import TaskSpec
from itpeval.corpus.contexts import ContextTable
from itpeval.corpus.storage import jsonl, read_jsonl
from itpeval.environments import load_project, prepare_project
from itpeval.extraction import extract_project
from itpeval.learning.episodes import export_jsonl, replay, task_prompt
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rollouts import rollout


def completion_row(prepared, cache: Path, manifest_path: str = "completion.json"):
    """Construct a dataset row from a reviewed manifest and a native declaration at its source anchor."""
    from itpeval.corpus.datasets import match_target

    task = build_task(prepared, manifest_path)
    entrypoint = task.artifact.entrypoint
    if task.is_detached_certificate:
        from itpeval.backends.external import detached_target
        entrypoint = detached_target(prepared, manifest_path).source_path
    extracted = extract_project(prepared, entrypoint, cache / "extraction")
    target = match_target(extracted.path, task, prepared=prepared)
    contexts = ContextTable(extracted.path)
    if target.context_id not in contexts or contexts.environment_id(target.context_id) != prepared.environment_id:
        raise ValueError("the target requires one context in the same prepared environment")
    return {"schema_version": 1, "operation": "proof_completion", "task": task.to_dict(),
            "task_id": task.task_id, "target": target.to_dict(), "context": contexts.context(target.context_id).to_dict(),
            "environment": prepared.spec.to_dict(), "extraction_id": extracted.path.name,
            "extraction_fields": extracted.report["fields"],
            "source_base64": base64.b64encode((prepared.project / target.source_path).read_bytes()).decode("ascii")}


def run(prover: str, prefix: Path, cache: Path, output: Path, *, archive_run: bool = False) -> Path:
    prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
    return run_prepared(prepared, cache, output, archive_run=archive_run)


def run_prepared(prepared, cache: Path, output: Path, *, manifest_path: str = "completion.json",
                 candidates=None, archive_run: bool = False) -> Path:
    """Repair a task in a prepared project using a sequence of prerecorded edits."""
    row = completion_row(prepared, cache, manifest_path)
    dataset_id = digest(row)
    task = TaskSpec.from_dict(row["task"])
    fixture_demo = candidates is None
    if fixture_demo:
        if task.is_detached_certificate:
            raise ValueError("provide prerecorded certificate candidates for a detached proof task")
        reference, incorrect = task.allowed_edits[:2]
        candidates = [incorrect, reference]
    if not isinstance(candidates, (list, tuple)) or not candidates or not all(isinstance(v, str) for v in candidates):
        raise ValueError("candidates must be a nonempty sequence of proof fragments")
    manifest = RunManifest.for_proof_task(task, dataset_id, digest(task_prompt(task)),
                                          {"id": "prerecorded", "edits": list(candidates)}, seed=0,
                                          max_attempts=len(candidates))
    if archive_run:
        output = output / manifest.run_id
    path = output / "episodes.jsonl"
    manifest.bind(path)
    jsonl(output / "dataset.jsonl", [row])

    def generate(_, history):
        candidate = candidates[len(history)]
        return Action("edit_document", candidate, candidate)

    if path.is_file():
        episode = Episode.from_dict(json.loads(path.read_bytes()))
        if episode.run_id != manifest.run_id:
            raise ValueError("saved episode differs from its run manifest")
    else:
        episode = rollout(task, prepared, manifest, generate)
        export_jsonl([episode], path, view="episodes")
    export_jsonl([episode], output / "attempts.jsonl")
    export_jsonl([episode], output / "supervised.jsonl", view="supervised")
    for view in ("repair", "trajectory"):
        export_jsonl([episode], output / (view + ".jsonl"), view=view)
    restored = Episode.from_dict(json.loads(path.read_text(encoding="utf-8")))
    if fixture_demo and [step.observation.task_success for step in restored.transitions] != [False, True]:
        raise RuntimeError(f"expected incorrect then successful completion; inspect {path}")
    reloaded_row, = read_jsonl(output / "dataset.jsonl")
    if digest(reloaded_row) != RunManifest.from_dict(restored.manifest).dataset_id:
        raise ValueError("episode dataset identity mismatch")
    final = replay(restored, task=TaskSpec.from_dict(reloaded_row["task"]), prepared=prepared,
                   receipt=path.with_name("replay.json"))
    if fixture_demo and final.task_success is not True:
        raise RuntimeError(f"final replay failed; inspect {path}")
    return path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    select = parser.add_mutually_exclusive_group(required=True)
    select.add_argument("--prover", choices=prover_ids())
    select.add_argument("--lock", type=Path, help="prepared environment for a reviewed project task")
    parser.add_argument("--manifest", default="completion.json")
    parser.add_argument("--candidates", type=Path, help="JSON array of prerecorded edits in attempt order")
    parser.add_argument("--prefix", type=Path, help="override the configured toolchain directory for --prover")
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--show-attempts", action="store_true", help="display each recorded candidate and checker verdict")
    args = parser.parse_args()
    if args.lock:
        if args.prefix or not args.candidates:
            parser.error("--lock requires --candidates and already specifies its toolchain prefix")
        prepared = load_project(args.lock)
    else:
        prepared = prepare_project(args.prover, curated_project(args.prover),
                                   prefix=args.prefix or default_prefix(), cache=args.cache)
    edits = json.loads(args.candidates.read_bytes()) if args.candidates else None
    path = run_prepared(prepared, args.cache, args.output, manifest_path=args.manifest, candidates=edits)
    if args.show_attempts:
        episode = Episode.from_dict(json.loads(path.read_bytes()))
        print("Prerecorded proof attempts", file=sys.stderr)
        for index, transition in enumerate(episode.transitions, 1):
            print(f"{index}. {transition.action.candidate!r} -> {transition.observation.checker_outcome}", file=sys.stderr)
    print(path)


if __name__ == "__main__":
    main()

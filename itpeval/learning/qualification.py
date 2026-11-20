"""Native conformance checks for curated document tasks, with replayable evidence."""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import tempfile
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, prover_ids
from itpeval.core.episodes import Episode
from itpeval.core.types import TaskSpec
from itpeval.environments import prepare_project
from itpeval.learning.episodes import replay
from itpeval.learning.example import run as run_episode
from itpeval.runtime.sessions import DocumentSession
from itpeval.verification.service import assemble, verify


def _record(path: Path, reports: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.with_suffix(".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        rows = [json.loads(line) for line in path.read_text().splitlines() if line] if path.exists() else []
        by_key = {(r["prover"], r["operation"]): r for r in rows + reports}
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as tmp:
            try:
                for key in sorted(by_key):
                    print(json.dumps(by_key[key], sort_keys=True), file=tmp)
                tmp.flush()
                os.replace(tmp.name, path)
            finally:
                Path(tmp.name).unlink(missing_ok=True)


def _reset(session, candidate):
    old = session.handle
    new = session.reset()
    try:
        session.submit(old, candidate)
    except ValueError as error:
        diagnostic = str(error)
    else:
        raise ValueError("reset accepted an obsolete document handle")
    return {"old_handle": old.to_dict(), "new_handle": new.to_dict(),
            "stale_rejected": old.worker_generation != new.worker_generation, "diagnostic": diagnostic}


def refresh_replay(prover: str, prefix: Path, cache: Path, directory: Path) -> bool:
    """Recheck the saved actions and capture the independent native results in their original environment."""
    path = directory / prover / "conformance.json"
    detail = json.loads(path.read_bytes())
    episode_path = path.parent / detail["episode"]
    episode = Episode.from_dict(json.loads(episode_path.read_bytes()))
    prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
    task = build_task(prepared)
    replay_path = episode_path.with_name("replay.json")
    final = replay(episode, task=task, prepared=prepared, receipt=replay_path)
    detail["reset"] = _reset(DocumentSession(task, prepared), episode.final_candidate)
    detail["replay"] = replay_path.relative_to(path.parent).as_posix()
    path.write_text(json.dumps(detail, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return final.task_success is True and detail["reset"]["stale_rejected"]


def qualify(prover: str, prefix: Path, cache: Path, directory: Path, report_path: Path) -> bool:
    directory = directory / prover
    directory.mkdir(parents=True, exist_ok=True)
    evidence = {}
    operations = {key: False for key in ("check_artifact", "proof_completion", "edit_document", "reset", "episode_replay", "end_to_end")}
    build = identity = None
    try:
        prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
        build, identity = prepared.spec.prover_build, prepared.environment_id
        task = build_task(prepared)
        reference, wrong = task.allowed_edits[:2]
        whole = TaskSpec(prover, identity, "check_artifact", assemble(task, reference))
        artifact = verify(whole, prepared=prepared)
        evidence["artifact"] = artifact.to_dict()
        operations["check_artifact"] = artifact.task_success is True

        candidates = {"changed_target": "theorem other : True", "deleted_obligation": "",
                      "admission": "admit", "changed_environment": "axiom unrelated"}
        negative = {key: verify(task, candidate, prepared=prepared) for key, candidate in candidates.items()}
        evidence["restricted_edits"] = {k: result.to_dict() for k, result in negative.items()}

        session = DocumentSession(task, prepared)
        old = session.handle
        handle, rejected = session.submit(old, wrong)
        evidence["incorrect_edit"] = rejected.to_dict()
        evidence["reset"] = _reset(session, reference)
        handle = session.handle
        operations["reset"] = evidence["reset"]["stale_rejected"]
        handle, checked = session.submit(handle, reference)
        final = session.finalize(handle)
        evidence["valid_edit"] = checked.to_dict()
        evidence["final"] = final.to_dict()
        operations["edit_document"] = rejected.task_success is False and checked.task_success is True and final.task_success is True

        alternates = [verify(task, edit, prepared=prepared) for edit in task.allowed_edits[2:3]]
        evidence["alternate"] = [result.to_dict() for result in alternates]
        operations["proof_completion"] = bool(
            operations["edit_document"] and all(result.checker_outcome == ("incomplete" if key == "deleted_obligation" else "policy_rejected")
                                                  for key, result in negative.items())
            and all(result.task_success is True for result in alternates) and alternates
        )

        saved = run_episode(prover, prefix, cache, directory / "episodes", archive_run=True)
        episode = Episode.from_dict(json.loads(saved.read_bytes()))
        operations["episode_replay"] = episode.environment_id == identity
        evidence["episode"] = saved.relative_to(directory).as_posix()
        evidence["replay"] = saved.with_name("replay.json").relative_to(directory).as_posix()
        dataset_path = saved.with_name("dataset.jsonl")
        dataset = json.loads(dataset_path.read_bytes())
        evidence["dataset"] = dataset_path.relative_to(directory).as_posix()
        evidence["declaration_id"] = dataset["target"]["declaration_id"]
        evidence["context_id"] = dataset["context"]["context_id"]
        operations["end_to_end"] = (dataset["task_id"] == episode.task_id
                                    and dataset["context"]["environment_id"] == identity
                                    and dataset["target"]["environment_id"] == identity)
    except (RuntimeError, ValueError, OSError, KeyError) as error:
        evidence["error"] = str(error)
    target = directory / "conformance.json"
    target.write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    _record(report_path, [{"prover": prover, "prover_build": build, "environment_id": identity,
                           "operation": operation, "status": "implemented/tested" if passed else "failed",
                           "evidence_path": os.path.relpath(target, report_path.parent)}
                          for operation, passed in operations.items()])
    return all(operations.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prover", choices=prover_ids(), action="append")
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--refresh-replay", action="store_true", help="reverify an existing qualified episode")
    args = parser.parse_args()
    results = {prover: (refresh_replay(prover, args.prefix, args.cache, args.output) if args.refresh_replay
                        else qualify(prover, args.prefix, args.cache, args.output, args.report))
               for prover in args.prover or prover_ids()}
    print(json.dumps(results, indent=2))
    raise SystemExit(0 if all(results.values()) else 1)


if __name__ == "__main__":
    main()

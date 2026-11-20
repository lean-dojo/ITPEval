"""Exercise the shared native driver and training export on all installed provers."""

from __future__ import annotations

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from contextlib import nullcontext
from pathlib import Path
from time import perf_counter

from itpeval.backends.hol_light.worker import ForkedHOLLight
from itpeval.backends.registry import curated_project, get_backend
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import NativeProofEpisode, replay_native_episode, rollout_native
from itpeval.learning.training_data import export_training_data
from itpeval.runtime.proof_driver import NativeProofAction as Action
from itpeval.runtime.proof_driver import NativeProofCheckpoint, NativeProofDriver


def _examples(prover, task):
    if prover in {"hol4", "hol-light"}:
        return (
            Action("tactic", "DISCH_TAC", ()), Action("tactic", "CONJ_TAC", (0,)),
            Action("tactic", "NO_TAC", (0, 0)), Action("tactic", "ASM_REWRITE_TAC []", (0, 1)),
            Action("tactic", "ASM_REWRITE_TAC []", (0, 0)),
        )
    if prover in {"mizar", "isabelle"}:
        return tuple(Action("edit_document", text) for text in (task.allowed_edits[1], task.allowed_edits[0]))
    commands = {
        "acl2": ("command", ("demote", "s")),
        "agda": ("term", ("Bool", "x")),
        "lean4": ("tactic", ("exact False.elim", "rfl")),
        "pvs": ("command", ("(skosimp)", "(split)", "(postpone)", "(grind)", "(grind)")),
        "rocq": ("command", ("exact I.", "intro p.", "exact p.")),
    }
    if prover == "metamath":
        return tuple(Action("assign", label, step_index=index) for index, label in
                     ((1, "distinct"), (1, "vx"), (2, "vx"), (2, "vy")))
    kind, examples = commands[prover]
    return tuple(Action(kind, text) for text in examples)


def exercise(prover, prefix, cache):
    project = curated_project(prover)
    if prover in {"acl2", "agda", "hol4", "hol-light", "isabelle", "pvs"}:
        project = project.parent / "interaction"
    prepared = prepare_project(prover, project, prefix=prefix, cache=cache)
    task = get_backend(prover).build_task(prepared)
    expected = _examples(prover, task)
    finish = task.allowed_edits[0] if prover == "pvs" else None
    manifest = RunManifest.for_native_proof_task(task, "native-session-examples", "native-step-example",
                                                 {"policy": "reviewed_commands"}, max_attempts=len(expected))
    preloader = ForkedHOLLight(prepared) if prover == "hol-light" else nullcontext()
    with preloader as worker:
        options = {"worker": worker} if worker is not None else {}
        start = perf_counter()
        episode = rollout_native(task, prepared, manifest, lambda _task, _state, history: expected[len(history)],
                                 proof_fragment=finish, **options)
        rollout_s = perf_counter() - start
        roundtrip = NativeProofEpisode.from_dict(json.loads(json.dumps(episode.to_dict())))
        start = perf_counter()
        replay = replay_native_episode(roundtrip, task=task, prepared=prepared, **options)
        replay_s = perf_counter() - start

        session = NativeProofDriver(task, prepared, **options)
        first = next(i for i, step in enumerate(episode.transitions) if step.committed)
        for step in episode.transitions[:first + 1]:
            session.advance(step.action)
        snapshot = session.checkpoint()
        saved = NativeProofCheckpoint.from_dict(json.loads(json.dumps(snapshot.to_dict())))
        child = session.fork()
        restored = NativeProofDriver.from_checkpoint(task, prepared, saved, **options)
        checkpoint_ok = (child.checkpoint() == restored.checkpoint() == snapshot and bool(snapshot.actions))
        for step in episode.transitions[first + 1:]:
            assert child.advance(step.action).committed == step.committed, prover
        assert session.checkpoint() == snapshot, prover

    checks = {
        "checkpoint_actions": checkpoint_ok,
        "initial_goal": episode.initial.status == "open",
        "native_feedback_replayed": (replay is not None and replay.task_success is True
                                     and episode.finalization.evidence.artifact_id == replay.artifact_id),
        "attempt_semantics": (prover == "pvs" or
                              any(step.observation.status == "rejected" and step.committed == (prover == "mizar")
                                  for step in episode.transitions[:-1])),
    }
    if not all(checks.values()):
        raise ValueError(f"{prover}: native proof driver regression: {checks}")
    print(prover, [step.observation.status for step in episode.transitions], replay.checker_outcome, flush=True)
    return episode, {"prover": prover, "environment_id": task.environment_id, "task_id": task.task_id,
                     "prover_build": prepared.spec.prover_build, "operations": checks,
                     "timings_s": {"rollout": rollout_s, "replay": replay_s},
                     "replayed_artifact_id": replay.artifact_id,
                     "steps": [{"kind": step.action.kind, "status": step.observation.status,
                                "committed": step.committed} for step in episode.transitions]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ("prefix", "cache", "output", "episodes", "training"):
        parser.add_argument("--" + argument, type=Path, required=True)
    provers = ("acl2", "agda", "hol-light", "hol4", "isabelle", "lean4", "metamath", "mizar", "pvs", "rocq")
    parser.add_argument("--prover", choices=provers, action="append")
    parser.add_argument("--format", choices=("jsonl", "parquet", "both"), default="jsonl")
    args = parser.parse_args()
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda prover: exercise(prover, args.prefix, args.cache), args.prover or provers))
    args.episodes.parent.mkdir(parents=True, exist_ok=True)
    jsonl(args.episodes, (episode.to_dict() for episode, _ in results))
    views = export_training_data(args.training, native_episodes=(args.episodes,), format=args.format, split="train")
    assert views["views"]["proof_steps"] == sum(len(episode.transitions) for episode, _ in results)
    write_json(args.output, [row for _, row in results])


if __name__ == "__main__":
    main()

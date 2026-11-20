"""Check ATP suggestions after native proof actions and export the resulting episodes."""

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from time import perf_counter

from itpeval.atp.session import NativeATPSuggestion
from itpeval.backends.registry import curated_project, get_backend
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import SearchWithATP, replay_native_episode, rollout_native
from itpeval.learning.training_data import export_training_data
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


def _exercise(prover, args):
    fixture = curated_project(prover).parent / ("hammer" if prover == "isabelle" else "horn-prefix")
    prepared = prepare_project(prover, fixture, cache=args.cache, prefix=args.prefix)
    task = get_backend(prover).build_task(prepared)
    actions = {
        "lean4": (NativeProofAction("tactic", "intro hready hpermitted"),
                  NativeProofAction("tactic", "intro hdelivered hcomplete")),
        "rocq": (NativeProofAction("command", "intro hp."),),
        "isabelle": (),
    }[prover]
    requests = tuple(SearchWithATP(name, binary if prover != "isabelle" else None)
                     for name, binary in (("e", args.e), ("vampire", args.vampire)))
    driver = NativeProofDriver(task, prepared)
    initial = driver.observe()
    if actions:
        unsupported = driver.suggest_atp(solver=requests[0].solver, executable=requests[0].executable)
        assert unsupported.outcome == "unsupported_goal" and unsupported.unsupported_observation is not None
    for action in actions:
        transition = driver.advance(action)
        assert transition.committed and transition.observation.status == "open"
    snapshot = driver.checkpoint()
    destination = args.work / prover
    write_json(destination / "checkpoint.json", snapshot.to_dict())
    write_json(destination / "lock-reference.json", {"lock": str(prepared.lock_path)})
    trials = []
    for request in requests:
        session = NativeProofDriver.from_checkpoint(task, prepared, snapshot)
        start = perf_counter()
        result = session.suggest_atp(solver=request.solver, executable=request.executable)
        seconds = perf_counter() - start
        decoded = NativeATPSuggestion.from_dict(json.loads(json.dumps(result.to_dict())))
        assert result == decoded and session.checkpoint() == snapshot
        assert result.outcome == "accepted", (prover, request.solver, result.outcome)
        transition = session.apply_atp(decoded)
        assert transition.committed and transition.observation.status == "ready"
        final = session.finalize()
        assert final.candidate == result.candidate and final.evidence.task_success is True
        assert final.evidence.artifact_id == result.verification.artifact_id
        try:
            session.apply_atp(decoded)
        except ValueError as error:
            assert "proof revision" in str(error)
        else:
            raise ValueError("applied a suggestion to a different native proof revision")
        write_json(destination / f"{request.solver}.json", result.to_dict())
        build = result.evidence.solver if prover == "isabelle" else result.evidence.search.solver
        trials.append({"solver": build.to_dict(), "outcome": result.outcome, "seconds": seconds,
                       "artifact_id": final.evidence.artifact_id, "candidate": result.candidate})

    manifest = RunManifest.for_native_proof_task(task, "hybrid-examples", "native-then-atp",
                                                 {"policy": "reviewed native steps followed by E"},
                                                 max_attempts=len(actions) + 1)
    decisions = (*actions, requests[0])
    episode = rollout_native(task, prepared, manifest, lambda _task, _state, history: decisions[len(history)])
    rechecked = replay_native_episode(episode, task=task, prepared=prepared)
    assert rechecked.task_success is True and episode.atp.outcome == "accepted"
    assert episode.atp.state_id == snapshot.state_ids[-1] and initial.state_id == snapshot.state_ids[0]
    print(prover, len(actions), len(trials), rechecked.checker_outcome, flush=True)
    return episode, {"prover": prover, "prover_build": prepared.spec.prover_build,
                     "task_id": task.task_id, "environment_id": task.environment_id,
                     "checkpoint": snapshot.to_dict(), "solvers": trials, "operations": {"atp_from_state": True}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for path in ("prefix", "e", "vampire", "cache", "work", "output"):
        parser.add_argument(f"--{path}", type=Path, required=True)
    parser.add_argument("--prover", action="append", choices=("lean4", "rocq", "isabelle"))
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(lambda prover: _exercise(prover, args), args.prover or ("lean4", "rocq", "isabelle")))
    path = args.work / "episodes.jsonl"
    jsonl(path, (episode.to_dict() for episode, _ in results))
    report = export_training_data(args.work / "training", native_episodes=(path,), format="both")
    assert report["views"]["proof_steps"] == sum(len(episode.transitions) for episode, _ in results)
    write_json(args.output, [row for _, row in results])


if __name__ == "__main__":
    main()

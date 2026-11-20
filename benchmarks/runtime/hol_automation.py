"""Exercise automated search on separate HOL subgoals and export its feedback."""

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from contextlib import nullcontext
from pathlib import Path
from time import perf_counter

from itpeval.atp import NativeATPSuggestion
from itpeval.backends.hol_light.worker import ForkedHOLLight
from itpeval.backends.registry import curated_project, get_backend
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import NativeProofEpisode, SearchWithATP, check_native_episode, rollout_native
from itpeval.learning.training_data import export_training_data
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


def _result(suggestion):
    evidence = suggestion.evidence
    return {"goal": evidence.goal.to_dict(), "remaining": [goal.to_dict() for goal in evidence.after.goals],
            "tactic": evidence.tactic, "outcome": suggestion.outcome, "duration_ms": evidence.duration_ms,
            "tptp": evidence.tptp, "search": evidence.search.to_dict() if evidence.search else None,
            "candidate": suggestion.candidate,
            "artifact_id": suggestion.verification.artifact_id if suggestion.verification else None}


def exercise(prover, solver, args):
    fixture = "metis" if prover == "hol4" else "automation"
    project = curated_project(prover).parent / fixture
    prepared = prepare_project(prover, project, prefix=args.prefix, cache=args.cache)
    task = get_backend(prover).build_task(prepared)
    introduce = "REPEAT DISCH_TAC" if prover == "hol4" else "DISCH_TAC"
    program = [NativeProofAction("tactic", introduce, ()), NativeProofAction("tactic", "CONJ_TAC", (0,))]
    executable = {"e": args.e, "vampire": args.vampire}.get(solver)
    # Work on the right branch first so we check that selection is respected.
    paths = (0, 1), (0, 0)
    program.extend(SearchWithATP(solver, executable, goal_path=path) for path in paths)
    manifest = RunManifest.for_native_proof_task(task, "hol-automation-examples", "select-branch",
                                                 {"solver": solver}, max_attempts=len(program))
    warm = prover == "hol-light" and ForkedHOLLight.supports_project(prepared)
    preloader = ForkedHOLLight(prepared) if warm else nullcontext()
    start = perf_counter()
    with preloader as worker:
        options = {"worker": worker} if worker is not None else {}
        startup_s = perf_counter() - start
        begin = perf_counter()
        episode = rollout_native(task, prepared, manifest, lambda _task, _state, history: program[len(history)], **options)
        rollout_s = perf_counter() - begin
        decoded = NativeProofEpisode.from_dict(json.loads(json.dumps(episode.to_dict())))
        assert decoded == episode and check_native_episode(decoded).task_success is True
        partial, = episode.atp_progress
        assert partial.step == 2 and partial.suggestion.outcome == "progress"
        assert partial.suggestion.verification is None and partial.suggestion.candidate is None
        assert [goal.path for goal in partial.suggestion.evidence.after.goals] == [paths[1]]
        assert episode.atp.outcome == "accepted" and episode.atp.verification.task_success is True
        assert episode.atp.verification.artifact_id == episode.finalization.evidence.artifact_id

        # The earlier suggestion is stale after its verified branch is committed.
        driver = NativeProofDriver(task, prepared, **options)
        for step in episode.transitions[:2]:
            driver.advance(step.action)
        saved = driver.checkpoint()
        suggestion = NativeATPSuggestion.from_dict(partial.suggestion.to_dict())
        driver.apply_atp(suggestion)
        after = driver.checkpoint()
        try:
            driver.apply_atp(suggestion)
        except ValueError as error:
            assert "proof revision" in str(error) and driver.checkpoint() == after
        else:
            raise ValueError("expected stale automation suggestion rejection")
        directory = args.work / f"{prover}-{solver}"
        write_json(directory / "checkpoint.json", saved.to_dict())
        write_json(directory / "lock-reference.json", {"lock": str(prepared.lock_path)})
    attempts = [_result(item) for item in (partial.suggestion, episode.atp)]
    if solver in {"e", "vampire"}:
        assert all(item["search"]["outcome"] == "theorem" for item in attempts)
    print(prover, solver, [item["outcome"] for item in attempts], flush=True)
    return episode, {"prover": prover, "solver": solver, "warm": warm, "startup_s": startup_s, "rollout_s": rollout_s,
                     "prover_build": prepared.spec.prover_build, "environment_id": task.environment_id,
                     "task_id": task.task_id, "attempts": attempts,
                     "operations": {"automated_search": True, "atp_from_state": True,
                                    "external_atp_goal": solver in {"e", "vampire"}}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for path in ("prefix", "cache", "work", "output"):
        parser.add_argument(f"--{path}", type=Path, required=True)
    parser.add_argument("--e", type=Path)
    parser.add_argument("--vampire", type=Path)
    parser.add_argument("--external", action="store_true", help="run the HOL4 E and Vampire arms")
    parser.add_argument("--prover", action="append", choices=("hol4", "hol-light"))
    args = parser.parse_args()
    cases = ([('hol4', 'e'), ('hol4', 'vampire')] if args.external else
             [(prover, "native") for prover in args.prover or ("hol4", "hol-light")])
    args.work.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda case: exercise(*case, args), cases))
    path = args.work / "episodes.jsonl"
    jsonl(path, (episode.to_dict() for episode, _ in results))
    archive = export_training_data(args.work / "training", native_episodes=(path,), format="both")
    assert archive["views"]["proof_steps"] == 4 * len(cases)
    write_json(args.output, [row for _, row in results])


if __name__ == "__main__":
    main()

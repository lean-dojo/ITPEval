"""Verify forked native search with real Lean, Agda, PVS, E and Vampire."""

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from time import perf_counter

from itpeval.atp.search import prepare_solver
from itpeval.backends.registry import curated_project, get_backend
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.learning.native_proofs import SearchWithATP
from itpeval.learning.portfolio import ProofPortfolio, replay_portfolio, search_portfolio
from itpeval.learning.training_data import export_training_data
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


def exercise(prover, solver_name, args):
    fixture = "portfolio" if prover == "lean4" else "horn"
    prepared = prepare_project(prover, curated_project(prover).parent / fixture, prefix=args.prefix, cache=args.cache)
    task = get_backend(prover).build_task(prepared)
    driver = NativeProofDriver(task, prepared)
    proof_fragment = None
    if prover == "pvs":
        for command in ("(skosimp)", "(split 1)"):
            driver.advance(NativeProofAction("command", command))
        proof_fragment = "(then (skosimp) (split 1) (grind))"
    start = driver.checkpoint()
    solver = prepare_solver(solver_name, prefix=prepared.prefix,
                            executable=args.e if solver_name == "e" else args.vampire)
    request = SearchWithATP(solver)

    def propose(_task, _state, history):
        if not history and prover == "lean4":
            return (request, NativeProofAction("tactic", "left"), NativeProofAction("tactic", "right"))
        if not history and prover == "pvs":
            return (request, NativeProofAction("command", "(grind)"))
        return (request,)

    begin = perf_counter()
    portfolio = search_portfolio(driver, propose, policy_id=f"{prover}-{solver_name}", max_depth=2,
                                 max_trials=8, proof_fragment=proof_fragment)
    search_s = perf_counter() - begin
    assert portfolio.outcome == "accepted" and driver.checkpoint() == start
    decoded = ProofPortfolio.from_dict(json.loads(json.dumps(portfolio.to_dict())))
    assert decoded == portfolio
    episode = replay_portfolio(decoded, task=task, prepared=prepared)
    assert episode.finalization.evidence.task_success is True
    if prover == "lean4":
        assert [trial.outcome for trial in portfolio.trials] == [
            "unsupported_goal", "open", "open", "counter_satisfiable", "accepted"]
        assert portfolio.trials[3].parent == 1 and portfolio.trials[4].parent == 2
        assert episode.transitions[0].action.text == "right"
    if prover == "pvs":
        assert len(portfolio.trials) == 3 and portfolio.winner == 2 and portfolio.trials[2].parent == 0
        assert episode.finalization.match == "same_locked_target"
        assert dict(episode.finalization.evidence.obligations)["twice_TCC1"] == "discharged"
    paths = args.work / f"{prover}-{solver_name}"
    write_json(paths / "portfolio.json", portfolio.to_dict())
    write_json(paths / "checkpoint.json", portfolio.start.to_dict())
    write_json(paths / "binding.json", {"lock": str(prepared.lock_path)})
    if proof_fragment:
        (paths / "proof.txt").write_text(proof_fragment + "\n", encoding="utf-8")
    print(prover, solver_name, len(portfolio.trials), episode.finalization.evidence.checker_outcome, flush=True)
    return episode, {"prover": prover, "environment_id": task.environment_id, "task_id": task.task_id,
                     "prover_build": prepared.spec.prover_build, "solver": solver.build.to_dict(), "search_s": search_s,
                     "trials": [{"parent": t.parent, "outcome": t.outcome,
                                 "action": t.action.to_dict() if t.action else None} for t in portfolio.trials],
                     "winner": portfolio.winner, "replay": episode.finalization.to_dict()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "e", "vampire", "work", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    cases = [(prover, solver) for prover in ("lean4", "agda", "pvs") for solver in ("e", "vampire")]
    with ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(lambda case: exercise(*case, args), cases))
    path = args.work / "episodes.jsonl"
    jsonl(path, (episode.to_dict() for episode, _ in results))
    views = export_training_data(args.work / "training", native_episodes=(path,), format="both")
    assert views["views"]["proof_steps"] == sum(len(episode.transitions) for episode, _ in results)
    groups = []
    for prover in ("lean4", "agda", "pvs"):
        rows = [row for _, row in results if row["prover"] == prover]
        group = {key: rows[0][key] for key in ("prover", "environment_id", "task_id", "prover_build")}
        assert all((row["environment_id"], row["task_id"]) == (group["environment_id"], group["task_id"]) for row in rows)
        assert len({row["replay"]["evidence"]["artifact_id"] for row in rows}) == 1
        groups.append({**group, "operations": {"proof_portfolio": True, "external_atp_goal": True}, "arms": rows})
    write_json(args.output, groups)


if __name__ == "__main__":
    main()

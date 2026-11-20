"""Pilot the two ATP engines and the cost of Sledgehammer plus native replay."""

import argparse
import platform
from datetime import datetime, timezone
from pathlib import Path
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.atp import SOLVERS, prepare_solver, run_sledgehammer, solve_tptp
from itpeval.backends.projects import build_task
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.verification.service import verify


FIXTURES = Path(__file__).resolve().parents[2] / "itpeval/tests/fixtures/projects"
STANDALONE = {
    "socrates.p": "theorem",
    "counterexample.p": "counter_satisfiable",
    "contradictory.p": "contradictory_axioms",
}
ARMS = ("native_replay", "e", "vampire")


def benchmark_solver_reuse(prefix, *, trials=5):
    """Measure repeated executable discovery over fresh standalone processes."""
    rows = []
    for solver in SOLVERS:
        started = perf_counter()
        prepared = prepare_solver(solver, prefix=prefix)
        preparation_s = perf_counter() - started
        samples = {"discover_each": [], "prepared": []}
        for trial in range(trials):
            path = tuple(STANDALONE)[trial % len(STANDALONE)]
            source = FIXTURES / "tptp" / path
            order = tuple(samples)
            for mode in order if trial % 2 == 0 else reversed(order):
                start = perf_counter()
                if mode == "prepared":
                    result = prepared.solve(source)
                else:
                    result = solve_tptp(source, solver=solver, prefix=prefix)
                seconds = perf_counter() - start
                if result.outcome != STANDALONE[path]:
                    raise RuntimeError(f"unexpected outcome for {solver} on {path}: {result.outcome}")
                samples[mode].append(seconds)
        rows.append({"solver": solver, "preparation_s": preparation_s, "trials": trials,
                     "wall_samples_s": samples,
                     "wall_medians_s": {mode: median(seconds) for mode, seconds in samples.items()}})
    return rows


def benchmark(prefix, *, trials=3, search_timeout_s=30, solver_timeout_s=5):
    """Return a compact report and the detailed evidence behind its rows."""
    report = {"protocol": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
              "platform": platform.platform(), "python": platform.python_version(), "trials": trials,
              "search_timeout_s": search_timeout_s, "solver_timeout_s": solver_timeout_s,
              "search_trace_premises": False, "search_native_parallel_proofs": 0,
              "replay_limit": 1, "standalone": [], "hybrid": []}
    raw = {"standalone": [], "hybrid": []}
    for solver in SOLVERS:
        for relative, expected in STANDALONE.items():
            start = perf_counter()
            outcome = solve_tptp(FIXTURES / "tptp" / relative, solver=solver, prefix=prefix)
            row = {"solver": solver, "problem": relative, "expected": expected, "outcome": outcome.outcome,
                   "status": outcome.native_status, "certificate_kind": outcome.certificate_kind,
                   "native_ms": outcome.process.duration_ms, "wall_s": perf_counter() - start,
                   "problem_id": outcome.problem_id, "build": outcome.solver.to_dict()}
            report["standalone"].append(row)
            raw["standalone"].append(outcome.to_dict())

    with TemporaryDirectory(prefix="itpeval-atp-pilot-") as temp:
        start = perf_counter()
        project = prepare_project("isabelle", FIXTURES / "isabelle/hammer", prefix=prefix, cache=Path(temp))
        task = build_task(project)
        report.update(project_preparation_s=perf_counter() - start, target=task.targets[0],
                      environment_id=project.environment_id, task_id=task.task_id,
                      prover_build=project.spec.prover_build, replay_budgets=task.budgets.to_dict())
        for trial in range(trials):
            # Rotate conditions to spread startup and filesystem effects.
            shift = trial % len(ARMS)
            for arm in ARMS[shift:] + ARMS[:shift]:
                start = perf_counter()
                if arm == "native_replay":
                    outcome = verify(task, "by simp", prepared=project)
                    proof, replay, native_search = "by simp", outcome, None
                else:
                    outcome = run_sledgehammer(task, prepared=project, solver=arm, replay_limit=1,
                                               search_timeout_s=search_timeout_s, solver_timeout_s=solver_timeout_s,
                                               trace_premises=False)
                    checked = outcome.checked_proof
                    proof, replay, native_search = (checked.text if checked else None,
                                                    checked.evidence if checked else None, outcome.search)
                row = {"arm": arm, "trial": trial + 1, "wall_s": perf_counter() - start,
                       "checked": bool(replay and replay.task_success), "proof": proof,
                       "replay_native_ms": replay.duration_ms if replay else None,
                       "search_native_ms": native_search.duration_ms if native_search else None}
                report["hybrid"].append(row)
                raw["hybrid"].append({"arm": arm, "trial": trial + 1, "evidence": outcome.to_dict()})
    report["medians_s"] = {arm: median(row["wall_s"] for row in report["hybrid"] if row["arm"] == arm)
                            for arm in ARMS}
    report["standalone_reuse"] = benchmark_solver_reuse(prefix)
    return report, raw


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--raw-output", type=Path, help="optional full TSTP and replay evidence")
    parser.add_argument("--trials", type=int, default=3, help="number of rotated hybrid trials")
    parser.add_argument("--search-timeout-s", type=float, default=30)
    parser.add_argument("--solver-timeout-s", type=int, default=5)
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("trials must be positive")
    if args.raw_output is not None and args.raw_output.resolve() == args.output.resolve():
        parser.error("choose separate paths for summary and raw evidence")
    report, raw = benchmark(args.prefix, trials=args.trials, search_timeout_s=args.search_timeout_s,
                            solver_timeout_s=args.solver_timeout_s)
    write_json(args.output, report)
    if args.raw_output is not None:
        write_json(args.raw_output, raw)
    for arm, seconds in report["medians_s"].items():
        print(f"{arm}: {seconds:.3f}s median wall time")
    success = (all(row["outcome"] == row["expected"] for row in report["standalone"])
               and all(row["checked"] for row in report["hybrid"]))
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())

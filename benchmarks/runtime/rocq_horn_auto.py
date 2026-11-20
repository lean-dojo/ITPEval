"""Pilot RocqIDE premise discovery with one shared native observation per goal."""

from __future__ import annotations

import argparse
import platform
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.atp import observe_rocq_horn, prepare_solver, run_rocq_horn_search
from itpeval.backends.projects import build_task
from itpeval.core.records import digest
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json


FIXTURES = Path(__file__).resolve().parents[2] / "itpeval/tests/fixtures/projects/rocq"
CASES = (
    ("delivery", "horn", "completion.json", "Theorem", "accepted", "accepted"),
    ("global_axiom_out_of_scope", "horn-policy", "global-completion.json", "CounterSatisfiable", "not_attempted", None),
    ("local_proof_with_unauthorized_axiom", "horn-policy", "local-completion.json", "Theorem", "rejected", "policy_rejected"),
)


def benchmark(prefix, e_executable, vampire_executable):
    report = {"protocol": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
              "platform": platform.platform(), "python": platform.python_version(),
              "method": "one native RocqIDE observation per task, then independent ATP search and native replay",
              "solver_builds": {}, "tasks": []}
    raw = []
    solvers = [prepare_solver("e", executable=e_executable), prepare_solver("vampire", executable=vampire_executable)]
    for solver in solvers:
        report["solver_builds"][solver.build.solver] = solver.build.to_dict()
    with TemporaryDirectory(prefix="itpeval-rocq-horn-pilot-") as tmp:
        cache = Path(tmp)
        projects = {folder: prepare_project("rocq", FIXTURES / folder, prefix=prefix, cache=cache)
                    for folder in ("horn", "horn-policy")}
        for case, folder, manifest, expected_search, expected_replay, expected_checker in CASES:
            prepared = projects[folder]
            task = build_task(prepared, manifest)
            started = perf_counter()
            observation = observe_rocq_horn(task, prepared=prepared)
            observation_s = perf_counter() - started
            if observation.problem is None:
                raise RuntimeError(f"Rocq did not produce a Horn problem for {case}: {observation.reason}")
            observed = observation.to_dict()
            observation_id = digest(observed)
            rows = []
            report["tasks"].append({"case": case, "target": task.targets[0], "prover_build": prepared.spec.prover_build,
                                    "manifest": str(Path(folder) / manifest), "observation_id": observation_id,
                                    "observation_wall_s": observation_s, "observation": observed, "runs": rows})
            for solver in solvers:
                started = perf_counter()
                evidence = run_rocq_horn_search(task, observation.problem, prepared=prepared, solver=solver)
                wall_s = perf_counter() - started
                checker = evidence.replay.checker_outcome if evidence.replay is not None else None
                rule = evidence.replay.stderr if evidence.replay is not None else ""
                native_stdout = evidence.replay.stdout if evidence.replay is not None else ""
                expected = (expected_search, expected_replay, expected_checker)
                actual = (evidence.search.native_status, evidence.replay_outcome, checker)
                rows.append({"solver": solver.build.solver, "observation_id": observation_id,
                             "tptp_problem_id": evidence.search.problem_id, "native_status": actual[0],
                             "replay_outcome": actual[1], "checker_outcome": checker,
                             "matches_expected": actual == expected,
                             "certificate_hypotheses": evidence.certificate_hypotheses,
                             "reconstructed_hypotheses": evidence.reconstructed_hypotheses,
                             "closed_under_global_context": "Closed under the global context" in native_stdout,
                             "unauthorized_dependencies": [line.removeprefix("Unauthorized dependencies: ")
                                                           for line in rule.splitlines()
                                                           if line.startswith("Unauthorized dependencies: ")],
                             "search_native_ms": evidence.search.process.duration_ms,
                             "replay_native_ms": evidence.replay.duration_ms if evidence.replay is not None else None,
                             "search_and_replay_wall_s": wall_s})
                raw.append({"case": case, "observation_id": observation_id,
                            "evidence": replace(evidence, observation=observation).to_dict()})
    return report, raw


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--e-executable", type=Path, required=True)
    parser.add_argument("--vampire-executable", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--raw-output", type=Path, help="also store complete solver and replay evidence")
    args = parser.parse_args()
    if args.raw_output is not None and args.raw_output.resolve() == args.output.resolve():
        parser.error("choose separate paths for summary and raw evidence")
    report, raw = benchmark(args.prefix, args.e_executable, args.vampire_executable)
    write_json(args.output, report)
    if args.raw_output is not None:
        write_json(args.raw_output, raw)
    for task in report["tasks"]:
        for row in task["runs"]:
            print(task["case"], row["solver"], row["native_status"], row["replay_outcome"])
    return 0 if all(row["matches_expected"] for task in report["tasks"] for row in task["runs"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())

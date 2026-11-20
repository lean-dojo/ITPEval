"""Run both external solvers on scoped Agda holes and record native verification."""

import argparse
import platform
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.atp.agda import _search_agda_problem, observe_agda_horn
from itpeval.atp.search import prepare_solver
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.environments.cache import sha256, write_json
from itpeval.runtime.interaction import AgdaHoleSession
from itpeval.verification.policies import assemble


def benchmark(prefix, e_executable, vampire_executable):
    solvers = [prepare_solver("e", executable=e_executable, prefix=prefix),
               prepare_solver("vampire", executable=vampire_executable, prefix=prefix)]
    fixture = curated_project("agda").parent / "horn"
    report = {"schema_version": 1, "platform": platform.platform(), "python": platform.python_version(),
              "method": "One native Agda context query per goal, external solver search and standalone replay. "
                        "For the solved case, give the proposed term in an isolated Agda session and run a fresh strict check.",
              "project_inputs": {path.name: sha256(path) for path in sorted(fixture.iterdir())}, "tasks": []}
    with TemporaryDirectory(prefix="itpeval-agda-horn-") as temp:
        prepared = prepare_project("agda", fixture, cache=Path(temp), prefix=prefix)
        report["prover_build"] = prepared.spec.prover_build
        report["environment_id"] = prepared.environment_id
        for manifest in ("completion.json", "transport.json"):
            task = build_task(prepared, manifest)
            begin = perf_counter()
            observation = observe_agda_horn(task, prepared=prepared)
            observation_wall_s = perf_counter() - begin
            assert observation.problem is not None
            task_result = {"manifest": manifest, "task_id": task.task_id, "observation_wall_s": observation_wall_s,
                           "runs": []}
            for solver in solvers:
                begin = perf_counter()
                receipt = _search_agda_problem(task, observation.problem, observation=observation,
                                               prepared=prepared, solver=solver)
                row = {"search_and_replay_wall_s": perf_counter() - begin, "evidence": receipt.to_dict()}
                if manifest == "completion.json":
                    assert receipt.search.native_status == "Theorem" and receipt.replay_outcome == "accepted"
                    original = AgdaHoleSession(task, prepared)
                    begin = perf_counter()
                    initial = original.handle
                    branch = original.fork(initial)
                    handle, _ = branch.give(branch.handle, receipt.suffix)
                    final = branch.finalize(handle)
                    row["give_and_strict_verification_wall_s"] = perf_counter() - begin
                    assert final.task_success is True and final.target_preservation == "preserved"
                    assert final.obligations == ((task.targets[0], "discharged"),)
                    assert branch.candidate == receipt.candidate == task.allowed_edits[0]
                    assert assemble(task, receipt.candidate).artifact_id == final.artifact_id == receipt.replay.artifact_id
                    assert original.handle == initial and original.candidate is None
                    row["native_revision"] = handle.revision
                    row["strict_artifact_id"] = final.artifact_id
                else:
                    assert receipt.search.outcome == "counter_satisfiable" and receipt.replay is None
                    assert "equal" in receipt.observation.skipped_bindings
                task_result["runs"].append(row)
            report["tasks"].append(task_result)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("prefix", "e-executable", "vampire-executable", "output"):
        parser.add_argument("--" + option, type=Path, required=True)
    args = parser.parse_args()
    report = benchmark(args.prefix, args.e_executable, args.vampire_executable)
    write_json(args.output, report)
    for task in report["tasks"]:
        for row in task["runs"]:
            evidence = row["evidence"]
            print(task["manifest"], evidence["search"]["solver"]["solver"],
                  evidence["search"]["native_status"], evidence["replay_outcome"])


if __name__ == "__main__":
    main()

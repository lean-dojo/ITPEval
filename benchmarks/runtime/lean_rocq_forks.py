"""Compare in-memory Lean and Rocq proof branching with native checkpoint replay."""

import argparse
from hashlib import sha256
from pathlib import Path
import platform
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter
from unittest.mock import patch

from benchmarks.runtime.rocq_action_restore import _COMMANDS, _write_project
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver
from itpeval.verification.policies import assemble


def measure(prepared, actions, trials):
    task = build_task(prepared)
    parent = NativeProofDriver(task, prepared)
    for action in actions[:-1]:
        step = parent.advance(action)
        assert step.committed and step.observation.status == "open"
    checkpoint, observation = parent.checkpoint(), parent.observe()
    assert len(set(checkpoint.state_ids)) == len(actions)

    def restore():
        return NativeProofDriver.from_checkpoint(task, prepared, checkpoint)

    methods = [("native_replay", restore), ("in_memory", parent.fork)]
    samples = {name: [] for name, _ in methods}
    session_type = type(parent._session)
    native_run = session_type._run
    transactions = parser_compilations = 0
    expected_transition = artifact_id = None

    def count_run(self, *args, **kwargs):
        nonlocal transactions, parser_compilations
        transactions += 1
        if task.prover == "rocq" and not self._spans:
            parser_compilations += 1
        return native_run(self, *args, **kwargs)

    with patch.object(session_type, "_run", count_run):
        for pair in range(trials):
            for label, branch_at_checkpoint in (methods if pair % 2 == 0 else reversed(methods)):
                transactions = parser_compilations = 0
                start = perf_counter()
                branch = branch_at_checkpoint()
                initial_fork_time = perf_counter() - start
                fork_transactions, fork_parser_compilations = transactions, parser_compilations
                branch_checkpoint, branch_observation = branch.checkpoint(), branch.observe()
                transition = branch.advance(actions[-1])
                fork_and_advance_time = perf_counter() - start
                assert branch_checkpoint == checkpoint and branch_observation == observation
                assert transition.committed and transition.observation.status == "ready"
                assert branch.checkpoint().actions == actions
                assert branch.checkpoint().state_ids[:-1] == checkpoint.state_ids
                assert parent.checkpoint() == checkpoint and parent.observe() == observation
                assert (fork_transactions, transactions) == ((1, 2) if label == "native_replay" else (0, 1))
                if task.prover == "rocq":
                    assert parser_compilations == fork_parser_compilations == (label == "native_replay")
                if expected_transition is None:
                    expected_transition = transition
                assert transition == expected_transition

                final = branch.finalize()
                evidence = final.evidence
                assert evidence.task_success and evidence.completion_status == "proved"
                assert evidence.target_preservation == "preserved"
                assert evidence.artifact_id == assemble(task, final.candidate).artifact_id
                if artifact_id is None:
                    artifact_id = evidence.artifact_id
                assert evidence.artifact_id == artifact_id
                samples[label].append({"pair": pair + 1, "fork_s": initial_fork_time,
                                       "fork_and_advance_s": fork_and_advance_time,
                                       "fork_native_transactions": fork_transactions,
                                       "total_native_transactions": transactions,
                                       "fork_parser_compilations": fork_parser_compilations,
                                       "checker_outcome": evidence.checker_outcome})
    return {"prover_build": prepared.spec.prover_build, "checkpoint": checkpoint.to_dict(),
            "closing_action": actions[-1].to_dict(), "closing_observation": expected_transition.observation.to_dict(),
            "strict_artifact_id": artifact_id, "medians": {
                label: {key: median(row[key] for row in rows) for key in ("fork_s", "fork_and_advance_s")}
                for label, rows in samples.items()}, "samples": samples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--trials", default=5, type=int)
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("trial count must be positive")

    repo = Path(__file__).resolve().parents[2]
    paths = ("benchmarks/runtime/lean_rocq_forks.py", "benchmarks/runtime/rocq_action_restore.py",
             "itpeval/runtime/proof_driver.py", "itpeval/runtime/interaction.py",
             "itpeval/backends/lean4/_goals.py", "itpeval/backends/rocq/interaction.py", "itpeval/backends/rocq/_ide.py")
    source_hashes = {name: sha256((repo / name).read_bytes()).hexdigest() for name in paths}
    results, project_inputs = {}, {}
    with TemporaryDirectory(prefix="itpeval-lean-rocq-forks-") as temporary:
        rocq_project = Path(temporary) / "rocq"
        _write_project(rocq_project)
        projects = {"lean4": curated_project("lean4").parent / "action-restore", "rocq": rocq_project}
        for prover, project in projects.items():
            prepared = prepare_project(prover, project, prefix=args.prefix, cache=args.cache,
                                       project_name=f"itpeval/benchmarks/{prover}-forks", project_commit="")
            if prover == "lean4":
                actions = tuple(NativeProofAction("tactic", line.strip()) for line in
                                build_task(prepared).allowed_edits[0].splitlines())
            else:
                actions = tuple(NativeProofAction("command", command) for command in _COMMANDS)
            results[prover] = measure(prepared, actions, args.trials)
            project_inputs[prover] = {path.name: sha256(path.read_bytes()).hexdigest()
                                      for path in sorted(project.iterdir()) if path.is_file()}
    assert source_hashes == {name: sha256((repo / name).read_bytes()).hexdigest() for name in paths}
    report = {"schema_version": 1, "platform": platform.platform(), "python": platform.python_version(),
              "method": "Alternate methods on a shared host at the same committed prefix and lock. "
                        "Measure branching alone and branching followed by the same native closing action. "
                        "Compare checkpoint state identities, exact closing observations and strict proof artifacts. "
                        "Time excludes preparing the project, building the prefix and independently checking each proof. "
                        "Rocq in-memory forks retain the prior parser spans.",
              "paired_trials_per_prover": args.trials, "source_sha256": source_hashes,
              "project_input_sha256": project_inputs, "results": results}
    write_json(args.output, report)
    print({prover: row["medians"] for prover, row in results.items()})


if __name__ == "__main__":
    main()

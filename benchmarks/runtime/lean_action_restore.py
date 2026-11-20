"""Compare Lean checkpoint replay per action and in one language-server transaction."""

import argparse
from hashlib import sha256
from pathlib import Path
import platform
from statistics import median
from time import perf_counter
from unittest.mock import patch

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime import interaction, proof_driver
from itpeval.runtime.interaction import LeanTacticSession
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


def measure(prepared, trials):
    task = build_task(prepared)
    tactics = tuple(map(str.strip, task.allowed_edits[0].splitlines()))
    actions = tuple(NativeProofAction("tactic", tactic) for tactic in tactics)

    def per_action():
        driver = NativeProofDriver(task, prepared)
        observed = [driver.observe()]
        for action in actions:
            transition = driver.advance(action)
            assert transition.committed
            observed.append(transition.observation)
        return driver, observed

    original, expected = per_action()
    checkpoint = original.checkpoint()
    assert len(set(checkpoint.state_ids)) == len(actions) + 1
    assert expected[-1].status == "ready"
    assert len(actions) >= 8

    native_run = LeanTacticSession._run
    native_replay = LeanTacticSession.replay_prefix
    transactions = 0
    replayed = []

    def count_run(self, *args, **kwargs):
        nonlocal transactions
        transactions += 1
        return native_run(self, *args, **kwargs)

    def capture_replay(self, *args, **kwargs):
        observed = native_replay(self, *args, **kwargs)
        replayed.extend(observed)
        return observed

    methods = ("per_action", "single_transaction")
    samples = {method: [] for method in methods}
    artifact_id = None
    with patch.object(LeanTacticSession, "_run", count_run), patch.object(LeanTacticSession, "replay_prefix", capture_replay):
        for trial in range(trials):
            for method in methods if trial % 2 == 0 else reversed(methods):
                transactions = 0
                replayed.clear()
                start = perf_counter()
                if method == "single_transaction":
                    restored = NativeProofDriver.from_checkpoint(task, prepared, checkpoint)
                else:
                    restored, observed = per_action()
                elapsed = perf_counter() - start
                assert restored.checkpoint() == checkpoint and restored.observe() == expected[-1]
                if method == "single_transaction":
                    assert transactions == 1 and replayed == [state.native for state in expected]
                else:
                    assert transactions == len(expected) and observed == expected
                final = restored.finalize()
                evidence = final.evidence
                assert final.candidate == " <;> ".join(tactics)
                assert evidence.task_success is True and evidence.completion_status == "proved"
                assert evidence.target_preservation == "preserved" and evidence.obligations == ((task.targets[0], "discharged"),)
                assert "does not depend on any axioms" in evidence.stdout
                if artifact_id is None:
                    artifact_id = evidence.artifact_id
                assert artifact_id == evidence.artifact_id
                samples[method].append({"wall_s": elapsed, "lsp_transactions": transactions,
                                        "checker_outcome": evidence.checker_outcome})
    return {"prover_build": prepared.spec.prover_build, "checkpoint": checkpoint.to_dict(),
            "distinct_semantic_states": len(expected), "strict_artifact_id": artifact_id,
            "median_s": {method: median(row["wall_s"] for row in rows) for method, rows in samples.items()},
            "samples": samples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("prefix", "cache", "output"):
        parser.add_argument("--" + option, type=Path, required=True)
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("trial count must be positive")
    fixture = curated_project("lean4").parent / "action-restore"
    prepared = prepare_project("lean4", fixture, prefix=args.prefix, cache=args.cache,
                                project_name="itpeval/benchmarks/lean-action-restore", project_commit="")
    result = measure(prepared, args.trials)
    repo = Path(__file__).resolve().parents[2]
    paths = (Path(__file__), Path(proof_driver.__file__), Path(interaction.__file__),
             repo / "itpeval/backends/lean4/_goals.py")
    report = {"schema_version": 1, "platform": platform.platform(), "python": platform.python_version(),
              "method": "Alternate per-action replay and one Lean language-server transaction on new sessions "
                        "with the same project lock. Compare all state identities and native observations. "
                        "Timings exclude project preparation and the independent strict verification after each restore.",
              "project_inputs": {path.name: sha256(path.read_bytes()).hexdigest() for path in sorted(fixture.iterdir())},
              "source_sha256": {str(path.relative_to(repo)): sha256(path.read_bytes()).hexdigest() for path in paths},
              **result}
    write_json(args.output, report)
    print(result["median_s"])


if __name__ == "__main__":
    main()

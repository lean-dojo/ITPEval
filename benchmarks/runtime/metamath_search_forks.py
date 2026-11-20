"""Measure Metamath bounded label search with native session forks."""

import argparse
from hashlib import sha256
from pathlib import Path
import platform
from statistics import median
from time import perf_counter
from unittest.mock import patch

from itpeval.atp import session, strategies
from itpeval.backends.metamath import interaction
from itpeval.backends.metamath.interaction import MetamathProofSession
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime import proof_driver
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


def _strict(evidence):
    if evidence is None:
        return None
    result = evidence.to_dict()
    return {key: result[key] for key in ("task_id", "environment_id", "artifact_id", "execution_outcome",
                                         "checker_outcome", "task_success", "target_preservation",
                                         "completion_status", "obligations", "evidence_references")}


def _observable(suggestion):
    evidence = suggestion.evidence
    return {"outcome": suggestion.outcome, "state_id": suggestion.state_id,
            "plan": [action.to_dict() for action in evidence.plan],
            "trials": [{"action": trial.action.to_dict(), "depth": trial.depth, "outcome": trial.outcome,
                        "feedback": trial.feedback.to_dict() if trial.feedback is not None else None,
                        "verification": _strict(trial.verification)} for trial in evidence.trials]}


def measure(prepared, trials):
    assert hasattr(MetamathProofSession, "fork")
    task = build_task(prepared)
    original = NativeProofDriver(task, prepared)
    opening = NativeProofAction("assign", "distinct", step_index=1)
    assert original.advance(opening).committed
    checkpoint = original.checkpoint()

    original_fork = NativeProofDriver.fork
    run = MetamathProofSession._run
    transactions = branches = 0
    variant = ""

    def counted_run(self, *args, **kwargs):
        nonlocal transactions
        transactions += 1
        return run(self, *args, **kwargs)

    def fork(self, *, cancel=None):
        nonlocal branches
        if self.task.prover != "metamath":
            return original_fork(self, cancel=cancel)
        branches += 1
        if variant == "checkpoint_restore":
            with self._lock:
                snapshot = self.checkpoint(cancel=cancel)
                return type(self).from_checkpoint(self.task, self.prepared, snapshot,
                                                  cancel=cancel, **self._session_options)
        return original_fork(self, cancel=cancel)

    samples = {"checkpoint_restore": [], "session_fork": []}
    expected_search = expected_verification = None
    order = tuple(samples)
    for trial in range(trials):
        for variant in (order if trial % 2 == 0 else reversed(order)):
            driver = NativeProofDriver.from_checkpoint(task, prepared, checkpoint)
            transactions = branches = 0
            with patch.object(NativeProofDriver, "fork", fork), patch.object(MetamathProofSession, "_run", counted_run):
                start = perf_counter()
                suggestion = driver.suggest_atp(solver="native", timeout_s=30, max_trials=32)
                wall = perf_counter() - start
            assert driver.checkpoint() == checkpoint
            observed = _observable(suggestion)
            assert suggestion.outcome == "progress" and len(suggestion.evidence.plan) == 2
            assert any(row["outcome"] == "rejected" for row in observed["trials"])
            assert observed["trials"][-1]["outcome"] == "accepted"
            assert observed["trials"][-1]["verification"]["task_success"] is True
            assert branches == len(observed["trials"]) + 1
            assert transactions == len(observed["trials"]) + (branches if variant == "checkpoint_restore" else 0)
            if expected_search is None:
                expected_search = observed
            assert observed == expected_search

            for action in suggestion.evidence.plan:
                assert driver.advance(action).committed
            final = driver.finalize()
            assert final.candidate == "vx vy distinct" and final.evidence.task_success is True
            assert final.evidence.artifact_id == observed["trials"][-1]["verification"]["artifact_id"]
            verification = _strict(final.evidence)
            if expected_verification is None:
                expected_verification = verification
            assert verification == expected_verification
            samples[variant].append({"wall_s": wall, "proof_assistant_transactions": transactions,
                                     "fork_calls": branches, "strict_recheck": final.evidence.checker_outcome})

    return {"prover_build": prepared.spec.prover_build, "checkpoint": checkpoint.to_dict(),
            "search": expected_search, "strict_verification": expected_verification, "samples": samples,
            "median_s": {label: median(row["wall_s"] for row in rows) for label, rows in samples.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("prefix", "cache", "output"):
        parser.add_argument("--" + option, type=Path, required=True)
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("trial count must be positive")
    project = curated_project("metamath")
    prepared = prepare_project("metamath", project, prefix=args.prefix, cache=args.cache)
    paths = (Path(__file__), Path(interaction.__file__), Path(proof_driver.__file__), Path(strategies.__file__),
             Path(session.__file__), project / "hello.mm", project / "completion.json")

    def source_hashes():
        root = Path(__file__).resolve().parents[2]
        return {str(path.resolve().relative_to(root)): sha256(path.read_bytes()).hexdigest() for path in paths}

    source = source_hashes()
    result = measure(prepared, args.trials)
    assert source == source_hashes()
    report = {"schema_version": 1, "platform": platform.platform(), "python": platform.python_version(),
              "method": "Alternate bounded native label searches from the same reviewed checkpoint. The baseline "
                        "uses checkpoint restoration for every Metamath fork. Compare plans, trial outcomes, exact "
                        "native feedback and strict proof artifact identities. Timings include proof verification "
                        "performed by search and exclude the independent replay and strict recheck after each search.",
              "source_sha256": source, **result}
    write_json(args.output, report)
    print(result["median_s"])


if __name__ == "__main__":
    main()

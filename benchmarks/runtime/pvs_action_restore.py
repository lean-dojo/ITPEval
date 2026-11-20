"""Compare per-action PVS restoration with replay in a single transaction."""

import argparse
from pathlib import Path
from statistics import median
from time import perf_counter

from itpeval.backends.registry import curated_project, get_backend
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ("prefix", "cache", "output"):
        parser.add_argument("--" + argument, type=Path, required=True)
    args = parser.parse_args()
    project = curated_project("pvs").parent / "interaction"
    prepared = prepare_project("pvs", project, prefix=args.prefix, cache=args.cache)
    task = get_backend("pvs").build_task(prepared)
    original = NativeProofDriver(task, prepared)
    for command in ("(skosimp)", "(split)", "(postpone)", "(grind)", "(grind)"):
        assert original.advance(NativeProofAction("command", command)).committed
    snapshot = original.checkpoint()

    def per_action():
        driver = NativeProofDriver(task, prepared)
        assert driver.observe().state_id == snapshot.state_ids[0]
        for step, state_id in zip(snapshot.actions, snapshot.state_ids[1:]):
            transition = driver.advance(step)
            assert transition.committed and transition.observation.state_id == state_id
        return driver

    def one_replay():
        return NativeProofDriver.from_checkpoint(task, prepared, snapshot)

    samples = {"per_action": [], "single_transaction": []}
    methods = [("per_action", per_action), ("single_transaction", one_replay)]
    for trial in range(5):
        for label, launch in (methods if trial % 2 == 0 else reversed(methods)):
            before = perf_counter()
            restored = launch()
            samples[label].append(perf_counter() - before)
            assert restored.checkpoint() == snapshot and restored.observe().status == "ready"
    evidence = restored.finalize(proof_fragment=task.allowed_edits[0]).evidence
    assert evidence.task_success is True
    medians = {label: median(seconds) for label, seconds in samples.items()}
    report = {"schema_version": 1, "prover": "pvs", "prover_build": prepared.spec.prover_build,
              "environment_id": task.environment_id, "task_id": task.task_id, "checkpoint": snapshot.to_dict(),
              "time_s": samples, "median_s": medians, "replayed_states_per_trial": len(snapshot.state_ids),
              "checker_outcome": evidence.checker_outcome, "artifact_id": evidence.artifact_id}
    write_json(args.output, report)
    print(medians)


if __name__ == "__main__":
    main()

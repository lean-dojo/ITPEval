"""Compare per-action ACL2 and Metamath checkpoint replay with a single native restore."""

import argparse
from hashlib import sha256
from pathlib import Path
import platform
from statistics import median
from time import perf_counter
from unittest.mock import patch

from itpeval.backends.registry import curated_project, get_backend
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime import proof_driver
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


_ACTIONS = {
    "acl2": tuple(NativeProofAction("command", command) for command in ("s", "undo", "s")),
    "metamath": tuple(NativeProofAction("assign", label, step_index=index)
                      for index, label in ((1, "distinct"), (1, "vx"), (2, "vy"))),
}


def measure(prover, prefix, cache, trials):
    project = curated_project(prover)
    if prover == "acl2":
        project = project.parent / "interaction"
    prepared = prepare_project(prover, project, prefix=prefix, cache=cache)
    task = get_backend(prover).build_task(prepared)
    original = NativeProofDriver(task, prepared)
    expected = [original.observe()]
    for action in _ACTIONS[prover]:
        step = original.advance(action)
        assert step.committed
        expected.append(step.observation)
    checkpoint = original.checkpoint()

    def per_action():
        driver = NativeProofDriver(task, prepared)
        observations = [driver.observe()]
        for action in checkpoint.actions:
            transition = driver.advance(action)
            assert transition.committed
            observations.append(transition.observation)
        assert observations == expected
        return driver

    def one_transaction():
        return NativeProofDriver.from_checkpoint(task, prepared, checkpoint)

    cls = type(original._session)
    native = cls._run
    call_count = 0

    def counted(self, *args, **kwargs):
        nonlocal call_count
        call_count += 1
        return native(self, *args, **kwargs)

    samples = {"per_action": [], "single_transaction": []}
    methods = [("per_action", per_action), ("single_transaction", one_transaction)]
    with patch.object(cls, "_run", counted):
        for trial in range(trials):
            for label, restore in (methods if trial % 2 == 0 else reversed(methods)):
                call_count = 0
                start = perf_counter()
                restored = restore()
                restore_time = perf_counter() - start
                assert restored.checkpoint() == checkpoint and restored.observe() == expected[-1]
                assert call_count == (len(expected) if label == "per_action" else 1)
                samples[label].append({"wall_s": restore_time, "native_transactions": call_count})
    evidence = restored.finalize().evidence
    assert evidence.task_success is True
    backend = Path(proof_driver.__file__).parents[1] / "backends" / prover / "interaction.py"
    return {"prover_build": prepared.spec.prover_build, "checkpoint": checkpoint.to_dict(),
            "backend_sha256": sha256(backend.read_bytes()).hexdigest(),
            "checker_outcome": evidence.checker_outcome, "artifact_id": evidence.artifact_id,
            "median_s": {label: median(row["wall_s"] for row in rows) for label, rows in samples.items()},
            "samples": samples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("prefix", "cache", "output"):
        parser.add_argument("--" + option, type=Path, required=True)
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("trial count must be positive")
    result = {"schema_version": 1, "host": platform.platform(), "python": platform.python_version(),
              "method": "Alternate restores starting from a new native session with the same prepared lock. "
                        "Compare the initial state and all saved state identities. Exclude preparation and final verification.",
              "source_sha256": {path.name: sha256(path.read_bytes()).hexdigest()
                                for path in (Path(proof_driver.__file__), Path(__file__))},
              "provers": {}}
    for prover in _ACTIONS:
        result["provers"][prover] = measure(prover, args.prefix, args.cache, args.trials)
        print(prover, result["provers"][prover]["median_s"], flush=True)
    write_json(args.output, result)


if __name__ == "__main__":
    main()

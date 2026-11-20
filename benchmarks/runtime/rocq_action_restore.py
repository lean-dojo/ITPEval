"""Compare per-command Rocq checkpoint restoration with one IDE transaction."""

import argparse
import json
from hashlib import sha256
from pathlib import Path
import platform
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter
from unittest.mock import patch

from itpeval.backends.projects import CompletionManifest, build_task
from itpeval.backends.rocq import interaction
from itpeval.backends.rocq.interaction import RocqIDESession
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime import proof_driver
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


_COMMANDS = ("intro p.", "intro q.", "intro r.", "intro s.", "split.", "exact s.",
             "split.", "exact r.", "split.", "exact q.", "exact p.")


def _write_project(directory):
    directory.mkdir()
    proposition = r"P -> Q -> R -> S -> S /\ (R /\ (Q /\ P))"
    fragment = "\n".join(_COMMANDS)
    anchor = f"Theorem itpeval_target : {proposition}.\nProof.\n{fragment}\nQed."
    source = f"Section LocalContext.\nVariables P Q R S : Prop.\n{anchor}\nEnd LocalContext.\n"
    manifest = CompletionManifest(
        entrypoint="hello.v", files=("hello.v",), anchor=anchor, target="itpeval_target",
        statement=f"forall P Q R S : Prop, {proposition}", proof_slot=fragment,
        allowed_edits=(fragment, "exact I."), proof_atoms=tuple(dict.fromkeys(c[:-1] for c in _COMMANDS)),
        observer_anchor="End LocalContext.",
    )
    (directory / "hello.v").write_text(source, encoding="utf-8")
    (directory / "completion.json").write_text(json.dumps(manifest.to_dict(), indent=2) + "\n", encoding="utf-8")


def measure(prepared, trials):
    task = build_task(prepared)
    original = NativeProofDriver(task, prepared)
    expected = [original.observe()]
    for command in _COMMANDS:
        step = original.advance(NativeProofAction("command", command))
        assert step.committed
        expected.append(step.observation)
    checkpoint = original.checkpoint()
    assert len(set(checkpoint.state_ids)) == len(_COMMANDS) + 1
    assert expected[-1].status == "ready"

    def per_command():
        driver = NativeProofDriver(task, prepared)
        observed = [driver.observe()]
        for action in checkpoint.actions:
            step = driver.advance(action)
            assert step.committed
            observed.append(step.observation)
        assert observed == expected
        return driver

    def batch():
        return NativeProofDriver.from_checkpoint(task, prepared, checkpoint)

    native_run = RocqIDESession._run
    native_replay = RocqIDESession.replay_prefix
    transaction_count = compilation_count = 0
    replayed_states = []

    def count_run(self, *args, **kwargs):
        nonlocal transaction_count, compilation_count
        transaction_count += 1
        # The IDE helper compiles once for parser positions when spans are absent.
        compilation_count += not self._spans
        return native_run(self, *args, **kwargs)

    def capture_replay(self, *args, **kwargs):
        states = native_replay(self, *args, **kwargs)
        replayed_states.extend(states)
        return states

    samples = {"per_command": [], "single_transaction": []}
    methods = [("per_command", per_command), ("single_transaction", batch)]
    artifact_id = None
    with patch.object(RocqIDESession, "_run", count_run), patch.object(RocqIDESession, "replay_prefix", capture_replay):
        for trial in range(trials):
            for label, restore in (methods if trial % 2 == 0 else reversed(methods)):
                transaction_count = compilation_count = 0
                replayed_states.clear()
                start = perf_counter()
                restored = restore()
                elapsed = perf_counter() - start
                assert restored.checkpoint() == checkpoint and restored.observe() == expected[-1]
                assert transaction_count == (len(expected) if label == "per_command" else 1)
                assert compilation_count == 1
                if label == "single_transaction":
                    assert [state.to_dict() for state in replayed_states] == [state.native for state in expected]
                final = restored.finalize()
                evidence = final.evidence
                assert final.candidate == "\n".join(_COMMANDS)
                assert evidence.task_success is True and evidence.completion_status == "proved"
                assert evidence.target_preservation == "preserved" and evidence.obligations == ((task.targets[0], "discharged"),)
                if artifact_id is None:
                    artifact_id = evidence.artifact_id
                assert artifact_id == evidence.artifact_id
                samples[label].append({"wall_s": elapsed, "ide_transactions": transaction_count,
                                       "parser_compilations": compilation_count, "checker_outcome": evidence.checker_outcome})
    return {"prover_build": prepared.spec.prover_build, "checkpoint": checkpoint.to_dict(),
            "distinct_semantic_states": len(expected), "strict_artifact_id": artifact_id,
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
    with TemporaryDirectory(prefix="itpeval-rocq-action-restore-") as temporary:
        project = Path(temporary) / "project"
        _write_project(project)
        prepared = prepare_project("rocq", project, prefix=args.prefix, cache=args.cache,
                                    project_name="itpeval/benchmarks/rocq-action-restore", project_commit="")
        result = measure(prepared, args.trials)
        paths = (Path(__file__), Path(proof_driver.__file__), Path(interaction.__file__),
                 Path(interaction.__file__).with_name("_ide.py"))
        report = {"schema_version": 1, "platform": platform.platform(), "python": platform.python_version(),
                  "method": "Alternate the prior per-command restore and one IDE transaction on new sessions "
                            "with the same project lock. Check all state identities and exact native records. "
                            "Each fresh restore compiles once to discover source spans. Timings exclude project "
                            "preparation and fresh strict verification, which is run after every restore.",
                  "project_inputs": {path.name: sha256(path.read_bytes()).hexdigest() for path in sorted(project.iterdir())},
                  "source_sha256": {str(path.relative_to(Path(__file__).resolve().parents[2])): sha256(path.read_bytes()).hexdigest()
                                    for path in paths}, **result}
    write_json(args.output, report)
    print(result["median_s"])


if __name__ == "__main__":
    main()

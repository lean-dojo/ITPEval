"""Verify native PVS sequents, branch replay, and separate ProofLite checks."""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.backends.projects import build_task
from itpeval.backends.pvs.interaction import PVSProofCheckpoint, PVSProofSession
from itpeval.backends.registry import ROOT
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json


_FIXTURE = ROOT / "tests/fixtures/projects/pvs/interaction"


def _rejected(call):
    try:
        call()
    except ValueError:
        return True
    return False


def _focus(state):
    focused = state.focused
    if focused is None:
        return None
    return {"theory": state.theory, "path": focused.path, "label": focused.label,
            "antecedents": [formula.text for formula in focused.sequent.antecedents],
            "succedents": [formula.text for formula in focused.sequent.succedents]}


def _finish(receipt):
    result = receipt.verification
    return {"theory": receipt.theory, "target": receipt.target, "proof_fragment": receipt.proof_fragment,
            "match": receipt.match, "commands": receipt.checkpoint.commands,
            "artifact_id": result.artifact_id, "outcome": result.checker_outcome, "obligations": result.obligations}


def _negative_probes(prefix, cache):
    with TemporaryDirectory(prefix="itpeval-pvs-session-checks-") as directory:
        root = Path(directory)
        duplicate = root / "duplicate"
        shutil.copytree(_FIXTURE, duplicate)
        entry = duplicate / "hello.pvs"
        source = entry.read_text(encoding="utf-8")
        first = "hello: THEORY\nBEGIN\n  itpeval_target: LEMMA TRUE\nEND hello\n\n"
        entry.write_text(first + source.replace("hello: THEORY", "branch_goals: THEORY")
                         .replace("END hello", "END branch_goals"), encoding="utf-8")
        manifest = duplicate / "completion.json"
        data = json.loads(manifest.read_text(encoding="utf-8"))
        unknown = "(not_an_itpeval_rule)"
        data["proof_atoms"].append(unknown)
        manifest.write_text(json.dumps(data), encoding="utf-8")
        lock = prepare_project("pvs", duplicate, prefix=prefix, cache=cache)
        task = build_task(lock)
        trial = PVSProofSession(task, lock)
        handle = trial.handle
        initial = trial.inspect(handle)
        before = trial.checkpoint(handle)
        unchanged, failure = trial.step(handle, unknown)
        rejected = bool(unchanged == handle and failure.error and "Ill-formed rule" in failure.error
                        and trial.checkpoint(handle) == before and trial.inspect(handle) == initial)

        unfinished = root / "unfinished-tcc"
        shutil.copytree(_FIXTURE, unfinished)
        (unfinished / "hello.pvs").write_text(source.replace("( GRIND )", "( SKIP )", 1), encoding="utf-8")
        lock = prepare_project("pvs", unfinished, prefix=prefix, cache=cache)
        task = build_task(lock)
        trial = PVSProofSession(task, lock)
        completed, state = trial.step(trial.handle, "(grind)")
        independent = trial.finalize(completed)
        verdict = independent.verification
        blocked = (state.status == "proved" and verdict.task_success is False
                   and verdict.checker_outcome == "incomplete" and "twice_TCC1" in verdict.stdout
                   and "unfinished" in verdict.stdout)
        return {
            "correct_theory": initial.theory == "branch_goals"
            and "twice" in initial.focused.sequent.succedents[0].text,
            "native_error_preserves_prefix": rejected,
            "unfinished_tcc_blocks_finalization": blocked,
            "duplicate_name_focus": _focus(initial),
            "native_error": failure.error,
            "unfinished_tcc": _finish(independent),
        }


def exercise(prefix, cache):
    prepared = prepare_project("pvs", _FIXTURE, prefix=prefix, cache=cache)
    task = build_task(prepared)
    session = PVSProofSession(task, prepared)
    start = perf_counter()
    initial_handle = session.handle
    initial = session.inspect(initial_handle)
    inspect_s = perf_counter() - start
    start = perf_counter()
    handle, no_change = session.step(initial_handle, "(split)")
    handle, introduced = session.step(handle, "(skosimp)")
    split_handle, split = session.step(handle, "(split)")
    advance_s = perf_counter() - start
    left, right = session.fork(split_handle), session.fork(split_handle)
    left_handle, left_closed = left.step(left.handle, "(grind)")
    saved = left.checkpoint(left_handle)
    payload = json.loads(json.dumps(saved.to_dict()))
    start = perf_counter()
    restored = PVSProofSession.from_checkpoint(task, prepared, PVSProofCheckpoint.from_dict(payload))
    restore_s = perf_counter() - start
    restored_state = restored.inspect(restored.handle)
    done, left_proved = restored.step(restored.handle, "(grind)")
    _, postponed = right.step(right.handle, "(postpone)")
    _, right_closed = right.step(right.handle, "(grind)")
    _, right_proved = right.step(right.handle, "(grind)")
    start = perf_counter()
    final = restored.finalize(done, task.allowed_edits[0])
    finalize_s = perf_counter() - start
    checks = _negative_probes(prefix, cache)
    operations = {
        "inspect_goals": initial.status == "init" and "FORALL" in initial.focused.sequent.succedents[0].text
        and checks["correct_theory"],
        "step_proof": "n!1" in introduced.focused.sequent.succedents[0].text
        and split.focused.label.endswith(".1") and left_proved.status == right_proved.status == "proved",
        "proof_branching": session.inspect(split_handle) == split
        and left_closed.focused.path == postponed.focused.path != right_closed.focused.path
        and right_closed.focused.path == split.focused.path,
        "checkpoint_proof": restored_state.state_digest == saved.state_digest
        and restored.checkpoint(done).commands == (*saved.commands, "(grind)"),
        "action_traces": any("No change on" in message for event in no_change.events for message in event.commentary)
        and _focus(no_change) == _focus(initial) and saved.commands[0] == "(split)"
        and any("Splitting conjunctions" in event.action for event in split.events),
        "misuse_rejected": checks["native_error_preserves_prefix"]
        and _rejected(lambda: session.inspect(initial_handle))
        and _rejected(lambda: session.inspect(left_handle))
        and _rejected(lambda: restored.step(done, "(skip)"))
        and _rejected(lambda: session.step(split_handle, "(quit)"))
        and _rejected(lambda: PVSProofSession.from_checkpoint(
            task, prepared, replace(saved, state_digest="incorrect"))),
        "independent_finalization": final.task_success is True and final.match == "same_locked_target"
        and dict(final.verification.obligations).get("twice_TCC1") == "discharged"
        and checks["unfinished_tcc_blocks_finalization"],
    }
    return {"prover": task.prover, "environment_id": task.environment_id, "task_id": task.task_id,
            "prover_build": prepared.spec.prover_build, "version": prepared.build["version"],
            "operations": operations, "timings_s": {"inspect": inspect_s, "three_commands": advance_s,
                                                    "restore": restore_s, "independent_check": finalize_s},
            "evidence": {"initial": _focus(initial), "split": _focus(split), "left_closed": _focus(left_closed),
                         "right_first": _focus(postponed), "right_closed": _focus(right_closed),
                         "checkpoint": saved.to_dict(), "verified": _finish(final), **checks}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = exercise(args.prefix, args.cache)
    write_json(args.output, report)
    print(report["operations"])
    return 0 if all(report["operations"].values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())

"""Check native HOL goal edits, independent branches, and portable tactic replay."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path

from itpeval.backends.hol_tactics import HOLProofCheckpoint, HOLProofSession, HOLTactic
from itpeval.backends.projects import build_task
from itpeval.backends.registry import ROOT
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.verification.policies import assemble


def rejects(action):
    try:
        action()
    except ValueError:
        return True
    return False


def exercise(prover, prefix, cache):
    prepared = prepare_project(prover, ROOT / "tests/fixtures/projects" / prover / "interaction",
                               prefix=prefix, cache=cache)
    task = build_task(prepared)
    implication = HOLTactic((), "DISCH_TAC", 1)
    conjunction = HOLTactic((0,), "CONJ_TAC", 2)
    left = HOLTactic((0, 0), "ASM_REWRITE_TAC []", 0)
    right = HOLTactic((0, 1), "ASM_REWRITE_TAC []", 0)
    checkpoint = HOLProofCheckpoint(task.task_id, prepared.environment_id, (implication, conjunction))
    session = HOLProofSession(task, prepared)

    def restore(actions):
        checkpoint = HOLProofCheckpoint(task.task_id, prepared.environment_id, actions)
        saved = json.loads(json.dumps(checkpoint.to_dict()))
        return HOLProofSession.from_checkpoint(task, prepared, HOLProofCheckpoint.from_dict(saved))

    def finish():
        closed = restore((*checkpoint.actions, right, left))
        return closed, closed.finalize(closed.handle)

    with ThreadPoolExecutor(max_workers=4) as pool:
        opening = pool.submit(session.inspect, session.handle)
        finalizing = pool.submit(finish)
        split = restore(checkpoint.actions)
        split_state = split.inspect(split.handle)
        parent = split.handle
        a, b, invalid = (split.fork(parent) for _ in range(3))
        before_b = b.handle
        failing = pool.submit(invalid.step, invalid.handle, left.path, "NO_TAC")
        solving_left = pool.submit(a.step, a.handle, left.path, left.text)
        solving_right = pool.submit(b.step, b.handle, right.path, right.text)
        # Foreign handles and unreviewed tactics must be rejected before use.
        foreign = rejects(lambda: a.inspect(parent))
        missing_goal = rejects(lambda: split.step(parent, (8,), "ALL_TAC"))
        unreviewed = rejects(lambda: split.step(parent, right.path, "admit"))
        opened = opening.result()
        failed_handle, failure = failing.result()
        handle_a, after_left = solving_left.result()
        handle_b, after_right = solving_right.result()
        final, evidence = finalizing.result()

    stale = rejects(lambda: b.inspect(before_b)) and rejects(lambda: b.step(handle_b, right.path, right.text))
    artifact_id = assemble(task, final.candidate).artifact_id
    operations = {
        "inspect_goals": len(opened.goals) == 1 and opened.goals[0].path == ()
        and [g.hypotheses for g in split_state.goals] == [("p",), ("p",)],
        "step_proof": bool([g.path for g in after_left.goals] == [right.path]
                           and [g.path for g in after_right.goals] == [left.path]
                           and failure.diagnostic and failure.goals == split_state.goals),
        "proof_branching": bool(split.inspect(parent) == split_state
                                and failed_handle == invalid.handle and invalid.checkpoint(failed_handle) == checkpoint
                                and a.checkpoint(handle_a).actions[-1] == left
                                and b.checkpoint(handle_b).actions[-1] == right
                                and len({parent.session_id, handle_a.session_id, handle_b.session_id}) == 3),
        "checkpoint_proof": bool(not final.inspect(final.handle).goals and evidence.task_success is True
                                 and evidence.artifact_id == artifact_id
                                 and final.checkpoint(final.handle).actions == (*checkpoint.actions, right, left)),
        "misuse_rejected": foreign and missing_goal and unreviewed and stale,
    }
    return {"prover": prover, "version": prepared.build["version"],
            "environment_id": task.environment_id, "task_id": task.task_id,
            "prover_build": prepared.spec.prover_build, "operations": operations,
            "evidence": {"initial": opened.to_dict(), "split": split_state.to_dict(),
                         "after_left": after_left.to_dict(), "after_right": after_right.to_dict(),
                         "failed": failure.to_dict(), "checkpoint": final.checkpoint(final.handle).to_dict(),
                         "candidate": final.candidate, "verified": evidence.checker_outcome,
                         "verified_artifact_id": evidence.artifact_id}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--prover", action="append", choices=("hol4", "hol-light"))
    args = parser.parse_args()
    reports = []
    for prover in args.prover or ("hol4", "hol-light"):
        report = exercise(prover, args.prefix, args.cache)
        print(prover, report["operations"], flush=True)
        reports.append(report)
    write_json(args.output, reports)
    return 0 if all(all(report["operations"].values()) for report in reports) else 1


if __name__ == "__main__":
    raise SystemExit(main())

"""Exercise native ACL2, Agda, Isabelle, Metamath, Mizar and Rocq proof feedback."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from itpeval.backends.acl2.interaction import ACL2ProofBuilderSession
from itpeval.backends.isabelle.interaction import IsabelleProofSession
from itpeval.backends.metamath.interaction import MetamathProofSession
from itpeval.backends.mizar.diagnostics import proof_trace
from itpeval.backends.projects import build_task
from itpeval.backends.registry import ROOT, curated_project
from itpeval.backends.rocq.interaction import RocqIDESession
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import AgdaHoleSession
from itpeval.verification.policies import assemble
from itpeval.verification.service import verify


def acl2(task, prepared):
    session = ACL2ProofBuilderSession(task, prepared)
    initial = session.inspect(session.handle)
    parent = session.handle
    handle, failed = session.step(parent, "demote")
    handle, solved = session.step(handle, "s")
    accepted = session.finalize(handle)
    incomplete = verify(task, task.allowed_edits[1], prepared=prepared)
    return {
        "inspect_goals": initial.goals == ("MAIN",) and "CAR" in initial.focused_term,
        "step_proof": failed.goals == initial.goals and handle == parent and solved.complete and accepted.task_success is True
        and incomplete.task_success is False,
    }, {
        "initial": initial.to_dict(), "failed": failed.to_dict(), "solved": solved.to_dict(),
        "instructions": session.candidate, "verified": accepted.checker_outcome,
        "incomplete": incomplete.checker_outcome,
    }


def agda(task, prepared):
    session = AgdaHoleSession(task, prepared)
    handle = session.handle
    goal = session.goal_context(handle)
    clauses = session.case_split(handle, "x")
    unchanged, failed = session.give(handle, "Bool")
    revised, events = session.give(unchanged, "x")
    final = session.finalize(revised)
    failed_path = next(event["filepath"] for event in failed if event["kind"] == "JumpToError")
    errors = [event["info"]["error"]["message"].replace(failed_path, goal.source_path)
              for event in failed if event.get("info", {}).get("kind") == "Error"]
    refinement = [event for event in events if event["kind"] == "GiveAction"]
    return {
        "inspect_goals": goal.expected_type == "Bool"
        and any(b.name == "x" and b.term == "Bool" and b.in_scope for b in goal.bindings),
        "refine_hole": bool(unchanged == handle and "UnequalTypes" in " ".join(errors)
                            and revised != unchanged and refinement and final.task_success is True),
        "case_split": clauses == ["ident false = ?", "ident true = ?"],
    }, {
        "goal": goal.to_dict(), "clauses": clauses, "errors": errors, "refinement": refinement,
        "verified": final.checker_outcome,
    }


def isabelle(task, prepared):
    session = IsabelleProofSession(task, prepared)
    handle = session.handle
    initial = session.inspect(handle)
    unchanged, failed = session.step(handle, task.allowed_edits[1])
    still_open = session.finalize(unchanged)
    final, closed = session.step(unchanged, task.allowed_edits[0])
    retained, rejected_edit = session.step(final, task.allowed_edits[1])
    checked = session.finalize(retained)
    return {
        "inspect_goals": len(initial.goals) == 1 and initial.goals[0].subgoal_count == 1,
        "step_proof": bool(unchanged == handle and failed.diagnostic and still_open.checker_outcome == "incomplete"
                           and retained == final and rejected_edit.diagnostic and checked.task_success is True
                           and [goal.subgoal_count for goal in closed.goals] == [1, 2, 1, 0]
                           and checked.artifact_id == assemble(task, task.allowed_edits[0]).artifact_id),
    }, {"initial": initial.to_dict(), "rejected": failed.to_dict(), "closed": closed.to_dict(),
        "after_first_rejection": still_open.checker_outcome, "after_second_rejection": checked.checker_outcome,
        "verified_artifact_id": checked.artifact_id}


def metamath(task, prepared):
    session = MetamathProofSession(task, prepared)
    initial = session.inspect(session.handle)
    states = [initial.to_dict()]
    handle = session.handle
    for index, label in ((1, "distinct"), (1, "vx"), (2, "vx"), (2, "vy")):
        previous = handle
        handle, state = session.assign(previous, index, label)
        if (index, label) == (2, "vx"):
            assert handle == previous
        states.append(state.to_dict())
    accepted = session.finalize(handle)
    rejected = verify(task, task.allowed_edits[1], prepared=prepared)
    return {
        "inspect_goals": len(initial.open_steps) == 1 and initial.open_steps[0].expression == "|- pair x y",
        "step_proof": not state.open_steps and accepted.task_success is True and rejected.task_success is False
        and "cannot be unified" in states[3]["diagnostic"],
    }, {"states": states, "verified": accepted.checker_outcome, "invalid": rejected.checker_outcome}


def mizar(task, prepared):
    good, bad = task.allowed_edits[:2]
    accepted = proof_trace(task, good, prepared=prepared)
    rejected = proof_trace(task, bad, prepared=prepared)
    replay = verify(task, good, prepared=prepared)
    return {
        "inspect_goals": accepted.theses[0].formula_kind == "For",
        "action_traces": accepted.article_checked and replay.task_success is True
        and accepted.theses[-1].formula_kind == "Verum"
        and not rejected.article_checked and rejected.theses[-1].formula_kind == "ErrorFrm"
        and any(d.error_code == 51 and d.message for d in rejected.diagnostics),
    }, {"accepted": accepted.to_dict(), "rejected": rejected.to_dict(), "verified": replay.checker_outcome}


def rocq(task, prepared):
    session = RocqIDESession(task, prepared)
    handle = session.handle
    initial = session.inspect(handle)
    unchanged, failure = session.step(handle, "exact I.")
    updated, introduction = session.step(unchanged, "intro p.")
    final, closed = session.step(updated, "exact p.")
    checked = session.finalize(final)
    return {
        "inspect_goals": bool(initial.goals and "Prop" in initial.goals["focused"])
        and set(initial.goals) == {"focused", "background", "shelved", "given_up"},
        "step_proof": bool(unchanged == handle and failure.error and closed.complete
                           and checked.task_success is True),
    }, {"initial": initial.to_dict(), "rejected": failure.to_dict(), "introduced": introduction.to_dict(),
        "closed": closed.to_dict(), "verified": checked.checker_outcome, "candidate": session.candidate}


PROBES = {"acl2": acl2, "agda": agda, "isabelle": isabelle, "metamath": metamath, "mizar": mizar, "rocq": rocq}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--prover", action="append", choices=PROBES)
    args = parser.parse_args()
    reports = []
    for prover in args.prover or PROBES:
        if prover in {"acl2", "agda", "isabelle"}:
            project = ROOT / "tests/fixtures/projects" / prover / "interaction"
        else:
            project = curated_project(prover)
        prepared = prepare_project(prover, project, prefix=args.prefix, cache=args.cache)
        task = build_task(prepared)
        operations, evidence = PROBES[prover](task, prepared)
        reports.append({"prover": prover, "task_id": task.task_id, "environment_id": prepared.environment_id,
                        "prover_build": prepared.spec.prover_build, "version": prepared.build["version"],
                        "operations": operations, "evidence": evidence})
        print(prover, operations)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(reports, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return 0 if all(all(row["operations"].values()) for row in reports) else 1


if __name__ == "__main__":
    raise SystemExit(main())

"""Search a typed PVS sequent with a local ATP and replay a reviewed strategy."""

from __future__ import annotations

from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic

from itpeval.backends.pvs.interaction import PVSProofSession, review_pvs_automation
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver
from itpeval.verification.fragments import permitted

from .ground import horn_budgets
from .search import PreparedSolver
from .strategies import NativeStrategyEvidence, StrategyTrial, _Deadline


def _tptp(observation):
    def atom(row):
        return f"p{row['atom']}"

    lines = []
    for premise in observation["premises"]:
        head = atom(premise["consequent"])
        body = " & ".join(atom(item) for item in premise["antecedents"])
        formula = f"(({body}) => {head})" if body else head
        lines.append(f"fof(premise_{-premise['label']}, axiom, {formula}).")
    lines.append(f"fof(goal, conjecture, {atom(observation['conclusion'])}).")
    return "\n".join(lines) + "\n"


def search_pvs_horn(driver: NativeProofDriver, *, solver: PreparedSolver,
                    proof_fragment: str | None = None, timeout_s: float | None = None,
                    cancel=None) -> NativeStrategyEvidence:
    """Export a focused Boolean-skolem Horn query and independently replay PVS.

    Only visible local antecedents in the supported fragment become TPTP
    axioms. The original driver is preserved. A theorem status permits trying
    a reviewed ``(grind)`` on a private native branch. Reaching a pending
    sibling records progress. Complete acceptance requires an independent
    check of the locked theorem and its TCCs.
    """
    task = driver.task
    if not isinstance(driver._session, PVSProofSession):
        raise TypeError("expected a native PVS proof driver")
    timeout = horn_budgets(task.budgets, timeout_s).timeout_s
    start = monotonic()
    deadline = _Deadline(timeout, cancel)
    action = NativeProofAction("command", "(grind)")
    probe = {}
    trials = []

    def result(outcome, *, step=None, final=None):
        return NativeStrategyEvidence(
            task.task_id, task.environment_id, task.targets[0], "pvs", "external_horn", outcome,
            1, timeout, round((monotonic() - start) * 1000), tuple(trials),
            action if step else None, step.observation if step else None,
            (action,) if step else (), final, probe or None,
        )

    if not permitted("pvs", action.text, task.allowed_edits + task.proof_atoms, task.proof_atoms):
        return result("outside_task_policy")
    review_pvs_automation(task, action.text, proof_fragment=proof_fragment)
    if deadline.is_set():
        return result(deadline.outcome)

    try:
        branch = driver.fork(cancel=deadline)
        before = branch.observe(cancel=deadline)
        if before.status != "open":
            raise ValueError("PVS Horn search requires an open focused sequent")
        session = branch._session
        observation = session.observe_horn(session.handle, cancel=deadline)
        probe.update(state_id=before.state_id, observation=observation)
        if deadline.is_set() or observation["unsupported"] is not None:
            return result(deadline.outcome or "unsupported_goal")

        tptp = _tptp(observation)
        probe["tptp"] = tptp
        with TemporaryDirectory(prefix="itpeval-pvs-horn-") as directory:
            problem = Path(directory) / "goal.p"
            problem.write_text(tptp, encoding="utf-8")
            remaining = deadline.end - monotonic()
            if remaining <= 0:
                return result(deadline.outcome)
            search = solver.solve(problem, budgets=horn_budgets(task.budgets, remaining), cancel=deadline)
        probe["search"] = search.to_dict()
        if deadline.is_set() or search.outcome != "theorem":
            return result(deadline.outcome or search.outcome)

        step = branch.advance(action, cancel=deadline)
        after = step.observation
        if deadline.is_set():
            trials.append(StrategyTrial(action, 1, deadline.outcome, after))
            return result(deadline.outcome)
        if step.committed and after.status == "open":
            path = observation["path"]
            next_path = after.native["events"][-1]["path"]
            if (path and next_path and next_path != path
                    and not next_path.startswith(path + ".") and not path.startswith(next_path + ".")):
                trials.append(StrategyTrial(action, 1, "progress", after))
                return result("progress", step=step)
        if not step.committed or after.status != "ready":
            trials.append(StrategyTrial(action, 1, "no_proof", after))
            return result("no_proof")

        if proof_fragment is None and len(branch.checkpoint().actions) != 1:
            trials.append(StrategyTrial(action, 1, "proof_fragment_required", after))
            return result("proof_fragment_required")
        final = branch.finalize(proof_fragment=proof_fragment, cancel=deadline)
        evidence = final.evidence
        if evidence.task_success is True:
            trials.append(StrategyTrial(action, 1, "accepted", after, evidence))
            return result("accepted", step=step, final=final)
        outcome = evidence.checker_outcome if evidence.task_success is False else (
            deadline.outcome or evidence.execution_outcome)
        trials.append(StrategyTrial(action, 1, outcome, after, evidence))
        return result(outcome)
    except RuntimeError as error:
        outcome = deadline.outcome or getattr(error, "outcome", None)
        if outcome is None:
            raise
        return result(outcome)

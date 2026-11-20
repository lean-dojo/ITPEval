"""Run first-order automation on one reviewed native HOL goal."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic

from itpeval.backends.hol_tactics import HOLGoal, HOLProofSession, HOLProofState, HOLTraceFailure
from itpeval.core.records import Record
from itpeval.core.types import VerificationEvidence
from itpeval.verification.fragments import permitted

from .ground import horn_budgets
from .search import PreparedSolver, SearchEvidence


HOL_AUTOMATION = {"hol4": "METIS_TAC []", "hol-light": "ASM_MESON_TAC []"}


@dataclass(frozen=True)
class HOLSearchEvidence(Record):
    task_id: str
    environment_id: str
    target: str
    prover: str
    tactic: str
    goal: HOLGoal
    outcome: str
    duration_ms: int
    after: HOLProofState | None = None
    diagnostic: str | None = None
    candidate: str | None = None
    verification: VerificationEvidence | None = None
    tptp: str | None = None
    search: SearchEvidence | None = None


def search_hol(session: HOLProofSession, *, goal_path=None, timeout_s=None, cancel=None,
               solver: PreparedSolver | None = None) -> HOLSearchEvidence:
    """Search on a private branch, preserving native state for a partial result."""
    if not isinstance(session, HOLProofSession):
        raise TypeError("expected a native HOL proof session")
    task = session.task
    if timeout_s is not None and not 0 < timeout_s <= task.budgets.timeout_s:
        raise ValueError("HOL search timeout must be positive and fit the task's wall budget")
    state = session.inspect(session.handle, cancel=cancel)
    if not state.goals:
        raise ValueError("HOL search requires a pending goal")
    goal = state.goals[0] if goal_path is None else next((item for item in state.goals if item.path == goal_path), None)
    if goal is None:
        raise ValueError("choose a pending native HOL goal path")
    tactic = HOL_AUTOMATION[task.prover]
    base = task.task_id, task.environment_id, task.targets[0], task.prover, tactic, goal
    if not permitted(task.prover, tactic, task.proof_atoms + task.allowed_edits, ()):
        return HOLSearchEvidence(*base, "outside_task_policy", 0)

    start = monotonic()
    handle = session.handle
    tptp = None
    search = None
    try:
        if solver is not None:
            if task.prover != "hol4":
                raise ValueError("external TPTP search is available for HOL4")
            from itpeval.backends.hol4.fof import export_hol4_branch

            tptp = export_hol4_branch(session, goal.path, cancel=cancel, timeout_s=timeout_s)
            with TemporaryDirectory(prefix="itpeval-hol4-fof-") as directory:
                problem = Path(directory) / "goal.p"
                problem.write_bytes(tptp.encode("utf-8"))
                search = solver.solve(problem, budgets=horn_budgets(task.budgets, timeout_s), cancel=cancel)
            if search.outcome != "theorem":
                return HOLSearchEvidence(*base, search.outcome, round((monotonic() - start) * 1000),
                                         tptp=tptp, search=search)
        changed, after = session.step(handle, goal.path, tactic, cancel=cancel, timeout_s=timeout_s)
    except HOLTraceFailure as error:
        return HOLSearchEvidence(*base, error.outcome, round((monotonic() - start) * 1000), diagnostic=str(error),
                                 tptp=tptp, search=search)
    elapsed = round((monotonic() - start) * 1000)
    pending = {item.path for item in state.goals if item.path != goal.path}
    if changed == handle or {item.path for item in after.goals} != pending:
        return HOLSearchEvidence(*base, "no_proof", elapsed, after, after.diagnostic, tptp=tptp, search=search)
    if pending:
        return HOLSearchEvidence(*base, "progress", elapsed, after, tptp=tptp, search=search)
    final = session.finalize(changed, cancel=cancel)
    outcome = "accepted" if final.task_success is True else (
        final.checker_outcome if final.task_success is False else final.execution_outcome)
    return HOLSearchEvidence(*base, outcome, elapsed, after, candidate=session.candidate, verification=final,
                             tptp=tptp, search=search)

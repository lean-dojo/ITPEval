"""Export an observed HOL4 branch with the installed HOLyHammer translator."""

from __future__ import annotations

import os
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event

from itpeval.backends.hol_tactics import HOLProofSession


_EXPORTER = Path(__file__).with_suffix(".sml")


def _sml_path(path: Path) -> str:
    # Encode every filesystem byte as a Standard ML string escape.
    return '"' + "".join(f"\\{byte:03d}" for byte in os.fsencode(path)) + '"'


def export_hol4_branch(session: HOLProofSession, goal_path: tuple[int, ...], *,
                       cancel: Event | None = None, timeout_s: float | None = None) -> str:
    """Export the typed goal and local assumptions from one pending HOL4 branch.

    The assumptions are discharged into the FOF conjecture. The native
    operation runs on a separate snapshot and leaves the source session intact.
    """
    if not isinstance(session, HOLProofSession) or session.prover != "hol4":
        raise ValueError("expected a native HOL4 proof session")
    if (not isinstance(goal_path, tuple)
            or any(type(index) is not int or index < 0 for index in goal_path)):
        raise ValueError("expected a current pending HOL4 goal path")
    with session._lock:
        snapshot = session.fork(session.handle)
    actions = snapshot._actions
    if goal_path not in snapshot._pending_paths(actions):
        raise ValueError("expected a current pending HOL4 goal path")

    limit = snapshot.task.budgets.max_log_bytes
    with TemporaryDirectory(prefix="itpeval-hol4-fof-") as temp:
        output = Path(temp) / "branch.p"
        tactic = (_EXPORTER.read_text(encoding="utf-8")
                  .replace("ITPEVAL_TERM_LIMIT", str(limit))
                  .replace("ITPEVAL_FOF_PATH", _sml_path(output)))
        state, replayed = snapshot._read_tree(actions, cancel, attempt=(goal_path, tactic), timeout_s=timeout_s)
        if state.diagnostic is not None:
            raise RuntimeError(f"HOL4 could not export the selected goal: {state.diagnostic}")
        if replayed[goal_path].subgoals != 1:
            raise ValueError("HOL4 export changed the selected branch")
        if snapshot._state is not None:
            goals = tuple(replace(goal, path=goal_path) if goal.path == (*goal_path, 0) else goal
                          for goal in state.goals)
            if goals != snapshot._state.goals:
                raise ValueError("HOL4 goals changed while replaying the export snapshot")
        with output.open("rb") as stream:
            problem = stream.read(limit + 1)
    if not problem or len(problem) > limit:
        raise ValueError("HOL4 export is empty or exceeds the task's output budget")
    return problem.decode("utf-8")

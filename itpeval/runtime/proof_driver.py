"""Drive reviewed proof tasks through each prover's native interaction model."""

from __future__ import annotations

import re
from copy import deepcopy
from dataclasses import dataclass
from threading import RLock
from typing import Any, Literal

from itpeval.backends.registry import get_backend
from itpeval.core.records import Record, digest
from itpeval.core.types import VerificationEvidence


ActionKind = Literal["tactic", "command", "term", "assign", "edit_document"]
GoalStatus = Literal["open", "ready", "rejected", "unknown"]

_ACTION_KINDS = {
    "acl2": "command", "agda": "term", "hol-light": "tactic", "hol4": "tactic",
    "isabelle": "edit_document", "lean4": "tactic", "metamath": "assign",
    "mizar": "edit_document", "pvs": "command", "rocq": "command",
}
_HOL = {"hol4", "hol-light"}
_STEP_LIMIT = 256
_STATE_ID = re.compile(r"[0-9a-f]{64}")


@dataclass(frozen=True)
class NativeProofAction(Record):
    kind: ActionKind
    text: str
    goal_path: tuple[int, ...] | None = None
    step_index: int | None = None

    def __post_init__(self):
        if self.kind not in _ACTION_KINDS.values() or not isinstance(self.text, str) or not self.text.strip():
            raise ValueError("expected a native action kind and nonempty source text")
        if self.goal_path is not None and (self.kind != "tactic" or not isinstance(self.goal_path, tuple)
                or len(self.goal_path) > _STEP_LIMIT
                or any(type(part) is not int or part < 0 for part in self.goal_path)):
            raise ValueError("goal_path must contain nonnegative subgoal indices for a tactic")
        if self.kind == "assign":
            if type(self.step_index) is not int or not 0 < self.step_index <= 2**31 - 1:
                raise ValueError("assign requires a positive Metamath step number")
        elif self.step_index is not None:
            raise ValueError("step_index only applies to Metamath assignments")

    def require_prover(self, prover: str):
        expected = _ACTION_KINDS.get(prover)
        if self.kind != expected:
            raise ValueError(f"{prover} expects an action of kind {expected}")
        if (self.goal_path is not None) != (prover in _HOL):
            raise ValueError("supply a pending goal path for HOL4 or HOL Light tactics")


@dataclass(frozen=True)
class NativeProofObservation(Record):
    status: GoalStatus
    state_id: str
    native: dict[str, Any] | list[dict[str, Any]]

    def __post_init__(self):
        if not _STATE_ID.fullmatch(self.state_id):
            raise ValueError("invalid native proof state identity")


@dataclass(frozen=True)
class NativeProofTransition(Record):
    action: NativeProofAction
    observation: NativeProofObservation
    committed: bool


@dataclass(frozen=True)
class NativeProofCheckpoint(Record):
    task_id: str
    environment_id: str
    actions: tuple[NativeProofAction, ...]
    state_ids: tuple[str, ...]

    def __post_init__(self):
        if len(self.actions) > _STEP_LIMIT or len(self.state_ids) != len(self.actions) + 1:
            raise ValueError("checkpoint needs an initial state and a state for each saved action")
        if any(not _STATE_ID.fullmatch(state_id) for state_id in self.state_ids):
            raise ValueError("invalid native proof checkpoint state identities")


@dataclass(frozen=True)
class NativeProofFinalization(Record):
    candidate: str | None
    match: Literal["session_candidate", "identical_native_command", "same_locked_target"]
    evidence: VerificationEvidence


def _state(prover, value, initial):
    """Return a goal status and native semantic fields suitable for replay checks."""
    if prover == "lean4":
        goals = value.get("goal")
        if goals is None:
            return "unknown", None
        return ("open" if goals["goals"] else "ready"), goals["goals"]
    if prover == "agda":
        points = next((event["interactionPoints"] for event in reversed(value)
                       if event["kind"] == "InteractionPoints"), None)
        if points is None:
            return "unknown", None
        # Workspace paths in warnings would make replay hashes unstable.
        goals = [event["info"].get("visibleGoals") for event in value
                 if event.get("info", {}).get("kind") in {"AllGoalsWarnings", "Goals"}]
        return ("open" if points else "ready"), ([point["id"] for point in points], goals[-1:])
    if prover in _HOL:
        return ("open" if value.goals else "ready"), value.to_dict()["goals"]
    if prover == "metamath":
        return ("open" if value.open_steps else "ready"), value.to_dict()["steps"]
    if prover == "acl2":
        return ("ready" if value.complete else "open"), (value.goals, value.focused_term, value.hypotheses)
    if prover == "rocq":
        return ("ready" if value.complete else "open"), value.goals
    if prover == "isabelle":
        return ("open" if initial else "ready"), value.to_dict()["goals"]
    if prover == "pvs":
        return ({"init": "open", "waiting": "open", "proved": "ready"}.get(value.status, "unknown"),
                value.state_digest)
    # Mizar deliberately retains unsuccessful document revisions for repair.
    return ({"open": "open", "closed": "ready", "rejected": "rejected"}.get(value.status, "unknown"),
            (value.status, [thesis.to_dict() for thesis in value.theses],
             [diagnostic.to_dict() for diagnostic in value.diagnostics]))


class NativeProofDriver:
    """Observe and replay a reviewed task with prover-specific actions and feedback."""

    def __init__(self, task, prepared, **session_options):
        if task.prover not in _ACTION_KINDS:
            raise NotImplementedError(f"no native proof driver for {task.prover}")
        self.task, self.prepared = task, prepared
        self.action_kind = _ACTION_KINDS[task.prover]
        self._session_options = session_options
        self._session = get_backend(task.prover).open_native_session(task, prepared=prepared, **session_options)
        self._lock = RLock()
        self._actions = []
        self._states = []
        self._observation = None

    def _observation_for(self, value, *, initial=False, committed=True):
        prover = self.task.prover
        current = value["after"] if prover == "lean4" and "after" in value else value
        if committed:
            status, state = _state(prover, current, initial)
            state_id = digest({"task_id": self.task.task_id, "status": status, "state": state})
        else:
            status, state_id = "rejected", self._observation.state_id
        native = current.to_dict() if isinstance(current, Record) else current
        return NativeProofObservation(status, state_id, native)

    def observe(self, *, cancel=None) -> NativeProofObservation:
        with self._lock:
            if self._observation is None:
                value = self._session.inspect(self._session.handle, cancel=cancel)
                self._observation = self._observation_for(value, initial=True)
                self._states.append(self._observation.state_id)
            return deepcopy(self._observation)

    def advance(self, action: NativeProofAction, *, cancel=None) -> NativeProofTransition:
        """Apply a native action and retain the observation even if the action fails."""
        with self._lock:
            prover = self.task.prover
            if not isinstance(action, NativeProofAction):
                raise ValueError("expected a NativeProofAction")
            action.require_prover(prover)
            if len(self._actions) >= _STEP_LIMIT:
                raise ValueError("native proof driver reached its action limit")
            if self._observation is None:
                self.observe(cancel=cancel)
            session = self._session
            handle = session.handle
            if prover in _HOL:
                changed, value = session.step(handle, action.goal_path, action.text, cancel=cancel)
            elif action.kind == "assign":
                changed, value = session.assign(handle, action.step_index, action.text, cancel=cancel)
            elif action.kind == "term":
                changed, value = session.give(handle, action.text, cancel=cancel)
            else:
                changed, value = session.step(handle, action.text, cancel=cancel)
            committed = changed != handle
            observation = self._observation_for(value, committed=committed)
            if committed:
                self._actions.append(action)
                self._states.append(observation.state_id)
                self._observation = observation
            return NativeProofTransition(action, deepcopy(observation), committed)

    def checkpoint(self, *, cancel=None) -> NativeProofCheckpoint:
        """Save the native action sequence and observed state identities."""
        with self._lock:
            if self._observation is None:
                self.observe(cancel=cancel)
            return NativeProofCheckpoint(self.task.task_id, self.task.environment_id,
                                         tuple(self._actions), tuple(self._states))

    @classmethod
    def from_checkpoint(cls, task, prepared, checkpoint: NativeProofCheckpoint, *, cancel=None, **session_options):
        """Execute saved actions in a new session and verify the observed state sequence."""
        if (task.task_id, prepared.environment_id) != (checkpoint.task_id, checkpoint.environment_id):
            raise ValueError("native proof checkpoint belongs to another task or environment")
        session = cls(task, prepared, **session_options)
        native = session._session
        if hasattr(native, "replay_prefix"):
            for action in checkpoint.actions:
                action.require_prover(task.prover)
            if task.prover == "metamath":
                inputs = ((action.step_index, action.text) for action in checkpoint.actions)
            else:
                inputs = (action.text for action in checkpoint.actions)
            states = native.replay_prefix(native.handle, inputs, cancel=cancel)
            observations = tuple(session._observation_for(state, initial=index == 0)
                                 for index, state in enumerate(states))
            if len(observations) != len(checkpoint.state_ids):
                raise ValueError("native checkpoint replay returned the wrong number of states")
            for index, (observed, expected) in enumerate(zip(observations, checkpoint.state_ids)):
                if observed.state_id != expected:
                    raise ValueError(f"native {task.prover} proof state differed at replay step {index}")
            session._actions = list(checkpoint.actions)
            session._states = list(checkpoint.state_ids)
            session._observation = observations[-1]
            return session
        if session.observe(cancel=cancel).state_id != checkpoint.state_ids[0]:
            raise ValueError("native initial state differed during replay")
        for index, (action, expected) in enumerate(zip(checkpoint.actions, checkpoint.state_ids[1:]), 1):
            step = session.advance(action, cancel=cancel)
            if not step.committed or step.observation.state_id != expected:
                raise ValueError(f"native proof state differed at replay step {index}")
        return session

    def fork(self, *, cancel=None):
        """Create an independent continuation from this driver’s committed state."""
        with self._lock:
            snapshot = self.checkpoint(cancel=cancel)
            if not hasattr(self._session, "fork"):
                return self.from_checkpoint(self.task, self.prepared, snapshot,
                                            cancel=cancel, **self._session_options)
            branch = type(self)(self.task, self.prepared, **self._session_options)
            branch._session = self._session.fork(self._session.handle)
            branch._actions = list(snapshot.actions)
            branch._states = list(snapshot.state_ids)
            branch._observation = deepcopy(self._observation)
            return branch

    def suggest_atp(self, *, solver=None, executable=None, timeout_s=None, cancel=None, goal_path=None,
                    max_trials=32, proof_fragment=None, hints=()):
        """Search the current goal and return proof evidence without changing the session."""
        from itpeval.atp.session import ATP_SESSION_PROVERS, suggest_at_checkpoint
        from itpeval.atp.strategies import NATIVE_STRATEGIES

        if self.task.prover not in ATP_SESSION_PROVERS:
            raise NotImplementedError(f"ATP-assisted sessions are unavailable for {self.task.prover}")
        with self._lock:
            if self.observe(cancel=cancel).status != "open":
                raise ValueError("ATP search requires an open native goal")
            snapshot = self.checkpoint()
            branch = self.fork(cancel=cancel) if self.task.prover in {*_HOL, *NATIVE_STRATEGIES} else None
        return suggest_at_checkpoint(self.task, self.prepared, snapshot, solver=solver,
                                     executable=executable, timeout_s=timeout_s, cancel=cancel,
                                     branch=branch, goal_path=goal_path, max_trials=max_trials,
                                     proof_fragment=proof_fragment, hints=hints)

    def apply_atp(self, suggestion, *, cancel=None) -> NativeProofTransition:
        """Submit the checked ATP action only at the revision that produced it."""
        from itpeval.atp.session import NativeATPSuggestion

        if not isinstance(suggestion, NativeATPSuggestion):
            raise TypeError("expected a NativeATPSuggestion")
        with self._lock:
            snapshot = self.checkpoint(cancel=cancel)
            action = suggestion.checked_action(self.task, snapshot)
            if not suggestion.checks_transition:
                return self.advance(action, cancel=cancel)
            branch = self.fork(cancel=cancel)
            transition = branch.advance(action, cancel=cancel)
            suggestion.require_native_result(transition)
            if (suggestion.outcome == "accepted" and self.task.prover != "pvs"
                    and branch._session.candidate != suggestion.candidate):
                raise ValueError("automation produced a different proof artifact")
            self._session = branch._session
            self._actions, self._states = branch._actions, branch._states
            self._observation = branch._observation
            return transition

    def finalize(self, *, proof_fragment=None, **options) -> NativeProofFinalization:
        """Run final task verification. PVS can require a separate ProofLite fragment."""
        with self._lock:
            session = self._session
            if self.task.prover == "pvs":
                result = session.finalize(session.handle, proof_fragment, **options)
                return NativeProofFinalization(result.proof_fragment, result.match, result.verification)
            if proof_fragment is not None:
                raise ValueError("a separate finishing fragment is only used by PVS")
            evidence = session.finalize(session.handle, **options)
            return NativeProofFinalization(session.candidate, "session_candidate", evidence)

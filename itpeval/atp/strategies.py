"""Bounded native search over a private proof-state revision."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from time import monotonic
from typing import Any

from itpeval.core.records import Record
from itpeval.core.types import VerificationEvidence
from itpeval.runtime.interaction import agda_term_candidate
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofFinalization, NativeProofObservation
from itpeval.verification.fragments import permitted


NATIVE_STRATEGIES = {"acl2": "proof_builder", "agda": "auto", "metamath": "label_search",
                     "mizar": "justification_search", "pvs": "sequent_strategy"}


@dataclass(frozen=True)
class StrategyTrial(Record):
    action: NativeProofAction
    depth: int
    outcome: str
    feedback: NativeProofObservation | None = None
    verification: VerificationEvidence | None = None


@dataclass(frozen=True)
class NativeStrategyEvidence(Record):
    task_id: str
    environment_id: str
    target: str
    prover: str
    strategy: str
    outcome: str
    max_trials: int
    timeout_s: float
    duration_ms: int
    trials: tuple[StrategyTrial, ...]
    action: NativeProofAction | None = None
    after: NativeProofObservation | None = None
    plan: tuple[NativeProofAction, ...] = ()
    finalization: NativeProofFinalization | None = None
    probe: dict[str, Any] | None = None


class _Deadline:
    def __init__(self, timeout, cancel):
        self.end, self.parent = monotonic() + timeout, cancel

    @property
    def outcome(self):
        if self.parent is not None and self.parent.is_set():
            return "cancelled"
        if monotonic() >= self.end:
            return "timeout"
        return None

    def is_set(self):
        return self.outcome is not None


def _actions(driver, observation):
    task = driver.task
    if task.prover == "acl2":
        return (NativeProofAction("command", command) for command in
                driver._session.automation_commands(driver._session.handle))
    if task.prover == "pvs":
        from itpeval.backends.pvs.interaction import PVS_AUTOMATION_STRATEGIES

        approved = task.proof_atoms + task.allowed_edits
        return (NativeProofAction("command", cmd) for cmd in PVS_AUTOMATION_STRATEGIES if cmd in approved)
    if task.prover == "mizar":
        candidates = tuple(dict.fromkeys((*task.proof_atoms, *task.allowed_edits)))
        return (NativeProofAction("edit_document", text) for text in candidates
                if permitted(task.prover, text, task.allowed_edits, task.proof_atoms))
    # Select the first unknown step from the actual Proof Assistant state.
    step = next(row["index"] for row in observation.native["steps"] if row["applied_label"] == "?")
    return (NativeProofAction("assign", label, step_index=step) for label in dict.fromkeys(task.proof_atoms))


def _progress(prover, before, after):
    if prover == "pvs":
        def focus(observation):
            event = observation.native["events"][-1]
            return event["path"], event["sequent"]
        return focus(before) != focus(after)
    return before.state_id != after.state_id


def search_native(driver, *, timeout_s=None, max_trials=32, proof_fragment=None, hints=(), cancel=None):
    """Search reviewed native actions, retaining attempts and any checked result."""
    task = driver.task
    prover = task.prover
    if type(max_trials) is not int or not 1 <= max_trials <= 256:
        raise ValueError("max_trials must be an integer from 1 to 256")
    timeout = min(30, task.budgets.timeout_s) if timeout_s is None else timeout_s
    if not 0 < timeout <= task.budgets.timeout_s:
        raise ValueError("search timeout must be positive and fit the task's wall budget")
    if hints and prover != "agda":
        raise ValueError("native search hints are available for Agda Auto")
    if proof_fragment is not None:
        if prover != "pvs":
            raise ValueError("a separate finishing fragment is only used by PVS")
        from itpeval.verification.policies import assemble

        assemble(task, proof_fragment)

    start = monotonic()
    deadline = _Deadline(timeout, cancel)
    trials = []
    probe = None

    def result(outcome, *, transitions=(), final=None):
        selected = transitions[0] if transitions else None
        return NativeStrategyEvidence(task.task_id, task.environment_id, task.targets[0], prover,
                                      NATIVE_STRATEGIES[prover], outcome, max_trials, timeout,
                                      round((monotonic() - start) * 1000), tuple(trials),
                                      selected.action if selected else None, selected.observation if selected else None,
                                      tuple(step.action for step in transitions), final, probe)

    if deadline.is_set():
        return result(deadline.outcome)
    try:
        initial = driver.observe(cancel=deadline)
        auto = None
        if prover == "agda":
            session = driver._session
            native_timeout = min(1, timeout) if timeout_s is None else timeout
            if native_timeout < 0.001:
                return result("timeout")
            auto = session.auto(session.handle, timeout_s=native_timeout, hints=hints, cancel=deadline)
            probe = auto.to_dict()
            if deadline.is_set() or auto.candidate is None:
                return result(deadline.outcome or auto.status)
        pending = deque([(driver, initial, ())])
        seen = {initial.state_id}
        while pending:
            node, before, path = pending.popleft()
            actions = [NativeProofAction("term", auto.candidate)] if auto is not None else _actions(node, before)
            for action in actions:
                if deadline.is_set() or len(trials) == max_trials:
                    return result(deadline.outcome or "trial_limit")
                child = node.fork(cancel=deadline)
                if auto is not None and not permitted(prover, agda_term_candidate(task, action.text),
                                                       task.allowed_edits, task.proof_atoms):
                    trials.append(StrategyTrial(action, 1, "outside_task_policy"))
                    return result("outside_task_policy")
                step = child.advance(action, cancel=deadline)
                after = step.observation
                depth = len(path) + 1
                if after.status == "unknown":
                    outcome = deadline.outcome or after.native.get("status", "unavailable")
                    trials.append(StrategyTrial(action, depth, outcome, after))
                    return result(outcome)
                if step.committed and after.status == "ready":
                    if prover == "pvs" and proof_fragment is None and len(child.checkpoint().actions) != 1:
                        trials.append(StrategyTrial(action, depth, "proof_fragment_required", after))
                        return result("proof_fragment_required")
                    final = child.finalize(proof_fragment=proof_fragment, cancel=deadline)
                    evidence = final.evidence
                    outcome = "accepted" if evidence.task_success is True else (
                        evidence.checker_outcome if evidence.task_success is False else evidence.execution_outcome)
                    trials.append(StrategyTrial(action, depth, outcome, after, evidence))
                    if evidence.task_success is True:
                        complete = (*path, step)
                        return result("accepted", transitions=complete, final=final) if not path else result(
                            "progress", transitions=complete)
                    if evidence.task_success is None:
                        return result(deadline.outcome or outcome)
                elif step.committed and after.status == "open" and _progress(prover, before, after):
                    trials.append(StrategyTrial(action, depth, "progress", after))
                    if prover in {"acl2", "pvs"}:
                        return result("progress", transitions=(step,))
                    if prover == "metamath" and after.state_id not in seen:
                        seen.add(after.state_id)
                        pending.append((child, after, (*path, step)))
                else:
                    trials.append(StrategyTrial(action, depth, after.status if after.status != "open" else "no_progress", after))
        return result("no_proof" if trials else "outside_task_policy")
    except RuntimeError as error:
        outcome = deadline.outcome or getattr(error, "outcome", None)
        if outcome is not None:
            return result(outcome)
        raise

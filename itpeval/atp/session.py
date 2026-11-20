"""Search at a saved interactive revision and bind any suggestion to that revision."""

from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path
from typing import Literal

from itpeval.core.records import Record, digest
from itpeval.runtime.interaction import agda_term_candidate
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofCheckpoint, NativeProofFinalization
from itpeval.verification.policies import assemble

from .agda import AgdaHornEvidence, AgdaHornObservation, _search_agda_problem, observe_agda_horn
from .hol import HOL_AUTOMATION, HOLSearchEvidence, search_hol
from .isabelle import HammerEvidence, run_sledgehammer
from .lean import LeanHornEvidence, LeanHornObservation, _search_lean_problem, observe_lean_horn
from .rocq import RocqHornEvidence, RocqHornObservation, observe_rocq_horn, run_rocq_horn_search
from .search import PreparedSolver, prepare_solver
from .strategies import NATIVE_STRATEGIES, NativeStrategyEvidence, search_native


ATP_SESSION_PROVERS = frozenset({"isabelle", "lean4", "rocq", *HOL_AUTOMATION, *NATIVE_STRATEGIES})


@dataclass(frozen=True)
class NativeATPSuggestion(Record):
    task_id: str
    environment_id: str
    prover: Literal["acl2", "agda", "hol4", "hol-light", "isabelle", "lean4", "metamath", "mizar", "pvs", "rocq"]
    checkpoint_id: str
    state_id: str
    outcome: str
    evidence: HammerEvidence | LeanHornEvidence | RocqHornEvidence | AgdaHornEvidence | HOLSearchEvidence | NativeStrategyEvidence | None = None
    unsupported_observation: LeanHornObservation | RocqHornObservation | AgdaHornObservation | None = None

    def __post_init__(self):
        if self.prover not in ATP_SESSION_PROVERS:
            raise ValueError("unknown native ATP prover")
        if self.evidence is not None:
            expected = {"isabelle": HammerEvidence, "lean4": LeanHornEvidence, "rocq": RocqHornEvidence,
                        **dict.fromkeys(HOL_AUTOMATION, HOLSearchEvidence), **dict.fromkeys(NATIVE_STRATEGIES, NativeStrategyEvidence),
                        "agda": (NativeStrategyEvidence, AgdaHornEvidence)}
            if (not isinstance(self.evidence, expected[self.prover]) or self.unsupported_observation is not None
                    or (self.evidence.task_id, self.evidence.environment_id) != (self.task_id, self.environment_id)):
                raise ValueError("search evidence does not match its ATP suggestion")
            if isinstance(self.evidence, (HOLSearchEvidence, NativeStrategyEvidence)) and (self.prover, self.outcome) != (
                    self.evidence.prover, self.evidence.outcome):
                raise ValueError("native search evidence does not match its prover or outcome")
        else:
            observations = {"lean4": LeanHornObservation, "rocq": RocqHornObservation, "agda": AgdaHornObservation}
            if (self.outcome != "unsupported_goal" or self.prover not in observations
                    or not isinstance(self.unsupported_observation, observations[self.prover])
                    or self.unsupported_observation.problem is not None
                    or (self.unsupported_observation.task_id, self.unsupported_observation.environment_id) !=
                    (self.task_id, self.environment_id)):
                raise ValueError("an unsupported ATP suggestion requires its native observation")

    @property
    def action(self) -> NativeProofAction | None:
        evidence = self.evidence
        if isinstance(evidence, NativeStrategyEvidence):
            return evidence.action
        if isinstance(evidence, HOLSearchEvidence) and self.outcome in {"accepted", "progress"}:
            return NativeProofAction("tactic", evidence.tactic, evidence.goal.path)
        if isinstance(evidence, HammerEvidence):
            proof = evidence.checked_proof
            return NativeProofAction("edit_document", proof.text) if proof else None
        if isinstance(evidence, (LeanHornEvidence, RocqHornEvidence)) and evidence.suffix:
            return NativeProofAction("tactic" if self.prover == "lean4" else "command", evidence.suffix)
        if isinstance(evidence, AgdaHornEvidence) and evidence.suffix:
            return NativeProofAction("term", evidence.suffix)
        return None

    @property
    def candidate(self) -> str | None:
        evidence = self.evidence
        if isinstance(evidence, NativeStrategyEvidence):
            return evidence.finalization.candidate if evidence.finalization else None
        if isinstance(evidence, HammerEvidence):
            return evidence.checked_proof.text if evidence.checked_proof else None
        return evidence.candidate if evidence is not None else None

    @property
    def verification(self):
        evidence = self.evidence
        if isinstance(evidence, NativeStrategyEvidence):
            return evidence.finalization.evidence if evidence.finalization else None
        if isinstance(evidence, HOLSearchEvidence):
            return evidence.verification
        if isinstance(evidence, HammerEvidence):
            return evidence.checked_proof.evidence if evidence.checked_proof else None
        return evidence.replay if evidence is not None else None

    @property
    def finalization(self) -> NativeProofFinalization | None:
        if self.outcome != "accepted" or self.verification is None:
            return None
        if isinstance(self.evidence, NativeStrategyEvidence):
            return self.evidence.finalization
        return NativeProofFinalization(self.candidate, "session_candidate", self.verification)

    def require_checkpoint(self, task, snapshot: NativeProofCheckpoint):
        if (self.task_id, self.environment_id, self.prover, self.checkpoint_id, self.state_id) != (
                task.task_id, task.environment_id, task.prover, digest(snapshot.to_dict()), snapshot.state_ids[-1]):
            raise ValueError("ATP suggestion belongs to another task or proof revision")

    def checked_action(self, task, snapshot: NativeProofCheckpoint) -> NativeProofAction:
        """Bind the previous native verdict to the exact composed artifact."""
        self.require_checkpoint(task, snapshot)
        action, evidence = self.action, self.verification
        if isinstance(self.evidence, NativeStrategyEvidence):
            observation = self.evidence.after
            if (action is None or observation is None or self.evidence.target != task.targets[0]
                    or not self.evidence.plan or action != self.evidence.plan[0]):
                raise ValueError("search did not check a native action for this task")
            action.require_prover(task.prover)
            if self.outcome == "progress" and observation.status == "open" and evidence is None:
                return action
            if (self.outcome == "accepted" and observation.status == "ready" and self.evidence.plan == (action,)
                    and evidence is not None and evidence.task_success is True and self.candidate is not None
                    and (evidence.task_id, evidence.environment_id) == (task.task_id, task.environment_id)
                    and evidence.artifact_id == assemble(task, self.candidate).artifact_id):
                return action
            raise ValueError("search evidence does not match the native result")
        if isinstance(self.evidence, HOLSearchEvidence):
            state = self.evidence.after
            if (action is None or state is None or (state.task_id, state.environment_id, state.target) !=
                    (task.task_id, task.environment_id, task.targets[0])):
                raise ValueError("HOL search did not check a native action for this task")
            if self.outcome == "progress" and state.goals and evidence is None and self.candidate is None:
                return action
            if (self.outcome == "accepted" and not state.goals and evidence is not None
                    and evidence.task_success is True and self.candidate is not None
                    and (evidence.task_id, evidence.environment_id) == (task.task_id, task.environment_id)
                    and evidence.artifact_id == assemble(task, self.candidate).artifact_id):
                return action
            raise ValueError("HOL search evidence does not match the tactic and its native result")
        if self.outcome != "accepted" or action is None or evidence is None or evidence.task_success is not True:
            raise ValueError("ATP suggestion has no proof accepted by the native checker")
        if task.prover == "agda":
            if snapshot.actions:
                raise ValueError("Agda external search requires the open completion hole")
            candidate = agda_term_candidate(task, action.text)
        else:
            separator = " <;> " if task.prover == "lean4" else "\n"
            candidate = separator.join([*(step.text for step in snapshot.actions), action.text])
        if (candidate != self.candidate or (evidence.task_id, evidence.environment_id) !=
                (task.task_id, task.environment_id) or evidence.artifact_id != assemble(task, candidate).artifact_id):
            raise ValueError("ATP verification does not match the action and its locked target")
        return action

    @property
    def checks_transition(self):
        return isinstance(self.evidence, (HOLSearchEvidence, NativeStrategyEvidence))

    def require_native_result(self, step):
        """Check that applying an action reproduced the observed native progress."""
        evidence = self.evidence
        if isinstance(evidence, NativeStrategyEvidence):
            matches = (evidence.after is not None and
                       (step.observation.status, step.observation.state_id) ==
                       (evidence.after.status, evidence.after.state_id))
        else:
            matches = isinstance(evidence, HOLSearchEvidence) and evidence.after is not None and (
                step.observation.native == evidence.after.to_dict())
        if (not matches or not step.committed or step.action != self.action
                or step.observation.status != ("ready" if self.outcome == "accepted" else "open")):
            raise ValueError("automation did not reproduce the checked native result")


def _prepared_solver(solver, prefix, executable):
    if isinstance(solver, PreparedSolver):
        if executable is not None:
            raise ValueError("an executable override cannot change an already prepared solver")
        return solver
    return prepare_solver(solver, prefix=prefix, executable=executable)


def suggest_at_checkpoint(task, prepared, checkpoint: NativeProofCheckpoint, *,
                          solver: str | PreparedSolver | None = None, executable: Path | None = None,
                          timeout_s: float | None = None, cancel=None, branch=None,
                          goal_path: tuple[int, ...] | None = None, max_trials=32,
                          proof_fragment=None, hints=()) -> NativeATPSuggestion:
    """Replay the committed scope in an isolated native prover for ATP search."""
    prover = task.prover
    if (checkpoint.task_id, checkpoint.environment_id) != (task.task_id, prepared.environment_id):
        raise ValueError("ATP checkpoint belongs to another task or environment")
    base = (task.task_id, task.environment_id, prover, digest(checkpoint.to_dict()), checkpoint.state_ids[-1])
    if prover in NATIVE_STRATEGIES:
        if branch is None or branch.task != task:
            raise ValueError("native search session belongs to another task")
        if goal_path is not None:
            raise ValueError("explicit goal paths are available for HOL automation")
        if solver in (None, "native") and executable is None:
            receipt = search_native(branch, timeout_s=timeout_s, max_trials=max_trials, proof_fragment=proof_fragment,
                                    hints=hints, cancel=cancel)
            return NativeATPSuggestion(*base, receipt.outcome, receipt)
        if prover not in {"agda", "pvs"} or solver in (None, "native"):
            raise ValueError(f"{prover} requires its native search strategy or an explicitly supported external solver")
        if hints:
            raise ValueError("search hints are available for Agda Auto")
        if prover == "pvs":
            from .pvs import search_pvs_horn

            external = _prepared_solver(solver, prepared.prefix, executable)
            receipt = search_pvs_horn(branch, solver=external, proof_fragment=proof_fragment,
                                      timeout_s=timeout_s, cancel=cancel)
            return NativeATPSuggestion(*base, receipt.outcome, receipt)
        if proof_fragment is not None or checkpoint.actions:
            raise ValueError("Agda external search requires a single open completion hole")
        observed = observe_agda_horn(task, prepared=prepared, timeout_s=timeout_s, cancel=cancel)
        if observed.problem is None:
            return NativeATPSuggestion(*base, "unsupported_goal", unsupported_observation=observed)
        external = _prepared_solver(solver, prepared.prefix, executable)
        receipt = _search_agda_problem(task, observed.problem, observation=observed, prepared=prepared,
                                       solver=external, search_timeout_s=timeout_s, cancel=cancel)
        outcome = receipt.replay_outcome if receipt.replay_outcome != "not_attempted" else receipt.search.outcome
        return NativeATPSuggestion(*base, outcome, receipt)
    if proof_fragment is not None or hints:
        raise ValueError("finishing fragments and hints are available for PVS and Agda respectively")
    if prover in HOL_AUTOMATION:
        if branch is None or branch.task != task:
            raise ValueError("HOL search session belongs to another task")
        if (solver is None or solver == "native") and executable is None:
            external = None
        elif prover != "hol4" or solver is None or solver == "native":
            raise ValueError("choose E or Vampire explicitly for external HOL4 search")
        else:
            external = _prepared_solver(solver, prepared.prefix, executable)
        receipt = search_hol(branch._session, goal_path=goal_path, timeout_s=timeout_s, cancel=cancel, solver=external)
        return NativeATPSuggestion(*base, receipt.outcome, receipt)
    if goal_path is not None:
        raise ValueError("explicit goal paths are available for HOL automation")
    if solver is None:
        solver = "e"
    prefix = tuple(item.text for item in checkpoint.actions)
    for item in checkpoint.actions:
        item.require_prover(prover)
    if prover == "isabelle":
        if prefix or executable is not None or not isinstance(solver, str):
            raise ValueError("the Isabelle session searches its original goal with a locked solver component")
        receipt = run_sledgehammer(task, prepared=prepared, solver=solver, search_timeout_s=timeout_s, cancel=cancel)
        outcome = "accepted" if receipt.checked_proof else next(
            (item.disposition for item in reversed(receipt.suggestions) if item.evidence is not None),
            receipt.suggestions[0].disposition if receipt.suggestions else receipt.search_outcome,
        )
        return NativeATPSuggestion(*base, outcome, receipt)
    if prover == "lean4":
        observe = observe_lean_horn
    elif prover == "rocq":
        observe = observe_rocq_horn
    else:
        raise NotImplementedError(f"ATP-assisted sessions are unavailable for {prover}")
    observation = observe(task, prepared=prepared, prefix=prefix, timeout_s=timeout_s, cancel=cancel)
    if observation.problem is None:
        return NativeATPSuggestion(*base, "unsupported_goal", unsupported_observation=observation)
    prepared_solver = _prepared_solver(solver, prepared.prefix, executable)
    options = dict(prepared=prepared, prefix=prefix, as_action=True,
                   solver=prepared_solver, search_timeout_s=timeout_s, cancel=cancel)
    if prover == "lean4":
        receipt = _search_lean_problem(task, observation.problem, observation=observation, **options)
    else:
        receipt = replace(run_rocq_horn_search(task, observation.problem, **options), observation=observation)
    outcome = receipt.replay_outcome if receipt.replay_outcome != "not_attempted" else receipt.search.outcome
    return NativeATPSuggestion(*base, outcome, receipt)

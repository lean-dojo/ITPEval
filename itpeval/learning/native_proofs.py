"""Collect and replay native goal/action trajectories with final verifier evidence."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from itpeval.atp.search import PreparedSolver
from itpeval.atp.session import NativeATPSuggestion
from itpeval.core.records import Record
from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.learning.episodes import _compare
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rewards import proof_reward
from itpeval.runtime.proof_driver import (NativeProofCheckpoint, NativeProofDriver, NativeProofFinalization,
                                          NativeProofObservation, NativeProofTransition)
from itpeval.verification.policies import assemble


@dataclass(frozen=True)
class SearchWithATP:
    """A policy decision to ask an automated prover about the current native goal."""

    solver: str | PreparedSolver | None = None
    executable: Path | None = None
    timeout_s: float | None = None
    goal_path: tuple[int, ...] | None = None
    max_trials: int = 32
    hints: tuple[str, ...] = ()


@dataclass(frozen=True)
class ATPProgress(Record):
    """The solver receipt for a step that closed a subgoal of a larger proof."""

    step: int
    suggestion: NativeATPSuggestion


@dataclass(frozen=True)
class NativeProofEpisode(Record):
    task: TaskSpec
    manifest: RunManifest
    initial: NativeProofObservation
    transitions: tuple[NativeProofTransition, ...]
    stop_reason: Literal["ready", "policy_stopped", "attempt_limit", "atp_unresolved"]
    finalization: NativeProofFinalization | None
    atp: NativeATPSuggestion | None = None
    atp_progress: tuple[ATPProgress, ...] = ()

    def to_dict(self) -> dict:
        data = super().to_dict()
        if self.atp is None:
            data.pop("atp")
        if not self.atp_progress:
            data.pop("atp_progress")
        return data


def _attempt_limit(task, manifest):
    if (task.operation != "proof_completion" or manifest.policy != "native_proof.v1"
            or task.task_id not in manifest.tasks or task.environment_id not in manifest.environments
            or manifest.budgets.get("checker", task.budgets.to_dict()) != task.budgets.to_dict()):
        raise ValueError("run manifest must cover the native proof task and its locked environment")
    limit = manifest.budgets.get("max_attempts")
    if type(limit) is not int or not 1 <= limit <= 256:
        raise ValueError("native proof runs require a max_attempts budget from 1 to 256")
    return limit


def rollout_native(task, prepared, manifest, generate, *, proof_fragment=None, cancel=None,
                   **session_options) -> NativeProofEpisode:
    """Ask generate(task, current_state, history) for actions until ready or stopped.

    Return None to stop or SearchWithATP to try closing the current goal.
    A PVS policy can supply the reviewed ProofLite fragment needed to verify
    a multi-command interactive proof.
    """
    if proof_fragment is not None and task.prover != "pvs":
        raise ValueError("a separate finishing fragment is only used by PVS")
    limit = _attempt_limit(task, manifest)
    driver = NativeProofDriver(task, prepared, **session_options)
    initial = current = driver.observe(cancel=cancel)
    transitions = []
    atp = None
    progress = []
    reason = "ready" if current.status == "ready" else "attempt_limit"
    if reason != "ready":
        for _ in range(limit):
            action = generate(task, current, tuple(transitions))
            if action is None:
                reason = "policy_stopped"
                break
            if isinstance(action, SearchWithATP):
                suggestion = driver.suggest_atp(solver=action.solver, executable=action.executable,
                                                timeout_s=action.timeout_s, cancel=cancel, goal_path=action.goal_path,
                                                max_trials=action.max_trials, proof_fragment=proof_fragment,
                                                hints=action.hints)
                if suggestion.outcome not in {"accepted", "progress"}:
                    atp = suggestion
                    reason = "atp_unresolved"
                    break
                step = driver.apply_atp(suggestion, cancel=cancel)
                if suggestion.outcome == "progress":
                    progress.append(ATPProgress(len(transitions), suggestion))
                elif not step.committed or step.observation.status != "ready":
                    raise RuntimeError("native session did not close with the verified ATP action")
                else:
                    atp = suggestion
            else:
                step = driver.advance(action, cancel=cancel)
            transitions.append(step)
            if step.committed:
                current = step.observation
                if current.status == "ready":
                    reason = "ready"
                    break
    finalization = None
    if reason == "ready":
        if atp is not None and atp.outcome == "accepted":
            # Applying the suggestion binds its fresh native check to the
            # exact final artifact. Replay can still recheck it independently.
            finalization = atp.finalization
        else:
            needs_prooflite = task.prover == "pvs" and len(driver.checkpoint().actions) != 1
            if not needs_prooflite or proof_fragment is not None:
                finalization = driver.finalize(proof_fragment=proof_fragment, cancel=cancel)
    return NativeProofEpisode(task, manifest, initial, tuple(transitions), reason, finalization, atp, tuple(progress))


def check_native_episode(episode: NativeProofEpisode) -> VerificationEvidence | None:
    """Validate record identities and episode structure without launching a prover."""
    task, manifest = episode.task, episode.manifest
    limit = _attempt_limit(task, manifest)
    if len(episode.transitions) > limit:
        raise ValueError("native proof episode exceeds its declared action limit")
    current = episode.initial
    committed = []
    states = [current.state_id]
    progress = {item.step: item.suggestion for item in episode.atp_progress}
    if (len(progress) != len(episode.atp_progress) or any(not 0 <= index < len(episode.transitions) for index in progress)
            or (episode.atp is not None and episode.atp.outcome == "progress")):
        raise ValueError("invalid ATP progress association in native proof episode")
    for index, step in enumerate(episode.transitions):
        step.action.require_prover(task.prover)
        if current.status == "ready":
            raise ValueError("native proof episode continues past its ready state")
        if index in progress:
            suggestion = progress[index]
            before = NativeProofCheckpoint(task.task_id, task.environment_id, tuple(committed), tuple(states))
            if suggestion.outcome != "progress" or suggestion.checked_action(task, before) != step.action:
                raise ValueError("ATP progress does not describe this native action")
            suggestion.require_native_result(step)
        if step.committed:
            current = step.observation
            committed.append(step.action)
            states.append(current.state_id)
        elif step.observation.status != "rejected" or step.observation.state_id != current.state_id:
            raise ValueError("an uncommitted action must retain the parent state identity")
    if (current.status == "ready") != (episode.stop_reason == "ready"):
        raise ValueError("native proof episode stop reason disagrees with its final state")
    if episode.stop_reason == "attempt_limit" and len(episode.transitions) != limit:
        raise ValueError("native proof episode stopped before reaching its action limit")
    if episode.atp is not None:
        accepted = episode.atp.outcome == "accepted"
        if accepted:
            if episode.stop_reason != "ready" or not episode.transitions or not episode.transitions[-1].committed:
                raise ValueError("accepted ATP evidence requires a committed final action")
            before = NativeProofCheckpoint(task.task_id, task.environment_id, tuple(committed[:-1]), tuple(states[:-1]))
            if episode.atp.checked_action(task, before) != committed[-1]:
                raise ValueError("ATP evidence does not describe the final native action")
            if episode.atp.checks_transition:
                episode.atp.require_native_result(episode.transitions[-1])
        else:
            if episode.stop_reason != "atp_unresolved" or len(episode.transitions) >= limit:
                raise ValueError("unresolved ATP search must end within the attempt limit")
            before = NativeProofCheckpoint(task.task_id, task.environment_id, tuple(committed), tuple(states))
            episode.atp.require_checkpoint(task, before)
    elif episode.stop_reason == "atp_unresolved":
        raise ValueError("native proof episode is missing its ATP receipt")
    result = episode.finalization
    if result is None:
        if current.status == "ready" and (task.prover != "pvs" or len(committed) == 1):
            raise ValueError("a ready episode is missing final verification")
        return None
    if current.status != "ready" or result.candidate is None:
        raise ValueError("native finalization requires a ready state and proof candidate")
    if task.prover == "pvs":
        identical = len(committed) == 1 and committed[0].text == result.candidate
        if result.match != ("identical_native_command" if identical else "same_locked_target"):
            raise ValueError("PVS finalization disagrees with the committed command sequence")
    elif result.match != "session_candidate":
        raise ValueError("finalization must verify the session's candidate")
    evidence = result.evidence
    proof_reward(task, evidence)
    try:
        artifact_id = assemble(task, result.candidate).artifact_id
    except ValueError:
        if evidence.checker_outcome != "policy_rejected":
            raise ValueError("invalid native candidate claims checker evidence") from None
        artifact_id = task.artifact.artifact_id
    if evidence.artifact_id != artifact_id:
        raise ValueError("final verification belongs to another proof artifact")
    if episode.atp is not None:
        _compare(episode.atp.verification, evidence)
    return evidence


def replay_native_episode(episode: NativeProofEpisode, *, task, prepared, cancel=None,
                          **session_options) -> VerificationEvidence | None:
    """Re-execute every submitted action and independently verify the final proof."""
    if task != episode.task:
        raise ValueError("native proof episode belongs to another task")
    expected = check_native_episode(episode)
    driver = NativeProofDriver(task, prepared, **session_options)

    def state_key(observation):
        return observation.status, observation.state_id

    if state_key(driver.observe(cancel=cancel)) != state_key(episode.initial):
        raise ValueError("native initial state differs from the episode")
    for index, transition in enumerate(episode.transitions):
        step = driver.advance(transition.action, cancel=cancel)
        if (step.committed != transition.committed
                or state_key(step.observation) != state_key(transition.observation)):
            raise ValueError(f"native replay differs at action {index}")
    if expected is None:
        return None
    proof_fragment = episode.finalization.candidate if task.prover == "pvs" else None
    final = driver.finalize(proof_fragment=proof_fragment, cancel=cancel)
    if (final.candidate, final.match) != (episode.finalization.candidate, episode.finalization.match):
        raise ValueError("finalized proof differs from the recorded candidate")
    _compare(expected, final.evidence)
    return final.evidence

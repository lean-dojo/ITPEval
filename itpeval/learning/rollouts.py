"""Collect verifier feedback from generated document revisions and replay the final candidate."""

from __future__ import annotations

from collections.abc import Callable

from itpeval.core.episodes import Action, Episode, Observation, Transition
from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.environments import PreparedProject
from itpeval.learning.manifests import RunManifest
from itpeval.verification.service import assemble, verify


def rollout(task: TaskSpec, prepared: PreparedProject, manifest: RunManifest,
            generate: Callable[[TaskSpec, tuple[Transition, ...]], Action]) -> Episode:
    """Give the generator prior attempts and check each proposed edit against the locked target.

    Rejections may be retried within the manifest budget. Success and infrastructure
    failures end the episode. A definitive final candidate gets a fresh verification.
    """
    if task.operation != "proof_completion":
        raise ValueError("document rollouts require a proof completion task")
    if task.task_id not in manifest.tasks or task.environment_id not in manifest.environments:
        raise ValueError("run manifest does not cover this task and environment")
    limit = manifest.budgets.get("max_attempts")
    if type(limit) is not int or limit < 1:
        raise ValueError("run manifest requires a positive max_attempts budget")
    if prepared.environment_id != task.environment_id or prepared.spec.prover != task.prover:
        raise ValueError("prepared environment differs from the rollout task")
    if "checker" in manifest.budgets and manifest.budgets["checker"] != task.budgets.to_dict():
        raise ValueError("manifest checker budget differs from the native task")
    transitions = []
    for _ in range(limit):
        try:
            action = generate(task, tuple(transitions))
        except Exception as error:
            action = Action("generation_error", "", "")
            evidence = VerificationEvidence(task.task_id, task.environment_id, task.artifact.artifact_id,
                                            "generation_error", "not_run", None, "unchecked", "unknown",
                                            stderr=f"{type(error).__name__}: {error}")
        else:
            if not isinstance(action, Action) or action.kind != "edit_document":
                raise ValueError("the document generator must return an edit_document action")
            evidence = verify(task, action.candidate, prepared=prepared)
        observation = Observation(evidence.execution_outcome, evidence.checker_outcome,
                                  evidence.task_success, evidence.stdout, evidence.stderr,
                                  evidence.duration_ms)
        transitions.append(Transition(action, observation, evidence.to_dict()))
        if evidence.task_success is not False:
            break
    candidate = transitions[-1].action.candidate
    # Infrastructure failures are retained for accounting. Retrying requires a new rollout.
    if evidence.task_success is not None:
        evidence = verify(task, candidate, prepared=prepared)
    try:
        artifact = assemble(task, candidate)
    except ValueError:
        artifact = None
    return Episode(task.task_id, task.environment_id, manifest.run_id, task.to_dict(),
                   manifest.to_dict(), tuple(transitions), candidate,
                   artifact.to_dict() if artifact is not None else None, evidence.to_dict())

"""Turn native checker feedback from solver suggestions into proof episodes."""

from __future__ import annotations

from itpeval.atp import HammerEvidence, LeanHornEvidence, RocqHornEvidence
from itpeval.core.episodes import Action, Episode, Observation, Transition
from itpeval.core.records import digest
from itpeval.core.types import TaskSpec
from itpeval.learning.episodes import check_episode, task_prompt
from itpeval.learning.manifests import RunManifest
from itpeval.verification.service import assemble


def episode_from_hammer(task: TaskSpec, receipt: HammerEvidence) -> Episode | None:
    """Record replayed suggestions through the first terminal native verdict."""
    return episode_from_search(task, receipt)


def episode_from_search(task: TaskSpec, receipt: HammerEvidence | LeanHornEvidence | RocqHornEvidence) -> Episode | None:
    """Export one checked solver workflow into the standard proof episode format."""
    if isinstance(receipt, HammerEvidence):
        prover = "isabelle"
        attempts = ((item.text, item.evidence) for item in receipt.suggestions if item.evidence is not None)
        settings = {"id": "isabelle.sledgehammer", "solver": receipt.solver.to_dict(),
                    "search_budgets": receipt.search_budgets.to_dict(), "solver_timeout_s": receipt.solver_timeout_s,
                    "trace_premises": receipt.trace_premises}
        limit = receipt.replay_limit
    elif isinstance(receipt, (LeanHornEvidence, RocqHornEvidence)):
        prover = "rocq" if isinstance(receipt, RocqHornEvidence) else "lean4"
        attempts = [(receipt.candidate, receipt.replay)] if receipt.replay is not None else []
        settings = {"id": f"{prover}.ground_horn", "solver": receipt.search.solver.to_dict(),
                    "search_budgets": receipt.search.budgets.to_dict()}
        if receipt.observation is not None:
            settings["premise_source"] = "native_tactic_state"
        limit = 1
    else:
        raise TypeError("expected a solver receipt with native replay evidence")
    if (task.prover != prover or task.operation != "proof_completion"
            or (task.task_id, task.environment_id, task.targets[0]) !=
            (receipt.task_id, receipt.environment_id, receipt.target)):
        raise ValueError("search receipt belongs to another proof task or environment")

    transitions = []
    for candidate, evidence in attempts:
        if candidate is None:
            raise ValueError("native replay evidence requires the submitted proof fragment")
        action = Action("edit_document", candidate, candidate)
        observation = Observation(evidence.execution_outcome, evidence.checker_outcome,
                                  evidence.task_success, evidence.stdout, evidence.stderr,
                                  evidence.duration_ms)
        transitions.append(Transition(action, observation, evidence.to_dict()))
        if evidence.task_success is not False:
            break
    if not transitions:
        return None

    manifest = RunManifest.for_proof_task(
        task, digest(receipt.to_dict()), digest(task_prompt(task, include_allowed_edits=False)),
        settings, max_attempts=limit if limit is not None else len(transitions),
    )
    final = transitions[-1]
    candidate = final.action.candidate
    try:
        artifact = assemble(task, candidate).to_dict()
    except ValueError:
        artifact = None
    episode = Episode(task.task_id, task.environment_id, manifest.run_id, task.to_dict(),
                      manifest.to_dict(), tuple(transitions), candidate, artifact, final.evidence)
    check_episode(episode, task)
    return episode

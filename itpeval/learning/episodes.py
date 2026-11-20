"""Recheck document episodes and export trainer-ready examples."""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Iterable

from itpeval.core.episodes import Episode
from itpeval.core.types import Artifact, TaskSpec, VerificationEvidence
from itpeval.environments import PreparedProject
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rewards import proof_reward
from itpeval.verification.service import assemble, verify


def check_episode(episode: Episode, task: TaskSpec) -> VerificationEvidence:
    """Validate recorded identities, edits and outcomes without launching a prover."""
    manifest = RunManifest.from_dict(episode.manifest)
    if (task != TaskSpec.from_dict(episode.task) or task.task_id != episode.task_id
            or task.environment_id != episode.environment_id
            or manifest.run_id != episode.run_id or task.task_id not in manifest.tasks
            or task.environment_id not in manifest.environments):
        raise ValueError("episode task, environment or manifest identity mismatch")
    final = VerificationEvidence.from_dict(episode.final_evidence)
    if final.task_id != task.task_id or final.environment_id != task.environment_id:
        raise ValueError("final evidence belongs to another task")
    try:
        assembled = assemble(task, episode.final_candidate)
    except ValueError:
        assembled = None
    if assembled is not None:
        if episode.final_artifact is None or assembled != Artifact.from_dict(episode.final_artifact):
            raise ValueError("exported artifact differs from assembled candidate")
        if final.task_success is not None and assembled.artifact_id != final.artifact_id:
            raise ValueError("final artifact digest differs from evidence")
    elif final.task_success is True or episode.final_artifact is not None:
        raise ValueError("final evidence or artifact for an invalid edit")
    if not episode.transitions or episode.transitions[-1].action.candidate != episode.final_candidate:
        raise ValueError("final candidate differs from last action")
    limit = manifest.budgets.get("max_attempts")
    if type(limit) is not int or len(episode.transitions) > limit:
        raise ValueError("episode exceeds its declared attempt budget")
    if any(t.observation.task_success is not False for t in episode.transitions[:-1]):
        raise ValueError("episode contains an action after a terminal observation")
    for transition in episode.transitions:
        observed = transition.observation
        evidence = VerificationEvidence.from_dict(transition.evidence)
        if (evidence.task_id, evidence.environment_id) != (task.task_id, task.environment_id):
            raise ValueError("transition evidence belongs to another task")
        if transition.action.kind == "generation_error":
            if (transition.action.raw_response or transition.action.candidate or
                    (evidence.execution_outcome, evidence.checker_outcome, evidence.task_success) !=
                    ("generation_error", "not_run", None)):
                raise ValueError("invalid generation failure in exported episode")
        elif transition.action.kind != "edit_document":
            raise ValueError("unsupported action in document episode")
        if evidence.task_success is not None:
            try:
                attempted = assemble(task, transition.action.candidate)
            except ValueError:
                allowed = {"policy_rejected"}
                if not transition.action.candidate.strip():
                    allowed.add("incomplete")
                if evidence.checker_outcome not in allowed or evidence.execution_outcome != "not_run":
                    raise ValueError("unassemblable transition claims native checker evidence")
                attempted = task.artifact
            if attempted.artifact_id != evidence.artifact_id:
                raise ValueError("transition candidate differs from its checked artifact")
        if any(getattr(observed, key) != getattr(evidence, key)
               for key in ("checker_outcome", "execution_outcome", "task_success", "stdout", "stderr", "duration_ms")):
            raise ValueError("transition observation and evidence disagree")
    return final


def replay(episode: Episode, *, task: TaskSpec, prepared: PreparedProject,
           receipt: Path | None = None) -> VerificationEvidence:
    """Check the exported actions and final artifact against a caller-selected task."""
    expected = check_episode(episode, task)
    observations = []
    for transition in episode.transitions:
        if transition.action.kind == "generation_error":
            raise ValueError("the generator failed before submitting an edit; no native check to replay")
        historical = VerificationEvidence.from_dict(transition.evidence)
        current = verify(task, transition.action.candidate, prepared=prepared)
        _compare(historical, current)
        if receipt is not None:
            observations.append(current.to_dict())
    final = verify(task, episode.final_candidate, prepared=prepared)
    _compare(expected, final)
    if receipt is not None:
        from itpeval.corpus.storage import jsonl
        receipt.parent.mkdir(parents=True, exist_ok=True)
        jsonl(receipt, [{"schema_version": 1, "task_id": task.task_id, "environment_id": task.environment_id,
                         "run_id": episode.run_id, "transitions": observations, "final": final.to_dict()}])
    return final


def _compare(first: VerificationEvidence, second: VerificationEvidence) -> None:
    for key in ("task_id", "environment_id", "artifact_id", "execution_outcome", "checker_outcome",
                "task_success", "completion_status", "target_preservation", "obligations", "evidence_references"):
        if getattr(first, key) != getattr(second, key):
            raise ValueError(f"replay differs on {key}")


def export_jsonl(episodes: Iterable[Episode], path: Path, *, view: str = "attempts") -> int:
    """Export attempts with exclusion reasons, or positive prompt/completion pairs."""
    if view in {"repair", "trajectory"}:
        from itpeval.corpus.storage import jsonl
        from itpeval.learning.views import repair_rows, trajectory_rows
        builder = repair_rows if view == "repair" else trajectory_rows
        count = 0

        def rows():
            nonlocal count
            for row in builder(episodes):
                count += 1
                yield row

        path.parent.mkdir(parents=True, exist_ok=True)
        jsonl(path, rows())
        return count
    if view not in {"attempts", "supervised", "episodes"}:
        raise ValueError(f"unknown export view {view!r}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as handle:
        tmp = Path(handle.name)
        count = 0
        try:
            for episode in episodes:
                task = TaskSpec.from_dict(episode.task)
                final = check_episode(episode, task)
                reward = proof_reward(task, final)
                if view == "episodes":
                    row = episode.to_dict()
                elif view == "supervised":
                    if reward.value != 1.0:
                        continue
                    row = {"prompt": task_prompt(task), "completion": episode.final_candidate,
                           "environment_id": task.environment_id, "task_id": task.task_id}
                else:
                    row = {"episode": episode.to_dict(), "reward": reward.value,
                           "disposition": reward.disposition}
                handle.write(json.dumps(row, ensure_ascii=False, allow_nan=False) + "\n")
                count += 1
            handle.flush()
            os.replace(tmp, path)
        finally:
            tmp.unlink(missing_ok=True)
    return count


def task_prompt(task: TaskSpec, *, include_allowed_edits: bool = True) -> str:
    """Describe the hole, with optional choices for constrained evaluation."""
    region = task.editable_regions[0]
    if task.is_detached_certificate:
        fixed = {item.path: item.data.decode("utf-8", errors="replace")
                 for item in task.artifact.files if item.path != region.path}
        if task.candidate_format == "binary_certificate":
            output = "Return only the certificate bytes as a canonical Base64 string."
        elif task.candidate_format == "text_certificate":
            output = "Return only the certificate text."
        else:
            output = "Return only the certificate object."
        kind = task.candidate_format.removesuffix("_certificate")
        if kind == "json":
            kind = "JSON"
        return (f"Produce a {task.prover} {kind} certificate for {task.targets[0]} in {region.path}. "
                f"{output} The fixed inputs are\n"
                + json.dumps(fixed, ensure_ascii=False))
    source = next(file.data for file in task.artifact.files if file.path == region.path)
    template = source[:region.start] + b"<PROOF>" + source[region.end:]
    if include_allowed_edits:
        return (f"Complete <PROOF> in {region.path} using one permitted edit.\n"
                + json.dumps(task.allowed_edits, ensure_ascii=False) + "\n" + template.decode())
    return (f"Fill <PROOF> in {region.path} with a proof fragment for {task.prover}. "
            "Return only the fragment.\n" + template.decode())

"""Bind evaluation to a trusted task and prepared environment selected by the caller."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.learning.manifests import RunManifest

if TYPE_CHECKING:
    from itpeval.environments import PreparedProject


@dataclass(frozen=True)
class TaskProfile:
    task: TaskSpec
    prepared: PreparedProject

    @classmethod
    def from_lock(cls, lock: Path, manifest_path: str = "completion.json") -> TaskProfile:
        from itpeval.backends.projects import build_task
        from itpeval.environments import load_project

        project = load_project(lock)
        return cls(build_task(project, manifest_path), project)

    def validate(self) -> None:
        self.prepared.validate()
        if self.task.environment_id != self.prepared.environment_id or self.task.prover != self.prepared.spec.prover:
            raise ValueError("task differs from the prepared environment")

    def verify(self, record: dict) -> dict:
        from itpeval.verification.service import verify

        if record["task_id"] != self.task.task_id or record["tgt_prover"] != self.task.prover:
            raise ValueError("input specifies another task or prover")
        if record.get("translate_error") and not record.get("generated"):
            evidence = VerificationEvidence(self.task.task_id, self.task.environment_id,
                self.task.artifact.artifact_id, "generation_error", "not_run", None,
                "unchecked", "unknown", stderr=record["translate_error"])
        else:
            evidence = verify(self.task, record.get("generated", ""), prepared=self.prepared)
        return {**record, "result_schema": "itpeval-task-v1", "environment_id": self.task.environment_id,
                "verified": evidence.task_success is True, "task_success": evidence.task_success,
                "verify_error": "" if evidence.task_success else (evidence.stderr or evidence.stdout or evidence.execution_outcome),
                "verify_ms": evidence.duration_ms, "evidence": evidence.to_dict()}

    def manifest(self, dataset_id: str, model_config: dict, *, seed: int | None = None) -> RunManifest:
        from itpeval.core.records import digest
        task = self.task
        request = completion_request(self)
        return RunManifest.for_proof_task(task, dataset_id, digest([request["system_prompt"], request["user_prompt"]]),
                                          model_config, seed=seed)


def completion_request(profile: TaskProfile, sample_idx: int = 0) -> dict:
    """Keep task binding outside the messages submitted to a provider."""
    from itpeval.core.records import digest
    from itpeval.learning.episodes import task_prompt

    task = profile.task
    return {"custom_id": "task_" + digest([task.task_id, sample_idx])[:40],
            "system_prompt": "Reply with exactly one permitted proof edit.",
            "user_prompt": task_prompt(task), "_task_id": task.task_id,
            "_tgt_prover": task.prover, "_sample_idx": sample_idx}


def completion_record(request: dict, model: dict, generated: str) -> dict:
    return {"result_schema": "itpeval-task-v1", "task_id": request["_task_id"],
            "tgt_prover": request["_tgt_prover"], "mode": "proof_completion",
            "custom_id": request["custom_id"], "model": model["label"], "model_id": model["id"],
            "sample_idx": request.get("_sample_idx", 0), "temperature": 0.0,
            "generated": generated, "raw_generated": generated}

"""Run a pinned detached certificate checker and bind its receipt to the task."""
from __future__ import annotations

import json
import os
from dataclasses import dataclass
from typing import Literal

from itpeval.backends.external import DetachedTarget, detached_target
from itpeval.core.records import Record
from itpeval.runtime.process import run_process


@dataclass(frozen=True)
class DetachedProofReceipt(Record):
    task_id: str
    environment_id: str
    artifact_id: str
    target: DetachedTarget
    inputs: dict[str, str]
    proof_sha256: str
    status: Literal["accepted", "rejected", "incomplete"]
    assumptions: tuple[str, ...]
    detail: str = ""


def run_detached_checker(task, prepared, artifact, source, attempt, cancel):
    target = detached_target(prepared, task.manifest_path)
    inputs = {entry.path: entry.sha256 for entry in artifact.files}
    request = {"schema_version": 1, "operation": task.operation, "task_id": task.task_id,
               "environment_id": task.environment_id, "artifact_id": artifact.artifact_id,
               "target": target.to_dict(), "proof_file": artifact.entrypoint, "inputs": inputs,
               "candidate_format": task.candidate_format}
    request_path = attempt / "request.json"
    request_path.write_text(json.dumps(request, ensure_ascii=False), encoding="utf-8")
    home = attempt / "home"
    scratch = attempt / "tmp"
    home.mkdir()
    scratch.mkdir()
    environment = {name: os.environ[name] for name in ("PATH", "LANG", "LC_ALL") if name in os.environ}
    environment.update(HOME=str(home), TMPDIR=str(scratch))
    adapter = prepared.adapter
    budgets = task.budgets
    process = run_process(adapter.command(adapter.checker, "--request", request_path, scratch=scratch),
                          cwd=source, env=environment,
                          timeout_s=budgets.timeout_s, max_log_bytes=budgets.max_log_bytes,
                          memory_bytes=budgets.memory_bytes, cpu_seconds=budgets.cpu_seconds, cancel=cancel)
    if process.outcome != "exited" or process.returncode or process.truncated:
        return process, None
    try:
        receipt = DetachedProofReceipt.from_dict(json.loads(process.stdout))
        if ((receipt.task_id, receipt.environment_id, receipt.artifact_id) !=
                (task.task_id, task.environment_id, artifact.artifact_id) or receipt.target != target
                or receipt.inputs != inputs or receipt.proof_sha256 != inputs[artifact.entrypoint]):
            return process, None
    except (ValueError, TypeError, KeyError, RecursionError):
        return process, None
    return process, receipt

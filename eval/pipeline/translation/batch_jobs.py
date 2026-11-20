"""Immutable generation plans and durable state for batch submit and collect."""

import json
import os
import tempfile
from pathlib import Path

from itpeval.core.records import digest
from itpeval.learning.manifests import RunManifest

from eval.pipeline.manifests import records_digest


def save_job(path: Path, data: dict, *, indent: int | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        staging = Path(stream.name)
        try:
            json.dump(data, stream, ensure_ascii=False, allow_nan=False, indent=indent)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
            os.replace(staging, path)
        finally:
            staging.unlink(missing_ok=True)


def generation_manifest(job: dict) -> RunManifest:
    requests = job["requests"]
    models = {name: {"id": info["model_id"], "provider": info["provider"],
                     "chunk_size": info["chunk_size"], "max_tokens": info["max_tokens"],
                     "temperature": info["temperature"]}
              for name, info in job["models"].items()}
    return RunManifest((job["task_id"],) if job.get("task_id") else (),
                       (job["environment_id"],) if job.get("environment_id") else (),
                       "batch_generation." + job["mode"] + ".v1",
                       records_digest({k: v for k, v in r.items() if k not in ("system_prompt", "user_prompt")}
                                      for r in requests),
                       records_digest([r["custom_id"], r["system_prompt"], r["user_prompt"]] for r in requests),
                       models, None, job["budgets"])


def validate_job(path: Path, job: dict) -> None:
    sidecar = path.with_suffix(path.suffix + ".manifest.json")
    if job.get("job_version") is None and not sidecar.is_file():
        return  # Archived submissions predate generation manifests.
    if job.get("job_version") != 1:
        raise ValueError("unsupported batch job version")
    manifest = generation_manifest(job)
    if job.get("run_id") != manifest.run_id:
        raise ValueError("batch requests or model configuration differ from the submitted manifest")
    manifest.bind(path)


def submit_recording(spool: Path, requests: list[dict], responses: dict) -> str:
    """Submit to the local prerecorded transport. Receipts contain the actual request payload."""
    contents = {"requests": requests, "results": {r["custom_id"]: responses[r["custom_id"]]
                                                  for r in requests if r["custom_id"] in responses}}
    handle = digest(contents)
    save_job(spool / (handle + ".json"), contents)
    return handle


def poll_recording(spool: Path, handle: str):
    if len(handle) != 64 or any(c not in "0123456789abcdef" for c in handle):
        raise ValueError("invalid prerecorded batch handle")
    contents = json.loads((spool / (handle + ".json")).read_bytes())
    if digest(contents) != handle:
        raise ValueError("prerecorded batch receipt differs from its submitted payload")
    return "completed", contents["results"]

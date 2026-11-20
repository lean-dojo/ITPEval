"""Acceptance of byte-range edits against trusted, positively specified tasks."""
from base64 import b64decode, b64encode
from dataclasses import replace
import json
from pathlib import PurePosixPath

from itpeval.backends.registry import curated_task
from itpeval.core.types import Artifact, TaskSpec

from .fragments import permitted


def candidate_from_bytes(task: TaskSpec, source: bytes) -> str:
    """Encode a proof file for the string-based candidate and episode APIs."""
    if task.candidate_format == "binary_certificate":
        return b64encode(source).decode("ascii")
    return source.decode("utf-8")


def _certificate_bytes(task, candidate):
    if not isinstance(candidate, str) or not candidate.strip():
        raise ValueError("supply a nonempty proof certificate")
    if task.candidate_format == "binary_certificate":
        try:
            raw = b64decode(candidate, validate=True)
        except ValueError as exc:
            raise ValueError("the binary certificate must be canonical Base64") from exc
        if not raw or candidate_from_bytes(task, raw) != candidate:
            raise ValueError("the binary certificate must be canonical Base64")
        return raw
    if task.candidate_format == "json_certificate":
        try:
            valid = isinstance(json.loads(candidate), dict)
        except (ValueError, RecursionError):
            valid = False
        if not valid:
            raise ValueError("the proof certificate must be one JSON object")
    return candidate.encode("utf-8")


def assemble(task: TaskSpec, candidate: str | None) -> Artifact:
    if task.operation != "proof_completion":
        if candidate is not None:
            raise ValueError("artifact and statement operations accept only the fixed artifact")
        return task.artifact
    if task.is_detached_certificate:
        replacement = _certificate_bytes(task, candidate)
    elif candidate is None or not permitted(task.prover, candidate, task.allowed_edits, task.proof_atoms):
        raise ValueError("candidate is outside the task's allowed proof fragments")
    else:
        replacement = candidate.encode("utf-8")
    region = task.editable_regions[0]
    files = {entry.path: entry.data for entry in task.artifact.files}
    source = files[region.path]
    files[region.path] = source[:region.start] + replacement + source[region.end:]
    transform = f"replaced bytes [{region.start},{region.end}) of {region.path}"
    return Artifact.from_files(task.artifact.entrypoint, files,
                               (*task.artifact.transformations, transform))


def reviewed(task: TaskSpec, prepared) -> bool:
    return reviewed_document_template(task, prepared) is not None


def reviewed_document_template(task: TaskSpec, prepared) -> bytes | None:
    """Return the original entry's fixed bytes for a task with a trusted target witness."""
    if task.manifest_path:
        from itpeval.backends.projects import _build_with_document_template
        reference, template = _build_with_document_template(prepared, task.manifest_path)
    else:
        reference = curated_task(task.prover, task.environment_id)
        template = next(item.data for item in reference.artifact.files if item.path == reference.artifact.entrypoint)
    # Resource budgets affect task identity but do not change the proposition.
    return template if task == replace(reference, budgets=task.budgets) else None

def validate_inputs(task: TaskSpec, artifact: Artifact) -> None:
    """Keep native build outputs out of the mutable part of an attempt."""
    if task.is_detached_certificate:
        return
    generated = {".olean", ".ilean", ".vo", ".vos", ".vok", ".glob", ".agdai", ".uo",
                 ".ui", ".heap", ".summary", ".err"}
    for entry in artifact.files:
        path = PurePosixPath(entry.path)
        if (path.suffix in generated or ".hol" in path.parts or "pvsbin" in path.parts
                or path.name == ".pvscontext" or path.name.startswith("itpeval-witness-")
                or path.name == "itpeval-target-witness"):
            raise ValueError(f"native build output is outside the task source profile: {entry.path}")
        if task.operation == "proof_completion" and task.prover == "pvs" and path.suffix == ".prf":
            raise ValueError("the PVS completion profile uses the source's inline ProofLite proof")

"""Portable environment, source artifact, task and verification contracts."""
from __future__ import annotations

import base64
import hashlib
import math
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Literal, Mapping

from .records import Record, digest


@dataclass(frozen=True)
class EnvironmentSpec(Record):
    prover: str
    prover_build: str
    project_revision: str
    libraries: tuple[tuple[str, str], ...] = ()
    imports: tuple[str, ...] = ()
    options: tuple[tuple[str, str], ...] = ()
    checking_profile: str = "strict"
    project_name: str = ""
    project_commit: str = ""
    library_commits: tuple[tuple[str, str], ...] = ()
    resolved_imports: tuple[tuple[str, str, str, str], ...] = ()

    def to_dict(self):
        record = super().to_dict()
        # Empty optional bindings preserve schema-v1 identities and old locks.
        if not self.resolved_imports:
            record.pop("resolved_imports")
        return record

    @property
    def environment_id(self) -> str:
        return digest(self.to_dict())


def logical_path(name: str) -> str:
    path = PurePosixPath(name)
    if (not name or name in (".", "..") or path.is_absolute() or ".." in path.parts
            or any(ord(c) < 32 for c in name) or name != path.as_posix() or "\\" in name or "\0" in name):
        raise ValueError(f"invalid logical path: {name!r}")
    return name


@dataclass(frozen=True)
class ArtifactFile(Record):
    path: str
    content_base64: str
    sha256: str

    def __post_init__(self):
        logical_path(self.path)
        if hashlib.sha256(self.data).hexdigest() != self.sha256:
            raise ValueError(f"hash mismatch for {self.path}")

    @property
    def data(self) -> bytes:
        return base64.b64decode(self.content_base64, validate=True)


@dataclass(frozen=True)
class Artifact(Record):
    entrypoint: str
    files: tuple[ArtifactFile, ...]
    transformations: tuple[str, ...] = ()

    def __post_init__(self):
        names = {item.path for item in self.files}
        if len(names) != len(self.files) or self.entrypoint not in names:
            raise ValueError("entrypoint must exist and artifact paths must be unique")
        for name in names:
            if any(str(parent) in names for parent in PurePosixPath(name).parents):
                raise ValueError("artifact file overlaps a directory")

    @classmethod
    def from_files(cls, entrypoint: str, files: Mapping[str, bytes],
                   transformations: tuple[str, ...] = ()) -> Artifact:
        return cls(entrypoint, tuple(ArtifactFile(name, base64.b64encode(data).decode("ascii"),
                                                  hashlib.sha256(data).hexdigest())
                                     for name, data in sorted(files.items())), transformations)

    @property
    def artifact_id(self) -> str:
        return digest(self.to_dict())

    def materialize(self, root: Path) -> None:
        """Materialize in an empty workspace so inputs cannot resolve to old outputs."""
        root.mkdir(parents=True, exist_ok=True)
        if any(root.iterdir()):
            raise ValueError("artifact workspace must be empty")
        for entry in self.files:
            dest = root / entry.path
            dest.parent.mkdir(parents=True, exist_ok=True)
            with dest.open("xb") as output:
                output.write(entry.data)


@dataclass(frozen=True)
class EditableRegion(Record):
    path: str
    start: int
    end: int

    def __post_init__(self):
        logical_path(self.path)
        if self.start < 0 or self.end < self.start:
            raise ValueError("invalid byte offsets")


@dataclass(frozen=True)
class Budgets(Record):
    timeout_s: float = 300
    max_log_bytes: int = 1 << 20
    memory_bytes: int | None = None
    cpu_seconds: int | None = None

    def __post_init__(self):
        if not math.isfinite(self.timeout_s) or self.timeout_s <= 0 or self.max_log_bytes <= 0:
            raise ValueError("timeout and output budgets must be positive")
        if any(limit is not None and limit <= 0 for limit in (self.memory_bytes, self.cpu_seconds)):
            raise ValueError("resource limits must be positive")


@dataclass(frozen=True)
class TaskSpec(Record):
    prover: str
    environment_id: str
    operation: str
    artifact: Artifact
    targets: tuple[str, ...] = ()
    editable_regions: tuple[EditableRegion, ...] = ()
    allowed_assumptions: tuple[str, ...] = ()
    allowed_edits: tuple[str, ...] = ()
    obligations: tuple[str, ...] = ()
    budgets: Budgets = field(default_factory=Budgets)
    proof_atoms: tuple[str, ...] = ()
    manifest_path: str | None = None
    native_receipt: str | None = None
    dependency_sources: tuple[str, ...] = ()
    candidate_format: Literal["native_fragment", "json_certificate", "text_certificate", "binary_certificate"] = "native_fragment"

    @property
    def is_detached_certificate(self) -> bool:
        return self.candidate_format != "native_fragment"

    def __post_init__(self):
        if self.candidate_format not in {"native_fragment", "json_certificate", "text_certificate", "binary_certificate"}:
            raise ValueError("unsupported candidate format")
        if self.dependency_sources:
            names = {entry.path for entry in self.artifact.files} - {self.artifact.entrypoint}
            suffix = {"lean4": ".lean", "rocq": ".v"}.get(self.prover)
            if (suffix is None or len(self.dependency_sources) != len(set(self.dependency_sources))
                    or any(path not in names or not path.endswith(suffix) for path in self.dependency_sources)):
                raise ValueError("expected distinct local dependency sources in the supported prover language")
        if self.manifest_path is not None:
            logical_path(self.manifest_path)
        if not self.environment_id:
            raise ValueError("missing environment identity")
        if self.operation == "proof_completion":
            if (not self.targets or len(self.editable_regions) != 1
                    or not self.is_detached_certificate and not self.allowed_edits):
                raise ValueError("proof completion requires named targets and a restricted proof slot")
            region = self.editable_regions[0]
            files = {item.path: item for item in self.artifact.files}
            if region.path not in files or region.end > len(files[region.path].data):
                raise ValueError("editable region outside artifact")
            if (self.is_detached_certificate and
                    (self.allowed_edits or self.proof_atoms or region.path != self.artifact.entrypoint
                     or region.start != 0 or region.end != 0 or files[region.path].data)):
                raise ValueError("a detached certificate occupies its own complete blank file")
        elif (self.editable_regions or self.allowed_edits or self.proof_atoms or self.native_receipt
              or self.is_detached_certificate):
            raise ValueError("only proof completion supports edits")

    def to_dict(self):
        record = super().to_dict()
        if self.candidate_format == "native_fragment":
            record.pop("candidate_format")
        return record

    @property
    def task_id(self) -> str:
        return digest(self.to_dict())


@dataclass(frozen=True)
class VerificationEvidence(Record):
    task_id: str
    environment_id: str
    artifact_id: str
    execution_outcome: str
    checker_outcome: str
    task_success: bool | None
    target_preservation: str
    completion_status: str
    obligations: tuple[tuple[str, str], ...] = ()
    duration_ms: int = 0
    returncode: int | None = None
    stdout: str = ""
    stderr: str = ""
    evidence_references: tuple[str, ...] = ()
    workspace: str | None = None
    peak_process_rss_bytes: int | None = None
    cpu_time_s: float | None = None
    logs_truncated: bool = False

# Keep these records importable from the original public module.
from .declarations import Context as Context, DependencyEdge as DependencyEdge, FormalObject as FormalObject
from .episodes import Action as Action, Episode as Episode, Observation as Observation, Transition as Transition

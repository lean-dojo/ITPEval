from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, Protocol

from .capabilities import Capability
from .types import Artifact, TaskSpec, VerificationEvidence

if TYPE_CHECKING:
    from itpeval.environments import PreparedProject
    from itpeval.extraction import ExtractionResult
    from itpeval.runtime.sessions import DocumentSession


class Backend(Protocol):
    prover: str

    def capabilities(self, *, prepared=None, qualification_report=None) -> tuple[Capability, ...]: ...

    def curated_task(self, environment_id: str) -> TaskSpec: ...

    def build_task(self, prepared: PreparedProject, manifest_path: str = "completion.json") -> TaskSpec: ...

    def inspect_declarations(self, prepared: PreparedProject, entrypoint: str, destination: Path, *,
                             timeout_s: float = 180) -> ExtractionResult: ...

    def open_document(self, task: TaskSpec, *, prepared: PreparedProject) -> DocumentSession: ...

    def check(self, task: TaskSpec, candidate: str | None = None, *,
              prepared, **options) -> VerificationEvidence: ...

    def check_document(self, task: TaskSpec, document: Artifact | str | bytes, *,
                       prepared: PreparedProject, **options) -> VerificationEvidence: ...


class Verifier(Protocol):
    def __call__(self, task: TaskSpec, candidate: str | None, *, prepared) -> VerificationEvidence: ...

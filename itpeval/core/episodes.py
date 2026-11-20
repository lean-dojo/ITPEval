"""Portable records for document edits, checker feedback, and final verification."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .records import Record


@dataclass(frozen=True)
class Action(Record):
    kind: str
    raw_response: str
    candidate: str


@dataclass(frozen=True)
class Observation(Record):
    execution_outcome: str
    checker_outcome: str
    task_success: bool | None
    stdout: str
    stderr: str
    duration_ms: int


@dataclass(frozen=True)
class Transition(Record):
    action: Action
    observation: Observation
    evidence: dict[str, Any]


@dataclass(frozen=True)
class Episode(Record):
    task_id: str
    environment_id: str
    run_id: str
    task: dict[str, Any]
    manifest: dict[str, Any]
    transitions: tuple[Transition, ...]
    final_candidate: str
    final_artifact: dict[str, Any] | None
    final_evidence: dict[str, Any]

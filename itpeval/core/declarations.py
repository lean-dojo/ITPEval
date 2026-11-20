"""Occurrence identities and source-grounded declaration records."""

from dataclasses import dataclass

from .records import Record


@dataclass(frozen=True)
class FormalObject(Record):
    declaration_id: str
    environment_id: str
    prover: str
    name: str
    kind: str
    statement: str
    source_path: str
    source_hash: str
    start_byte: int
    end_byte: int
    context_id: str
    checking_status: str
    evidence: tuple[str, ...] = ()


@dataclass(frozen=True)
class Context(Record):
    context_id: str
    environment_id: str
    source_path: str
    visible: tuple[str, ...]
    imports: tuple[str, ...] = ()
    hypotheses: tuple[str, ...] = ()
    disjoint: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True)
class DependencyEdge(Record):
    origin: str
    relation: str
    target_name: str
    target_id: str | None

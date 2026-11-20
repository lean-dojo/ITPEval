from dataclasses import dataclass

from .records import Record


@dataclass(frozen=True)
class Capability(Record):
    operation: str
    status: str
    semantics: str
    includes_environment_changes: bool = False
    survives_restart: bool = False
    portable_between_workers: bool = False

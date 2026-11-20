"""Locate native shell adapters for the CLI and run_itp's file-checking interface."""
from __future__ import annotations

import os
import re
from pathlib import Path

BUILTIN = Path(__file__).resolve().parent / "provers"
PROVER_ID = re.compile(r"[a-z0-9][a-z0-9-]*")


def external_root() -> Path | None:
    directory = os.environ.get("ITPEVAL_ADAPTER_DIR")
    return Path(directory).expanduser().resolve() if directory else None


def adapter_root(prover: str) -> Path:
    """Prefer the bundled adapter, then look for a checker in the configured directory."""
    if not PROVER_ID.fullmatch(prover):
        raise ValueError(f"invalid prover ID: {prover!r}")
    builtin = BUILTIN / prover
    extra = external_root()
    if not builtin.exists() and extra and (extra / prover / "check.sh").is_file():
        return extra / prover
    return builtin

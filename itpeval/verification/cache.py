"""Explicit reuse of completed native checks in a local experiment."""
from __future__ import annotations

import json
import sqlite3
import sys
from contextlib import closing
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path

from itpeval.core.records import digest
from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.environments import PreparedProject
from itpeval.verification.service import verify


@dataclass(frozen=True)
class VerificationLookup:
    evidence: VerificationEvidence
    cache_hit: bool
    key: str


def _implementation(prover: str):
    package = Path(__file__).resolve().parents[1]
    # A changed admission policy or target observer invalidates an old answer
    # even when the installed native compiler and the candidate are identical.
    implementation = {}
    for group in ("verification", "runtime", "core", "environments"):
        for path in sorted((package / group).glob("*.py")):
            implementation[str(path.relative_to(package))] = sha256(path.read_bytes()).hexdigest()
    backend = "hol_light" if prover == "hol-light" else prover
    if backend.isidentifier():
        for path in sorted((package / "backends" / backend).glob("*.py")):
            implementation[str(path.relative_to(package))] = sha256(path.read_bytes()).hexdigest()
    for name in ("adapter_paths.py", "backends/external.py", "backends/projects.py", "backends/registry.py",
                 "backends/tasks.json"):
        implementation[name] = sha256((package / name).read_bytes()).hexdigest()
    return {"implementation": implementation, "python": list(sys.version_info[:3])}


def verifier_revision(prover: str) -> str:
    """Identify the Python checker, policy, target adapter and interpreter used for this prover."""
    return digest(_implementation(prover))


def _key(task, candidate):
    return digest({"schema": 1, "environment_id": task.environment_id, "task_id": task.task_id,
                   "candidate": candidate, **_implementation(task.prover)})


def verify_cached(task: TaskSpec, candidate: str | None = None, *, prepared: PreparedProject,
                  cache: Path, cancel=None) -> VerificationLookup:
    """Retrieve evidence for identical inputs, or run and record a native check.

    Only definite native acceptances and rejections enter the cache. Concurrent
    misses can both do real work. Each caller reports whether it ran the prover.
    Finalization and episode replay call the fresh verification service directly.
    """
    key = _key(task, candidate)
    cache = Path(cache)
    cache.mkdir(parents=True, exist_ok=True)
    with closing(sqlite3.connect(cache / "verification.sqlite3", timeout=60)) as db:
        db.execute("CREATE TABLE IF NOT EXISTS results "
                   "(key TEXT PRIMARY KEY, checksum TEXT NOT NULL, evidence TEXT NOT NULL)")
        hit = db.execute("SELECT checksum, evidence FROM results WHERE key=?", (key,)).fetchone()
        if (hit and prepared.environment_id == task.environment_id
                and (cancel is None or not cancel.is_set())):
            try:
                prepared.validate()
            except (OSError, ValueError, RuntimeError):
                # The ordinary service classifies the unavailable environment.
                pass
            else:
                checksum, payload = hit
                if sha256(payload.encode()).hexdigest() != checksum:
                    raise ValueError("damaged verification cache entry")
                evidence = VerificationEvidence.from_dict(json.loads(payload))
                if evidence.task_id != task.task_id or evidence.environment_id != task.environment_id:
                    raise ValueError("cached evidence identity differs from the request")
                return VerificationLookup(evidence, True, key)
        evidence = verify(task, candidate, prepared=prepared, cancel=cancel)
        if (evidence.execution_outcome == "exited" and evidence.task_success is not None
                and evidence.checker_outcome in {"accepted", "rejected", "incomplete"}):
            payload = json.dumps(evidence.to_dict(), ensure_ascii=False, sort_keys=True)
            with db:
                db.execute("INSERT OR IGNORE INTO results VALUES (?, ?, ?)",
                           (key, sha256(payload.encode()).hexdigest(), payload))
        return VerificationLookup(evidence, False, key)

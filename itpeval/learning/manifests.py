"""Content-addressed run configuration and atomic checkpoint manifest validation."""

from __future__ import annotations

import json
import os
import tempfile
from dataclasses import dataclass, replace
from typing import Any
from pathlib import Path

from itpeval.core.records import Record, digest


@dataclass(frozen=True)
class RunManifest(Record):
    tasks: tuple[str, ...]
    environments: tuple[str, ...]
    policy: str
    dataset_id: str
    prompt_id: str
    model_config: dict[str, Any]
    seed: int | None
    budgets: dict[str, Any]

    @classmethod
    def for_proof_task(cls, task, dataset_id: str, prompt_id: str, model_config: dict, *,
                       seed: int | None = None, max_attempts: int | None = None):
        """Bind new proof runs to the native task and the installed verifier implementation."""
        from itpeval.verification.cache import verifier_revision

        budgets = {"checker": task.budgets.to_dict(), "verifier_revision": verifier_revision(task.prover)}
        if max_attempts is not None:
            if type(max_attempts) is not int or max_attempts < 1:
                raise ValueError("max_attempts must be a positive integer")
            budgets["max_attempts"] = max_attempts
        return cls((task.task_id,), (task.environment_id,), "proof_completion.v1", dataset_id, prompt_id,
                   model_config, seed, budgets)

    @classmethod
    def for_native_proof_task(cls, task, dataset_id: str, prompt_id: str, model_config: dict, *,
                              max_attempts: int, seed: int | None = None):
        """Bind a run that records native actions and goal observations."""
        manifest = cls.for_proof_task(task, dataset_id, prompt_id, model_config,
                                     max_attempts=max_attempts, seed=seed)
        return replace(manifest, policy="native_proof.v1")

    @property
    def run_id(self) -> str:
        return digest(self.to_dict())

    def bind(self, results: Path, *checkpoint_paths: Path) -> None:
        """Publish once, then compare before any job can reuse previous results."""
        results.parent.mkdir(parents=True, exist_ok=True)
        path = results.with_suffix(results.suffix + ".manifest.json")
        if not path.exists():
            if any(p.exists() and p.stat().st_size for p in (results, *checkpoint_paths)):
                raise ValueError(f"existing results have no run manifest; select a new output: {results}")
            with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False, encoding="utf-8") as handle:
                tmp = Path(handle.name)
                try:
                    json.dump(self.to_dict(), handle, ensure_ascii=False, sort_keys=True)
                    handle.flush()
                    try:
                        os.link(tmp, path)
                    except FileExistsError:
                        pass
                finally:
                    tmp.unlink(missing_ok=True)
        saved = self.from_dict(json.loads(path.read_text(encoding="utf-8")))
        if saved.run_id != self.run_id:
            raise ValueError(f"run manifest mismatch for {results}")

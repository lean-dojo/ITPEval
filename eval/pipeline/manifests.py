"""Checkpoint compatibility for archived translation and task-bound evaluation."""

from __future__ import annotations

import hashlib
import os
import subprocess
from functools import lru_cache
from pathlib import Path

from itpeval.core.records import digest
from itpeval.learning.manifests import RunManifest

from eval.pipeline.config import PROVER_TIMEOUTS


def records_digest(records) -> str:
    h = hashlib.sha256()
    for record in records:
        h.update(bytes.fromhex(digest(record)))
    return h.hexdigest()


def legacy_environments(provers):
    """Identify the native builds used by full-file benchmark verification."""
    from itpeval.backends.registry import curated_project
    from itpeval.cli.lib import default_prefix
    from itpeval.environments import prepare_project

    prefix = default_prefix().resolve()
    home = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    cache = Path(os.environ.get("ITPEVAL_EVAL_ENV_CACHE", home / "itpeval/evaluation-environments"))
    package = Path(__file__).resolve().parent
    from itpeval import adapter_paths, itp, staging, validation
    policy = digest([hashlib.sha256(path.read_bytes()).hexdigest() for path in (
        package / "verify.py", package / "translation/scaffold.py", package / "translation/validation.py",
        Path(itp.__file__), Path(adapter_paths.__file__), Path(staging.__file__), Path(validation.__file__),
    )])
    # Path selectors and native checker flags can change full-file admission behavior.
    settings = digest({k: v for k, v in os.environ.items()
                       if k.startswith(("ITPEVAL_", "LEAN_", "MIZFILES", "PVSPATH", "ACL2_SYSTEM_BOOKS"))
                       and k not in {"ITPEVAL_EVAL_ENV_CACHE", "ITPEVAL_TEST_CACHE", "ITPEVAL_CONFORMANCE_PROVER",
                                     "ITPEVAL_RESULTS_DIR"}})
    ids = []
    for prover in sorted(set(provers)):
        try:
            prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache,
                                       checking_profile="legacy_translation")
            identity = prepared.environment_id
        except (ValueError, OSError, subprocess.SubprocessError) as exc:
            identity = ["unavailable", type(exc).__name__, str(exc)]
        ids.append(digest([prover, str(prefix), policy, settings, identity]))
    return tuple(ids)


def translation_manifest(models, pairs, mode, k, temperature, max_tokens, no_verify):
    # Both the prompt implementation and the prover-specific prompt strings affect generation.
    package = Path(__file__).parent
    prompt_sources = [(package / filename).read_bytes() for filename in ("config.py", "translation/prompt.py")]
    prompt_id = digest([hashlib.sha256(data).hexdigest() for data in prompt_sources])
    @lru_cache(maxsize=None)
    def source_digest(source):
        return hashlib.sha256(source.encode("utf-8")).hexdigest()

    dataset_id = records_digest(
        (p.get("corpus"), p["source"], p["theorem_id"], p["title"], p["src_prover"], p["tgt_prover"],
         p.get("source_sha256"), source_digest(p["src_content"]))
        for p in pairs
    )
    environments = () if no_verify else legacy_environments(p["tgt_prover"] for p in pairs)
    return RunManifest((), environments, f"legacy_translation.{mode}.v1", dataset_id, prompt_id,
                       {"models": models, "temperature": temperature, "samples": k}, None,
                       {"max_tokens": max_tokens, "native_timeouts": PROVER_TIMEOUTS,
                        "verify": not no_verify})

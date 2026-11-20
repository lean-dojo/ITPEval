"""Shared collector for adapters operating on an isolated, prepared project copy."""

import os
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

from itpeval.core.declarations import Context, DependencyEdge, FormalObject
from itpeval.core.records import Record
from itpeval.corpus.contexts import METAMATH_PREFIX
from itpeval.corpus.storage import object_id, project_file, store_blob


@dataclass(frozen=True)
class _MetamathContext(Record):
    context_id: str
    environment_id: str
    source_path: str
    visibility: dict[str, str | int]
    imports: tuple[str, ...]
    hypotheses: tuple[str, ...]
    disjoint: tuple[tuple[str, str], ...]


class Extraction:
    def __init__(self, prepared, root: Path, blob_dir: Path, timeout_s: float, *, context_storage="expanded"):
        if context_storage not in {"expanded", "compact"}:
            raise ValueError("context_storage must be expanded or compact")
        self.prepared = prepared
        self.root = root
        self.blob_dir = blob_dir
        self.timeout_s = timeout_s
        self.context_storage = context_storage
        self.declarations = []
        self.contexts = {}
        self.edges = []
        self.sources = {}
        self.structures = {}
        self.notes = defaultdict(list)
        self.availability = dict.fromkeys(
            ("names", "kinds", "source_mapping", "statements", "context", "imports",
             "statement_references", "definition_references", "proof_used_premises", "rewrite_rules",
             "generated_obligations", "term_trees", "action_traces"), "unavailable"
        )

    def source(self, path: str) -> bytes:
        raw = project_file(self.prepared.project, path).read_bytes()
        self.sources[path] = store_blob(self.blob_dir, raw)
        return raw

    def context(self, path, *, visible=(), imports=(), hypotheses=(), disjoint=()):
        env = self.prepared.environment_id
        values = (tuple(visible), tuple(imports), tuple(hypotheses), tuple(disjoint))
        key = object_id("context", env, path, values)
        self.contexts[key] = Context(key, env, path, *values)
        return key

    def metamath_context(self, path, *, assertions, assertion_digest, imports=(), hypotheses=(), disjoint=()):
        env = self.prepared.environment_id
        visibility = {"kind": METAMATH_PREFIX, "assertions": assertions}
        values = (tuple(imports), tuple(hypotheses), tuple(disjoint))
        key = object_id("context", env, path, (visibility, assertion_digest, *values))
        self.contexts[key] = _MetamathContext(key, env, path, visibility, *values)
        return key

    def declare(self, path, name, kind, statement, start_byte, end_byte, context_id,
                checking_status, *, evidence=()):
        if context_id not in self.contexts:
            raise ValueError("declaration context was not recorded")
        if path not in self.sources:
            self.source(path)
        if not 0 <= start_byte <= end_byte <= project_file(self.prepared.project, path).stat().st_size:
            raise ValueError(f"invalid source offsets for {name}")
        env = self.prepared.environment_id
        key = object_id("declaration", env, path, self.sources[path], name, start_byte)
        decl = FormalObject(key, env, self.prepared.spec.prover, name, kind, statement,
                            path, self.sources[path], start_byte, end_byte, context_id,
                            checking_status, tuple(evidence))
        self.declarations.append(decl)
        return key

    def edge(self, origin, relation, target_name, target_id=None):
        self.edges.append(DependencyEdge(origin, relation, target_name, target_id))

    def evidence(self, data: bytes):
        return store_blob(self.blob_dir, data)

    def run(self, cmd, *, env=None, stdin_path=None):
        """Run the native command with the same process supervision as verification."""
        from itpeval.runtime.process import run_process
        settings = {k: os.environ[k] for k in ("HOME", "USER", "LANG", "PATH", "LC_ALL")
                    if k in os.environ}
        settings.update(self.prepared.environment)
        if env:
            settings.update(env)
        result = run_process([str(s) for s in cmd], cwd=self.root, env=settings, stdin_path=stdin_path,
                             timeout_s=self.timeout_s, max_log_bytes=16 * 1024 * 1024)
        if result.returncode or result.outcome != "exited" or result.truncated:
            raise ValueError(f"{Path(str(cmd[0])).name} failed ({result.outcome}, "
                             f"{result.returncode}): {(result.stderr + result.stdout)[-2400:]}")
        return result.stdout, result.stderr

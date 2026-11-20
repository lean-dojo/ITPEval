"""Opt-in typed adapters and detached certificate tasks."""
from __future__ import annotations

import json
import sys
import sysconfig
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from itpeval.adapter_paths import PROVER_ID, external_root
from itpeval.core.records import Record
from itpeval.core.types import Artifact, Budgets, EditableRegion, TaskSpec, logical_path
from itpeval.corpus.storage import digest


@dataclass(frozen=True)
class ExternalAdapter:
    prover: str
    version: str
    descriptor: Path
    checker: Path
    extractor: Path | None
    inputs: tuple[tuple[str, Path], ...]
    interpreter: Path

    def command(self, script: Path, *arguments, scratch: Path) -> list[str]:
        # -B prevents writes. A fresh prefix also prevents reading caches that
        # sit next to a declared source module outside the prepared inputs.
        return [str(self.interpreter), "-I", "-S", "-B", "-X", f"pycache_prefix={scratch / 'pycache'}",
                str(script), *map(str, arguments)]

    def build_inputs(self) -> dict[str, Path]:
        roots = {"descriptor": self.descriptor, "checker": self.checker, "interpreter": self.interpreter}
        if self.extractor is not None:
            roots["extractor"] = self.extractor
        roots.update((f"adapter/{name}", path) for name, path in self.inputs)
        libdir, library = (sysconfig.get_config_var(name) for name in ("LIBDIR", "LDLIBRARY"))
        if libdir and library and (Path(libdir) / library).is_file():
            roots["libpython"] = (Path(libdir) / library).resolve()
        return roots


def external_adapter(prover: str) -> ExternalAdapter | None:
    """Read a descriptor from a configured directory without importing adapter code."""
    root = external_root()
    if root is None or not PROVER_ID.fullmatch(prover):
        return None
    directory = (root / prover).resolve()
    descriptor = (directory / "typed-adapter.json").resolve()
    if not (directory.is_relative_to(root) and descriptor.is_relative_to(directory) and descriptor.is_file()):
        return None
    value = json.loads(descriptor.read_bytes())
    required = {"schema_version", "id", "version", "checker"}
    if (not isinstance(value, dict) or not required.issubset(value)
            or value.keys() - (required | {"extractor", "inputs"})
            or type(value["schema_version"]) is not int or value["schema_version"] != 1
            or value["id"] != prover or not isinstance(value["version"], str)
            or not value["version"].strip() or not value["version"].isprintable()):
        raise ValueError(f"invalid typed adapter descriptor for {prover}")

    def path(name, *, script=False):
        if not isinstance(name, str):
            raise ValueError("expected an adapter-relative input path")
        resolved = (directory / logical_path(name)).resolve(strict=True)
        if (not resolved.is_relative_to(directory) or (script and not resolved.is_file())
                or not (resolved.is_file() or resolved.is_dir())):
            raise ValueError(f"expected an input inside the adapter directory: {name!r}")
        return resolved

    inputs = value.get("inputs", [])
    if (not isinstance(inputs, list) or not all(isinstance(name, str) for name in inputs)
            or len(inputs) != len(set(inputs))):
        raise ValueError("expected distinct adapter input paths")
    extractor = path(value["extractor"], script=True) if "extractor" in value else None
    return ExternalAdapter(prover, value["version"], descriptor, path(value["checker"], script=True),
                           extractor, tuple((name, path(name)) for name in sorted(inputs)),
                           Path(sys.executable).resolve(strict=True))


def external_adapter_ids() -> tuple[str, ...]:
    root = external_root()
    if root is None or not root.is_dir():
        return ()
    return tuple(sorted(path.name for path in root.iterdir() if PROVER_ID.fullmatch(path.name)
                        and path.resolve().is_relative_to(root) and (path / "typed-adapter.json").is_file()))


@dataclass(frozen=True)
class DetachedCompletionManifest(Record):
    source_path: str
    proof_file: str
    files: tuple[str, ...]
    anchor: str
    target: str
    statement: str
    allowed_assumptions: tuple[str, ...] = ()
    budgets: Budgets = field(default_factory=Budgets)
    certificate_format: Literal["json", "text", "binary"] = "json"

    def __post_init__(self):
        if (self.source_path == self.proof_file or not {self.source_path, self.proof_file}.issubset(self.files)
                or len(self.files) != len(set(self.files)) or not self.anchor or not self.target.strip()
                or not self.statement.strip() or len(self.allowed_assumptions) != len(set(self.allowed_assumptions))):
            raise ValueError("expected a named target with a separate certificate file and fixed inputs")
        if self.certificate_format not in {"json", "text", "binary"}:
            raise ValueError("unsupported detached certificate format")


@dataclass(frozen=True)
class DetachedTarget(Record):
    source_path: str
    name: str
    start_byte: int
    end_byte: int
    statement: str
    source_sha256: str
    statement_sha256: str


def _detached_manifest(prepared, manifest_path):
    from itpeval.backends.projects import project_file

    return DetachedCompletionManifest.from_dict(json.loads(project_file(prepared.project, manifest_path).read_bytes()))


def _target_in_source(manifest, raw) -> DetachedTarget:
    anchor = manifest.anchor.encode()
    if raw.count(anchor) != 1:
        raise ValueError("expected a unique anchor in the fixed target source")
    start = raw.index(anchor)
    return DetachedTarget(manifest.source_path, manifest.target, start, start + len(anchor), manifest.statement,
                          digest(raw), digest(anchor))


def detached_target(prepared, manifest_path: str) -> DetachedTarget:
    from itpeval.backends.projects import project_file

    manifest = _detached_manifest(prepared, manifest_path)
    return _target_in_source(manifest, project_file(prepared.project, manifest.source_path).read_bytes())


def build_detached_task(prepared, manifest_path: str) -> tuple[TaskSpec, bytes]:
    from itpeval.backends.projects import project_file

    manifest = _detached_manifest(prepared, manifest_path)
    files = {name: project_file(prepared.project, name).read_bytes() for name in manifest.files}
    target = _target_in_source(manifest, files[manifest.source_path])
    files[manifest.proof_file] = b""
    artifact = Artifact.from_files(manifest.proof_file, files, ("removed reference certificate",))
    task = TaskSpec(prepared.spec.prover, prepared.environment_id, "proof_completion", artifact,
                    targets=(target.name,), editable_regions=(EditableRegion(manifest.proof_file, 0, 0),),
                    allowed_assumptions=manifest.allowed_assumptions, obligations=(target.name,),
                    manifest_path=manifest_path, budgets=manifest.budgets,
                    candidate_format=f"{manifest.certificate_format}_certificate")
    return task, b""

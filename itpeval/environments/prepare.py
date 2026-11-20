"""Prepare and reload an environment independently of an evaluation or trainer."""
from __future__ import annotations

import json
import os
import re
import subprocess
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path

from itpeval.backends.external import ExternalAdapter, external_adapter
from itpeval.core.records import digest
from itpeval.core.types import EnvironmentSpec, logical_path

from .cache import hash_index, inventory, sha256, snapshot, write_json
from .toolchains import LAUNCHERS, PACKAGE, build_info, resolved_inputs


@dataclass(frozen=True)
class PreparedProject:
    spec: EnvironmentSpec
    project: Path
    prefix: Path
    lock_path: Path
    cache: Path
    build: dict
    library_paths: tuple[tuple[str, Path], ...]
    extra_inputs: tuple[tuple[str, Path], ...]
    adapter: ExternalAdapter | None = None

    @property
    def environment_id(self) -> str:
        return self.spec.environment_id

    @property
    def environment(self) -> dict[str, str]:
        """Translate locked library roles into native configuration at execution."""
        paths = dict(self.library_paths)
        settings = {}
        if self.spec.prover == "lean4":
            # The legacy adapter otherwise searches a mutable project at its prefix.
            settings["ITPEVAL_LEAN4_MATHLIB_PROJECT"] = str(self.project)
            if self.library_paths:
                search = []
                for _, root in self.library_paths:
                    compiled = root / ".lake/build/lib/lean"
                    search.append(str(compiled if compiled.is_dir() else root))
                settings["ITPEVAL_LEAN4_LEAN_PATH"] = os.pathsep.join(search)
            settings["ITPEVAL_LEAN_OPTIONS"] = "\n".join(
                f"-D{name}={value}" for name, value in self.spec.options)
        if self.spec.prover == "agda":
            settings["ITPEVAL_AGDA_INCLUDE_PATH"] = "\n".join(str(p) for _, p in self.library_paths)
        if self.spec.prover == "rocq":
            settings["ITPEVAL_ROCQ_LOAD_PATH"] = "\n".join(
                f"{name}\t{path}" for name, path in self.library_paths)
        if "mizfiles" in paths and self.spec.prover == "mizar":
            settings["ITPEVAL_MIZFILES"] = str(paths["mizfiles"])
        return settings

    def validate(self) -> None:
        """Fail closed when source, dependencies, launchers or installed runtimes drift."""
        with hash_index(self.cache / "indexes" / self.spec.prover) as db:
            if digest(inventory(self.project, db)) != self.spec.project_revision:
                raise ValueError("prepared project content differs from the lock")
            libs = tuple((n, digest(inventory(p, db))) for n, p in self.library_paths)
            if libs != self.spec.libraries:
                raise ValueError("prepared library content differs from the lock")
            adapter = _project_adapter(self.spec.prover)
            if adapter != self.adapter:
                raise ValueError("configured typed adapter changed since preparation")
            roots = _input_roots(self.spec.prover, self.prefix, adapter, self.extra_inputs)
            roots.update(self.extra_inputs)
            now = build_info(self.spec.prover, self.prefix, roots, db, adapter=adapter)
            if now != self.build or _build_id(now) != self.spec.prover_build:
                raise ValueError("native toolchain or adapter differs from the lock")


def _resolve_imports(names, bindings, source, libraries, runtimes):
    """Bind declared logical imports to exact files without guessing a prover's search order."""
    locations = {"project": source, **{"library/" + k: p for k, p in libraries.items()},
                 **{"toolchain/" + k: p for k, p in runtimes.items()}}
    if len(names) != len(set(names)) or bindings.keys() - set(names):
        raise ValueError("import names must be unique and every binding must name a declared import")
    resolved = []
    for name in names:
        owner, rel = bindings.get(name, ("project", name))
        base = locations.get(owner)
        if base is None:
            raise ValueError(f"unknown import source {owner!r} for {name!r}")
        path = base if rel == "." else base / logical_path(rel)
        if not path.is_file():
            raise ValueError(f"cannot resolve import {name!r} at {owner}/{rel}; supply its file binding")
        resolved.append((name, owner, rel, sha256(path)))
    return tuple(resolved)


def _build_id(build):
    return build["version"].splitlines()[0] + "@" + digest(build)


def _project_adapter(prover):
    if prover in LAUNCHERS:
        return None
    adapter = external_adapter(prover)
    if adapter is None:
        raise ValueError(f"unknown prover {prover!r}; configure its typed adapter with ITPEVAL_ADAPTER_DIR")
    return adapter


def _input_roots(prover, prefix, adapter, extra):
    return (adapter.build_inputs() if adapter is not None
            else resolved_inputs(prover, prefix, external=bool(extra)))


def _git_revision(path):
    # A source tree unpacked below a larger checkout can be entirely untracked.
    # Only attribute it to the enclosing Git commit when it contains tracked files.
    tracked = subprocess.run(["git", "-C", str(path), "ls-files", "--", "."],
                             capture_output=True, check=False)
    if tracked.returncode or not tracked.stdout:
        return ""
    head = subprocess.run(["git", "-C", str(path), "rev-parse", "--verify", "HEAD"],
                          capture_output=True, text=True, check=False)
    return head.stdout.strip() if head.returncode == 0 else ""


def prepare_project(prover: str, project: Path, *, prefix: Path, cache: Path,
                    libraries: Mapping[str, Path] | None = None,
                    options: Mapping[str, str] | None = None, imports: Iterable[str] = (),
                    import_bindings: Mapping[str, tuple[str, str]] | None = None,
                    checking_profile: str = "strict",
                    toolchain_inputs: Mapping[str, Path] | None = None,
                    project_name: str | None = None, project_commit: str | None = None,
                    library_commits: Mapping[str, str] | None = None) -> PreparedProject:
    """Freeze local source inputs and resolve the installed native distribution.

    Libraries name versioned source trees. For externally wired installations,
    supply any native library or image outside the standard installation layout
    through toolchain_inputs. Their bytes participate in every subsequent check.
    """
    prefix, cache, project = (Path(p).resolve() for p in (prefix, cache, project))
    adapter = _project_adapter(prover)
    if any(ch in str(cache) for ch in "\r\n\t"):
        raise ValueError("cache paths must be representable to the native library loaders")
    if prover == "rocq" and any(not all(part.isidentifier() for part in name.split("."))
                                for name in (libraries or {})):
        raise ValueError("Rocq library names must be qualified module identifiers")
    options = options or {}
    if options and prover != "lean4":
        raise ValueError(f"{prover} has no supported per-project checker options")
    for name, value in options.items():
        if not re.fullmatch(r"[a-zA-Z][a-zA-Z0-9_.]*", name) or any(c in value for c in "\r\n\0"):
            raise ValueError(f"invalid Lean checker option {name!r}")
    fixtures = PACKAGE / "tests" / "fixtures" / "projects"
    if project.is_relative_to(fixtures):
        # A packaged example has the same identity in a wheel and in a checkout.
        label = f"itpeval/{project.relative_to(fixtures).as_posix()}"
        revision_hint = ""
    else:
        label, revision_hint = project.name, _git_revision(project)
    declared = library_commits or {}
    if declared.keys() - (libraries or {}).keys():
        raise ValueError("library commit without a corresponding library tree")
    names = tuple(imports)
    if adapter is not None and (checking_profile != "strict" or libraries or names or import_bindings or toolchain_inputs):
        raise ValueError("typed adapters take fixed project files and dependencies declared by the adapter")
    extra = tuple(sorted(("external/" + name, Path(path).resolve(strict=True))
                         for name, path in (toolchain_inputs or {}).items()))
    roots = _input_roots(prover, prefix, adapter, extra)
    roots.update(extra)
    with hash_index(cache / "indexes" / prover) as db:
        source, revision = snapshot(project, cache, db)
        deps = [(name, *snapshot(Path(path), cache, db))
                for name, path in sorted((libraries or {}).items())]
        build = build_info(prover, prefix, roots, db, adapter=adapter)
    commits = tuple((name, declared.get(name) or _git_revision(path))
                    for name, path in sorted((libraries or {}).items()))
    bindings = _resolve_imports(names, import_bindings or {}, source,
                                {k: p for k, p, _ in deps}, roots)
    spec = EnvironmentSpec(prover, _build_id(build), revision,
                           tuple((k, rev) for k, _, rev in deps), names,
                           tuple(sorted(options.items())), checking_profile,
                           project_name or label, revision_hint if project_commit is None else project_commit,
                           commits, bindings)
    # Bind physical locations in the local lock independently of portable identities.
    locations = {"cache": str(cache), "prefix": str(prefix), "project": str(source),
                 "libraries": {k: str(p) for k, p, _ in deps},
                 "extra_inputs": {k: str(p) for k, p in extra}}
    lock = {"schema_version": 1, "environment_id": spec.environment_id, "spec": spec.to_dict(),
            "build": build, "locations": locations, "source_git_head": spec.project_commit}
    path = cache / "locks" / spec.environment_id / (digest(lock) + ".json")
    write_json(path, lock)
    return PreparedProject(spec, source, prefix, path, cache, build,
                           tuple((k, p) for k, p, _ in deps), extra, adapter)


def load_project(lock_path: Path) -> PreparedProject:
    """Read a previously produced lock and check its actual local inputs."""
    path = Path(lock_path).resolve(strict=True)
    lock = json.loads(path.read_text(encoding="utf-8"))
    if lock.get("schema_version") != 1 or digest(lock) != path.stem:
        raise ValueError("unknown or damaged environment lock")
    spec = EnvironmentSpec.from_dict(lock["spec"])
    if spec.environment_id != lock["environment_id"]:
        raise ValueError("environment identity does not match specification")
    locations = lock["locations"]
    def pairs(key):
        return tuple((k, Path(v)) for k, v in sorted(locations[key].items()))
    instance = PreparedProject(spec, Path(locations["project"]), Path(locations["prefix"]),
                               path, Path(locations["cache"]), lock["build"], pairs("libraries"),
                               pairs("extra_inputs"), _project_adapter(spec.prover))
    instance.validate()
    return instance

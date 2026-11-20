"""Resolve a project and its source dependencies from a portable JSON manifest."""
from __future__ import annotations

import fcntl
import json
import re
import shutil
import subprocess
import tarfile
import tempfile
from contextlib import ExitStack
from pathlib import Path
from urllib.parse import urlsplit

from itpeval.core.records import digest
from itpeval.core.types import logical_path

from .prepare import PreparedProject, prepare_project


def _git(store, *argv):
    return subprocess.run(["git", "--git-dir", str(store), *argv], stdin=subprocess.DEVNULL,
                          check=True, capture_output=True, text=True).stdout.strip()


def _git_tree(spec, base, cache, tmp):
    url = spec["url"]
    scheme = urlsplit(url).scheme
    if scheme not in ("", "https") or not scheme and "::" in url:
        raise ValueError("source URL must be an HTTPS repository or local directory")
    if not scheme:
        url = str((base / url).resolve())
    ref = spec.get("revision", "HEAD")
    if not isinstance(ref, str) or not ref or ref.startswith("-"):
        raise ValueError("invalid Git revision")
    directory = spec.get("subdir", ".")
    if directory != ".":
        logical_path(directory)
    mirrors = cache / "git"
    mirrors.mkdir(parents=True, exist_ok=True)
    key = digest(url)
    mirror = mirrors / (key + ".git")
    archive = tmp / "source.tar"
    with (mirrors / (key + ".lock")).open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not mirror.exists():
            subprocess.run(["git", "init", "--quiet", "--bare", str(mirror)], check=True)
        # A symbolic ref must be resolved anew. A commit already present in
        # this store is sufficient to recreate a pinned project offline.
        pinned = bool(re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", ref))
        if pinned:
            found = subprocess.run(["git", "--git-dir", str(mirror), "cat-file", "-e", ref + "^{commit}"],
                                   capture_output=True, check=False).returncode == 0
        if not pinned or not found:
            _git(mirror, "fetch", "--quiet", "--depth=1", "--no-tags", url, ref)
            commit = _git(mirror, "rev-parse", "--verify", "FETCH_HEAD^{commit}")
        else:
            commit = ref
        tree = commit if directory == "." else f"{commit}:{directory}"
        if any(line.startswith("160000 ") for line in _git(mirror, "ls-tree", "-r", tree).splitlines()):
            raise ValueError("declare submodule sources as separate pinned dependencies")
        _git(mirror, "archive", "--format=tar", "-o", str(archive), tree)
    dest = tmp / "project"
    dest.mkdir()
    with tarfile.open(archive, "r") as source:
        for member in source:
            path = dest / logical_path(member.name.rstrip("/"))
            if member.isdir():
                path.mkdir(exist_ok=True, parents=True)
            elif member.isfile():
                path.parent.mkdir(exist_ok=True, parents=True)
                with source.extractfile(member) as inp, path.open("xb") as out:
                    shutil.copyfileobj(inp, out)
                path.chmod(0o755 if member.mode & 0o111 else 0o644)
            else:
                raise ValueError(f"prepared Git input must be a regular file or directory: {member.name}")
    return dest, commit


def prepare_manifest(manifest: Path, *, prefix: Path, cache: Path) -> PreparedProject:
    """Resolve local directories or Git refs, snapshot their bytes and write a checked lock."""
    manifest = Path(manifest).resolve(strict=True)
    data = json.loads(manifest.read_text(encoding="utf-8"))
    required = {"schema_version", "prover", "name", "project"}
    allowed = required | {"libraries", "imports", "options", "checking_profile", "import_bindings", "toolchain_inputs"}
    if (not isinstance(data, dict) or required - data.keys() or data.keys() - allowed
            or type(data["schema_version"]) is not int or data["schema_version"] != 1):
        raise ValueError("invalid project manifest schema or fields")
    if any(not isinstance(data[k], str) or not data[k] for k in ("prover", "name")):
        raise ValueError("project name and prover must be nonempty strings")
    for key in ("libraries", "options", "import_bindings", "toolchain_inputs"):
        if not isinstance(data.get(key, {}), dict) or not all(data.get(key, {})):
            raise ValueError(f"{key} must map names to inputs")
    if not isinstance(data.get("imports", []), list) or not all(isinstance(n, str) and n for n in data.get("imports", [])):
        raise ValueError("imports must be a list of logical names")
    if not all(isinstance(v, str) for v in data.get("options", {}).values()):
        raise ValueError("checker option values must be strings")
    if not isinstance(data.get("checking_profile", "strict"), str) or not data.get("checking_profile", "strict"):
        raise ValueError("checking_profile must name a profile")
    cache = Path(cache).resolve()
    cache.mkdir(parents=True, exist_ok=True)
    with ExitStack() as temps:
        def resolve(spec):
            if not isinstance(spec, dict) or not all(isinstance(v, str) and v for v in spec.values()):
                raise ValueError("a project source must name a directory or Git revision")
            if set(spec) == {"path"}:
                return (manifest.parent / spec["path"]).resolve(strict=True), ""
            if "url" not in spec or spec.keys() - {"url", "revision", "subdir"}:
                raise ValueError("invalid source specification")
            tmp = temps.enter_context(tempfile.TemporaryDirectory(dir=cache))
            return _git_tree(spec, manifest.parent, cache, Path(tmp))

        project, revision = resolve(data["project"])
        libraries = {name: resolve(spec) for name, spec in data.get("libraries", {}).items()}
        bindings = {}
        for name, locator in data.get("import_bindings", {}).items():
            if (not isinstance(locator, dict) or set(locator) != {"source", "path"}
                    or not all(isinstance(v, str) and v for v in locator.values())):
                raise ValueError("an import binding requires source and path")
            bindings[name] = (locator["source"], locator["path"])
        native = {}
        for role, locator in data.get("toolchain_inputs", {}).items():
            if not role or not isinstance(locator, dict) or len(locator) != 1:
                raise ValueError("a named native input requires path or prefix_path")
            origin, value = next(iter(locator.items()))
            if origin not in {"path", "prefix_path"} or not isinstance(value, str) or not value:
                raise ValueError(f"invalid native input locator for {role}")
            native[role] = (Path(prefix) / logical_path(value) if origin == "prefix_path"
                            else manifest.parent / value).resolve(strict=True)
        return prepare_project(data["prover"], project, prefix=prefix, cache=cache,
                               project_name=data["name"], project_commit=revision or None,
                               libraries={k: p for k, (p, _) in libraries.items()},
                               library_commits={k: rev for k, (_, rev) in libraries.items() if rev},
                               imports=data.get("imports", ()), import_bindings=bindings,
                               toolchain_inputs=native,
                               options=data.get("options", {}),
                               checking_profile=data.get("checking_profile", "strict"))

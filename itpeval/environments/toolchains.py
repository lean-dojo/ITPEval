"""Identify the native launchers, runtimes and library trees used by an adapter."""
from __future__ import annotations

import os
import platform
import subprocess
from pathlib import Path

from itpeval.core.records import digest

from .cache import inventory

PACKAGE = Path(__file__).resolve().parents[1]
LAUNCHERS = {
    "lean4": "lean", "rocq": "rocq", "agda": "agda", "isabelle": "isabelle",
    "hol4": "Holmake", "hol-light": "hollight-run", "acl2": "acl2",
    "metamath": "metamath", "mizar": "verifier", "pvs": "proveit",
}


def _query(command, prefix: Path) -> str:
    env = {k: os.environ[k] for k in ("PATH", "HOME", "USER", "LANG") if k in os.environ}
    env.update(ITPEVAL_PREFIX=str(prefix), LC_ALL="C")
    try:
        result = subprocess.run(command, capture_output=True, text=True, env=env, check=True,
                                stdin=subprocess.DEVNULL, timeout=45)
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f"unable to identify installed toolchain with {command[0]}") from exc
    return result.stdout.strip()


def resolved_inputs(prover: str, prefix: Path, *, external=False) -> dict[str, Path]:
    """Locate payloads behind the launchers produced by the packaged installers."""
    if prover not in LAUNCHERS:
        raise ValueError(f"unknown prover {prover!r}")
    root = prefix / prover
    binary = root / "bin" / LAUNCHERS[prover]
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise ValueError(f"missing {binary}; install {prover} into {prefix} first")
    roots = {"adapter": PACKAGE / "provers" / prover / "check.sh",
             "adapter_common": PACKAGE / "bin" / "common.sh", "launchers": root / "bin"}

    if prover == "lean4":
        dist = Path(_query([binary, "--print-prefix"], prefix))
        roots.update(compiler=dist / "bin", libraries=dist / "lib" / "lean")
    elif prover == "rocq":
        coqlib = Path(_query([binary, "compile", "-where"], prefix))
        roots.update(compiler=coqlib.parents[1] / "bin", libraries=coqlib)
        for name in ("coq-core", "rocq-runtime", "rocq-core", "coq-stdlib"):
            if (coqlib.parent / name).is_dir():
                roots[name] = coqlib.parent / name
    elif prover == "agda":
        # A release install has a wrapper around the downloaded executable.
        # A standalone upstream binary already participates via launchers.
        if (root / "dist/agda").is_file():
            roots["compiler"] = root / "dist/agda"
        roots["builtins"] = Path(_query([binary, "--print-agda-data-dir"], prefix)) / "lib"
    else:
        packages = {
            "isabelle": ("dist",),
            "hol4": ("src/HOL/bin", "src/HOL/sigobj", "polyml"),
            "hol-light": ("src", "opamroot/hol-light/lib", "opamroot/hol-light/bin"),
            "acl2": ("src/acl2-*/saved_acl2*", "src/acl2-*/books", "lisp", "sbcl"),
            "mizar": ("vendor/bin", "vendor/mizfiles"),
            "pvs": ("lib", "pvs", "proveit", "compat"),
            "metamath": (),
        }
        if (packages[prover] and not external
                and not any(root.glob(packages[prover][0]))):
            raise ValueError(f"cannot resolve {prover} runtime files under {root}; "
                             "supply explicit toolchain_inputs for an external installation")
        for pattern in packages[prover]:
            for path in sorted(root.glob(pattern)):
                roots[str(path.relative_to(root))] = path
    return roots


def build_info(prover: str, prefix: Path, roots: dict[str, Path], db, *, adapter=None) -> dict:
    hashes = {name: digest(inventory(path, db, native=True)) for name, path in sorted(roots.items())}
    version = (_query(["bash", PACKAGE / "provers" / prover / "version.sh"], prefix) if adapter is None
               else f"{adapter.prover} {adapter.version} (Python {platform.python_version()})")
    if not version:
        raise ValueError(f"{prover} returned an empty version")
    # The version labels alone can coincide across locally rebuilt binaries.
    return {"version": version, "runtime_roots": hashes, "platform": platform.system(),
            "architecture": platform.machine(), "libc": list(platform.libc_ver())}

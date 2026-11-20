"""Install a pinned set of native theorem provers on Linux/x86-64."""
from __future__ import annotations

import argparse
import fcntl
import json
import os
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path
from shlex import quote

from itpeval.core.records import digest
from itpeval.runtime.process import run_process, task_environment

from .cache import sha256, write_json
from .toolchains import LAUNCHERS, PACKAGE

LOCK = Path(__file__).with_name("linux-x86_64.json")
PROFILES = {"baseline": LOCK, "stable": LOCK.with_name("linux-x86_64-stable.json")}


def _archive(resource, env):
    # Reuse the shell adapters' checksummed download cache and retry semantics.
    path = subprocess.check_output(
        ["bash", "-c", 'source "$1"; download_cached "$2" "$3" ""', "itpeval",
         str(PACKAGE / "bin/common.sh"), resource["url"], resource["sha256"]],
        env=env, text=True, timeout=2400).strip()
    return Path(path)


def _checkout(source, path):
    commit = source["commit"]
    if path.is_dir() and (path / ".git").is_dir():
        got = subprocess.check_output(["git", "-C", path, "rev-parse", "HEAD"], text=True).strip()
        if got != commit:
            raise ValueError(f"{path} has {got}, expected {commit}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=path.parent) as tmp:
        stage = Path(tmp) / "checkout"
        subprocess.run(["git", "init", "-q", stage], check=True)
        subprocess.run(["git", "-C", stage, "fetch", "-q", "--depth=1", source["url"], commit], check=True)
        subprocess.run(["git", "-C", stage, "checkout", "-q", "--detach", commit], check=True)
        # The checkout only becomes visible after its objects and working tree exist.
        try:
            stage.rename(path)
        except OSError:
            if not (path / ".git").is_dir():
                raise
            got = subprocess.check_output(["git", "-C", path, "rev-parse", "HEAD"], text=True).strip()
            if got != commit:
                raise ValueError(f"concurrent checkout at {path} resolved a different commit")


def _agda(archive, root):
    binary = root / "dist" / "agda"
    binary.parent.mkdir(exist_ok=True, parents=True)
    with tempfile.TemporaryDirectory(dir=binary.parent) as tmp, tarfile.open(archive) as bundle:
        member = bundle.getmember("agda")
        if not member.isfile():
            raise ValueError("the pinned Agda archive must contain the agda executable")
        stage = Path(tmp) / "agda"
        with bundle.extractfile(member) as inp, stage.open("wb") as out:
            shutil.copyfileobj(inp, out)
        stage.chmod(0o755)
        os.replace(stage, binary)
    launcher = root / "bin" / "agda"
    launcher.parent.mkdir(exist_ok=True)
    launcher.write_text('#!/bin/sh\nexport XDG_DATA_HOME=' + quote(str(root / "data")) +
                        '\nexec ' + quote(str(binary)) + ' "$@"\n', encoding="utf-8")
    launcher.chmod(0o755)
    subprocess.run([launcher, "--setup"], check=True)

def _inputs(prover, prefix, cache, env, recipe):
    versions, git, archives = (recipe[key] for key in ("versions", "git", "archives"))
    root = prefix / prover
    root.mkdir(parents=True, exist_ok=True)
    if prover in {"hol-light", "rocq"}:
        repo = cache / "opam" / git["opam-repository"]["commit"]
        _checkout(git["opam-repository"], repo)
        env.update(ITPEVAL_OPAM_REPO_URL=str(repo), OCAML_VERSION=versions["ocaml"],
                   ITPEVAL_OCAML_VERSION=versions["ocaml"], ROCQ_VERSION=versions["rocq"],
                   ITPEVAL_OPAM_PACKAGES=" ".join(recipe["opam"][prover]))
    if prover == "lean4":
        # Install the release archive directly so machines without elan take the
        # same path and interactive toolchain defaults cannot change this build.
        dist = root / ("lean-" + versions["lean4"] + "-linux")
        if not dist.exists():
            archive = _archive(archives[prover], env)
            with tempfile.TemporaryDirectory(dir=root) as tmp:
                subprocess.run(["tar", "--zstd", "-xf", archive, "-C", tmp], check=True)
                stage = Path(tmp) / dist.name
                if not all((stage / "bin" / name).is_file() for name in ("lean", "lake")):
                    raise ValueError("the pinned Lean distribution is missing its compiler or Lake")
                stage.rename(dist)
        env["ITPEVAL_LEAN4_DISTRIBUTION"] = str(dist)
    elif prover == "hol4":
        _checkout(git["polyml"], root / "src/polyml")
        _checkout(git["hol4"], root / "src/HOL")
    elif prover == "hol-light":
        _checkout(git["hol-light"], root / "src")
    elif prover == "acl2":
        sbcl = _archive(archives["acl2-sbcl"], env)
        lisp = root / "lisp"
        subprocess.run(["dpkg-deb", "-x", sbcl, lisp], check=True)
        env.update(ITPEVAL_ACL2_LISP=str(lisp / "usr/bin/sbcl"),
                   SBCL_HOME=str(lisp / "usr/lib/sbcl"),
                   ITPEVAL_ACL2_TARBALL_URL=archives[prover]["url"],
                   ITPEVAL_ACL2_SHA256=archives[prover]["sha256"],
                   ITPEVAL_ACL2_VERSION=versions[prover])
    elif prover == "isabelle":
        env.update(ITPEVAL_ISABELLE_VERSION=versions[prover],
                   ITPEVAL_ISABELLE_SHA256=archives[prover]["sha256"])
    elif prover == "metamath":
        env.update(ITPEVAL_METAMATH_URL=archives[prover]["url"],
                   ITPEVAL_METAMATH_SHA256=archives[prover]["sha256"])
    elif prover == "agda":
        _agda(_archive(archives[prover], env), root)
    elif prover == "mizar":
        env["ITPEVAL_MIZAR_TARBALL"] = str(_archive(archives[prover], env))
    elif prover == "pvs":
        env["ITPEVAL_PVS_TARBALL"] = str(_archive(archives[prover], env))
        libc, version = platform.libc_ver()
        if libc == "glibc" and tuple(map(int, version.split(".")[:2])) < (2, 34):
            package = _archive(archives["pvs-glibc"], env)
            subprocess.run(["dpkg-deb", "-x", package, root / "compat"], check=True)
            env["ITPEVAL_PVS_GLIBC_DIR"] = str(root / "compat/lib/x86_64-linux-gnu")



def _release_inputs(prover, lock):
    """A change to an unrelated prover does not change this installation's owner."""
    git_keys = {
        "hol4": ("hol4", "polyml"), "hol-light": ("hol-light", "opam-repository"),
        "rocq": ("opam-repository",),
    }.get(prover, ())
    archive_keys = {"acl2": ("acl2", "acl2-sbcl"), "pvs": ("pvs", "pvs-glibc")}.get(prover, (prover,))
    version_keys = {"hol-light": ("ocaml",), "rocq": ("rocq", "ocaml", "rocq-stdlib")}.get(prover, (prover,))
    return {"prover": prover, "system": lock["system"], "architecture": lock["architecture"],
            "versions": {k: lock["versions"][k] for k in version_keys if k in lock["versions"]},
            "git": {k: lock["git"][k] for k in git_keys},
            "archives": {k: lock["archives"][k] for k in archive_keys if k in lock["archives"]},
            "opam": lock["opam"].get(prover, [])}

def install_toolchain(prover: str, *, prefix: Path, cache: Path, jobs: int = 4,
                      timeout_s: float = 10800, profile: str = "baseline") -> Path:
    """Install one pinned native distribution. Return its local build receipt.

    Concurrent callers share completed downloads and serialize installation of the
    same prover. Build logs and the pending recipe are retained across an interruption.
    """
    if prover not in LAUNCHERS or jobs < 1 or timeout_s <= 0:
        raise ValueError("expected a supported prover, positive job count and positive build budget")
    recipe_path = PROFILES[profile]
    recipe = json.loads(recipe_path.read_text())
    if (platform.system(), platform.machine()) != (recipe["system"], recipe["architecture"]):
        raise ValueError("this release recipe requires Linux/x86-64")
    prefix, cache = Path(prefix).resolve(), Path(cache).resolve()
    admin = prefix / ".itpeval"
    admin.mkdir(parents=True, exist_ok=True)
    cache.mkdir(parents=True, exist_ok=True)
    receipt = admin / (prover + ".json")
    env = {k: v for k, v in task_environment().items()
           if not k.startswith("ITPEVAL_") and k not in ("LEAN_TOOLCHAIN", "ELAN_TOOLCHAIN",
                 "MIZFILES", "PVS_HOME", "ACL2_HOME", "HOL4_HOME", "OPAMROOT", "OPAMSWITCH")}
    env.update(ITPEVAL_PREFIX=str(prefix), ITPEVAL_PINNED_INSTALL="1", ITPEVAL_DOWNLOAD_CACHE=str(cache / "downloads"),
               ITPEVAL_BUILD_JOBS=str(jobs), OPAMJOBS=str(jobs), ITPEVAL_ACL2_BOOK_JOBS=str(jobs))
    owner = admin / (prover + ".recipe")
    inputs = _release_inputs(prover, recipe)
    identity = digest(inputs)
    installer_id = digest({key: sha256(path) for key, path in {
        "controller": Path(__file__), "shell": PACKAGE / "provers" / prover / "install.sh",
        "common": PACKAGE / "bin/common.sh"}.items()})
    with (admin / (prover + ".lock")).open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if owner.exists() and owner.read_text().strip() != identity:
            raise ValueError(f"a different recipe owns {prefix / prover}; select a new prefix")
        binary = prefix / prover / "bin" / LAUNCHERS[prover]
        if receipt.exists() and binary.is_file():
            previous = json.loads(receipt.read_text())
            actual = subprocess.run(["bash", PACKAGE / "provers" / prover / "version.sh"],
                                    env=env, capture_output=True, text=True, timeout=60, check=False)
            if (previous["recipe_id"] == identity and previous.get("installer_id") == installer_id
                    and previous["launcher_sha256"] == sha256(binary)
                    and actual.returncode == 0 and previous["version"] == actual.stdout.strip()):
                return receipt
        if not owner.exists() and (prefix / prover).is_dir() and any((prefix / prover).iterdir()):
            raise ValueError(f"{prefix / prover} contains an existing installation; prepare it or select a new prefix")
        if not owner.exists():
            # The lock serializes publishers. Atomic replacement also protects a
            # subsequent retry if this process dies while persisting ownership.
            with tempfile.NamedTemporaryFile(dir=admin, mode="w", delete=False) as pending:
                pending.write(identity + "\n")
            os.replace(pending.name, owner)
        # One job owns network resolution, dependency installation and compilation.
        # Its deadline and descendant cleanup therefore also apply during bootstrap.
        result = run_process([sys.executable, "-m", "itpeval.environments.install", "_build",
                              prover, str(prefix), str(cache), profile], env=env,
                             timeout_s=timeout_s, max_log_bytes=4 << 20, merge_stderr=True)
        log = admin / (prover + ".install.log")
        log.write_text(result.stdout + result.stderr)
        if result.outcome != "exited" or result.returncode or not binary.is_file():
            raise RuntimeError(f"{prover} install failed ({result.outcome}, {result.returncode}); see {log}")
        version = subprocess.check_output(["bash", PACKAGE / "provers" / prover / "version.sh"],
                                          env=env, text=True, timeout=60).strip()
        expected = recipe["versions"].get(prover)
        if expected and expected not in version:
            raise RuntimeError(f"expected {prover} {expected}, got {version}")
        write_json(receipt, {"schema_version": 1, "prover": prover, "recipe_id": identity,
                             "inputs": inputs, "installer_id": installer_id,
                             "recipe_file_sha256": sha256(recipe_path), "version": version,
                             "launcher_sha256": sha256(binary), "duration_ms": result.duration_ms})
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("provers", nargs="+", choices=["all", *sorted(LAUNCHERS)])
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--profile", choices=PROFILES, default="baseline",
                        help="select the benchmark baseline or the stable release set")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=10800, help="native build budget in seconds")
    args = parser.parse_args()
    if "all" in args.provers and len(args.provers) != 1:
        parser.error("use all by itself or name individual provers")
    for prover in (sorted(LAUNCHERS) if args.provers == ["all"] else args.provers):
        print(install_toolchain(prover, prefix=args.prefix, cache=args.cache,
                                jobs=args.jobs, timeout_s=args.timeout, profile=args.profile), flush=True)


if __name__ == "__main__":
    if len(sys.argv) == 6 and sys.argv[1] == "_build":
        _, _, prover, prefix, cache, profile = sys.argv
        env = dict(os.environ)
        _inputs(prover, Path(prefix), Path(cache), env, json.loads(PROFILES[profile].read_text()))
        os.execve("/bin/bash", ["bash", str(PACKAGE / "provers" / prover / "install.sh")], env)
    else:
        main()

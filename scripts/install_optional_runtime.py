"""Build the pinned Lean instruments or export Pétanque from its matching Rocq switch."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


PANTOGRAPH_REVISION = "0ee70917fb93a5421157119362ecde806a4d881b"
LEANDOJO_REVISION = "f3b01b180e7429ed5389c2409ed14ce9ede93987"


def export_lean(pantograph: Path, leandojo: Path, prefix: Path):
    """Build with the installed Lean compiler from the two exact Git objects."""
    prefix = prefix.resolve(strict=True)
    lean = prefix / "lean4/bin/lean"
    sysroot = Path(subprocess.check_output([lean, "--print-prefix"], text=True).strip())
    dest = prefix / "auxiliary/lean4"
    dest.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=dest) as temporary:
        stage = Path(temporary)
        source = stage / "Pantograph"
        subprocess.run(["git", "clone", "--quiet", "--no-checkout",
                        pantograph.resolve(strict=True), source], check=True)
        subprocess.run(["git", "-C", source, "checkout", "--quiet", "--detach", PANTOGRAPH_REVISION], check=True)
        # Materialize the Lake lock before compilation. This also works on
        # release hosts whose Git cannot fetch partial clones through Lake.
        lock = json.loads((source / "lake-manifest.json").read_bytes())
        for entry in lock["packages"]:
            local = source / lock["packagesDir"] / entry["name"]
            local.mkdir(parents=True)
            subprocess.run(["git", "init", "--quiet", local], check=True)
            subprocess.run(["git", "-C", local, "remote", "add", "origin", entry["url"]], check=True)
            subprocess.run(["git", "-C", local, "fetch", "--quiet", "--depth=1", "origin", entry["rev"]], check=True)
            subprocess.run(["git", "-C", local, "checkout", "--quiet", "--detach", entry["rev"]], check=True)
        # Select Lake from the release compiler regardless of the user's elan default.
        env = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN"}}
        env.update(PATH=str(sysroot / "bin") + os.pathsep + env["PATH"], LEAN_SYSROOT=str(sysroot))
        subprocess.run([sysroot / "bin/lake", "build", "repl"], cwd=source, env=env, check=True)
        shutil.copy2(source / ".lake/build/bin/repl", stage / "pantograph")
        tracer = "lean_dojo_v2/lean_dojo/data_extraction/ExtractData.lean"
        with (stage / "ExtractData.lean").open("wb") as output:
            subprocess.run(["git", "-C", leandojo, "show", LEANDOJO_REVISION + ":" + tracer],
                           check=True, stdout=output)
        files = ("pantograph", "ExtractData.lean")
        provenance = {"pantograph_revision": PANTOGRAPH_REVISION, "leandojo_revision": LEANDOJO_REVISION,
                      "lean_version": subprocess.check_output([lean, "--version"], text=True).strip(),
                      "sha256": {name: hashlib.sha256((stage / name).read_bytes()).hexdigest() for name in files}}
        (stage / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        for name in (*files, "provenance.json"):
            os.replace(stage / name, dest / name)


def export_petanque(switch: Path, prefix: Path):
    switch = switch.resolve(strict=True)
    packages = switch / ".opam-switch/packages"
    for package in ("rocq-runtime.9.1.1", "coq-lsp.0.2.5+9.1"):
        if not (packages / package).is_dir():
            raise ValueError(f"install {package} in {switch} before exporting it")
    destination = prefix.resolve() / "auxiliary/rocq"
    lib = destination / "lib"
    lib.mkdir(parents=True, exist_ok=True)
    shutil.copy2(switch / "bin/pet", destination / "pet")
    source = switch / "lib"
    shutil.copytree(source / "coq", lib / "coq", dirs_exist_ok=True)
    # OCaml findlib resolves plugin dependencies transitively through META files.
    for item in sorted(source.rglob("*")):
        if item.is_file() and (item.name == "META" or item.suffix in {".cmxs", ".so"}):
            copy = lib / item.relative_to(source)
            copy.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(item, copy)
    (lib / "findlib.conf").write_text('path=""\n', encoding="utf-8")
    print(subprocess.check_output([destination / "pet", "--version"], text=True).strip())


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    subparsers = cli.add_subparsers(dest="prover", required=True)
    rocq = subparsers.add_parser("rocq")
    rocq.add_argument("--opam-switch", type=Path, required=True, help="installed opam switch prefix")
    lean = subparsers.add_parser("lean4")
    lean.add_argument("--pantograph", type=Path, required=True, help="local Pantograph Git checkout")
    lean.add_argument("--leandojo", type=Path, required=True, help="local LeanDojo-v2 Git checkout")
    for command in (rocq, lean):
        command.add_argument("--prefix", type=Path, required=True, help="ITPEval native toolchain prefix")
    args = cli.parse_args()
    if args.prover == "rocq":
        export_petanque(args.opam_switch, args.prefix)
    else:
        export_lean(args.pantograph, args.leandojo, args.prefix)

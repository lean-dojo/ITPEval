"""Build the wheel and sdist. Install each in a fresh venv and exercise packaged assets."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import zipfile
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if __package__ in (None, ""):
    # The report writer uses the checkout. Installed-package probes below run with -I.
    sys.path.insert(0, str(ROOT))

PROBE = """
import importlib, inspect, json, pathlib, subprocess, sys
from importlib import metadata
from itpeval.backends.registry import curated_task, prover_ids
from itpeval.cli.lib import ROOT, discover_provers
from itpeval.core.types import TaskSpec
from itpeval.core.schema import schemas
from itpeval.learning.episodes import check_episode
from itpeval.extraction import ADAPTERS
from eval.datasets import LOCK

assert len(prover_ids()) == 10
assert set(prover_ids()) == set(discover_provers())
assert len(json.loads(LOCK.read_bytes())['files']) >= 10
assert (ROOT / 'bin/common.sh').is_file()
assert (ROOT / 'manifest.json').is_file()
assert (ROOT / 'environments/linux-x86_64.json').is_file(), 'pinned Linux toolchain manifest missing'
assert (ROOT / 'environments/project.schema.json').is_file()
assert (ROOT / 'semantics/CheckDirections.lean').is_file()
assert (ROOT / 'backends/lean4/_goals.py').is_file()
assert (ROOT / 'backends/rocq/_pet.py').is_file()
assert json.loads((ROOT / 'core/schemas.json').read_bytes()) == schemas()
for name in ('hol4.sml', 'hol_light.ml', 'isabelle.ML', 'lean_horn.lean', 'rocq_horn.v', 'pvs.lisp', 'pvs_commands.lisp'):
    assert (ROOT / 'extraction/native' / name).is_file()
for name in ('hol4/tactics.sml', 'hol4/fof.sml', 'hol_light/tactics.ml', 'hol_light/worker.ml'):
    assert (ROOT / 'backends' / name).is_file()
for name in ('lean4/library/Mathlib/LICENSE', 'rocq/library/StrictProp.v', 'rocq/library/LICENSE.stdlib',
             'agda/library/LICENCE', 'mizar/library/real_1.miz', 'mizar/library/COPYING.GPL',
             'mizar/library/COPYING.CC-BY-SA', 'mizar/library/COPYING.interpretation',
             'acl2/library/books/std/lists/append.lisp', 'pvs/interaction/completion.json',
             'lean4/horn-prefix/completion.json', 'rocq/horn-prefix/completion.json',
             'hol-light/automation/completion.json', 'hol4/metis/completion.json',
             'acl2/automation/completion.json', 'agda/auto/Compose.agda', 'agda/auto/right-zero.json',
             'mizar/justifications/completion.json', 'pvs/grind/doubling.pvs',
             'lean4/portfolio/Disjunction.lean', 'agda/horn/DeliveryHorn.agda', 'pvs/horn/propagation.pvs'):
    assert (ROOT / 'tests/fixtures/projects' / name).is_file()
assert set(ADAPTERS) <= set(prover_ids())
for prover in prover_ids():
    backend = importlib.import_module('itpeval.backends.' + prover.replace('-', '_')).backend
    assert backend.prover == prover
    assert 'qualification_report' in inspect.signature(backend.capabilities).parameters
    directory = ROOT / 'provers' / prover
    assert (directory / 'adapter.json').is_file()
    for script in ('check.sh', 'version.sh', 'install.sh'):
        assert (directory / script).is_file()
    assert any(p.is_file() for p in (directory / 'hello').rglob('*'))
    assert any(p.is_file() for p in (ROOT / 'tasks/arith_2_plus_2' / prover).rglob('*'))
    task = curated_task(prover, 'distribution-check')
    assert TaskSpec.from_dict(task.to_dict()) == task
assert set(subprocess.check_output([str(pathlib.Path(sys.executable).with_name('itpeval')), 'list-provers'], text=True).split()) == set(prover_ids())
assert not [dep for dep in (metadata.requires('itpeval') or []) if 'extra ==' not in dep]
"""

INSTALLED_PROOF = """
import json, pathlib, sys
from itpeval.backends.registry import curated_project, get_backend
from itpeval.environments import prepare_project
from itpeval.itp import run_itp
prover, prefix, cache = sys.argv[1:]
prepared = prepare_project(prover, curated_project(prover), prefix=pathlib.Path(prefix), cache=pathlib.Path(cache))
backend = get_backend(prover)
task = backend.build_task(prepared)
checked = run_itp(task=task, candidate=task.allowed_edits[0], prepared=prepared)
assert checked.task_success is True, checked.stderr or checked.stdout
print(json.dumps({"prover_build": prepared.spec.prover_build, "evidence": checked.to_dict()}))
"""

INSTALLED_EXTERNAL = """
import sys
from pathlib import Path
from itpeval.backends.registry import get_backend
from itpeval.corpus.datasets import export_dataset, match_target
from itpeval.environments import load_project, prepare_project
from itpeval.verification import verify
project, work = map(Path, sys.argv[1:])
env = prepare_project('sprig', project, prefix=work, cache=work / 'cache')
env = load_project(env.lock_path)
task = get_backend('sprig').build_task(env)
checked = verify(task, (project / 'proof.json').read_text(), prepared=env)
assert checked.task_success is True, checked.stderr or checked.stdout
bundle, _ = export_dataset(env, 'problem.json', work / 'dataset')
assert match_target(bundle.path, task, prepared=env).checking_status == 'proof_verified'
"""


def check(native_report: Path | None = None, cache: Path | None = None, provers=(),
          dist_dir: Path | None = None, from_dist: Path | None = None):
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)
        installed = {}
        archives = from_dist.resolve(strict=True) if from_dist else tmp
        if from_dist is None:
            # Setuptools can reuse build/lib from a previous revision. Build
            # from the current source files in a new directory on every run.
            source = tmp / "source"
            paths = subprocess.check_output(
                ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--",
                 "README.md", "LICENSE", "MANIFEST.in", "pyproject.toml", "itpeval", "eval", "benchmarks", "docs",
                 "examples/prover-adapters/sprig", "examples/prover-adapters/drat", "scripts",
                 ":!eval/data", ":!eval/subsets"], cwd=ROOT)
            for name in filter(None, os.fsdecode(paths).split("\0")):
                original, destination = ROOT / name, source / name
                if original.is_file():
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(original, destination)
            for target in ("build_sdist", "build_wheel"):
                subprocess.run([sys.executable, "-c",
                                f"from setuptools.build_meta import {target}; "
                                f"import sys; {target}(sys.argv[1])", str(tmp)],
                               cwd=source, check=True)
        wheel, = archives.glob("*.whl")
        sdist, = archives.glob("*.tar.gz")
        sdist_hash = hashlib.sha256(sdist.read_bytes()).hexdigest()
        with tarfile.open(sdist) as archive:
            names = archive.getnames()
            if any("/data/logipedia/data/" in path or "/eval/data/extended/" in path for path in names):
                raise RuntimeError("corpus unexpectedly bundled in source distribution")
            if any("/benchmarks/runtime/evidence/" in path or path.endswith("/qualification.jsonl") for path in names):
                raise RuntimeError("self-referential release attestations in the source distribution")
        derived = tmp / "derived"
        derived.mkdir()
        subprocess.run([sys.executable, "-m", "pip", "wheel", "--no-index", "--no-deps",
                        "--no-build-isolation", "-w", str(derived), str(sdist)], cwd=tmp, check=True)
        derivative, = derived.glob("*.whl")
        def contents(path):
            with zipfile.ZipFile(path) as archive:
                return {item.filename: (item.external_attr >> 16, hashlib.sha256(archive.read(item)).digest())
                        for item in archive.infolist() if not item.is_dir()}
        if contents(derivative) != contents(wheel):
            raise ValueError("wheel built from source distribution differs in payload or executable permissions")
        for i, package in enumerate((wheel, derivative)):
            with zipfile.ZipFile(package) as archive:
                if any("/_toolchains/" in path or path.startswith("eval/data/extended/") for path in archive.namelist()):
                    raise RuntimeError("native toolchain or corpus unexpectedly bundled")
            venv = tmp / f"venv-{i}"
            subprocess.run([sys.executable, "-m", "venv", venv], check=True)
            python = venv / "bin/python"
            subprocess.run([python, "-m", "pip", "install", "--no-index", "--no-deps", package], cwd=tmp, check=True)
            env = os.environ.copy()
            env.pop("PYTHONPATH", None)
            env.pop("ITPEVAL_ADAPTER_DIR", None)
            env["ITPEVAL_RESULTS_DIR"] = str(tmp / "benchmark-results")
            subprocess.run([python, "-I", "-c", PROBE], cwd=tmp, env=env, check=True)
            adapter = tmp / f"external-{i}" / "sprig"
            shutil.copytree(ROOT / "examples/prover-adapters/sprig", adapter, ignore=shutil.ignore_patterns("__pycache__"))
            subprocess.run([python, "-I", "-c", INSTALLED_EXTERNAL, adapter / "hello", tmp / f"adapter-test-{i}"],
                           cwd=tmp, env={**env, "ITPEVAL_ADAPTER_DIR": str(adapter.parent)}, check=True)
            if i == 0:
                env["ITPEVAL_DATA_DIR"] = str(tmp / "corpus/eval/data")
                subprocess.run([python, "-I", "-m", "eval.datasets", "--destination", tmp / "corpus",
                                "--from-checkout", ROOT], cwd=tmp, env=env, check=True)
            else:
                env["ITPEVAL_DATA_DIR"] = str(tmp / "corpus/eval/data")
            subprocess.run([python, "-I", "-m", "eval.pipeline.translation.run", "--dry-run", "--sources",
                            "babel-formal", "--ids", "1", "--src", "lean4", "--tgt", "pvs", "--model", "gpt-5.5"],
                           cwd=tmp, env=env, check=True)
            prefix = os.environ.get("ITPEVAL_PREFIX")
            if prefix and (Path(prefix) / "metamath/bin/metamath").is_file():
                subprocess.run([python, "-I", "-m", "itpeval.learning.example", "--prover", "metamath",
                                "--prefix", Path(prefix).resolve(), "--cache", tmp / "prepared",
                                "--output", tmp / f"native-{i}"], cwd=tmp, env=env, check=True)
            if native_report:
                from itpeval.backends.registry import prover_ids

                if not prefix:
                    raise ValueError("set ITPEVAL_PREFIX to the installed ten-prover prefix")
                wheel_hash = hashlib.sha256(package.read_bytes()).hexdigest()
                def probe(prover):
                    checked = subprocess.run(
                        [python, "-I", "-c", INSTALLED_PROOF, prover, Path(prefix).resolve(), cache or tmp / "prepared"],
                        cwd=tmp, env=env, text=True, stdout=subprocess.PIPE, check=True)
                    result = json.loads(checked.stdout)
                    result["wheel_sha256"] = wheel_hash
                    if i:
                        result["sdist_sha256"] = sdist_hash
                    return prover, result

                selected = list(dict.fromkeys(provers or ())) or ["hol-light", *(p for p in prover_ids() if p != "hol-light")]
                if set(selected) - set(prover_ids()):
                    raise ValueError("unknown prover selected for installed-distribution checks")
                with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
                    for prover, result in pool.map(probe, selected):
                        installed.setdefault(prover, {})["sdist" if i else "wheel"] = result
        if native_report:
            from itpeval.learning.qualification import _record

            rows = []
            for prover, result in installed.items():
                direct, rebuilt = (result[source]["evidence"] for source in ("wheel", "sdist"))
                for key in ("task_id", "environment_id", "artifact_id", "task_success", "obligations", "evidence_references"):
                    if direct[key] != rebuilt[key]:
                        raise ValueError(f"{prover}: distributions disagree on {key}")
                relative = Path("evidence") / prover / "distribution.json"
                path = native_report.parent / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps(result, indent=2) + "\n")
                rows.append({"prover": prover, "environment_id": direct["environment_id"],
                             "prover_build": result["wheel"]["prover_build"], "operation": "installed_package",
                             "status": "implemented/tested", "evidence_path": relative.as_posix()})
            _record(native_report, rows)
        if dist_dir is not None:
            # Keep the exact tested files so a release install can be checked
            # against its receipt without building another pair of archives.
            dist_dir.mkdir(parents=True, exist_ok=True)
            for package in (wheel, sdist):
                destination = dist_dir / package.name
                if destination.resolve() != package.resolve():
                    shutil.copy2(package, destination)



if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-report", type=Path, help="check a proof for all ten tools in both installations")
    parser.add_argument("--cache", type=Path, help="shared disposable environment cache for all-ten checks")
    parser.add_argument("--prover", action="append", help="restrict native distribution checks to this prover")
    parser.add_argument("--dist-dir", type=Path, help="retain the tested wheel and source archive")
    parser.add_argument("--from-dist", type=Path, help="test an existing release wheel and sdist")
    args = parser.parse_args()
    if args.prover and not args.native_report:
        parser.error("--prover requires --native-report")
    check(args.native_report, args.cache.resolve() if args.cache else None, args.prover, args.dist_dir, args.from_dist)

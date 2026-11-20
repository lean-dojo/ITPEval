"""Compare fresh whole-file checks by Metamath, the ITPEval adapter, and mmverify.py."""
import argparse
import platform
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.backends.metamath.syntax import tokens
from itpeval.backends.registry import ROOT
from itpeval.environments.cache import sha256, write_json
from itpeval.itp import run_itp


def measure(source, prefix, mmverify, repeats):
    exe = prefix / "metamath/bin/metamath"
    with TemporaryDirectory() as directory:
        root = Path(directory)
        db = root / "input.mm"
        shutil.copyfile(source, db)
        proofs = 0
        in_proof = False
        for token, _, _ in tokens(db.read_bytes()):
            if token == "$[" or (in_proof and "?" in token):
                raise ValueError("use a self-contained database with complete proofs")
            if token == "$=":
                in_proof = True
            elif token == "$.":
                in_proof = False
            proofs += token == "$p"
        if not proofs:
            raise ValueError("the database contains no proofs")

        def native():
            return subprocess.run([exe, "read input.mm", "verify proof *", "exit"], cwd=root,
                                  stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=600)

        def adapter():
            return run_itp(prover="metamath", prefix=prefix, task_dir=root,
                           task_file=Path("input.mm"), timeout_s=600)

        def independent():
            return subprocess.run([sys.executable, mmverify, "-v", "1", "input.mm"], cwd=root,
                                  stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=600)

        methods = [("metamath", native), ("itpeval", adapter), ("mmverify", independent)]
        samples = []
        for trial in range(repeats):
            # Rotate the first method, since successive processes share the OS page cache.
            offset = trial % len(methods)
            durations = {}
            for name, run in methods[offset:] + methods[:offset]:
                start = perf_counter()
                result = run()
                durations[name] = perf_counter() - start
                marker = "No errors were found." if name == "mmverify" else "All proofs in the database were verified"
                if result.returncode or marker not in result.stdout + result.stderr:
                    raise ValueError(f"{name} failed to verify {source.name}: {(result.stderr + result.stdout)[-800:]}")
            samples.append(durations)
        return {"source": source.name, "bytes": db.stat().st_size, "sha256": sha256(db),
                "proofs": proofs, "wall_seconds": samples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--mmverify", type=Path, required=True, help="upstream mmverify.py")
    parser.add_argument("--database", type=Path, nargs="+", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    prefix, verifier = args.prefix.resolve(), args.mmverify.resolve(strict=True)
    exe = prefix / "metamath/bin/metamath"
    banner = subprocess.check_output([exe, "exit"], stdin=subprocess.DEVNULL, text=True).splitlines()[0]
    adapter_files = ("itp.py", "staging.py", "adapter_paths.py", "runtime/checker.py",
                     "runtime/process.py", "runtime/_linux_job.py", "runtime/logging.py",
                     "provers/metamath/check.sh", "bin/common.sh")
    report = {"protocol": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
              "platform": platform.platform(), "python": sys.version.split()[0],
              "native_version": banner.strip(), "native_launcher_sha256": sha256(exe),
              "itpeval_sources": {name: sha256(ROOT / name) for name in adapter_files},
              "mmverify_sha256": sha256(verifier), "rows": []}
    for source in args.database:
        report["rows"].append(measure(source, prefix, verifier, args.repeats))
        print(f"{source.name} finished", flush=True)
    write_json(args.output, report)


if __name__ == "__main__":
    main()

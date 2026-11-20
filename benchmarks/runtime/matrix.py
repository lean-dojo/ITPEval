"""Reproduce the all-ten Linux reference measurements with isolated suite caches."""
import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from tempfile import NamedTemporaryFile

from itpeval.backends.registry import prover_ids

HERE = Path(__file__).resolve().parent


def run_suite(prover, workload, prefix, cache, output):
    result_path = output / "suites" / f"{prover}.{workload}.jsonl"
    result_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(HERE / "run.py"), "--prefix", str(prefix), "--cache", str(cache/prover/workload),
           "--provers", prover, "--count", "2", "--workers", "2", "--workload", workload,
           "--cpu-seconds", "300", "--memory-gib", "128", "--output", str(result_path)]
    subprocess.run(cmd, check=True)
    row = json.loads(result_path.read_bytes())
    if (not all(s["correct"] and s["agreement"] for s in row["runs"])
            or [s["success"] for s in row["samples"]] != [True, True, False]):
        raise ValueError(f"{prover} {workload} failed; see {result_path}")
    return row


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    for key in ("prefix", "cache", "output"):
        cli.add_argument("--" + key, type=Path, required=True)
    cli.add_argument("--suite-workers", type=int, default=4)
    args = cli.parse_args()
    if args.suite_workers <= 0:
        cli.error("suite-workers must be positive")
    workloads = {"completion": "linux-x86_64.jsonl", "library": "library-linux-x86_64.jsonl"}
    ordered = ["hol-light", *(p for p in prover_ids() if p != "hol-light")]
    completed = {key: [] for key in workloads}
    with ThreadPoolExecutor(max_workers=args.suite_workers) as pool:
        jobs = [pool.submit(run_suite, p, w, args.prefix, args.cache, args.output) for p in ordered for w in workloads]
        for job in as_completed(jobs):
            row = job.result()
            completed[row["workload"]].append(row)
            print(row["prover"], row["workload"], flush=True)
    for workload, filename in workloads.items():
        with NamedTemporaryFile(dir=args.output, mode="w", delete=False) as tmp:
            for row in sorted(completed[workload], key=lambda r: r["prover"]):
                print(json.dumps(row, sort_keys=True), file=tmp)
        os.replace(tmp.name, args.output/filename)


if __name__ == "__main__":
    main()

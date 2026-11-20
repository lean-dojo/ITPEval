"""Compare worker counts on distinct native proof-completion jobs."""
import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import platform
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, prover_ids
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime.scheduler import Job, run_jobs
from itpeval.verification.cache import verifier_revision


def prepare_jobs(prover, prefix, root, count):
    project = curated_project(prover)
    manifest = json.loads((project / "completion.json").read_bytes())
    target = manifest["target"]
    good, bad = manifest["allowed_edits"][:2]
    jobs = []

    for index in range(count):
        # Give each job its own named theorem and source bytes while keeping
        # the template, proof obligations and proof policy comparable.
        name = f"{target}{index:04d}"
        source = root / f"task-{index}"
        for relative in manifest["files"]:
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            data = (project / relative).read_bytes().replace(target.encode(), name.encode())
            path.write_bytes(data)
        edited = dict(manifest)
        for key in ("target", "anchor", "observer_anchor"):
            value = edited.get(key)
            if isinstance(value, str):
                edited[key] = value.replace(target, name)
        (source / "completion.json").write_text(json.dumps(edited), encoding="utf-8")
        prepared = prepare_project(prover, source, prefix=prefix, cache=root / "locks")
        task = build_task(prepared)
        # Keep good and bad edits interleaved. Third choices can differ in
        # their native proof status across tasks, so use the reviewed pair.
        jobs.append(Job(task, good if index % 2 == 0 else bad, prepared))
    return jobs


def percentile(values, fraction):
    ordered = sorted(values)
    return ordered[math.ceil(len(ordered) * fraction) - 1]


def sample(jobs, workers):
    started = perf_counter()
    rows = []
    prover = jobs[0].task.prover
    for index, evidence in run_jobs(jobs, workers=workers, prover_limits={prover: workers}):
        elapsed = perf_counter() - started
        expected = index % 2 == 0
        expected_outcomes = {"accepted"} if expected else {"rejected", "incomplete"}
        correct = (
            evidence.execution_outcome == "exited"
            and evidence.task_success is expected
            and evidence.checker_outcome in expected_outcomes
            and evidence.duration_ms > 0
        )
        rows.append({
            "job": index,
            "time_to_verdict_s": elapsed,
            "native_checker_ms": evidence.duration_ms,
            "native_peak_process_rss_bytes": evidence.peak_process_rss_bytes,
            "native_cpu_s": evidence.cpu_time_s,
            "execution_outcome": evidence.execution_outcome,
            "checker_outcome": evidence.checker_outcome,
            "task_success": evidence.task_success,
            "matches_expected": correct,
            "diagnostic": None if correct else (evidence.stderr + evidence.stdout)[-1800:],
        })
    wall = perf_counter() - started
    if len(rows) != len(jobs):
        raise RuntimeError(f"{prover} returned {len(rows)} of {len(jobs)} jobs")
    latencies = [row["time_to_verdict_s"] for row in rows]
    rss = [row["native_peak_process_rss_bytes"] for row in rows
           if row["native_peak_process_rss_bytes"] is not None]
    cpu = [row["native_cpu_s"] for row in rows if row["native_cpu_s"] is not None]
    return {
        "workers": workers,
        "wall_s": wall,
        "attempts_per_second": len(rows) / wall,
        "p50_time_to_verdict_s": percentile(latencies, .50),
        "p95_time_to_verdict_s": percentile(latencies, .95),
        "peak_native_process_rss_bytes": max(rss, default=None),
        "sum_native_cpu_s": sum(cpu) if cpu else None,
        "correct": sum(row["matches_expected"] for row in rows),
        "rows": sorted(rows, key=lambda row: row["job"]),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache-parent", type=Path)
    parser.add_argument("--provers", nargs="+", choices=prover_ids(), default=prover_ids())
    parser.add_argument("--workers", nargs="+", type=int, default=(1, 4))
    parser.add_argument("--count", type=int, help="jobs per prover (default 16, Isabelle 4, HOL Light 2)")
    parser.add_argument("--trials", type=int, default=1, help="alternate worker order across trials")
    args = parser.parse_args()
    if args.trials < 1 or any(value < 1 for value in args.workers):
        parser.error("trial and worker counts must be positive")
    if args.count is not None and args.count < 2:
        parser.error("the batch needs at least two jobs")

    report = {
        "protocol": 1,
        "workload": "distinct locked proof targets from the bundled completion templates",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "logical_cpus": len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count(),
        "trials": args.trials,
        "provers": [],
    }
    # Start the longest prover first and keep each worker comparison isolated.
    for prover in sorted(set(args.provers), key=lambda name: (name != "hol-light", name)):
        count = args.count or {"hol-light": 2, "isabelle": 4}.get(prover, 16)
        with TemporaryDirectory(dir=args.cache_parent, prefix=f"itpeval-scale-{prover}-") as path:
            started = perf_counter()
            jobs = prepare_jobs(prover, args.prefix, Path(path), count)
            preparation_s = perf_counter() - started
            suite = {
                "prover": prover,
                "preparation_s": preparation_s,
                "prover_build": jobs[0].prepared.spec.prover_build,
                "verifier_revision": verifier_revision(prover),
                "jobs": [{"task_id": job.task.task_id, "environment_id": job.task.environment_id,
                          "target": job.task.targets[0], "candidate": job.candidate,
                          "expected": index % 2 == 0}
                         for index, job in enumerate(jobs)],
                "samples": [],
            }
            report["provers"].append(suite)
            order = tuple(dict.fromkeys(args.workers))
            for trial in range(1, args.trials + 1):
                for workers in order:
                    measured = sample(jobs, workers)
                    suite["samples"].append({**measured, "trial": trial})
                    write_json(args.output, report)
                    print(f"{prover}: {measured['correct']}/{count} expected outcomes at {workers} workers "
                          f"in {measured['wall_s']:.3f} s (trial {trial})", flush=True)
                order = order[::-1]
    if any(s["correct"] != len(prover["jobs"]) for prover in report["provers"] for s in prover["samples"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()

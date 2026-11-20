"""Measure fresh-checker work and pooled throughput on reviewed completion tasks."""
import argparse
import os
from dataclasses import replace
import json
from pathlib import Path
from time import monotonic

from itpeval.backends.registry import curated_project, curated_task, prover_ids
from itpeval.environments import prepare_project
from itpeval.runtime.scheduler import Job, run_jobs
from itpeval.verification.service import verify


def tree_bytes(path):
    return sum(f.stat().st_size for f in path.rglob("*") if f.is_file() and not f.is_symlink())


def sample(prover, prefix, cache, workers, count, workload="completion", cpu_seconds=None, memory_bytes=None):
    cache.mkdir(parents=True, exist_ok=True)
    size_before = tree_bytes(cache)
    start = monotonic()
    if workload == "library":
        from library import prepare
        prepared, task, invalid = prepare(prover, prefix, cache)
        good = bad = None
    else:
        prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
        task = invalid = curated_task(prover, prepared.environment_id)
        good, bad = task.allowed_edits[:2]
    budgets = replace(task.budgets, cpu_seconds=cpu_seconds, memory_bytes=memory_bytes)
    task, invalid = replace(task, budgets=budgets), replace(invalid, budgets=budgets)
    preparation = monotonic() - start
    results = []
    for label, candidate in (("first_check", good), ("warm_check", good), ("rejected_attempt", bad)):
        start = monotonic()
        ev = verify(invalid if label == "rejected_attempt" else task, candidate, prepared=prepared)
        results.append({"workload": label, "wall_s": monotonic()-start,
                        "checker_ms": ev.duration_ms, "peak_process_rss_bytes": ev.peak_process_rss_bytes,
                        "cpu_time_s": ev.cpu_time_s, "outcome": ev.execution_outcome,
                        "success": ev.task_success, "failure": (ev.stderr + ev.stdout)[-1500:]
                        if ev.task_success is not (label != "rejected_attempt") else None})
    jobs = [Job(task if idx % 2 == 0 else invalid, good if idx % 2 == 0 else bad, prepared) for idx in range(count)]
    runs = []
    reference = None
    for concurrency in dict.fromkeys((1, workers)):
        start = monotonic()
        evidence = sorted(run_jobs(jobs, workers=concurrency, prover_limits={prover: concurrency}))
        elapsed = monotonic()-start
        outcomes = [(ev.execution_outcome, ev.checker_outcome, ev.task_success, ev.completion_status)
                    for _, ev in evidence]
        timeouts = sum(ev.execution_outcome == "timeout" for _, ev in evidence)
        crashes = sum(ev.execution_outcome == "crash" for _, ev in evidence)
        runs.append({"workers": concurrency, "wall_s": elapsed, "attempts_per_second": count/elapsed,
                     "infrastructure_failures": sum(ev.task_success is None for _, ev in evidence),
                     "timeouts": timeouts, "crashes": crashes,
                     "timeout_rate": timeouts / count, "crash_rate": crashes / count,
                     "agreement": (reference is None or reference == outcomes) and all(
                         ev.task_success is not None for _, ev in evidence),
                     "correct": all(ev.task_success is (idx % 2 == 0) for idx, ev in evidence)})
        reference = outcomes
    return {"workload": workload,
            "available_logical_cpus": len(os.sched_getaffinity(0)),
            "physical_memory_bytes": os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE"), "task_budgets": task.budgets.to_dict(),
            "invalid_task_id": invalid.task_id, "prover": prover, "environment_id": prepared.environment_id, "task_id": task.task_id,
            "prover_build": prepared.spec.prover_build, "preparation_s": preparation,
            "cache_growth_bytes": tree_bytes(cache)-size_before, "samples": results, "runs": runs,
            "count": count}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--provers", nargs="+", choices=prover_ids(), default=list(prover_ids()))
    parser.add_argument("--workload", choices=("completion", "library"), default="completion")
    parser.add_argument("--cpu-seconds", type=int, help="CPU seconds per native process")
    parser.add_argument("--memory-gib", type=int, help="virtual address space per native process")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--count", type=int, default=4)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.count < 2 or args.workers < 1:
        parser.error("count must be at least 2 and workers must be positive")
    passed = True
    with args.output.open("w", encoding="utf-8") as out:
        for prover in args.provers:
            row = sample(prover, args.prefix, args.cache, args.workers, args.count, args.workload,
                         args.cpu_seconds, args.memory_gib * 1024**3 if args.memory_gib else None)
            print(json.dumps(row, sort_keys=True), file=out, flush=True)
            if ([s["success"] for s in row["samples"]] != [True, True, False]
                    or not all(r["agreement"] and r["correct"] for r in row["runs"])):
                passed = False
    raise SystemExit(0 if passed else 1)

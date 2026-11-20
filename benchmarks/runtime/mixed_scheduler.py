"""Measure bounded scheduling on fresh mixed ACL2, Rocq and Metamath attempts."""

import argparse
from collections import Counter
from dataclasses import replace
from datetime import datetime, timezone
from hashlib import sha256
import os
from pathlib import Path
import platform
from statistics import median
import subprocess
import sys
from tempfile import TemporaryDirectory
from threading import Event, Lock, get_ident
from time import perf_counter
from types import ModuleType
from unittest.mock import patch

from benchmarks.runtime.scale import percentile, prepare_jobs
from itpeval.core.types import VerificationEvidence
from itpeval.environments.cache import write_json
from itpeval.runtime import pool, scheduler
from itpeval.verification.cache import verifier_revision

PROVERS = ("acl2", "rocq", "metamath")
WORKERS = 4
LIMITS = {"acl2": 4, "rocq": 1, "metamath": 1}
QUEUE_LIMIT = 16


def _baseline(revision):
    modules, hashes = {}, {}
    for name in ("pool", "scheduler"):
        path = f"itpeval/runtime/{name}.py"
        source = subprocess.check_output(["git", "show", f"{revision}:{path}"])
        module = ModuleType(f"itpeval.runtime._before_{name}")
        sys.modules[module.__name__] = module
        exec(compile(source, path, "exec"), module.__dict__)
        modules[name] = module
        hashes[name] = sha256(source).hexdigest()
    modules["scheduler"].LocalPool = modules["pool"].LocalPool
    return modules["scheduler"], hashes


def _workload(prefix, root, cycles):
    templates = {}
    for prover in PROVERS:
        projects = prepare_jobs(prover, prefix, root / prover, 8)
        ordered = sorted(projects, key=lambda job: job.task.environment_id)
        # Stress the former ordering by using low sorting IDs for the slower
        # prover and high sorting IDs for the two faster provers.
        templates[prover] = ordered[:2] if prover == "acl2" else ordered[-2:]
    counts = Counter()
    jobs = []
    for prover in ("acl2", "acl2", "rocq", "metamath") * cycles:
        occurrence = counts[prover]
        template = templates[prover][occurrence // 2 % 2]
        budgets = replace(template.task.budgets, timeout_s=template.task.budgets.timeout_s + occurrence)
        task = replace(template.task, budgets=budgets)
        jobs.append(scheduler.Job(task, task.allowed_edits[occurrence % 2], template.prepared))
        counts[prover] += 1
    return jobs


def _sample(module, jobs):
    rows, started_order = [], []
    index = {job.task.task_id: i for i, job in enumerate(jobs)}
    assert len(index) == len(jobs)
    pulled = max_pending = max_active = 0
    active, peak = Counter(), Counter()
    started = perf_counter()
    lock = Lock()
    caller = get_ident()
    check = module.verify

    def checker(task, candidate, **kwargs):
        nonlocal max_active
        with lock:
            started_order.append(index[task.task_id])
            active[task.prover] += 1
            peak[task.prover] = max(peak[task.prover], active[task.prover])
            max_active = max(max_active, sum(active.values()))
        try:
            return check(task, candidate, **kwargs)
        finally:
            with lock:
                active[task.prover] -= 1

    def source():
        nonlocal pulled, max_pending
        for job in jobs:
            pulled += 1
            max_pending = max(max_pending, pulled - len(rows))
            yield job

    def writer(i, evidence):
        assert get_ident() == caller
        job = jobs[i]
        accepted = job.candidate == job.task.allowed_edits[0]
        correct = (evidence.task_id == job.task.task_id and evidence.environment_id == job.task.environment_id
                   and evidence.execution_outcome == "exited" and evidence.task_success is accepted
                   and evidence.checker_outcome in ({"accepted"} if accepted else {"rejected", "incomplete"}))
        if not correct:
            raise ValueError(f"unexpected evidence for job {i}: {evidence.checker_outcome}: {evidence.stderr[-800:]}")
        rows.append({"index": i, "verdict_s": perf_counter() - started, "success": evidence.task_success,
                     "checker_outcome": evidence.checker_outcome, "native_ms": evidence.duration_ms})

    with patch.object(module, "verify", checker):
        for i, _ in module.run_jobs(source(), workers=WORKERS, prover_limits=LIMITS,
                                    queue_limit=QUEUE_LIMIT, writer=writer):
            assert rows[-1]["index"] == i
    wall = perf_counter() - started
    assert {row["index"] for row in rows} == set(range(len(jobs))) and len(rows) == len(jobs)
    assert max_pending <= QUEUE_LIMIT and max_active <= WORKERS
    assert all(peak[prover] <= LIMITS[prover] for prover in PROVERS)
    latencies = {prover: [row["verdict_s"] for row in rows if jobs[row["index"]].task.prover == prover]
                 for prover in PROVERS}
    return {"wall_s": wall, "first_verdict_s": {p: min(values) for p, values in latencies.items()},
            "p95_verdict_s": {p: percentile(values, .95) for p, values in latencies.items()},
            "max_admitted_unwritten": max_pending, "max_checker_calls": max_active,
            "max_checker_calls_by_prover": dict(peak), "checker_start_order": started_order, "rows": rows}


def _simulate_failure_and_cancel(task):
    cancel = Event()
    pulled, called = [], []

    def source():
        for i in range(20):
            pulled.append(i)
            yield scheduler.Job(task, str(i), None)

    def checker(task, candidate, **kwargs):
        index = int(candidate)
        called.append(index)
        if index == 0:
            raise RuntimeError("simulated worker failure")
        if index == 2:
            cancel.set()
            return pool.cancelled_evidence(task)
        return VerificationEvidence(task.task_id, task.environment_id, task.artifact.artifact_id,
                                    "exited", "accepted", True, "preserved", "proved")

    with patch.object(scheduler, "verify", checker):
        results = [(i, ev.execution_outcome, ev.checker_outcome) for i, ev in
                   scheduler.run_jobs(source(), workers=1, queue_limit=4, cancel=cancel)]
    assert pulled == list(range(6)) and called == [0, 1, 2]
    assert results[:2] == [(0, "backend_error", "not_run"), (1, "exited", "accepted")]
    assert results[2:] == [(i, "cancelled", "not_run") for i in range(2, 6)]
    return {"offered_jobs": 20, "admitted": pulled, "checker_called": called, "outcomes": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--baseline-revision", required=True, help="Git revision supplying the original scheduler and pool")
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--cycles", type=int, default=8, help="four jobs per cycle, with two ACL2 jobs")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.trials < 1 or args.cycles < 4:
        parser.error("use at least one trial and four workload cycles")

    before, before_hashes = _baseline(args.baseline_revision)
    started = datetime.now(timezone.utc).isoformat()
    with TemporaryDirectory(prefix="itpeval-mixed-scheduler-") as temporary:
        begin = perf_counter()
        jobs = _workload(args.prefix, Path(temporary), args.cycles)
        preparation = perf_counter() - begin
        samples = {"before": [], "after": []}
        for trial in range(args.trials):
            versions = [("before", before), ("after", scheduler)]
            for name, module in versions if trial % 2 == 0 else reversed(versions):
                result = _sample(module, jobs)
                samples[name].append(result)
                print(f"trial {trial + 1} {name} {result['wall_s']:.3f} s", flush=True)
        outcomes = [{row["index"]: (row["success"], row["checker_outcome"]) for row in sample["rows"]}
                    for version in samples.values() for sample in version]
        assert all(outcome == outcomes[0] for outcome in outcomes)
        summary = {name: {"median_wall_s": median(item["wall_s"] for item in items),
                          "median_first_verdict_s": {p: median(i["first_verdict_s"][p] for i in items) for p in PROVERS},
                          "median_p95_verdict_s": {p: median(i["p95_verdict_s"][p] for i in items) for p in PROVERS}}
                   for name, items in samples.items()}
        affinity = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
        report = {
            "schema_version": 1, "started_utc": started, "python": platform.python_version(),
            "platform": platform.platform(), "cpu_affinity": affinity, "preparation_wall_s": preparation,
            "method": "Alternate baseline and current schedulers on the same fresh checks with identical native locks. "
                      "The six locked projects include environment IDs selected to stress the former lexicographic "
                      "priority. Use the OS filesystem cache on one shared host and bypass the verdict cache.",
            "baseline_revision": args.baseline_revision, "source_sha256": {"before": before_hashes, "after": {
                m.__name__.rsplit(".", 1)[-1]: sha256(Path(m.__file__).read_bytes()).hexdigest()
                for m in (pool, scheduler)}},
            "workers": WORKERS, "prover_limits": LIMITS, "queue_limit": QUEUE_LIMIT,
            "verifier_revisions": {p: verifier_revision(p) for p in PROVERS},
            "jobs": [{"prover": j.task.prover, "environment_id": j.task.environment_id, "task_id": j.task.task_id,
                      "build": j.prepared.spec.prover_build, "expected": j.candidate == j.task.allowed_edits[0]} for j in jobs],
            "summary": summary, "trials": samples, "failure_and_cancellation": _simulate_failure_and_cancel(jobs[0].task),
        }
    write_json(args.output, report)


if __name__ == "__main__":
    main()

"""Time project preparation, lock loading and verification-result reuse on the same proof."""
import argparse
import os
import platform
import sys
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.backends.registry import curated_project, curated_task, prover_ids
from itpeval.environments import load_project, prepare_project
from itpeval.environments.cache import write_json
from itpeval.verification.cache import verifier_revision, verify_cached


def timed(operation, *args, **kwargs):
    start = perf_counter()
    result = operation(*args, **kwargs)
    return result, perf_counter() - start


def measure(prover, prefix, cache, repeats):
    project = curated_project(prover)
    prepared, first = timed(prepare_project, prover, project, prefix=prefix, cache=cache)
    task = curated_task(prover, prepared.environment_id)
    candidate = task.allowed_edits[0]
    samples = []
    for attempt in range(repeats):
        again, prepare_s = timed(prepare_project, prover, project, prefix=prefix, cache=cache)
        locked, load_s = timed(load_project, again.lock_path)
        if locked.environment_id != prepared.environment_id:
            raise ValueError(f"{prover}: the environment changed during measurement")
        # A separate result database makes the first call of every pair a native check.
        options = {"prepared": locked, "cache": cache / f"results-{attempt}"}
        miss, miss_s = timed(verify_cached, task, candidate, **options)
        hit, hit_s = timed(verify_cached, task, candidate, **options)
        if (miss.cache_hit or not hit.cache_hit or miss.key != hit.key
                or hit.evidence != miss.evidence or miss.evidence.task_success is not True
                or miss.evidence.checker_outcome != "accepted"):
            raise ValueError(f"{prover}: expected accepted native evidence followed by identical cached evidence")
        samples.append({"repeat_prepare_s": prepare_s, "load_lock_s": load_s,
                        "miss_s": miss_s, "hit_s": hit_s, "native_checker_ms": miss.evidence.duration_ms,
                        "cache_hits": [miss.cache_hit, hit.cache_hit],
                        "checker_outcome": hit.evidence.checker_outcome, "task_success": hit.evidence.task_success})
    return {"prover": prover, "prover_build": prepared.spec.prover_build, "task_id": task.task_id,
            "environment_id": prepared.environment_id, "verifier_revision": verifier_revision(prover),
            "result_key": miss.key, "first_prepare_s": first, "samples": samples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True, help="installed native toolchains")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache-parent", type=Path, help="directory for the temporary benchmark caches")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--provers", nargs="+", choices=prover_ids(), default=prover_ids())
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    report = {"protocol": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
              "platform": platform.platform(), "python": sys.version.split()[0],
              "available_cpus": len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count(),
              "repeats": args.repeats, "rows": []}
    for prover in dict.fromkeys(args.provers):
        with TemporaryDirectory(dir=args.cache_parent, prefix="itpeval-cache-") as tmp:
            report["rows"].append(measure(prover, args.prefix, Path(tmp), args.repeats))
        print(f"{prover} finished", flush=True)
    write_json(args.output, report)


if __name__ == "__main__":
    main()

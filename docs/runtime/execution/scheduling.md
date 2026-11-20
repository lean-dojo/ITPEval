# Schedule proof checks

## Check several candidates in parallel

`run_jobs` takes an iterable of `Job(task, candidate, prepared)` and yields `(input_index, evidence)` as checks finish. Set overall `workers` and per-prover `prover_limits`. The scheduler rotates through eligible provers and environments and dispatches in input order within each environment. Its default queue holds four jobs per worker.

`writer(index, evidence)` runs on the consuming thread in result order. Cancellation stops admission, asks running checks to end, and reports cancellation for queued jobs. After a crash, the next job launches a fresh checker.

For a fixed theorem, reuse the lock from `itpeval prepare`. Give the script one `candidate` per JSONL row.

```python
import json
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import load_project
from itpeval.runtime.scheduler import Job, run_jobs

# Reuse the project lock for every candidate in this file.
project = load_project(Path("path/to/project.lock.json"))
task = build_task(project)
jobs = (Job(task, row["candidate"], project) for row in read_jsonl(Path("candidates.jsonl")))

# Write each result as it completes without collecting the batch in memory.
with Path("verdicts.jsonl").open("w", encoding="utf-8") as output:
    for index, evidence in run_jobs(jobs, workers=4, prover_limits={task.prover: 2}):
        print(json.dumps({"input_index": index, "evidence": evidence.to_dict()}), file=output)
```

Use a matching task and lock for each job. When several projects have separate input streams, `interleave_jobs(*sources)` draws from them in turn. Set a smaller per-prover cap for heavier native processes. [Mixed-prover timings](../measurements/throughput.md#mixed-prover-queue-latency)

## Time and memory limits

On Linux, a job guardian kills and waits for all remaining descendants on exit, timeout, or cancellation. The wall deadline covers the whole tree. Optional CPU and address-space limits apply per process through `prlimit`. A deployment resource controller can cap memory for the whole tree.

Evidence reports wall time in `duration_ms`, descendant CPU in `cpu_time_s` and per-process peak memory in `peak_process_rss_bytes`. `Budgets.max_log_bytes` limits each diagnostic stream to its tail, and `logs_truncated` reports dropped output.

The legacy `run_itp` accepts `budgets`, `install_budgets` and an optional cancellation event. Its explicit timeout overrides the corresponding budget deadline. The staged CLI takes `--check-cpu-seconds`, `--check-memory-bytes`, `--install-cpu-seconds`, `--install-memory-bytes` and `--max-log-bytes`.

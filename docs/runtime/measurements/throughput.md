# Throughput and queue latency

## Throughput on distinct proof tasks

The scheduler checks distinct locked targets with one worker and with a cap of four. Targets are variants of the bundled tasks. Half the candidates are reviewed proofs, and half are incorrect or incomplete edits. Each job starts a native check.

The first sweep ran **134 jobs at each worker cap** across ten provers. All 268 checker outcomes matched the expected valid and invalid edits. The four-worker cap allowed both HOL Light jobs to run together, reducing that batch from 212.94 s to 106.52 s. [HOL Light receipt](../../../benchmarks/runtime/scalability-hol-light.json) · [Other nine prover receipts](../../../benchmarks/runtime/scalability-nine.json)

<!-- scale-controls -->

<!-- table:scale -->
| Prover | Jobs per run | 1 worker (jobs/s) | 4-worker cap (jobs/s) | Batch speedup | p95 at 4 (s) | Peak process RSS at 4 (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| acl2 | 16 | 1.072 | 0.370 | 0.35× | 43.234 | 70.9 |
| agda | 16 | 7.257 | 26.258 | 3.62× | 0.609 | 64.5 |
| hol-light | 2 | 0.009 | 0.019 | 2.00× | 106.524 | 352.4 |
| hol4 | 16 | 1.607 | 1.498 | 0.93× | 10.679 | 111.1 |
| isabelle | 4 | 0.115 | 0.235 | 2.04× | 17.016 | 1205.7 |
| lean4 | 16 | 1.534 | 1.106 | 0.72× | 14.467 | 465.9 |
| metamath | 16 | 8.764 | 29.345 | 3.35× | 0.545 | 12.9 |
| mizar | 16 | 3.215 | 1.442 | 0.45× | 11.094 | 12.9 |
| pvs | 16 | 1.245 | 4.630 | 3.72× | 3.455 | 385.5 |
| rocq | 16 | 2.980 | 2.531 | 0.85× | 6.321 | 63.7 |
<!-- end:scale -->

ACL2’s 16 checks took 14.93 s with one worker and 43.23 s at a cap of four. Native calls took about 0.1 s each, prompting a closer look at lock validation.

### Faster lock validation

The new hash index reuses hashes for unchanged files, groups index writes, and rereads recently changed files. The comparison changes only the index implementation. It uses eight distinct targets, two trials per cap and an empty result cache. All verdicts matched. [Trials, commands and build identities](../../../benchmarks/runtime/lock-validation-optimization.json)

| Prover | One worker, before → after (s) | Four-worker cap, before → after (s) |
| --- | ---: | ---: |
| ACL2 | 7.98 → 3.18 | 16.50 → 4.33 |
| Rocq | 2.62 → 1.95 | 2.29 → 0.95 |
| Metamath | 0.80 → 0.78 | 0.27 → 0.26 |

The optimized version also completed three four-worker Metamath batches of 128 tasks. All 384 verdicts matched, and the receipt records CPU affinity for the stress runs.

### Longer queues

The completed 128-target batches for Agda, Metamath and Rocq matched all 768 expected verdicts. The figures use a completed Metamath rerun after an earlier four-worker batch stalled for an unknown reason. [Completed batches and aborted trial](../../../benchmarks/runtime/scalability-extended.json)

<!-- table:scale_extended -->
| Prover | Jobs per run | 1 worker (jobs/s) | 4-worker cap (jobs/s) | Batch speedup | p95 at 4 (s) | Peak process RSS at 4 (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| agda | 128 | 7.625 | 28.399 | 3.72× | 4.347 | 64.5 |
| metamath | 128 | 8.738 | 34.350 | 3.93× | 3.555 | 13.0 |
| rocq | 128 | 2.985 | 2.856 | 0.96× | 43.140 | 63.7 |
<!-- end:scale_extended -->

In a separate Metamath run, five trials of 32 jobs alternated which worker cap ran first. The median batch went from **3.677 s** with one worker (range 3.667–3.682 s) to **0.962 s** at a cap of four (range 0.957–0.985 s). All 320 checks matched their expected outcomes. [Five-trial receipt](../../../benchmarks/runtime/scalability-metamath-repeats.json)

Throughput divides jobs by batch wall time. The 95th percentile includes queue time and selects rank `ceil(0.95 × jobs)`, the last verdict for two- and four-job batches. Peak RSS is the highest memory reading for one native process.

These tables use one completed trial per cap, a 300-second checker deadline and a retained OS page cache. Suites overlapped on a shared host, with preparation timed separately. Use `--trials 5` on an idle machine to estimate variance. [Whole-database control](libraries.md#comparing-verifiers-on-the-same-library)

From the repository root, use `--provers` or `--workers` to change the comparison. The default is 16 jobs per prover, 4 for Isabelle/HOL and 2 for HOL Light.

```bash
# Measure fresh jobs from all ten provers, one prover at a time.
python -m benchmarks.runtime.scale --prefix "$ITPEVAL_PREFIX" \
  --output build/scalability.json
# Run a larger queue of 128 jobs per prover with the same worker comparison.
python -m benchmarks.runtime.scale --prefix "$ITPEVAL_PREFIX" \
  --provers agda metamath rocq --count 128 --output build/scalability-extended.json
# Repeat the Metamath comparison and alternate worker order.
python -m benchmarks.runtime.scale --prefix "$ITPEVAL_PREFIX" \
  --provers metamath --count 32 --trials 5 --output build/scalability-metamath.json
```

## Mixed-prover queue latency

This workload checks 32 candidates from six locked ACL2, Rocq and Metamath projects. Four workers share a per-prover cap of one each for Rocq and Metamath. Round-robin dispatch puts all three provers in the first wave. All 192 outcomes agreed across three paired runs. [Timings and command](../../../benchmarks/runtime/mixed-scheduler.json)

| Measurement | Earlier scheduler | Round-robin scheduler |
| --- | ---: | ---: |
| Batch wall time | 9.41 s | 8.56 s |
| First ACL2 verdict | 2.11 s | 1.52 s |
| First Rocq verdict | 4.52 s | 0.41 s |
| First Metamath verdict | 4.31 s | 0.11 s |

Values are medians, with at most 16 jobs in flight. The receipt also records failure recovery and cancellation. [Scheduler configuration](../execution/scheduling.md#check-several-candidates-in-parallel)

## Proof completions

Each completion is a fresh native check of a small fixed task with result caching bypassed. Peak RSS takes the largest reading across three single checks. Throughput includes lock validation and scheduling. The two worker configurations each use one valid and one invalid candidate, giving four scheduled attempts per row. Up to four suites shared the host. [Trial data](../../../benchmarks/runtime/linux-x86_64.jsonl)

<!-- table:completion -->
| Prover | First check (s) | Repeat (s) | Invalid (s) | Peak RSS (MiB) | 1 worker (jobs/s) | 2 workers (jobs/s) | Crashes / timeouts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| acl2 | 0.098 | 0.098 | 0.097 | 70.1 | 0.958 | 0.560 | 0 / 0 |
| agda | 0.113 | 0.113 | 0.114 | 63.4 | 7.813 | 14.954 | 0 / 0 |
| hol-light | 106.818 | 105.201 | 106.240 | 351.0 | 0.009 | 0.018 | 0 / 0 |
| hol4 | 0.399 | 0.415 | 0.334 | 112.1 | 1.653 | 1.411 | 0 / 0 |
| isabelle | 8.208 | 8.453 | 5.525 | 606.7 | 0.130 | 0.187 | 0 / 0 |
| lean4 | 0.283 | 0.283 | 0.285 | 465.2 | 1.415 | 1.482 | 0 / 0 |
| metamath | 0.118 | 0.118 | 0.083 | 12.8 | 8.830 | 15.025 | 0 / 0 |
| mizar | 0.063 | 0.063 | 0.063 | 12.9 | 2.969 | 1.826 | 0 / 0 |
| pvs | 0.684 | 0.684 | 0.649 | 378.4 | 1.353 | 2.520 | 0 / 0 |
| rocq | 0.132 | 0.132 | 0.133 | 63.7 | 3.242 | 2.876 | 0 / 0 |
<!-- end:completion -->

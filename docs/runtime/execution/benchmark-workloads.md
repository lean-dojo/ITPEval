# Benchmark a workload

<span id="measure-your-workload"></span>

From the repository root, run the benchmark with a pinned prefix and writable, isolated cache directory.

```sh
# Record native verification time and resource use.
PYTHONPATH=. python benchmarks/runtime/run.py --prefix "${ITPEVAL_PREFIX:-$HOME/.local/share/itpeval/toolchains/current}" \
    --cache /tmp/itpeval-benchmark-cache --provers metamath pvs \
    --workers 2 --count 4 --output runtime.jsonl
```

Both checks start fresh prover processes. The repeat uses the host’s page cache and any existing dependency builds. Compare native checker time with wall time, which includes lock validation and scheduling. [Raw completion measurements](../../../benchmarks/runtime/linux-x86_64.jsonl)

## Library-dependent runtime protocol

Use `--workload library` to check the pinned multi-declaration projects. The runner measures setup, native and wall time, memory, cache growth and verdict agreement. [Workload source](../../../benchmarks/runtime/library.py) · [Library measurements](../measurements/libraries.md#library-checks)

The reference matrix used separate caches for each prover and workload. All ten provers returned the same completion and library verdicts with one or two workers. [Native limits and trial data](../measurements/libraries.md#library-checks)

```sh
# Measure the library-dependent workloads on this host.
PYTHONPATH=. python benchmarks/runtime/matrix.py --prefix "$ITPEVAL_PREFIX" \
    --cache /tmp/itpeval-reference-cache --output /tmp/itpeval-reference-results
```

## Startup and negative cases

The startup probe runs the smallest supported workload twice in fresh processes, recording wall time, CPU time, peak memory and the native result. [Startup details](../measurements/startup-and-caching.md#fresh-native-startup)

An empty slot reports `incomplete` with execution `not_run`. A native open-goal diagnostic reports `incomplete` after execution `exited`. Syntax and typing failures report `rejected`. The PVS trials cover a malformed command and the valid but unfinished `(skip)`. These cases report `task_success=False`. [Negative-case inputs and verdicts](../../../benchmarks/runtime/malformed)

```sh
# Record fresh startup and rejection behavior separately.
PYTHONPATH=. python benchmarks/runtime/startup.py --prefix "$ITPEVAL_PREFIX" \
    --cache /tmp/itpeval-startup --output startup-results --workers 4
PYTHONPATH=. python benchmarks/runtime/negative_cases.py --prefix "$ITPEVAL_PREFIX" \
    --cache /tmp/itpeval-negative --output negative-results
```

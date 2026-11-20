# Startup and caching

## Fresh native startup

Each trial starts a fresh process in a private directory with minimal input. The host retains its page cache, and up to four suites run concurrently. HOL Light loads `hol.ml`, Isabelle starts the HOL heap, and Mizar runs accommodation and verification. [Startup trials](../../../benchmarks/runtime/startup-linux-x86_64)

<!-- table:startup -->
| Prover | First launch (s) | Repeat launch (s) |
| --- | ---: | ---: |
| acl2 | 0.064 | 0.064 |
| agda | 0.098 | 0.099 |
| hol-light | 107.145 | 105.634 |
| hol4 | 0.148 | 0.133 |
| isabelle | 2.920 | 2.938 |
| lean4 | 0.234 | 0.234 |
| metamath | 0.034 | 0.033 |
| mizar | 0.053 | 0.048 |
| pvs | 0.085 | 0.083 |
| rocq | 0.082 | 0.086 |
<!-- end:startup -->

## Loading a project and reusing a verification result

Preparation records the sources, dependencies and native build. Repeated preparation can reuse hashes and snapshots. Loading the lock validates those inputs.

Each row uses a bundled proof-completion task. **Miss** checks an input with an empty result cache. **Hit** retrieves the same evidence after lock validation. Both report wall time.

<!-- timing-controls -->

<!-- table:cache -->
| Prover | First prepare (s) | Repeat prepare (s) | Load lock (s) | Miss (s) | Hit (s) | Miss / hit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| acl2 | 2.533 | 0.829 | 0.835 | 0.941 | 0.911 | 1.0× |
| agda | 0.063 | 0.013 | 0.013 | 0.149 | 0.015 | 9.7× |
| hol-light | 0.887 | 0.153 | 0.151 | 104.843 | 0.150 | 701.1× |
| hol4 | 0.407 | 0.259 | 0.259 | 0.695 | 0.258 | 2.7× |
| isabelle | 2.179 | 0.690 | 0.684 | 9.155 | 0.685 | 13.4× |
| lean4 | 2.850 | 0.405 | 0.400 | 0.685 | 0.397 | 1.7× |
| metamath | 0.017 | 0.013 | 0.013 | 0.133 | 0.014 | 9.3× |
| mizar | 0.732 | 0.257 | 0.260 | 0.327 | 0.260 | 1.3× |
| pvs | 0.277 | 0.064 | 0.063 | 0.754 | 0.066 | 11.5× |
| rocq | 0.974 | 0.180 | 0.178 | 0.346 | 0.181 | 1.9× |
<!-- end:cache -->

HOL Light shows the largest difference because the miss initializes its OCaml environment. These trials predate the [lock validation change](throughput.md#faster-lock-validation).

Repeat prepare, lock, miss and hit are medians of three paired trials with the OS page cache retained. The ratio divides the median miss by the median hit. Toolchains were already installed. [Raw trials and build identities](../../../benchmarks/runtime/cache-latency.json) · [Runner](../../../benchmarks/runtime/cache_latency.py)

Use `verify_cached` to reproduce the hit for the same locked task and candidate. [Python example](../../reference/python.md#reuse-an-identical-check)

From the repository root, point `ITPEVAL_PREFIX` at an installation. The runner creates a temporary cache per prover. Add `--provers lean4 metamath` to measure a subset.

```sh
# Compare a fresh verification with a lookup of the same candidate.
python -m benchmarks.runtime.cache_latency --prefix "$ITPEVAL_PREFIX" --output cache-latency.json
```

### Reusing dependencies for a changed candidate

Building two HOL4 dependency theories took **2.994 s**. Reusing them reduced a new valid check from **5.686 s** to **2.894 s**, and the invalid check from **5.528 s** to **2.848 s** with the same rejection. Each attempt checked the candidate against the dependencies. [Reuse HOL4 theories](../execution/cache.md#reuse-compiled-hol4-dependencies) · [Trial data](../../../benchmarks/runtime/hol4-theories.json)

## Warm workers in the paper

The paper measured 16 Babel-formal statement files per prover. Cold verification starts an independent native check for each input. Warm verification checks new files through a worker pool or server that is already running. The elapsed times below are for the entire batch. [Paper, section 4.2 and Table 2](https://arxiv.org/html/2607.19407v1#S4.T2)

| Prover | Warm backend | Cold (s) | Warm (s) | Speedup |
|---|---|---:|---:|---:|
| Lean 4 | Compiler pool | 15.1 | 3.7 | 4.1× |
| Rocq | REPL pool with reset | 4.3 | 0.5 | 8.6× |
| Isabelle/HOL | Server batch | 472.2 | 6.9 | 68.4× |
| HOL Light | Preloaded forkserver | 527.4 | 149.0 | 3.5× |

In a separate Linux HOL Light experiment, a preloaded process forked a fresh child for each of five inputs. The five checks each took **22–57 ms** after initialization. Starting and shutting down the parent took **110.27 s**. That upfront cost matters when deciding how many checks to group into a batch. [HOL Light worker experiment](../hol-light-fork.md)

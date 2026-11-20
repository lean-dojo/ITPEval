# Library checks and extraction

## Library checks

Each trial checks a multi-declaration project and a source mutation. PVS typechecks a parameterized importing theory, and the other provers run their designated artifact checks. Each process has a 300 CPU second and 128 GiB virtual address-space cap, plus the task’s wall deadline. [Library inputs](../../provers/index.md) · [Raw trials](../../../benchmarks/runtime/library-linux-x86_64.jsonl)

<!-- table:library -->
| Prover | First check (s) | Repeat (s) | Invalid (s) | Peak RSS (MiB) | 1 worker (jobs/s) | 2 workers (jobs/s) | Crashes / timeouts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| acl2 | 0.190 | 0.190 | 0.190 | 120.3 | 0.861 | 0.553 | 0 / 0 |
| agda | 0.132 | 0.133 | 0.133 | 63.6 | 6.815 | 13.041 | 0 / 0 |
| hol-light | 107.211 | 105.259 | 106.424 | 351.2 | 0.009 | 0.018 | 0 / 0 |
| hol4 | 5.396 | 5.298 | 5.311 | 276.1 | 0.179 | 0.316 | 0 / 0 |
| isabelle | 8.448 | 8.498 | 5.446 | 589.8 | 0.129 | 0.186 | 0 / 0 |
| lean4 | 1.301 | 1.317 | 1.337 | 738.0 | 0.586 | 0.727 | 0 / 0 |
| metamath | 0.082 | 0.082 | 0.082 | 12.8 | 10.464 | 20.311 | 0 / 0 |
| mizar | 0.133 | 0.132 | 0.132 | 12.8 | 2.493 | 1.777 | 0 / 0 |
| pvs | 1.503 | 1.519 | 0.235 | 428.6 | 1.070 | 1.234 | 0 / 0 |
| rocq | 0.249 | 0.237 | 0.240 | 68.7 | 2.354 | 2.442 | 0 / 0 |
<!-- end:library -->

## Building a library retrieval index

The SQLite index stores consecutive visibility as a range. A declaration that leaves scope and returns gets another range. `CorpusIndex` reads both index formats. [Scoped premise lookup](../../guides/extract-and-build-a-dataset.md#look-up-premises-visible-at-a-theorem)

The 1,976-declaration `ql.mm` bundle produced a **2.61 MB** index, down from **414.65 MB**. The median build fell from **3.76 s to 0.47 s** across three paired trials. All 1,330,905 visibility pairs and 345 ranked lookups matched. Four timed lookup cases differed by at most 0.23 ms in their medians. These measurements cover a rebuild of the SQLite index from the same expanded JSONL. [Trial results and source hashes](../../../benchmarks/runtime/retrieval-index-optimization.json)

## Compact Metamath extraction

Three fresh `ql.mm` builds per mode agreed on ordered visibility lists, declaration IDs, dependencies and proof traces. Compact records used **1.09 MB** versus **90.15 MB** expanded. Median extraction time, including native verification and indexing, fell from **2.89 s to 1.47 s**.

The full `set.mm` run checked **48,388 proofs** and extracted **121,224 declarations**. Its 121,221 compact contexts represent **3.51 billion** visible-declaration pairs in **237 MB**. Inline IDs would occupy about **236 GB**, calculated from serialized widths. The run retained 1.43 GB of proof traces. Its stages took 98 s for extraction and native verification, 24 s for JSONL, and 20 s for indexing.

The `dataset` command took **167 s**, including verification, indexing and the referenced premise export. The training exporter wrote **1,935,826** labeled retrieval pairs in another **36 s**. [Trials, commands and resource use](../../../benchmarks/runtime/metamath-compact-extraction.json) · [Run compact extraction](../../guides/extract-and-build-a-dataset/extract-a-library.md#extract-a-large-metamath-database)

## Comparing verifiers on the same library

Each trial checks every proof in one database with a fresh process. ITPEval’s time includes its Python call, shell adapter, supervision and diagnostics. The table reports median wall seconds over three trials in rotated order. [Raw times and source hashes](../../../benchmarks/runtime/metamath-verifiers.json)

<!-- table:verifiers -->
| Database | Proofs | Metamath (s) | ITPEval (s) | mmverify.py (s) |
| --- | ---: | ---: | ---: | ---: |
| ql.mm | 1,140 | 0.061 | 0.132 | 0.357 |
| set.mm | 48,388 | 7.477 | 7.649 | 31.998 |
<!-- end:verifiers -->

ITPEval added **0.172 s** over calling Metamath directly on `set.mm`. On `ql.mm`, adapter startup makes up a larger share of the total.

Download both databases and the independent checker into the working directory. The runner checks the native success message for each method. [set.mm](https://github.com/metamath/set.mm/blob/844c01282c43f4ed03a8d302f19cd971a3a2be8c/set.mm) · [ql.mm](https://github.com/metamath/set.mm/blob/844c01282c43f4ed03a8d302f19cd971a3a2be8c/ql.mm) · [mmverify.py](https://github.com/david-a-wheeler/mmverify.py/blob/63a2aa3815cd5bf67892dbfc7f2048cbb177524c/mmverify.py) · [Runner](../../../benchmarks/runtime/metamath_verifiers.py)

```sh
# Run each verifier on the same databases so their timings are comparable.
python -m benchmarks.runtime.metamath_verifiers --prefix "$ITPEVAL_PREFIX" \
    --mmverify mmverify.py --database ql.mm set.mm --output metamath-verifiers.json
```

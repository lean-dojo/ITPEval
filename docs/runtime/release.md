# Reproduce a release

Use the release checkout, a Python virtual environment and Linux x86-64. Install the pinned provers and set `ITPEVAL_PREFIX` to their directory. [Native installation](toolchains.md#reproduce-the-pinned-toolchains) · [Lean and Rocq instruments](execution/optional-interfaces.md#reproduce-the-optional-native-interfaces) · [Isabelle setup](isa-repl.md)

The checked-in qualification records describe earlier archives. Run qualification against the exact wheel and source archive you intend to publish, and keep the resulting evidence with them.

The Lean qualifier reads compiler and instrument hashes from the installer. Keep Isabelle sources in `$ITPEVAL_PREFIX/auxiliary/isabelle` or pass `--isa-integrations`. The library checks include Rocq Stdlib, a certified ACL2 Community Book and an MML article. [Library fixtures](../provers/index.md)

## Build the wheel and source archive

Run these commands from the release checkout. The PyTorch CPU wheel matches the small Metamath training example used during the release checks.

```bash
# Build the distributions and install the wheel into the release environment.
release_dir="${ITPEVAL_RELEASE_DIR:-$PWD/build/itpeval-release}"
python -m pip install 'setuptools>=68' wheel
python -m scripts.check_distribution --dist-dir "$release_dir/dist"
python -m pip install 'torch==2.11.0' --index-url https://download.pytorch.org/whl/cpu
wheel=("$release_dir"/dist/*.whl)
python -m pip install "${wheel[0]}[evaluation,grpo,isabelle,parquet,training]"
```

## Check the installed package

The release script tests a wheel and a separate source-archive installation outside the checkout. It records preparation, extraction, checking, learning and interaction in a directory per prover. `--jobs` caps concurrent provers, and `--probe-jobs` caps checks per prover. HOL Light reloads its libraries for each independent check.

```bash
# Reuse the distributions built above for native qualification.
release_dir="${ITPEVAL_RELEASE_DIR:-$PWD/build/itpeval-release}"
python -m scripts.check_distribution --from-dist "$release_dir/dist" \
  --native-report "$release_dir/native/qualification.jsonl" --cache "$release_dir/cache"
python -m scripts.qualify_native --distributions "$release_dir/dist" --prefix "$ITPEVAL_PREFIX" \
  --cache "$release_dir/cache" --output "$release_dir/native" --jobs 2
python -m scripts.check_release "$release_dir/native/qualification.jsonl" \
  --distributions "$release_dir/dist"
```

## Read the reports

Find the reports beside the archives in the checkout or CI artifacts. Each report identifies both archives by hash. The archives include the probes and fixtures.

The gate checks archive hashes, native acceptance and rejection, named obligations, revision identity, finalization after deletion, reset and replay. It compares dataset rows, five evaluation routes and a trainer update. Additional native operations need evidence from their own fixtures. [Runtime measurements](measurements.md) · [Capability matrix](../reference/capabilities.md)

GitHub Actions builds the archives once and downloads them for each prover shard. Scheduled, manual and tagged runs also check all ten shards together. [Conformance workflow](../../.github/workflows/conformance.yml)

<details markdown="1"><summary>Implementation and review ownership for this release</summary>

| Prover | Integration lead | Review focus |
|---|---|---|
| Lean 4 | Runtime implementer (`runtime`) | Kernel assumptions, proof regions and native instrument versions |
| Rocq | Corpus implementer (`corpus`) | Section discharge, module context and pending goals |
| Isabelle/HOL | Release lead (`root`) | HOL session preparation and isolated Isa-REPL rollback |
| HOL Light | Runtime implementer (`runtime`) | Tactic states and worker isolation |
| ACL2 | Runtime implementer (`runtime`) | Admitted events, guards, rule use and replay |
| Agda | Corpus implementer (`corpus`) | Hole state, constraints and imported libraries |
| HOL4 | Runtime implementer (`runtime`) | Trusted compiled theories and theorem assumptions |
| Metamath | Evaluation implementer (`evaluation`) | Fixed proof tasks, verified stacks and trainer rewards |
| Mizar | Corpus implementer (`corpus`) | Accommodation, semantic XML and article diagnostics |
| PVS | Release lead (`root`) | Sequent traces, named formulas and generated obligations |

</details>

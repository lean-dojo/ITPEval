# ITPEval

> **Review branch.** This is a development snapshot. Full release qualification for the newer proof-session and ATP features is pending. [Release checks](docs/runtime/release.md)

ITPEval gives ten theorem provers a common Python interface. Check a file, extract a library, or run an agent that proposes proof edits and learns from the native checker’s feedback. Replay attempts and export them for training. [Quickstart](docs/start/quickstart.md) · [Features](docs/start/features.md)

## Prepare a project and verify a proof

From a checkout, install the Python package and Metamath. [Platform setup](docs/runtime/toolchains.md)

```bash
python -m pip install -e .
itpeval install metamath
```

This example locks the bundled project and checks `|- pair x y`.

```python
from pathlib import Path

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project
from itpeval.verification import verify

# Lock the sources and checker before submitting a proof.
project = prepare_project("metamath", curated_project("metamath"),
                          prefix=default_prefix(), cache=Path("cache"))
task = get_backend("metamath").build_task(project)
evidence = verify(task, "vx vy distinct", prepared=project)
assert evidence.task_success is True, evidence.stderr
```

For your own theorem, specify the target and editable proof region. To edit a bundled exercise in VS Code, run `itpeval practice` with your prover ID. [Work with your own files](docs/guides/work-with-a-library.md) · [Try a VS Code exercise](docs/start/proof-completion.md)

## Extract a library for training

```bash
# Write declaration records and premise-selection examples.
itpeval dataset metamath --output ./metamath-dataset
```

Use `--project DIR --entrypoint FILE` for your own library. The export reports which fields the prover supplied. Combine libraries across provers and export JSONL or Parquet for pretraining, fine-tuning, retrieval, or reinforcement learning. [Combine libraries](docs/guides/extract-and-build-a-dataset/combine-libraries.md) · [Choose a training view](docs/guides/training-data/choose-a-view.md)

## Search for a proof with an ATP

Run E or Vampire on TPTP problems or ask for help on supported interactive goals. ITPEval checks completed interactive proofs in the original prover. [Automated proof search](docs/guides/automated-proving.md)

## Run an agent or evaluation loop

An agent can submit a full proof candidate or advance a native proof one action at a time. Save candidate edits, goals, and checker feedback with the project lock. Reuse setup and run independent checks across workers. [Agent examples](docs/guides/verification-and-learning.md) · [Measured throughput](docs/runtime/measurements/throughput.md)

```bash
# Record a rejected proof, its repair, and a fresh replay.
python -m itpeval.learning.example --prover metamath --cache ./cache \
  --output ./evidence/metamath
```

## Import the translation benchmark

The benchmark has **2,634 aligned statement items across ten provers** and **74 proof items across four**. A release checkout can import the corpus with its original IDs and provenance. [Benchmark and paper](docs/benchmarks/translation.md) · [Dataset inventory](docs/new_data_description.md)

```bash
# Import the released data into a fresh directory.
python -m itpeval.corpus.importers.itpeval . ./released-corpus
```

```bash
# Preview one Lean-to-PVS translation prompt without a model call.
python -m pip install -e '.[evaluation]'
python -m eval.pipeline.translation.run --sources babel-formal --ids 1 \
  --src lean4 --tgt pvs --model gpt-5.5 --dry-run
```

## Reference and licensing

[Python API](docs/reference/python.md) · [Agent skills](docs/agents/index.md) · [Backend capabilities](docs/reference/capabilities.md) · [Documentation preview](website/README.md)

The MIT license covers the original repository material. The dataset notices identify upstream licenses. [Repository license](LICENSE) · [Third-party notices](data/third_party_licenses/README.md)

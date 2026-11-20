# Extract a library

Choose an installed prover to extract its bundled library. The command prints paths to the declarations, premise records, and full bundle. [Install a prover](../../runtime/toolchains.md#install-the-stable-releases)

<div class="dataset-example" markdown="1">
<!-- dataset-controls -->

```sh
# Export declarations and premise-selection records into the dataset directory.
python -m itpeval.cli dataset metamath --output ./dataset
```

</div>

## Extract your own project

Add `--project ./my-library --entrypoint path/to/source` with an entrypoint relative to the project root. For pinned dependencies, use `itpeval dataset --lock PATH --entrypoint FILE --output ./dataset`. Export each entrypoint and check `report.json` for skipped files. [Prepare a project with imports](../environment-manifest.md)

## Extract a large Metamath database

Put the database and its include files in a project directory. For `set.mm`, use compact contexts so each record refers to the shared prefix of earlier assertions. The bundle retains active hypotheses, disjoint-variable conditions, proof references, and the full proof-stack traces. [Full database measurements](../../runtime/measurements/libraries.md#compact-metamath-extraction)

```bash
# Extract and index the complete database with referenced premise contexts.
itpeval dataset metamath --project ./metamath-db --entrypoint set.mm \
  --context-storage compact --timeout-s 300 --output ./metamath-data
```

With compact storage, each premise row has `available: null`. Resolve `declaration.context_id` against the original bundle. Declaration IDs identify the same locked source occurrence in either storage mode. To materialize full premise lists, pass `--premise-visibility expanded`. An expanded row has `available: []` when its scope is empty.

```python
from pathlib import Path

from itpeval.corpus.contexts import ContextTable
from itpeval.corpus.storage import read_jsonl

# Use the bundle path printed by the dataset command.
bundle = Path("./path-to-extraction-bundle")
target = next(row for row in read_jsonl(bundle / "declarations.jsonl") if row["name"] == "mpd")
context = ContextTable(bundle).context(target["context_id"])
print(len(context.visible), context.hypotheses)
```

## Export Parquet

Install the optional dependency from the checkout, then request Parquet directly from the dataset command. The exporter preserves nested dependency records, null targets, empty lists and proof-use availability.

```sh
# Install the optional writer and export both views as Parquet.
python -m pip install '.[parquet]'
itpeval dataset metamath --output ./dataset --format parquet
```

To convert existing JSONL without another prover run, use `python -m itpeval.corpus.parquet declarations SOURCE DESTINATION`. Replace `declarations` with `premises` for the premise-selection file. Pass the paths the original export printed.

The extraction tests cover known declarations, proof fields, and reproducibility on a bundled fixture for each of the ten provers. [Per-prover extraction results](../../../benchmarks/runtime/stable-extraction.json)

Check coverage and find the records for a target declaration in the resulting bundle. [Read an extraction bundle](read-a-bundle.md)

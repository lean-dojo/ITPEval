# Combine libraries across provers

Extract each library with its own toolchain. Use the library's source entrypoints to include its declarations. A client that imports a compiled library may produce declarations for that client alone. Save the bundle directory printed by each run. [Extract a library](extract-a-library.md)

Create a `libraries.json` catalog. Use one entry per library revision and list the bundles from every entrypoint you want to include. The names are labels you choose. Paths are relative to the catalog file. Replace the example paths with the bundle directories printed by your extraction commands.

```json
{
  "schema_version": 1,
  "libraries": [
    {
      "name": "Mathlib",
      "revision": "fc4f59e577feb1a4956671bc04ac18aaaf8cd842",
      "license": "Apache-2.0",
      "bundles": ["build/extractions/mathlib-language", "build/extractions/mathlib-nat"]
    },
    {
      "name": "Metamath quantum logic database",
      "revision": "844c01282c43f4ed03a8d302f19cd971a3a2be8c",
      "license": "CC0-1.0",
      "bundles": ["build/extractions/metamath-ql"]
    }
  ]
}
```

```bash
# Combine declarations and premise records into JSONL and Parquet tables.
itpeval training-data libraries --catalog libraries.json \
  --output build/combined-libraries --format both

# Use the same catalog to export source text and labeled premise pairs.
itpeval training-data native --catalog libraries.json \
  --output build/library-training --format both
```

Each declaration keeps its prover, library, revision, source location, and environment ID. The collection manifest records the entrypoints and the files they covered. Group occurrences in a locked environment with `declaration_id`. Repeated observations retain their bundle IDs so you can compare contexts and proof-use evidence.

Use explicit correspondence data to align theorems across languages. [Aligned translation corpus](../../benchmarks/translation.md#dataset-scope)

For a large combined dataset, add `--premise-visibility reference`. Each premise row uses its `bundle_id` and `declaration.context_id` to refer to the context. Keep the bundle folders with the export. The same option works with JSONL and Parquet.

The optional `revision` and `license` fields document the snapshot you selected. The environment ID identifies the source and toolchain that produced the extraction. Keep the original bundles if you need to follow source hashes back to bytes or inspect the native evidence.

```python
from datasets import load_dataset

# Stream the combined declarations and browse just the Mathlib rows.
rows = load_dataset("parquet", data_files="build/combined-libraries/declarations.parquet",
                    split="train", streaming=True)
mathlib = rows.filter(lambda row: row["library"] == "Mathlib")
print(next(iter(mathlib))["statement"])
```

`split="train"` selects the loader’s default name for this file. Assign your training and evaluation partitions before building model inputs. [Keep related examples together](../training-data/choose-a-view.md#keep-related-examples-together)

The collection reads the shared extraction format, so a future prover can join as soon as an exporter produces a conforming bundle. To run extraction directly in ITPEval, register a native extraction backend and its environment setup. Proof tasks and live checker rewards need the corresponding verifier. [Add a prover backend](../../reference/extending-a-backend.md)

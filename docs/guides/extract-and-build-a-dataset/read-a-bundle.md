# Read an extraction bundle

Start with `report.json` to see which files the adapter covered and which fields it recovered. Use the tables and source blobs to inspect individual declarations.

| File | What it contains |
|---|---|
| `declarations.jsonl` | Names, kinds, statements, source locations and checker status |
| `contexts.jsonl` | IDs of visible declarations and imports |
| `dependencies.jsonl` | Edges for imports, references and proof use |
| `index.sqlite` | Local lookup by environment and context |
| `report.json` | Coverage by input file and availability by field |
| `blobs/` | Original source bytes and native evidence stored by SHA-256 |

A source range is a half-open UTF-8 byte interval. It may cover a name, statement, or complete command depending on the native tool. An unresolved dependency keeps its source name and uses a null target ID. Use `match_target` to join a proof task's source anchor to a native occurrence from the same environment, file, and source hash. [Replay and train on proof attempts](../verification-and-learning.md)

## Look up premises visible at a theorem

Use the context ID for `pair-rule` in `client.mm` to search only premises that theorem can cite.

```python
# Restrict premise lookup to declarations visible at the target.
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.environments import prepare_project
from itpeval.retrieval import CorpusIndex
from itpeval.corpus.storage import read_jsonl

environment = prepare_project(
    "metamath", LIBRARY / "metamath/library",
    prefix=default_prefix(), cache=Path("build/prepared"),
)
bundle, dataset = export_dataset(environment, "client.mm", Path("build/dataset"))
target = next(d for d in read_jsonl(bundle.path / "declarations.jsonl") if d["name"] == "pair-rule")
# The context ID restricts retrieval to premises in scope for pair-rule.
index = CorpusIndex(bundle.path / "index.sqlite")
premises = index.search("pair", environment_id=environment.environment_id, context_id=target["context_id"])
assert [p["name"] for p in premises] == ["pair-dv"]
```

| Premise-selection field | Meaning |
|---|---|
| `available` | Declarations in scope, or `null` when the row refers to a compact context |
| `retrieved` | Search results when an experiment records retrieval |
| `proof_used` | References the adapter observed in the proof |
| `proof_used_availability` | Whether the observed references can support a training label |

The SQLite index stores visibility ranges to use less disk space. The scoped lookup API works with both index formats. [Library index measurements](../../runtime/measurements/libraries.md#building-a-library-retrieval-index)

For formats and fields that depend on the backend, see [Native evidence by prover](native-evidence.md).

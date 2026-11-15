# Evaluation inputs

| Input | Items | Records | Provers | Directed pairs |
|---|---:|---:|---:|---:|
| `extended/manifest.json` and eight dataset shards | 2,634 | 26,340 | 10 | 237,060 |
| `proofs.json` (available proof records) | 74 | 296 | 4 | 888 |

Statement translation uses the same ten-prover input for every direction.
Proof translation uses the available records in `proofs.json`; cycle utilities
use `minif2f_nl4itp.jsonl`. The archived `stmts.json` is retained for the existing
Lean-target BEq runner and is not a selectable statement-translation corpus.

## Records and identities

The proof file and each statement shard are JSON arrays. Core fields:

| Field | Meaning |
|---|---|
| `theorem_id` | Stable integer release identity; previously assigned IDs remain reserved |
| `title` | Shared item title/file stem across its prover representations |
| `source` | Dataset name; include it when joining records |
| `tier` | `a` for Babel-formal; `b` for the other datasets |
| `prover` | Native adapter ID |
| `content` | Complete statement or proof source text |
| `split` | miniF2F's `test` or `valid` membership |

Statement records additionally contain `item_id` (canonical dataset identity),
`artifact` (repository-relative source path), and `sha256` (source-file bytes).
Ten-way membership is explicit in `../subsets/extended_stmts_2634.json`.
Existing identities keep their integer IDs, excluded IDs remain reserved,
and additional identities use IDs above 390. IDs therefore
need not be contiguous. Catalogue numbers and dataset-specific IDs are `item_id`,
not necessarily `theorem_id`.

Join representations by `(source, theorem_id)` and records by
`(source, theorem_id, prover)`. The corpus does not deduplicate mathematical
content across datasets. Pin the data revision and source hashes when reproducing
an experiment: matching IDs alone does not establish unchanged content.

## Access

```python
from eval.pipeline.translation.data import load_statement_records, load_pairs

records = load_statement_records(sources=["putnambench"])
assert len(records) == 6570
pairs = load_pairs("stmts", sources=["babel-formal"])
assert len(pairs) == 15 * 10 * 9
```

Each dataset shard has a checksum in `extended/manifest.json`. The loader checks
it before use and loads only requested datasets. Statement result IDs include a
version prefix and source-content fingerprint so changed content cannot silently
reuse a different input's checkpoint.

From the repository root, `python3 data/build_eval_jsons.py --check` verifies
export bytes against the current selected sources without writing. See
[data/README.md](../../data/README.md) for regeneration and provenance.

# Import the released benchmark

Use the importer when you need the aligned artifacts and review records from the released translation corpus. Run it from the checkout and give it a new destination directory.

```sh
# Import the released benchmark into a fresh local directory.
python -m itpeval.corpus.importers.itpeval . /tmp/itpeval-release
```

The importer checks the source and shard hashes before writing the corpus. It preserves the original item IDs, membership, dataset indexes, licenses, run data and canonical review decisions. Read the import manifest for the checkout revision, the importer revision, the historical `source_commit` and the input hashes.

## Keep related tasks in the same split

All formal representations of one item go into the same partition. For example, Lean and PVS versions of a single theorem belong together. The importer keeps the upstream miniF2F split and groups the 597 related nTP4VC obligations by their 202 original Why3 programs. To group reviewed duplicates across datasets, pass their benchmark item IDs in `duplicate_groups`. The importer raises an error if a group has conflicting upstream splits.

## Read the review and source records

| Record | What it tells you |
|---|---|
| `alignments.jsonl` | The artifacts that share an item ID in the released benchmark |
| `reviewed_correspondences.jsonl` | A directed review decision with its references, hashes and recorded native checker outcome |
| `canonical_statements.jsonl` | PutnamBench's separate canonical judgments and upstream revision |
| Source locator | A declaration's kind, role, checker status, and byte range in its original artifact |

A native checker outcome and a semantic review answer different questions. Some artifacts that passed the checker received a negative formalization review. A mapped locator's `basis` says how the importer resolved it, through a reviewed span, released index identifier, or literal membership identifier. The `candidate_target_locators` field keeps less direct matches such as naming conventions for review. An artifact with only a Metamath comment reports `comment_only_no_declaration`.

The recorded import preserved 26,340 artifacts and mapped 6,702 source locations. Among those, 22 spans were individually reviewed, 1,070 matched a released index identifier, and 5,610 matched a literal membership identifier. The receipt also counts candidate-only, comment-only and unresolved artifacts by prover and dataset. [Frozen corpus import receipt](../../../benchmarks/corpus/released-import.json)

Use the Python API to look up a review by item, target path or decision. This example reads the target-expressivity decision for item 392.

```python
# Read reviewed correspondences between declarations in different provers.
from itpeval.alignment import reviewed_correspondences

reviews = reviewed_correspondences(
    "/tmp/itpeval-release", benchmark_item_id=392, decision="blocked_target_expressivity",
)
for review in reviews:
    print(review.target.path, review.decision, review.native_check, review.evidence_sha256)
```

Use the imported corpus to build aligned views for formalization and translation. [Export benchmark views](../training-data/export-the-benchmark.md)

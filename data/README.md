# Benchmark sources

The primary statement corpus has 2,634 dataset-scoped items represented in all
ten provers, across Babel-formal, Hundred Theorems, miniF2F, PutnamBench, nTP4VC,
Logipedia, Thousand Theorems, and VERINA. See
[the exact coverage description](../docs/new_data_description.md).

## Source layout

Statement sources use `data/<dataset>/data/stmts/<prover>/`, with source metadata
in `data/<dataset>/data/index.json`. miniF2F keeps `test/` and `valid/` subdirectories;
nTP4VC and Logipedia preserve nested source identities. Prover IDs are `lean4`,
`rocq`, `isabelle`, `hol-light`, `acl2`, `agda`, `hol4`, `metamath`, `mizar`, and `pvs`.

The source directories also retain candidate items outside the ten-way intersection.
Only the 2,634 identities in `eval/subsets/extended_stmts_2634.json` are exported.
The 59 excluded candidates lack ordinary ACL2 statements. ACL2r files are not used.
miniF2F aliases and nTP4VC filename normalization are explicit in
`extended_inventory.py`; supporting modules and alias files are not extra items.

nTP4VC includes the selected 600 candidate identities, the selection list, and
Why3 source/repair records. Source statements that were symlinks in the development
checkout are materialized as ordinary files. No external git checkout is needed
to build or audit this release. Putnam metadata used by the audit is bundled in
`putnambench/data/upstream_problem_metadata.json`.

Archived source exports stay at `data/{babel-formal,hundred-theorems,minif2f}/`
under their existing `stmts/` and `proofs/` directories. They provide provenance
for retained reference and proof files; statement runs use the ten-way membership.

## Rebuilding exports

```bash
python3 data/build_eval_jsons.py          # statement shards
python3 data/build_eval_jsons.py --check  # read-only byte-for-byte consistency check
python3 docs/audit_extended_dataset.py    # read-only inventory and source breakdowns
```

The builder preserves assigned IDs for existing identities and allocates
new IDs above 390. The checked-in extended membership freezes those assignments:
a changed identity/path map is rejected for explicit review. Exports include the
source path and SHA256 for every representation, and the manifest hashes each shard.

The archived `eval/data/stmts.json` reference export and `proofs.json` proof
records are preserved as separate artifacts; the statement builder only writes
the ten-prover shards and membership manifest.

## Interpretation

Statements can contain multiple declarations, axioms inherited from a source
signature, or complete program contracts. Presence in all ten systems is an
inventory criterion, not an equivalence or proof certificate. The
`tier` field uses `a` for Babel's controlled axiomatized files and `b` for the
other datasets; it is a repository grouping, not an upstream difficulty label.

The available proof data contains 74 items / 296 records in four provers.
Statement coverage does not imply proof availability. miniF2F's test/validation
split and nTP4VC's source-level leakage constraints remain relevant.

See [the record schema](../eval/data/README.md) and
[third-party provenance and notices](third_party_licenses/README.md).

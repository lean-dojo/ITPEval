# Release membership

- `extended_stmts_2634.json`: exact ten-way statement membership, stable integer
  IDs, dataset identities, miniF2F splits, and every selected source path.
- `full_stmts_390.json`: ID-reservation manifest used to keep previously assigned
  IDs stable when building the release.
- `full_proofs_74.json`: membership of the available proof records.

The statement loader uses the ten-way membership for all source/target provers.
Generic dataset, item and direction filters narrow that common population; the
ID-reservation manifest is provenance, not a separate benchmark run mode.

The extended builder rejects changed membership rather than silently renumbering
items. A changed release population requires an explicit review of this manifest
and its documented counts. Shard content hashes are in `../data/extended/manifest.json`.

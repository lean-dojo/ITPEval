# ITPEval Tasks

This directory stores benchmark tasks in a prover-neutral layout.

Current arithmetic smoke tasks:
- `arith_0_plus_0/` — proves `0 + 0 = 0`
- `arith_1_plus_1/` — proves `1 + 1 = 2`
- `arith_2_plus_2/` — proves `2 + 2 = 4` in all ten release provers
- `arith_2_times_3/` — proves `2 * 3 = 6`
- `arith_3_plus_3/` — proves `3 + 3 = 6`

Layout convention:
- `itpeval/tasks/<task-name>/<prover>/...`
- each prover directory contains the exact filenames its adapter expects
- task files should be self-contained when possible
- optional `task.json` files can describe the task metadata and prover mapping

The benchmark layer is separate from the prover adapters:
- adapters know how to install/check a prover
- tasks provide the proof artifact or script to verify

Each arithmetic task has the prover coverage listed in its task metadata. The
ten-prover statement inventory is maintained separately under `data/` and
`eval/subsets/`; the smoke tasks do not establish whole-corpus acceptance.

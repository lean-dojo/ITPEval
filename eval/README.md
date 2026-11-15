# Evaluation pipeline

ITPEval supports statement translation between Lean 4, Rocq, Isabelle/HOL,
HOL Light, ACL2, Agda, HOL4, Metamath, Mizar, and PVS.

## Scope and modes

| Mode | Input | Directed tasks |
|---|---|---:|
| `stmts` (default) | 2,634 items × ten provers, eight datasets | 237,060 |
| `proofs` | 74 items with available proof records | 888 |

Statement mode asks for the proposition in the target system, without proving it.
Each target has its own representation: for example ACL2 predicates, Agda types,
quoted HOL terms, and PVS Boolean definitions. Response extraction and structural
validation precede native checks. Native acceptance alone does not establish
semantic equivalence or theorem truth. Proof mode asks for a complete checked
proof; admissions and prover-specific escape hatches are rejected.

All ten provers share the statement interface. Proof pairs are drawn from the
available records in `proofs.json`, currently covering Lean 4, Rocq, Isabelle/HOL,
and HOL Light. Statement coverage does not imply completed proofs in every prover.
See [data/README.md](data/README.md) for schemas, stable IDs, and export checks.

## Setup

From a repository checkout:

```bash
pip install -e .
cp eval/.env.example eval/.env
```

Set only the provider keys needed for the run (`OPENAI_API_KEY`,
`ANTHROPIC_API_KEY`, `GEMINI_API_KEY`, or `OPENROUTER_API_KEY`). Model identifiers
are configured in `pipeline/config.py`; availability depends on the provider.
Install the desired target provers using [the harness guide](../itpeval/README.md).
Linux supports all ten adapters; see the guide for macOS limitations.

## Synchronous runs

```bash
python3 -m eval.pipeline.translation.run \
  --sources babel-formal --ids 1 \
  --src lean4 --tgt pvs --model gpt-5.5 --dry-run
```

`--dry-run` previews prompts without API calls, prover runs, or output-directory
creation. Remove it to execute. Narrow the selection before a full run; the
statement population contains 237,060 directed tasks per model/sample.

| Option | Purpose |
|---|---|
| `--mode stmts` / `--mode proofs` | Translate statements or available proofs; default is `stmts` |
| `--sources` | Comma-separated dataset names |
| `--ids` | Comma-separated release theorem IDs |
| `--subset` | JSON list of `{source, theorem_id}` records |
| `--src`, `--tgt` | Directed source/target prover filters |
| `--k`, `--temperature`, `--max-tokens` | Sampling and generation settings |
| `--workers` | Concurrent generation/verification workers |
| `--max-src-chars` | Explicit source-length filter, reported in output |
| `--no-verify` | Store raw generations without native checking |
| `--resume PATH` | Resume an existing result file |

Results include a data-version identity and source SHA256. Statement custom IDs
include that version and source fingerprint. Use a separate results file for each
model and sampling configuration, and retain the same settings when resuming.

## Batch submission and collection

```bash
python3 -m eval.pipeline.translation.batch_run submit \
  --sources babel-formal --ids 1 --src lean4 --tgt agda \
  --models gpt-5.5 --dry-run
```

Remove `--dry-run` to submit. Submission supports the same dataset, ID, subset,
and prover filters. It writes a job file under `results/batch_jobs/`.
Collect on a machine with the target toolchains installed:

```bash
python3 -m eval.pipeline.translation.batch_run collect \
  eval/results/batch_jobs/<timestamp>.json --workers 8
```

Collection is resumable and uses the same response validation/native verifier
as synchronous runs. Completed job files embed provider responses, so collecting
those files does not require provider access. Generated results and checkpoint
files stay local and are ignored by Git.

## Existing BEq and cycle experiments

The BEq implementation accepts verified **Lean 4 targets** and reads the archived
reference export `data/stmts.json`. It is not yet connected to the statement
shards, so it must not be used to claim equivalence scores for this ten-prover
release. Native acceptance and semantic equivalence are different checks.
The cycle utilities use their own `minif2f_nl4itp.jsonl` input and
`pipeline/cycle/` entrypoints; they do not define the statement population.

## Local verification

```bash
python3 data/build_eval_jsons.py --check
python3 -m unittest discover -s eval/pipeline/tests
python3 -m unittest discover -s itpeval/tests
```

These checks require the standard library, use local fixtures, and do not call
model providers or certify native acceptance of the entire dataset. Real smoke
checks are available through `./itpeval/bin/itpeval check --task hello <provers>`.

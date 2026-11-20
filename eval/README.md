# Evaluation pipeline

## Scope and modes

| Mode | Input | Directed tasks |
|---|---|---:|
| `stmts` (default) | 2,634 items × ten provers, eight datasets | 237,060 |
| `stmts --corpus published` | Published 390 items × four original provers | 4,680 |
| `proofs` | 74 items with available proof records | 888 |

Statement mode checks the generated proposition in the target prover. Semantic equivalence is a separate check. Proof mode requires a completed proof and rejects admissions. Its pairs come from `proofs.json`, covering Lean 4, Rocq, Isabelle/HOL, and HOL Light. [Record schemas and export checks](data/README.md)

## Setup

From a repository checkout:

```bash
pip install -e '.[evaluation]'
cp eval/.env.example eval/.env
```

Set only the provider keys needed for the run (`OPENAI_API_KEY`,
`ANTHROPIC_API_KEY`, `GEMINI_API_KEY`, or `OPENROUTER_API_KEY`). Model identifiers
are configured in `pipeline/config.py`; availability depends on the provider.
Install the native target provers before running checks. [Toolchain setup](../docs/runtime/toolchains.md)

## Synchronous runs

```bash
python3 -m eval.pipeline.translation.run \
  --sources babel-formal --ids 1 \
  --src lean4 --tgt pvs --model gpt-5.5 --dry-run
```

`--dry-run` previews prompts without API calls, prover runs, or output files. Filter the task selection before running without it.

| Option | Purpose |
|---|---|
| `--mode stmts` / `--mode proofs` | Translate statements or available proofs; default is `stmts` |
| `--corpus published` | Select the published four-prover statement population and its original request IDs |
| `--responses PATH` | Read a JSON object mapping selected request IDs to prerecorded response text |
| `--output PATH` | Choose the destination of a new run |
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

Set `--job-file PATH` on submit to choose a durable job to resume. Submit writes the immutable request plan, model settings and per-chunk state before contacting the provider. If a connection drops during submission, check the provider dashboard for the batch ID. Rerun the same command with `--recover-batch LABEL=ID` to recover that job, or use `--retry-unconfirmed LABEL` after confirming that the provider did not create it. Collect writes one record for every submitted request, including missing outputs and provider errors. Supply `--output PATH` to select the verified output.

The local prerecorded transport accepts `--responses PATH` in place of a model. It stores the exact request and response in the adjacent job spool and checks the receipt digest on collection.

Collection can resume and uses the same verifier as synchronous runs. Completed job files contain the responses and can be collected offline. Git ignores generated results and checkpoints.

## Existing BEq and cycle experiments

The historical BEq runner accepts verified Lean 4 statement translations. Published records use `data/stmts.json`. Extended records use their dataset, theorem and target prover to find the reference in the checksum-verified shards. The result retains both directional checks and reports “equivalence not established” when bounded search is unsuccessful. Use `--output-dir PATH` to select a new result directory. The checker for extracted Lean declarations is documented separately. [Declaration equivalence](../docs/reference/python.md)

The following command replays a published MiniF2F Lean→Rocq statement through synchronous generation, batch submit/collect and post-hoc verification. It uses recorded text and the local Rocq installation. Each result retains the raw fenced response, the extracted statement, and its native acceptance with an unbound target.

```bash
python -m eval.pipeline.published_qualification --output ./published-translation.json
```
For autoformalization and auto-informalization, `python -m eval.pipeline.cycle.run` generates English-to-formal-to-English-to-formal round trips from `minif2f_nl4itp.jsonl`. Choose Lean alone or all four paper provers. Then run `python -m eval.pipeline.cycle.verify` to check the generated formal statements. [Worked example and commands](../docs/guides/formalization-and-translation.md#round-trip-evaluation)

## Local verification

```bash
python3 data/build_eval_jsons.py --check
python3 -m unittest discover -s eval/pipeline/tests
python3 -m unittest discover -s itpeval/tests
```

These checks require the standard library, use local fixtures, and do not call
model providers or certify native acceptance of the entire dataset. Real smoke
checks are available through `./itpeval/bin/itpeval check --task hello <provers>`.

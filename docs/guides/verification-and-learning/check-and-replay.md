# Check and replay proof attempts

## Check one candidate

The Metamath exercise proves `|- pair x y`. Submit `vx vy distinct` to put the two variable hypotheses on the stack and apply the rule for distinct variables.

```bash
# Keep the lock path so subsequent attempts use the same database.
itpeval prepare metamath --cache ./cache > project.json
LOCK=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')
itpeval verify-task --lock "$LOCK" --candidate "vx vy distinct"
```

For your own task, prepare the project with its completion manifest. If the manifest differs from `completion.json`, pass its project-relative path with `--manifest`. [Define a proof task](../../reference/task-manifests.md)

## Save and replay an episode

The demo submits two prerecorded fragments. Metamath rejects `vx vx distinct` because it repeats a variable, then accepts `vx vy distinct`. [Choose a prover exercise](../../start/proof-completion.md)

```bash
# Print both candidate verdicts and save the episode and training views.
python -m itpeval.learning.example --prover metamath --show-attempts \
  --cache ./cache --output ./evidence/metamath
```

The command prints the path to `episodes.jsonl`.

| File | What to use it for |
|---|---|
| `dataset.jsonl` | Find the exact declaration, source bytes and context the task refers to |
| `episodes.jsonl` | Replay an ordered series of attempts and inspect its final proof |
| `attempts.jsonl` | Inspect or score individual attempts |
| `supervised.jsonl` | Train on accepted completions |
| `repair.jsonl` | Train on a failed edit, its diagnostic and the next successful edit |
| `trajectory.jsonl` | Read the actions, observations and rewards in order |
| `replay.json` | Inspect evidence from a fresh check of every submitted edit and the final artifact |

The run manifest records which dataset row, environment and attempt budget you used. Keep null rewards in your run counts and exclude them from scored training rows. Record a retry after a timeout or checker failure as a separate attempt.

Write your candidates to `edits.json` as a JSON array of proof fragments. Use the same lock, or supply one for your own project. Reusing the output directory checks the saved configuration and replays its episode.

```bash
# Read the candidate sequence from edits.json, then replay the saved episode.
LOCK=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')
python -m itpeval.learning.example --lock "$LOCK" --manifest completion.json \
  --candidates ./edits.json --cache ./cache --output ./my-run
python -m itpeval.learning.replay ./my-run/episodes.jsonl --lock "$LOCK" \
  --receipt ./replayed.json --export ./repairs.jsonl --view repair
```

## Evaluate candidates in a batch

Write the candidate to `edit.txt`, including any spaces or newlines required by the task. The completion pipeline checks this exact text under the lock. Use a configured `--model` in place of `--candidate` to generate the text before checking it. [Model provider setup](../../benchmarks/translation.md#quick-start)

```bash
# Use the candidate from disk as the proposed edit.
LOCK=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')
python -m eval.pipeline.completion "$LOCK" results.jsonl --candidate edit.txt
```

Use the local batch queue to submit and collect a prerecorded candidate against the same lock. To check saved model outputs later, generate with `--generate-only` and run `verify_generated` against that file.

```bash
# Submit and collect using the same locked proof task.
LOCK=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')
python -m eval.pipeline.translation.batch_run submit --completion-lock "$LOCK" \
  --candidate edit.txt --job-file ./job.json
python -m eval.pipeline.translation.batch_run collect ./job.json --completion-lock "$LOCK" \
  --output ./batch-verified.jsonl
python -m eval.pipeline.completion "$LOCK" ./generated.jsonl --candidate edit.txt --generate-only
python -m eval.pipeline.translation.verify_generated ./generated.jsonl --completion-lock "$LOCK" \
  --output-dir ./verified
```

The results have a sibling run manifest identifying the task, environment, prompt, generation settings and budget. A verification checkpoint also records the generated input. Resume a run with the same manifest and use a new output path for a changed configuration.

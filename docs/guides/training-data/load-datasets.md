# Load datasets in Hugging Face

Install the loader with `python -m pip install -e '.[training]'`. This example uses the accepted edits from the training export. [Export a training dataset](export-a-dataset.md)

## Load accepted proofs

```python
from datasets import load_dataset

# Load accepted proof edits. Each row contains an input prompt and a completion.
proof_edits = load_dataset("parquet", data_files="build/training-native/sft.parquet", split="train")
print(proof_edits.column_names)
```

Use the `"json"` loader for `sft.jsonl`. For a large Parquet export, add `streaming=True` to read it incrementally. If you exported separate data splits, pass a mapping of split name to file paths as `data_files`. The loader's default split name does not assign a held-out set. [Load local files and splits](https://huggingface.co/docs/datasets/loading)

For a single file, `itpeval.learning.huggingface.load_export(path)` selects the same loader from its extension.

## Attach verifier rewards for GRPO

For online GRPO, export prompts directly from prepared locks. Each prompt has a task ID, and the manifest associates it with the native checker, theorem, and dependencies.

```bash
# Save the path to the Metamath exercise's prepared environment.
lock=$(itpeval prepare metamath --cache build/training-cache |
    python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
itpeval training-data native --lock "$lock" --output build/grpo-prompts
```

```python
from pathlib import Path

from datasets import load_dataset
from itpeval.learning.huggingface import VerifierReward

directory = Path("build/grpo-prompts")
prompts = load_dataset("json", data_files=str(directory / "grpo.jsonl"), split="train")
# Bind the prompt IDs to the theorem and native checker for each row.
reward = VerifierReward.from_manifest(directory / "manifest.json")
```

Pass `prompts` as `train_dataset` and `reward` as `reward_funcs` when creating a `GRPOTrainer`. Retain the `task_id` column so each generation reaches its checker. For an export that combines live locks and archived episodes, filter the prompt rows to task IDs in `reward.tasks` for your online run. [Try the local GRPO example](../verification-and-learning/verifier-rewards.md#train-with-the-verifier) · [TRL custom rewards](https://huggingface.co/docs/trl/grpo_trainer#using-a-custom-reward-function)

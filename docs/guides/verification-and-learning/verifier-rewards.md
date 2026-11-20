# Train with verifier rewards

## Train with the verifier

`itpeval.learning.views` provides `repair_rows` for failed and corrected edits and `trajectory_rows` for the full sequence. To reproduce a batch from `sample_tasks(tasks, count=..., seed=...)`, save the selected task IDs and seed. [Load the exported rows](../training-data/load-datasets.md)

`itpeval.learning.huggingface.VerifierReward({task.task_id: (task, prepared)}, record=save_attempt)` verifies TRL text or assistant-message completions using each row's `task_id`. The optional sink records raw responses, submitted candidates, outcomes, and rewards. An online generator failure records the exception and a null reward. Exclude null rewards from scored updates. Native replay requires a submitted candidate.

Install the `grpo` extra to run one CPU optimizer step on a local 20,224-parameter GPT-2 model. A deterministic sampler supplies two Metamath candidate sequences and computes their token log probabilities from the model. The native verifier scores them, and TRL updates the model using their rewards. The receipt records the parameter change, dependency versions, generation and checker budgets, and per-attempt evidence.

```bash
# Run the small trainer example with the local verifier as its reward source.
python -m pip install '.[grpo]'
OMP_NUM_THREADS=1 HF_HUB_OFFLINE=1 python -m itpeval.learning.grpo_example \
  --prefix "${ITPEVAL_PREFIX:-$HOME/.local/share/itpeval/toolchains/current}" --cache ./cache --output ./grpo-run
```

[Example trainer outputs](../../../benchmarks/runtime/evidence/metamath/grpo/trainer.json)

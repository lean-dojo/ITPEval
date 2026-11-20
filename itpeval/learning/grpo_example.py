"""One CPU GRPO step with a local tiny model and two native Metamath rewards."""

import argparse
from importlib.metadata import version
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.learning.episodes import task_prompt
from itpeval.learning.huggingface import VerifierReward


def train_one_step(prepared, output: Path):
    import torch
    from datasets import Dataset
    from tokenizers import Tokenizer
    from tokenizers.models import WordLevel
    from tokenizers.pre_tokenizers import WhitespaceSplit
    from transformers import GPT2Config, GPT2LMHeadModel, PreTrainedTokenizerFast
    from trl import GRPOConfig, GRPOTrainer

    task = build_task(prepared)
    if task.prover != "metamath":
        raise ValueError("this small whitespace-tokenized training fixture uses Metamath")
    torch.manual_seed(42)
    prompt = task_prompt(task)
    alternatives = task.allowed_edits[:2]
    words = sorted(set(" ".join((prompt, *alternatives)).split()))
    vocab = {token: i for i, token in enumerate(["[PAD]", "[UNK]", "[EOS]", *words])}
    base = Tokenizer(WordLevel(vocab, unk_token="[UNK]"))
    base.pre_tokenizer = WhitespaceSplit()
    tokenizer = PreTrainedTokenizerFast(tokenizer_object=base, pad_token="[PAD]", unk_token="[UNK]",
                                        eos_token="[EOS]", model_max_length=1024)
    model = GPT2LMHeadModel(GPT2Config(vocab_size=len(tokenizer), n_layer=1, n_head=1, n_embd=16,
                                       n_positions=1024, bos_token_id=2, eos_token_id=2, pad_token_id=0))
    dataset = Dataset.from_list([{"prompt": prompt, "task_id": task.task_id}])

    def recorded_rollout(prompts, trainer):
        # A deterministic sampler makes both kinds of native feedback observable.
        # Compute the sampling model's token log probabilities for the supplied edits.
        prefixes, completions, logprobs = [], [], []
        for i, text in enumerate(prompts):
            prefix = tokenizer.encode(text, add_special_tokens=False)
            tokens = tokenizer.encode(alternatives[i % len(alternatives)], add_special_tokens=False)
            with torch.no_grad():
                ids = torch.tensor([prefix + tokens], device=trainer.accelerator.device)
                logits = trainer.model(ids).logits[0, len(prefix) - 1:-1]
                logps = logits.log_softmax(dim=-1).gather(1, ids[0, len(prefix):, None])
            prefixes.append(prefix)
            completions.append(tokens)
            logprobs.append(logps.flatten().tolist())
        return {"prompt_ids": prefixes, "completion_ids": completions, "logprobs": logprobs}

    attempts = []
    native = VerifierReward({task.task_id: (task, prepared)}, record=attempts.append)
    output.mkdir(parents=True, exist_ok=True)
    args = GRPOConfig(output_dir=str(output / "trainer"), max_steps=1, per_device_train_batch_size=2,
                      num_generations=2, max_completion_length=16, use_cpu=True, fp16=False, bf16=False,
                      gradient_checkpointing=False, report_to=[], save_strategy="no", disable_tqdm=True,
                      remove_unused_columns=False, seed=42)
    trainer = GRPOTrainer(model=model, args=args, train_dataset=dataset, processing_class=tokenizer,
                          reward_funcs=native, rollout_func=recorded_rollout)
    weights = model.transformer.wte.weight.detach().clone()
    result = trainer.train()
    rewards = [row["reward"] for row in attempts]
    delta = float((weights - model.transformer.wte.weight.detach()).abs().max())
    report = {"schema_version": 1, "task_id": task.task_id, "environment_id": prepared.environment_id,
              "trainer": "GRPOTrainer", "sampling": "prerecorded_candidates", "seed": 42,
              "versions": {name: version(name) for name in ("trl", "transformers", "datasets", "accelerate", "tokenizers", "torch")},
              "device": str(trainer.accelerator.device), "optimizer": args.optim.value,
              "learning_rate": args.learning_rate, "model_parameters": model.num_parameters(),
              "budgets": {"training_steps": args.max_steps, "examples_per_device": args.per_device_train_batch_size,
                          "generations_per_prompt": args.num_generations, "max_completion_tokens": args.max_completion_length,
                          "checker": task.budgets.to_dict()},
              "steps": result.global_step, "rewards": rewards, "max_embedding_update": delta}
    jsonl(output / "trainer-attempts.jsonl", attempts)
    jsonl(output / "trainer.json", [report])
    if result.global_step != 1 or sorted(rewards) != [0.0, 1.0] or not delta > 0:
        raise RuntimeError(f"expected one parameter update using accepted and rejected proofs; inspect {output}")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    project = prepare_project("metamath", curated_project("metamath"), prefix=args.prefix, cache=args.cache)
    print(train_one_step(project, args.output))

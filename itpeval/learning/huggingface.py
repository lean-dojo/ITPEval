"""Dataset loading and a native reward function for Hugging Face trainers."""

from collections.abc import Callable, Mapping, Sequence
import json
from pathlib import Path

from itpeval.core.types import TaskSpec
from itpeval.environments import PreparedProject
from itpeval.learning.rewards import proof_reward
from itpeval.verification.service import verify


def load_export(path: Path):
    """Load an ITPEval JSONL or Parquet view as a Hugging Face Dataset."""
    from datasets import Dataset

    if Path(path).suffix.lower() == ".parquet":
        return Dataset.from_parquet(str(path))
    return Dataset.from_json(str(path))


class VerifierReward:
    """TRL-compatible reward callback using caller-selected native tasks and environments.

    Supply the dataset's task_id column to the trainer. A completion can be plain text
    or one assistant message. Infrastructure failures have a None reward and the
    optional sink receives every raw response, extracted candidate and native result.
    """

    def __init__(self, tasks: Mapping[str, tuple[TaskSpec, PreparedProject]], *,
                 record: Callable[[dict], None] | None = None,
                 extract: Callable[[str], str] | None = None):
        self.tasks = dict(tasks)
        self.record = record
        self.extract = extract
        for ident, (task, prepared) in self.tasks.items():
            if task.task_id != ident or task.environment_id != prepared.environment_id or task.prover != prepared.spec.prover:
                raise ValueError("reward configuration requires exact task and environment identities")
            if task.operation != "proof_completion":
                raise ValueError("verifier rewards require proof completion tasks")
        self.__name__ = "itpeval_proof_reward"

    @classmethod
    def from_manifest(cls, path: Path, **kwargs) -> "VerifierReward":
        """Load the local task locks recorded by a training export."""
        from itpeval.backends.projects import build_task
        from itpeval.environments import load_project

        manifest = json.loads(Path(path).read_bytes())
        bindings = manifest.get("runtime_tasks")
        if manifest.get("schema_version") != 1 or not bindings:
            raise ValueError("export GRPO prompts with --lock to record local task bindings")
        tasks = {}
        for task_id, binding in bindings.items():
            prepared = load_project(Path(binding["lock_path"]))
            task = build_task(prepared, binding["manifest_path"])
            if (binding["environment_id"], binding["prover"]) != (task.environment_id, task.prover):
                raise ValueError(f"GRPO export does not match its local task: {task_id}")
            tasks[task_id] = task, prepared
        return cls(tasks, **kwargs)

    def __call__(self, completions: Sequence, task_id: Sequence[str], **kwargs) -> list[float | None]:
        if len(completions) != len(task_id):
            raise ValueError("each completion requires its own dataset task_id")
        pairs = []
        for completion, ident in zip(completions, task_id):
            if ident not in self.tasks:
                raise ValueError(f"unknown task_id in reward batch: {ident!r}")
            if isinstance(completion, str):
                raw = completion
            elif (isinstance(completion, list) and len(completion) == 1
                  and isinstance(completion[0], dict) and completion[0].get("role") == "assistant"
                  and isinstance(completion[0].get("content"), str)):
                raw = completion[0]["content"]
            else:
                raise ValueError("expected completion text or one assistant response")
            pairs.append((ident, raw, self.extract(raw) if self.extract else raw))
        rewards = []
        for ident, raw, candidate in pairs:
            task, prepared = self.tasks[ident]
            checked = verify(task, candidate, prepared=prepared)
            reward = proof_reward(task, checked)
            if self.record is not None:
                self.record({"task_id": ident, "environment_id": task.environment_id,
                             "raw_response": raw, "candidate": candidate, "evidence": checked.to_dict(),
                             "reward": reward.value, "disposition": reward.disposition})
            rewards.append(reward.value)
        return rewards

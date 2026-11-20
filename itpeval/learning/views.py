"""Sample versioned tasks and construct training rows from checked trajectories."""

from collections.abc import Iterable, Iterator
from heapq import nsmallest

from itpeval.core.episodes import Episode
from itpeval.core.records import digest
from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.learning.episodes import check_episode, task_prompt
from itpeval.learning.rewards import proof_reward


def sample_tasks(tasks: Iterable[TaskSpec], *, count: int, seed: int) -> tuple[TaskSpec, ...]:
    """Sample distinct task identities without replacement, independent of input order."""
    if type(count) is not int or count < 0 or type(seed) is not int:
        raise ValueError("task sampling requires a nonnegative count and integer seed")
    by_id = {task.task_id: task for task in tasks}
    if count > len(by_id):
        raise ValueError("the requested sample exceeds the number of distinct tasks")
    return tuple(by_id[key] for key in nsmallest(count, by_id, key=lambda key: (digest([seed, key]), key)))


def trajectory_rows(episodes: Iterable[Episode]) -> Iterator[dict]:
    """Yield action, observation and verifier reward in the order they occurred."""
    for episode in episodes:
        task = TaskSpec.from_dict(episode.task)
        check_episode(episode, task)
        for index, transition in enumerate(episode.transitions):
            evidence = VerificationEvidence.from_dict(transition.evidence)
            reward = proof_reward(task, evidence)
            yield {"schema_version": 1, "task_id": task.task_id, "environment_id": task.environment_id,
                   "run_id": episode.run_id, "step": index, "action": transition.action.to_dict(),
                   "observation": transition.observation.to_dict(), "evidence": evidence.to_dict(),
                   "reward": reward.value, "disposition": reward.disposition}


def repair_rows(episodes: Iterable[Episode]) -> Iterator[dict]:
    """Use the previous failed edit and its feedback as input to the next correction."""
    for episode in episodes:
        task = TaskSpec.from_dict(episode.task)
        previous = None
        for current in trajectory_rows((episode,)):
            if previous and previous["reward"] == 0 and current["reward"] == 1:
                yield {"schema_version": 1, "task_id": task.task_id, "environment_id": task.environment_id,
                       "run_id": episode.run_id, "prompt": task_prompt(task),
                       "failed_candidate": previous["action"]["candidate"], "feedback": previous["observation"],
                       "completion": current["action"]["candidate"], "step": current["step"]}
            previous = current

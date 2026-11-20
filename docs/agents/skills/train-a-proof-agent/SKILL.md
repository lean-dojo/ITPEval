---
name: train-a-proof-agent
description: Collect and replay ITPEval agent episodes, turn repairs into supervised examples, or connect native verification rewards to a trainer.
---

# Train a proof agent

Run from an ITPEval checkout. For an installed copy of this skill, resolve the guide links from `docs/agents/skills/train-a-proof-agent/SKILL.md` in that checkout.

## Collect and replay attempts

Start from a locked task with an attempt budget. For a JSON array of proof fragments, run `python -m itpeval.learning.example --lock LOCK --candidates FILE --cache CACHE --output RUN`. For a policy that proposes edits from feedback, call `rollout` with a generator callback. Save the raw response, submitted edit, checker feedback, and final artifact. [Replay a list of edits](../../../guides/verification-and-learning/check-and-replay.md#save-and-replay-an-episode) · [Write a policy callback](../../../guides/verification-and-learning/search-with-an-agent.md#run-a-local-search-agent)

When the task needs native proof states and actions, use `rollout_native` and retain the state before each attempt. Replay saved episodes under the original lock before exporting. [Use native goals in an agent](../../../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

## Export or train

Use `itpeval training-data native --episodes FILE --output DIRECTORY` for proof-edit episodes or `--native-episodes FILE` for goal and action episodes. Choose `repair` for failed edits paired with accepted revisions, `trajectory` for ordered proof-edit attempts, or `proof_steps` for native state and action rows. Check the export manifest for view counts. [Export training data](../../../guides/training-data/export-a-dataset.md)

Use the native verifier reward for online training. A completed proof scores one and a definitive failure scores zero. Keep infrastructure failures in run accounting with a null reward. For a real optimizer step, run the Metamath GRPO example and inspect its parameter-change receipt. [Train with verifier rewards](../../../guides/verification-and-learning/verifier-rewards.md#train-with-the-verifier)

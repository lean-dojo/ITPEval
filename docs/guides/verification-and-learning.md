# Proof repair and agent training

An agent proposes a proof, reads the native checker feedback, and can revise its next attempt. The episode records the full run.

<span id="the-proof-environment"></span>

| Part of the loop | What ITPEval records |
|---|---|
| Starting state | The theorem, editable proof region, and locked project and libraries |
| Action | The proposed proof fragment or native proof action |
| Observation | A checker verdict and diagnostics, or a new native proof state |
| Reward | `1` for a checked completion, `0` for a definitive failed candidate, and null for an unknown outcome |
| Episode end | Success, an exhausted budget, or an execution failure |

## Chapters

- <span id="check-one-candidate"></span><span id="save-and-replay-an-episode"></span><span id="evaluate-candidates-in-a-batch"></span>[Check and replay proof attempts](verification-and-learning/check-and-replay.md)
  Try a Metamath proof, save the attempts and recheck them under the same project lock.
- <span id="search-over-proof-edits"></span><span id="run-a-local-search-agent"></span><span id="search-with-native-proof-information"></span><span id="use-native-goals-in-an-agent"></span>[Write a proof-search agent](verification-and-learning/search-with-an-agent.md)
  Build a proof-edit policy or step through a native goal, then record the checker feedback.
- <span id="train-with-the-verifier"></span>[Train with verifier rewards](verification-and-learning/verifier-rewards.md)
  Score candidates with the native checker and run a small GRPO training example.

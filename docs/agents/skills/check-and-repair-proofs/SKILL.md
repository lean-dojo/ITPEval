---
name: check-and-repair-proofs
description: Check an existing native file or evaluate candidate proofs against a fixed ITPEval task. Use for native checker diagnostics, proof repair and replay.
---

# Check and repair proofs

Run from an ITPEval checkout. For an installed copy of this skill, resolve the guide links from `docs/agents/skills/check-and-repair-proofs/SKILL.md` in that checkout.

## Check an existing file

Run `itpeval eval --prover PROVER --file FILE` for a standalone source file. For a file that resolves imports or companion files by path, use the supported native layout and `--task-dir DIR --task-file FILE`. Report the native diagnostic and say whether the checker ran. [Check an existing file](../../../guides/work-with-a-library.md#check-a-file-you-already-have)

## Repair a locked theorem

1. Prepare the project with `itpeval prepare PROVER --project DIR --cache CACHE`. Read the completion manifest to identify the target, permitted edits, assumptions, and obligations. Keep the source outside the proof slot fixed. [Task manifest format](../../../reference/task-manifests.md)
2. Run `itpeval verify-task --lock LOCK --candidate-file FILE` with a proof fragment or certificate. For an inline proof, `--document-file FILE` accepts a full revised entrypoint. Add `--manifest MANIFEST` when the task uses a manifest other than `completion.json`.
3. Read `checker_outcome`, `task_success`, and `obligations`. Use the diagnostics to revise the permitted fragment. Replay the successful candidate under the same lock. Record a timeout or unavailable toolchain as an unknown result. [Check and replay an attempt](../../../guides/verification-and-learning/check-and-replay.md)

## Use automated search when the goal is supported

Use `itpeval atp hammer --lock LOCK` for Isabelle/HOL. For supported Lean or Rocq goals, use `itpeval atp lean-horn --lock LOCK --auto` or `itpeval atp rocq-horn --lock LOCK --auto`. Replace `--auto` with `--problem FILE` to supply an explicit premise map. Add `--output FILE` to keep the search receipt and `--episodes-output FILE` to export the native replay as an episode. Use the replay verdict to establish success. [Prover bridges](../../../guides/automated-proving/prover-bridges.md)

Check capabilities before requesting native goal or tactic APIs. In HOL4 or HOL Light, pass a pending branch's `goal_path` to `driver.suggest_atp` and apply checked progress with `driver.apply_atp(suggestion)` at the same revision. For external search, HOL4 also accepts `solver="e"` or `solver="vampire"`. Verify the completed proof after closing all branches. [Capabilities](../../../reference/capabilities.md) · [Search one HOL subgoal](../../../guides/automated-proving/search-a-proof-state.md#search-one-hol-subgoal)

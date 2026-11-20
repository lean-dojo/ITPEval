# Proof search and agent APIs

## Ask an automated prover for help

`itpeval.atp.solve_tptp(problem, solver="e")` runs E on a TPTP input. Pass `solver="vampire"` for Vampire or `executable=Path(...)` to select a local solver build. Use `prepare_solver(name, executable=...)` to reuse a discovered build across calls. [Standalone TPTP search](../../guides/automated-proving/run-a-solver.md#solve-a-tptp-problem)

For a live proof, use `driver.suggest_atp()` and apply the checked suggestion with `driver.apply_atp(suggestion)` at the same revision. [Supported goals and proof-state examples](../../guides/automated-proving/search-a-proof-state.md)

For one-off calls from a reviewed task, see the Sledgehammer and Horn search functions. Use `episode_from_search(task, receipt)` from `itpeval.learning.assisted` for supported Isabelle, Lean, and Rocq receipts. [Prover bridges](../../guides/automated-proving/prover-bridges.md)

## Record and replay agent actions

Use `rollout` for full proof edits and `rollout_native` for individual proof actions. The callback receives previous attempts and feedback. Use `replay` or `replay_native_episode` to rerun a saved episode with its locked task. [Write a proof-search agent](../../guides/verification-and-learning/search-with-an-agent.md)

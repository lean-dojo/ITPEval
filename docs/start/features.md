# Features

Bring a proof, a library, or a collection of attempts. ITPEval gives you a Python and command-line interface to the native tools. For a first run, start with one small proof. [Quickstart](quickstart.md)

## Check and write proofs

- **Check a source file.** Run its native checker. Keep the project layout when the file has local imports or build files. [Check your own file](../guides/work-with-a-library.md#check-a-file-you-already-have)
- **Repair a proof.** Prepare a project and hold the theorem, imports, and allowed assumptions fixed as you try revisions to its proof. Save the attempts and replay them under the same lock. [Check a candidate](../guides/verification-and-learning/check-and-replay.md)
- **Build a proof agent.** Read native feedback and record a rollout as the agent submits tactics, commands, terms, or document edits. The available actions vary by prover. [Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

## Search, branch, and replay

- **Run a standalone solver.** Give a TPTP problem to local E or Vampire and keep its answer and any returned proof or model. [Run a solver on TPTP](../guides/automated-proving/run-a-solver.md)
- **Search during a proof.** Try automated search on reviewed tasks in all ten built-in provers. E and Vampire can search supported goals in Lean 4, Rocq, Isabelle/HOL, HOL4, Agda, and PVS. The original prover checks the completed proof. [Use a prover bridge](../guides/automated-proving/prover-bridges.md)
- **Save your place.** Save a document revision or action checkpoint and reopen it later. Try alternate proof branches where supported, then replay the winning route into a training episode. [Branch and replay](../guides/automated-proving/branch-and-replay.md)

## Extract libraries and train models

- **Extract a library.** Export declarations, source locations, and the premises visible at a theorem. Check the report for coverage and which proof references the backend recovered. [Extract a library](../guides/extract-and-build-a-dataset/extract-a-library.md)
- **Combine libraries.** Put extracts from different provers into one collection while keeping their library names, revisions, source locations, and environment IDs. [Combine libraries across provers](../guides/extract-and-build-a-dataset/combine-libraries.md)
- **Export training rows.** Write JSONL or Parquet for continued pretraining, supervised fine-tuning, proof repair, paired preferences, unpaired preferences, online GRPO, offline trajectories, native proof steps, or premise retrieval. [Choose a training dataset](../guides/training-data/choose-a-view.md)
- **Score new attempts.** Use the native verifier as a reward function for the task in your trainer. [Train with verifier rewards](../guides/verification-and-learning/verifier-rewards.md)

## Formalize, explain, and translate

- **Go between English and a formal statement.** Use your configured model for autoformalization or auto-informalization. The released round trips use Lean 4 alone or Lean 4, Rocq, Isabelle/HOL, and HOL Light together. [Formalization and round-trip evaluation](../guides/formalization-and-translation.md)
- **Translate between provers.** The released benchmark covers statement translation across ten provers and proof translation across four. [Translation benchmark](../benchmarks/translation.md#dataset-scope)
- **Compare Lean statements.** Try to prove both directions between a generated statement and a reference within a fixed budget. [Semantic equivalence in Lean](../guides/formalization-and-translation.md#semantic-equivalence-in-lean)

## Run larger jobs and add a prover

- **Check a batch.** Schedule independent checks across workers and bound time and memory. [Schedule proof checks](../runtime/execution/scheduling.md)
- **Reuse work.** Cache exact repeat verdicts for the same locked task and reuse compiled dependencies or initialized workers where supported. [Reuse check and dependency results](../runtime/execution/cache.md)
- **Add a prover.** Start with its native file checker. Add fixed-target certificate verification or extraction when the prover exposes the required evidence. [Add a prover backend](../reference/extending-a-backend.md)
- **Give your agent a workflow.** Use a repository skill for prover integration, translation, repair, extraction, or training. [Agent skills](../agents/index.md)

Check which operations have native tests for your prover. [Backend capabilities](../reference/capabilities.md)

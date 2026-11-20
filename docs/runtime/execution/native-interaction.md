# Native proof sessions

<span id="native-interaction"></span>

Use `require_capabilities(prover, operations)` to check what a prover exposes. `get_backend(prover).open_native_session(task, prepared=project)` opens the native API. Each session has a `handle` and an `inspect(handle)` method.

`NativeProofDriver` provides a common loop for applying native actions and saving portable checkpoints. The ten-prover example compares the replayed goal sequence and independently checks the final proof. [Agent example](../../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent) · [Replay results](../../../benchmarks/runtime/native-proof-driver.json)

ACL2, Lean, Metamath, PVS, and Rocq replay a saved action prefix in one native process and compare every state. [Checkpoint timings](../measurements/proof-sessions.md)

`branch = driver.fork()` lets you try another action from the same goal. Lean and Rocq copy the goal and committed candidate in memory. The next action runs natively, and each completed branch can call `branch.finalize()` to check its candidate against the locked target. [Lean and Rocq branch timings](../measurements/proof-sessions.md#fork-a-lean-or-rocq-proof-session)

`LeanTacticSession.step(handle, tactic)` reconstructs the current revision and submits the new one to Lean’s language server. It returns the goal and diagnostics for both document versions.

Agda’s `case_split` returns proposed clauses for the hole while preserving the task target and arguments. `MetamathStackReplay` reads accepted extraction traces by declaration ID and exposes each instruction’s stack height and top expression.

| Prover | Native view | How you use it |
|---|---|---|
| ACL2 | `ACL2ProofBuilderSession.inspect(handle)` | Read the focused goal and hypotheses, apply a supported proof-builder instruction with `step`, and replay the resulting instructions with `finalize`. |
| Agda | `AgdaHoleSession.goal_context(handle)` | Read the expected type, typed local bindings, and source range. Fill the hole with `give` or inspect the clauses returned by `case_split`. |
| HOL4 and HOL Light | `HOLProofSession.inspect(handle)` | See pending subgoal paths. Apply a tactic to a selected path, fork the tactic tree, or save a checkpoint. |
| Isabelle/HOL | `IsabelleProofSession.inspect(handle)` | Read the original Isar goal. Use `step` with an authorized proof fragment to see the states after standalone parenthesized `apply` commands. The stock session uses an installed parent heap. |
| Lean 4 | `LeanTacticSession.inspect(handle)` | Read Lean’s tactic state at the proof slot. Use `step` to submit a reviewed tactic. |
| Metamath | `MetamathProofSession.inspect(handle)` | Read open numbered proof steps, use `assign` with a permitted label, and check the resulting proof independently with `finalize`. |
| Mizar | `MizarArticleSession.inspect(handle)` | Read the verifier’s thesis progression and source diagnostics. `step` replaces the reviewed proof fragment, and `submit_document` takes the whole article. |
| PVS | `PVSProofSession.inspect(handle)` | Read the focused sequent and apply reviewed native commands. Fork or restore the command prefix before exploring another continuation. |
| Rocq | `RocqIDESession.inspect(handle)` | Read focused, background, shelved, and given-up goals using stock `coqidetop`. Use `step` with a reviewed tactic sentence, then replay the accepted sentences with `finalize`. Pétanque also supports branching over native states. |

```bash
# Exercise these native APIs on the examples and save their evidence.
python -m benchmarks.runtime.native_depth --prefix "$ITPEVAL_PREFIX" \
  --cache build/native-proof-cache --output build/native-proof-feedback.json
```

The runner saves native feedback from the bundled examples. [Ten-prover feedback](../../../benchmarks/runtime/evidence/native-depth.json)

Run the interaction regression to reproduce the Agda Boolean split and Lean goal transition.

```sh
# Collect the interactions exposed by the installed backends.
PYTHONPATH=. python benchmarks/runtime/interaction.py --prefix "${ITPEVAL_PREFIX:-$HOME/.local/share/itpeval/toolchains/current}" \
    --cache build/native-interactions/cache --output build/native-interactions/evidence \
    --report build/native-interactions/qualification.jsonl
```

Mizar retains unsuccessful revisions with thesis coordinates and native errors so you can repair them. Finalization checks the selected revision. [Mizar diagnostics](../../../benchmarks/runtime/evidence/mizar/native-interaction.json)

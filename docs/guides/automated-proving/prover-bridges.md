# Use a prover bridge

## Search and replay in Isabelle

Sledgehammer searches the original goal with an Isabelle solver component. The bridge uses `process_theories`, introduced in Isabelle2025-1. The example uses Isabelle2026. [Isabelle release notes](https://isabelle.in.tum.de/website-Isabelle2025-1/dist/Isabelle2025-1/doc/NEWS.html)

```bash
# Ask E for proof text, then run the normal native proof verifier.
itpeval atp hammer --demo --solver e --output build/isabelle-hammer.json
```

Read `search_outcome` for the solver result and `evidence.task_success` for each suggestion's replay under the task's assumptions and obligations.

`premise_pools` lists the candidate facts Sledgehammer printed for each selection method. Search and replay can use subsets of these facts. Use `--no-trace-premises` to skip collecting the pools.

For your own theorem, prepare the sources, session `ROOT`, and completion manifest. Pass `--lock PATH` to use the locked Isabelle components. [Define a proof task](../../reference/task-manifests.md)

Set `--timeout-s` for the supervised search deadline, `--solver-timeout-s` for the solver’s own limit, and `--replay-limit` for the number of suggestions checked. Each replay uses the task’s resource budget.

## Search and replay in Lean

A ready and permitted item is delivered, and delivery implies completion. Each Horn rule lists its premises. A fact has none. [Lean theorem](../../../itpeval/tests/fixtures/projects/lean4/horn/Delivery.lean) · [Horn input](../../../itpeval/tests/fixtures/projects/lean4/horn/horn.json)

```bash
# Run E and keep both the search receipt and the native proof attempt.
itpeval atp lean-horn --demo --auto --solver e \
  --output build/lean-horn.json --episodes-output build/lean-horn-episodes.jsonl
```

With `--auto`, Lean elaborates the file at the locked tactic slot. Discovery covers a single ground goal, named propositions, flat applications such as `ready item`, and nondependent implication chains. The receipt keeps the goal’s byte offset and any skipped propositions.

The bridge maps ground propositions to TPTP atoms and reconstructs a proof from the solver's named hypotheses. The receipt keeps the problem, hypotheses used in search and reconstruction, and Lean's verdict in the original project. [Native discovery and replay results](../../../benchmarks/runtime/lean-horn-auto.json)

Use `--lock PATH --auto` with default checker options, prebuilt imports, and a reviewed tactic slot on an indented line. For an explicit map, pass `--problem PATH` or omit both flags to load `horn.json`. Tests used Lean 4.36.0, E 3.5.10, and Vampire 5.1.0. Use `--executable PATH` for a Vampire build that reports input clause names. [Vampire release](https://github.com/vprover/vampire/releases/tag/v5.1.0)

If a recovered fragment falls outside the edit policy, the receipt puts it in `candidate` and reports `outside_task_policy`. Review the fragment before adding it to `allowed_edits`, then prepare the updated project and run the check. [Proof task manifests](../../reference/task-manifests.md)

## Search and replay in Rocq

With `--auto`, RocqIDE supplies the focused goal and local hypotheses. The bridge reconstructs typed `assert` steps for Rocq to check. E 3.5.10 and Vampire 5.1.0 produced accepted proofs with Rocq 9.3.0. [Native solver results](../../../benchmarks/runtime/rocq-horn-auto.json)

```bash
# Run the Rocq demo and keep the replay in the same format as the Lean episode.
itpeval atp rocq-horn --demo --auto --solver e \
  --output build/rocq-horn.json --episodes-output build/rocq-horn-episodes.jsonl
```

Use `--lock PATH --auto` for a reviewed proof slot with prebuilt imports. Discovery supports named local propositions and nondependent implication chains, and records skipped propositions. To supply a map, omit `--auto` to load `horn.json` or pass `--problem PATH`. A mismapped hypothesis can yield a solver theorem and a Rocq rejection. [Rocq theorem](../../../itpeval/tests/fixtures/projects/rocq/horn/Delivery.v) · [Hypothesis map](../../../itpeval/tests/fixtures/projects/rocq/horn/horn.json)

## Search Agda and PVS goals with E or Vampire

Agda exports one typed hole with a named local `Set` type or flat application such as `Complete item`. Premises include local inhabitants and nondependent implications between supported types. The bridge records omitted bindings and reconstructs a term from the certificate's named premises. Apply the checked term at the same revision. [Agda native results](../../../benchmarks/runtime/agda-horn.json)

PVS exports a focused sequent whose conclusion is a Boolean skolem, a fresh Boolean name introduced during the proof. It uses visible facts and implication chains between those names. A solver theorem lets the driver try the reviewed `(grind)` command. A remaining sibling yields `progress`. Acceptance requires a separate PVS check of the locked formula and its type-correctness conditions using the reviewed ProofLite fragment. [PVS guide](../../provers/pvs.md)

Agda defaults to Auto and PVS to reviewed native strategies. Pass `solver="e"` or `solver="vampire"` for external search and `executable=Path(...)` to select a build. Agda reconstruction needs a Vampire build that reports source clause labels, such as 5.1.0. `counter_satisfiable` applies to the exported Horn problem and selected premises.

## Use the Python API

- **Isabelle** `run_sledgehammer(task, prepared=project, solver="e")` keeps the search receipt and returns the accepted suggestion in `checked_proof` when replay succeeds.
- **Lean and Rocq** `observe_lean_horn` and `observe_rocq_horn` read the native goal. `run_horn_search` and `run_rocq_horn_search` use the discovered scope or accept an explicit `LeanHornProblem` or `RocqHornProblem`.
- **Agda** `observe_agda_horn` and `run_agda_horn_search` in `itpeval.atp.agda` expose the typed context and external search with replay.
- **PVS** Use the proof driver to focus a sequent and call `suggest_atp` with an external solver.

Pass a solver from `prepare_solver` to reuse its discovered build. [Python reference](../../reference/python/proof-agents.md#ask-an-automated-prover-for-help)

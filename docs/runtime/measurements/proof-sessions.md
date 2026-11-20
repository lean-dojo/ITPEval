# Interactive proof benchmarks

## Restore a PVS action checkpoint

A saved PVS proof can replay its entire command history in one native process. In five paired trials on a five-command proof with two subgoals, median restore time fell from **2.42 s to 0.58 s**. Each restore reproduced all six observed states, including the initial goal. The restored theorem and its type-correctness condition passed an independent check. [Timing and state identities](../../../benchmarks/runtime/pvs-action-restore.json) · [PVS proof walkthrough](../hol-and-pvs-interaction.md#branch-and-restore-a-pvs-proof)

## Restore ACL2, Metamath, and Rocq checkpoints

Medians cover five paired trials. Both restore methods reproduced the initial state and every action state. Fresh native checks accepted the restored candidates.

| Prover | Actions | Per-action restore | Single-transaction restore |
| --- | ---: | ---: | ---: |
| ACL2 | 3 | 1.486 s | 0.350 s |
| Metamath | 3 | 0.185 s | 0.048 s |
| Rocq | 11 | 3.013 s | 0.317 s |

The ACL2 and Metamath examples go from four interactive prover launches to one. Rocq goes from twelve RocqIDE launches to one, with one separate compiler call in both cases to locate source spans. [ACL2 and Metamath timing records](../../../benchmarks/runtime/acl2-metamath-action-restore.json) · [Rocq timing record](../../../benchmarks/runtime/rocq-action-restore.json)

## Restore a Lean tactic checkpoint

One Lean language-server transaction can check all saved revisions. On a ten-tactic proof, median restore time across five paired trials fell from **8.21 s to 2.62 s**. All eleven native goal states matched, including the initial state. A fresh check accepted every completed candidate and reported no axioms. [Lean timing record](../../../benchmarks/runtime/lean-action-restore.json)

## Fork a Lean or Rocq proof session

Fork and replay start from the same observed goal and run the same native closing action. Medians cover five pairs, with alternating order on a shared host. [Trials and source hashes](../../../benchmarks/runtime/lean-rocq-forks.json)

| Prover | Saved actions | Replay checkpoint | Fork in memory | Replay and close | Fork and close |
| --- | ---: | ---: | ---: | ---: | ---: |
| Lean 4.36.0 | 9 | 2.419 s | 1.72 ms | 3.183 s | 0.766 s |
| Rocq 9.3.0 | 10 | 0.335 s | 2.11 ms | 0.602 s | 0.266 s |

The fork saves one interactive transaction. Rocq also reuses the parser’s source positions. Starting and closing observations matched, while every parent goal stayed open. All 20 fresh strict checks accepted the same artifact within each prover. Timing starts at the saved prefix and stops before the separate strict check. [Native session workflow](../execution/native-interaction.md#native-interaction)

From the repository root, point `ITPEVAL_PREFIX` at an installation containing Lean and Rocq and run the paired comparison. [Benchmark runner](../../../benchmarks/runtime/lean_rocq_forks.py)

```bash
# Compare the two branch methods five times on the same proof prefix.
python -m benchmarks.runtime.lean_rocq_forks --prefix "$ITPEVAL_PREFIX" \
  --cache build/native-fork-cache --trials 5 --output build/lean-rocq-forks.json
```

## Fork a Metamath search state

Metamath copies the observed parent state in memory and runs every assignment in the native Proof Assistant.

On the bundled two-hole goal, median search time fell from **0.745 s to 0.423 s** over five paired runs. Both methods tried the same six assignments, returned the same feedback and plan, and passed all ten independent strict checks. Proof Assistant launches fell from **13 to 6** per search. [Metamath timing record](../../../benchmarks/runtime/metamath-search-forks.json)

## Automated search and native replay

The Isabelle pilot compares a known proof, `by simp`, with Sledgehammer followed by native replay. Medians cover three trials in rotated order. All nine checks accepted the same proof. [Solver outcomes and timings](../../../benchmarks/runtime/atp-pilot.json) · [Runner](../../../benchmarks/runtime/atp.py)

| Workflow | Median wall time (s) |
| --- | ---: |
| Check the supplied proof | 9.97 |
| E search and Isabelle check | 20.75 |
| Vampire search and Isabelle check | 21.99 |

The same pilot also records standalone TPTP outcomes on three problems per solver, covering a theorem, a counterexample, and inconsistent axioms. [Run E or Vampire on your own goals](../../guides/automated-proving.md)

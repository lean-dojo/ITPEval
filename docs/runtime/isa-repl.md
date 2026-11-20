# Isabelle proof states

Stock `IsabelleProofSession` opens the goal in Isabelle2026. `step` accepts an authorized fragment and shows the goal after each standalone parenthesized `apply` line. `finalize` checks the locked target. The API uses `process_theories`, introduced in Isabelle2025-1. [Release notes](https://isabelle.in.tum.de/website-Isabelle2025-1/dist/Isabelle2025-1/doc/NEWS.html)

## Branch with Isa-REPL

The Isa-REPL example branches at goal `p` with locale assumption `premise: p`. It tries `by (rule premise)` and `by (fact premise)` from that same goal. Final verification checks the fragment in the complete locked artifact. [Example theorem](../provers/isabelle.md#proof-completion) · [Branch observations](../../benchmarks/runtime/evidence/isabelle/isa-repl.json)

The branch adapter is pinned to Isa-REPL 0.9.4 and the Isabelle2024 HOL heap. Stock `IsabelleProofSession` loads the installed parent heap named in the project’s `ROOT`. [Isabelle sessions](../provers/isabelle.md#libraries)

Use these revisions to match the Isabelle2024 heap’s ML solver and printer APIs.

```sh
# Pin both Isabelle integrations before collecting proof states.
python -m pip install '.[isabelle]'
mkdir -p integrations
git clone https://github.com/xqyww123/Isa-REPL.git integrations/isa_repl
git -C integrations/isa_repl checkout --detach 141083616134af3629ef07137ffe07f098ab8ee2
git clone https://github.com/xqyww123/auto_sledgehammer.git integrations/auto_sledgehammer
git -C integrations/auto_sledgehammer checkout --detach c226522e5744f7c3a06864789a475053c9dd93b6
PYTHONPATH=. python benchmarks/runtime/isa_repl.py --prefix "$ITPEVAL_PREFIX" \
    --cache ./cache --integrations ./integrations --output ./run/evidence --report ./run/qualification.jsonl
```

Register both directories in `prepare_project(..., toolchain_inputs=...)` as `isa_repl` and `auto_sledgehammer`. Call `itpeval.backends.isabelle.interaction.branch_trace(task, candidates, prepared=env)`. Each call gets a fresh loopback server, user directory and theory table. Checkpoints expire with that process, and the tested project imports theories already in the HOL heap. [Isa-REPL source](https://github.com/xqyww123/Isa-REPL/tree/141083616134af3629ef07137ffe07f098ab8ee2) · [Auto_Sledgehammer source](https://github.com/xqyww123/auto_sledgehammer/tree/c226522e5744f7c3a06864789a475053c9dd93b6)

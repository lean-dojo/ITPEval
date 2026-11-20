# Backend capabilities

All ten built-in provers can check native source, verify a fixed proof task, extract declarations and replay a sequence of edits. Check the second table before building an agent that needs individual tactics, goal states or proof branching.

**Tested** marks an operation with a passing native example in a recorded environment. **Experimental** marks an implementation awaiting a passing example in these reports. **Planned** marks an operation awaiting a public implementation. **N/A** means the operation does not apply.

For compatible library layouts and concrete imports, see [Provers and libraries](../provers/index.md).

The portable document checkpoint test forks a rejected edit and restores the accepted artifact in a fresh session. [Native results](../../benchmarks/runtime/document-checkpoints.jsonl) · [Fork and save a document](../runtime/execution/document-revisions.md#fork-and-save-a-document)

Native proof feedback can be a tactic goal, an interaction hole, or a thesis observed while checking a complete article. [Interfaces and native evidence](../runtime/execution/native-interaction.md#native-interaction)

## Documents, extraction and evaluation

| Feature | Availability by prover |
|---|---|
| `installed_package` | **Tested** · all ten provers |
| `check_artifact` | **Tested** · all ten provers |
| `proof_completion` | **Tested** · all ten provers |
| `fixed_context` | **Tested** · all ten provers |
| `edit_document` | **Tested** · all ten provers |
| `reset` | **Tested** · all ten provers |
| `fork_document` | **Tested** · all ten provers |
| `checkpoint_document` | **Tested** · all ten provers |
| `inspect_declarations` | **Tested** · all ten provers |
| `episode_replay` | **Tested** · all ten provers |
| `end_to_end` | **Tested** · all ten provers |
| `evaluation_parity` | **Tested** · all ten provers |

## Native interactions and semantic checking

| Feature | Availability by prover |
|---|---|
| `inspect_goals` | **Tested** · all ten provers |
| `step_proof` | **Tested** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [PVS](../provers/pvs.md)<br>**Planned** · [Agda](../provers/agda.md), [Mizar](../provers/mizar.md) |
| `refine_hole` | **Planned** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Tested** · [Agda](../provers/agda.md) |
| `case_split` | **Planned** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Tested** · [Agda](../provers/agda.md) |
| `replay_stack` | **N/A** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Tested** · [Metamath](../provers/metamath.md) |
| `proof_branching` | **Tested** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [PVS](../provers/pvs.md)<br>**Planned** · [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md) |
| `checkpoint_proof` | **Planned** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md)<br>**Tested** · [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [PVS](../provers/pvs.md) |
| `checkpoint_actions` | **Tested** · all ten provers |
| `warm_proof_session` | **Planned** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Tested** · [HOL Light](../provers/hol-light.md) |
| `automated_search` | **Tested** · all ten provers |
| `atp_from_state` | **Tested** · all ten provers |
| `external_atp_goal` | **Tested** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL4](../provers/hol4.md), [Agda](../provers/agda.md), [PVS](../provers/pvs.md)<br>**Planned** · [HOL Light](../provers/hol-light.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md) |
| `proof_portfolio` | **Tested** · [Lean 4](../provers/lean4.md), [Agda](../provers/agda.md), [PVS](../provers/pvs.md)<br>**Experimental** · [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md) |
| `snapshot` | **Planned** · all ten provers |
| `action_traces` | **Tested** · [Lean 4](../provers/lean4.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Planned** · [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md) |
| `bounded_equivalence` | **Tested** · [Lean 4](../provers/lean4.md)<br>**N/A** · [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md) |
| `article_errors` | **N/A** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [PVS](../provers/pvs.md)<br>**Tested** · [Mizar](../provers/mizar.md) |
| `replay_event` | **N/A** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Tested** · [ACL2](../provers/acl2.md) |
| `verify_base_database` | **N/A** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Tested** · [Metamath](../provers/metamath.md) |

## Extracted structural fields

| Feature | Availability by prover |
|---|---|
| `action_traces` | **Unavailable** · [Lean 4](../provers/lean4.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [Rocq](../provers/rocq.md)<br>**Reconstructed** · [Metamath](../provers/metamath.md) |
| `constraints` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [Agda](../provers/agda.md) |
| `context` | **Reconstructed** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [Metamath](../provers/metamath.md) |
| `declaration_references` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md)<br>**Observed** · [PVS](../provers/pvs.md) |
| `definition_references` | **Observed** · [Lean 4](../provers/lean4.md)<br>**Unavailable** · [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md) |
| `definition_registrations` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [HOL Light](../provers/hol-light.md) |
| `enabled_rules` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [ACL2](../provers/acl2.md) |
| `generated_obligations` | **Unavailable** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Mizar](../provers/mizar.md)<br>**N/A** · [Metamath](../provers/metamath.md)<br>**Observed** · [PVS](../provers/pvs.md) |
| `imports` | **Observed** · all ten provers |
| `justification_references` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [PVS](../provers/pvs.md)<br>**Observed** · [Mizar](../provers/mizar.md) |
| `kinds` | **Observed** · all ten provers |
| `names` | **Observed** · all ten provers |
| `parameters` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md)<br>**Observed** · [PVS](../provers/pvs.md) |
| `pending_goals` | **Unreported** · [Lean 4](../provers/lean4.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [Rocq](../provers/rocq.md), [Agda](../provers/agda.md) |
| `proof_regions` | **Observed** · [Lean 4](../provers/lean4.md)<br>**Unreported** · [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md) |
| `proof_used_premises` | **Observed** · [Lean 4](../provers/lean4.md), [Isabelle](../provers/isabelle.md), [ACL2](../provers/acl2.md), [Metamath](../provers/metamath.md)<br>**Unavailable** · [Rocq](../provers/rocq.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [Agda](../provers/agda.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md) |
| `registrations` | **Unreported** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [PVS](../provers/pvs.md)<br>**Observed** · [Mizar](../provers/mizar.md) |
| `rewrite_rules` | **Unavailable** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [Isabelle](../provers/isabelle.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Observed** · [ACL2](../provers/acl2.md) |
| `source_mapping` | **Observed** · [Lean 4](../provers/lean4.md), [Rocq](../provers/rocq.md), [HOL Light](../provers/hol-light.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md)<br>**Reconstructed** · [Isabelle](../provers/isabelle.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md) |
| `statement_references` | **Observed** · [Lean 4](../provers/lean4.md), [Isabelle](../provers/isabelle.md)<br>**Unavailable** · [Rocq](../provers/rocq.md), [HOL Light](../provers/hol-light.md), [HOL4](../provers/hol4.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [Metamath](../provers/metamath.md), [Mizar](../provers/mizar.md), [PVS](../provers/pvs.md) |
| `statements` | **Observed** · all ten provers |
| `term_trees` | **Observed** · [Lean 4](../provers/lean4.md), [Isabelle](../provers/isabelle.md), [HOL4](../provers/hol4.md), [Mizar](../provers/mizar.md)<br>**Unavailable** · [Rocq](../provers/rocq.md), [HOL Light](../provers/hol-light.md), [ACL2](../provers/acl2.md), [Agda](../provers/agda.md), [PVS](../provers/pvs.md)<br>**N/A** · [Metamath](../provers/metamath.md) |

Document reset discards candidate revisions. Ephemeral handles identify a session and worker generation. Branching a proof and saving a process snapshot are distinct operations.

[Historical release records](../../benchmarks/runtime/qualification.jsonl) · [Stable-toolchain interaction records](../../benchmarks/runtime/interaction-capabilities.jsonl)

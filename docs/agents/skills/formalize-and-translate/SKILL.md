---
name: formalize-and-translate
description: Run ITPEval for English-to-formal generation, formal-to-English restatement, cross-prover translation or a Lean equivalence check.
---

# Formalize and translate

Run from an ITPEval checkout. For an installed copy of this skill, resolve the guide links from `docs/agents/skills/formalize-and-translate/SKILL.md` in that checkout.

Preserve the source statement's domains, quantifiers, hypotheses, and conclusion. Record the model and keep its response alongside the checked output.

- For an English claim, generate a statement in the requested prover with the imports it needs. On the released round-trip data, run `python -m eval.pipeline.cycle.run --data FILE --cycle 1 --model MODEL` for Lean or use `--cycle 2` for the four-prover round trip. Run `python -m eval.pipeline.cycle.verify` with the same cycle and model. For a formal-to-English round-trip result, read `step2_nl`. [Round-trip example](../../../guides/formalization-and-translation.md#round-trip-evaluation)
- For a formal-to-English request on your own file, read the native declaration and its context. Explain the hypotheses and conclusion in English, and use the native proof if the user also asks how the theorem was proved. [Auto-informalization](../../../guides/formalization-and-translation.md#auto-informalization)
- For released cross-prover tasks, run `python -m eval.pipeline.translation.run` with `--src`, `--tgt`, and `--ids`. Choose `--mode stmts` for statements or `--mode proofs` for proofs. Preview the selected prompts with `--dry-run`. The released statement data covers ten provers, and the proof data covers four. [Translation commands](../../../guides/formalization-and-translation.md#cross-prover-translation)

Check generated formal outputs in the target prover. For semantic equivalence on verified Lean-target statement translations, run `python -m eval.pipeline.beq.beq_check RESULTS.jsonl --target lean4`. Record evidence for both implications. Report equivalence as unestablished if the bounded check fails to prove either direction. [Semantic equivalence in Lean](../../../guides/formalization-and-translation.md#semantic-equivalence-in-lean)

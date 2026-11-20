# Formalization and translation

ITPEval saves the configured model's response. Check formal outputs with the target prover and its libraries.

| Task | Input | Output | Released benchmark scope |
|---|---|---|---|
| Autoformalization | A theorem statement in English | A formal statement | Lean 4 alone, or Lean 4, Rocq, Isabelle/HOL and HOL Light together |
| Auto-informalization | One or more formal versions of a theorem | An English statement of its assumptions and conclusion | The same two configurations, as the middle step of a round trip |
| Cross-prover statement translation | A formal statement in one prover | A formal statement in another | Ten provers, 90 directed source–target pairs |
| Cross-prover proof translation | A proof in one prover | A complete proof file for another | The released proof data covers the original four provers |

## Autoformalization

“The square of every real number is nonnegative” becomes `∀ x : ℝ, 0 ≤ x ^ 2` in Lean. The quantifier covers every `x`, `ℝ` fixes the domain, and `0 ≤ x ^ 2` states the claim. The round-trip experiment leaves the proof open. [Paper, §4.7](https://arxiv.org/html/2607.19407v1#S4.SS7)

<details markdown="1">
<summary>What changes if the model writes ℕ?</summary>

The claim then ranges over natural numbers. It has a smaller domain than the English sentence, which also covers negative numbers and noninteger real numbers. Both statements can be valid and still express different claims.

</details>

## Auto-informalization

Ask the model to express a formal statement's domain, assumptions, and conclusion in English. In the square example, `ℝ` becomes “real number” and `0 ≤` becomes “nonnegative.” The saved round trip records the English claim in `step2_nl`. To explain how the theorem was proved, read the proof as well. [Worked proof explanation](../start/reading-proofs.md#what-is-a-proof-explanation)

## Cross-prover translation

Translate a complete proof by supplying both the claim and its proof in the target language. If the target claim is already reviewed, use a proof-completion task to fill its proof. [Fixed-target proof tasks](../reference/task-manifests.md)

From the checkout, use `--dry-run` to review a Lean-to-PVS task selection and preview its prompt locally.

```bash
# Preview the first Babel-formal statement in this translation direction.
python -m eval.pipeline.translation.run --sources babel-formal --ids 1 \
  --src lean4 --tgt pvs --model claude-sonnet-4-6 --dry-run
```

Remove `--dry-run` when the target prover and model provider are ready. [Run a translation](../benchmarks/translation.md#quick-start)

## Round-trip evaluation

The cycle runner starts with English, generates a formal statement, turns it back into English, then generates a second formal statement. Read the intermediate English along with the first and last formal outputs to locate where a change entered the cycle.

In the paper’s worked example, a logarithm problem formalized over natural numbers in the reference came back with real-valued variables. The generated Lean versions preserved that change through both passes. A reader comparing only the two generated versions could miss the change of domain. [Worked example, Appendix E.1](https://arxiv.org/html/2607.19407v1#A5.SS1.SSS0.Px1)

To run this record, install the evaluation extra and target provers, then configure a model provider. [Evaluation setup](../benchmarks/translation.md#quick-start)

```python
# Select the paper's worked example from the released miniF2F records.
import json
from pathlib import Path

records = Path("eval/data/minif2f_nl4itp.jsonl").read_text(encoding="utf-8").splitlines()
record = next(line for line in records if json.loads(line)["name"] == "aime_1983_p1")
# Keep only the selected record so the round trip processes one problem.
folder = Path("build/aime-round-trip")
folder.mkdir(parents=True, exist_ok=True)
(folder / "input.jsonl").write_text(record + "\n", encoding="utf-8")
```

```bash
# Generate all three stages with the configured model, then verify the formal outputs.
export ITPEVAL_RESULTS_DIR="$PWD/build/aime-round-trip/results"
python -m eval.pipeline.cycle.run --data build/aime-round-trip/input.jsonl --cycle 2 --model claude-sonnet-4-6
python -m eval.pipeline.cycle.verify --cycle 2 --model claude-sonnet-4-6
```

Use `--cycle 1` in both commands for Lean alone. Cycle 2 saves the English description as `step2_nl` and the first and final Lean outputs as `step1_lean4` and `step3_lean4`, alongside the other three provers’ outputs. The verifier writes a sibling file ending in `_verified.jsonl`.

## Semantic equivalence in Lean

Lean BEq tries to prove both $G \Rightarrow R$ and $R \Rightarrow G$ for a generated statement $G$ and reference $R$. Read each direction separately. If the budget expires before both proofs are found, the result is *equivalence not established*. [Paper, §3.4](https://arxiv.org/html/2607.19407v1#S3.SS4)

Run BEq on verified Lean-target **statement translations** saved by the translation pipeline. Give it the results JSONL for your run. The checker resolves Lean references from the published records or the extended statement shards. For declarations in your own prepared Lean project, the Python API also exposes a bidirectional check. [Python API](../reference/python.md)

```bash
# Supply the verified translation results file as the positional argument.
python -m eval.pipeline.beq.beq_check translations.jsonl --target lean4 --output-dir ./build/beq
```

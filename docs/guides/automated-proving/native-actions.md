# Search with native actions

For the provers below, `driver.suggest_atp()` tries native actions on a fork. It records attempts, feedback, and any final checker evidence. Set `max_trials` for candidate checks and `timeout_s` for the search deadline.

| Prover | What search tries | What the example checks |
| --- | --- | --- |
| ACL2 | Reviewed proof-builder simplification and `bash` | After `promote`, `s` simplifies a goal using its hypotheses. When further simplification makes no change, `bash` closes it. |
| Agda | [Auto](https://agda.readthedocs.io/en/v2.9.0/tools/auto.html) for the current typed hole | Finds `f (g x)` from local arguments. Another example supplies a lemma with `hints=("plus-zero",)`. |
| Metamath | Reviewed labels for numbered proof steps | Bounded search tries assignments in the native Proof Assistant and checks a completed candidate before offering its next assignment. |
| Mizar | Reviewed `by` justifications | The verifier rejects an irrelevant reference and accepts a local theorem that supplies the missing justification. |
| PVS | Reviewed `(grind)` and `(assert)` commands | Search follows the current sequent’s focus. A separate reviewed ProofLite script checks the completed formula and its TCCs. |

[Native search results](../../../benchmarks/runtime/native-search.json)

Mizar needs transitivity of set inclusion. The task permits the local theorem `Th1` and the irrelevant `TARSKI:2` so you can compare their checker verdicts. [Mizar article](../../../itpeval/tests/fixtures/projects/mizar/justifications/hello.miz)

```python
from pathlib import Path

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project
from itpeval.runtime.proof_driver import NativeProofDriver

# Open the locked article at the proposition whose justification is missing.
root = curated_project("mizar").parent / "justifications"
env = prepare_project("mizar", root, prefix=default_prefix(), cache=Path("build/native-search-cache"))
task = get_backend("mizar").build_task(env)
driver = NativeProofDriver(task, env)

# Try two reviewed justifications and print the native verdict for each.
suggestion = driver.suggest_atp(max_trials=2)
for trial in suggestion.evidence.trials:
    print(trial.action.text, trial.outcome)

# Apply the accepted proof to the same revision.
if suggestion.outcome == "accepted":
    driver.apply_atp(suggestion)
    print(suggestion.verification.checker_outcome)
```

Metamath can return a checked completion plan in `suggestion.evidence.plan`. Applying a `progress` suggestion commits the next assignment. The trial log keeps the verdict for the plan, and the session earns proof credit after its complete proof passes. For a saved checkpoint, set the search budget with `--max-trials`.

In PVS, call `driver.suggest_atp(proof_fragment=fragment)` with a reviewed ProofLite fragment when an interactive command sequence can finish the proof. The receipt records `same_locked_target` when the strategy independently proves the same formula and its obligations. Use `--proof-file PATH` to supply that fragment from the command line. For Agda, repeat `--hint NAME` to pass named lemma hints. [PVS proof walkthrough](../../runtime/hol-and-pvs-interaction.md#branch-and-restore-a-pvs-proof)

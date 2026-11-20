# Search from a proof state

## Ask an ATP during an interactive proof

In Lean and Rocq, introducing a hypothesis can leave a goal the Horn bridge supports. Here `intro hp.` changes `p -> q` to `q` and adds `hp : p`. The bridge can then use `hpq : p -> q`. Rocq checks the complete proof with the introduction in place. [Rocq theorem](../../../itpeval/tests/fixtures/projects/rocq/horn-prefix/Implication.v)

```python
from pathlib import Path

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver

# Prepare the Rocq exercise and open its goal in the native proof driver.
root = curated_project("rocq").parent / "horn-prefix"
env = prepare_project("rocq", root, prefix=default_prefix(), cache=Path("build/atp-cache"))
task = get_backend("rocq").build_task(env)
driver = NativeProofDriver(task, env)

# Introduce the hypothesis, then save this revision before running search.
driver.advance(NativeProofAction("command", "intro hp."))
write_json(Path("build/rocq-open-checkpoint.json"), driver.checkpoint().to_dict())
print(env.lock_path)

# Search without changing the session. Apply only the independently checked action.
proposal = driver.suggest_atp(solver="e")
if proposal.outcome == "accepted":
    step = driver.apply_atp(proposal)
    print(step.observation.status, driver.finalize().evidence.checker_outcome)
else:
    print(proposal.outcome, proposal.candidate)
```

Suggestions belong to one task, lock, and proof revision. Request a new suggestion after advancing. `outside_task_policy` retains the candidate for review, and `unsupported_goal` keeps the native observation. Lean and Rocq support a single focused ground Horn goal. [E and Vampire runs](../../../benchmarks/runtime/atp-from-session.json)

Use the printed lock path and saved checkpoint to search the same revision from the CLI.

```bash
# Substitute the lock path printed by the Python example.
itpeval atp resume --lock path/to/lock.json \
  --checkpoint build/rocq-open-checkpoint.json --output build/rocq-atp-suggestion.json
```

## Search one HOL subgoal

HOL4’s `METIS_TAC []` and HOL Light’s `ASM_MESON_TAC []` run first-order search with the assumptions of the selected goal. The driver can try either tactic on a private branch. A result of `progress` closes that subgoal and leaves its siblings available. A result of `accepted` includes the fresh checker verdict for the complete theorem. [HOL4 Metis reference](https://hol-theorem-prover.org/docs/trindemossen-2/Reference/bossLib.METIS_TAC) · [HOL Light MESON reference](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ASM_MESON_TAC.html)

The bundled HOL4 example introduces three assumptions, then splits the conclusion into `q n` and `r n`. First solve `r n` using both implication rules. Then solve `q n` using the first rule. [HOL4 source](../../../itpeval/tests/fixtures/projects/hol4/metis/helloScript.sml) · [HOL Light source](../../../itpeval/tests/fixtures/projects/hol-light/automation/hello.ml)

```python
from pathlib import Path

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver

# Prepare the packaged HOL4 project and bring its hypotheses into scope.
root = curated_project("hol4").parent / "metis"
env = prepare_project("hol4", root, prefix=default_prefix(), cache=Path("build/hol-atp-cache"))
task = get_backend("hol4").build_task(env)
driver = NativeProofDriver(task, env)
driver.advance(NativeProofAction("tactic", "REPEAT DISCH_TAC", ()))
driver.advance(NativeProofAction("tactic", "CONJ_TAC", (0,)))

# Search the right branch while leaving the left branch available.
right = driver.suggest_atp(solver="native", goal_path=(0, 1))
remaining = driver.apply_atp(right).observation.native["goals"]
print(right.outcome, remaining[0]["path"])

# Close the last branch and read the independent strict check.
left = driver.suggest_atp(solver="native", goal_path=(0, 0))
driver.apply_atp(left)
print(left.outcome, left.verification.checker_outcome)
```

In HOL4, `solver="e"` or `solver="vampire"` searches a selected goal's first-order encoding through HOLyHammer, including its local assumptions. The receipt keeps the actual TPTP input and solver answer. HOL4 tries Metis on the selected goal and checks the completed proof tree. [Native and external benchmark runs](../../../benchmarks/runtime/hol-automation.json)

For HOL Light, prepare the `automation` fixture and introduce its hypothesis with `DISCH_TAC`. The path selection works the same way. Pass a preloaded worker to the driver to reuse the HOL core when exploring branches. [Preloaded HOL Light worker](../../runtime/hol-light-fork.md#use-a-preloaded-worker)

For a saved checkpoint, `itpeval atp resume --goal-path 0.1` selects the right branch. Add `--lock` and `--checkpoint` as in the Rocq example. The search defaults to the native tactic for either HOL system.

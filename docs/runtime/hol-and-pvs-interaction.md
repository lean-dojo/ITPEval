# HOL tactics and PVS commands

HOL4 and HOL Light return a goal and its hypotheses. PVS returns a sequent with assumptions on the left and formulas to prove on the right. The trace preserves the native form and ties it to the source and imports with a task ID.

## Follow a HOL tactic

`tactic_trace(task, actions, prepared=env)` runs the supplied HOL4 or HOL Light tactics at a locked theorem. It combines them using native `THEN`. If a tactic creates two subgoals, the following tactic runs once on each. Read `invocations` to see each input goal, hypothesis list, result and any diagnostic.

In this HOL4 example, `ALL_TAC` leaves the goal as it was. `PROVE_TAC []` closes it and returns an empty list of subgoals.

```python
from pathlib import Path

from itpeval.backends.hol_tactics import tactic_trace
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project

# Lock the HOL4 exercise and trace two tactics on p implies p.
env = prepare_project("hol4", curated_project("hol4"),
                      prefix=default_prefix(), cache=Path("build/interaction-cache"))
task = build_task(env)
trace = tactic_trace(task, ["ALL_TAC", "PROVE_TAC []"], prepared=env)
for step in trace["invocations"]:
    print(step["action"], len(step["subgoals"]))
```

Run the final proof through `verify` when you need task acceptance. [HOL4 trace](../../benchmarks/runtime/evidence/hol4/native-interaction.json) · [HOL Light trace](../../benchmarks/runtime/evidence/hol-light/native-interaction.json) · [Check a candidate](../reference/python/checking.md#check-a-candidate)

## Edit one HOL subgoal at a time

`HOLProofSession` uses native `THENL` to apply each tactic to its chosen subgoal. A goal’s `path` is a tuple of child indices, and `()` denotes the initial goal. For $p \Rightarrow (p \land p)$, `DISCH_TAC` puts `p` in the hypotheses. `CONJ_TAC` then produces two goals that each ask for `p`.

```python
import json
from pathlib import Path

from itpeval.backends.hol_tactics import HOLProofCheckpoint, HOLProofSession
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project

# Use the bundled branch exercise. Change the ID to hol-light for OCaml syntax.
prover = "hol4"
project = curated_project(prover).parent / "interaction"
env = prepare_project(prover, project, prefix=default_prefix(), cache=Path("build/interaction-cache"))
task = build_task(env)
session = HOLProofSession(task, env)
handle, _ = session.step(session.handle, (), "DISCH_TAC")
handle, split = session.step(handle, (0,), "CONJ_TAC")

# Close the left subgoal in a separate session. The parent still has both goals.
branch = session.fork(handle)
changed, remaining = branch.step(branch.handle, split.goals[0].path, "ASM_REWRITE_TAC []")
print(remaining.goals[0].path)
closed, _ = branch.step(changed, remaining.goals[0].path, "ASM_REWRITE_TAC []")

# Move the tactic tree through JSON and replay it against the same task.
saved = json.dumps(branch.checkpoint(closed).to_dict())
checkpoint = HOLProofCheckpoint.from_dict(json.loads(saved))
restored = HOLProofSession.from_checkpoint(task, env, checkpoint)
print(restored.finalize(restored.handle).checker_outcome)
```

A checkpoint stores tactics, goal paths and subgoal counts. Replay compares the counts with the native replies. Supported HOL Light projects can restore observations in an isolated child of a preloaded worker. [Preloaded worker](hol-light-fork.md#use-a-preloaded-worker) · [Branch and replay trials](../../benchmarks/runtime/evidence/hol-branches.json)

## Read a PVS proof state

`itpeval.backends.pvs.interaction.command_trace(task, commands, prepared=env)` calls `prover-init` and records one `prover-step` response per command. In the example, `(grind)` closes $orall n \in \mathbb{Z},\ \mathrm{twice}(n)=2n$. Final verification runs ProofLite in a fresh workspace and checks `twice_TCC1`. [PVS trace](../../benchmarks/runtime/evidence/pvs/native-interaction.json) · [PVS proof completion](../provers/pvs.md#proof-completion)

## Branch and restore a PVS proof

The branch example asks PVS to prove two equalities. `(skosimp)` introduces an arbitrary integer, and `(split)` gives each equality its own subgoal. The active subgoal’s `path` identifies where PVS is working. Use `(postpone)` to move the focus to the other goal.

```python
import json
from pathlib import Path

from itpeval.backends.pvs.interaction import PVSProofCheckpoint, PVSProofSession
from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project

# Prepare the example theorem and its reviewed proof commands.
backend = get_backend("pvs")
project = curated_project("pvs").parent / "interaction"
env = prepare_project("pvs", project, prefix=default_prefix(), cache=Path("build/interaction-cache"))
task = backend.build_task(env)
session = backend.open_native_session(task, prepared=env)
handle, _ = session.step(session.handle, "(skosimp)")
handle, first = session.step(handle, "(split)")

# Change focus on a branch and keep the parent at the first goal.
branch = session.fork(handle)
changed, second = branch.step(branch.handle, "(postpone)")
print(first.focused.path, second.focused.path)

# Serialize the exact command prefix, then replay it and close both goals.
saved = json.dumps(branch.checkpoint(changed).to_dict())
restored = PVSProofSession.from_checkpoint(task, env, PVSProofCheckpoint.from_dict(json.loads(saved)))
handle, _ = restored.step(restored.handle, "(grind)")
handle, state = restored.step(handle, "(grind)")
print(state.status)

# Independently check the theorem and its TCC using the reviewed batch proof.
result = restored.finalize(handle, "(then (skosimp) (split) (grind))")
print(result.verification.task_success, result.match)
```

Replay checks the commands and native state under the saved task and lock. `same_locked_target` means ProofLite checked a separate batch proof of the same theorem. `identical_native_command` means one command served as both the interactive and batch proof. [PVS replay results](../../benchmarks/runtime/pvs-proof-sessions.json)

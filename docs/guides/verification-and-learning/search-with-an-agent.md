# Write a proof-search agent

## Search over proof edits

### Run a local search agent

This agent chooses the shortest untried edit. Rocq rejects `exact I.` because `I` proves `True` and the goal is `P -> P`. The next call sees that attempt in its history and submits `intro p; exact p.`, which closes the proof. Change `prover` to try another packaged task.

```python
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.cli.lib import default_prefix
from itpeval.core.episodes import Action
from itpeval.core.records import digest
from itpeval.environments import prepare_project
from itpeval.learning.episodes import export_jsonl, task_prompt
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rollouts import rollout

# Use the installed prover and lock the theorem before collecting attempts.
prover = "rocq"
project = prepare_project(prover, curated_project(prover), prefix=default_prefix(), cache=Path("cache"))
task = build_task(project)

def propose(task, history):
    # A retry sees earlier submissions. Pick the shortest remaining candidate.
    tried = {step.action.candidate for step in history}
    remaining = (edit for edit in task.allowed_edits if edit not in tried)
    candidate = min(remaining, key=len)
    return Action("edit_document", candidate, candidate)

# Allow one attempt per listed fragment. A successful native check ends the loop.
manifest = RunManifest.for_proof_task(
    task, dataset_id=digest([task.task_id]), prompt_id=digest(task_prompt(task)),
    model_config={"algorithm": "shortest permitted edit first"}, max_attempts=len(task.allowed_edits),
)
episode = rollout(task, project, manifest, propose)
for step in episode.transitions:
    print(step.action.candidate, "→", step.observation.checker_outcome)
export_jsonl([episode], Path("build/search") / prover / "episodes.jsonl", view="episodes")
```

The search above chooses from a finite list. A model-backed generator can read `task_prompt(task)` and the last transition’s `observation.stdout` and `observation.stderr` to write a revision. Return its original response and the submitted fragment in the same `Action`. [Run one model-generated completion](../../start/proof-completion.md#let-a-model-or-agent-supply-the-proof)

### Search with native proof information

Both examples accept `--qualification-report PATH` to require capability evidence for the exact environment and build. Metamath retrieves assertions visible at the target, forms applications from their active hypotheses, and checks each candidate. The manifest keeps retrieved occurrence IDs and required capabilities. [Metamath premise-search episode](../../../benchmarks/runtime/evidence/metamath/premise-search.jsonl)

```bash
# Search over assertions visible at the Metamath target.
python -m itpeval.learning.premise_search \
  --prefix "${ITPEVAL_PREFIX:-$HOME/.local/share/itpeval/toolchains/current}" --cache ./cache \
  --output ./premise-search.jsonl
```


Lean explores permitted tactics breadth first, expands distinct goals from the language server, and verifies apparently complete proofs. The run keeps node and depth budgets, states, and checker evidence. [Lean tactic-search episode](../../../benchmarks/runtime/evidence/lean4/goal-search.jsonl)

```bash
# Use Lean goal feedback to explore the permitted proof edits.
python -m itpeval.learning.goal_search \
  --prefix "${ITPEVAL_PREFIX:-$HOME/.local/share/itpeval/toolchains/current}" --cache ./cache \
  --output ./lean-search.jsonl
```

## Use native goals in an agent

Use `NativeProofDriver` with a reviewed proof task on any of the ten built-in provers. `observe()` reads the current goal, typed hole, sequent, or thesis. `advance(action)` returns the native response and a `committed` flag. A failed Rocq tactic leaves the same goal available for the next attempt. A rejected Mizar article edit commits the edited document so the agent can repair it.

The example uses a fixed action sequence to show Rocq's feedback. A model-backed policy can choose its next action from the current goal and attempt history.

```python
from pathlib import Path

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import replay_native_episode, rollout_native
from itpeval.runtime.proof_driver import NativeProofAction

# Prepare the bundled theorem P → P and bind the run to that environment.
backend = get_backend("rocq")
env = prepare_project("rocq", curated_project("rocq"),
                      prefix=default_prefix(), cache=Path("build/agent-cache"))
task = backend.build_task(env)
commands = ("exact I.", "intro p.", "exact p.")
manifest = RunManifest.for_native_proof_task(task, "bundled-exercises", "rocq-demo",
                                             {"policy": "fixed sequence"}, max_attempts=len(commands))

def propose(task, current, history):
    # Use current.native to inspect Rocq's goal and history to read failed feedback.
    return NativeProofAction("command", commands[len(history)])

episode = rollout_native(task, env, manifest, propose)
for transition in episode.transitions:
    print(transition.action.text, transition.observation.status, transition.committed)

# Save the trajectory for training and recheck it in a fresh session.
jsonl(Path("build/rocq-native-episodes.jsonl"), [episode.to_dict()])
print(replay_native_episode(episode, task=task, prepared=env).checker_outcome)
```

`ready` means the session can be finalized. The final check verifies the locked theorem and its obligations. A multi-command PVS run needs a reviewed ProofLite fragment for that check. [PVS finalization](../../runtime/hol-and-pvs-interaction.md#branch-and-restore-a-pvs-proof)

`driver.action_kind` tells the policy which action to supply. Use a `tactic` for Lean or HOL, supplying `goal_path` for HOL. Use `term` for an Agda hole, `assign` with a Metamath `step_index`, and `command` for ACL2, PVS, or Rocq. For Isabelle and Mizar, use `edit_document` with a complete replacement for the reviewed proof slot. [Native actions and observations](../../runtime/execution/native-interaction.md#native-interaction)

`driver.fork()` preserves the current state while you try another continuation. To resume after restarting Python, save `driver.checkpoint().to_dict()` as JSON. Decode it with `NativeProofCheckpoint.from_dict(data)` and call `NativeProofDriver.from_checkpoint(task, env, checkpoint)`. Restoration reruns the saved actions and checks the observed state identities under the same task and environment. [Export goal and action rows](../training-data/export-a-dataset.md#export-native-goal-and-action-data)

An agent can also return `SearchWithATP()` from its policy to finish from a supported native goal. The episode keeps the proof steps and the solver receipt. In Lean and Rocq the goal can be a later revision, such as the state after introducing hypotheses. [Search during a native proof](../automated-proving/search-a-proof-state.md#ask-an-atp-during-an-interactive-proof)

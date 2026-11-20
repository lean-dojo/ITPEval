# HOL Light workers

Loading a HOL Light development such as Multivariate builds its definitions and theorems in OCaml. On Linux, a batch can load the shared part once and fork an isolated child for each input. [HOL Light libraries](../provers/hol-light.md#libraries)

## Use a preloaded worker

Pass `ForkedHOLLight` to `HOLProofSession` for the packaged completion, branching, and local-import projects. The worker preloads the locked HOL core and uses a fresh child and workspace for each observation. Starting the worker took **105.19 s** in the branching exercise. The first observation took **121 ms**, including lock validation. Native tests checked checkpoint replay, subgoal isolation, import parity, and cleanup after cancellation and deadlines. [Worker measurements and evidence](../../benchmarks/runtime/hol-light-worker.json)

```python
from pathlib import Path

from itpeval.backends.hol_light.worker import ForkedHOLLight
from itpeval.backends.hol_tactics import HOLProofSession
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project

# Prepare the bundled branching project and preload its locked HOL core.
path = curated_project("hol-light").parent / "interaction"
project = prepare_project("hol-light", path, prefix=default_prefix(), cache=Path("build/hol-cache"))
task = build_task(project)
with ForkedHOLLight(project) as worker:
    session = HOLProofSession(task, project, worker=worker)
    first = session.inspect(session.handle)
    changed, goals = session.step(session.handle, first.goals[0].path, "DISCH_TAC")
    print(goals.goals)
```

Use `ForkedHOLLight.supports_project(project)` to check the lock before startup. The worker requires the Linux job guardian and default CPU and address-space limits. Lock drift, timeouts and cancellation of active requests retire the worker and reap its descendants. `finalize` runs a fresh check, and `HOLProofSession(task, project)` uses fresh transactions for other projects. [HOL proof sessions](hol-and-pvs-interaction.md#edit-one-hol-subgoal-at-a-time)

```bash
# Repeat the native branching, import, and process cleanup checks.
python -m benchmarks.runtime.hol_light_worker --prefix "$ITPEVAL_PREFIX" \
  --output build/hol-light-worker.json
```

## Static batch checks

An OCaml driver loads HOL Light and forks one child at a time. The parent’s startup and shutdown took **110.27 s**. After loading, the five checks took **22–57 ms** each. [Native timings](../../benchmarks/runtime/hol-light-fork.json)

The first child declares an OCaml name that the second cannot see. Three more children accept a proof, reject an invalid tactic and accept another proof. The fixture checks the conclusion and hypotheses. General verification and final replay use fresh processes and workspaces. [Fresh startup timings](measurements/startup-and-caching.md#fresh-native-startup)

```sh
# Run the preinitialized worker experiment against the native HOL Light installation.
python -m benchmarks.runtime.hol_light_fork --prefix "$ITPEVAL_PREFIX" \
    --cache /tmp/itpeval-benchmark-cache --output hol-light-fork.json
```

## Preloaded proof-state observations

Two fresh tactic-trace transactions took about **106 s** each. The preloaded parent took about **106 s** to start and stop, and its children took **50–54 ms** per transaction. Both modes produced byte-identical traces on acceptance and rejection, and the retry matched the first edit. OCaml bindings, environment variables and load-path changes stayed in the issuing child. [Pilot trials](../../benchmarks/runtime/hol-light-branch-fork-pilot.json)

The static pilot times native processes. The reusable worker also times lock validation and Python dispatch.

```bash
# Run the same goal observation and isolation cases on one preloaded parent.
python -m benchmarks.runtime.hol_light_branch_fork --prefix "$ITPEVAL_PREFIX" \
  --cache build/hol-fork-cache --output build/hol-light-branch-fork-pilot.json
```

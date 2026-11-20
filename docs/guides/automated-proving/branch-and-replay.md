# Branch and replay

## Explore alternate proof branches

`search_portfolio` explores continuations breadth first, each on a fork. In this Lean example, E tries `p ∨ q`, then the goals reached by `left` and `right`. The context contains `hq : q`. Run it with Lean and E installed. [Lean theorem](../../../itpeval/tests/fixtures/projects/lean4/portfolio/Disjunction.lean)

```python
from pathlib import Path

from itpeval.atp import prepare_solver
from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.learning.native_proofs import SearchWithATP
from itpeval.learning.portfolio import replay_portfolio, search_portfolio
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver

# Open the reviewed Lean exercise and discover the solver once for every branch.
root = curated_project("lean4").parent / "portfolio"
env = prepare_project("lean4", root, prefix=default_prefix(), cache=Path("build/portfolio-cache"))
task = get_backend("lean4").build_task(env)
driver = NativeProofDriver(task, env)
request = SearchWithATP(prepare_solver("e", prefix=env.prefix))


def propose(_task, _state, history):
    # Try the whole goal and both disjuncts. On each branch, search the chosen goal.
    if not history:
        return request, NativeProofAction("tactic", "left"), NativeProofAction("tactic", "right")
    return (request,)


# Keep the starting revision while trying up to eight choices, two actions deep.
start = driver.checkpoint()
portfolio = search_portfolio(driver, propose, policy_id="choose-disjunct", max_trials=8,
                             max_depth=2, timeout_s=30)
assert driver.checkpoint() == start
for index, trial in enumerate(portfolio.trials):
    print(index, trial.parent, trial.outcome)
write_json(Path("build/lean-portfolio.json"), portfolio.to_dict())

# Replay the successful route from the original proof and save its training episode.
if portfolio.outcome == "accepted":
    episode = replay_portfolio(portfolio, task=task, prepared=env)
    print(episode.finalization.evidence.checker_outcome)
    jsonl(Path("build/lean-portfolio-episodes.jsonl"), (episode.to_dict(),))
```

`parent` is the zero-based index of the trial that led to the attempt. `None` marks a choice made at the starting revision.

- Trial `0` reports `unsupported_goal` for the original disjunction.
- Trial `3` follows trial `1`, the `left` tactic. Its `suggestion` contains the ATP receipt with `counter_satisfiable` for the `p` branch.
- Trial `4` follows trial `2`, the `right` tactic. The accepted proof uses `hq` to establish `q`.

`max_trials` counts choices, including unsuccessful ones. `max_depth` bounds actions per branch. `timeout_s` limits wall time for forking and native search, so keep the Python policy callback short. [Portfolio runs](../../../benchmarks/runtime/proof-portfolios.json)

Keep the portfolio to inspect attempts and ancestry. `replay_portfolio` rechecks the winning route and returns a `NativeProofEpisode` for training.

## Export replayed suggestions for training

The episode records suggestions sent to the native checker up to its first success or infrastructure failure. A search with no replayable suggestions writes an empty episode file.

```bash
# Keep solver diagnostics alongside the native proof attempts.
itpeval atp hammer --demo --solver e \
  --output build/isabelle-hammer.json \
  --episodes-output build/isabelle-episodes.jsonl

# Produce the supervised, trajectory and verifier-prompt views for this run.
itpeval training-data native --episodes build/isabelle-episodes.jsonl \
  --output build/isabelle-training --split train
```

In Python, call `itpeval.learning.assisted.episode_from_search(task, receipt)` for standalone Isabelle, Lean, or Rocq receipts. Repeat `--episodes FILE` to combine several provers in the same training export.

To retain the actions leading to a search, return `SearchWithATP()` from a `rollout_native` policy at an open goal. In HOL, pass `goal_path` to select a subgoal. After partial progress the policy can search again. An unresolved search ends the rollout and retains the preceding actions and receipt. With the driver API, you can continue manually. [Export native goal and action data](../training-data/export-a-dataset.md#export-native-goal-and-action-data)

[See the measured cost of search and native replay on the bundled lemma](../../runtime/measurements/proof-sessions.md#automated-search-and-native-replay).

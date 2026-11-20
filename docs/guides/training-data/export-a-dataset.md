# Export a training dataset

Run from the checkout with Metamath installed. For Parquet, install ITPEval with `python -m pip install -e '.[parquet]'`. [Extract your own project](../extract-and-build-a-dataset/extract-a-library.md#extract-your-own-project)

```bash
# Export the library and read the path to the resulting bundle.
bundle=$(itpeval dataset metamath --output build/training-inputs |
    python -c 'import json, sys; print(json.load(sys.stdin)["bundle"])')
# Record a failed proof attempt and its successful revision.
python -m itpeval.learning.example --prover metamath --show-attempts \
  --cache build/training-cache --output build/training-inputs/metamath-episode

# Write training datasets from the library and the proof episode.
itpeval training-data native --bundle "$bundle" \
  --episodes build/training-inputs/metamath-episode/episodes.jsonl \
  --output build/training-native --format both
```

Use `--format jsonl` for a standard-library-only export. Repeat `--bundle` and `--episodes` to combine inputs from different provers. Use `--style chat` for conversational fine-tuning, preferences, and prompt-only data. Choose a fresh output directory for each export.

Use `--catalog libraries.json` for multiple bundles. Add `--episodes` or `--lock` to include proof-training inputs. [Combine libraries across provers](../extract-and-build-a-dataset/combine-libraries.md)

Retrieval labels use resolved, in-scope premises observed in the proof. An accepted first attempt can supply a fine-tuning row. Repair and preference rows also need a failed attempt. The manifest counts rows for every view.

## Export native goal and action data

Pass a goal/action episode from a [native agent run](../verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent) to `--native-episodes`. Repeat the option to combine provers. You can also include library bundles or document-level proof episodes in the same export.

```bash
# Export one row per native action, including actions the prover declined.
itpeval training-data native --native-episodes build/rocq-native-episodes.jsonl \
  --output build/native-steps --split train --format both
```

Each `proof_steps` row includes the prior committed state, the attempted action, its feedback, and whether that action advanced the session. Decode `before.native_json` and `feedback.native_json` to read the prover-specific fields. The last row keeps the checker evidence when final verification ran. Rewards attach to verified proof candidates. A separately checked PVS strategy appears with `final_match="same_locked_target"` and a null action reward.

`atp_json` keeps the suggestion, proof revision, solver output, and any checker evidence for an applied action. A HOL episode can record a search for each closed subgoal. An unresolved final search goes in `unapplied_atp_json`, or in the episode file when there are no actions. [Search during a proof](../automated-proving/search-a-proof-state.md)

Native candidate trials remain in the search receipt. For example, a Metamath row can record a checked completion plan while awarding credit only to the final executed proof. A Mizar row keeps rejected justifications alongside the accepted edit. [Search with native actions](../automated-proving/native-actions.md#search-with-native-actions)

For a portfolio, call `replay_portfolio()` and write its winning episode as one JSONL record for `--native-episodes`. Keep the portfolio itself for unsuccessful branches. [Explore alternate proof branches](../automated-proving/branch-and-replay.md#explore-alternate-proof-branches)

Load the resulting files with [Hugging Face Datasets](load-datasets.md).

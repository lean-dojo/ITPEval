# CLI commands

Run `itpeval --help` for the command list and `itpeval COMMAND --help` for that command’s options. To use a specific toolchain directory, place `--prefix PATH` before the command.

## Check your own file with `eval`

Use `--file` for a complete source file in the selected prover’s language. This form stages the input using the adapter’s usual file layout. For a self-contained fragment, `--code` accepts source text and `--mode snippet` selects the adapter’s snippet wrapper where available.

```bash
# Check an existing Lean source file. Use another prover ID for its source format.
itpeval eval --prover lean4 --file MyProof.lean --json
```

Use `--task-dir DIR` for a project in the adapter’s native layout and `--task-file FILE` to select a file inside it when the adapter supports file selection. The native prover runs inside that directory, where it may write build outputs. File checking reports the adapter’s verdict on the supplied source. For a fixed theorem and proof region, use [`verify-task`](#check-a-proof-with-verify-task). [Work with your own files and imports](../guides/work-with-a-library.md)

## List provers with `list-provers`

```sh
# Print the backend IDs accepted by the CLI.
itpeval list-provers
```

Use the printed IDs in commands. For example, Lean 4 is `lean4` and HOL Light is `hol-light`.

## Inspect or install toolchains

Run `itpeval toolchains status` to query every built-in native toolchain in the active prefix. Use `itpeval toolchains install lean4 rocq` on Linux x86-64 or WSL to install the selected stable builds. Add `--profile baseline` for the benchmark toolchain set and use a separate prefix for it. [Installation and platform setup](../runtime/toolchains.md)

## Lock a project with `prepare`

This example prepares the Lean project from the [quickstart](../start/quickstart.md), reads the path to its lock, then checks the proof of $x = x$.

```sh
# Save the lock location for the following examples.
itpeval prepare lean4 --cache ./cache > project.json
```

A lock identifies the source, libraries and prover build for a check. Supply `--project ./my-project` to lock your own project. To describe a project and its named libraries in one file, use `--manifest environment.json`. The Rocq example binds a compiled module by logical name. The Lean example binds Mathlib and CSLib by their compiled paths. [Rocq project manifest](../guides/environment-manifest.md) · [Lean dependencies](../provers/lean4/mathlib-and-cslib.md)

## Open an editor exercise with `practice`

`itpeval practice PROVER` creates `build/practice/PROVER` with an editable native source file and a VS Code task named **ITPEval: Check saved proof**. Open the folder and run the task after saving your edit. Use `--output DIR` for a new location or reopen the existing folder to continue your work. [Choose a prover and see exactly what to edit](../start/proof-completion.md#choose-your-prover)

## Check a proof with `verify-task`

The command checks a candidate against the theorem and proof region in the project’s completion manifest. It reads the lock from the previous step. Pass the text of the proof fragment with `--candidate`.

```sh
# Read the saved lock and submit the proof fragment.
lock=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')
itpeval verify-task --lock "$lock" --candidate 'rfl'
```

Use `--candidate-file` for a proof saved on disk, `--document-file` for a revised entrypoint, or `--artifact-json` for a set of files. The exit code is **0** for a completed task, **1** for an unsuccessful proof, and **2** when the checker cannot return a result or the invocation is invalid.

For a detached binary certificate, use `--candidate-file` to submit the original bytes. If you use `--candidate` for the same task, pass canonical Base64. [Certificate formats](extending-a-backend.md#add-verification-for-a-detached-certificate)

Add `--summary` to print the prover, target, verdict and any failure diagnostics in the terminal. The default output is the full JSON evidence record.

Add `--save-checkpoint FILE` to save the exact submission. Later pass `--checkpoint FILE` as the input with the same task and lock. The verifier checks the restored submission in a new native process. [Forking and restoring in Python](../runtime/execution/document-revisions.md#fork-and-save-a-document)

## Read declarations with `extract`

Give `extract` the project's lock, a source file relative to the project root, and a directory for the output.

```sh
# Extract declarations defined in the project entrypoint.
lock=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')
itpeval extract --lock "$lock" --entrypoint Hello.lean --output ./declarations
```

## Export training data with `dataset`

```sh
# Export the bundled database and print the paths to both training files.
itpeval dataset metamath --output ./dataset
```

Use a prover ID for its bundled example, or add `--project DIR --entrypoint FILE` to run on your sources. Use `--lock PATH --entrypoint FILE` for a library with a prepared environment. Add `--format parquet` to write both training views as Parquet. Set `--timeout-s SECONDS` for a library that needs more than the default 180 seconds. The JSON response gives the record count and output paths. [Dataset guide](../guides/extract-and-build-a-dataset.md)

Use `--context-storage compact` with `dataset` or `extract` for a large Metamath database. For `dataset`, compact mode defaults to referencing the context by ID in each premise row. Pass `--premise-visibility expanded` to write full lists inline. [Compact Metamath walkthrough](../guides/extract-and-build-a-dataset/extract-a-library.md#extract-a-large-metamath-database)

## Export trainer data with `training-data`

Use `itpeval training-data native --bundle DIR --episodes FILE --output DIR` to turn native extraction or recorded episodes into training views. Pass either input or both. Repeat the flags to include more input projects. Use `itpeval training-data benchmark` for the separately labeled reference views of the released benchmark. [View names, columns, and examples](../guides/training-data.md)

Pass `--native-episodes FILE` to export the states, actions, and feedback from a native proof session. Repeat it to combine proof states from multiple provers in the `proof_steps` view. [Export native goal and action data](../guides/training-data/export-a-dataset.md#export-native-goal-and-action-data)

Use `itpeval training-data libraries --catalog FILE --output DIR` to combine declaration and premise records from multiple libraries, keeping their provenance. Pass the same `--catalog FILE` to `training-data native` to export trainer views from those bundles. [Catalog format and example](../guides/extract-and-build-a-dataset/combine-libraries.md#combine-libraries-across-provers)

## Other commands

| Command | When to use it |
|---|---|
| `check` | Run a packaged example selected by `--task` and save a log for each prover. |
| `report` | Summarize a saved run. Add `--json` for machine-readable results. |
| `eval` | Check a file, snippet or task directory through the original translation interface. |
| `atp` | Run E or Vampire on a TPTP problem. Use `hammer` for Isabelle, `lean-horn` or `rocq-horn` for ground Horn search, and `resume` to search a saved checkpoint in any built-in prover. [Search and replay guide](../guides/automated-proving.md) |
| `install`, `run` | Reproduce the original benchmark’s install and run stages. For a new project, follow the [toolchain setup](../runtime/toolchains.md). |

The same commands are available through `python -m itpeval.cli`.

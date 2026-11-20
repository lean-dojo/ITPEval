# Work with your own files

Each adapter follows its prover's rules for filenames, load paths, and build files. [Find your prover and its libraries](../provers/index.md)

| What you have | What to use |
|---|---|
| A standalone source file | `itpeval eval --prover PROVER --file FILE` |
| A directory with local imports or native build files | `itpeval eval --prover PROVER --task-dir DIR --task-file FILE` where the adapter accepts explicit file selection |
| A project you want to extract, compare or use in repeated checks | `prepare_project` or `itpeval prepare` to record the source and dependencies in a lock |
| A theorem whose proof an agent should finish | Prepare the project with a completion manifest that identifies the theorem and the proof fragment to fill |

## Check a file you already have

Pass the path to a standalone Lean file. For another prover, use its ID and a file in its language.

```bash
# Ask Lean to check a source file you saved.
itpeval eval --prover lean4 --file ./MyProof.lean
```

To try it with a new file, save the following as `MyProof.lean`. The theorem says that swapping the two sides of an equality preserves the equality.

```lean4
-- Given h : x = y, use equality's symmetry to prove y = x.
theorem my_symmetry (x y : Nat) (h : x = y) : y = x :=
  h.symm
```

In Python, the corresponding argument is `code_path`. The result gives the native exit status, diagnostics and elapsed checker time.

```python
from pathlib import Path

from itpeval.itp import run_itp

# Use the same file and backend as the command-line example.
result = run_itp(prover="lean4", code_path=Path("MyProof.lean"))
print(result.ok)
print(result.stdout + result.stderr)
```

Read `ok` as the selected adapter's file verdict. To check that a candidate proves a particular unchanged theorem under its declared assumptions, define a completion task. [Proof task manifests](../reference/task-manifests.md)

The single-file interface stages the selected file in a temporary directory. If the file includes sibling sources, use the directory interface and preserve their layout. For example, this checks the bundled Metamath database and all its includes. Replace the directory and entrypoint with your own database to use the same command.

```bash
# Run from the checkout and select the database's top-level file.
itpeval eval --prover metamath \
  --task-dir itpeval/tests/fixtures/projects/metamath/library --task-file client.mm
```

Some native tools write build outputs in the directory you supply. Prepare a project for isolated attempts with repeatable imports. [Project configuration](environment-manifest.md)

## Follow a proof through a library

The entrypoint `client.mm` includes `base.mm`, which includes an excerpt of set.mm. Install ITPEval from the checkout with `python -m pip install -e .` and run the Python blocks in order with Metamath installed. [Install Metamath](../runtime/toolchains.md)

## Load the project and its imports

Prepare the source directory, then use its lock for extraction and verification.

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import load_project, prepare_project

output = Path("build/library-workflow")
project = LIBRARY / "metamath/library"
# Lock the source files and the installed Metamath toolchain together.
prepared = prepare_project("metamath", project, prefix=default_prefix(), cache=output / "cache")
# A later process can reopen the same project using this path.
library = load_project(prepared.lock_path)
entrypoint = "client.mm"
```

## Extract declarations and training records

Metamath processes all three source files in this bundle. Check the coverage report for the units and fields recovered in your own run. [Example database](../../itpeval/tests/fixtures/projects/metamath/library/client.mm)

```python
# Export the declarations and premise records, then check which files were covered.
bundle, premise_path = export_dataset(library, entrypoint, output)
print("Processed files:", bundle.report["succeeded"])
print("Skipped:", bundle.report["skipped"], "Failed:", bundle.report["failed"])

# Find the proof by its Metamath label in the declaration stream.
declarations = read_jsonl(bundle.path / "declarations.jsonl")
theorem = next(row for row in declarations if row["name"] == "pair-rule")
print(theorem["source_path"], theorem["name"], theorem["checking_status"])
```

The last line prints `client.mm pair-rule proof_verified`. Use the declaration ID to find its training record. The available premises are the model’s context. References observed in the proof are labels for premise selection.

```python
# Join the training record to this exact declaration by ID.
example = next(row for row in read_jsonl(premise_path)
               if row["declaration"]["declaration_id"] == theorem["declaration_id"])
print("Premises available to the model:", len(example["available"]))
print("Proof-use evidence:", example["proof_used_availability"])
# These labels identify the premises that the recorded proof actually uses.
print("References:", [edge["target_name"] for edge in example["proof_used"]])
```

This proof uses `vx`, `vy` and `pair-dv`. Keep the availability field when exporting training data. An adapter may report that proof-use evidence is unavailable. [Declaration, context and dataset formats](extract-and-build-a-dataset.md)

## Check the proofs in the database

Pass the same entrypoint and its included files to the native verifier. Metamath reads the assembled database and runs `verify proof *` over every proof reachable from the entrypoint.

```python
from itpeval.core.types import Artifact, TaskSpec
from itpeval.verification import verify

# Preserve relative paths so Metamath can resolve the database includes.
sources = {path.relative_to(library.project).as_posix(): path.read_bytes()
           for path in library.project.rglob("*.mm")}
artifact = Artifact.from_files(entrypoint, sources)
# Check every proof reachable from client.mm in the prepared environment.
task = TaskSpec("metamath", library.environment_id, "check_artifact", artifact)
result = verify(task, prepared=library)
print(result.checker_outcome)  # accepted
```

Try a proof that substitutes the same variable twice. The rule requires two distinct variables. Submit the changed entrypoint against the same imports and inspect the result.

```python
# Repeating A makes the proof supply the same variable to both arguments.
changed = sources[entrypoint].replace(b"( pair-dv ) ABC", b"( pair-dv ) AAC")
changed_artifact = Artifact.from_files(entrypoint, {**sources, entrypoint: changed})
changed_task = TaskSpec("metamath", library.environment_id, "check_artifact", changed_artifact)
result = verify(changed_task, prepared=library)
print(result.checker_outcome)  # rejected
```

The two attempts use the same environment. The second has different artifact bytes and needs its own check. When you submit identical bytes or the same proof fragment again, you can opt into result caching with `verify_cached`. [Runtime measurements](../runtime/measurements/startup-and-caching.md#loading-a-project-and-reusing-a-verification-result)

## Use your own library

1. Choose a project root and a source entrypoint relative to it. For example, a Metamath database can include sibling databases, and a Rocq client can import compiled modules by logical name. [Project layouts by prover](../provers/index.md)
2. Point `prepare_project` at your source directory. If your project depends on packages built elsewhere, bind those imports in an environment manifest. To extract declarations from a dependency itself, select its sources and an entrypoint there. [Configure projects and imports](environment-manifest.md)
3. Run `export_dataset` for each entrypoint you want to cover. Inspect `succeeded`, `skipped`, `failed` and field availability in each report before combining the outputs. [Build a dataset](extract-and-build-a-dataset.md)
4. Choose the check your task needs. Each adapter defines what a whole-file check establishes. To evaluate a candidate proof for a specific theorem, identify its statement, editable proof and required obligations in a completion manifest, then run `itpeval verify-task`. [Define and check a proof task](../reference/task-manifests.md)

From the repository root, the CLI can export the same example. Substitute your own project path and entrypoint in this command. For longer extractions, increase `--timeout-s`.

```bash
# Point the exporter at the database root and its top-level file.
itpeval dataset metamath --project itpeval/tests/fixtures/projects/metamath/library \
  --entrypoint client.mm --output build/library-cli
```

For a prepared environment, use `itpeval dataset --lock PATH --entrypoint FILE --output DIR`.

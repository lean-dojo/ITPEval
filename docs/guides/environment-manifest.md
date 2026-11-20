# Project configuration

Prepare a project to lock its source snapshot, imports, and native toolchain for checking, extraction, and replay. [Check a standalone file](work-with-a-library.md#check-a-file-you-already-have)

## Prepare a local directory

This Metamath example keeps the database and its included files under one project root.

```sh
# Select the project directory. Keep the printed lock path for later checks.
itpeval prepare metamath --project itpeval/tests/fixtures/projects/metamath/library --cache ./cache
```

For your project, choose a layout that the adapter and its toolchain can build. Add a completion manifest only for tasks that hold a theorem fixed and check edits to its proof. [Find your prover's layout](../provers/index.md) · [Choose a target and proof region](../reference/task-manifests.md)

## Name the project's dependencies

Use a project manifest to record named libraries, options, or Git revisions. In this Rocq example, save `environment.json` beside `src` and `library` so the client can import `Aux.Base`.

<figure class="proof-listing" data-listing="rocq" markdown="1">

<figcaption><strong>library/Base.v</strong></figcaption>

```rocq
(* Define the project's helper function. *)
Definition twice (n : nat) := n + n.
```

</figure>

<figure class="proof-listing" data-listing="rocq" markdown="1">

<figcaption><strong>src/Client.v</strong></figcaption>

```rocq
(* Import Base under the logical prefix Aux. *)
From Aux Require Import Base.

(* Both sides compute to 4. *)
Example twice_two : twice 2 = 4.
Proof. reflexivity. Qed.
```

</figure>

Compile the dependency `Base.v` into `library/Base.vo` with the Rocq version you will use for the client. Run this from the project root with the `rocq` command available in your shell.

```bash
# Compile the dependency under the same logical prefix used by the client.
rocq compile -Q library Aux library/Base.v
```

```json
{
  "schema_version": 1,
  "name": "my-rocq-project",
  "prover": "rocq",
  "project": {"path": "src"},
  "libraries": {"Aux": {"path": "library"}},
  "imports": ["Aux.Base"],
  "import_bindings": {"Aux.Base": {"source": "library/Aux", "path": "Base.vo"}},
  "checking_profile": "strict"
}
```

`project.path` points to the client source directory. The key `Aux` gives the compiled library a logical prefix, and `import_bindings` associates `Aux.Base` with the exact `Base.vo` file.

```sh
# Print the lock path for the project described by environment.json.
itpeval prepare --manifest environment.json --cache ./cache > prepared.json
# Extract the client file using the same logical import and compiled module.
lock=$(python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])' < prepared.json)
itpeval extract --lock "$lock" --entrypoint Client.v --output ./declarations
```

Use the printed bundle path to find `twice_two` in `declarations.jsonl` and the compiler's observed import in `report.json`.

Supply compiled module directories for Lean dependencies such as Mathlib or CSLib. Keep Metamath includes at the paths requested by the entrypoint, and bind the Mizar library with the `mizfiles` role. [Lean library configuration](../provers/lean4/mathlib-and-cslib.md)

### Pin a Git revision

A source can give `url` and `revision` with an optional `subdir` in place of `path`. Use an HTTPS Git URL or a local repository path. Preparation resolves branches and tags and records the resulting commit. You can prepare a full commit offline if ITPEval's local mirror already has it. Declare submodules as separate dependencies and materialize symlinks into regular project files before preparing them.

## Reopen a prepared project

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.environments import load_project, prepare_manifest

# Prepare once. A later process can load the printed lock path directly.
env = prepare_manifest(Path("environment.json"), prefix=default_prefix(), cache=Path("cache"))
restored = load_project(env.lock_path)
assert restored.environment_id == env.environment_id
```

Preparing a local directory captures its current source bytes, including uncommitted edits. Git provenance and the source content hash are separate fields. When you change a source file you want to use in later checks, prepare the project again. For a series of candidate edits to the same theorem, reuse the original lock and submit each edit as a candidate.

Explicit import bindings record the logical name, source role, relative path and SHA-256 of the referenced file. Source roles include `project`, `library/NAME` and `toolchain/ROLE`. An import named by project-relative path binds to that file. Reopening a lock validates source and runtime inputs using cached hashes where possible. Run preparation on the destination host to resolve its own toolchain paths. [Runtime and cache behavior](../runtime/execution.md)

## Include extra native tools

The optional `toolchain_inputs` map attaches native executables, modules or library directories to the build fingerprint. A `prefix_path` is relative to the selected native installation. A `path` is resolved from the manifest directory. A Lean project using Pantograph and LeanDojo can include the following field.

```json
{
  "toolchain_inputs": {
    "pantograph": {"prefix_path": "auxiliary/lean4/pantograph"},
    "leandojo_tracer": {"prefix_path": "auxiliary/lean4/ExtractData.lean"}
  }
}
```

ITPEval records a hash for each input and checks it again when you reopen the project. The CLI accepts repeated `--toolchain-input ROLE=PATH` flags when preparing a directory directly. The corresponding Python argument is `toolchain_inputs`. [Project manifest schema](../../itpeval/environments/project.schema.json)

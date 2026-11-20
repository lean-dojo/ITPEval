# Lean 4

Lean is a programming language and an interactive theorem prover. The same language describes functions, statements about those functions, and proofs of those statements. [Project documentation](https://lean-lang.org/doc/reference/latest/The-Type-System/)

## How proof checking works

Lean uses dependent type theory. A type can mention a value, such as the length `n` of a vector. The proposition `nextIndex n = n + 1` is a type that mentions `n` too. A proof is a term of that type. To prove the equation for every natural number, write a function that takes `n` and returns the corresponding proof.

You can give Lean a proof term directly or write a `by` block with tactics that construct it. The kernel typechecks the result. For instance, `rfl` works when both sides of an equation reduce to the same term. For a proof-completion task, ITPEval can also inspect the axioms reported by Lean’s `#print axioms`. [Lean’s introduction to propositions and proofs](https://docs.lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/)

## Read a proof

In `Counts.lean`, `def nextIndex (n : Nat) : Nat := n + 1` defines a function on natural numbers. Calling it adds one. [Open Counts.lean](../../itpeval/tests/fixtures/projects/lean4/library/Counts.lean)

<figure class="proof-listing" data-listing="lean4" data-proof="Counts.next_index_zero" markdown="1">

<figcaption markdown="span"><strong>Lean 4</strong> [Client.lean](../../itpeval/tests/fixtures/projects/lean4/library/Client.lean)</figcaption>

```lean4
-- Apply the imported Counts lemma for the successor of zero.
theorem first_successor : Counts.nextIndex 0 = 1 := Counts.next_index_zero
```

</figure>

**The claim.** `first_successor` is the theorem’s name. The expression after the colon, `Counts.nextIndex 0 = 1`, says that the index following zero is one.

**The proof.** Everything after `:=` in this theorem is its proof. Here the entire proof is `Counts.next_index_zero`, the name of an earlier theorem with exactly the required statement. [Print this proof from an ITPEval export](#see-the-original-proof-text)

Follow that name into `Counts.lean`. Its proof is `rfl`. Unfolding `nextIndex 0` gives `0 + 1`, which computes to `1`. Reflexivity proves the resulting equation `1 = 1`.

<details markdown="1">
<summary>Why can the client use an existing theorem as its entire proof?</summary>

The imported theorem `Counts.next_index_zero` is already a term with type `Counts.nextIndex 0 = 1`. Lean accepts it directly. There is no need to open a tactic block and prove the same equation again.

</details>

## Use your own project

Use a `.lean` file as the entrypoint. For a Lake project, build its dependencies with the project’s Lean release and pass their compiled module roots. Keep the module names and import paths you use in the project.

Check a source file with `itpeval eval --prover lean4 --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset lean4 --project ./my-project \
  --entrypoint Client.lean --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `lean4 --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

Lean ships the initialization library and the standard library with its toolchain. Lake projects can add Mathlib, CSLib, Batteries or packages of their own.

- [Init](https://github.com/leanprover/lean4/tree/v4.36.0/src/Init) — the prelude and foundational definitions.
- [Std](https://github.com/leanprover/lean4/tree/v4.36.0/src/Std) — the Lean standard library.
- [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) — mathematics, from algebra to computability.
- [CSLib](https://www.cslib.io/) — formal computer science, including languages and automata.
- [Batteries](https://github.com/leanprover-community/batteries) — data structures and utilities for Lean programs.

Build the imports with the same Lean version as the checker. Pass each dependency’s compiled module directory to `prepare_project(libraries=...)`, including transitive dependencies. The [Mathlib and CSLib example](lean4/mathlib-and-cslib.md) checks a theorem and extracts its declaration from a client module.

### Extract a library

The bundled client imports a Mathlib directory linter and a local module named `Counts`.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "lean4/library"
output = Path("build/library/lean4")
library = prepare_project("lean4", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "Client.lean", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "first_successor")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `kernel_checked`. Lean checked the proof of the client theorem against its imports.

### See the original proof text

The extractor records this proof’s byte range in the original UTF-8 file.

```python
import json

def blob(key):
    # Bundle blobs are stored by hash, with the first two characters as the directory.
    return (bundle.path / "blobs" / key[:2] / key[2:]).read_bytes()

# Resolve the proof range, then slice the source bytes before decoding the text.
region = json.loads(blob(bundle.report["structures"][target["declaration_id"]]))
source = blob(region["source_sha256"])
print(source[region["start_byte"]:region["end_byte"]].decode("utf-8").strip())
```

This prints `Counts.next_index_zero`. Some generated declarations have no recoverable proof range. [Extraction fields and coverage](../guides/extract-and-build-a-dataset.md)

## Proof completion

The goal is `x = x` for an arbitrary natural number `x`. Replace the underlined fragment.

<figure class="proof-listing" data-listing="lean4" data-proof="exact False.elim" markdown="1">

<figcaption markdown="span"><strong>Lean 4</strong> Starting proof in Hello.lean</figcaption>

```lean4
-- The tactic after by must prove the equality.
theorem itpeval_target (x : Nat) : x = x := by
  exact False.elim
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice lean4
code build/practice/lean4
```

1. Open `Hello.lean` and run **Terminal → Run Task → ITPEval: Check saved proof**. `False.elim` still needs a proof of False.
2. Find `exact False.elim` inside `itpeval_target` and replace it with `rfl`. Reflexivity proves that `x` equals itself.
3. Save and rerun the task. The terminal prints `lean4 · itpeval_target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/lean4/completion/Hello.lean)

The official Lean 4 extension shows the goal in the Infoview when you place the cursor inside the proof. [Lean 4 in VS Code](https://lean-lang.org/getting-started/)

[Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover lean4 --show-attempts \
  --cache ./cache --output ./evidence/lean4
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare lean4 --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/lean4/model.jsonl --model claude-sonnet-4-6
```

## See also


[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/lean4)

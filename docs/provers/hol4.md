# HOL4

HOL4 is a prover for classical higher-order logic with a Standard ML interface. Definitions and theorems are organized into theories that other scripts can import. [Project documentation](https://hol-theorem-prover.org/)

## How proof checking works

HOL4’s simple type theory has types for values, functions and predicates. A Boolean formula can describe the behavior of a function or the steps of a machine. In a proof script, tactics simplify goals or split them into smaller ones. The logical kernel’s inference rules produce the final theorem.

A theory script records the definitions and proved results you want to reuse. Holmake builds its dependencies and makes the resulting theory available to other scripts. A theorem such as `twice_zero` can depend on a local definition from `baseTheory` in the same way that a program depends on an imported module. [The HOL4 project and its applications](https://hol-theorem-prover.org/about)

## Read a proof

The base theory uses a `Definition twice_def:` block with the equation `twice (n:num) = n + n`. [Open baseScript.sml](../../itpeval/tests/fixtures/projects/hol4/library/baseScript.sml)

<figure class="proof-listing" data-listing="hol4" data-proof="simp[twice_def]" markdown="1">

<figcaption markdown="span"><strong>HOL4</strong> [sampleScript.sml](../../itpeval/tests/fixtures/projects/hol4/library/sampleScript.sml)</figcaption>

```hol4
(* Unfold twice and simplify at zero. *)
Theorem twice_zero:
  twice 0 = 0
Proof
  simp[twice_def]
QED
```

</figure>

**The claim.** The line between `Theorem twice_zero:` and `Proof` is the statement, `twice 0 = 0`.

**The proof.** Inside `Proof` … `QED`, the tactic `simp[twice_def]` asks HOL4 to simplify using the definition of `twice`.

Expanding `twice 0` gives `0 + 0`. Arithmetic simplification reduces that to zero, so the two sides agree.

<details markdown="1">
<summary>What does simp[twice_def] add to simplification?</summary>

It gives the simplifier the defining equation for `twice`. The goal `twice 0 = 0` becomes `0 + 0 = 0`, which the existing arithmetic simplification rules can solve.

</details>

## Use your own project

Use a theory script named `nameScript.sml` at the top level of the prepared project. Keep its `Holmakefile`, theory dependencies and required build options together. Use an entry script for the theory you want to extract.

Use `itpeval eval --prover hol4 --task-dir DIR` for a theory with its own Holmake project. The single-file form stages declarations inside a small theory wrapper. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset hol4 --project ./my-project \
  --entrypoint sampleScript.sml --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `hol4 --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

HOL4 ships compiled theories and their source scripts. Further HOL4 projects, including CakeML, build their own theories with Holmake.

- [HOL4 theories](https://github.com/HOL-Theorem-Prover/HOL/tree/develop/src) — arithmetic, predicate sets and other core theories.
- [HOL4 examples](https://github.com/HOL-Theorem-Prover/HOL/tree/develop/examples) — additional formal developments and theory scripts.
- [CakeML](https://github.com/CakeML/cakeml) — a verified implementation of ML built using HOL4.

### Build and check a library

Reuse the core theories supplied by the matching HOL4 installation. For your own theory directory, build its default targets with `Holmake`. For a larger development such as CakeML, use the project's build instructions to select its directories, targets and prerequisite theories. [HOL4 build tools](https://hol-theorem-prover.org/docs/trindemossen-2/Description/misc)

```bash
# Build the theory directory with HOL4's Holmake on PATH.
(cd ./my-library && Holmake)

# Have ITPEval run Holmake on a staged copy and return the verdict.
itpeval eval --prover hol4 --task-dir ./my-library
```

Keep the `Holmakefile` and its required local sources together. The extractor runs Holmake for the prepared project's top-level `nameScript.sml` before reading the theory database.

### Extract a library

The bundled script imports `base` and `refuteUnused`. The latter is an upstream HolRefute example. Holmake builds these theories before the extractor reads their theorems.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "hol4/library"
output = Path("build/library/hol4")
library = prepare_project("hol4", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "sampleScript.sml", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "sample.twice_zero")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `exported_theorem_value`. HOL4 exported this theorem from the compiled sample theory.

## Proof completion

Supply the tactic passed to `store_thm` to prove that `p` implies itself. Replace the underlined fragment.

<figure class="proof-listing" data-listing="hol4" data-proof="NO_TAC" markdown="1">

<figcaption markdown="span"><strong>HOL4</strong> Starting proof in helloScript.sml</figcaption>

```hol4
(* The third argument of store_thm supplies the tactic. *)
val itpeval_target = store_thm ("itpeval_target", ``p ==> p``, NO_TAC);
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice hol4
code build/practice/hol4
```

1. Open `helloScript.sml` and run **Terminal → Run Task → ITPEval: Check saved proof**. NO_TAC always fails.
2. Find `NO_TAC` inside `itpeval_target` and replace it with `PROVE_TAC []`. PROVE_TAC proves the implication using its built-in reasoning and an empty list of supplied theorems.
3. Save and rerun the task. The terminal prints `hol4 · itpeval_target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/hol4/completion/helloScript.sml)

HOL4 mode can display a Goals pane for theory scripts with a compatible HOL installation. [HOL4 mode for VS Code](https://github.com/HOL-Theorem-Prover/hol4-vscode)

Select a pending subgoal and search it with Metis, E, or Vampire. [Search one HOL subgoal](../guides/automated-proving/search-a-proof-state.md#search-one-hol-subgoal)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover hol4 --show-attempts \
  --cache ./cache --output ./evidence/hol4
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare hol4 --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/hol4/model.jsonl --model claude-sonnet-4-6
```

## See also


[HOL tactic and PVS sequent observations](../runtime/hol-and-pvs-interaction.md)

[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/hol4)

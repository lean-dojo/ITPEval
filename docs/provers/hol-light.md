# HOL Light

HOL Light is an OCaml-based theorem prover for classical higher-order logic. A script defines mathematical objects, applies tactics and binds the theorems it proves to OCaml names. [Project documentation](https://hol-light.github.io/)

## How proof checking works

HOL Light distinguishes the OCaml program from the logical terms it manipulates. Backticks enclose a term in the prover’s language. Inside a term, `p ==> p` is logical implication. In higher-order logic you can also write statements about functions and predicates.

A value of type `thm` records a conclusion and its hypotheses. The inference rules construct these values. A tactic can decompose a goal into simpler goals and justify the original goal once they are solved. In the exercise, `prove` returns a theorem with an empty hypothesis list, so the conclusion holds without extra local assumptions. [John Harrison’s HOL Light tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf)

## Read a proof

The same file uses `new_definition` to introduce the equation `itpeval_neg (p:bool) = ~p`. The new operation means logical negation. The binding `itpeval_neg_def` holds its defining theorem.

<figure class="proof-listing" data-listing="hol-light" data-proof="DISCH `p:bool` under_assumption" markdown="1">

<figcaption markdown="span"><strong>HOL Light</strong> [sample.ml](../../itpeval/tests/fixtures/projects/hol-light/library/sample.ml)</figcaption>

```hol-light
(* DISCH turns the assumed p into the premise of p ==> p. *)
let under_assumption = ASSUME `p:bool`;;

let discharge_assumption = DISCH `p:bool` under_assumption;;
```

</figure>

**The claim.** The result named `discharge_assumption` has conclusion `p ==> p` (“if p, then p”) and no remaining assumptions. Here the conclusion is produced by the OCaml expression.

**The proof.** Read both bindings in order. `ASSUME` produces a theorem with conclusion `p` under the assumption `p`. The expression starting with `DISCH` builds the final theorem from it.

Suppose `p`. Under that assumption you already have `p`. Discharging the assumption turns that reasoning into the implication `p ==> p`. The resulting theorem value can be reused by name.

<details markdown="1">
<summary>Where does the assumption p go after DISCH?</summary>

It moves from the hypotheses to the left side of the implication. Apply `concl` to `discharge_assumption` to see `p ==> p`, or `hyp` to see its empty hypothesis list.

</details>

## Use your own project

Use an OCaml `.ml` script for HOL Light. Keep the files it loads with `needs` at their expected paths. A script that loads an installed development can check a client theorem even when the extractor’s source coverage is limited to files inside your project.

Check a source file with `itpeval eval --prover hol-light --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset hol-light --project ./my-project \
  --entrypoint sample.ml --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `hol-light --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

HOL Light loads its foundational theories at startup. Its source tree includes the Library, Multivariate and 100 directories. Projects can load additional developments from source.

- [HOL Light Library](https://github.com/jrh13/hol-light/tree/master/Library) — number theory, lists and other reusable developments.
- [Multivariate](https://github.com/jrh13/hol-light/tree/master/Multivariate) — vectors, topology and multivariate analysis.
- [Formalizing 100 Theorems](https://github.com/jrh13/hol-light/tree/master/100) — standalone mathematical developments.

The native OCaml process loads the entry `.ml` file. Stage local dependencies where `needs` can find them. The extractor follows source files inside the project. Loading an installed development and extracting its own source declarations are different operations.

### Extract a library

The bundled client loads `base.ml` and an upstream arithmetic development from `100/arithmetic.ml`, then constructs a theorem by discharging an assumption.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "hol-light/library"
output = Path("build/library/hol-light")
library = prepare_project("hol-light", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "sample.ml", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "discharge_assumption")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `kernel_theorem_value`. The OCaml binding holds a theorem constructed by the HOL Light kernel.

## Proof completion

Construct a closed theorem with conclusion `p ==> p`. The editable expression is the tactic given to `prove`. Replace the underlined fragment.

<figure class="proof-listing" data-listing="hol-light" data-proof="NO_TAC" markdown="1">

<figcaption markdown="span"><strong>HOL Light</strong> Starting proof in hello.ml</figcaption>

```hol-light
(* The second argument of prove is the tactic. *)
let itpeval_target = prove (`p ==> p`, NO_TAC);;
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice hol-light
code build/practice/hol-light
```

1. Open `hello.ml` and run **Terminal → Run Task → ITPEval: Check saved proof**. NO_TAC always fails.
2. Find `NO_TAC` inside `itpeval_target` and replace it with `ITAUT_TAC`. ITAUT_TAC proves the implication using propositional reasoning.
3. Save and rerun the task. The terminal prints `hol-light · itpeval_target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/hol-light/completion/hello.ml)

The HOL Light extension sends OCaml phrases and selected tactics to a running HOL Light session. [HOL Light extension](https://github.com/monadius/vscode-hol-light)

Select a pending subgoal and try its local assumptions with MESON. [Search one HOL subgoal](../guides/automated-proving/search-a-proof-state.md#search-one-hol-subgoal)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover hol-light --show-attempts \
  --cache ./cache --output ./evidence/hol-light
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare hol-light --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/hol-light/model.jsonl --model claude-sonnet-4-6
```

## See also


[HOL tactic and PVS sequent observations](../runtime/hol-and-pvs-interaction.md)

[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/hol-light)

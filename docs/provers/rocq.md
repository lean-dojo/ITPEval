# Rocq

Rocq, formerly Coq, lets you define programs, state their properties and check proofs of those properties. You may see the name Coq in older projects and papers. [Project documentation](https://rocq-prover.org/doc/V9.2.0/refman/)

## How proof checking works

The Calculus of Inductive Constructions gives Rocq both dependent types and inductive definitions. A proof of `P -> Q` is a function from proofs of `P` to proofs of `Q`. An inductive definition gives you constructors and a corresponding way to reason by cases or induction. For example, natural numbers have a zero case and a successor case.

In proof mode, tactics guide the construction of a proof term. `Qed.` asks the kernel to check that the completed term has the type given by the original statement. `Print Assumptions` reports what the theorem depends on. This is useful when checking a candidate against a task that permits a particular set of assumptions. [Rocq core language and proof terms](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html)

## Read a proof

Inside a section with a type `A`, `Definition identity (x : A) : A := x.` defines a function that returns its input. [Open Library.v](../../itpeval/tests/fixtures/projects/rocq/library/Library.v)

<figure class="proof-listing" data-listing="rocq" data-proof="apply M.identity_eq." markdown="1">

<figcaption markdown="span"><strong>Rocq</strong> [Client.v](../../itpeval/tests/fixtures/projects/rocq/library/Client.v)</figcaption>

```rocq
(* Specialize the library’s identity theorem to natural numbers. *)
Theorem identity_nat (n : nat) : M.identity nat n = n.
Proof. apply M.identity_eq. Qed.
```

</figure>

**The claim.** `(n : nat)` introduces an arbitrary natural number. The claim after the colon is that applying `M.identity` to that number gives back `n`.

**The proof.** The proof script sits between `Proof.` and `Qed.`. Its only instruction is `apply M.identity_eq.`

The library already proves the identity equation for any type and any element. Rocq matches that lemma to the goal by choosing the type `nat` and the element `n`. This closes the goal. The library proves the original lemma by `reflexivity`, since the identity function returns its argument.

<details markdown="1">
<summary>What does Rocq infer from the goal when you apply the imported lemma?</summary>

The imported lemma works for any type and any value of that type. Rocq matches it against `M.identity nat n = n`, choosing `nat` as the type and `n` as the value.

</details>

## Use your own project

Use a `.v` file. Compile its dependencies and preserve their logical module names, such as `Stdlib` or your own root. In a project with several `.v` files, record their dependency order and installed plugins where the checker needs them.

Check a source file with `itpeval eval --prover rocq --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset rocq --project ./my-project \
  --entrypoint Client.v --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `rocq --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

Rocq provides its prelude through Corelib. Stdlib supplies the standard library. Projects can also import developments such as Mathematical Components and Iris.

- [Corelib](https://github.com/rocq-prover/rocq/tree/master/theories) — the prelude and core language support.
- [Stdlib](https://github.com/rocq-prover/stdlib) — Rocq’s standard mathematical and programming library.
- [Mathematical Components](https://math-comp.github.io/) — algebra, finite groups and analysis.
- [Iris](https://iris-project.org/) — higher-order concurrent separation logic.

### Build and check a library

Reuse installed `.vo` files built with your project's Rocq version. Install Stdlib and any other packaged dependencies in the same Rocq environment. If a source checkout provides `_CoqProject`, build the files it lists with these commands. For projects with their own build instructions, follow those to include any required plugins. [Rocq project build guide](https://rocq-prover.org/doc/v9.2/refman/practical-tools/utilities.html)

```bash
# Run from the library root with the matching Rocq on PATH.
rocq makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

For a client that imports `MyLib`, bind the compiled module directory as `libraries={"MyLib": compiled_root}`. ITPEval passes that path and logical name to Rocq with `-Q`. The extractor maps the client project itself to `ITPProject`. [Check a client with external imports](../reference/python/checking.md#check-a-file-with-external-imports)

### Extract a library

The bundled project compiles `StrictProp.v` from Stdlib and a client that imports `ITPProject.Library`.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "rocq/library"
output = Path("build/library/rocq")
library = prepare_project("rocq", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "Client.v", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "ITPProject.Client.identity_nat")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `kernel_checked`. The Rocq kernel checked the proof in the compiled client module.

## Proof completion

For any proposition `P`, prove `P -> P` inside the section. Replace the underlined fragment.

<figure class="proof-listing" data-listing="rocq" data-proof="exact I." markdown="1">

<figcaption markdown="span"><strong>Rocq</strong> Starting proof in hello.v</figcaption>

```rocq
(* Give the body of the proof between Proof. and Qed. *)
Theorem itpeval_target : P -> P.
Proof.
  exact I.
Qed.
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice rocq
code build/practice/rocq
```

1. Open `hello.v` and run **Terminal → Run Task → ITPEval: Check saved proof**. `I` proves True. The goal is an implication about an arbitrary proposition.
2. Find `exact I.` inside `itpeval_target` and replace it with `exact (fun p => p).`. The function takes a proof of P and returns that same proof.
3. Save and rerun the task. The terminal prints `rocq · itpeval_target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/rocq/completion/hello.v)

VsRocq and its language server can step through the proof and show its goals. [VsRocq](https://github.com/rocq-prover/vsrocq)

[Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover rocq --show-attempts \
  --cache ./cache --output ./evidence/rocq
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare rocq --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/rocq/model.jsonl --model claude-sonnet-4-6
```

## See also


[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/rocq)

# Isabelle/HOL

Isabelle is a framework for formal proofs. This guide uses Isabelle/HOL, the Isabelle instance for classical higher-order logic, with proofs written in Isar. [Project documentation](https://isabelle.in.tum.de/overview.html)

## How proof checking works

Higher-order logic lets you quantify over functions and predicates as well as values. For example, one statement can describe a property shared by every function of type `nat ⇒ nat`. Isabelle’s underlying logic, Pure, supplies the rules for reasoning about judgments and local assumptions. HOL supplies mathematical propositions, types and connectives.

An Isar proof can name assumptions, prove intermediate facts and use those facts to close goals. A locale packages such a context so its lemmas can be interpreted wherever the assumptions hold. A command such as `by (rule premise)` applies an existing theorem or local fact. Isabelle’s inference machinery checks the result in the theory’s context. [Isabelle/Isar reference, Pure and object logics](https://isabelle.in.tum.de/doc/isar-ref.pdf)

## Read a proof

In `Base.thy`, the command `definition twice` introduces the equation `twice n = n + n`. Isabelle gives that equation the name `twice_def`. [Open Base.thy](../../itpeval/tests/fixtures/projects/isabelle/library/Base.thy)

<figure class="proof-listing" data-listing="isabelle" data-proof="using positive by (simp add: twice_def)" markdown="1">

<figcaption markdown="span"><strong>Isabelle/HOL</strong> [Sample.thy](../../itpeval/tests/fixtures/projects/isabelle/library/Sample.thy)</figcaption>

```isabelle
(* The locale supplies the assumption that n is positive. *)
lemma twice_positive: "0 < twice n"
  using positive by (simp add: twice_def)
```

</figure>

**The claim.** The quoted formula `0 < twice n` is the statement. The surrounding locale (a named context) supplies a natural number `n` and an assumption `positive` saying that `0 < n`.

**The proof.** The proof is `using positive by (simp add: twice_def)`. The word `using` supplies the assumption. The method after `by` asks Isabelle’s simplifier to use the defining equation.

Replace `twice n` by `n + n`. Because `n` is positive, adding it to itself gives a positive number. The simplifier establishes this from the facts in scope.

<details markdown="1">
<summary>Why does the lemma need the assumption that n is positive?</summary>

Try `n = 0`. Then `twice n` is zero and the claim `0 < twice n` fails. Inside the locale, the named fact `positive` rules out that case.

</details>

## Use your own project

Use a `.thy` file and keep the file name aligned with the theory name. Include a session’s `ROOT` and its local theories when the project needs them. An AFP development can require a particular Isabelle release and a session beyond the installed HOL heap.

Check a source file with `itpeval eval --prover isabelle --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset isabelle --project ./my-project \
  --entrypoint Sample.thy --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `isabelle --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

Isabelle/HOL projects usually build on the HOL session. The distribution includes further sessions such as HOL-Analysis. The Archive of Formal Proofs publishes additional developments.

- [HOL](https://isabelle.in.tum.de/library/HOL/HOL/) — Isabelle’s higher-order logic theories.
- [HOL-Analysis](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/) — real and complex analysis.
- [Archive of Formal Proofs](https://www.isa-afp.org/entries/Graph_Theory.html) — contributed sessions such as Graph Theory.

### Build and check a library

The installed HOL heap supplies prebuilt `HOL` to dependent sessions. Use `-D` to build the sessions registered by a directory's `ROOT` or `ROOTS` files. Keep each `ROOT` file and its imports together. For an AFP development, use the matching Isabelle release and register any required session directories as described by AFP. [Isabelle session build manual](https://isabelle.in.tum.de/library/Doc/System/Sessions.html) · [Using AFP](https://devel.isa-afp.org/help/)

```bash
# Build the sessions registered for this directory.
isabelle build -o quick_and_dirty=false -D ./my-library

# Check a project whose ROOT starts with the session you want to check.
itpeval eval --prover isabelle --task-dir ./my-library
```

The ITPEval command selects the first session in the top-level `ROOT` and uses a private build home. Keep dependencies available to that session. This file-check command can enable `quick_and_dirty` when it sees `sorry`. For a proof-completion verdict, use a [strict proof task](../reference/task-manifests.md). The extractor starts the installed `HOL` heap and loads the entry theory.

### Extract a library

The bundled `Sample.thy` imports `Base.thy`, which imports `Main` from HOL. The lemma uses a locale assumption to show that doubling a positive natural preserves positivity.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "isabelle/library"
output = Path("build/library/isabelle")
library = prepare_project("isabelle", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "Sample.thy", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "Sample.bounded.twice_positive")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `kernel_checked`. Isabelle checked the theorem in its locale, so its statement carries the locale assumptions.

## Proof completion

Inside the locale, prove `p` using its named assumption `premise: p`. Replace the underlined fragment.

<figure class="proof-listing" data-listing="isabelle" data-proof="by (rule FalseE)" markdown="1">

<figcaption markdown="span"><strong>Isabelle/HOL</strong> Starting proof in Hello.thy</figcaption>

```isabelle
(* The proof method on the second line must establish p. *)
lemma itpeval_target: p
  by (rule FalseE)
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice isabelle
code build/practice/isabelle
```

1. Open `Hello.thy` and run **Terminal → Run Task → ITPEval: Check saved proof**. False elimination leaves a goal of False, which the locale does not supply.
2. Find `by (rule FalseE)` inside `itpeval_target` and replace it with `by (rule premise)`. The named assumption matches the goal directly.
3. Save and rerun the task. The terminal prints `isabelle · itpeval_target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/isabelle/completion/Hello.thy)

For live PIDE feedback, open the theory with the Isabelle distribution’s `isabelle vscode` launcher or Isabelle/jEdit. [Isabelle/VSCode launcher](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Tools/VSCode/src/vscode_main.scala)

[Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover isabelle --show-attempts \
  --cache ./cache --output ./evidence/isabelle
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare isabelle --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/isabelle/model.jsonl --model claude-sonnet-4-6
```

## See also


[Isa-REPL proof steps and state handles](../runtime/isa-repl.md)

[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/isabelle)

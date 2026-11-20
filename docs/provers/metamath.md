# Metamath

Metamath verifies proofs against the axioms and rules in a database. The same verifier can check databases based on different logics. [Project documentation](https://us.metamath.org/)

## How proof checking works

A database declares its symbol vocabulary, hypotheses and assertions. In set.mm these give you classical logic and ZFC set theory. Other databases can start with different rules. A `$p` statement includes the claim and a proof written as labels that refer to hypotheses or earlier assertions.

The verifier works through the labels with a stack. A hypothesis adds an expression. An assertion consumes the hypotheses it needs, checks a substitution and puts the resulting conclusion back on the stack. A line such as `$d x y $.` requires substitutions to respect distinct variables. At the end, the stack must contain just the expression the theorem claims. [Metamath book, proof verification](https://us.metamath.org/downloads/metamath.pdf)

## Read a proof

Metamath databases express definitions using assertions. For example, set.mm’s `df-ne` defines “A is unequal to B” to mean “it is false that A equals B.” Its source has the form `df-ne $a … $.`. In the small database below, `pair-dv` is an assumed rule. [Definition of inequality in set.mm](https://us.metamath.org/mpeuni/df-ne.html) · [Open base.mm](../../itpeval/tests/fixtures/projects/metamath/library/base.mm)

<figure class="proof-listing" data-listing="metamath" data-proof="( pair-dv ) ABC" markdown="1">

<figcaption markdown="span"><strong>Metamath</strong> [client.mm](../../itpeval/tests/fixtures/projects/metamath/library/client.mm)</figcaption>

```metamath
$( The assertion pair-dv requires x and y to be distinct. $)
${ $d x y $.
  pair-rule $p |- pair x y $= ( pair-dv ) ABC $.
$}
```

</figure>

**The claim.** `pair-rule` is the label. The expression between `$p` and `$=` is the assertion to prove, `|- pair x y`. The preceding `$d x y $.` requires the variables to be distinct.

**The proof.** The compressed proof is `( pair-dv ) ABC`, between `$=` and `$.`. In this example A refers to the type hypothesis for `x`, B to the one for `y`, and C to the listed assertion `pair-dv`.

Supply the two variables and apply the existing pair rule. Its distinct-variable requirement is satisfied by the local declaration, and its conclusion matches the goal.

<details markdown="1">
<summary>What happens if the proof supplies x twice to pair-dv?</summary>

The rule requires its two variables to stay distinct after substitution. Supplying `x` for both violates that requirement. Declaring `$d x y $.` permits the substitution that uses `x` and `y` in their separate positions.

</details>

## Use your own project

Use a `.mm` database as the entrypoint. Keep any `$[ ... $]` includes at the same relative paths. A project can use its own database and axioms, including ones different from set.mm.

For a full database, use `--context-storage compact` to keep visibility references in the export. The full `set.mm` example includes native verification and proof-stack traces. [Large Metamath database walkthrough](../guides/extract-and-build-a-dataset/extract-a-library.md#extract-a-large-metamath-database)

Check a source file with `itpeval eval --prover metamath --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset metamath --project ./my-project \
  --entrypoint client.mm --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `metamath --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

A Metamath database supplies its axioms and syntax. set.mm develops classical mathematics and iset.mm develops intuitionistic mathematics. Projects can supply their own database and included files.

- [set.mm](https://us.metamath.org/mpeuni/mmset.html) — classical logic and ZFC set theory.
- [iset.mm](https://us.metamath.org/ileuni/mmil.html) — intuitionistic logic and constructive set theory.

Keep included files at the paths named by `$[ ... $]`. Select the file that brings those includes together as the entrypoint. The extractor resolves dependencies from the database and its included files.

### Extract a library

The example contains the dependency closure of the set.mm assertion `a1i`. Its client separately exercises a disjoint-variable rule from a local database.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "metamath/library"
output = Path("build/library/metamath")
library = prepare_project("metamath", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "client.mm", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "pair-rule")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `proof_verified`. Metamath verified the compressed proof using the included assertion and its distinct-variable condition.

## Proof completion

Prove `|- pair x y` by supplying the labels after `$=` and before `$.`. Replace the underlined fragment.

<figure class="proof-listing" data-listing="metamath" data-proof="vx vx distinct" markdown="1">

<figcaption markdown="span"><strong>Metamath</strong> Starting proof in hello.mm</figcaption>

```metamath
$( The labels after the equality marker form the proof. $)
itpeval-target $p |- pair x y $= vx vx distinct $.
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice metamath
code build/practice/metamath
```

1. Open `hello.mm` and run **Terminal → Run Task → ITPEval: Check saved proof**. The starting sequence supplies x twice to a rule that requires distinct variables.
2. Find `vx vx distinct` inside `itpeval-target` and replace it with `vx vy distinct`. The two type hypotheses supply x and y in order, and the axiom distinct yields the target expression.
3. Save and rerun the task. The terminal prints `metamath · itpeval-target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/metamath/completion/hello.mm)

The Metamath extension uses its language server to display proofs and diagnostics for .mm databases. [Metamath for VS Code](https://marketplace.visualstudio.com/items?itemName=tirix.metamath)

[Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover metamath --show-attempts \
  --cache ./cache --output ./evidence/metamath
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare metamath --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/metamath/model.jsonl --model claude-sonnet-4-6
```

## See also


[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/metamath)

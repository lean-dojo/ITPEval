# Agda

Agda is a dependently typed programming language and proof assistant. To prove a proposition, define a value whose type expresses it. [Project documentation](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html)

## How proof checking works

Agda builds on Martin-Löf dependent type theory. A type can contain a value, such as the length of a vector. An equality such as `true ≡ true` is a type too. Its constructor `refl` provides evidence when the two sides agree by computation. Pattern matching can refine what you know about the indices of a type and help determine what the remaining proof must produce.

Agda typechecks the proof alongside the rest of the module. It checks the positivity of inductive data definitions and the termination of recursive functions. The example uses `--safe`, which rules out features such as unrestricted postulates and turning off termination checking. Check the module’s options and imports when deciding what a typecheck means. [Safe Agda](https://agda.readthedocs.io/en/latest/language/safe-agda.html)

## Read a proof

In `Algebra.agda`, `idNat : Nat → Nat` gives a function’s type and `idNat n = n` gives its definition. The library example `first = idNat zero` therefore constructs a number. Below is an equality proof from the separate completion example. [Open Algebra.agda](../../itpeval/tests/fixtures/projects/agda/library/Algebra.agda)

<figure class="proof-listing" data-listing="agda" data-proof="refl" markdown="1">

<figcaption markdown="span"><strong>Agda</strong> [Hello.agda](../../itpeval/tests/fixtures/projects/agda/completion/Hello.agda)</figcaption>

```agda
-- The first line states the equality. The second supplies its proof.
itpeval-target : true ≡ true
itpeval-target = refl
```

</figure>

**The claim.** Agda expresses a proposition as a type. The type after the colon, `true ≡ true`, asks for evidence that the Boolean value `true` equals itself.

**The proof.** The defining equation on the next line supplies that evidence. The entire proof term to the right of `=` is `refl`, the constructor for reflexive equality.

Both sides are the same Boolean value. The equality constructor therefore has exactly the requested type. The name `itpeval-target` can be used wherever a proof of this equality is needed.

<details markdown="1">
<summary>Why does false fail even though both sides of the equality are Boolean values?</summary>

`false` is a value of type `Bool`. The proof has to inhabit another type, `true ≡ true`. `refl` has that type because both sides are the same value.

</details>

## Use your own project

Use an `.agda` file and make its path match its module name. Pass the source roots of imported modules with `libraries`. If a project uses Cubical Agda, match the library and toolchain versions and keep the module’s language options.

Check a source file with `itpeval eval --prover agda --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset agda --project ./my-project \
  --entrypoint Client.agda --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `agda --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

Agda ships primitive and builtin modules. The Agda standard library and the Cubical library are separately versioned dependencies.

- [Agda.Builtin](https://agda.readthedocs.io/en/stable/language/built-ins.html) — builtin types and operations.
- [Standard Library](https://github.com/agda/agda-stdlib) — data types, algebra and proofs.
- [Cubical Agda library](https://github.com/agda/cubical) — cubical type theory and homotopy type theory.

### Build and check a library

Install the source release that matches your Agda version. Agda can typecheck imported modules as it loads them, so you can start with the library's sources. To typecheck the standard library as a whole, use its generated umbrella module from the standard-library checkout. [Agda library management](https://agda.readthedocs.io/en/stable/tools/package-system.html) · [Standard library test workflow](https://github.com/agda/agda-stdlib/blob/v2.3/.github/workflows/ci-ubuntu.yml#L153-L159)

```bash
# Generate the umbrella module, including deprecated modules, using Cabal.
cabal run GenerateEverything -- --include-deprecated
agda -WnoUserWarning Everything.agda
```

For an ITPEval client importing modules such as `Data.Nat`, pass the standard library's `src` directory as a named library. Bind all required source roots explicitly and preserve any language options in the files. The checker and extractor use these roots with `-i`. [Check a client with external imports](../reference/python/checking.md#check-a-file-with-external-imports)

### Extract a library

The bundled project includes the standard library’s `Level.agda`. The client also imports a local algebra module and applies its identity function to zero.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "agda/library"
output = Path("build/library/agda")
library = prepare_project("agda", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "Client.agda", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "Client.first")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `typechecked`. Agda typechecked first as a definition of type Nat. Here the extracted term is data.

## Proof completion

Supply the right-hand side of a definition whose type is the equality `true ≡ true`. The editable text includes the equals sign. Replace the underlined fragment.

<figure class="proof-listing" data-listing="agda" data-proof="= false" markdown="1">

<figcaption markdown="span"><strong>Agda</strong> Starting proof in Hello.agda</figcaption>

```agda
-- The first line states the equality. The next supplies its proof.
itpeval-target : true ≡ true
itpeval-target = false
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice agda
code build/practice/agda
```

1. Open `Hello.agda` and run **Terminal → Run Task → ITPEval: Check saved proof**. The value false is a Boolean. The expected type is an equality.
2. Find `= false` inside `itpeval-target` and replace it with `= refl`. refl is a term of the required equality type.
3. Save and rerun the task. The terminal prints `agda · itpeval-target · accepted`.

The community agda-mode extension can load the module and show the types and contexts of interaction holes. [agda-mode for VS Code](https://github.com/banacorn/agda-mode-vscode)

[Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover agda --show-attempts \
  --cache ./cache --output ./evidence/agda
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare agda --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/agda/model.jsonl --model claude-sonnet-4-6
```

## See also


[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/agda)

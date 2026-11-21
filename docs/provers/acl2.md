# ACL2

ACL2 is both a functional programming language in the Common Lisp family and an automated theorem prover. You submit definitions and theorem statements as events. [Project documentation](https://www.cs.utexas.edu/~moore/acl2/)

## How proof checking works

ACL2 uses first-order logic. A theorem can quantify over Lisp values such as lists, numbers and symbols. When a function recurses over a list, the prover can use a related induction scheme and simplify each case using definitions and rewrite rules it already knows.

The logical world records definitions, previously proved theorems and enabled rules. `defthm` asks ACL2 to prove a formula in that world. After a successful proof, ACL2 admits the theorem and can use it in future proofs according to its rule classes. Use `:hints` to suggest a lemma or an induction when the automatic search needs direction. [Events and the ACL2 logical world](https://acl2.org/doc/index-seo.php?xkey=ACL2____EVENTS)

## Read a proof

The earlier event `(defun my-id (x) x)` defines a function with argument `x` and body `x`. It returns its input.

<figure class="proof-listing" data-listing="acl2" markdown="1">

<figcaption markdown="span"><strong>ACL2</strong> [events.lisp](../../itpeval/tests/fixtures/projects/acl2/library/events.lisp)</figcaption>

```acl2
; ACL2 proves this equation using the definition of my-id.
(defthm my-id-id (equal (my-id x) x))
```

</figure>

**The claim.** The first argument of `defthm` is the theorem name `my-id-id`. Its formula `(equal (my-id x) x)` says that applying the function gives back the original value for every `x`.

**The proof.** This event has no handwritten proof script. Submitting `defthm` asks ACL2 to prove the formula automatically. The checker’s admission of the event records success. Other events can supply `:hints` to guide the prover.

Expand `(my-id x)` using the function body. The equality becomes `(equal x x)`, which holds by reflexivity.

<details markdown="1">
<summary>Where is the proof text if an ACL2 theorem has no hints?</summary>

ACL2 searches for a proof from its current world when it processes the event. Read its proof transcript to see the rules it used. The source event supplies the formula and any hints you elected to write.

</details>

## Use your own project

Use a Lisp source file with ACL2 events. Keep package declarations, local books and their certification prerequisites in order. For `:dir :system` imports, install the matching community books with the selected ACL2 build.

Check a source file with `itpeval eval --prover acl2 --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset acl2 --project ./my-project \
  --entrypoint events.lisp --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `acl2 --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

The ACL2 Community Books include the standard library under std/ and developments such as Arithmetic-5. Your project can also include its own certified books.

- [Community Books](https://github.com/acl2/acl2/tree/master/books) — certified books distributed with ACL2.
- [Standard Library](https://github.com/acl2/acl2/tree/master/books/std) — lists, strings and other common data types.
- [Arithmetic-5](https://github.com/acl2/acl2/tree/master/books/arithmetic-5) — arithmetic rewrite rules and proof support.

### Build and check a library

Reuse certified Community Books from the matching ACL2 installation. To build a development, certify its books with the project's build targets or ACL2's `cert.pl`, which follows book dependencies. In the Community Books tree, `make basic` certifies the basic set and `make all` runs the full certification target. Use the matching ACL2 executable for certification. [ACL2 book tools](https://github.com/acl2/acl2/tree/master/books/build) · [Community Books build targets](https://github.com/acl2/acl2/blob/master/books/GNUmakefile)

```bash
# Import the certified books in check.lsp and have it admit a client theorem.
itpeval eval --prover acl2 --task-dir ./my-project --task-file check.lsp
```

Use `:dir :system` for installed system books. Keep local books and their certificates at the paths the script imports. The extractor uses the prepared project and the installed books tree.

### Extract a library

The bundled project includes the certified `std/lists/append` book. It also defines `my-id` and proves that applying it returns the argument.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "acl2/library"
output = Path("build/library/acl2")
library = prepare_project("acl2", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "events.lisp", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "MY-ID-ID")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `admitted_event`. ACL2 admitted the defthm event when it processed the book.

## Proof completion

Prove that the first element of `(cons x y)` is `x`. You edit the hints attached to `defthm`, and ACL2 searches for the proof. Replace the underlined fragment.

<figure class="proof-listing" data-listing="acl2" data-proof=":hints ((&quot;Goal&quot; :use itpeval-unknown))" markdown="1">

<figcaption markdown="span"><strong>ACL2</strong> Starting proof in hello.lsp</figcaption>

```acl2
; Edit the hint supplied to the theorem prover.
(defthm itpeval-target
  (equal (car (cons x y)) x)
  :hints (("Goal" :use itpeval-unknown))
  :rule-classes nil)
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice acl2
code build/practice/acl2
```

1. Open `hello.lsp` and run **Terminal → Run Task → ITPEval: Check saved proof**. The hint asks ACL2 to use an unknown theorem.
2. Find `:hints (("Goal" :use itpeval-unknown))` inside `itpeval-target` and replace it with `:hints nil`. An empty hint list lets ACL2 prove this elementary car/cons equation on its own.
3. Save and rerun the task. The terminal prints `acl2 · itpeval-target · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/acl2/completion/hello.lsp)

Use the VS Code task to submit the event and read the ACL2 transcript. For interactive subgoals, ACL2 also provides a proof builder in its own command loop. [ACL2 proof builder](https://acl2.org/doc/index-seo.php?xkey=ACL2____PROOF-BUILDER)

[Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover acl2 --show-attempts \
  --cache ./cache --output ./evidence/acl2
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare acl2 --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/acl2/model.jsonl --model claude-sonnet-4-6
```

## See also


[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/acl2)

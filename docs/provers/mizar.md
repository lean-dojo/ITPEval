# Mizar

Mizar checks mathematical articles written in a language shaped like textbook proofs. A typical article introduces definitions and then justifies its claims with earlier results. [Project documentation](https://mizar.uwb.edu.pl/)

## How proof checking works

The Mizar Mathematical Library builds on classical first-order logic and Tarski–Grothendieck set theory. An article can still describe objects using mathematical types, such as a set or a natural number, and the verifier uses types, definitions and registered properties when it checks justifications.

The `environ` section selects vocabulary, notation, constructors and imported results. The Accommodator prepares that environment, then the verifier checks the article’s text against it. A line such as `thus thesis by A1;` proves the current goal by citing a previously named fact. The verifier checks that the cited facts justify the claim. [Mizar verifier and the article environment](https://mizar.uwb.edu.pl/system/verifier.html)

## Read a proof

In a Mizar `definition` block, `func {y} -> set means` introduces the singleton of `y`. Its defining condition says an object belongs to this set exactly when it equals `y`. [Read the singleton definition](https://mizar.uwb.edu.pl/version/current/html/tarski.html#D1)

<figure class="proof-listing" data-listing="mizar" data-proof="by Th1" markdown="1">

<figcaption markdown="span"><strong>Mizar</strong> [sample.miz](../../itpeval/tests/fixtures/projects/mizar/library/sample.miz)</figcaption>

```mizar
:: Th2 cites the earlier theorem Th1 to justify the same conclusion.
theorem Th1: for x being object holds x = x;
theorem Th2: for x being object holds x = x by Th1;
```

</figure>

**The claim.** In the second theorem, the text following `Th2:` and preceding `by` says that every object equals itself.

**The proof.** The short justification is `by Th1`. The completion exercise below shows Mizar’s longer `proof` … `end;` form.

The preceding theorem `Th1` already establishes this exact universal claim. Citing it justifies `Th2` immediately.

<details markdown="1">
<summary>How does the verifier know which Th1 the proof cites?</summary>

`Th1` is the label of an earlier theorem in the same article. The verifier resolves the name in the article context. For a theorem imported by the environment, the citation can include its library article and theorem number.

</details>

## Use your own project

Use a `.miz` article and keep its `environ` section. Use a Mizar library installation compatible with the article’s imports. Point the `mizfiles` library role at the configured tree when using a separate installation.

Check a source file with `itpeval eval --prover mizar --file PATH`. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

For extraction, choose an entrypoint relative to the project root.

```bash
# Replace the directory and entrypoint with the paths for your project.
itpeval dataset mizar --project ./my-project \
  --entrypoint sample.miz --output ./dataset
```

For a prepared project, pass `--lock PATH` in place of `mizar --project ./my-project`. [Configure a project](../guides/environment-manifest.md)

## Libraries

The Mizar Mathematical Library (MML) accompanies the verifier. An article selects the vocabulary, constructors and theorems it needs through its environ section.

- [Mizar Mathematical Library](https://mizar.uwb.edu.pl/library/) — the MML article collection.
- [REAL_1](https://mizar.uwb.edu.pl/version/current/html/real_1.html) — an MML article about real numbers.
- [GROUP_1](https://mizar.uwb.edu.pl/version/current/html/group_1.html) — an MML article on groups.

Mizar’s Accommodator resolves an article’s vocabulary, notation and imports against the installed MML. To use a different installation, pass the root of the installed library as `mizfiles`.

### Extract a library

The bundled project includes the original `REAL_1` article from MML 5.106.1517. Its client uses the accommodated environment and a preceding local theorem, `Th1`.

After installation, run the Python examples in order. [Installation](../runtime/toolchains.md)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.corpus.datasets import export_dataset
from itpeval.corpus.example import LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project

# Prepare the source files and the prover that will load them.
project = LIBRARY / "mizar/library"
output = Path("build/library/mizar")
library = prepare_project("mizar", project, prefix=default_prefix(), cache=Path("build/itpeval-cache"))
# Export the records and print the files the extractor actually processed.
bundle, premises = export_dataset(library, "sample.miz", output)
print("Processed files:", bundle.report["succeeded"])
```

### Find a declaration in the export

Join the declaration to its premise record using `declaration_id`.

```python
# Find this declaration in the export and read the status supplied by the prover.
rows = read_jsonl(bundle.path / "declarations.jsonl")
target = next(row for row in rows if row["name"] == "SAMPLE.Th2")
print(target["name"], target["checking_status"])
print(target["statement"])
```

The checker status is `article_checked`. Mizar successfully checked the article containing this theorem in its declared environment.

## Proof completion

After introducing an arbitrary set `x`, finish the proof of `x = x`. The editable justification includes its terminating semicolon. Replace the underlined fragment.

<figure class="proof-listing" data-listing="mizar" data-proof="thus contradiction;" markdown="1">

<figcaption markdown="span"><strong>Mizar</strong> Starting proof in hello.miz</figcaption>

```mizar
:: Edit the justification after the variable is introduced.
theorem Th1:
  for x being set holds x = x
proof
  let x be set;
  thus contradiction;
end;
```

</figure>

### Complete it yourself in VS Code

```bash
# Create a working copy with a failing proof and a task for the native checker.
itpeval practice mizar
code build/practice/mizar
```

1. Open `hello.miz` and run **Terminal → Run Task → ITPEval: Check saved proof**. There is no contradiction to conclude from the assumptions.
2. Find `thus contradiction;` inside `Th1` and replace it with `thus thesis;`. The thesis is x = x, which the verifier can justify by reflexivity.
3. Save and rerun the task. The terminal prints `mizar · Th1 · accepted`. [Completed source](../../itpeval/tests/fixtures/projects/mizar/completion/hello.miz)

The Mizar extension offers article compilation and syntax highlighting with a configured local verifier. [Mizar extension](https://marketplace.visualstudio.com/items?itemName=fpsbpkm.mizar-extension)

Read the current thesis and native diagnostics from Python as you revise the article. [Use native goals in an agent](../guides/verification-and-learning/search-with-an-agent.md#use-native-goals-in-an-agent)

### Watch the prerecorded attempts

The episode records the native checker’s reply to each edit.

```bash
# Display the actual candidates and verdicts, then print the saved episode path.
python -m itpeval.learning.example --prover mizar --show-attempts \
  --cache ./cache --output ./evidence/mizar
```

### Ask a model to complete the proof

Run this from the repository checkout after setting up a provider. [Provider setup](../benchmarks/translation.md#quick-start)

```bash
# Prepare the fixed theorem and read its environment lock.
lock=$(itpeval prepare mizar --cache ./cache | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')
# Send the exercise to the configured model and check its reply locally.
python -m eval.pipeline.completion "$lock" ./evidence/mizar/model.jsonl --model claude-sonnet-4-6
```

## See also


[Compare supported operations](../reference/capabilities.md) · [Native adapter sources and version script](../../itpeval/provers/mizar)

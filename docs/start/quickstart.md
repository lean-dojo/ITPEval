# Quickstart

Check a file from Python or the command line, then set up a fixed theorem that you or an agent can try to prove. [Install ITPEval and Lean](#installation) · [Explore all features](features.md)

## Check a file

Save the following as `MyProof.lean` in your working directory. The proof uses Lean’s built-in natural numbers, so the file is ready to check on its own. For another prover, start with its file format and use its ID in place of `lean4`. [Find your prover](../provers/index.md)

```lean4
-- The two sides reduce to the same natural number.
theorem two_plus_two : 2 + 2 = (4 : Nat) := by
  rfl
```

<div class="interface-switch" data-label="Check a file" markdown="1">
<section class="interface-panel" markdown="1">

### Check a file in Python

```python
from pathlib import Path

from itpeval.itp import run_itp

# Run Lean on the saved source file.
result = run_itp(prover="lean4", code_path=Path("MyProof.lean"))
print(result.ok)
```

```text
True
```

`result.ok` reports whether the prover accepted the file. Inspect `result.stdout` and `result.stderr` for its messages.

</section>
<section class="interface-panel" markdown="1">

### Check a file at the command line

```bash
# Check the saved Lean file and print the result.
itpeval eval --prover lean4 --file MyProof.lean
```

</section>
</div>

Have a project with imports? Keep the source files and their library configuration together. For example, an Isabelle session needs its theories and `ROOT` file, and a Metamath database may include other files. [Check your own project](../guides/work-with-a-library.md#check-a-file-you-already-have)

## The task

For proof completion, fix the statement before asking for a proof. The bundled task asks you to prove that every natural number equals itself, $\forall x \in \mathbb{N},\; x = x$. The candidate supplies the line after `by`. [See how to read a theorem](reading-proofs.md)

```lean4
-- The statement stays fixed. The candidate supplies the proof after "by".
theorem itpeval_target (x : Nat) : x = x := by
  rfl
```

## Verify a candidate

<div class="interface-switch" markdown="1">
<section class="interface-panel" markdown="1">

### Python

```python
import os
from pathlib import Path

from itpeval.backends.registry import curated_project, get_backend
from itpeval.environments import prepare_project
from itpeval.verification import verify

# Lock the sources and the installed Lean compiler.
prefix = Path(os.getenv("ITPEVAL_PREFIX", Path.home() / ".local/share/itpeval/toolchains/current"))
project = prepare_project("lean4", curated_project("lean4"), prefix=prefix, cache=Path("cache"))

# Read the target from the project's manifest, then submit a proof fragment.
task = get_backend("lean4").build_task(project)
result = verify(task, "rfl", prepared=project)
print(result.checker_outcome, result.task_success)
```

```text
accepted True
```

`checker_outcome` records the checker’s verdict. `task_success` tells you whether the candidate proved the required theorem and met the task’s other conditions. Try `"exact Eq.refl x"` for another valid proof.

</section>
<section class="interface-panel" markdown="1">

### Command line

```bash
# With no project argument, prepare the bundled Lean task.
itpeval prepare lean4 --cache ./cache > project.json
lock=$(python -c 'import json; print(json.load(open("project.json"))["lock_path"])')

# Reuse that lock to check a candidate and print its evidence as JSON.
itpeval verify-task --lock "$lock" --candidate 'rfl'
```

The JSON record includes the checker’s verdict, task success and diagnostics. Try `--candidate 'exact False.elim'` to see Lean’s type error. Add `--summary` for a short terminal result.

</section>
</div>

## Installation

Choose your setup for [macOS](../runtime/toolchains.md#macos), [Windows](../runtime/toolchains.md#windows), or [Linux](../runtime/toolchains.md#linux). Each path installs the Python package and Lean, then sets `ITPEVAL_PREFIX` for the examples above.

<!-- release-downloads -->

## Use a library project

Each prover guide starts with native source and shows how to load its project, extract declarations and try a proof. You can also open an exercise in VS Code and check the saved file as you edit. [Prover guides](../provers/index.md) · [VS Code exercises](proof-completion.md#choose-your-prover)

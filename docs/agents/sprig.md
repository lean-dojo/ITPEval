# Sprig, a proof-producing search agent

Give Sprig a propositional goal and its premises. It searches for resolution steps that prove the goal, and a separate checker tests those steps against the original problem. Both programs use the Python standard library. [Download Sprig and the sample problem](../assets/sprig.zip)

## What does it prove?

Suppose a door can be opened with a key or a code. You have at least one of them. Can you open the door?

| Premise | Clause |
|---|---|
| You have a key or a code | $K \lor C$ |
| A key opens the door | $\neg K \lor O$ |
| A code opens the door | $\neg C \lor O$ |

Sprig starts by adding $\neg O$ to the premises. To resolve $K \lor C$ with $\neg K \lor O$, remove the complementary literals $K$ and $\neg K$, then combine the remaining literals to get $C \lor O$. Resolve that with $\neg C \lor O$ to get $O$. Resolving $O$ with $\neg O$ leaves no literals. This empty clause marks a contradiction, so the original premises entail $O$.

<details markdown="1">
<summary>What happens if the code no longer opens the door?</summary>

Remove the clause $\neg C \lor O$. Then a person with only a code might fail to open the door. In that case set $C$ to true and both $K$ and $O$ to false. The two remaining premises hold and the goal fails.

</details>

## Generate and check a certificate

Run this from the repository root. The JSON problem uses one list per clause, with a tilde for negation. The goal is also a clause.

```bash
# Keep the problem fixed and write the new certificate to the build directory.
sprig=examples/prover-adapters/sprig
problem="$sprig/hello/problem.json"
certificate=build/sprig/found.json
mkdir -p build/sprig

# Search for a certificate, then replay its steps with the independent checker.
python "$sprig/sprig.py" prove "$problem" > "$certificate"
python "$sprig/sprig.py" check "$problem" "$certificate"
```

The checker prints `accepted`. Each step names the positive clause, the negative clause, and their shared atom. For example, `[0, 1, "Key"]` resolves the first two premises on `Key`. Numbering starts at zero with premises in file order, then unit clauses for distinct negated goal literals in lexicographic order, then derived clauses. [Sample certificate](../../examples/prover-adapters/sprig/hello/proof.json) · [Sample problem](../../examples/prover-adapters/sprig/hello/problem.json)

Sprig tries shorter clauses first, breaks ties by insertion order, and indexes pairs with complementary literals. If it exhausts the inferences without a contradiction, the premises can hold while the goal is false. If `--max-inferences` stops it early, it reports `unknown`. [Search implementation](../../examples/prover-adapters/sprig/sprig.py) · [Prover9's given-clause loop](https://prover9.org/manual-2026/loop.html)

You can also give the checker a certificate you wrote by hand. It reconstructs each step and requires the empty clause. [Checking kernel](../../examples/prover-adapters/sprig/kernel.py)

## Run it through ITPEval

Point `ITPEVAL_ADAPTER_DIR` at the parent of `sprig` to check its `hello/` fixture.

```bash
# Discover local adapters for this invocation and run Sprig's own fixture.
ITPEVAL_ADAPTER_DIR="$PWD/examples/prover-adapters" ./itpeval/bin/itpeval check --task hello sprig
```

Place the original problem beside the generated certificate so the adapter can read both.

```python
import os
from pathlib import Path
from shutil import copyfile
from itpeval.itp import run_itp

# Select the adapter and stage the fixed problem beside the generated certificate.
adapters = Path("examples/prover-adapters").resolve()
os.environ["ITPEVAL_ADAPTER_DIR"] = str(adapters)
project = Path("build/sprig")
copyfile(adapters / "sprig/hello/problem.json", project / "problem.json")
# The adapter reads problem.json from the same directory as found.json.
result = run_itp(prover="sprig", task_dir=project, task_file=Path("found.json"))
print(result.ok, result.stdout.strip())
```

## Verify a locked task and extract it

Sprig's typed adapter locks the original `problem.json` and lets you replace `proof.json`. Its kernel reports the precise goal, hashes of the inputs, and the premises used by the proof. The same task supports document forks, saved checkpoints, and proof episodes. [Read the completion manifest](../../examples/prover-adapters/sprig/hello/completion.json)

```bash
# Use the local adapter and prepare its sample theorem.
export ITPEVAL_ADAPTER_DIR="$PWD/examples/prover-adapters"
sprig="$ITPEVAL_ADAPTER_DIR/sprig"
lock=$(itpeval prepare sprig --project "$sprig/hello" --cache build/sprig/cache \
  | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')

# Check the existing certificate and save it for replay.
itpeval verify-task --lock "$lock" --candidate-file "$sprig/hello/proof.json" \
  --save-checkpoint build/sprig/proof-checkpoint.json --summary
itpeval verify-task --lock "$lock" --checkpoint build/sprig/proof-checkpoint.json --summary

# Extract the three premises and the goal into the standard dataset format.
itpeval dataset --lock "$lock" --entrypoint problem.json --output build/sprig/dataset
```

Try `build/sprig/found.json` as `--candidate-file`. The lock keeps the goal fixed. Open the premise export to see which premises the proof uses. [Verification and extraction result](../../benchmarks/runtime/external-adapter-sprig.json)

Use the same pattern for your prover. [Integration skill](skills/integrate-a-prover/SKILL.md)

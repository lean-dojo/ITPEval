# Run a solver on TPTP

<span id="solve-a-tptp-problem"></span>

Save the example as `socrates.p`. Since every human is mortal and Socrates is human, the conjecture is that Socrates is mortal. [TPTP language guide](https://tptp.org/UserDocs/QuickGuide/)

```text
% Give the solver the premises and the claim to prove.
fof(human_mortal, axiom, ! [X] : (human(X) => mortal(X))).
fof(socrates_human, axiom, human(socrates)).
fof(mortal_socrates, conjecture, mortal(socrates)).
```

```bash
# Run locally with a 20-second wall deadline and keep the result.
itpeval atp solve e socrates.p --timeout-s 20 --output build/socrates-atp.json
```

Use `vampire` in place of `e` to switch solvers. ITPEval looks on your path and in the toolchain prefix, including an installed Isabelle's components. Use `--executable PATH` to select a build. For problems with includes, set `--tptp-root DIR` to the directory containing the input and includes. [E](https://github.com/eprover/eprover) · [Vampire](https://github.com/vprover/vampire)

The receipt includes the solver version and executable hash, inputs, budgets, diagnostics, native SZS status, and returned proof or model text. `Theorem` applies to the submitted axioms and conjecture. A timeout has its own outcome. [SZS statuses](https://szs.tptp.org/)

## Use Python

```python
from pathlib import Path

from itpeval.atp import solve_tptp
from itpeval.core.types import Budgets

# Read the solver verdict and retain its proof artifact.
result = solve_tptp(Path("socrates.p"), solver="e", budgets=Budgets(timeout_s=20))
print(result.native_status, result.certificate_kind)
```

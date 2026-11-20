# Mathlib and CSLib

This example uses Mathlib’s definition of a formal language and a theorem from CSLib. A language is a set of words. Over an empty alphabet, the only possible word is the empty word $\varepsilon$, so any language $L$ is one of these two sets.

$$
L = \varnothing \quad\text{or}\quad L = \{\varepsilon\}.
$$

In Lean, `0` denotes the empty language and `1` contains only $\varepsilon$. The proof applies the CSLib theorem to `L`. [Mathlib language theory](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Computability/Language.lean) · [CSLib language theory](https://github.com/leanprover/cslib/blob/22b39634cb3dc80d829683ad1f65c5680b722309/Cslib/Computability/Languages/Language.lean)

```lean4
import Mathlib.Computability.Language
import Cslib.Computability.Languages.Language

/-- Over an empty alphabet the only possible word is the empty list. -/
theorem emptyAlphabetLanguage (L : Language Empty) : L = 0 ∨ L = 1 :=
  Language.eq_zero_or_one_ofIsEmpty L
```

## Build the imports

Run this from an ITPEval checkout with the package installed and Elan on your path. The CSLib checkout pins the Lean compiler and selects a compatible Mathlib revision through its Lake manifest. This example uses Lean 4.36.0. If you already have this CSLib build, set `CSLIB` to its location and skip the clone and build.

```bash
# Build just the requested target and the dependencies it imports.
CSLIB="$PWD/build/lean-libraries/cslib"
mkdir -p "$(dirname "$CSLIB")"
revision=22b39634cb3dc80d829683ad1f65c5680b722309
if [ ! -d "$CSLIB" ]; then
  git clone https://github.com/leanprover/cslib.git "$CSLIB" || exit 1
  git -C "$CSLIB" checkout --detach "$revision" || exit 1
fi
# Leave an existing checkout on the revision its owner selected.
[ "$(git -C "$CSLIB" rev-parse HEAD)" = "$revision" ] || exit 1
(cd "$CSLIB" && lake build Cslib.Computability.Languages.Language)
```

## Check the file and read the result

Check the file with the compiler that built its imports. Set `CSLIB` to your checkout path if it differs from the one below.

```bash
CSLIB="$PWD/build/lean-libraries/cslib"
PREFIX="$PWD/build/lean-libraries/toolchains"
# Link the compiler that built the .olean files into this example's prefix.
mkdir -p "$PREFIX/lean4/bin"
compiler=$(cd "$CSLIB" && lean --print-prefix)
ln -sfn "$compiler/bin/lean" "$PREFIX/lean4/bin/lean"

# Check the source and print the names extracted from it.
python examples/lean_libraries/run.py --cslib "$CSLIB" --prefix "$PREFIX" \
  --output ./build/lean-libraries/results
```

The script prints the verdict and the extracted declaration name.

```text
accepted
emptyAlphabetLanguage
```

## Use another Lean library

Build dependencies with Lake and pass all compiled module roots to `prepare_project`, including transitive dependencies. Here, `Words.lean` is the entrypoint. To extract declarations from a dependency, prepare its source tree and select an entrypoint there.

The example script shows the calls to `prepare_project`, `verify` and `extract_project`. For an exercise where a model fills in part of your proof, add a completion manifest. [Runnable Python example](../../../examples/lean_libraries/run.py) · [Proof-completion task format](../../reference/task-manifests.md) · [Lean libraries](../lean4.md#libraries)

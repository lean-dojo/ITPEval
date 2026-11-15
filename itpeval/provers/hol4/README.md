# HOL4 support for ITPEval

This directory contains the best-effort HOL4 adapter used by `ITPEval`.

## What it does

- `install.sh` looks for an existing HOL4 installation or source tree and wires it into `ITPEVAL_PREFIX/hol4`.
- `check.sh` tries to build the bundled `hello/` theory with `Holmake`.
- `hello/` contains the smallest theory file I could use as a smoke test.

## Supported setup paths

The script accepts any of these inputs:

- An existing `hol`/`Holmake` on `PATH`
- A local HOL4 source tree pointed to by `HOL4_HOME`, `ITPEVAL_HOL4_HOME`, or `ITPEVAL_HOL4_SRC`
- A HOL4 binary/source tree already unpacked inside `ITPEVAL_PREFIX/hol4`

## Expected dependencies

HOL4 typically needs:

- Poly/ML
- GNU `make`
- `git` if you want to clone sources locally

If those are missing, the install script prints a short guidance message and exits nonzero.

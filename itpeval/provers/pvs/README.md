# PVS support for ITPEval

This directory contains the best-effort PVS adapter used by `ITPEval`.

## What it does

- `install.sh` installs (or wires) PVS into `ITPEVAL_PREFIX/pvs`.
- `check.sh` looks for `proveit` first, then falls back to a basic `pvs` runtime check.
- `hello/` contains a tiny theory with a ProofLite script.

## Supported setup paths

The install script accepts any of these inputs:

- No input: downloads the pinned official PVS 8.1 GitHub release for the current Linux/macOS architecture and relocates it.
- An existing `pvs` executable on `PATH`
- A downloaded PVS tarball via `PVS_TARBALL` or `ITPEVAL_PVS_TARBALL`
- A local PVS source/install tree pointed to by `PVS_HOME`, `ITPEVAL_PVS_HOME`, or `ITPEVAL_PVS_SRC`

You can override the default GitHub release or provide a full download URL with:

- `ITPEVAL_PVS_RELEASE_TAG` (default `pvs8.1-master-20260624`)
- `ITPEVAL_PVS_RELEASE_BUILD` (default `master-20260624`)
- `ITPEVAL_PVS_TARBALL_URL` (full URL override)

The legacy `ITPEVAL_PVS_VERSION` and `ITPEVAL_PVS_LISP` overrides remain available for old SRI-hosted package names.

## Expected dependencies

For binary installs, PVS commonly wants:

- `emacs`
- `wish` / Tcl-Tk
- a Common Lisp implementation for source builds

For ITPEval batch checks, `emacs` is optional: if `emacs` is missing, the installer patches `PVSPATH` in the PVS scripts and skips Emacs byte compilation.

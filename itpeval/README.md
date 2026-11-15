# ITPEval

`ITPEval` is a lightweight “HumanEval-style” environment harness for Interactive Theorem Provers (ITPs).

Goals:
- Install a set of common ITP toolchains locally (no global system pollution).
- Provide one command to (best-effort) install and one command to smoke-test everything.
- Keep target-prover setup isolated under `itpeval/provers/<name>/`.

## Quickstart (macOS)

`bootstrap-system.sh` targets Amazon Linux 2023 and will not work on macOS. Use the macOS bootstrap instead:

```bash
cd itpeval
./bin/bootstrap-macos.sh   # installs Homebrew deps (opam, gcc, java, ...)
```

### macOS prover compatibility

| Prover | macOS (Apple Silicon / Intel) | Notes |
|--------|-------------------------------|-------|
| Lean 4 | Works | `elan` supports arm64/x86_64 |
| Rocq (Coq) | Works | Requires `opam` (installed by bootstrap) |
| Agda | Works | `ghcup`/`cabal` support macOS |
| Metamath | Works | Builds from C source via Clang |
| HOL Light | Works | Builds via OCaml (installed by bootstrap) |
| HOL4 | Works | Builds Poly/ML and HOL4 from source |
| PVS | Works | Installs the pinned native PVS 8.1 release for arm64/x86_64 |
| Isabelle | Works | `install.sh` selects the macOS tarball automatically |
| ACL2 | Manual | Wire an existing install via `ACL2_HOME` or `ITPEVAL_ACL2_HOME` |
| Mizar | Not supported | The adapter works on Linux/x86; upstream does not provide current macOS binaries |

To install the provers with known macOS support:

```bash
./bin/itpeval install lean4 rocq agda metamath hol-light hol4 pvs isabelle
./bin/itpeval check --task hello \
  lean4 rocq agda metamath hol-light hol4 pvs isabelle
```

#### Isabelle tarball override

`install.sh` auto-selects `Isabelle<version>_macos.tar.gz` on macOS (Isabelle ships a universal build). If the filename ever differs, override it:

```bash
ITPEVAL_ISABELLE_TARBALL=Isabelle2024_macos_arm64.tar.gz ./bin/itpeval install isabelle
```

---

## Quickstart (Amazon Linux 2023)

From the repo root:

```bash
cd itpeval
./bin/bootstrap-system.sh
./bin/itpeval list-provers
./bin/itpeval install \
  lean4 rocq isabelle hol-light acl2 agda hol4 metamath mizar pvs
./bin/itpeval check --task hello \
  lean4 rocq isabelle hol-light acl2 agda hol4 metamath mizar pvs
```

To install/check only a subset:

```bash
./bin/itpeval install agda pvs hol4
./bin/itpeval check --task hello agda pvs hol4
./bin/itpeval run --task hello agda pvs hol4
./bin/itpeval report
```

To evaluate a one-off snippet/file against a single prover:

```bash
./bin/itpeval eval --prover rocq --ensure-installed \
  --code $'Theorem t : 2 + 3 = 5.\nProof. reflexivity. Qed.'
./bin/itpeval eval --prover isabelle --mode snippet --ensure-installed \
  --code 'lemma t: "(2::nat) + 3 = 5" by simp'
```

Install location defaults to `itpeval/_toolchains`, except that repositories
under `/efs` default to `/tmp/itpeval-toolchains` to avoid slow toolchain
builds on network storage. You can override either default:

```bash
ITPEVAL_PREFIX="$PWD/_toolchains" ./bin/itpeval install
```

Shared downloads default to `itpeval/.downloads`. You can override:

```bash
ITPEVAL_DOWNLOAD_CACHE="$PWD/.downloads" ./bin/install-all.sh
```

## What “check” means

Each prover folder contains:
- `install.sh`: installs the prover into `ITPEVAL_PREFIX`.
- `check.sh`: runs a small “hello” proof/script and ensures the prover can verify it.
- `hello/`: minimal files used by `check.sh`.

Every `install`, `check`, and `run` invocation creates a timestamped run folder under `itpeval/.runs/<timestamp>/` with:
- `results.jsonl` for machine-readable per-stage results
- `summary.json` for aggregated counts and per-prover status
- `logs/` for full per-prover stdout/stderr
- for `check`/`run`, a staged copy of `itpeval/tasks/<task>/` under `tasks/<task>/itpeval/` so the shared benchmark layout stays self-contained

## Supported provers

- Lean 4: `itpeval/provers/lean4/`
- Rocq (Coq): `itpeval/provers/rocq/`
- Agda: `itpeval/provers/agda/`
- Isabelle: `itpeval/provers/isabelle/`
- HOL Light: `itpeval/provers/hol-light/`
- HOL4: `itpeval/provers/hol4/`
- ACL2: `itpeval/provers/acl2/`
- Metamath: `itpeval/provers/metamath/`
- PVS: `itpeval/provers/pvs/`
- Mizar: `itpeval/provers/mizar/`

Notes:
- Some provers are large downloads/builds. `install-all.sh` is best-effort and will continue if one prover fails.
- This harness is intended for research prototyping; pin versions explicitly if you need strict reproducibility.
- Statement trust checks are prover-specific: each adapter permits its native
  conservative definitions and library mechanisms while rejecting that
  prover's axiom, oracle, raw-theorem, or unchecked-admission mechanisms.
- `itpeval/bin/install-all.sh` and `itpeval/bin/check-all.sh` remain as compatibility wrappers around `itpeval/bin/itpeval`.
- `./bin/itpeval` defaults to the shared smoke task `arith_2_plus_2`; pass `--task hello` to run each adapter’s built-in `hello/` check, or pass `--task <name>` to select another benchmark task.
- The Python implementation lives in `itpeval/cli/`; `itpeval/bin/itpeval` is a small shim.

## One-file “run any ITP” runner

If you want a single entrypoint where you choose a prover and pass some code,
use `itpeval eval`. From the repository root:

Run inline code (writes a minimal `ITPEVAL_TASK_DIR` layout and calls the selected prover adapter):

```bash
./itpeval/bin/itpeval eval --prover lean4 \
  --code 'theorem t : (2+3:Nat)=5 := rfl'
./itpeval/bin/itpeval eval --prover rocq \
  --code $'Theorem t : 2 + 3 = 5.\nProof. reflexivity. Qed.'
./itpeval/bin/itpeval eval --prover isabelle --mode snippet \
  --code 'lemma t: "(2::nat) + 3 = 5" by simp'
./itpeval/bin/itpeval eval --prover agda \
  --code $'module Example where\n\ndata Truth : Set where\n  truth : Truth\n\nproof : Truth\nproof = truth'
./itpeval/bin/itpeval eval --prover pvs \
  --code $'Example: THEORY\nBEGIN\n  truth: LEMMA TRUE\n  %|- truth : PROOF\n  %|- (grind)\n  %|- QED\nEND Example'
./itpeval/bin/itpeval eval --prover hol4 \
  --code 'val truth = prove(``T``, REWRITE_TAC[]);'
./itpeval/bin/itpeval eval --prover mizar --mode snippet \
  --code $'::$P-\ntheorem for x being set holds x = x\nproof\nend;\n::$P+'
```

The same `eval` interface accepts `--file` for a source file or `--task-dir`
for an already staged task. Agda raw mode derives the `.agda` path from the
declared module, PVS raw mode derives the `.pvs` filename from the theory, and
HOL4 inserts the supplied SML fragment into a generated theory wrapper.

## Shared cache

`itpeval/manifest.json` acts as a simple lockfile for shared downloads we already know about. The cache helper in `itpeval/bin/common.sh` stores files under `itpeval/.downloads` by default and reuses them across runs.

After sourcing the helper file, you can prefetch or reuse a download manually:

```bash
source itpeval/bin/common.sh
download_cached "https://us.metamath.org/downloads/metamath.tar.gz" \
  "0bb7fa403df652fb4158f086652c14cd477acb54dd23d5ef64f929186ea00aa0"
```

You can also pass a destination path as the third argument if you want the cached file copied somewhere specific.

If the file is already cached, the helper validates the hash and reuses it. If you set `ITPEVAL_DOWNLOAD_CACHE`, the same cache can live outside the repo for offline or shared-machine workflows.

## Per-prover notes

### Lean 4

- Installer: `itpeval/provers/lean4/install.sh`
- Toolchain override: `LEAN_TOOLCHAIN=leanprover/lean4:stable`
- Installs wrappers into: `ITPEVAL_PREFIX/bin/lean` and `ITPEVAL_PREFIX/bin/lake`

### Rocq (Coq)

- Installer: `itpeval/provers/rocq/install.sh`
- Uses a local opam root: `ITPEVAL_PREFIX/rocq/opamroot`
- You can override the opam root (useful if an old root is in a bad state): `ITPEVAL_ROCQ_OPAMROOT=/some/path`
- If `opam` is missing, downloads a local opam binary into `ITPEVAL_PREFIX/rocq/bin/opam`
- Opam repository URL override: `ITPEVAL_OPAM_REPO_URL=git+https://github.com/ocaml/opam-repository.git`
- Version overrides:
  - `ROCQ_VERSION=9.0.0`
  - `OCAML_VERSION=4.14.2`
  - `ROCQ_SWITCH_NAME=rocq`
  - `ITPEVAL_OPAM_VERSION=2.5.0`

### Agda

- Installer: `itpeval/provers/agda/install.sh`
- Prefers a system `agda` if available; otherwise bootstraps `ghcup` + `cabal` and builds Agda.
- Installs wrapper into: `ITPEVAL_PREFIX/bin/agda`

### Isabelle

- Installer: `itpeval/provers/isabelle/install.sh`
- Downloads the Isabelle distribution tarball into `ITPEVAL_PREFIX/isabelle/dist`
- Tarball is selected automatically based on platform/arch (`_linux`, `_macos`, `_macos_arm64`)
- Version override: `ITPEVAL_ISABELLE_VERSION=Isabelle2024`
- Base URL override: `ITPEVAL_ISABELLE_BASE_URL=...`
- Tarball filename override: `ITPEVAL_ISABELLE_TARBALL=Isabelle2024_macos_arm64.tar.gz`
- Installs wrapper into: `ITPEVAL_PREFIX/bin/isabelle`

### HOL Light

- Installer: `itpeval/provers/hol-light/install.sh`
- Clones from the upstream GitHub repo by default and builds in-place.
- Useful env vars: `HOL_LIGHT_HOME`, `ITPEVAL_HOL_LIGHT_HOME`, `ITPEVAL_HOL_LIGHT_SRC`

### HOL4

- Installer: `itpeval/provers/hol4/install.sh`
- Wires an existing HOL4 tree or builds Poly/ML and HOL4 from source.
- Useful env vars: `HOL4_HOME`, `ITPEVAL_HOL4_HOME`, `ITPEVAL_HOL4_SRC`, `ITPEVAL_HOL4_REPO_URL`
- One-file tasks automatically receive `helloScript.sml` and `Holmakefile` wrappers around the editable SML fragment.

### ACL2

- Installer: `itpeval/provers/acl2/install.sh`
- Wires an existing installation or downloads and builds ACL2 8.6, then
  certifies the `basic` community-book set.
- On Linux, it can bootstrap a local SBCL when no Lisp implementation is available. On macOS, wire an existing ACL2 installation.
- Useful env vars: `ACL2_HOME`, `ITPEVAL_ACL2_HOME`, `ITPEVAL_ACL2_SRC`,
  `ITPEVAL_ACL2_VERSION`, `ITPEVAL_ACL2_LISP`,
  `ITPEVAL_ACL2_BOOK_TARGETS` (for example `basic`, `regression`, or a
  space-separated list of `.cert` targets), and `ITPEVAL_ACL2_BOOK_JOBS`.

### Metamath

- Installer: `itpeval/provers/metamath/install.sh`
- Downloads and builds the Metamath verifier locally, then exposes `metamath` via `ITPEVAL_PREFIX/bin/metamath`.
- Useful env vars: `ITPEVAL_METAMATH_URL`

### PVS

- Installer: `itpeval/provers/pvs/install.sh`
- Downloads the pinned PVS 8.1 native release for supported Linux/macOS architectures, or wires an existing installation.
- Useful env vars: `PVS_HOME`, `ITPEVAL_PVS_HOME`, `PVS_TARBALL`, `ITPEVAL_PVS_TARBALL`, `ITPEVAL_PVS_TARBALL_URL`

### Mizar

- Installer: `itpeval/provers/mizar/install.sh`
- Installs an official Linux/x86 bundle or wires an existing install/source tree.
- Accepts current and legacy Mizar database layouts with `abstr/` plus `prel/`, `mml/`, or `dict/`.
- Useful env vars: `MIZAR_HOME`, `ITPEVAL_MIZAR_HOME`, `ITPEVAL_MIZAR_SRC`, `MIZFILES`, `ITPEVAL_MIZFILES`, `MIZAR_TARBALL`, `ITPEVAL_MIZAR_TARBALL`, `ITPEVAL_MIZAR_TARBALL_URL`, `ITPEVAL_TMPDIR`
- Exposes wrappers for `mizf`, `verifier`, `accom`, `exporter`, `makeenv`, `miz2prel`, `errflag`, and `addfmsg` when available.
- `check.sh` accepts one `.miz` in the task root or `text/`, supports `ITPEVAL_TASK_FILE`, and verifies a disposable copy so Mizar cannot annotate the source candidate.

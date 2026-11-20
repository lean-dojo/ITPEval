# Installation

Install ITPEval and the native prover on the machine that will check your proofs. The API and CLI share a toolchain prefix. Use the prover version your project’s libraries expect. [Library setup by prover](../provers/index.md)

## Set up your platform

<div class="interface-switch" data-label="Operating system" markdown="1">
<section class="interface-panel" markdown="1">

### macOS

On Apple Silicon or Intel Macs, run the Homebrew bootstrap from the repository root.

```bash
# Install native build tools with Homebrew.
./itpeval/bin/bootstrap-macos.sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -e .

# Install Lean for the quickstart in a prefix shared by the API and CLI.
export ITPEVAL_PREFIX="$HOME/.local/share/itpeval/toolchains/current"
itpeval install lean4
```

The native installers cover Lean, Rocq, Isabelle/HOL, HOL Light, Agda, HOL4, Metamath and PVS. For ACL2, point `ACL2_HOME` at an existing installation. For Mizar, run its checker on an x86 Linux host with 32-bit execution support.

</section>
<section class="interface-panel" markdown="1">

### Windows

For the [dataset loader](../benchmarks/translation.md#data-access-and-validation), use your regular Windows Python environment. For native checking, run the prover commands in a WSL 2 terminal. To set up WSL, open PowerShell as administrator, run `wsl --install`, restart when prompted, and open Ubuntu. Clone the repository inside your WSL home directory. [Microsoft’s WSL installation guide](https://learn.microsoft.com/en-us/windows/wsl/install)

```bash
# In Ubuntu, install the tools for the Lean quickstart.
sudo apt-get update
sudo apt-get install -y python3-venv git curl zstd
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -e .

# From the repository root, install Lean in WSL.
export ITPEVAL_PREFIX="$HOME/.local/share/itpeval/toolchains/current"
itpeval install lean4
```

For a pinned build, use the release installer on x86-64 WSL. [Pinned toolchains](#reproduce-the-pinned-toolchains)

</section>
<section class="interface-panel" markdown="1">

### Linux

Use Bash in your repository checkout. Install Python 3.10 or newer with its virtual environment module, Git and curl. The Lean installer can reuse an existing Lean and Lake installation or install them through Elan.

```bash
# Install the Python package and the Lean toolchain used in the quickstart.
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -e .
export ITPEVAL_PREFIX="$HOME/.local/share/itpeval/toolchains/current"
itpeval install lean4
```

Use `itpeval install` with the [prover IDs](../reference/cli.md) you need. For versions matching the published all-ten run, use a separate prefix and the pinned installer below.

</section>
</div>

Try the quickstart, check your own file, or run `itpeval practice` with a prover ID to open an editable exercise. [Quickstart](../start/quickstart.md) · [Own projects](../guides/work-with-a-library.md) · [VS Code exercises](../start/proof-completion.md)

## Check what is installed

Run `itpeval toolchains status` to see the launchers and versions in your active prefix. Give it prover IDs to check a subset or add `--json` for a script. Set `ITPEVAL_PREFIX` or pass `itpeval --prefix DIR toolchains status` to inspect a different installation.

## Install the stable releases

The stable profile pins the releases listed below as of November 19, 2026. Use this checkout on x86-64 Linux or WSL and give these builds their own prefix. Replace `all` with prover IDs for a subset. [Build dependencies](../../.github/workflows/conformance.yml) · [Stable profile](../../itpeval/environments/linux-x86_64-stable.json)

```bash
# Keep this set of ten pinned releases together in its own toolchain directory.
export ITPEVAL_PREFIX="$HOME/.local/share/itpeval/toolchains/stable-2026-11-19"
itpeval toolchains install all
itpeval toolchains status
```

| Prover | Stable release |
|---|---|
| Lean 4 | [4.36.0](https://lean-lang.org/doc/reference/latest/releases/v4.36.0/) |
| Rocq | [9.3.0](https://github.com/rocq-prover/rocq/releases/tag/V9.3.0) with [Stdlib 9.2.0](https://github.com/rocq-prover/stdlib/releases/tag/V9.2.0) |
| Isabelle/HOL | [Isabelle2026](https://isabelle.in.tum.de/website-Isabelle2026/) |
| HOL Light | [3.2.0](https://github.com/jrh13/hol-light/releases/tag/Release-3.2.0) |
| ACL2 | [8.7](https://github.com/acl2-devel/acl2-devel/releases/tag/8.7) |
| Agda | [2.9.0](https://github.com/agda/agda/releases/tag/v2.9.0) |
| HOL4 | [Trindemossen-2, patch v11](https://github.com/HOL-Theorem-Prover/HOL/tree/trindemossen-2-v11) |
| Metamath | [0.198](https://github.com/metamath/metamath-exe/tree/v0.198) |
| Mizar | [8.1.15 with MML 5.106.1517](https://mizar.uwb.edu.pl/~softadm/current/) |
| PVS | [8.1.3](https://github.com/SRI-CSL/PVS/releases/tag/pvs8.1.3) |

Metamath's current development build identifies itself as 0.200.pre. Upstream skipped the 0.199 release. PVS reports the major and minor version in its startup banner and records its full release tag in the distribution's `metadata.json`. [Metamath version history](https://github.com/metamath/metamath-exe/commit/5a6b55170a47ba9e76212b47fd47f3f08d2894a2)

Projects pin their library and compiler versions independently of this profile. For an experiment that uses Pantograph, Pétanque or Isa-REPL, select the matching prover and instrument recorded in its environment. [Optional integrations](../reference/capabilities.md)

## Reproduce the pinned toolchains

Use the baseline profile for the recorded ten-prover measurements on Linux x86-64. Install it in a separate prefix. [Installer inputs](../../itpeval/environments/linux-x86_64.json) · [Build dependencies](../../.github/workflows/conformance.yml)

```bash
# Install one pinned prover. Add more prover IDs to the same command as needed.
export ITPEVAL_PREFIX="$HOME/.local/share/itpeval/toolchains/pinned"
python -m itpeval.environments.install --profile baseline --prefix "$ITPEVAL_PREFIX" \
  --cache "$HOME/.cache/itpeval/downloads" lean4
```

For the complete set, pass `lean4 rocq isabelle hol-light acl2 agda hol4 metamath mizar pvs`. The installer writes build logs and receipts under `$ITPEVAL_PREFIX/.itpeval/`.

| Prover | Pinned version |
|---|---|
| Lean 4 | 4.35.0 |
| Rocq | 9.1.1, Stdlib 9.0.0, OCaml 4.14.2 |
| Isabelle/HOL | Isabelle2024, HOL heap |
| HOL Light | `6dbb775efdff`, OCaml 4.14.2 |
| ACL2 | 8.6, selected certified Community Books |
| Agda | 2.9.0 |
| HOL4 | `0c30bdb71aaf`, Poly/ML 5.9.2 |
| Metamath | 0.200.pre, 17-Aug-2026 |
| Mizar | 8.1.15, MML 5.106.1517 |
| PVS | 8.1, upstream build `pvs8.1-master-20260624` |

An installed Python distribution looks under `$XDG_DATA_HOME/itpeval/toolchains` or `~/.local/share/itpeval/toolchains`. A `current` directory or symlink inside that location selects a versioned installation. `ITPEVAL_PREFIX` or CLI `--prefix` selects a different installation. A checkout also uses the selected `current` installation if present and falls back to `itpeval/_toolchains`.

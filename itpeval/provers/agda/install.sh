#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROVER_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${PROVER_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
AGDA_PREFIX="${PREFIX}/agda"
BIN_DIR="${AGDA_PREFIX}/bin"
STATE_DIR="${AGDA_PREFIX}/state"
GHCUP_BASE_PREFIX="${ITPEVAL_AGDA_GHCUP_PREFIX:-${AGDA_PREFIX}/ghcup}"

ensure_dir "${BIN_DIR}"
ensure_dir "${STATE_DIR}"

agda_binary="${BIN_DIR}/agda"

if [[ -x "${agda_binary}" ]] && "${agda_binary}" --version >/dev/null 2>&1; then
  link_into_prefix_bin "${agda_binary}" "agda"
  log "Agda already installed at ${agda_binary}"
  exit 0
fi

export GHCUP_INSTALL_BASE_PREFIX="${GHCUP_BASE_PREFIX}"
export PATH="${GHCUP_INSTALL_BASE_PREFIX}/.ghcup/bin:${GHCUP_INSTALL_BASE_PREFIX}/.cabal/bin:${PATH}"

if command -v dnf >/dev/null 2>&1; then
  # ghcup/cabal builds commonly need these -dev packages (zlib, ncurses/tinfo).
  # Install them proactively to avoid opaque Cabal failures like "Missing C library: z" or "-ltinfo".
  needed_pkgs=(
    gcc
    gcc-c++
    gmp-devel
    make
    ncurses-devel
    pkgconf-pkg-config
    xz
    zlib-devel
  )
  missing_pkgs=()
  if command -v rpm >/dev/null 2>&1; then
    for pkg in "${needed_pkgs[@]}"; do
      if ! rpm -q "${pkg}" >/dev/null 2>&1; then
        missing_pkgs+=("${pkg}")
      fi
    done
  else
    missing_pkgs=("${needed_pkgs[@]}")
  fi
  if ((${#missing_pkgs[@]})); then
    log "Installing system dependencies via dnf: ${missing_pkgs[*]}"
    run sudo dnf -y install "${missing_pkgs[@]}"
  fi
fi

if command -v dnf >/dev/null 2>&1; then
  if dnf -q list available agda >/dev/null 2>&1; then
    log "Installing Agda from dnf into the system package database"
    run sudo dnf -y install agda
    system_agda="$(command -v agda || true)"
    if [[ -n "${system_agda}" ]]; then
      ln -sf "${system_agda}" "${agda_binary}"
    fi
    log "Installed system Agda and linked it into ${agda_binary}"
    exit 0
  fi
fi

if ! command -v ghcup >/dev/null 2>&1; then
  log "Installing ghcup into ${AGDA_PREFIX}"
  tmp_installer="$(mktemp)"
  trap 'rm -f "${tmp_installer}"' EXIT
  run curl -fsSL https://get-ghcup.haskell.org -o "${tmp_installer}"
  env \
    BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
    BOOTSTRAP_HASKELL_GHC_VERSION=recommended \
    BOOTSTRAP_HASKELL_CABAL_VERSION=recommended \
    BOOTSTRAP_HASKELL_INSTALL_NO_STACK=1 \
    GHCUP_INSTALL_BASE_PREFIX="${GHCUP_BASE_PREFIX}" \
    /bin/bash "${tmp_installer}"
fi

if ! command -v cabal >/dev/null 2>&1; then
  log "Installing GHC and cabal via ghcup"
  ghcup install ghc recommended
  ghcup install cabal recommended
  ghcup set ghc recommended
  ghcup set cabal recommended
fi

export PATH="${GHCUP_INSTALL_BASE_PREFIX}/.ghcup/bin:${GHCUP_INSTALL_BASE_PREFIX}/.cabal/bin:${PATH}"

if ! command -v cabal >/dev/null 2>&1; then
  fail "cabal is unavailable after ghcup bootstrap"
fi

log "Building Agda with cabal into ${BIN_DIR}"
run cabal update
run cabal install Agda --install-method=copy --overwrite-policy=always --installdir="${BIN_DIR}"

if [[ ! -x "${agda_binary}" ]]; then
  if command -v agda >/dev/null 2>&1; then
    ln -sf "$(command -v agda)" "${agda_binary}"
  else
    fail "Agda installation did not produce ${agda_binary}"
  fi
fi

link_into_prefix_bin "${agda_binary}" "agda"
log "Agda available at ${agda_binary}"

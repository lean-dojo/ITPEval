#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
INSTALL_ROOT="${PREFIX}/metamath"
ARCHIVE_DIR="${INSTALL_ROOT}/archive"
SRC_DIR="${INSTALL_ROOT}/src"
BIN_DIR="${INSTALL_ROOT}/bin"

METAMATH_URL="${ITPEVAL_METAMATH_URL:-https://us.metamath.org/downloads/metamath.tar.gz}"
METAMATH_SHA256="${ITPEVAL_METAMATH_SHA256:-$(itpeval_manifest_get metamath.source sha256 2>/dev/null || true)}"

ensure_dir "${ARCHIVE_DIR}"
ensure_dir "${SRC_DIR}"
ensure_dir "${BIN_DIR}"

METAMATH_BIN="${BIN_DIR}/metamath"

if [[ -x "${METAMATH_BIN}" ]]; then
  link_into_prefix_bin "${METAMATH_BIN}" "metamath"
  log "Metamath already installed at ${METAMATH_BIN}"
  exit 0
fi

tmp_dir="$(mktemp -d)"
trap 'rm -rf "${tmp_dir}"' EXIT

tarball_path="${ARCHIVE_DIR}/metamath.tar.gz"
log "Downloading Metamath source tarball from ${METAMATH_URL}"
download_cached "${METAMATH_URL}" "${METAMATH_SHA256}" "${tarball_path}"

run tar -xzf "${tarball_path}" -C "${tmp_dir}"

source_file="$(find "${tmp_dir}" -name 'metamath.c' -print -quit)"
if [[ -z "${source_file}" ]]; then
  fail "could not find metamath.c inside the downloaded tarball"
fi

source_root="$(dirname "${source_file}")"
rm -rf "${SRC_DIR}"
ensure_dir "${SRC_DIR}"
cp -a "${source_root}/." "${SRC_DIR}/"

compiler="$(command -v gcc || command -v cc || true)"
if [[ -z "${compiler}" ]]; then
  if command -v sudo >/dev/null 2>&1; then
    log "No C compiler found; installing gcc via dnf"
    run sudo dnf -y install gcc
    compiler="$(command -v gcc || command -v cc || true)"
  fi
fi

if [[ -z "${compiler}" ]]; then
  fail "no C compiler found; install gcc or cc"
fi

log "Building Metamath with ${compiler}"
(
  cd "${SRC_DIR}"
  run "${compiler}" -O2 -o "${METAMATH_BIN}" ./*.c
)

if [[ ! -x "${METAMATH_BIN}" ]]; then
  fail "build did not produce ${METAMATH_BIN}"
fi

link_into_prefix_bin "${METAMATH_BIN}" "metamath"
log "Metamath installed at ${METAMATH_BIN}"

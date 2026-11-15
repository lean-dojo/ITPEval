#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
SOURCE_DIR="${PREFIX}/hol4/src/HOL"
HOL4_BIN_DIR="${PREFIX}/hol4/bin"

if [[ -d "${SOURCE_DIR}/.git" ]]; then
  exec git -C "${SOURCE_DIR}" describe --always --dirty --tags
fi

if [[ -x "${HOL4_BIN_DIR}/Holmake" ]]; then
  echo "HOL4 installed at ${PREFIX}/hol4"
  exit 0
fi

if command -v Holmake >/dev/null 2>&1; then
  echo "HOL4 available on PATH"
  exit 0
fi

echo "[ITPEval][hol4] missing HOL4 installation" >&2
exit 1

#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
PVS_BIN_DIR="${PREFIX}/pvs/bin"

if [[ -x "${PVS_BIN_DIR}/pvs" ]]; then
  exec "${PVS_BIN_DIR}/pvs" --version
fi

if command -v pvs >/dev/null 2>&1; then
  exec pvs --version
fi

echo "[ITPEval][pvs] missing PVS binary" >&2
exit 1

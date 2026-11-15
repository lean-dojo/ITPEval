#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROVER_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${PROVER_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
AGDA_BIN="${PREFIX}/agda/bin/agda"

if [[ -x "${AGDA_BIN}" ]]; then
  exec "${AGDA_BIN}" --version
fi

if command -v agda >/dev/null 2>&1; then
  exec agda --version
fi

echo "[ITPEval][agda] missing Agda binary" >&2
exit 1

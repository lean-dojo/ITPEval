#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
METAMATH_BIN="${PREFIX}/metamath/bin/metamath"

if [[ -x "${METAMATH_BIN}" ]]; then
  exec bash -lc "printf 'exit\n' | '${METAMATH_BIN}'"
fi

if command -v metamath >/dev/null 2>&1; then
  exec bash -lc "printf 'exit\n' | metamath"
fi

echo "[ITPEval][metamath] missing Metamath binary" >&2
exit 1

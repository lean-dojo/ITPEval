#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
MIZAR_BIN_DIR="${PREFIX}/mizar/bin"

version_file="${ITPEVAL_MIZFILES:-${PREFIX}/mizar/vendor/mizfiles}/mml.ini"
if [[ -x "${MIZAR_BIN_DIR}/verifier" && -f "${version_file}" ]]; then
  python3 - "${version_file}" <<'PY'
from configparser import ConfigParser
import sys

config = ConfigParser()
config.read(sys.argv[1])
v = config["Mizar verifier"]
lib = config["MML"]
print("Mizar " + ".".join(v[k] for k in ("MizarReleaseNbr", "MizarVersionNbr", "MizarVariantNbr"))
      + f" (MML {lib['MMLVersion']}.{lib['NumberOfArticles']})")
PY
  exit 0
fi

if [[ -x "${MIZAR_BIN_DIR}/mizf" ]]; then
  if "${MIZAR_BIN_DIR}/mizf" --version >/dev/null 2>&1; then
    exec "${MIZAR_BIN_DIR}/mizf" --version
  fi
fi

if command -v mizf >/dev/null 2>&1; then
  if mizf --version >/dev/null 2>&1; then
    exec mizf --version
  fi
fi

if [[ -x "${MIZAR_BIN_DIR}/verifier" ]]; then
  echo "Mizar installed at ${PREFIX}/mizar"
  exit 0
fi

echo "[ITPEval][mizar] missing Mizar installation" >&2
exit 1

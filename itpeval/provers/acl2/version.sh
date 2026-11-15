#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
ACL2_ROOT="${PREFIX}/acl2"
ACL2_BIN="${ACL2_ROOT}/bin/acl2"

if [[ -d "${ACL2_ROOT}/src" ]]; then
  acl2_src_dir="$(find "${ACL2_ROOT}/src" -maxdepth 1 -type d -name 'acl2-*' | head -n 1 || true)"
  if [[ -n "${acl2_src_dir}" ]]; then
    echo "ACL2 ${acl2_src_dir##*/acl2-}"
    exit 0
  fi
fi

if [[ -x "${ACL2_BIN}" ]]; then
  echo "ACL2 installed at ${ACL2_ROOT}"
  exit 0
fi

if command -v acl2 >/dev/null 2>&1; then
  echo "ACL2 available on PATH"
  exit 0
fi

echo "[ITPEval][acl2] missing ACL2 installation" >&2
exit 1

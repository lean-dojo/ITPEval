#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
PVS_BIN_DIR="${PREFIX}/pvs/bin"

if [[ -x "${PVS_BIN_DIR}/pvs" ]]; then
  # The saved Lisp image also prints its license banner on some builds.
  version_output="$("${PVS_BIN_DIR}/pvs" --version)"
  if [[ "${version_output}" =~ (PVS[[:space:]]Version[[:space:]][^[:space:]]+) ]]; then
    banner="${BASH_REMATCH[1]}"
    metadata="${PREFIX}/pvs/metadata.json"
    if [[ -f "${metadata}" ]]; then
      # The native banner can omit the patch level. SRI ships the build tag
      # in the same distribution, including its commit and target platform.
      if tag="$(python3 -c 'import json, sys; print(json.load(sys.stdin)["ci"]["ref"])' < "${metadata}" 2>/dev/null)" &&
          [[ "${tag}" =~ ^refs/tags/pvs([0-9]+\.[0-9]+\.[0-9]+)$ ]]; then
        release="${BASH_REMATCH[1]}"
        if [[ "${release}" == "${banner##* }" || "${release%.*}" == "${banner##* }" ]]; then
          banner="PVS Version ${release}"
        fi
      fi
    fi
    printf '%s\n' "${banner}"
    exit 0
  fi
  fail "PVS returned no recognizable version"
fi

if command -v pvs >/dev/null 2>&1; then
  exec pvs --version
fi

echo "[ITPEval][pvs] missing PVS binary" >&2
exit 1

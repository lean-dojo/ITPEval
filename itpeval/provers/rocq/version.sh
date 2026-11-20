#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

ROCQ_ID="${ITPEVAL_ROCQ_ID:-rocq}"
ROCQ_ROOT="$(itpeval_prefix)/${ROCQ_ID}"
OPAMROOT="${ITPEVAL_ROCQ_OPAMROOT:-${ROCQ_ROOT}/opamroot}"
SWITCH_NAME="${ROCQ_SWITCH_NAME:-rocq}"
OPAM_CMD="${ROCQ_ROOT}/bin/opam"

if [[ -L "${ROCQ_ROOT}/bin/rocq" && -x "${ROCQ_ROOT}/bin/rocq" ]]; then
  exec "$(itpeval_realpath "${ROCQ_ROOT}/bin/rocq")" --version
fi

if [[ ! -d "${OPAMROOT}" ]]; then
  if command -v rocq >/dev/null 2>&1; then
    exec rocq --version
  fi
  if command -v coqc >/dev/null 2>&1; then
    exec coqc --version
  fi
  echo "[ITPEval][rocq] missing opam root and compiler" >&2
  exit 1
fi

if [[ ! -x "${OPAM_CMD}" ]]; then
  if command -v opam >/dev/null 2>&1; then
    OPAM_CMD="$(command -v opam)"
  else
    echo "[ITPEval][rocq] missing opam" >&2
    exit 1
  fi
fi

compiler_path="$("${OPAM_CMD}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v rocq || command -v coqc')"
exec "${OPAM_CMD}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c '"$1" --version' sh "${compiler_path}"

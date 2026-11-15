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
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "Missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"
OPAM_CMD="${ROCQ_ROOT}/bin/opam"

if [[ -x "${OPAM_CMD}" ]]; then
  opam_cmd="${OPAM_CMD}"
elif command -v opam >/dev/null 2>&1; then
  opam_cmd="$(command -v opam)"
else
  fail "opam not found; run install.sh first"
fi

if [[ ! -d "${OPAMROOT}" ]]; then
  fail "Rocq opam root not found at ${OPAMROOT}; run install.sh first."
fi

if [[ ! -f "${TASK_DIR}/hello.v" ]]; then
  fail "Missing hello file at ${TASK_DIR}/hello.v"
fi

itpeval_validate_statement_file "rocq" "${TASK_DIR}/hello.v"

ROCQ_PATH="$("${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v rocq' || true)"
COQC_PATH="$("${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v coqc' || true)"

if [[ -n "${COQC_PATH}" ]]; then
  log "Using compiler: ${COQC_PATH}"
  run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'cd "$1" && compiler="$2" && "$compiler" hello.v' sh "${TASK_DIR}" "${COQC_PATH}"
elif [[ -n "${ROCQ_PATH}" ]]; then
  log "Using compiler: ${ROCQ_PATH} (rocq compile)"
  run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'cd "$1" && compiler="$2" && "$compiler" compile hello.v' sh "${TASK_DIR}" "${ROCQ_PATH}"
else
  fail "Neither rocq nor coqc found in opam switch ${SWITCH_NAME}"
fi
test -f "${TASK_DIR}/hello.vo"
if [[ -n "${ROCQ_PATH}" ]]; then
  run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c '"$1" --version' sh "${ROCQ_PATH}"
else
  run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c '"$1" --version' sh "${COQC_PATH}"
fi

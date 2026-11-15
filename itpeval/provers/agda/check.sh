#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROVER_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${PROVER_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
AGDA_BIN="${PREFIX}/agda/bin/agda"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"

if [[ -n "${ITPEVAL_TASK_FILE:-}" ]]; then
  AGDA_FILE="${ITPEVAL_TASK_FILE}"
  if [[ "${AGDA_FILE}" != /* ]]; then
    AGDA_FILE="${TASK_DIR}/${AGDA_FILE}"
  fi
  if [[ ! -f "${AGDA_FILE}" ]]; then
    fail "Agda task file not found at ${AGDA_FILE}"
  fi
else
  shopt -s nullglob
  agda_files=("${TASK_DIR}"/*.agda)
  shopt -u nullglob
  if (( ${#agda_files[@]} == 0 )); then
    fail "no .agda task file found in ${TASK_DIR}"
  fi
  if (( ${#agda_files[@]} > 1 )); then
    fail "multiple .agda task files found in ${TASK_DIR}; set ITPEVAL_TASK_FILE"
  fi
  AGDA_FILE="${agda_files[0]}"
fi

if [[ "${AGDA_FILE}" != *.agda ]]; then
  fail "Agda task file must use the .agda extension: ${AGDA_FILE}"
fi

itpeval_validate_statement_file "agda" "${AGDA_FILE}"

if [[ -x "${AGDA_BIN}" ]]; then
  agda_cmd="${AGDA_BIN}"
elif command -v agda >/dev/null 2>&1; then
  agda_cmd="$(command -v agda)"
else
  fail "agda executable not found; run itpeval/provers/agda/install.sh first"
fi

run "${agda_cmd}" --no-libraries --no-default-libraries -i "${TASK_DIR}" "${AGDA_FILE}"
log "Agda task module typechecked successfully"

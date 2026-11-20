#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
PVS_BIN_DIR="${PREFIX}/pvs/bin"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd -P)"

if [[ -n "${ITPEVAL_TASK_FILE:-}" ]]; then
  PVS_FILE="${ITPEVAL_TASK_FILE}"
  if [[ "${PVS_FILE}" != /* ]]; then
    PVS_FILE="${TASK_DIR}/${PVS_FILE}"
  fi
  if [[ ! -f "${PVS_FILE}" ]]; then
    fail "PVS task file not found at ${PVS_FILE}"
  fi
else
  shopt -s nullglob
  pvs_files=("${TASK_DIR}"/*.pvs)
  shopt -u nullglob
  if (( ${#pvs_files[@]} == 0 )); then
    fail "no .pvs task file found in ${TASK_DIR}"
  fi
  if (( ${#pvs_files[@]} > 1 )); then
    fail "multiple .pvs task files found in ${TASK_DIR}; set ITPEVAL_TASK_FILE"
  fi
  PVS_FILE="${pvs_files[0]}"
fi

if [[ "${PVS_FILE}" != *.pvs ]]; then
  fail "PVS task file must use the .pvs extension: ${PVS_FILE}"
fi

PVS_FILE="$(itpeval_realpath "${PVS_FILE}")"
case "${PVS_FILE}" in
  "${TASK_DIR}"/*) ;;
  *) fail "PVS task file must resolve inside task directory: ${PVS_FILE}" ;;
esac
PVS_RELATIVE_FILE="${PVS_FILE#"${TASK_DIR}/"}"
itpeval_validate_statement_file "pvs" "${PVS_FILE}"
statement_mode=0
if [[ "${ITPEVAL_OPERATION:-legacy}" == statement ]]; then
  statement_mode=1
elif [[ "${ITPEVAL_OPERATION:-legacy}" == legacy ]] && {
  grep -Fq -- "Statement-only formalization of" "${PVS_FILE}" ||
    grep -Fqi -- ":itpeval-statement-checked" "${PVS_FILE}"
}; then
  statement_mode=1
fi

# Run from a clean copy so proveit cannot rewrite tracked task caches.
WORK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/itpeval-pvs-check.XXXXXX")"
tar \
  --exclude='./.pvscontext' \
  --exclude='./pvsbin' \
  --exclude='./*.summary' \
  -C "${TASK_DIR}" -cf - . | tar -C "${WORK_DIR}" -xf -
PVS_FILE="${WORK_DIR}/${PVS_RELATIVE_FILE}"

# PVS 8.1 initializes its log directory even when proof logging is disabled.
# Keep that state in a disposable writable directory instead of ~/.pvslog so
# batch verification works in sandboxed environments.
PVS_LOG_DIR="$(mktemp -d "${TMPDIR:-/tmp}/itpeval-pvs-log.XXXXXX")"
trap 'rm -rf "${WORK_DIR}" "${PVS_LOG_DIR}"' EXIT
export PVS_LOG_DIR

if [[ -x "${PVS_BIN_DIR}/proveit" ]]; then
  export PATH="${PVS_BIN_DIR}:${PATH}"
fi
if [[ -x "${PVS_BIN_DIR}/pvs" ]]; then
  export PATH="${PVS_BIN_DIR}:${PATH}"
fi

if command -v proveit >/dev/null 2>&1; then
  pushd "${WORK_DIR}" >/dev/null
  if [[ "${statement_mode}" -eq 1 ]]; then
    run proveit -T "${PVS_FILE}"
  elif [[ "${ITPEVAL_OPERATION:-legacy}" == proof_completion ]]; then
    rc=0
    run proveit -l --disable-oracles -o itpeval "${PVS_FILE}" || rc=$?
    if [[ -f "${WORK_DIR}/itpeval.summary" ]]; then
      cat "${WORK_DIR}/itpeval.summary"
    fi
    if ((rc != 0)); then
      [[ ! -f "${WORK_DIR}/itpeval.log" ]] || tail -100 "${WORK_DIR}/itpeval.log" >&2
      exit "${rc}"
    fi
  else
    run proveit "${PVS_FILE}"
  fi
  popd >/dev/null
  log "PVS task theory checked successfully"
  exit 0
fi

if command -v pvs >/dev/null 2>&1; then
  run pvs -batch -q -f pvs-version
  fail "PVS runtime is present, but proveit was not found; install ProofLite/proveit to verify the task theory"
fi

fail "PVS check needs proveit or pvs in PATH or in ${PVS_BIN_DIR}; run install.sh first"

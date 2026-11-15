#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
METAMATH_BIN="${PREFIX}/metamath/bin/metamath"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd -P)"

if [[ ! -x "${METAMATH_BIN}" ]]; then
  fail "missing Metamath executable at ${METAMATH_BIN}; run install.sh first"
fi

if [[ -n "${ITPEVAL_TASK_FILE:-}" ]]; then
  if [[ "${ITPEVAL_TASK_FILE}" = /* ]]; then
    TASK_FILE_CANDIDATE="${ITPEVAL_TASK_FILE}"
  else
    TASK_FILE_CANDIDATE="${TASK_DIR}/${ITPEVAL_TASK_FILE}"
  fi
else
  shopt -s nullglob
  TASK_FILES=("${TASK_DIR}"/*.mm)
  shopt -u nullglob
  if [[ "${#TASK_FILES[@]}" -ne 1 ]]; then
    fail "expected exactly one root .mm file in ${TASK_DIR}, found ${#TASK_FILES[@]}"
  fi
  TASK_FILE_CANDIDATE="${TASK_FILES[0]}"
fi

if [[ "${TASK_FILE_CANDIDATE}" != *.mm ]]; then
  fail "Metamath task file must have a .mm extension: ${TASK_FILE_CANDIDATE}"
fi
if [[ ! -f "${TASK_FILE_CANDIDATE}" ]]; then
  fail "missing Metamath task file at ${TASK_FILE_CANDIDATE}"
fi

TASK_FILE="$(itpeval_realpath "${TASK_FILE_CANDIDATE}")"
case "${TASK_FILE}" in
  "${TASK_DIR}"/*) ;;
  *) fail "Metamath task file must resolve inside task directory: ${TASK_FILE}" ;;
esac
TASK_FILE_REL="${TASK_FILE#"${TASK_DIR}/"}"

itpeval_validate_statement_file "metamath" "${TASK_FILE}"

log "+ ${METAMATH_BIN} read ${TASK_FILE_REL} verify proof * exit"
set +e
METAMATH_OUTPUT="$(
  cd "${TASK_DIR}"
  "${METAMATH_BIN}" "read ${TASK_FILE_REL}" "verify proof *" exit 2>&1
)"
METAMATH_RC=$?
set -e
printf '%s\n' "${METAMATH_OUTPUT}"

if [[ "${METAMATH_RC}" -ne 0 ]]; then
  fail "Metamath exited with status ${METAMATH_RC}"
fi
if grep -Fq -- "?Error" <<<"${METAMATH_OUTPUT}"; then
  fail "Metamath reported a parser or verifier error"
fi
if ! grep -Fq -- "No errors were found." <<<"${METAMATH_OUTPUT}"; then
  fail "Metamath output is missing the successful read marker"
fi
if ! grep -Fq -- "All proofs in the database were verified" <<<"${METAMATH_OUTPUT}"; then
  fail "Metamath output is missing the successful proof-verification marker"
fi

log "Metamath database verified successfully"

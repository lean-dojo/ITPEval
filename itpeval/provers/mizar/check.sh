#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
MIZAR_BIN_DIR="${PREFIX}/mizar/bin"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"

if [[ -n "${ITPEVAL_TASK_FILE:-}" ]]; then
  MIZAR_FILE="${ITPEVAL_TASK_FILE}"
  if [[ "${MIZAR_FILE}" != /* ]]; then
    MIZAR_FILE="${TASK_DIR}/${MIZAR_FILE}"
  fi
  if [[ ! -f "${MIZAR_FILE}" ]]; then
    fail "Mizar task file not found at ${MIZAR_FILE}"
  fi
else
  shopt -s nullglob
  mizar_files=("${TASK_DIR}"/*.miz "${TASK_DIR}"/text/*.miz)
  shopt -u nullglob
  if (( ${#mizar_files[@]} == 0 )); then
    fail "no .miz task file found in ${TASK_DIR} or ${TASK_DIR}/text"
  fi
  if (( ${#mizar_files[@]} > 1 )); then
    fail "multiple .miz task files found in ${TASK_DIR}; set ITPEVAL_TASK_FILE"
  fi
  MIZAR_FILE="${mizar_files[0]}"
fi

if [[ "${MIZAR_FILE}" != *.miz ]]; then
  fail "Mizar task file must use the .miz extension: ${MIZAR_FILE}"
fi

MIZAR_FILE="$(cd "$(dirname "${MIZAR_FILE}")" && pwd)/$(basename "${MIZAR_FILE}")"
case "${MIZAR_FILE}" in
  "${TASK_DIR}"/*) ;;
  *) fail "Mizar task file must be inside ITPEVAL_TASK_DIR: ${MIZAR_FILE}" ;;
esac
MIZAR_REL="${MIZAR_FILE#"${TASK_DIR}"/}"

itpeval_validate_statement_file "mizar" "${MIZAR_FILE}"

if [[ -x "${MIZAR_BIN_DIR}/mizf" ]]; then
  export PATH="${MIZAR_BIN_DIR}:${PATH}"
fi
if [[ -x "${MIZAR_BIN_DIR}/verifier" ]]; then
  export PATH="${MIZAR_BIN_DIR}:${PATH}"
fi
if [[ -x "${MIZAR_BIN_DIR}/accom" ]]; then
  export PATH="${MIZAR_BIN_DIR}:${PATH}"
fi
if [[ -n "${ITPEVAL_MIZFILES:-}" ]]; then
  export MIZFILES="${ITPEVAL_MIZFILES}"
fi

make_work_dir() {
  local root=""
  local candidate=""
  for root in "${ITPEVAL_TMPDIR:-}" "${TMPDIR:-}" /tmp /var/tmp; do
    if [[ -z "${root}" || ! -d "${root}" || ! -w "${root}" ]]; then
      continue
    fi
    if candidate="$(mktemp -d "${root%/}/itpeval-mizar.XXXXXX" 2>/dev/null)"; then
      printf '%s\n' "${candidate}"
      return 0
    fi
  done
  fail "unable to create a Mizar work directory; set ITPEVAL_TMPDIR to writable local storage"
}

# `errflag`, called by the standard `mizf` driver, annotates erroneous source
# files in place. Verify a disposable copy so corpus candidates remain clean.
WORK_DIR="$(make_work_dir)"
trap 'rm -rf "${WORK_DIR}"' EXIT
cp -a "${TASK_DIR}/." "${WORK_DIR}/"

STAGED_FILE="${WORK_DIR}/${MIZAR_REL}"
ARTICLE_REL="${MIZAR_REL%.miz}"
ERR_FILE="${STAGED_FILE%.miz}.err"
rm -f "${ERR_FILE}"

driver_rc=0
if command -v mizf >/dev/null 2>&1; then
  (cd "${WORK_DIR}" && run mizf "${ARTICLE_REL}") || driver_rc=$?
elif command -v verifier >/dev/null 2>&1; then
  if command -v makeenv >/dev/null 2>&1; then
    (cd "${WORK_DIR}" && run makeenv "${ARTICLE_REL}") || driver_rc=$?
  elif command -v accom >/dev/null 2>&1; then
    (cd "${WORK_DIR}" && run accom "${ARTICLE_REL}") || driver_rc=$?
  else
    fail "verifier is present but makeenv/accom is missing; use mizf or provide the full Mizar toolchain"
  fi
  if (( driver_rc == 0 )); then
    (cd "${WORK_DIR}" && run verifier "${ARTICLE_REL}") || driver_rc=$?
  fi
  if command -v errflag >/dev/null 2>&1; then
    (cd "${WORK_DIR}" && errflag "${ARTICLE_REL}") || true
  fi
else
  fail "Mizar check needs mizf or verifier in PATH or in ${MIZAR_BIN_DIR}; run install.sh first"
fi

if [[ ! -f "${ERR_FILE}" ]]; then
  fail "Mizar did not produce an error report for ${MIZAR_REL} (driver rc=${driver_rc})"
fi

if [[ -s "${ERR_FILE}" ]]; then
  log "Mizar reported verification errors in ${MIZAR_REL}:"
  while read -r line column code _; do
    log "  line ${line}, column ${column}, error ${code}"
  done <"${ERR_FILE}"
  fail "Mizar task verification failed"
fi

if (( driver_rc != 0 )); then
  fail "Mizar driver failed with exit code ${driver_rc}"
fi

log "Mizar task article checked successfully"

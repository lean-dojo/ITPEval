#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
ACL2_BIN="${PREFIX}/acl2/bin/acl2"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd -P)"

if [[ ! -x "${ACL2_BIN}" ]]; then
  fail "missing ACL2 executable at ${ACL2_BIN}; run install.sh first"
fi

if [[ -n "${ITPEVAL_TASK_FILE:-}" ]]; then
  if [[ "${ITPEVAL_TASK_FILE}" = /* ]]; then
    TASK_FILE_CANDIDATE="${ITPEVAL_TASK_FILE}"
  else
    TASK_FILE_CANDIDATE="${TASK_DIR}/${ITPEVAL_TASK_FILE}"
  fi
else
  shopt -s nullglob
  TASK_FILES=("${TASK_DIR}"/*.lsp)
  shopt -u nullglob
  if [[ "${#TASK_FILES[@]}" -ne 1 ]]; then
    fail "expected exactly one root .lsp file in ${TASK_DIR}, found ${#TASK_FILES[@]}"
  fi
  TASK_FILE_CANDIDATE="${TASK_FILES[0]}"
fi

if [[ "${TASK_FILE_CANDIDATE}" != *.lsp ]]; then
  fail "ACL2 task file must have a .lsp extension: ${TASK_FILE_CANDIDATE}"
fi
if [[ ! -f "${TASK_FILE_CANDIDATE}" ]]; then
  fail "missing ACL2 task file at ${TASK_FILE_CANDIDATE}"
fi

TASK_FILE="$(itpeval_realpath "${TASK_FILE_CANDIDATE}")"
case "${TASK_FILE}" in
  "${TASK_DIR}"/*) ;;
  *) fail "ACL2 task file must resolve inside task directory: ${TASK_FILE}" ;;
esac
TASK_FILE_REL="${TASK_FILE#"${TASK_DIR}/"}"

statement_mode=0
if grep -Fqi -- ":itpeval-statement-checked" "${TASK_FILE}"; then
  statement_mode=1
  itpeval_validate_statement_file "acl2" "${TASK_FILE}"
fi

tmp_output="$(mktemp)"
trap 'rm -f "${tmp_output}"' EXIT

log "+ ${ACL2_BIN} < ${TASK_FILE_REL}"
set +e
if command -v timeout >/dev/null 2>&1; then
  (
    cd "${TASK_DIR}"
    timeout 120s "${ACL2_BIN}" < "${TASK_FILE}"
  ) >"${tmp_output}" 2>&1
  acl2_rc=$?
else
  (
    cd "${TASK_DIR}"
    "${ACL2_BIN}" < "${TASK_FILE}"
  ) >"${tmp_output}" 2>&1
  acl2_rc=$?
fi
set -e
cat "${tmp_output}"

if [[ "${acl2_rc}" -ne 0 ]]; then
  fail "ACL2 exited with status ${acl2_rc}"
fi
if grep -Fq -- "ACL2 Error" "${tmp_output}" \
  || grep -Fq -- "******** FAILED ********" "${tmp_output}"; then
  fail "ACL2 reported a rejected event"
fi

if [[ "${statement_mode}" -eq 1 ]]; then
  if ! grep -Fq -- ":ITPEVAL-STATEMENT-CHECKED" "${tmp_output}"; then
    fail "ACL2 output is missing the statement-check sentinel"
  fi
  log "ACL2 statement script checked successfully"
elif ! grep -Eq 'Q\.E\.D\.|Proof succeeded|Completed' "${tmp_output}"; then
  fail "ACL2 ran, but the smoke test output did not look like a successful proof"
else
  log "ACL2 proof script completed successfully"
fi

#!/usr/bin/env bash
# check.sh — verify that HOL Light is installed and can prove a simple theorem.
#
# Loading hol.ml takes ~30-90 s; this is expected.  Set a generous timeout via
# ITPEVAL_HOLLIGHT_CHECK_TIMEOUT (seconds, default 300) if your machine is slow.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
RUN_BIN="${PREFIX}/hol-light/bin/hollight-run"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"

if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"
HELLO_FILE="${TASK_DIR}/hello.ml"

if [[ ! -x "${RUN_BIN}" ]]; then
  fail "hollight-run not found at ${RUN_BIN}; run install.sh first"
fi

if [[ ! -f "${HELLO_FILE}" ]]; then
  fail "missing hello file at ${HELLO_FILE}"
fi

itpeval_validate_statement_file "hol-light" "${HELLO_FILE}"

TIMEOUT_SEC="${ITPEVAL_HOLLIGHT_CHECK_TIMEOUT:-300}"
log "Running HOL Light hello check (timeout ${TIMEOUT_SEC}s) …"
log "  Note: loading hol.ml takes 30–90 s on a typical machine."

# Use GNU timeout if available; fall back to running directly.
if command -v timeout >/dev/null 2>&1; then
  run timeout "${TIMEOUT_SEC}" "${RUN_BIN}" "${HELLO_FILE}"
else
  run "${RUN_BIN}" "${HELLO_FILE}"
fi

log "check passed"

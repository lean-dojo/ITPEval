#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
LEAN_ROOT="${PREFIX}/lean4"
LEAN_BIN="${LEAN_ROOT}/bin/lean"
LAKE_BIN="${LEAN_ROOT}/bin/lake"
MATHLIB_PROJECT_DIR="${ITPEVAL_LEAN4_MATHLIB_PROJECT:-${LEAN_ROOT}/mathlib-project}"
MATHLIB_OLEAN="${MATHLIB_PROJECT_DIR}/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"
HELLO_FILE="${TASK_DIR}/Hello.lean"

if [[ ! -x "${LEAN_BIN}" ]]; then
  fail "missing Lean binary at ${LEAN_BIN}; run install.sh first"
fi

if [[ ! -f "${HELLO_FILE}" ]]; then
  fail "missing hello file at ${HELLO_FILE}"
fi

itpeval_validate_statement_file "lean4" "${HELLO_FILE}"

export PATH="${LEAN_ROOT}/bin:${PREFIX}/bin:${PATH}"

run "${LEAN_BIN}" --version

needs_mathlib=0
if grep -Eq "^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+Mathlib([[:space:].]|$)" "${HELLO_FILE}"; then
  needs_mathlib=1
fi

if [[ "${needs_mathlib}" == "1" ]]; then
  if [[ -n "${ITPEVAL_LEAN4_LEAN_PATH:-}" ]]; then
    export LEAN_PATH="${ITPEVAL_LEAN4_LEAN_PATH}"
    run "${LEAN_BIN}" "${HELLO_FILE}"
  elif [[ -x "${LAKE_BIN}" ]] && [[ -f "${MATHLIB_PROJECT_DIR}/lakefile.lean" || -f "${MATHLIB_PROJECT_DIR}/lakefile.toml" ]]; then
    if [[ ! -f "${MATHLIB_OLEAN}" ]]; then
      fail "Hello.lean imports Mathlib, but Mathlib.olean is missing under ${MATHLIB_PROJECT_DIR}. Build or fetch Mathlib there, or set ITPEVAL_LEAN4_MATHLIB_PROJECT/ITPEVAL_LEAN4_LEAN_PATH."
    fi
    run "${LAKE_BIN}" -d "${MATHLIB_PROJECT_DIR}" env "${LEAN_BIN}" "${HELLO_FILE}"
  else
    fail "Hello.lean imports Mathlib, but no Mathlib environment was found at ${MATHLIB_PROJECT_DIR}. Set ITPEVAL_LEAN4_MATHLIB_PROJECT or ITPEVAL_LEAN4_LEAN_PATH."
  fi
else
  run "${LEAN_BIN}" "${HELLO_FILE}"
fi

log "check passed"

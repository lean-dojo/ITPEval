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
local_sources=()
if [[ "${ITPEVAL_OPERATION:-legacy}" != legacy ]]; then
  HELLO_FILE="${TASK_DIR}/${ITPEVAL_TASK_FILE:-Hello.lean}"
  [[ "${HELLO_FILE}" == *.lean ]] || fail "expected a Lean source entrypoint"
  while IFS= read -r local_source; do
    [[ -z "${local_source}" ]] || local_sources+=("${TASK_DIR}/${local_source}")
  done <<<"${ITPEVAL_LOCAL_SOURCES:-}"
fi

if [[ ! -x "${LEAN_BIN}" ]]; then
  fail "missing Lean binary at ${LEAN_BIN}; run install.sh first"
fi

if [[ ! -f "${HELLO_FILE}" ]]; then
  fail "missing hello file at ${HELLO_FILE}"
fi

itpeval_validate_statement_file "lean4" "${HELLO_FILE}"

export PATH="${LEAN_ROOT}/bin:${PREFIX}/bin:${PATH}"

run "${LEAN_BIN}" --version
lean_opts=()
if [[ -n "${ITPEVAL_LEAN_OPTIONS:-}" ]]; then
  while IFS= read -r option; do
    [[ "${option}" == -D*=* ]] || fail "malformed Lean option"
    lean_opts+=("${option}")
  done <<< "${ITPEVAL_LEAN_OPTIONS}"
fi
if [[ -n "${ITPEVAL_LEAN4_LEAN_PATH:-}" ]]; then
  export LEAN_PATH="${TASK_DIR}:${ITPEVAL_LEAN4_LEAN_PATH}"
fi

check_sources() {
  for source in ${local_sources[@]+"${local_sources[@]}"}; do
    run "$@" -o "${source%.lean}.olean" "${source}"
  done
  run "$@" "${HELLO_FILE}"
}

if (( ${#local_sources[@]} )); then
  export LEAN_PATH="${TASK_DIR}${LEAN_PATH:+:${LEAN_PATH}}"
fi
needs_mathlib=0
if grep -Eq "^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+Mathlib([[:space:].]|$)" "${HELLO_FILE}" ${local_sources[@]+"${local_sources[@]}"}; then
  needs_mathlib=1
fi

if [[ "${needs_mathlib}" == "1" ]]; then
  if [[ -n "${ITPEVAL_LEAN4_LEAN_PATH:-}" ]]; then
    export LEAN_PATH="${TASK_DIR}:${ITPEVAL_LEAN4_LEAN_PATH}"
    check_sources "${LEAN_BIN}" ${lean_opts[@]+"${lean_opts[@]}"}
  elif [[ -x "${LAKE_BIN}" ]] && [[ -f "${MATHLIB_PROJECT_DIR}/lakefile.lean" || -f "${MATHLIB_PROJECT_DIR}/lakefile.toml" ]]; then
    if [[ ! -f "${MATHLIB_OLEAN}" ]]; then
      fail "Hello.lean imports Mathlib, but Mathlib.olean is missing under ${MATHLIB_PROJECT_DIR}. Build or fetch Mathlib there, or set ITPEVAL_LEAN4_MATHLIB_PROJECT/ITPEVAL_LEAN4_LEAN_PATH."
    fi
    check_sources "${LAKE_BIN}" -d "${MATHLIB_PROJECT_DIR}" env "${LEAN_BIN}" ${lean_opts[@]+"${lean_opts[@]}"}
  else
    fail "Hello.lean imports Mathlib, but no Mathlib environment was found at ${MATHLIB_PROJECT_DIR}. Set ITPEVAL_LEAN4_MATHLIB_PROJECT or ITPEVAL_LEAN4_LEAN_PATH."
  fi
else
  check_sources "${LEAN_BIN}" ${lean_opts[@]+"${lean_opts[@]}"}
fi

log "check passed"

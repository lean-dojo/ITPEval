#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"

ISABELLE="${PREFIX}/isabelle/bin/isabelle"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"
ROOT_FILE="${TASK_DIR}/ROOT"

if [[ ! -x "${ISABELLE}" ]]; then
  fail "missing Isabelle executable at ${ISABELLE}; run install.sh first"
fi

if [[ ! -f "${ROOT_FILE}" ]]; then
  fail "missing ROOT file at ${ROOT_FILE}"
fi

shopt -s nullglob
for theory_file in "${TASK_DIR}"/*.thy; do
  itpeval_validate_statement_file "isabelle" "${theory_file}"
done
shopt -u nullglob

session_line="$(grep -m1 '^session' "${ROOT_FILE}" || true)"
session_name=""
if [[ "${session_line}" =~ session[[:space:]]+\"([^\"]+)\" ]]; then
  session_name="${BASH_REMATCH[1]}"
elif [[ "${session_line}" =~ session[[:space:]]+([^[:space:]]+) ]]; then
  session_name="${BASH_REMATCH[1]}"
fi

if [[ -z "${session_name}" ]]; then
  echo "[ITPEval] could not determine session name from ${ROOT_FILE}" >&2
  exit 1
fi

extra_opts=()
if command -v rg >/dev/null 2>&1; then
  sorry_found=$(rg -n --no-messages "\\bsorry\\b" "${TASK_DIR}"/*.thy 2>/dev/null && echo yes || echo no)
else
  sorry_found=$(grep -n '\bsorry\b' "${TASK_DIR}"/*.thy 2>/dev/null && echo yes || echo no)
fi
if [[ "${sorry_found}" == *yes ]]; then
  extra_opts+=(-o quick_and_dirty=true)
fi

# Repeated AgentTarget sessions must not share SQLite build/log databases.
# System HOL heaps remain readable; only this check's user state is isolated.
if [[ -n "${ITPEVAL_ISABELLE_USER_HOME:-}" ]]; then
  export USER_HOME="${ITPEVAL_ISABELLE_USER_HOME}"
else
  isabelle_task_home="$(mktemp -d "${TMPDIR:-/tmp}/itpeval-isabelle.XXXXXX")"
  trap 'rm -rf -- "${isabelle_task_home}"' EXIT
  export USER_HOME="${isabelle_task_home}"
fi

"${ISABELLE}" build ${extra_opts[@]+"${extra_opts[@]}"} -D "${TASK_DIR}" -b "${session_name}"

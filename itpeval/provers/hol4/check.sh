#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
HOL4_BIN_DIR="${PREFIX}/hol4/bin"
HOL4_SOURCE_DIR="${PREFIX}/hol4/src/HOL"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd -P)"

if [[ -x "${HOL4_BIN_DIR}/Holmake" ]]; then
  export PATH="${HOL4_BIN_DIR}:${PATH}"
fi
if [[ -d "${HOL4_SOURCE_DIR}" ]]; then
  export HOLDIR="${HOL4_SOURCE_DIR}"
fi

if ! command -v Holmake >/dev/null 2>&1; then
  fail "HOL4 check needs Holmake in PATH or in ${HOL4_BIN_DIR}; run install.sh first"
fi

BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/itpeval-hol4-check.XXXXXX")"
trap 'rm -rf "${BUILD_DIR}"' EXIT
tar --exclude='./.hol' -C "${TASK_DIR}" -cf - . | tar -C "${BUILD_DIR}" -xf -

if [[ -n "${ITPEVAL_TASK_FILE:-}" ]]; then
  if [[ "${ITPEVAL_TASK_FILE}" = /* ]]; then
    TASK_FILE_CANDIDATE="${ITPEVAL_TASK_FILE}"
  else
    TASK_FILE_CANDIDATE="${TASK_DIR}/${ITPEVAL_TASK_FILE}"
  fi
  if [[ "${TASK_FILE_CANDIDATE}" != *.sml ]]; then
    fail "HOL4 task file must have a .sml extension: ${TASK_FILE_CANDIDATE}"
  fi
  if [[ ! -f "${TASK_FILE_CANDIDATE}" ]]; then
    fail "missing HOL4 task file at ${TASK_FILE_CANDIDATE}"
  fi

  TASK_FILE="$(itpeval_realpath "${TASK_FILE_CANDIDATE}")"
  case "${TASK_FILE}" in
    "${TASK_DIR}"/*) ;;
    *) fail "HOL4 task file must resolve inside task directory: ${TASK_FILE}" ;;
  esac
  itpeval_validate_statement_file "hol4" "${TASK_FILE}"

  WRAPPER="${TASK_DIR}/helloScript.sml"
  if [[ ! -f "${WRAPPER}" ]]; then
    fail "missing HOL4 wrapper at ${WRAPPER}"
  fi
  marker='(* ITPEVAL_AGENT_TARGET *)'
  legacy_marker='val _ = use "AgentTarget.sml";'
  if ! grep -Fqx -- "${marker}" "${WRAPPER}" \
    && ! grep -Fqx -- "${legacy_marker}" "${WRAPPER}"; then
    fail "HOL4 wrapper is missing the target insertion marker"
  fi

  printf '%s\n' 'THEORIES = hello' >"${BUILD_DIR}/Holmakefile"
  while IFS= read -r line || [[ -n "${line}" ]]; do
    if [[ "${line}" == "${marker}" || "${line}" == "${legacy_marker}" ]]; then
      cat "${TASK_FILE}"
      printf '\n'
    else
      printf '%s\n' "${line}"
    fi
  done <"${WRAPPER}" >"${BUILD_DIR}/helloScript.sml"
fi

pushd "${BUILD_DIR}" >/dev/null
run Holmake
if [[ "${ITPEVAL_OPERATION:-legacy}" == proof_completion ]]; then
  if [[ ! -f itpeval-target-witness ]] || [[ "$(cat itpeval-target-witness)" != "${ITPEVAL_EXPECT_TARGET}" ]]; then
    fail "missing named HOL4 theorem witness"
  fi
  printf 'ITPEVAL_TARGET %s\n' "${ITPEVAL_EXPECT_TARGET}"
fi
popd >/dev/null

log "HOL4 task theory built successfully"

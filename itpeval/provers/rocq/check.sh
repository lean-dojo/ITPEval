#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

ROCQ_ID="${ITPEVAL_ROCQ_ID:-rocq}"
ROCQ_ROOT="$(itpeval_prefix)/${ROCQ_ID}"
OPAMROOT="${ITPEVAL_ROCQ_OPAMROOT:-${ROCQ_ROOT}/opamroot}"
SWITCH_NAME="${ROCQ_SWITCH_NAME:-rocq}"
TASK_DIR="${ITPEVAL_TASK_DIR:-${SCRIPT_DIR}/hello}"
if [[ ! -d "${TASK_DIR}" ]]; then
  fail "Missing task directory at ${TASK_DIR}"
fi
TASK_DIR="$(cd "${TASK_DIR}" && pwd)"
OPAM_CMD="${ROCQ_ROOT}/bin/opam"

entry=hello.v
local_sources=()
load_options=()
if [[ "${ITPEVAL_OPERATION:-legacy}" != legacy ]]; then
  entry="${ITPEVAL_TASK_FILE:-hello.v}"
  [[ "${entry}" == *.v ]] || fail "expected a Rocq source entrypoint"
  while IFS= read -r local_source; do
    [[ -z "${local_source}" ]] || local_sources+=("${local_source}")
  done <<<"${ITPEVAL_LOCAL_SOURCES:-}"
  while IFS=$'\t' read -r name directory; do
    [[ -z "${name}" ]] || load_options+=(-Q "${directory}" "${name}")
  done <<< "${ITPEVAL_ROCQ_LOAD_PATH:-}"
fi

check_sources() (
  cd "${TASK_DIR}"
  for source in ${local_sources[@]+"${local_sources[@]}"} "${entry}"; do
    run "$@" ${load_options[@]+"${load_options[@]}"} "${source}"
    test -f "${source%.v}.vo"
  done
)

itpeval_validate_statement_file rocq "${TASK_DIR}/${entry}"
if [[ -L "${ROCQ_ROOT}/bin/rocq" && -x "${ROCQ_ROOT}/bin/rocq" ]]; then
  compiler="$(itpeval_realpath "${ROCQ_ROOT}/bin/rocq")"
  check_sources "${compiler}" compile
  exit 0
fi

if [[ -x "${OPAM_CMD}" ]]; then
  opam_cmd="${OPAM_CMD}"
elif command -v opam >/dev/null 2>&1; then
  opam_cmd="$(command -v opam)"
else
  fail "opam not found; run install.sh first"
fi

if [[ ! -d "${OPAMROOT}" ]]; then
  fail "Rocq opam root not found at ${OPAMROOT}; run install.sh first."
fi

ROCQ_PATH="$("${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v rocq' || true)"
COQC_PATH="$("${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v coqc' || true)"

if [[ -n "${COQC_PATH}" ]]; then
  log "Using compiler: ${COQC_PATH}"
  check_sources "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- "${COQC_PATH}"
elif [[ -n "${ROCQ_PATH}" ]]; then
  log "Using compiler: ${ROCQ_PATH} (rocq compile)"
  check_sources "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- "${ROCQ_PATH}" compile
else
  fail "Neither rocq nor coqc found in opam switch ${SWITCH_NAME}"
fi
if [[ -n "${ROCQ_PATH}" ]]; then
  run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c '"$1" --version' sh "${ROCQ_PATH}"
else
  run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c '"$1" --version' sh "${COQC_PATH}"
fi

#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

ROCQ_ID="${ITPEVAL_ROCQ_ID:-rocq}"
ROCQ_ROOT="$(itpeval_prefix)/${ROCQ_ID}"
BIN_DIR="${ROCQ_ROOT}/bin"
ensure_dir "${BIN_DIR}"

if [[ -n "${ITPEVAL_ROCQ_BIN_DIR:-}" ]]; then
  external_bin="$(cd "${ITPEVAL_ROCQ_BIN_DIR}" && pwd -P)"
  [[ -x "${external_bin}/rocq" ]] || fail "missing Rocq compiler in ${external_bin}"
  run "${external_bin}/rocq" --version
  for name in rocq coqc coqidetop; do
    if [[ -x "${external_bin}/${name}" ]]; then
      ln -sf "${external_bin}/${name}" "${BIN_DIR}/${name}"
      link_into_prefix_bin "${BIN_DIR}/${name}" "${name}"
    fi
  done
  exit 0
fi

opam_cmd="opam"
if [[ -x "${BIN_DIR}/opam" ]]; then
  opam_cmd="${BIN_DIR}/opam"
elif ! command -v opam >/dev/null 2>&1; then
  OPAM_VERSION="${ITPEVAL_OPAM_VERSION:-2.5.0}"
  OPAM_SHA256="${ITPEVAL_OPAM_SHA256:-$(itpeval_manifest_get rocq.opam-binary sha256 2>/dev/null || true)}"
  arch="$(uname -m)"
  case "${arch}" in
    x86_64) opam_asset="opam-${OPAM_VERSION}-x86_64-linux" ;;
    aarch64|arm64) opam_asset="opam-${OPAM_VERSION}-arm64-linux" ;;
    *) fail "unsupported architecture for opam binary: ${arch}" ;;
  esac

  url="https://github.com/ocaml/opam/releases/download/${OPAM_VERSION}/${opam_asset}"
  log "opam not found; downloading ${url} to ${BIN_DIR}/opam"
  download_cached "${url}" "${OPAM_SHA256}" "${BIN_DIR}/opam"
  run chmod +x "${BIN_DIR}/opam"
  opam_cmd="${BIN_DIR}/opam"
fi

OPAMROOT="${ROCQ_ROOT}/opamroot"
OPAMROOT="${ITPEVAL_ROCQ_OPAMROOT:-${OPAMROOT}}"
SWITCH_NAME="${ROCQ_SWITCH_NAME:-rocq}"
ROCQ_VERSION="${ROCQ_VERSION:-9.0.0}"
OCAML_VERSION="${OCAML_VERSION:-4.14.2}"
OPAM_REPO_URL="${ITPEVAL_OPAM_REPO_URL:-https://opam.ocaml.org}"

ensure_dir "${ROCQ_ROOT}"
ensure_dir "${OPAMROOT}"

if command -v flock >/dev/null 2>&1; then
  lock_file="${OPAMROOT}/itpeval.install.lock"
  exec 9>"${lock_file}"
  if ! flock -n 9; then
    fail "Another Rocq install appears to be running for OPAMROOT=${OPAMROOT} (lock: ${lock_file})"
  fi
fi

log "Rocq root: ${ROCQ_ROOT}"
log "Opam root: ${OPAMROOT}"
log "Switch: ${SWITCH_NAME}"
log "Version: ${ROCQ_VERSION}"
log "Opam repo: ${OPAM_REPO_URL}"

opam_reinit=()
if [[ -f "${OPAMROOT}/config" ]]; then
  opam_reinit=(--reinit)
fi
run "${opam_cmd}" init -y ${opam_reinit[@]+"${opam_reinit[@]}"} --bare --disable-sandboxing --root "${OPAMROOT}" --no-setup default "${OPAM_REPO_URL}"

if ! "${opam_cmd}" switch list --root "${OPAMROOT}" --short | grep -Fxq "${SWITCH_NAME}"; then
  if ! "${opam_cmd}" switch create "${SWITCH_NAME}" "ocaml-base-compiler.${OCAML_VERSION}" --root "${OPAMROOT}"; then
    if command -v ocamlc >/dev/null 2>&1; then
      log "Falling back to ocaml-system (detected system ocamlc=$(ocamlc -version))"
      run "${opam_cmd}" switch create "${SWITCH_NAME}" ocaml-system --root "${OPAMROOT}"
    else
      fail "Failed to create opam switch ${SWITCH_NAME}; try setting ITPEVAL_OPAM_REPO_URL=git+https://github.com/ocaml/opam-repository.git"
    fi
  fi
fi

ROCQ_PIN_ALL="${ROCQ_PIN_ALL:-0}"
if [[ "${ROCQ_PIN_ALL}" == "1" ]]; then
  log "Pinning Rocq components to ${ROCQ_VERSION} (ROCQ_PIN_ALL=1)"
  run "${opam_cmd}" pin add --no-action --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y rocq-core "${ROCQ_VERSION}"
  run "${opam_cmd}" pin add --no-action --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y rocq-runtime "${ROCQ_VERSION}"
  run "${opam_cmd}" pin add --no-action --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y rocq-stdlib "${ROCQ_VERSION}" || true
fi

if command -v rpm >/dev/null 2>&1; then
  if ! rpm -q gmp-devel >/dev/null 2>&1; then
    if command -v dnf >/dev/null 2>&1; then
      run sudo dnf install -y gmp-devel
    elif command -v yum >/dev/null 2>&1; then
      run sudo yum install -y gmp-devel
    else
      fail "Missing gmp-devel (needed by zarith); install it via your system package manager and retry"
    fi
  fi
fi

if [[ -n "${ITPEVAL_OPAM_PACKAGES:-}" ]]; then
  # A qualified release locks core, runtime and Stdlib independently.
  read -r -a packages <<< "${ITPEVAL_OPAM_PACKAGES}"
  run "${opam_cmd}" install --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y "${packages[@]}"
else
  run "${opam_cmd}" repo add --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y rocq-released https://rocq-prover.org/opam/released || true
  if ! "${opam_cmd}" pin add --no-action --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y rocq-prover "${ROCQ_VERSION}"; then
    log "Available rocq-prover versions:"
    "${opam_cmd}" show --root "${OPAMROOT}" --switch "${SWITCH_NAME}" rocq-prover --all-versions || true
    fail "rocq-prover has no known version ${ROCQ_VERSION}; set ROCQ_VERSION to one of the versions above"
  fi
  run "${opam_cmd}" install --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -y rocq-prover
fi

run "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- rocq --version
rocq_path="$("${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v rocq')"
coqc_path="$("${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- sh -c 'command -v coqc' || true)"

cat > "${BIN_DIR}/rocq" <<EOF
#!/usr/bin/env bash
set -euo pipefail
exec "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- rocq "\$@"
EOF

if [[ -n "${coqc_path}" ]]; then
  cat > "${BIN_DIR}/coqc" <<EOF
#!/usr/bin/env bash
set -euo pipefail
exec "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- "${coqc_path}" "\$@"
EOF
else
  cat > "${BIN_DIR}/coqc" <<EOF
#!/usr/bin/env bash
set -euo pipefail
exec "${opam_cmd}" exec --root "${OPAMROOT}" --switch "${SWITCH_NAME}" -- "${rocq_path}" compile "\$@"
EOF
fi

# The extractor queries the IDE protocol for every category of pending goal.
# Keep the executable paired with the rocq compiler in this exact switch.
ide_path="$(dirname "${rocq_path}")/coqidetop"
if [[ -x "${ide_path}" ]]; then
  ln -sf "${ide_path}" "${BIN_DIR}/coqidetop"
elif [[ -n "${ITPEVAL_OPAM_PACKAGES:-}" ]]; then
  fail "the pinned RocqIDE server is missing from ${SWITCH_NAME}"
fi

run chmod +x "${BIN_DIR}/rocq" "${BIN_DIR}/coqc"
if [[ "${ROCQ_ID}" == "rocq" ]]; then
  link_into_prefix_bin "${BIN_DIR}/rocq" "rocq"
  link_into_prefix_bin "${BIN_DIR}/coqc" "coqc"
fi

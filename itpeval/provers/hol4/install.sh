#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
INSTALL_ROOT="${PREFIX}/hol4"
BIN_DIR="${INSTALL_ROOT}/bin"
SOURCE_DIR="${INSTALL_ROOT}/src/HOL"
POLYML_PREFIX="${INSTALL_ROOT}/polyml"
POLYML_SRC="${INSTALL_ROOT}/src/polyml"

HOL4_REPO_URL="${ITPEVAL_HOL4_REPO_URL:-https://github.com/HOL-Theorem-Prover/HOL.git}"
POLYML_REPO_URL="${ITPEVAL_POLYML_REPO_URL:-https://github.com/polyml/polyml.git}"
POLYML_VERSION="${ITPEVAL_POLYML_VERSION:-v5.9.2}"

ensure_dir "${BIN_DIR}"
ensure_dir "${SOURCE_DIR}"
ensure_dir "${POLYML_PREFIX}"
ensure_dir "${POLYML_SRC}"

wrap_binary() {
  local binary_path="$1"
  local name="$2"
  local holdir="${3:-}"
  local extra_ld_path="${4:-}"
  local holdir_export=""
  local ld_export=""
  if [[ -n "${holdir}" ]]; then
    holdir_export="export HOLDIR=\"${holdir}\""
  fi
  if [[ -n "${extra_ld_path}" ]]; then
    ld_export="export LD_LIBRARY_PATH=\"${extra_ld_path}:\${LD_LIBRARY_PATH:-}\""
  fi
  cat >"${BIN_DIR}/${name}" <<EOF
#!/usr/bin/env bash
${holdir_export}
${ld_export}
exec "${binary_path}" "\$@"
EOF
  chmod +x "${BIN_DIR}/${name}"
  link_into_prefix_bin "${BIN_DIR}/${name}" "${name}"
}

source_root=""
if [[ -n "${ITPEVAL_HOL4_HOME:-}" ]]; then
  source_root="${ITPEVAL_HOL4_HOME}"
elif [[ -n "${HOL4_HOME:-}" ]]; then
  source_root="${HOL4_HOME}"
elif [[ -n "${ITPEVAL_HOL4_SRC:-}" ]]; then
  source_root="${ITPEVAL_HOL4_SRC}"
fi

if [[ -n "${source_root}" ]]; then
  if [[ -x "${source_root}/bin/Holmake" ]]; then
    wrap_binary "${source_root}/bin/Holmake" "Holmake" "${source_root}"
  fi
  if [[ -x "${source_root}/bin/hol" ]]; then
    wrap_binary "${source_root}/bin/hol" "hol" "${source_root}"
  fi
  if [[ -x "${source_root}/tools/Holmake" && ! -x "${BIN_DIR}/Holmake" ]]; then
    wrap_binary "${source_root}/tools/Holmake" "Holmake" "${source_root}"
  fi

  if [[ -x "${BIN_DIR}/Holmake" ]]; then
    log "HOL4 wired from existing source tree: ${source_root}"
    exit 0
  fi
fi

if command -v hol >/dev/null 2>&1 && command -v Holmake >/dev/null 2>&1; then
  wrap_binary "$(command -v hol)" "hol"
  wrap_binary "$(command -v Holmake)" "Holmake"
  log "HOL4 wired from PATH into ${INSTALL_ROOT}"
  exit 0
fi

if command -v dnf >/dev/null 2>&1; then
  # Poly/ML + HOL4 build deps (best-effort).
  needed_pkgs=(git make gcc gcc-c++ gmp-devel libffi-devel zlib-devel)
  missing_pkgs=()
  if command -v rpm >/dev/null 2>&1; then
    for pkg in "${needed_pkgs[@]}"; do
      if ! rpm -q "${pkg}" >/dev/null 2>&1; then
        missing_pkgs+=("${pkg}")
      fi
    done
  else
    missing_pkgs=("${needed_pkgs[@]}")
  fi
  if ((${#missing_pkgs[@]})); then
    log "Installing HOL4 build dependencies via dnf: ${missing_pkgs[*]}"
    run sudo dnf -y install "${missing_pkgs[@]}"
  fi
fi

poly_bin="${POLYML_PREFIX}/bin/poly"
if [[ ! -x "${poly_bin}" ]]; then
  log "Bootstrapping Poly/ML (${POLYML_VERSION}) into ${POLYML_PREFIX}"
  if [[ ! -d "${POLYML_SRC}/.git" ]]; then
    rm -rf "${POLYML_SRC}"
    ensure_dir "$(dirname "${POLYML_SRC}")"
    run git clone --depth 1 --branch "${POLYML_VERSION}" "${POLYML_REPO_URL}" "${POLYML_SRC}"
  fi
  (
    cd "${POLYML_SRC}"
    run ./configure --prefix="${POLYML_PREFIX}"
    jobs="$(command -v nproc >/dev/null 2>&1 && nproc || echo 2)"
    run make -j"${jobs}"
    run make install
  )
fi

poly_lib_dir=""
if [[ -d "${POLYML_PREFIX}/lib" ]]; then
  poly_lib_dir="${POLYML_PREFIX}/lib"
elif [[ -d "${POLYML_PREFIX}/lib64" ]]; then
  poly_lib_dir="${POLYML_PREFIX}/lib64"
fi
export PATH="${POLYML_PREFIX}/bin:${PATH}"
if [[ -n "${poly_lib_dir}" ]]; then
  export LD_LIBRARY_PATH="${poly_lib_dir}:${LD_LIBRARY_PATH:-}"
fi

if [[ ! -d "${SOURCE_DIR}/.git" ]]; then
  rm -rf "${SOURCE_DIR}"
  ensure_dir "$(dirname "${SOURCE_DIR}")"
  log "Cloning HOL4 from ${HOL4_REPO_URL} into ${SOURCE_DIR}"
  run git clone --depth 1 "${HOL4_REPO_URL}" "${SOURCE_DIR}"
fi

if [[ ! -x "${SOURCE_DIR}/bin/Holmake" || ! -x "${SOURCE_DIR}/bin/hol" ]]; then
  log "Configuring HOL4 with Poly/ML"
  (
    cd "${SOURCE_DIR}"
    run poly --script tools/smart-configure.sml
    log "Building HOL4 (this can take a while)"
    run bin/build
  )
fi

if [[ ! -x "${SOURCE_DIR}/bin/Holmake" || ! -x "${SOURCE_DIR}/bin/hol" ]]; then
  fail "HOL4 build completed but expected binaries are missing under ${SOURCE_DIR}/bin"
fi

wrap_binary "${SOURCE_DIR}/bin/hol" "hol" "${SOURCE_DIR}" "${poly_lib_dir}"
wrap_binary "${SOURCE_DIR}/bin/Holmake" "Holmake" "${SOURCE_DIR}" "${poly_lib_dir}"
log "HOL4 installed at ${SOURCE_DIR} (wrappers in ${BIN_DIR})"

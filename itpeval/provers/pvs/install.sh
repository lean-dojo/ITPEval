#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
INSTALL_ROOT="${PREFIX}/pvs"
BIN_DIR="${INSTALL_ROOT}/bin"

ensure_dir "${BIN_DIR}"

wrap_binary() {
  local binary_path="$1"
  local name="$2"
  local extra_exports="${3:-}"
  cat >"${BIN_DIR}/${name}" <<EOF
#!/bin/sh
${extra_exports}
exec "${binary_path}" "\$@"
EOF
  chmod +x "${BIN_DIR}/${name}"
  link_into_prefix_bin "${BIN_DIR}/${name}" "${name}"
}

extract_tarball() {
  local tarball_path="$1"
  local target_dir="$2"
  local tmp_dir
  tmp_dir="$(mktemp -d)"
  tar -xf "${tarball_path}" -C "${tmp_dir}"
  local extracted_root
  extracted_root="$(find "${tmp_dir}" -mindepth 1 -maxdepth 1 | head -n 1)"
  if [[ -d "${extracted_root}" ]]; then
    mkdir -p "${target_dir}"
    cp -a "${extracted_root}/." "${target_dir}/"
  fi
  rm -rf "${tmp_dir}"
}

have_emacs() {
  if command -v emacs >/dev/null 2>&1; then
    return 0
  fi
  if [[ -n "${PVSEMACS:-}" && -x "${PVSEMACS}" ]]; then
    return 0
  fi
  return 1
}

relocate_pvspath_only() {
  local root="$1"
  for script in pvs pvsio proveit; do
    if [[ -f "${root}/${script}" ]]; then
      run chmod u+w "${root}/${script}"
      run sed -i.bak -e "s,^PVSPATH=.*$,PVSPATH=${root}," "${root}/${script}"
      run chmod a+x "${root}/${script}"
      rm -f "${root}/${script}.bak"
    fi
  done
  if [[ -f "${root}/provethem" ]]; then
    run chmod u+w "${root}/provethem"
    run sed -i.bak -e "s,^\\$PVSPATH=.*$,\\$PVSPATH=\\\"${root}\\\";," "${root}/provethem"
    run chmod a+x "${root}/provethem"
    rm -f "${root}/provethem.bak"
  fi
}

wire_installed_tree() {
  local root="$1"
  local exports=""
  exports="export PVSPATH=\"${root}\""

  if [[ -x "${root}/pvs" ]]; then
    wrap_binary "${root}/pvs" "pvs" "${exports}"
  elif [[ -x "${root}/bin/pvs" ]]; then
    wrap_binary "${root}/bin/pvs" "pvs" "${exports}"
  fi

  for name in proveit pvsio provethem; do
    if [[ -x "${root}/${name}" ]]; then
      wrap_binary "${root}/${name}" "${name}" "${exports}"
    elif [[ -x "${root}/bin/${name}" ]]; then
      wrap_binary "${root}/bin/${name}" "${name}" "${exports}"
    fi
  done
}

if [[ -x "${INSTALL_ROOT}/pvs" || -x "${INSTALL_ROOT}/bin/pvs" || -x "${INSTALL_ROOT}/proveit" || -x "${INSTALL_ROOT}/bin/proveit" ]]; then
  wire_installed_tree "${INSTALL_ROOT}"
  log "PVS already installed under ${INSTALL_ROOT}"
  exit 0
fi

source_root=""
if [[ -n "${ITPEVAL_PVS_HOME:-}" ]]; then
  source_root="${ITPEVAL_PVS_HOME}"
elif [[ -n "${PVS_HOME:-}" ]]; then
  source_root="${PVS_HOME}"
elif [[ -n "${ITPEVAL_PVS_SRC:-}" ]]; then
  source_root="${ITPEVAL_PVS_SRC}"
fi

if [[ -n "${source_root}" ]]; then
  wire_installed_tree "${source_root}"
  if [[ -x "${BIN_DIR}/pvs" || -x "${BIN_DIR}/proveit" ]]; then
    log "PVS wired from existing tree: ${source_root}"
    exit 0
  fi
fi

tarball_path="${ITPEVAL_PVS_TARBALL:-${PVS_TARBALL:-}}"
if [[ -n "${tarball_path}" ]]; then
  if [[ ! -f "${tarball_path}" ]]; then
    fail "PVS tarball not found: ${tarball_path}"
  fi
  extract_tarball "${tarball_path}" "${INSTALL_ROOT}"
  if [[ -x "${INSTALL_ROOT}/install-sh" ]]; then
    if have_emacs; then
      (cd "${INSTALL_ROOT}" && run ./install-sh)
    else
      log "emacs not found; patching PVSPATH in scripts (skipping ./install-sh byte compilation)"
      relocate_pvspath_only "${INSTALL_ROOT}"
    fi
  fi
  wire_installed_tree "${INSTALL_ROOT}"
  log "PVS installed from tarball into ${INSTALL_ROOT}"
  exit 0
fi

if command -v pvs >/dev/null 2>&1; then
  pvs_path="$(command -v pvs)"
  pvs_dir="$(cd "$(dirname "${pvs_path}")" && pwd)"
  pvs_root="${pvs_dir}"
  if [[ "${pvs_dir}" == */bin ]]; then
    pvs_root="$(cd "${pvs_dir}/.." && pwd)"
  fi
  wire_installed_tree "${pvs_root}"
  log "PVS wired from PATH into ${INSTALL_ROOT}"
  exit 0
fi

arch="$(uname -m)"
platform="$(uname -s)"

if [[ -n "${ITPEVAL_PVS_VERSION:-}" || -n "${ITPEVAL_PVS_LISP:-}" ]]; then
  # Preserve the legacy SRI download convention for callers that explicitly
  # opt into the old version/lisp overrides.
  PVS_VERSION="${ITPEVAL_PVS_VERSION:-7.1.0}"
  PVS_LISP="${ITPEVAL_PVS_LISP:-sbclisp}"
  case "${arch}" in
    x86_64) pvs_arch="ix86_64" ;;
    aarch64|arm64) pvs_arch="aarch64" ;;
    *) fail "unsupported architecture for PVS binaries: ${arch}" ;;
  esac
  case "${platform}" in
    Linux) pvs_platform="Linux" ;;
    Darwin) pvs_platform="MacOSX" ;;
    *) fail "unsupported platform for PVS binaries: ${platform}" ;;
  esac
  default_url="https://pvs.csl.sri.com/downloads/pvs${PVS_VERSION}-${pvs_arch}-${pvs_platform}-${PVS_LISP}.tgz"
  release_label="PVS ${PVS_VERSION} (${pvs_platform} ${pvs_arch} ${PVS_LISP})"
else
  PVS_RELEASE_TAG="${ITPEVAL_PVS_RELEASE_TAG:-pvs8.1-master-20260624}"
  PVS_RELEASE_BUILD="${ITPEVAL_PVS_RELEASE_BUILD:-master-20260624}"
  case "${platform}:${arch}" in
    Darwin:arm64|Darwin:aarch64) pvs_asset="macos-arm64" ;;
    Darwin:x86_64) pvs_asset="macos-x86_64" ;;
    Linux:arm64|Linux:aarch64) pvs_asset="linux-aarch64" ;;
    Linux:x86_64) pvs_asset="linux-x86_64" ;;
    *) fail "unsupported platform/architecture for PVS binaries: ${platform}/${arch}" ;;
  esac
  default_url="https://github.com/SRI-CSL/PVS/releases/download/${PVS_RELEASE_TAG}/pvs-${PVS_RELEASE_BUILD}-${pvs_asset}.tgz"
  release_label="PVS release ${PVS_RELEASE_TAG} (${pvs_asset})"
fi

tarball_url="${ITPEVAL_PVS_TARBALL_URL:-${default_url}}"

log "Downloading ${release_label}"
log "URL: ${tarball_url}"
download_path="$(download_cached "${tarball_url}" "" "")"

extract_tarball "${download_path}" "${INSTALL_ROOT}"
if [[ -x "${INSTALL_ROOT}/install-sh" ]]; then
  if have_emacs; then
    (cd "${INSTALL_ROOT}" && run ./install-sh)
  else
    log "emacs not found; patching PVSPATH in scripts (skipping ./install-sh byte compilation)"
    relocate_pvspath_only "${INSTALL_ROOT}"
  fi
fi
wire_installed_tree "${INSTALL_ROOT}"
log "PVS installed into ${INSTALL_ROOT}"

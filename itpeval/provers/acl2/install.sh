#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
INSTALL_ROOT="${PREFIX}/acl2"
BIN_DIR="${INSTALL_ROOT}/bin"
SRC_ROOT="${INSTALL_ROOT}/src"

ensure_dir "${BIN_DIR}"
ensure_dir "${SRC_ROOT}"

wrap_binary() {
  local binary_path="$1"
  local name="$2"
  cat >"${BIN_DIR}/${name}" <<EOF
#!/usr/bin/env bash
exec "${binary_path}" "\$@"
EOF
  chmod +x "${BIN_DIR}/${name}"
  link_into_prefix_bin "${BIN_DIR}/${name}" "${name}"
}

certify_books() {
  local source_dir="$1"
  local acl2_binary="$2"
  local targets="${ITPEVAL_ACL2_BOOK_TARGETS:-basic}"
  local jobs="${ITPEVAL_ACL2_BOOK_JOBS:-8}"
  local -a target_args

  if [[ -z "${targets}" || "${targets}" == "none" ]]; then
    log "Skipping ACL2 community-book certification"
    return 0
  fi
  if [[ ! -f "${source_dir}/books/GNUmakefile" ]]; then
    fail "ACL2 community-book GNUmakefile is missing under ${source_dir}/books"
  fi
  if [[ ! "${jobs}" =~ ^[1-9][0-9]*$ ]]; then
    fail "ITPEVAL_ACL2_BOOK_JOBS must be a positive integer"
  fi

  read -r -a target_args <<<"${targets}"
  log "Certifying ACL2 community books: ${targets} (${jobs} workers)"
  (
    cd "${source_dir}/books"
    export ACL2_SYSTEM_BOOKS="${source_dir}/books"
    run make -f GNUmakefile -j "${jobs}" \
      "ACL2=${acl2_binary}" \
      "${target_args[@]}"
  )
}

install_sbcl() {
  local sbcl_root="${INSTALL_ROOT}/sbcl"
  local sbcl_bin="${sbcl_root}/bin/sbcl"
  if [[ -x "${sbcl_bin}" ]]; then
    echo "${sbcl_bin}"
    return 0
  fi

  local sbcl_version="${ITPEVAL_SBCL_VERSION:-2.4.0}"
  local sbcl_url="${ITPEVAL_SBCL_URL:-https://sourceforge.net/projects/sbcl/files/sbcl/${sbcl_version}/sbcl-${sbcl_version}-x86-64-linux-binary.tar.bz2/download}"
  local archive_path="${INSTALL_ROOT}/sbcl-${sbcl_version}-x86-64-linux-binary.tar.bz2"

  if ! command -v bzip2 >/dev/null 2>&1; then
    if command -v dnf >/dev/null 2>&1; then
      log "Installing bzip2 via dnf (required to unpack SBCL)"
      run sudo dnf -y install bzip2 tar
    fi
  fi
  if ! command -v bzip2 >/dev/null 2>&1; then
    fail "bzip2 is required to unpack SBCL; install it and retry"
  fi

  log "Bootstrapping SBCL ${sbcl_version} from ${sbcl_url}"
  download_cached "${sbcl_url}" "" "${archive_path}" >/dev/null

  local tmp_dir extracted
  tmp_dir="$(mktemp -d)"
  run tar -xjf "${archive_path}" -C "${tmp_dir}"

  extracted="$(find "${tmp_dir}" -mindepth 1 -maxdepth 1 -type d -name 'sbcl-*' | head -n 1 || true)"
  if [[ -z "${extracted}" || ! -x "${extracted}/install.sh" ]]; then
    rm -rf "${tmp_dir}"
    fail "unexpected SBCL archive layout in ${archive_path}"
  fi

  ensure_dir "${sbcl_root}"
  (
    cd "${extracted}"
    # Redirect SBCL installer output away from stdout so callers can safely use
    # command substitution on this function.
    sh ./install.sh --prefix="${sbcl_root}" 1>&2
  )
  rm -rf "${tmp_dir}"

  if [[ ! -x "${sbcl_bin}" ]]; then
    fail "SBCL install completed but ${sbcl_bin} is missing"
  fi

  echo "${sbcl_bin}"
}

source_root=""
if [[ -n "${ITPEVAL_ACL2_HOME:-}" ]]; then
  source_root="${ITPEVAL_ACL2_HOME}"
elif [[ -n "${ACL2_HOME:-}" ]]; then
  source_root="${ACL2_HOME}"
elif [[ -n "${ITPEVAL_ACL2_SRC:-}" ]]; then
  source_root="${ITPEVAL_ACL2_SRC}"
fi

if [[ -n "${source_root}" ]]; then
  if [[ -x "${source_root}/saved_acl2" ]]; then
    wrap_binary "${source_root}/saved_acl2" "saved_acl2"
    cat >"${BIN_DIR}/acl2" <<EOF
#!/usr/bin/env bash
set -euo pipefail
export ACL2_SYSTEM_BOOKS="${source_root}/books"
exec "${source_root}/saved_acl2" "\$@"
EOF
    chmod +x "${BIN_DIR}/acl2"
    link_into_prefix_bin "${BIN_DIR}/acl2" "acl2"
    certify_books "${source_root}" "${source_root}/saved_acl2"
    log "ACL2 wired from existing source tree: ${source_root}"
    exit 0
  fi
fi

ACL2_VERSION="${ITPEVAL_ACL2_VERSION:-${ACL2_VERSION:-8.6}}"
ACL2_TARBALL_URL="${ITPEVAL_ACL2_TARBALL_URL:-https://github.com/acl2-devel/acl2-devel/releases/download/${ACL2_VERSION}/acl2-${ACL2_VERSION}.tar.gz}"

acl2_dir="${SRC_ROOT}/acl2-${ACL2_VERSION}"
saved_acl2="${acl2_dir}/saved_acl2"

if [[ -x "${saved_acl2}" ]]; then
  wrap_binary "${saved_acl2}" "saved_acl2"
  cat >"${BIN_DIR}/acl2" <<EOF
#!/usr/bin/env bash
set -euo pipefail
export ACL2_SYSTEM_BOOKS="${acl2_dir}/books"
exec "${saved_acl2}" "\$@"
EOF
  chmod +x "${BIN_DIR}/acl2"
  link_into_prefix_bin "${BIN_DIR}/acl2" "acl2"
  certify_books "${acl2_dir}" "${saved_acl2}"
  log "ACL2 already built at ${acl2_dir}"
  exit 0
fi

tarball_path="${INSTALL_ROOT}/acl2-${ACL2_VERSION}.tar.gz"
log "Downloading ACL2 ${ACL2_VERSION} source tarball"
download_cached "${ACL2_TARBALL_URL}" "" "${tarball_path}"

rm -rf "${acl2_dir}"
ensure_dir "${SRC_ROOT}"
run tar -xzf "${tarball_path}" -C "${SRC_ROOT}"

if [[ ! -d "${acl2_dir}" ]]; then
  fail "expected ACL2 source directory at ${acl2_dir} after extracting ${tarball_path}"
fi

LISP_BIN="${ITPEVAL_ACL2_LISP:-}"
if [[ -z "${LISP_BIN}" ]]; then
  if command -v sbcl >/dev/null 2>&1; then
    LISP_BIN="$(command -v sbcl)"
  fi
fi

if [[ -z "${LISP_BIN}" ]]; then
  if command -v dnf >/dev/null 2>&1; then
    run sudo dnf -y install make gcc || true
  fi
  LISP_BIN="$(install_sbcl)"
fi

if [[ -z "${LISP_BIN}" ]]; then
  fail "SBCL not found. Install sbcl and retry, or set ITPEVAL_ACL2_LISP=/path/to/sbcl"
fi

log "Building ACL2 with LISP=${LISP_BIN}"
(
  cd "${acl2_dir}"
  run make "LISP=${LISP_BIN}"
)

if [[ ! -x "${saved_acl2}" ]]; then
  fail "ACL2 build completed but ${saved_acl2} is missing"
fi

wrap_binary "${saved_acl2}" "saved_acl2"
cat >"${BIN_DIR}/acl2" <<EOF
#!/usr/bin/env bash
set -euo pipefail
export ACL2_SYSTEM_BOOKS="${acl2_dir}/books"
exec "${saved_acl2}" "\$@"
EOF
chmod +x "${BIN_DIR}/acl2"
link_into_prefix_bin "${BIN_DIR}/acl2" "acl2"

certify_books "${acl2_dir}" "${saved_acl2}"
log "ACL2 installed into ${INSTALL_ROOT}"

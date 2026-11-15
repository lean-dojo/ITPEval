#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../../bin/common.sh
source "${SCRIPT_DIR}/../../bin/common.sh"

PREFIX="$(itpeval_prefix)"
INSTALL_ROOT="${PREFIX}/mizar"
BIN_DIR="${INSTALL_ROOT}/bin"

ensure_dir "${BIN_DIR}"

make_install_dir() {
  local root=""
  local candidate=""
  for root in "${ITPEVAL_TMPDIR:-}" "${TMPDIR:-}" /tmp /var/tmp; do
    if [[ -z "${root}" || ! -d "${root}" || ! -w "${root}" ]]; then
      continue
    fi
    if candidate="$(mktemp -d "${root%/}/itpeval-mizar-install.XXXXXX" 2>/dev/null)"; then
      printf '%s\n' "${candidate}"
      return 0
    fi
  done
  fail "unable to create a Mizar install directory; set ITPEVAL_TMPDIR to writable local storage"
}

is_mizfiles_root() {
  local root="$1"
  [[ -d "${root}/abstr" ]] &&
    [[ -d "${root}/prel" || -d "${root}/mml" || -d "${root}/dict" ]]
}

detect_mizfiles() {
  local candidate=""
  if [[ -n "${ITPEVAL_MIZFILES:-}" ]]; then
    candidate="${ITPEVAL_MIZFILES}"
  elif [[ -n "${MIZFILES:-}" ]]; then
    candidate="${MIZFILES}"
  else
    for root in "${ITPEVAL_MIZAR_HOME:-}" "${MIZAR_HOME:-}" "${ITPEVAL_MIZAR_SRC:-}"; do
      [[ -z "${root}" ]] && continue
      for probe in "${root}" "${root}/share" "${root}/share/mizar" "${root}/mizar" "${root}/data/mizar"; do
        if is_mizfiles_root "${probe}"; then
          candidate="${probe}"
          break 2
        fi
      done
    done
  fi
  echo "${candidate}"
}

wrap_binary() {
  local binary_path="$1"
  local name="$2"
  local mizfiles_root="${3:-}"
  local binary_dir
  binary_dir="$(cd "$(dirname "${binary_path}")" && pwd)"
  cat >"${BIN_DIR}/${name}" <<EOF
#!/usr/bin/env bash
set -euo pipefail
export PATH="${binary_dir}:\${PATH}"
EOF
  if [[ -n "${mizfiles_root}" ]]; then
    cat >>"${BIN_DIR}/${name}" <<EOF
export MIZFILES="${mizfiles_root}"
EOF
  fi
  cat >>"${BIN_DIR}/${name}" <<EOF
exec "${binary_path}" "\$@"
EOF
  chmod +x "${BIN_DIR}/${name}"
  link_into_prefix_bin "${BIN_DIR}/${name}" "${name}"
}

source_root=""
if [[ -n "${ITPEVAL_MIZAR_HOME:-}" ]]; then
  source_root="${ITPEVAL_MIZAR_HOME}"
elif [[ -n "${MIZAR_HOME:-}" ]]; then
  source_root="${MIZAR_HOME}"
elif [[ -n "${ITPEVAL_MIZAR_SRC:-}" ]]; then
  source_root="${ITPEVAL_MIZAR_SRC}"
fi

mizfiles_root="$(detect_mizfiles)"
if [[ -z "${mizfiles_root}" && -n "${source_root}" ]]; then
  for probe in "${source_root}" "${source_root}/share" "${source_root}/share/mizar" "${source_root}/mizar" "${source_root}/data/mizar"; do
    if is_mizfiles_root "${probe}"; then
      mizfiles_root="${probe}"
      break
    fi
  done
fi

if [[ -n "${source_root}" ]]; then
  if [[ -x "${source_root}/bin/mizf" ]]; then
    wrap_binary "${source_root}/bin/mizf" "mizf" "${mizfiles_root}"
  elif [[ -x "${source_root}/mizf" ]]; then
    wrap_binary "${source_root}/mizf" "mizf" "${mizfiles_root}"
  fi

  for name in accom verifier exporter makeenv miz2prel errflag addfmsg; do
    if [[ -x "${source_root}/bin/${name}" ]]; then
      wrap_binary "${source_root}/bin/${name}" "${name}" "${mizfiles_root}"
    elif [[ -x "${source_root}/${name}" && ! -x "${BIN_DIR}/${name}" ]]; then
      wrap_binary "${source_root}/${name}" "${name}" "${mizfiles_root}"
    fi
  done

  if [[ -x "${BIN_DIR}/mizf" || -x "${BIN_DIR}/verifier" ]]; then
    log "Mizar wired from existing tree: ${source_root}"
    if [[ -n "${mizfiles_root}" ]]; then
      log "MIZFILES root detected at: ${mizfiles_root}"
    fi
    exit 0
  fi
fi

if command -v mizf >/dev/null 2>&1 || command -v verifier >/dev/null 2>&1; then
  if command -v mizf >/dev/null 2>&1; then
    wrap_binary "$(command -v mizf)" "mizf" "${mizfiles_root}"
  fi
  for name in accom verifier exporter makeenv miz2prel errflag addfmsg; do
    if command -v "${name}" >/dev/null 2>&1; then
      wrap_binary "$(command -v "${name}")" "${name}" "${mizfiles_root}"
    fi
  done
  log "Mizar wired from PATH into ${INSTALL_ROOT}"
  if [[ -n "${mizfiles_root}" ]]; then
    log "MIZFILES root detected at: ${mizfiles_root}"
  fi
  exit 0
fi

MIZAR_BASE_URL="${ITPEVAL_MIZAR_BASE_URL:-http://mizar.uwb.edu.pl/~softadm/current}"
ARCHIVE_DIR="${INSTALL_ROOT}/archive"
VENDOR_ROOT="${INSTALL_ROOT}/vendor"
VENDOR_BIN="${VENDOR_ROOT}/bin"
VENDOR_MIZFILES="${VENDOR_ROOT}/mizfiles"
VENDOR_DOC="${VENDOR_ROOT}/doc"

ensure_dir "${ARCHIVE_DIR}"
ensure_dir "${VENDOR_BIN}"
ensure_dir "${VENDOR_MIZFILES}"
ensure_dir "${VENDOR_DOC}"

wrap_vendor_binary() {
  local name="$1"
  local vendor_path="${VENDOR_BIN}/${name}"
  if [[ ! -x "${vendor_path}" ]]; then
    return 0
  fi
  cat >"${BIN_DIR}/${name}" <<EOF
#!/usr/bin/env bash
set -euo pipefail
export MIZFILES="${VENDOR_MIZFILES}"
export PATH="${VENDOR_BIN}:\${PATH}"
exec "${vendor_path}" "\$@"
EOF
  chmod +x "${BIN_DIR}/${name}"
  link_into_prefix_bin "${BIN_DIR}/${name}" "${name}"
}

if [[ -x "${VENDOR_BIN}/mizf" || -x "${VENDOR_BIN}/verifier" ]]; then
  for name in mizf verifier accom makeenv exporter miz2prel errflag addfmsg; do
    wrap_vendor_binary "${name}"
  done
  log "Mizar already installed under ${VENDOR_ROOT} and wired into ${BIN_DIR}"
  log "MIZFILES set to ${VENDOR_MIZFILES} in wrappers"
  exit 0
fi

log "Attempting to bootstrap Mizar from ${MIZAR_BASE_URL}"
tarball_path="${ITPEVAL_MIZAR_TARBALL:-${MIZAR_TARBALL:-}}"
if [[ -n "${tarball_path}" ]]; then
  if [[ ! -f "${tarball_path}" ]]; then
    fail "Mizar tarball not found: ${tarball_path}"
  fi
  tarball_name="$(basename "${tarball_path}")"
else
  tarball_url="${ITPEVAL_MIZAR_TARBALL_URL:-}"
  if [[ -n "${tarball_url}" ]]; then
    tarball_name="$(basename "${tarball_url%%\?*}")"
  else
    tarball_name="$(
      curl -fsSL "${MIZAR_BASE_URL}/" | python3 -c 'import re,sys; html=sys.stdin.read(); m=re.search(r"mizar-[^\" ]+-i386-linux\.tar", html); print(m.group(0) if m else "")' || true
    )"
    if [[ -n "${tarball_name}" ]]; then
      tarball_url="${MIZAR_BASE_URL}/${tarball_name}"
    fi
  fi
  if [[ -n "${tarball_name}" ]]; then
    tarball_path="${ARCHIVE_DIR}/${tarball_name}"
    download_cached "${tarball_url}" "" "${tarball_path}"
  fi
fi

if [[ -z "${tarball_name:-}" ]]; then
  log "Could not find an i386-linux Mizar tarball under ${MIZAR_BASE_URL}; falling back to manual wiring"
else

  tmp_dir="$(make_install_dir)"
  trap 'rm -rf "${tmp_dir}"' EXIT
  run tar -xf "${tarball_path}" -C "${tmp_dir}"

  if [[ ! -x "${tmp_dir}/install.sh" ]]; then
    fail "Mizar bundle is missing install.sh: ${tarball_path}"
  fi

  # Install into our vendor directories. Use --nodialog so we can feed answers via STDIN.
  (
    cd "${tmp_dir}"
    printf '%s\n%s\n%s\n' "${VENDOR_BIN}" "${VENDOR_MIZFILES}" "${VENDOR_DOC}" | run bash ./install.sh --nodialog
  )

  # Wire key binaries. `mizf` is the preferred driver.
  for name in mizf verifier accom makeenv exporter miz2prel errflag addfmsg; do
    wrap_vendor_binary "${name}"
  done

  if [[ -x "${BIN_DIR}/mizf" || -x "${BIN_DIR}/verifier" ]]; then
    log "Mizar installed into ${VENDOR_ROOT} and wired into ${BIN_DIR}"
    log "MIZFILES set to ${VENDOR_MIZFILES} in wrappers"
    exit 0
  fi
fi

cat >&2 <<'EOF'
[ITPEval] Mizar is best wired from an existing install or source tree.
[ITPEval] Provide one of:
[ITPEval]   - MIZAR_HOME / ITPEVAL_MIZAR_HOME
[ITPEval]   - ITPEVAL_MIZAR_SRC
[ITPEval]   - mizf / verifier on PATH
[ITPEval] And, if needed, set MIZFILES / ITPEVAL_MIZFILES to the Mizar database root
[ITPEval] (the directory that contains abstr/ and prel/ or mml/).
EOF
exit 1

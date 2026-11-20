#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
LEAN_ROOT="${PREFIX}/lean4"
PREFIX_BIN="$(itpeval_prefix_bin)"
LEAN_TOOLCHAIN="${LEAN_TOOLCHAIN:-leanprover/lean4:stable}"

mkdir -p "${LEAN_ROOT}/bin" "${PREFIX_BIN}"

if [[ -n "${ITPEVAL_LEAN4_DISTRIBUTION:-}" ]]; then
  TOOLCHAIN_ROOT="$(cd "${ITPEVAL_LEAN4_DISTRIBUTION}" && pwd -P)"
  [[ -x "${TOOLCHAIN_ROOT}/bin/lean" && -x "${TOOLCHAIN_ROOT}/bin/lake" ]] || fail "incomplete Lean distribution"
elif command -v lean >/dev/null 2>&1 && command -v lake >/dev/null 2>&1; then
  TOOLCHAIN_ROOT="$(lean --print-prefix)"
else
  ELAN_HOME="${LEAN_ROOT}/.elan"
  mkdir -p "${ELAN_HOME}"

  if [[ -x "${ELAN_HOME}/bin/elan" ]]; then
    elan_bin="${ELAN_HOME}/bin/elan"
  elif command -v elan >/dev/null 2>&1; then
    elan_bin="$(command -v elan)"
  else
    log "elan not found; installing elan into ${ELAN_HOME}"
    tmp_installer="$(mktemp)"
    trap 'rm -f "${tmp_installer}"' EXIT
    run curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "${tmp_installer}"
    run env ELAN_HOME="${ELAN_HOME}" bash "${tmp_installer}" -y --no-modify-path --default-toolchain "${LEAN_TOOLCHAIN}"
    elan_bin="${ELAN_HOME}/bin/elan"
  fi

  run env ELAN_HOME="${ELAN_HOME}" "${elan_bin}" toolchain install "${LEAN_TOOLCHAIN}"
  TOOLCHAIN_ROOT="$(ELAN_HOME="${ELAN_HOME}" "${elan_bin}" which lean | xargs dirname | xargs dirname)"
fi

cat > "${LEAN_ROOT}/bin/lean" <<EOF
#!/usr/bin/env bash
set -euo pipefail
exec "${TOOLCHAIN_ROOT}/bin/lean" "\$@"
EOF

cat > "${LEAN_ROOT}/bin/lake" <<EOF
#!/usr/bin/env bash
set -euo pipefail
exec "${TOOLCHAIN_ROOT}/bin/lake" "\$@"
EOF

chmod +x "${LEAN_ROOT}/bin/lean" "${LEAN_ROOT}/bin/lake"
ln -sf "${LEAN_ROOT}/bin/lean" "${PREFIX_BIN}/lean"
ln -sf "${LEAN_ROOT}/bin/lake" "${PREFIX_BIN}/lake"

log "Installed Lean 4 into ${LEAN_ROOT}"

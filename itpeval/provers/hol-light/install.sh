#!/usr/bin/env bash
# Install HOL Light and its OCaml dependencies.
#
# Environment variables (all optional):
#   ITPEVAL_OCAML_VERSION    OCaml version for the opam switch (default: 4.14.2)
#   ITPEVAL_CAMLP5_VERSION   camlp5 version (default: 8.03.06; HOL Light Makefile scripts may break with newer camlp5)
#   ITPEVAL_HOLLIGHT_REF     git ref to checkout (default: master)
#   ITPEVAL_OPAM_VERSION     opam binary version to download if opam is absent (default: 2.5.0)
#   ITPEVAL_HOLLIGHT_REPO    git URL for HOL Light (default: https://github.com/jrh13/hol-light)
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
HL_ROOT="${PREFIX}/hol-light"
BIN_DIR="${HL_ROOT}/bin"
PREFIX_BIN="$(itpeval_prefix_bin)"

OCAML_VERSION="${ITPEVAL_OCAML_VERSION:-4.14.2}"
CAMLP5_VERSION="${ITPEVAL_CAMLP5_VERSION:-8.03.06}"
HOLLIGHT_REF="${ITPEVAL_HOLLIGHT_REF:-master}"
HOLLIGHT_REPO="${ITPEVAL_HOLLIGHT_REPO:-https://github.com/jrh13/hol-light}"
HOLLIGHT_DIR="${HL_ROOT}/src"

ensure_dir "${BIN_DIR}"
ensure_dir "${PREFIX_BIN}"

# ---------------------------------------------------------------------------
# 1. Ensure opam is available
# ---------------------------------------------------------------------------
opam_cmd="opam"
if [[ -x "${BIN_DIR}/opam" ]]; then
  opam_cmd="${BIN_DIR}/opam"
elif ! command -v opam >/dev/null 2>&1; then
  OPAM_VERSION="${ITPEVAL_OPAM_VERSION:-2.5.0}"
  arch="$(uname -m)"
  platform="$(uname -s)"
  if [[ "${platform}" == "Darwin" ]]; then
    case "${arch}" in
      x86_64)        opam_asset="opam-${OPAM_VERSION}-x86_64-macos" ;;
      arm64|aarch64) opam_asset="opam-${OPAM_VERSION}-arm64-macos"  ;;
      *) fail "unsupported macOS architecture: ${arch}" ;;
    esac
  else
    case "${arch}" in
      x86_64)        opam_asset="opam-${OPAM_VERSION}-x86_64-linux"  ;;
      aarch64|arm64) opam_asset="opam-${OPAM_VERSION}-arm64-linux"   ;;
      *) fail "unsupported Linux architecture: ${arch}" ;;
    esac
  fi
  url="https://github.com/ocaml/opam/releases/download/${OPAM_VERSION}/${opam_asset}"
  log "opam not found; downloading ${url}"
  download_cached "${url}" "" "${BIN_DIR}/opam"
  run chmod +x "${BIN_DIR}/opam"
  opam_cmd="${BIN_DIR}/opam"
fi

# ---------------------------------------------------------------------------
# 2. Initialise opam root and create switch
# ---------------------------------------------------------------------------
OPAMROOT="${HL_ROOT}/opamroot"
export OPAMROOT

if [[ ! -f "${OPAMROOT}/config" ]]; then
  run "${opam_cmd}" init --bare --no-setup --disable-sandboxing -y default "${ITPEVAL_OPAM_REPO_URL:-https://opam.ocaml.org}"
fi

SWITCH_NAME="hol-light"
if ! "${opam_cmd}" switch list --short 2>/dev/null | grep -qxF "${SWITCH_NAME}"; then
  run "${opam_cmd}" switch create "${SWITCH_NAME}" "ocaml-base-compiler.${OCAML_VERSION}" -y --no-install
fi

eval "$("${opam_cmd}" env --switch="${SWITCH_NAME}" --set-switch)"

# ---------------------------------------------------------------------------
# 3. Install OCaml packages required by HOL Light
# ---------------------------------------------------------------------------
log "Installing OCaml deps for HOL Light (OCaml ${OCAML_VERSION}, camlp5 ${CAMLP5_VERSION})"
packages=("camlp5.${CAMLP5_VERSION}" zarith)
if [[ -n "${ITPEVAL_OPAM_PACKAGES:-}" ]]; then
  read -r -a packages <<< "${ITPEVAL_OPAM_PACKAGES}"
fi
if ! "${opam_cmd}" install -y --switch="${SWITCH_NAME}" "${packages[@]}"; then
  log "Available camlp5 versions:"
  "${opam_cmd}" show --switch="${SWITCH_NAME}" camlp5 --all-versions || true
  fail "Failed to install camlp5.${CAMLP5_VERSION}; override with ITPEVAL_CAMLP5_VERSION"
fi

# ---------------------------------------------------------------------------
# 4. Clone / update HOL Light source
# ---------------------------------------------------------------------------
if [[ ! -d "${HOLLIGHT_DIR}/.git" ]]; then
  run git clone --depth 1 --branch "${HOLLIGHT_REF}" "${HOLLIGHT_REPO}" "${HOLLIGHT_DIR}" \
    || run git clone --depth 1 "${HOLLIGHT_REPO}" "${HOLLIGHT_DIR}"
else
  log "HOL Light source already present at ${HOLLIGHT_DIR}; skipping clone"
fi

# ---------------------------------------------------------------------------
# 5. Build HOL Light (runs make to preprocess via camlp5)
# ---------------------------------------------------------------------------
(cd "${HOLLIGHT_DIR}" && run make)

# ---------------------------------------------------------------------------
# 6. Write wrapper scripts
# ---------------------------------------------------------------------------

# hollight-run: start HOL Light and execute a given .ml file non-interactively.
#
# IMPORTANT: do not invoke `ocaml hol.ml` directly here; HOL Light relies on its
# `ocaml-hol` wrapper (built by `make`) to preload required runtime libraries.
cat > "${BIN_DIR}/hollight-run" <<EOF
#!/usr/bin/env bash
# Usage: hollight-run <proof.ml>
set -euo pipefail
PROOF_FILE="\${1:?usage: hollight-run <proof.ml>}"
PROOF_FILE="\$(cd "\$(dirname "\${PROOF_FILE}")" && pwd)/\$(basename "\${PROOF_FILE}")"
HOLLIGHT_DIR="${HOLLIGHT_DIR}"
export HOLLIGHT_DIR
cd "\${HOLLIGHT_DIR}"
# Escape for embedding in an OCaml string literal.
PROOF_FILE_OCAML="\${PROOF_FILE//\\\\/\\\\\\\\}"
PROOF_FILE_OCAML="\${PROOF_FILE_OCAML//\\\"/\\\\\\\"}"

# We can't pass the proof file as a command-line argument, because the OCaml
# toplevel parses those files with the *standard* OCaml parser, which does not
# understand HOL Light quotation syntax. Instead we load it via Toploop after
# hol.ml has installed the HOL Light syntax extension.
{
  printf 'use_file_raise_failure := true;;\\n'; \
  printf 'let ok = Toploop.use_file Format.std_formatter \"%s\";;\\n' "\${PROOF_FILE_OCAML}"; \
  printf 'if not ok then exit 1;;\\n'; \
  printf '#quit;;\\n'; \
} | exec env OPAMROOT="${OPAMROOT}" \\
    "${opam_cmd}" exec --switch="${SWITCH_NAME}" -- \\
    "\${HOLLIGHT_DIR}/ocaml-hol" -I "\${HOLLIGHT_DIR}" -init "\${HOLLIGHT_DIR}/hol.ml"
EOF
chmod +x "${BIN_DIR}/hollight-run"
ln -sf "${BIN_DIR}/hollight-run" "${PREFIX_BIN}/hollight-run"

# hollight-version: print OCaml version and HOL Light git hash
cat > "${BIN_DIR}/hollight-version" <<EOF
#!/usr/bin/env bash
set -euo pipefail
HOLLIGHT_DIR="${HOLLIGHT_DIR}"
cd "\${HOLLIGHT_DIR}" || true
echo -n "HOL Light "
if [[ -f "\${HOLLIGHT_DIR}/VERSION" ]]; then
  cat "\${HOLLIGHT_DIR}/VERSION"
elif git -C "\${HOLLIGHT_DIR}" rev-parse --short HEAD >/dev/null 2>&1; then
  git -C "\${HOLLIGHT_DIR}" rev-parse --short HEAD
else
  echo "(unknown)"
fi
env OPAMROOT="${OPAMROOT}" \\
  "${opam_cmd}" exec --switch="${SWITCH_NAME}" -- \\
  ocaml --version
EOF
chmod +x "${BIN_DIR}/hollight-version"
ln -sf "${BIN_DIR}/hollight-version" "${PREFIX_BIN}/hollight-version"

log "HOL Light installed at ${HL_ROOT}"
log "  source:  ${HOLLIGHT_DIR}"
log "  wrapper: ${BIN_DIR}/hollight-run"

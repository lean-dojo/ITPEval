#!/usr/bin/env bash
set -euo pipefail

itpeval_repo_root() {
  (cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
}

itpeval_root() {
  (cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
}

itpeval_prefix() {
  if [[ -n "${ITPEVAL_PREFIX:-}" ]]; then
    echo "${ITPEVAL_PREFIX}"
  else
    # On EFS, toolchains with many small files (opam/cabal) can be extremely slow.
    # Default to local ephemeral storage unless the user explicitly sets ITPEVAL_PREFIX.
    local root
    root="$(itpeval_root)"
    if [[ "${root}" == /efs/* ]]; then
      echo "/tmp/itpeval-toolchains"
    else
      local installed="${XDG_DATA_HOME:-${HOME}/.local/share}/itpeval/toolchains"
      if [[ -d "${installed}/current" ]]; then
        (cd "${installed}/current" && pwd -P)
      elif [[ -f "${root}/../pyproject.toml" ]]; then
        echo "${root}/_toolchains"
      else
        echo "${installed}"
      fi
    fi
  fi
}

itpeval_prefix_bin() {
  echo "$(itpeval_prefix)/bin"
}

itpeval_realpath() {
  # BSD/macOS realpath lacks GNU's -e flag. Python is already required by
  # the harness; strict resolution preserves the missing-file check.
  python3 -c 'import sys; from pathlib import Path; print(Path(sys.argv[1]).resolve(strict=True))' "$1"
}

itpeval_validate_statement_file() {
  local prover="$1"
  local file_path="$2"
  local repo_root

  if [[ ! -f "${file_path}" ]]; then
    fail "missing statement source at ${file_path}"
  fi
  [[ "${ITPEVAL_OPERATION:-legacy}" == legacy ]] || return 0
  if ! grep -Fq -- "Statement-only formalization of" "${file_path}" \
    && ! grep -Fqi -- ":itpeval-statement-checked" "${file_path}"; then
    return 0
  fi

  repo_root="$(itpeval_repo_root)"
  PYTHONPATH="${repo_root}${PYTHONPATH:+:${PYTHONPATH}}" \
    "${ITPEVAL_PYTHON:-python3}" -m eval.pipeline.translation.validation \
      --prover "${prover}" \
      --file "${file_path}"
}

itpeval_manifest_path() {
  echo "$(itpeval_root)/manifest.json"
}

itpeval_download_cache_dir() {
  if [[ -n "${ITPEVAL_DOWNLOAD_CACHE:-}" ]]; then
    echo "${ITPEVAL_DOWNLOAD_CACHE}"
  else
    if [[ -f "$(itpeval_root)/../pyproject.toml" ]]; then
      echo "$(itpeval_root)/.downloads"
    else
      echo "${XDG_CACHE_HOME:-${HOME}/.cache}/itpeval/downloads"
    fi
  fi
}

itpeval_hash_text() {
  local text="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    printf '%s' "${text}" | sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    printf '%s' "${text}" | shasum -a 256 | awk '{print $1}'
  else
    fail "neither sha256sum nor shasum is available"
  fi
}

itpeval_sha256_file() {
  local file_path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${file_path}" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${file_path}" | awk '{print $1}'
  else
    fail "neither sha256sum nor shasum is available"
  fi
}

itpeval_download_cache_key() {
  local url="$1"
  local expected_sha="${2:-}"
  local sanitized_name
  sanitized_name="$(basename "${url%%\?*}")"
  sanitized_name="${sanitized_name%%#*}"
  if [[ -z "${sanitized_name}" || "${sanitized_name}" == "." || "${sanitized_name}" == "/" ]]; then
    sanitized_name="download"
  fi
  echo "$(itpeval_hash_text "${url}|${expected_sha}")-${sanitized_name}"
}

itpeval_download_cache_path() {
  local url="$1"
  local expected_sha="${2:-}"
  echo "$(itpeval_download_cache_dir)/$(itpeval_download_cache_key "${url}" "${expected_sha}")"
}

itpeval_manifest_get() {
  local resource_id="$1"
  local field="$2"
  local manifest_path
  manifest_path="$(itpeval_manifest_path)"

  if [[ ! -f "${manifest_path}" ]]; then
    return 1
  fi
  if ! command -v python3 >/dev/null 2>&1; then
    return 1
  fi

  python3 - "${manifest_path}" "${resource_id}" "${field}" <<'PY'
import json
import sys

manifest_path, resource_id, field = sys.argv[1], sys.argv[2], sys.argv[3]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
for resource in manifest.get("resources", []):
    if resource.get("id") == resource_id:
        value = resource.get(field, "")
        if isinstance(value, (dict, list)):
            print(json.dumps(value))
        else:
            print(value)
        raise SystemExit(0)
raise SystemExit(1)
PY
}

ensure_dir() {
  mkdir -p "$1"
}

verify_sha256() {
  local file_path="$1"
  local expected_sha="$2"
  local actual_sha
  actual_sha="$(itpeval_sha256_file "${file_path}")"
  if [[ "${actual_sha}" != "${expected_sha}" ]]; then
    fail "sha256 mismatch for ${file_path}: expected ${expected_sha}, got ${actual_sha}"
  fi
}

download_cached() {
  local url="$1"
  local expected_sha="${2:-}"
  local destination="${3:-}"
  local cache_dir
  local cache_path
  local temp_path

  cache_dir="$(itpeval_download_cache_dir)"
  ensure_dir "${cache_dir}"
  cache_path="$(itpeval_download_cache_path "${url}" "${expected_sha}")"

  if [[ ! -f "${cache_path}" ]]; then
    temp_path="$(mktemp "${cache_dir}/.download.XXXXXX")"
    run curl -fsSL "${url}" -o "${temp_path}"
    if [[ -n "${expected_sha}" ]]; then
      verify_sha256 "${temp_path}" "${expected_sha}"
    fi
    mv "${temp_path}" "${cache_path}"
  elif [[ -n "${expected_sha}" ]]; then
    verify_sha256 "${cache_path}" "${expected_sha}"
  fi

  if [[ -n "${destination}" ]]; then
    ensure_dir "$(dirname "${destination}")"
    cp -f "${cache_path}" "${destination}"
    echo "${destination}"
  else
    echo "${cache_path}"
  fi
}

link_into_prefix_bin() {
  local target="$1"
  local name="$2"
  local bin_dir
  bin_dir="$(itpeval_prefix_bin)"
  ensure_dir "${bin_dir}"
  ln -sf "${target}" "${bin_dir}/${name}"
}

log() {
  printf '[ITPEval] %s\n' "$*" 1>&2
}

fail() {
  printf '[ITPEval] ERROR: %s\n' "$*" 1>&2
  return 1
}

run() {
  log "+ $*"
  "$@"
}

#!/usr/bin/env bash
set -euo pipefail

PINNED_SOLC_VERSION="${PINNED_SOLC_VERSION:-0.8.30+commit.73712a01}"
INSTALL_DIR="${1:-${SOLC_INSTALL_DIR:-$PWD/.solc}}"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    platform="linux-amd64"
    binary="solc-linux-amd64-v${PINNED_SOLC_VERSION}"
    ;;
  Darwin-x86_64)
    platform="macosx-amd64"
    binary="solc-macosx-amd64-v${PINNED_SOLC_VERSION}"
    ;;
  Darwin-arm64)
    platform="macosx-amd64"
    binary="solc-macosx-amd64-v${PINNED_SOLC_VERSION}"
    ;;
  *)
    echo "unsupported platform for pinned solc install: $(uname -s)-$(uname -m)" >&2
    exit 1
    ;;
esac

mkdir -p "$INSTALL_DIR"
solc_path="$INSTALL_DIR/solc"

# Content hash, not version string. `--version` output is trivially forged by a
# substituted binary, and this project's entire reproducibility claim rests on
# the compiler being exactly this one. Per-platform hashes are published in
# https://binaries.soliditylang.org/${platform}/list.json -- fill these in and
# record them in the artifact manifest alongside the flag set.
declare -A PINNED_SOLC_SHA256=(
  ["linux-amd64"]="TODO-fill-from-list.json"
  ["macosx-amd64"]="TODO-fill-from-list.json"
)

if [[ ! -x "$solc_path" ]] || ! "$solc_path" --version | grep -q "Version: ${PINNED_SOLC_VERSION}"; then
  url="https://binaries.soliditylang.org/${platform}/${binary}"
  echo "[install-solc] downloading $url"
  curl -fsSL "$url" -o "$solc_path"
  expected="${PINNED_SOLC_SHA256[$platform]:-}"
  if [[ -z "$expected" || "$expected" == TODO-* ]]; then
    echo "[install-solc] no pinned SHA-256 recorded for platform '$platform'." >&2
    echo "[install-solc] Fetch it from https://binaries.soliditylang.org/${platform}/list.json" >&2
    echo "[install-solc] and set PINNED_SOLC_SHA256 in this script." >&2
    rm -f "$solc_path"
    exit 1
  fi
  actual="$(shasum -a 256 "$solc_path" 2>/dev/null | cut -d' ' -f1 || sha256sum "$solc_path" | cut -d' ' -f1)"
  if [[ "$actual" != "$expected" ]]; then
    echo "[install-solc] SHA-256 mismatch for $url" >&2
    echo "[install-solc]   expected $expected" >&2
    echo "[install-solc]   actual   $actual" >&2
    rm -f "$solc_path"
    exit 1
  fi
  chmod +x "$solc_path"
fi

"$solc_path" --version
echo "$solc_path"

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
    # Upstream publishes no macosx-arm64 binary for this solc version; Apple
    # Silicon deliberately runs the x86_64 binary under Rosetta 2. Same
    # binary, same hash, same emitted bytecode.
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
# the compiler being exactly this one. These are the official sha256 values
# from https://binaries.soliditylang.org/<platform>/list.json for
# v0.8.30+commit.73712a01 (recorded 2026-08-12); they are also recorded in
# docs/reference/REPRODUCIBLE_BUILDS.md and the review-packet manifest.
# (A plain case statement, not `declare -A`: stock macOS bash is 3.2, which
# has no associative arrays.)
case "$platform" in
  linux-amd64)  pinned_solc_sha256="f3e987dc6ecebd4bd350c48edcbc320b46cf9e3109bd3fc3d88f1acaf4c428f7" ;;
  macosx-amd64) pinned_solc_sha256="738dcdc6afddeb505ee4e4ef24f1c1fdba2b8c924e614cbbf5801a5b062dd683" ;;
  *)            pinned_solc_sha256="" ;;
esac

if [[ ! -x "$solc_path" ]] || ! "$solc_path" --version | grep -q "Version: ${PINNED_SOLC_VERSION}"; then
  url="https://binaries.soliditylang.org/${platform}/${binary}"
  echo "[install-solc] downloading $url"
  curl -fsSL "$url" -o "$solc_path"
  expected="$pinned_solc_sha256"
  if [[ -z "$expected" || "$expected" == TODO-* ]]; then
    echo "[install-solc] no pinned SHA-256 recorded for platform '$platform'." >&2
    echo "[install-solc] Fetch it from https://binaries.soliditylang.org/${platform}/list.json" >&2
    echo "[install-solc] and set pinned_solc_sha256 in this script." >&2
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

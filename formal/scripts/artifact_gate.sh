#!/usr/bin/env bash
# B5 artifact gate (D-B5): the Rust reference render against the tracked F1 dump.
#
# Pins, in order:
#   1. Halo2VerifyingKey.sol byte-for-byte and by sha256;
#   2. Halo2Verifier.sol byte count, line count, and exactly ONE differing line,
#      whose two sides both contain BUILD_ID (the build-stamp INPUT, not a proof line);
#   3. prints features, srs_fingerprint, srs_sha256 and both BUILD_ID values.
#
# It is deliberately NOT part of scripts/checks.sh: DG.7 says the formal CI job
# needs no Rust toolchain. Run it where cargo and the SRS assets are available:
#
#   bash formal/scripts/artifact_gate.sh
#
# The SRS assets come from the repo's own fetch script:
#   (cd proofs/solidity-verifier && bash scripts/ensure_srs_assets.sh)
set -euo pipefail

FORMAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="$(cd "$FORMAL/.." && pwd)"
SRS_DIR="${SRS_DIR:-$REPO/proofs/solidity-verifier/.srs}"

if [[ ! -s "$SRS_DIR/bls_filecoin_2p19" ]]; then
  echo "artifact_gate: missing $SRS_DIR/bls_filecoin_2p19" >&2
  echo "artifact_gate: run (cd proofs/solidity-verifier && bash scripts/ensure_srs_assets.sh)" >&2
  exit 1
fi

# rustup toolchains are not on PATH in a clean shell on this host.
if ! command -v cargo >/dev/null 2>&1; then
  for d in "$HOME"/.rustup/toolchains/*/bin; do
    if [[ -x "$d/cargo" ]]; then
      export PATH="$d:$HOME/.cargo/bin:$PATH"
      break
    fi
  done
fi
command -v cargo >/dev/null 2>&1 || {
  echo "artifact_gate: cargo not found (install rustup or add a toolchain to PATH)" >&2
  exit 1
}

cd "$REPO/proofs/solidity-verifier"
SRS_DIR="$SRS_DIR" MIDFALL_ARTIFACT_GATE=1 \
  cargo test --features truncated-challenges --test artifact_export -- --nocapture

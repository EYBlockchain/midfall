#!/usr/bin/env bash
# Emit the REVIEW_PACKET.md section-4 artifact-manifest table for one rendered
# fixture dump (a directory under target/, e.g. target/poseidon-fixture-dump).
#
# Hashes generated sources and fixture binaries with SHA-256, and — when the
# pinned solc is available — compiles each contract with the recorded flag set
# to report the runtime bytecode length and keccak256. The point of the script
# is that manifest rows are produced by a maintained tool instead of being
# hand-filled (M-5 / I-3, docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md).
#
# Usage:
#   scripts/generate_artifact_manifest.sh <dump-dir> [--runs <N>]
#
# Environment:
#   SOLC              path to solc (default: resolved like the test harness:
#                     $SOLC, then .solc/solc, then solc on PATH)
#   SOLC_OPTIMIZE_RUNS  overrides --runs / the default of 200
set -euo pipefail

dump_dir="${1:?usage: $0 <dump-dir> [--runs <N>]}"
shift || true
runs="${SOLC_OPTIMIZE_RUNS:-200}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --runs) runs="${2:?--runs needs a value}"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 1 ;;
  esac
done

[[ -d "$dump_dir" ]] || { echo "not a directory: $dump_dir" >&2; exit 1; }

sha256() {
  shasum -a 256 "$1" 2>/dev/null | cut -d' ' -f1 || sha256sum "$1" | cut -d' ' -f1
}

solc_bin="${SOLC:-}"
if [[ -z "$solc_bin" ]]; then
  if [[ -x ".solc/solc" ]]; then solc_bin=".solc/solc"; else solc_bin="$(command -v solc || true)"; fi
fi

# Compile one contract with the recorded flag set and print
# "<runtime-bytes> <runtime-keccak256>" for its largest emitted runtime
# (the file's main contract). Requires solc and python3.
runtime_info() {
  local src="$1"
  [[ -n "$solc_bin" ]] || { echo "n/a (no solc)"; return; }
  local hex
  hex="$("$solc_bin" --bin-runtime --optimize --optimize-runs "$runs" --via-ir \
        --evm-version cancun --no-cbor-metadata "$src" 2>/dev/null \
        | awk '/^[0-9a-f]+$/ { if (length($0) > length(best)) best = $0 } END { print best }')"
  [[ -n "$hex" ]] || { echo "n/a (compile failed)"; return; }
  python3 - "$hex" <<'PY'
import sys

data = bytes.fromhex(sys.argv[1])
# keccak256 (pre-NIST padding), matching EVM EXTCODEHASH and the recorded
# runtime hashes in REPRODUCIBLE_BUILDS.md. CPython's hashlib sha3_256 is
# NIST SHA-3, NOT keccak, so require pycryptodome and say so if missing.
try:
    from Crypto.Hash import keccak
except ImportError:
    sys.stdout.write(f"{len(data)} bytes, keccak256 unavailable (pip install pycryptodome)")
    sys.exit(0)
digest = keccak.new(digest_bits=256, data=data).hexdigest()
sys.stdout.write(f"{len(data)} bytes, 0x{digest}")
PY
}

row() { printf '| %s | %s |\n' "$1" "$2"; }

commit="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
dirty="clean"
[[ -n "$(git status --porcelain 2>/dev/null)" ]] && dirty="dirty"

echo "### Artifact manifest: $dump_dir"
echo
echo "| Item | Value |"
echo "| --- | --- |"
row "Repository commit" "\`$commit\` (this repository; working tree $dirty)"
row "Rust toolchain" "\`rust-toolchain.toml\`"
row "Solidity compiler" "\`$("$solc_bin" --version 2>/dev/null | grep -o 'Version: .*' || echo 'n/a')\`"
row "Solidity flags" "\`--bin --optimize --optimize-runs $runs --via-ir --evm-version cancun --no-cbor-metadata\`"
row "Cargo features" "fill from the render invocation (not recoverable from the dump)"

for name in Halo2Verifier Halo2VerifyingKey Halo2QuotientEvaluator; do
  src="$dump_dir/$name.sol"
  if [[ -f "$src" ]]; then
    row "Generated $name source hash" "\`$(sha256 "$src")\`"
    if [[ "$name" == "Halo2VerifyingKey" ]]; then
      # The VK's deployed runtime (INVALID || payload) is constructed by its
      # constructor, so the static --bin-runtime output is a stub and hashing
      # it would be misleading. The authoritative pin is the generated
      # EXPECTED_VK_CODEHASH constant checked on-chain.
      row "$name runtime length/hash" "deploy-time constructed; pinned by EXPECTED_VK_LENGTH / EXPECTED_VK_CODEHASH in the verifier"
    else
      row "$name runtime length/hash" "$(runtime_info "$src")"
    fi
  else
    row "Generated $name source hash" "not rendered (single-contract or embedded profile)"
  fi
done

for f in proof.bin calldata.bin instances.be instance.le; do
  if [[ -f "$dump_dir/$f" ]]; then
    row "Fixture \`$f\` hash" "\`$(sha256 "$dump_dir/$f")\`"
  fi
done

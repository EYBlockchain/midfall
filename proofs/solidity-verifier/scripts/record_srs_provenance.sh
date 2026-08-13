#!/usr/bin/env bash
# Record the SRS assets a verifier build trusts (H-1,
# docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md).
#
# NEG_S_G2_BASE — the element every soundness guarantee of the deployed
# verifier rests on — is derived from the SRS at build time. Build-time code
# (src/lowering/vk.rs) now proves the SRS is internally consistent (s_g2
# matches the tau underlying g_lagrange), but internal consistency cannot
# prove WHICH ceremony the asset came from. That link is this record: the
# SHA-256 of the exact asset bytes, checked against the table below and
# recorded in docs/reference/REPRODUCIBLE_BUILDS.md next to the ceremony
# reference.
#
# Usage:
#   scripts/record_srs_provenance.sh [srs-dir]
#
# srs-dir defaults to $SRS_DIR, then ./.srs, then
# ../../zk_stdlib/examples/assets relative to this script.
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
default_assets="$script_dir/../../../zk_stdlib/examples/assets"

srs_dir="${1:-${SRS_DIR:-}}"
if [[ -z "$srs_dir" ]]; then
  if [[ -d "./.srs" ]]; then srs_dir="./.srs"; else srs_dir="$default_assets"; fi
fi
[[ -d "$srs_dir" ]] || { echo "SRS directory not found: $srs_dir" >&2; exit 1; }

sha256() {
  shasum -a 256 "$1" 2>/dev/null | cut -d' ' -f1 || sha256sum "$1" | cut -d' ' -f1
}

echo "### SRS provenance ($(date -u +%Y-%m-%dT%H:%M:%SZ), dir: $srs_dir)"
echo
echo "| Asset | Bytes | SHA-256 |"
echo "| --- | ---: | --- |"

found=0
for asset in midnight-srs-2p19 midnight-srs-2p20 midnight-srs-2p22 \
             bls_filecoin_2p19 bls_filecoin_2p13 bls_filecoin_2p12 bls_filecoin_2p6; do
  path="$srs_dir/$asset"
  [[ -f "$path" ]] || continue
  found=1
  size="$(wc -c < "$path" | tr -d ' ')"
  echo "| \`$asset\` | $size | \`$(sha256 "$path")\` |"
done

if [[ "$found" == 0 ]]; then
  echo >&2
  echo "no known SRS assets found in $srs_dir" >&2
  echo "download Midnight assets with: scripts/run_ivc_bench.sh (or curl from https://srs.midnight.network/)" >&2
  exit 1
fi

cat <<'EOF'

Record these rows in docs/reference/REPRODUCIBLE_BUILDS.md ("SRS Provenance")
and compare against the hashes already recorded there before any deployment
build. The tau-binding of each asset's s_g2 (the NEG_S_G2_BASE source) is
checked by the gated test:

    HALO2_SOLIDITY_RUN_EVM_TESTS=1 cargo test --release --features evm \
        midnight_srs_assets_bind_s_g2_to_lagrange_tau
EOF

#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

CHECK_ONLY=0
GAS_CHECKPOINTS=1
RUN_NATIVE_MIDFALL=0
RUN_SOLIDITY_BENCH=1
SKIP_SRS_DOWNLOAD=0
RUN_TRACE=0
IN_CIRCUIT_FEWER_POINT_SETS=1
OUTER_SINGLE_H_COMMITMENT=0
ALLOW_UNPINNED_SOLC="${HALO2_SOLIDITY_ALLOW_UNPINNED_SOLC:-0}"
RUST_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-}"

SRS_DIR="${SRS_DIR:-"$ROOT_DIR/../../zk_stdlib/examples/assets"}"
MIDFALL_DIR="${MIDFALL_DIR:-"$ROOT_DIR/../.."}"
IVC_LEAF_BUNDLE="${IVC_LEAF_BUNDLE:-"$ROOT_DIR/target/ivc-keccak-solidity-dump/ivc-leaf-bundle.bin"}"

FILECOIN_SRS_URL="https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19"
MIDNIGHT_SRS_2P19_URL="https://srs.midnight.network/midnight-srs-2p19"
MIDNIGHT_SRS_2P20_URL="https://srs.midnight.network/midnight-srs-2p20"
MIDNIGHT_SRS_2P22_URL="https://srs.midnight.network/midnight-srs-2p22"
PINNED_SOLC_VERSION="0.8.30+commit.73712a01"

usage() {
  cat <<'USAGE'
Run the IVC Keccak Solidity verifier bench over Poseidon hash-chain leaves.

Usage:
  scripts/run_ivc_bench.sh [options]

Options:
  --check-only          Download/check SRS assets and compile the ignored tests
                        without running the slow proving/verifier bench.
  --skip-srs-download  Fail if a required SRS asset is missing.
  --srs-dir DIR        Directory for SRS assets. Defaults to $SRS_DIR or
                       ../../zk_stdlib/examples/assets.
  --no-gas-checkpoints Run the Solidity verifier bench without section logs.
  --outer-single-h-commitment
                       Enable the single-H quotient commitment layout
                       for the final Solidity-facing decider proof.
  --leaf-bundle PATH   Path for the generated/reused multi-limb IVC leaf
                       bundle. Defaults to target/ivc-keccak-solidity-dump/
                       ivc-leaf-bundle.bin.
  --trace              Enable native Rust/Solidity trace equivalence.
                       Requires midnight-proofs/solidity-verifier-trace.
  --allow-unpinned-solc
                       Use the configured solc even if it does not match the
                       pinned reproducible compiler. Gas/bytecode are ad hoc.
  --rust-toolchain NAME
                       Export RUSTUP_TOOLCHAIN=NAME for cargo commands
                       (for example, stable) instead of rustup's default
                       rust-toolchain.toml selection.
  --native-midfall     Also run Midfall's native Poseidon-chain final IVC test from
                        $MIDFALL_DIR/aggregation.
  --native-only        Run only the Midfall native Poseidon-chain final IVC test.
  --midfall-dir DIR    Local Midfall checkout for --native-midfall.
                       Defaults to this repository root.
  -h, --help           Show this help.

Default behavior:
  1. Ensure SRS_DIR has Midnight's midnight-srs-2p19 and midnight-srs-2p20.
     The optional outer single-H path also needs midnight-srs-2p22.
     The optional --native-midfall path also needs a Filecoin SRS.
  2. Compile the gated Solidity verifier bench.
  3. If --outer-single-h-commitment is set, generate the multi-limb IVC leaf
     bundle without outer-single-h-commitment, then run the final decider
     Solidity bench with outer-single-h-commitment.

Examples:
  scripts/run_ivc_bench.sh --check-only
  scripts/run_ivc_bench.sh
  scripts/run_ivc_bench.sh --trace --no-gas-checkpoints
  scripts/run_ivc_bench.sh --allow-unpinned-solc --rust-toolchain stable
  SRS_DIR=/path/to/srs scripts/run_ivc_bench.sh --native-midfall
USAGE
}

die() {
  echo "[ivc-bench] error: $*" >&2
  exit 1
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found on PATH: $1"
}

env_flag_enabled() {
  case "${1:-}" in
    1|true|TRUE|yes|YES|on|ON) return 0 ;;
    *) return 1 ;;
  esac
}

require_pinned_solc() {
  local solc_bin="${SOLC:-solc}"
  command -v "$solc_bin" >/dev/null 2>&1 || die "required command not found: $solc_bin"
  local actual
  actual="$("$solc_bin" --version | awk '/^Version: / { print $2; exit }')"
  if env_flag_enabled "$ALLOW_UNPINNED_SOLC"; then
    echo "[ivc-bench] warning: using unpinned solc $actual; gas/bytecode are not reproducible against pinned $PINNED_SOLC_VERSION"
    return
  fi
  [[ "$actual" == "$PINNED_SOLC_VERSION"* ]] || die "solc version $actual does not match pinned $PINNED_SOLC_VERSION"
}

abs_path() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s\n' "$PWD/${1#./}" ;;
  esac
}

while (($#)); do
  case "$1" in
    --check-only)
      CHECK_ONLY=1
      ;;
    --skip-srs-download)
      SKIP_SRS_DOWNLOAD=1
      ;;
    --srs-dir)
      [[ $# -ge 2 ]] || die "--srs-dir requires a value"
      SRS_DIR="$2"
      shift
      ;;
    --no-gas-checkpoints)
      GAS_CHECKPOINTS=0
      ;;
    --outer-single-h-commitment)
      OUTER_SINGLE_H_COMMITMENT=1
      ;;
    --leaf-bundle)
      [[ $# -ge 2 ]] || die "--leaf-bundle requires a value"
      IVC_LEAF_BUNDLE="$2"
      shift
      ;;
    --trace)
      RUN_TRACE=1
      ;;
    --allow-unpinned-solc)
      ALLOW_UNPINNED_SOLC=1
      ;;
    --rust-toolchain)
      [[ $# -ge 2 ]] || die "--rust-toolchain requires a value"
      RUST_TOOLCHAIN="$2"
      shift
      ;;
    --native-midfall)
      RUN_NATIVE_MIDFALL=1
      ;;
    --native-only)
      RUN_NATIVE_MIDFALL=1
      RUN_SOLIDITY_BENCH=0
      ;;
    --midfall-dir)
      [[ $# -ge 2 ]] || die "--midfall-dir requires a value"
      MIDFALL_DIR="$2"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
  shift
done

SRS_DIR="$(abs_path "$SRS_DIR")"
MIDFALL_DIR="$(abs_path "$MIDFALL_DIR")"
IVC_LEAF_BUNDLE="$(abs_path "$IVC_LEAF_BUNDLE")"

if env_flag_enabled "$ALLOW_UNPINNED_SOLC"; then
  export HALO2_SOLIDITY_ALLOW_UNPINNED_SOLC=1
fi
if [[ -n "$RUST_TOOLCHAIN" ]]; then
  export RUSTUP_TOOLCHAIN="$RUST_TOOLCHAIN"
fi

download_if_missing() {
  local path="$1"
  local url="$2"

  if [[ -s "$path" ]]; then
    echo "[ivc-bench] using $(basename "$path")"
    return
  fi

  [[ "$SKIP_SRS_DOWNLOAD" -eq 0 ]] || die "missing SRS asset: $path"
  require_cmd curl

  mkdir -p "$(dirname "$path")"
  local tmp="$path.partial"
  echo "[ivc-bench] downloading $(basename "$path")"
  echo "[ivc-bench]   from $url"
  curl -fL --retry 3 --retry-delay 2 -o "$tmp" "$url"
  mv "$tmp" "$path"
}

ensure_srs_assets() {
  mkdir -p "$SRS_DIR"

  download_if_missing "$SRS_DIR/midnight-srs-2p19" "$MIDNIGHT_SRS_2P19_URL"
  download_if_missing "$SRS_DIR/midnight-srs-2p20" "$MIDNIGHT_SRS_2P20_URL"
  if [[ "$OUTER_SINGLE_H_COMMITMENT" -eq 1 ]]; then
    download_if_missing "$SRS_DIR/midnight-srs-2p22" "$MIDNIGHT_SRS_2P22_URL"
  fi
}

ensure_filecoin_srs_asset() {
  if [[ -s "$SRS_DIR/bls_filecoin_2p13" ]]; then
    echo "[ivc-bench] using bls_filecoin_2p13"
  elif [[ -s "$SRS_DIR/bls_filecoin_2p19" ]]; then
    echo "[ivc-bench] using bls_filecoin_2p19; Midfall will downsize to bls_filecoin_2p13 if needed"
  else
    download_if_missing "$SRS_DIR/bls_filecoin_2p19" "$FILECOIN_SRS_URL"
  fi
}

cargo_features() {
  local include_outer_single_h="${1:-$OUTER_SINGLE_H_COMMITMENT}"
  local features="evm,truncated-challenges"
  if [[ "$IN_CIRCUIT_FEWER_POINT_SETS" -eq 1 ]]; then
    features="$features,in-circuit-fewer-point-sets"
  fi
  if [[ "$include_outer_single_h" -eq 1 ]]; then
    features="$features,outer-single-h-commitment"
  fi
  if [[ "$GAS_CHECKPOINTS" -eq 1 ]]; then
    features="$features,solidity-gas-checkpoints"
  fi
  if [[ "$RUN_TRACE" -eq 1 ]]; then
    features="$features,solidity-trace"
  fi
  if [[ "$RUN_TRACE" -eq 1 ]]; then
    features="$features,rust-verifier-trace"
  fi
  printf '%s\n' "$features"
}

run_native_midfall() {
  [[ -f "$MIDFALL_DIR/aggregation/Cargo.toml" ]] || die "Midfall aggregation Cargo.toml not found under $MIDFALL_DIR"
  ensure_filecoin_srs_asset

  echo "[ivc-bench] compiling Midfall native Poseidon-chain final IVC test"
  echo "+ SRS_DIR=$SRS_DIR cargo test --release --manifest-path $MIDFALL_DIR/aggregation/Cargo.toml --test ivc_keccak_final --features keccak-transcript,truncated-challenges,fewer-point-sets --no-run"
  SRS_DIR="$SRS_DIR" cargo test --release \
    --manifest-path "$MIDFALL_DIR/aggregation/Cargo.toml" \
    --test ivc_keccak_final \
    --features keccak-transcript,truncated-challenges,fewer-point-sets \
    --no-run

  if [[ "$CHECK_ONLY" -eq 0 ]]; then
    echo "[ivc-bench] running Midfall native Poseidon-chain final IVC test"
    echo "+ SRS_DIR=$SRS_DIR cargo test --release --manifest-path $MIDFALL_DIR/aggregation/Cargo.toml --test ivc_keccak_final --features keccak-transcript,truncated-challenges,fewer-point-sets -- --ignored --nocapture"
    SRS_DIR="$SRS_DIR" cargo test --release \
      --manifest-path "$MIDFALL_DIR/aggregation/Cargo.toml" \
      --test ivc_keccak_final \
      --features keccak-transcript,truncated-challenges,fewer-point-sets \
      -- --ignored --nocapture
  fi
}

run_solidity_bench() {
  local features
  local leaf_features
  features="$(cargo_features "$OUTER_SINGLE_H_COMMITMENT")"
  leaf_features="$(cargo_features 0)"

  if [[ "$CHECK_ONLY" -eq 0 ]]; then
    require_pinned_solc
  fi

  if [[ "$OUTER_SINGLE_H_COMMITMENT" -eq 1 ]]; then
    echo "[ivc-bench] compiling multi-limb IVC leaf-bundle generator"
    echo "+ SRS_DIR=$SRS_DIR cargo test --release --features $leaf_features --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e --no-run"
    (
      cd "$ROOT_DIR"
      SRS_DIR="$SRS_DIR" cargo test --release \
        --features "$leaf_features" \
        --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e \
        --no-run
    )

    if [[ "$CHECK_ONLY" -eq 0 ]]; then
      mkdir -p "$(dirname "$IVC_LEAF_BUNDLE")"
      echo "[ivc-bench] generating multi-limb IVC leaf bundle"
      echo "+ HALO2_SOLIDITY_RUN_IVC_BENCH=1 HALO2_SOLIDITY_WRITE_IVC_LEAF_BUNDLE=1 HALO2_SOLIDITY_IVC_LEAF_BUNDLE=$IVC_LEAF_BUNDLE SRS_DIR=$SRS_DIR cargo test --release --features $leaf_features --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e -- --nocapture"
      (
        cd "$ROOT_DIR"
        HALO2_SOLIDITY_RUN_IVC_BENCH=1 \
          HALO2_SOLIDITY_WRITE_IVC_LEAF_BUNDLE=1 \
          HALO2_SOLIDITY_IVC_LEAF_BUNDLE="$IVC_LEAF_BUNDLE" \
          SRS_DIR="$SRS_DIR" cargo test --release \
            --features "$leaf_features" \
            --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e \
            -- --nocapture
      )
    fi
  fi

  echo "[ivc-bench] compiling IVC Keccak Solidity verifier bench (Poseidon-chain leaves)"
  echo "+ SRS_DIR=$SRS_DIR cargo test --release --features $features --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e --no-run"
  (
    cd "$ROOT_DIR"
    SRS_DIR="$SRS_DIR" cargo test --release \
      --features "$features" \
      --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e \
      --no-run
  )

  if [[ "$CHECK_ONLY" -eq 0 ]]; then
    echo "[ivc-bench] running IVC Keccak Solidity verifier bench (Poseidon-chain leaves)"
    echo "+ HALO2_SOLIDITY_RUN_IVC_BENCH=1 HALO2_SOLIDITY_IVC_LEAF_BUNDLE=$IVC_LEAF_BUNDLE SRS_DIR=$SRS_DIR cargo test --release --features $features --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e -- --nocapture"
    (
      cd "$ROOT_DIR"
      HALO2_SOLIDITY_RUN_IVC_BENCH=1 \
        HALO2_SOLIDITY_IVC_LEAF_BUNDLE="$IVC_LEAF_BUNDLE" \
        SRS_DIR="$SRS_DIR" cargo test --release \
        --features "$features" \
        --test ivc_keccak_solidity ivc_final_keccak_solidity_e2e \
        -- --nocapture
    )

    local dump_dir="$ROOT_DIR/target/ivc-keccak-solidity-dump"
    if [[ -d "$dump_dir" ]]; then
      echo "[ivc-bench] generated Solidity artifacts: $dump_dir"
      if [[ -f "$dump_dir/contract-sizes.txt" ]]; then
        echo "[ivc-bench] contract sizes:"
        cat "$dump_dir/contract-sizes.txt"
      fi
    fi
  fi
}

require_cmd cargo
ensure_srs_assets

echo "[ivc-bench] SRS_DIR=$SRS_DIR"
if env_flag_enabled "$ALLOW_UNPINNED_SOLC"; then
  echo "[ivc-bench] unpinned solc: enabled"
fi
if [[ -n "${RUSTUP_TOOLCHAIN:-}" ]]; then
  echo "[ivc-bench] RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN"
fi
if [[ "$OUTER_SINGLE_H_COMMITMENT" -eq 1 ]]; then
  echo "[ivc-bench] outer single-H commitment: enabled"
  echo "[ivc-bench] IVC_LEAF_BUNDLE=$IVC_LEAF_BUNDLE"
else
  echo "[ivc-bench] outer single-H commitment: disabled"
fi

if [[ "$RUN_NATIVE_MIDFALL" -eq 1 ]]; then
  run_native_midfall
fi

if [[ "$RUN_SOLIDITY_BENCH" -eq 1 ]]; then
  run_solidity_bench
fi

echo "[ivc-bench] done"

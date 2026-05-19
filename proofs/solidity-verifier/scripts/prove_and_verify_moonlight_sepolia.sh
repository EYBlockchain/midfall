#!/usr/bin/env bash
set -Eeuo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MIDFALL_DIR="$(cd "$ROOT_DIR/../.." && pwd)"
DEFAULT_MOONLIGHT_DIR="$(cd "$MIDFALL_DIR/.." && pwd)/Moonlight"
cd "$ROOT_DIR"

MOONLIGHT_DIR="${MOONLIGHT_DIR:-"$DEFAULT_MOONLIGHT_DIR"}"
MOONLIGHT_TEST="${MOONLIGHT_WRAP_TEST:-wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs}"
DUMP_DIR="${MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR:-"$ROOT_DIR/target/moonlight-wrap-solidity-dump"}"
SRS_DIR="${SRS_DIR:-"$ROOT_DIR/.srs"}"
RPC_URL="${SEPOLIA_RPC_URL:-${ETH_RPC_URL:-}}"
CHAIN="${CHAIN:-sepolia}"
SOLC_BIN="${SOLC:-"$ROOT_DIR/.solc/solc"}"
DEPLOYMENT_ENV="${MOONLIGHT_DEPLOYMENT_ENV:-"$ROOT_DIR/target/moonlight-wrap-sepolia-deployment.env"}"
VERIFIER_ADDRESS="${MOONLIGHT_VERIFIER_ADDRESS:-}"
VK_ADDRESS="${MOONLIGHT_VK_ADDRESS:-}"
PRIVATE_KEY_VALUE="${PRIVATE_KEY:-${ETH_PRIVATE_KEY:-}}"
WALLET_KEYSTORE="${ETH_KEYSTORE:-${MOONLIGHT_SEPOLIA_KEYSTORE:-}}"
WALLET_ACCOUNT="${ETH_KEYSTORE_ACCOUNT:-${MOONLIGHT_SEPOLIA_ACCOUNT:-}}"
WALLET_PASSWORD_FILE="${ETH_PASSWORD_FILE:-${MOONLIGHT_SEPOLIA_PASSWORD_FILE:-}}"
WALLET_FROM="${ETH_FROM:-${MOONLIGHT_SEPOLIA_FROM:-}}"
GAS_LIMIT="${MOONLIGHT_VERIFY_GAS_LIMIT:-5000000}"
RUN_PROVE=1
RUN_DEPLOY=0
RUN_SEND=0
RUN_TRACE="${MOONLIGHT_RUN_WRAP_SOLIDITY_TRACE:-1}"
SKIP_CONTRACT_VERIFY=0
WALLET_ARGS=()

if [[ -z "$WALLET_PASSWORD_FILE" && -n "${ETH_PASSWORD:-}" && -f "${ETH_PASSWORD:-}" ]]; then
  WALLET_PASSWORD_FILE="$ETH_PASSWORD"
fi

usage() {
  cat <<'USAGE'
Create the Moonlight wrap proof, then verify its generated calldata on Sepolia.

Usage:
  scripts/prove_and_verify_moonlight_sepolia.sh [options]

Typical flows:
  # Prove locally, then eth_call an already deployed verifier on Sepolia.
  scripts/prove_and_verify_moonlight_sepolia.sh --verifier 0x...

  # Prove, deploy fresh Moonlight VK/verifier contracts, then eth_call them.
  scripts/prove_and_verify_moonlight_sepolia.sh --deploy

  # Reuse existing dump/calldata and broadcast a view tx to the verifier.
  scripts/prove_and_verify_moonlight_sepolia.sh --skip-prove --verifier 0x... --send

Required:
  --rpc-url URL             Sepolia RPC URL, or set SEPOLIA_RPC_URL / ETH_RPC_URL.
  --verifier ADDRESS        Existing Halo2Verifier address, unless --deploy or
                            --deployment-env supplies one.

Options:
  --deploy                  Deploy Moonlight contracts before verification.
  --vk-address ADDRESS      Reuse an existing VK when --deploy is set.
  --deployment-env PATH     Read/write deployment env file. Defaults to
                            target/moonlight-wrap-sepolia-deployment.env.
  --moonlight-dir DIR       Moonlight checkout. Defaults to sibling ../Moonlight.
  --dump-dir DIR            Dump directory for generated Solidity/proof/calldata.
  --srs-dir DIR             SRS directory passed to the Moonlight proof command.
  --rpc-url URL             Sepolia RPC URL.
  --chain NAME_OR_ID        Foundry chain. Defaults to sepolia.
  --solc PATH               solc binary passed through to proof/deploy commands.
  --gas-limit GAS           Gas limit for eth_call / optional send tx.
  --skip-prove              Use existing calldata.bin instead of running Moonlight.
  --trace / --no-trace      Toggle Moonlight trace dump env. Trace is on by default.
  --send                    Broadcast a transaction after the successful eth_call.
  --skip-contract-verify    When --deploy is used, do not verify source on Etherscan.

Wallet options forwarded to deploy/send when needed:
  --private-key KEY | --interactive | --ledger | --trezor | --browser
  --keystore PATH --account NAME --password-file PATH --from ADDRESS

Environment:
  SEPOLIA_RPC_URL, PRIVATE_KEY, ETHERSCAN_API_KEY, SOLC, SRS_DIR,
  MOONLIGHT_VERIFIER_ADDRESS, MOONLIGHT_VK_ADDRESS,
  ETH_KEYSTORE_ACCOUNT / MOONLIGHT_SEPOLIA_ACCOUNT,
  ETH_PASSWORD_FILE / MOONLIGHT_SEPOLIA_PASSWORD_FILE
USAGE
}

die() {
  echo "[moonlight-prove-verify] error: $*" >&2
  exit 1
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found on PATH: $1"
}

is_address() {
  [[ "${1:-}" =~ ^0x[0-9a-fA-F]{40}$ ]]
}

while (($#)); do
  case "$1" in
    --deploy)
      RUN_DEPLOY=1
      ;;
    --vk-address)
      [[ $# -ge 2 ]] || die "--vk-address requires ADDRESS"
      VK_ADDRESS="$2"
      shift
      ;;
    --deployment-env)
      [[ $# -ge 2 ]] || die "--deployment-env requires PATH"
      DEPLOYMENT_ENV="$2"
      shift
      ;;
    --moonlight-dir)
      [[ $# -ge 2 ]] || die "--moonlight-dir requires DIR"
      MOONLIGHT_DIR="$2"
      shift
      ;;
    --dump-dir)
      [[ $# -ge 2 ]] || die "--dump-dir requires DIR"
      DUMP_DIR="$2"
      shift
      ;;
    --srs-dir)
      [[ $# -ge 2 ]] || die "--srs-dir requires DIR"
      SRS_DIR="$2"
      shift
      ;;
    --rpc-url)
      [[ $# -ge 2 ]] || die "--rpc-url requires URL"
      RPC_URL="$2"
      shift
      ;;
    --chain)
      [[ $# -ge 2 ]] || die "--chain requires NAME_OR_ID"
      CHAIN="$2"
      shift
      ;;
    --solc)
      [[ $# -ge 2 ]] || die "--solc requires PATH"
      SOLC_BIN="$2"
      shift
      ;;
    --gas-limit)
      [[ $# -ge 2 ]] || die "--gas-limit requires GAS"
      GAS_LIMIT="$2"
      shift
      ;;
    --verifier)
      [[ $# -ge 2 ]] || die "--verifier requires ADDRESS"
      VERIFIER_ADDRESS="$2"
      shift
      ;;
    --skip-prove)
      RUN_PROVE=0
      ;;
    --trace)
      RUN_TRACE=1
      ;;
    --no-trace)
      RUN_TRACE=0
      ;;
    --send)
      RUN_SEND=1
      ;;
    --skip-contract-verify)
      SKIP_CONTRACT_VERIFY=1
      ;;
    --private-key)
      [[ $# -ge 2 ]] || die "--private-key requires KEY"
      WALLET_ARGS+=(--private-key "$2")
      shift
      ;;
    --interactive|--ledger|--trezor|--browser)
      WALLET_ARGS+=("$1")
      ;;
    --keystore|--account|--password-file|--from)
      [[ $# -ge 2 ]] || die "$1 requires a value"
      WALLET_ARGS+=("$1" "$2")
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

[[ -n "$RPC_URL" ]] || die "missing Sepolia RPC URL; pass --rpc-url or set SEPOLIA_RPC_URL"
if [[ -n "$VERIFIER_ADDRESS" ]]; then
  is_address "$VERIFIER_ADDRESS" || die "--verifier is not an Ethereum address: $VERIFIER_ADDRESS"
fi
if [[ -n "$VK_ADDRESS" ]]; then
  is_address "$VK_ADDRESS" || die "--vk-address is not an Ethereum address: $VK_ADDRESS"
fi
if [[ ${#WALLET_ARGS[@]} -eq 0 && -n "$PRIVATE_KEY_VALUE" ]]; then
  WALLET_ARGS+=(--private-key "$PRIVATE_KEY_VALUE")
fi
if [[ ${#WALLET_ARGS[@]} -eq 0 ]]; then
  if [[ -n "$WALLET_KEYSTORE" ]]; then
    WALLET_ARGS+=(--keystore "$WALLET_KEYSTORE")
  fi
  if [[ -n "$WALLET_ACCOUNT" ]]; then
    WALLET_ARGS+=(--account "$WALLET_ACCOUNT")
  fi
  if [[ -n "$WALLET_PASSWORD_FILE" ]]; then
    [[ -f "$WALLET_PASSWORD_FILE" ]] || die "wallet password file not found: $WALLET_PASSWORD_FILE"
    WALLET_ARGS+=(--password-file "$WALLET_PASSWORD_FILE")
  fi
  if [[ -n "$WALLET_FROM" ]]; then
    WALLET_ARGS+=(--from "$WALLET_FROM")
  fi
fi

require_cmd cast
require_cmd xxd

if [[ "$RUN_PROVE" -eq 1 ]]; then
  require_cmd cargo
  [[ -f "$MOONLIGHT_DIR/aggregation/Cargo.toml" ]] || die "Moonlight aggregation manifest not found: $MOONLIGHT_DIR/aggregation/Cargo.toml"
  mkdir -p "$DUMP_DIR"
  marker="$(mktemp)"
  echo "[moonlight-prove-verify] generating Moonlight proof and Solidity calldata"
  echo "[moonlight-prove-verify] dump dir: $DUMP_DIR"
  SOLC="$SOLC_BIN" \
  SRS_DIR="$SRS_DIR" \
  MOONLIGHT_RUN_WRAP_SOLIDITY_BENCH=1 \
  MOONLIGHT_RUN_WRAP_SOLIDITY_TRACE="$RUN_TRACE" \
  MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR="$DUMP_DIR" \
    cargo test --manifest-path "$MOONLIGHT_DIR/aggregation/Cargo.toml" \
      "$MOONLIGHT_TEST" --release --lib -- --ignored --nocapture
  if [[ ! "$DUMP_DIR/calldata.bin" -nt "$marker" || ! "$DUMP_DIR/proof.bin" -nt "$marker" ]]; then
    rm -f "$marker"
    die "Moonlight run did not refresh calldata.bin/proof.bin. Check that the Moonlight checkout includes the Solidity dump hooks."
  fi
  rm -f "$marker"
fi

[[ -f "$DUMP_DIR/calldata.bin" ]] || die "missing calldata: $DUMP_DIR/calldata.bin"
[[ -f "$DUMP_DIR/proof.bin" ]] || die "missing proof: $DUMP_DIR/proof.bin"
selector="$(xxd -p -l 4 "$DUMP_DIR/calldata.bin")"
[[ "$selector" == "1e8e1e13" ]] || die "calldata.bin has unexpected selector 0x$selector"

if [[ "$RUN_DEPLOY" -eq 1 ]]; then
  if [[ -n "$VERIFIER_ADDRESS" ]]; then
    die "--deploy conflicts with --verifier; pass one or the other"
  fi
  require_cmd forge
  deploy_args=(
    --dump-dir "$DUMP_DIR"
    --rpc-url "$RPC_URL"
    --chain "$CHAIN"
    --solc "$SOLC_BIN"
    --output-env "$DEPLOYMENT_ENV"
  )
  if [[ -n "$VK_ADDRESS" ]]; then
    deploy_args+=(--vk-address "$VK_ADDRESS")
  fi
  if [[ "$SKIP_CONTRACT_VERIFY" -eq 1 ]]; then
    deploy_args+=(--skip-verify)
  fi
  deploy_args+=("${WALLET_ARGS[@]}")
  "$ROOT_DIR/scripts/deploy_moonlight_sepolia.sh" "${deploy_args[@]}"
fi

if [[ -z "$VERIFIER_ADDRESS" && -f "$DEPLOYMENT_ENV" ]]; then
  # shellcheck disable=SC1090
  source "$DEPLOYMENT_ENV"
  VERIFIER_ADDRESS="${MOONLIGHT_VERIFIER_ADDRESS:-}"
fi
is_address "$VERIFIER_ADDRESS" || die "missing verifier address; pass --verifier, --deploy, or --deployment-env"

CALLDATA="0x$(xxd -p -c 0 "$DUMP_DIR/calldata.bin")"
EXPECTED="0x0000000000000000000000000000000000000000000000000000000000000001"

echo "[moonlight-prove-verify] eth_call verifyProof on $VERIFIER_ADDRESS"
OUTPUT="$(cast call "$VERIFIER_ADDRESS" --data "$CALLDATA" --rpc-url "$RPC_URL" --gas-limit "$GAS_LIMIT")"
if [[ "$OUTPUT" != "$EXPECTED" ]]; then
  die "Sepolia eth_call returned $OUTPUT; expected $EXPECTED"
fi
echo "[moonlight-prove-verify] PASS: Sepolia eth_call returned true"

if [[ "$RUN_SEND" -eq 1 ]]; then
  if [[ ${#WALLET_ARGS[@]} -eq 0 ]]; then
    die "--send needs a wallet option or PRIVATE_KEY"
  fi
  echo "[moonlight-prove-verify] broadcasting verifyProof transaction"
  cast send "$VERIFIER_ADDRESS" "$CALLDATA" \
    --rpc-url "$RPC_URL" \
    --chain "$CHAIN" \
    --gas-limit "$GAS_LIMIT" \
    "${WALLET_ARGS[@]}"
fi

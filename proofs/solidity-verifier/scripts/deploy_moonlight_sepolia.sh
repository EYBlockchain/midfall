#!/usr/bin/env bash
set -Eeuo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

DUMP_DIR="${MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR:-"$ROOT_DIR/target/moonlight-wrap-solidity-dump"}"
RPC_URL="${SEPOLIA_RPC_URL:-${ETH_RPC_URL:-}}"
CHAIN="${CHAIN:-sepolia}"
SOLC_BIN="${SOLC:-"$ROOT_DIR/.solc/solc"}"
OPTIMIZER_RUNS="${SOLC_OPTIMIZE_RUNS:-200}"
EVM_VERSION="${EVM_VERSION:-cancun}"
VERIFY_CONTRACTS=1
VERIFIER_PROVIDER="${VERIFIER_PROVIDER:-etherscan}"
ETHERSCAN_KEY="${ETHERSCAN_API_KEY:-}"
VK_ADDRESS="${MOONLIGHT_VK_ADDRESS:-}"
OUTPUT_ENV="${MOONLIGHT_DEPLOYMENT_ENV:-"$ROOT_DIR/target/moonlight-wrap-sepolia-deployment.env"}"
OUTPUT_JSON="${MOONLIGHT_DEPLOYMENT_JSON:-"$ROOT_DIR/target/moonlight-wrap-sepolia-deployment.json"}"
DEPLOY_GAS_LIMIT="${DEPLOY_GAS_LIMIT:-}"
PRIVATE_KEY_VALUE="${PRIVATE_KEY:-${ETH_PRIVATE_KEY:-}}"
WALLET_KEYSTORE="${ETH_KEYSTORE:-${MOONLIGHT_SEPOLIA_KEYSTORE:-}}"
WALLET_ACCOUNT="${ETH_KEYSTORE_ACCOUNT:-${MOONLIGHT_SEPOLIA_ACCOUNT:-}}"
WALLET_PASSWORD_FILE="${ETH_PASSWORD_FILE:-${MOONLIGHT_SEPOLIA_PASSWORD_FILE:-}}"
WALLET_FROM="${ETH_FROM:-${MOONLIGHT_SEPOLIA_FROM:-}}"
WALLET_ARGS=()

if [[ -z "$WALLET_PASSWORD_FILE" && -n "${ETH_PASSWORD:-}" && -f "${ETH_PASSWORD:-}" ]]; then
  WALLET_PASSWORD_FILE="$ETH_PASSWORD"
fi

usage() {
  cat <<'USAGE'
Deploy generated Moonlight wrap verifier contracts on Sepolia.

Usage:
  scripts/deploy_moonlight_sepolia.sh [options]

Required:
  --rpc-url URL             Sepolia RPC URL, or set SEPOLIA_RPC_URL / ETH_RPC_URL.
  A Foundry wallet option, or set PRIVATE_KEY / ETH_PRIVATE_KEY.
                            The script also honors ETH_KEYSTORE_ACCOUNT /
                            MOONLIGHT_SEPOLIA_ACCOUNT with a password file.

Options:
  --dump-dir DIR            Directory containing Halo2Verifier.sol and
                            Halo2VerifyingKey.sol. Defaults to
                            target/moonlight-wrap-solidity-dump.
  --vk-address ADDRESS      Reuse an existing Halo2VerifyingKey and deploy only
                            Halo2Verifier against it.
  --output-env PATH         Write addresses as shell env. Defaults to
                            target/moonlight-wrap-sepolia-deployment.env.
  --output-json PATH        Write addresses as JSON. Defaults to
                            target/moonlight-wrap-sepolia-deployment.json.
  --solc PATH               solc binary. Defaults to $SOLC or .solc/solc.
  --optimizer-runs N        Solidity optimizer runs. Defaults to 200.
  --evm-version NAME        Solidity EVM target. Defaults to cancun.
  --chain NAME_OR_ID        Foundry chain. Defaults to sepolia.
  --gas-limit GAS           Optional deployment gas limit.
  --skip-verify             Do not submit source verification.
  --verifier NAME           Foundry verifier provider. Defaults to etherscan.
  --etherscan-api-key KEY   Etherscan API key, or set ETHERSCAN_API_KEY.

Wallet options forwarded to forge:
  --private-key KEY | --interactive | --ledger | --trezor | --browser
  --keystore PATH --account NAME --password-file PATH --from ADDRESS

Examples:
  SEPOLIA_RPC_URL=https://... PRIVATE_KEY=0x... ETHERSCAN_API_KEY=... \
    scripts/deploy_moonlight_sepolia.sh

  source target/moonlight-wrap-sepolia-wallet.env
  SEPOLIA_RPC_URL=https://... scripts/deploy_moonlight_sepolia.sh --skip-verify

  scripts/deploy_moonlight_sepolia.sh --vk-address 0x... --skip-verify
USAGE
}

die() {
  echo "[moonlight-deploy] error: $*" >&2
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
    --dump-dir)
      [[ $# -ge 2 ]] || die "--dump-dir requires DIR"
      DUMP_DIR="$2"
      shift
      ;;
    --rpc-url)
      [[ $# -ge 2 ]] || die "--rpc-url requires URL"
      RPC_URL="$2"
      shift
      ;;
    --vk-address)
      [[ $# -ge 2 ]] || die "--vk-address requires ADDRESS"
      VK_ADDRESS="$2"
      shift
      ;;
    --output-env)
      [[ $# -ge 2 ]] || die "--output-env requires PATH"
      OUTPUT_ENV="$2"
      shift
      ;;
    --output-json)
      [[ $# -ge 2 ]] || die "--output-json requires PATH"
      OUTPUT_JSON="$2"
      shift
      ;;
    --solc)
      [[ $# -ge 2 ]] || die "--solc requires PATH"
      SOLC_BIN="$2"
      shift
      ;;
    --optimizer-runs)
      [[ $# -ge 2 ]] || die "--optimizer-runs requires N"
      OPTIMIZER_RUNS="$2"
      shift
      ;;
    --evm-version)
      [[ $# -ge 2 ]] || die "--evm-version requires NAME"
      EVM_VERSION="$2"
      shift
      ;;
    --chain)
      [[ $# -ge 2 ]] || die "--chain requires NAME_OR_ID"
      CHAIN="$2"
      shift
      ;;
    --gas-limit)
      [[ $# -ge 2 ]] || die "--gas-limit requires GAS"
      DEPLOY_GAS_LIMIT="$2"
      shift
      ;;
    --skip-verify)
      VERIFY_CONTRACTS=0
      ;;
    --verifier)
      [[ $# -ge 2 ]] || die "--verifier requires NAME"
      VERIFIER_PROVIDER="$2"
      shift
      ;;
    --etherscan-api-key)
      [[ $# -ge 2 ]] || die "--etherscan-api-key requires KEY"
      ETHERSCAN_KEY="$2"
      shift
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
[[ -d "$DUMP_DIR" ]] || die "dump directory not found: $DUMP_DIR"
[[ -f "$DUMP_DIR/Halo2Verifier.sol" ]] || die "missing $DUMP_DIR/Halo2Verifier.sol"
[[ -f "$DUMP_DIR/Halo2VerifyingKey.sol" ]] || die "missing $DUMP_DIR/Halo2VerifyingKey.sol"
[[ -x "$SOLC_BIN" || "$(command -v "$SOLC_BIN" 2>/dev/null || true)" ]] || die "solc not found: $SOLC_BIN"
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
if [[ ${#WALLET_ARGS[@]} -eq 0 ]]; then
  die "missing wallet; pass --private-key/--interactive/etc. or set PRIVATE_KEY"
fi

require_cmd forge
require_cmd cast

COMMON_CREATE_ARGS=(
  --broadcast
  --rpc-url "$RPC_URL"
  --chain "$CHAIN"
  --use "$SOLC_BIN"
  --via-ir
  --evm-version "$EVM_VERSION"
  --optimize
  --optimizer-runs "$OPTIMIZER_RUNS"
  --no-metadata
  --root "$ROOT_DIR"
)
if [[ -n "$DEPLOY_GAS_LIMIT" ]]; then
  COMMON_CREATE_ARGS+=(--gas-limit "$DEPLOY_GAS_LIMIT")
fi
if [[ "$VERIFY_CONTRACTS" -eq 1 ]]; then
  [[ -n "$ETHERSCAN_KEY" ]] || die "ETHERSCAN_API_KEY is required unless --skip-verify is set"
  COMMON_CREATE_ARGS+=(
    --verify
    --verifier "$VERIFIER_PROVIDER"
    --etherscan-api-key "$ETHERSCAN_KEY"
  )
fi

LAST_DEPLOYED=""
run_create() {
  local label="$1"
  shift
  local log
  log="$(mktemp)"
  echo "[moonlight-deploy] deploying $label"
  if ! forge create "${COMMON_CREATE_ARGS[@]}" "${WALLET_ARGS[@]}" "$@" 2>&1 | tee "$log"; then
    rm -f "$log"
    die "forge create failed for $label"
  fi
  LAST_DEPLOYED="$(awk '/Deployed to:/ {print $3}' "$log" | tail -n 1)"
  rm -f "$log"
  is_address "$LAST_DEPLOYED" || die "could not parse deployed address for $label"
  echo "[moonlight-deploy] $label = $LAST_DEPLOYED"
}

if [[ -z "$VK_ADDRESS" ]]; then
  run_create \
    "Halo2VerifyingKey" \
    "$DUMP_DIR/Halo2VerifyingKey.sol:Halo2VerifyingKey"
  VK_ADDRESS="$LAST_DEPLOYED"
else
  echo "[moonlight-deploy] reusing Halo2VerifyingKey = $VK_ADDRESS"
fi

run_create \
  "Halo2Verifier" \
  "$DUMP_DIR/Halo2Verifier.sol:Halo2Verifier" \
  --constructor-args "$VK_ADDRESS"
VERIFIER_ADDRESS="$LAST_DEPLOYED"

mkdir -p "$(dirname "$OUTPUT_ENV")" "$(dirname "$OUTPUT_JSON")"
{
  printf 'MOONLIGHT_VK_ADDRESS=%q\n' "$VK_ADDRESS"
  printf 'MOONLIGHT_VERIFIER_ADDRESS=%q\n' "$VERIFIER_ADDRESS"
  printf 'MOONLIGHT_DEPLOY_CHAIN=%q\n' "$CHAIN"
  printf 'MOONLIGHT_DUMP_DIR=%q\n' "$DUMP_DIR"
} >"$OUTPUT_ENV"
cat >"$OUTPUT_JSON" <<EOF
{
  "chain": "$CHAIN",
  "dumpDir": "$DUMP_DIR",
  "vk": "$VK_ADDRESS",
  "verifier": "$VERIFIER_ADDRESS"
}
EOF

echo "[moonlight-deploy] wrote $OUTPUT_ENV"
echo "[moonlight-deploy] wrote $OUTPUT_JSON"
echo "[moonlight-deploy] done"

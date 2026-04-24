#!/usr/bin/env bash
#
# Run the full Solidity-verifier test suite described in
# proofs/solidity-verifier/ARCHITECTURE.md §5.
#
# Stages (in order):
#   1. cargo run --bin generate          (regenerate VK + fixtures, §5.1)
#   2. forge build                       (§5.2)
#   3. forge test                        (24 Solidity unit/component/e2e, §5.3)
#   4. cargo test --test forge           (Rust ↔ Solidity trace-diff, §5.5)
#   5. cargo test --test pbt --ignored   (7 property-based tests, §5.6)
#
# Each stage prints a coloured banner with a short description of what
# it exercises, then runs the command and reports pass/fail + timing.
# Everything (stdout + stderr) is mirrored to a timestamped log file
# under `target/solidity-verifier-logs/`. The script exits non-zero on
# the first failing stage and prints a final summary table.
#
# Usage:
#   bash proofs/solidity-verifier/scripts/run-all-tests.sh
#
# Environment:
#   SRS_DIR   Path to the KZG trusted-setup assets. Defaults to
#             $REPO_ROOT/zk_stdlib/examples/assets.
#   NO_COLOR  Disable ANSI colours (honored in addition to non-TTY
#             detection).

set -u
set -o pipefail

# ------------------------------------------------------------------- paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$CRATE_DIR/../.." && pwd)"
LOG_DIR="$REPO_ROOT/target/solidity-verifier-logs"
mkdir -p "$LOG_DIR"
TIMESTAMP="$(date +%Y%m%dT%H%M%S)"
LOG_FILE="$LOG_DIR/run-all-tests-$TIMESTAMP.log"

# ---------------------------------------------------- colour detection (pre-exec)
# Must happen before we redirect stdout: after `exec > >(tee ...)` the
# [ -t 1 ] check would always be false even when the user is watching
# interactively.
if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
    BOLD=$'\e[1m'
    DIM=$'\e[2m'
    RED=$'\e[31m'
    GREEN=$'\e[32m'
    YELLOW=$'\e[33m'
    CYAN=$'\e[36m'
    GREY=$'\e[90m'
    RESET=$'\e[0m'
    COLOR_MODE="tty"
else
    BOLD=; DIM=; RED=; GREEN=; YELLOW=; CYAN=; GREY=; RESET=
    COLOR_MODE="off"
fi

# ------------------------------------------------- mirror all output to a log
exec > >(tee -a "$LOG_FILE") 2>&1

# Force downstream tools to keep coloured output even though their
# stdout is now a pipe (to tee).
export CARGO_TERM_COLOR=always
export FORCE_COLOR=1
export CLICOLOR_FORCE=1

# ----------------------------------------------------------------- env defaults
export SRS_DIR="${SRS_DIR:-$REPO_ROOT/zk_stdlib/examples/assets}"

# ----------------------------------------------------------------- preflight
missing=""
for bin in cargo forge; do
    if ! command -v "$bin" >/dev/null 2>&1; then
        missing="$missing $bin"
    fi
done
if [ -n "$missing" ]; then
    printf '%s[fatal]%s required binaries missing:%s\n' \
        "$RED$BOLD" "$RESET" "$missing"
    printf '        install cargo (rustup) and forge (foundryup) and retry.\n'
    exit 127
fi
if [ ! -d "$SRS_DIR" ]; then
    printf '%s[warn]%s SRS_DIR=%s does not exist; the `generate` stage will fail.\n' \
        "$YELLOW$BOLD" "$RESET" "$SRS_DIR"
fi

# -------------------------------------------------------------- stage bookkeeping
STAGES=()
STATUSES=()
TIMINGS=()
TOTAL_START=$SECONDS
TOTAL_STAGES=5

step() {
    local idx="$1" title="$2" desc="$3" cmd="$4"
    printf '\n%s==> [%s/%s]%s %s%s%s\n' \
        "$BOLD$CYAN" "$idx" "$TOTAL_STAGES" "$RESET" "$BOLD" "$title" "$RESET"
    printf '    %s%s%s\n' "$DIM" "$desc" "$RESET"
    printf '    %s$ %s%s\n' "$GREY" "$cmd" "$RESET"

    STAGES+=("$title")
    local start=$SECONDS
    # Run in a subshell so stage-local `cd` doesn't leak into later stages.
    if ( eval "$cmd" ); then
        local dur=$((SECONDS - start))
        TIMINGS+=("$dur")
        STATUSES+=("ok")
        printf '    %s[ok]%s   in %ss\n' "$GREEN$BOLD" "$RESET" "$dur"
    else
        local rc=$?
        local dur=$((SECONDS - start))
        TIMINGS+=("$dur")
        STATUSES+=("fail")
        printf '    %s[fail]%s in %ss (exit %s)\n' \
            "$RED$BOLD" "$RESET" "$dur" "$rc"
        printf '    %sFull log: %s%s\n' "$YELLOW" "$LOG_FILE" "$RESET"
        summarise_and_exit 1
    fi
}

summarise_and_exit() {
    local exit_code="$1"
    local total=$((SECONDS - TOTAL_START))
    printf '\n%s==== summary ====%s\n' "$BOLD" "$RESET"
    for i in "${!STAGES[@]}"; do
        local tag
        if [ "${STATUSES[$i]}" = "ok" ]; then
            tag="${GREEN}ok  ${RESET}"
        else
            tag="${RED}fail${RESET}"
        fi
        printf '  [%b] %-60s %4ss\n' "$tag" "${STAGES[$i]}" "${TIMINGS[$i]}"
    done
    printf '%s=================%s\n' "$BOLD" "$RESET"
    if [ "$exit_code" = 0 ]; then
        printf '%s[pass]%s all %s stages succeeded in %ss total.\n' \
            "$GREEN$BOLD" "$RESET" "$TOTAL_STAGES" "$total"
    else
        printf '%s[fail]%s after %ss total.\n' \
            "$RED$BOLD" "$RESET" "$total"
    fi
    printf '       log written to %s\n' "$LOG_FILE"
    exit "$exit_code"
}

# ---------------------------------------------------------------------- banner
printf '%s==================================================%s\n' "$BOLD$CYAN" "$RESET"
printf '%s Solidity verifier - full test suite%s\n' "$BOLD$CYAN" "$RESET"
printf '%s==================================================%s\n' "$BOLD$CYAN" "$RESET"
printf '  repo root   : %s\n' "$REPO_ROOT"
printf '  crate dir   : %s\n' "$CRATE_DIR"
printf '  SRS_DIR     : %s\n' "$SRS_DIR"
printf '  log file    : %s\n' "$LOG_FILE"
printf '  colour mode : %s\n' "$COLOR_MODE"
printf '  started     : %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# ---------------------------------------------------------------------- stages
step 1 'Regenerate VK contract + proof fixtures' \
    'Runs cargo run --bin generate: executes a fresh KZG prover pass against the poseidon fixture and re-emits PoseidonVerifyingKey.sol plus fixtures/proof.bin, fixtures/instance.be and all per-phase witness blobs.' \
    "cd '$REPO_ROOT' && cargo run --quiet -p midnight-solidity-verifier --bin generate"

step 2 'forge build' \
    'Compiles PoseidonVerifier.sol and the freshly regenerated PoseidonVerifyingKey.sol under solc 0.8.24 with via_ir + optimizer (200 runs). Emits artefacts into out/.' \
    "cd '$CRATE_DIR' && forge build"

step 3 'forge test (24 Solidity unit / component / end-to-end tests)' \
    'Runs the full Foundry test suite: per-phase positional signatures, algebra helpers, gate / lookup / trashcan bytecode interpreters, linearization commitment, multi-prepare driver, final pairing RHS, and test_verify_poseidon_proof / test_verify_rejects_mutated_proof. A bit-flip anywhere in the proof is rejected.' \
    "cd '$CRATE_DIR' && forge test"

step 4 'cargo test --test forge (Rust ↔ Solidity trace-diff harness)' \
    'Regenerates the proof, runs forge test -vv, replays the Fiat-Shamir transcript on the Rust side and asserts element-wise identical traces across all challenges, scalar reads and point reads.' \
    "cd '$REPO_ROOT' && cargo test --quiet -p midnight-solidity-verifier --test forge --release"

step 5 'cargo test --test pbt (7 property-based tests, ~60 s)' \
    '7 #[ignore] tests driving the Solidity verifier in-process via revm: determinism, positive accept, wrong instance, mutated proof, VK blob byte mutation, 5 malformed-calldata variants, and mutated-VK-source + forge rebuild.' \
    "cd '$REPO_ROOT' && cargo test --quiet -p midnight-solidity-verifier --test pbt --release -- --ignored --test-threads=1"

summarise_and_exit 0

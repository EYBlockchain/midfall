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
# By default the noisy compilation/test output from cargo + forge is
# written to a timestamped log file only (kept quiet on the terminal
# so the orchestration banners stay readable); set VERBOSE=1 to also
# stream that output to the terminal. On failure, the last 40 lines
# of the log are dumped so the reader has enough context to debug
# without having to open the log file manually.
#
# Usage:
#   bash proofs/solidity-verifier/scripts/run-all-tests.sh
#   VERBOSE=1 bash proofs/solidity-verifier/scripts/run-all-tests.sh
#
# Environment:
#   SRS_DIR   Path to the KZG trusted-setup assets. Defaults to
#             $REPO_ROOT/zk_stdlib/examples/assets.
#   VERBOSE   If set and non-empty, also stream cargo/forge output to
#             the terminal (otherwise it's kept in the log file only).
#   NO_COLOR  Disable ANSI colours (honoured in addition to non-TTY
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

# ---------------------------------------------------- colour detection
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

# ---------------------------------------------------- quiet / verbose modes
# Default: hide cargo/forge output from the terminal, keep it in the log
# file only. Orchestration banners still appear on the terminal (and in
# the log). Set VERBOSE=1 to also stream the raw compilation output.
QUIET_MODE="${VERBOSE:+off}"    # "off" means verbose
QUIET_MODE="${QUIET_MODE:-on}"  # default to quiet

# FD 3 appends to the log file; used by `say` below to duplicate banner
# lines into the log without going through a tee pipe.
exec 3>>"$LOG_FILE"

# Force downstream tools to emit colour even though their stdout is a
# file (not a TTY). This keeps the log file readable with `less -R` and
# preserves colour in VERBOSE mode.
export CARGO_TERM_COLOR=always
export FORCE_COLOR=1
export CLICOLOR_FORCE=1

# ----------------------------------------------------------------- env defaults
export SRS_DIR="${SRS_DIR:-$REPO_ROOT/zk_stdlib/examples/assets}"

# ----------------------------------------------------- orchestration helpers
# `say` writes a formatted line to the terminal AND the log file. The
# argument list matches `printf` (format string + args). Use this
# everywhere instead of bare printf so the log captures the full
# orchestration narrative.
say() {
    # shellcheck disable=SC2059
    printf "$@"
    # shellcheck disable=SC2059
    printf "$@" >&3
}

# Run a stage command. In QUIET_MODE=on the command's stdout+stderr go
# to the log file only; in VERBOSE mode they're also streamed to the
# terminal via tee. Returns the command's exit status in both paths.
run_cmd() {
    local cmd="$1"
    if [ "$QUIET_MODE" = "on" ]; then
        ( eval "$cmd" ) >>"$LOG_FILE" 2>&1
    else
        ( eval "$cmd" ) 2>&1 | tee -a "$LOG_FILE"
    fi
}

# Print the last N lines of the log file (terminal only; the log file
# already contains them). Used on stage failure.
dump_log_tail() {
    local n="$1"
    say '%s----- last %s lines of %s -----%s\n' "$DIM" "$n" "$LOG_FILE" "$RESET"
    tail -n "$n" "$LOG_FILE" || true
    say '%s----- end log tail -----%s\n' "$DIM" "$RESET"
}

# ----------------------------------------------------------------- preflight
missing=""
for bin in cargo forge; do
    if ! command -v "$bin" >/dev/null 2>&1; then
        missing="$missing $bin"
    fi
done
if [ -n "$missing" ]; then
    say '%s[fatal]%s required binaries missing:%s\n' \
        "$RED$BOLD" "$RESET" "$missing"
    say '        install cargo (rustup) and forge (foundryup) and retry.\n'
    exit 127
fi
if [ ! -d "$SRS_DIR" ]; then
    say '%s[warn]%s SRS_DIR=%s does not exist; the `generate` stage will fail.\n' \
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
    say '\n%s==> [%s/%s]%s %s%s%s\n' \
        "$BOLD$CYAN" "$idx" "$TOTAL_STAGES" "$RESET" "$BOLD" "$title" "$RESET"
    say '    %s%s%s\n' "$DIM" "$desc" "$RESET"
    say '    %s$ %s%s\n' "$GREY" "$cmd" "$RESET"
    if [ "$QUIET_MODE" = "on" ]; then
        say '    %s(compilation output hidden; set VERBOSE=1 to stream)%s\n' \
            "$DIM" "$RESET"
    fi

    STAGES+=("$title")
    local start=$SECONDS
    if run_cmd "$cmd"; then
        local dur=$((SECONDS - start))
        TIMINGS+=("$dur")
        STATUSES+=("ok")
        say '    %s[ok]%s   in %ss\n' "$GREEN$BOLD" "$RESET" "$dur"
    else
        local rc=$?
        local dur=$((SECONDS - start))
        TIMINGS+=("$dur")
        STATUSES+=("fail")
        say '    %s[fail]%s in %ss (exit %s)\n' \
            "$RED$BOLD" "$RESET" "$dur" "$rc"
        say '    %sFull log: %s%s\n' "$YELLOW" "$LOG_FILE" "$RESET"
        if [ "$QUIET_MODE" = "on" ]; then
            dump_log_tail 40
        fi
        summarise_and_exit 1
    fi
}

summarise_and_exit() {
    local exit_code="$1"
    local total=$((SECONDS - TOTAL_START))
    say '\n%s==== summary ====%s\n' "$BOLD" "$RESET"
    for i in "${!STAGES[@]}"; do
        local tag
        if [ "${STATUSES[$i]}" = "ok" ]; then
            tag="${GREEN}ok  ${RESET}"
        else
            tag="${RED}fail${RESET}"
        fi
        say '  [%b] %-60s %4ss\n' "$tag" "${STAGES[$i]}" "${TIMINGS[$i]}"
    done
    say '%s=================%s\n' "$BOLD" "$RESET"
    if [ "$exit_code" = 0 ]; then
        say '%s[pass]%s all %s stages succeeded in %ss total.\n' \
            "$GREEN$BOLD" "$RESET" "$TOTAL_STAGES" "$total"
    else
        say '%s[fail]%s after %ss total.\n' \
            "$RED$BOLD" "$RESET" "$total"
    fi
    say '       log written to %s\n' "$LOG_FILE"
    exit "$exit_code"
}

# ---------------------------------------------------------------------- banner
say '%s==================================================%s\n' "$BOLD$CYAN" "$RESET"
say '%s Solidity verifier - full test suite%s\n' "$BOLD$CYAN" "$RESET"
say '%s==================================================%s\n' "$BOLD$CYAN" "$RESET"
say '  repo root   : %s\n' "$REPO_ROOT"
say '  crate dir   : %s\n' "$CRATE_DIR"
say '  SRS_DIR     : %s\n' "$SRS_DIR"
say '  log file    : %s\n' "$LOG_FILE"
say '  colour mode : %s\n' "$COLOR_MODE"
say '  quiet mode  : %s (set VERBOSE=1 to stream cargo/forge output)\n' "$QUIET_MODE"
say '  started     : %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"

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

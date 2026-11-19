#!/usr/bin/env bash
# verify.sh - ONE command that verifies a V2 ticket (PLAN-V2 §6, card Q0.3).
#
#   bash scripts/verify.sh --quick    build + DoneTest + ConeReport          (inner loop)
#   bash scripts/verify.sh --report   ConeReport + the progress report, NO build (the STATUS.md header)
#   bash scripts/verify.sh            ram_guard + build + checks.sh + DoneTest + ConeReport + report
#
# DG.2: the progress report is scripts/Report.lean (the whole-tree sweeps: cone_report, exhibits,
# block_coverage, axiom_sweep, sorry_sweep, closure_fingerprint). The sorry register in checks.sh reads
# its SORRY lines through scripts/sorries.sh --env, so the gate and the report are the same scan.
#
# DG.1: the axiom half of DONE is ASSERTED inside ConeReport.lean by three #assert_axioms commands, and
# the two lines cone_report() now requires below are what stop that gate from being deleted in silence.
# The gate's own self-test (scripts/DoneTest.lean) runs in both modes: a gate nobody runs is a gate that
# rots.
# Non-zero exit on ANY failure. `set -euo pipefail` makes every step fatal, and the ConeReport
# output is additionally scanned: a cone violation is reported by `#cone_avoids` as a Lean error
# (so lean already exits non-zero), but the phrases below are matched directly too, so a future
# wrapper that swallows an exit code cannot turn a red cone green.
set -euo pipefail
cd "$(dirname "$0")/.."

# ConeReport is a Lean file whose #imports_avoid / #cone_avoids / #cone_sorries commands log their
# verdicts as `info` messages. `lake env lean` re-elaborates it, so the lines print even when the
# build is cached and `lake build` would say nothing at all.
# D-P74 item 3 re-keys the progress root to Midfall.LoweringV3.lowering_correct. That declaration
# cannot be elaborated inside ConeReport.lean: ConeReport's own #imports_avoid gate reddens on
# Midfall.Lowering.Accumulator, which LoweringV3/Widening.lean imports. So the V3 root's cone and its
# axiom gate are printed by LoweringV3/GeneratorTheorem.lean, and cone_report runs BOTH files and
# scans the joined output - the V2 cone checks stay, the assert they carried moves to the V3 root.
cone_report() {
  local out
  if ! out=$( { lake env lean Midfall/Tools/ConeReport.lean 2>&1; \
                lake env lean Midfall/LoweringV3/GeneratorTheorem.lean 2>&1; } ); then
    printf '%s\n' "$out"
    echo 'verify.sh: ConeReport / GeneratorTheorem failed (lean exited non-zero)' >&2
    return 1
  fi
  if printf '%s\n' "$out" | grep -Eq 'imports_avoid: imports|: touches '; then
    printf '%s\n' "$out"
    echo 'verify.sh: ConeReport reported a cone violation' >&2
    return 1
  fi
  # The axiom half of DONE is ASSERTED by `#assert_axioms` - in ConeReport.lean for the retired V2
  # headline and in LoweringV3/GeneratorTheorem.lean for the V3 root (review J-1, G-9); this requires
  # the assertion to still be THERE, so deleting the line cannot turn it green. The V3 root's
  # assertion is the one with an EMPTY native list (D-P71's own gate).
  local want
  for want in 'imports_avoid: ok' \
      'assert_axioms Midfall.LoweringV3.lowering_correct: ok' \
      'assert_axioms Midfall.LoweringV3.lowering_sound: ok'; do
    if ! printf '%s\n' "$out" | grep -Fq "$want"; then
      printf '%s\n' "$out"
      echo "verify.sh: ConeReport did not print '$want'" >&2
      return 1
    fi
  done
  printf '%s\n' "$out"
}

# The progress report: tool output only. STATUS.md opens with it, verbatim (W8, card DG.8). The
# `SORRY ` and `DECL ` rows are the machine-readable feeds (SORRY.md, Closure.manifest) and are
# filtered out here: what prints is the report a human reads.
progress_report() {
  local out
  if ! out=$(lake env lean scripts/Report.lean 2>&1); then
    printf '%s\n' "$out"
    echo 'verify.sh: scripts/Report.lean failed' >&2
    return 1
  fi
  printf '%s\n' "$out" | grep -Ev '^(SORRY|DECL|  opaque) '
}

case "${1:-}" in
  --quick)
    lake build
    lake env lean scripts/DoneTest.lean
    cone_report
    ;;
  --report)
    cone_report
    progress_report
    ;;
  '')
    # --proc-limit is the shape that matters here: a cold parallel `lake build` legitimately sums
    # past 16 GiB across ten workers while no single worker passes 4.3 GiB (D-P31), so a budget on
    # the SUM alone would kill an honest build. The guard kills if EITHER is crossed.
    bash scripts/ram_guard.sh --limit 12G --proc-limit 6G -- lake build
    bash scripts/checks.sh
    lake env lean scripts/DoneTest.lean
    cone_report
    progress_report
    ;;
  *)
    echo "verify.sh: unknown argument '$1' (expected --quick, --report or nothing)" >&2
    exit 2
    ;;
esac

echo "verify.sh: ok (${1:-full})"

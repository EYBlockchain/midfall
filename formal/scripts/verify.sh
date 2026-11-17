#!/usr/bin/env bash
# verify.sh - ONE command that verifies a V2 ticket (PLAN-V2 §6, card Q0.3).
#
#   bash scripts/verify.sh --quick    build + DoneTest + ConeReport          (inner loop)
#   bash scripts/verify.sh            ram_guard + build + checks.sh + DoneTest + ConeReport
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
cone_report() {
  local out
  if ! out=$(lake env lean Midfall/Tools/ConeReport.lean 2>&1); then
    printf '%s\n' "$out"
    echo 'verify.sh: ConeReport failed (lean exited non-zero)' >&2
    return 1
  fi
  if printf '%s\n' "$out" | grep -Eq 'imports_avoid: imports|: touches '; then
    printf '%s\n' "$out"
    echo 'verify.sh: ConeReport reported a cone violation' >&2
    return 1
  fi
  # The axiom half of DONE is ASSERTED by `#assert_axioms` in ConeReport.lean (review J-1, G-9);
  # this requires the assertion to still be THERE, so deleting the line cannot turn it green.
  local want
  for want in 'imports_avoid: ok' \
      'assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: ok'; do
    if ! printf '%s\n' "$out" | grep -Fq "$want"; then
      printf '%s\n' "$out"
      echo "verify.sh: ConeReport did not print '$want'" >&2
      return 1
    fi
  done
  printf '%s\n' "$out"
}

case "${1:-}" in
  --quick)
    lake build
    lake env lean scripts/DoneTest.lean
    cone_report
    ;;
  '')
    # --proc-limit is the shape that matters here: a cold parallel `lake build` legitimately sums
    # past 16 GiB across ten workers while no single worker passes 4.3 GiB (D-P31), so a budget on
    # the SUM alone would kill an honest build. The guard kills if EITHER is crossed.
    bash scripts/ram_guard.sh --limit 12G --proc-limit 6G -- lake build
    bash scripts/checks.sh
    lake env lean scripts/DoneTest.lean
    cone_report
    ;;
  *)
    echo "verify.sh: unknown argument '$1' (expected --quick or nothing)" >&2
    exit 2
    ;;
esac

echo "verify.sh: ok (${1:-full})"

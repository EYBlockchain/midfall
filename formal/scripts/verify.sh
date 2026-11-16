#!/usr/bin/env bash
# verify.sh - ONE command that verifies a V2 ticket (PLAN-V2 §6, card Q0.3).
#
#   bash scripts/verify.sh --quick    build + ConeReport                    (inner loop)
#   bash scripts/verify.sh            ram_guard + build + checks.sh + ConeReport
#
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
  printf '%s\n' "$out"
}

case "${1:-}" in
  --quick)
    lake build
    cone_report
    ;;
  '')
    # --proc-limit is the shape that matters here: a cold parallel `lake build` legitimately sums
    # past 16 GiB across ten workers while no single worker passes 4.3 GiB (D-P31), so a budget on
    # the SUM alone would kill an honest build. The guard kills if EITHER is crossed.
    bash scripts/ram_guard.sh --limit 12G --proc-limit 6G -- lake build
    bash scripts/checks.sh
    cone_report
    ;;
  *)
    echo "verify.sh: unknown argument '$1' (expected --quick or nothing)" >&2
    exit 2
    ;;
esac

echo "verify.sh: ok (${1:-full})"

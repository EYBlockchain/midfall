#!/usr/bin/env bash
# check.sh - typecheck the PLAN-V3 evidence against the BUILT tree. Run from formal/:
#
#     bash docs/plans/V3-evidence/check.sh            # everything (about 6 minutes)
#     bash docs/plans/V3-evidence/check.sh statements # one area
#
# Nothing is written into the repository: compiled interfaces go to a temporary directory
# (override with V3_OUT=<dir>). `lake build` must have run first; this script never builds.
# One Lean process at a time. Exit status is non-zero if any file fails to elaborate.
set -uo pipefail
cd "$(dirname "$0")/../../.."
E=docs/plans/V3-evidence
OUT="${V3_OUT:-$(mktemp -d)}"
mkdir -p "$OUT"
BASE_LP="$(lake env printenv LEAN_PATH)"
fail=0

# area <dir> <file>...  : files in dependency order; each may import the earlier ones.
area() {
  local dir="$1"; shift
  mkdir -p "$OUT/$dir"
  for f in "$@"; do
    local src="$E/lean/$dir/$f.lean" log="$OUT/$dir/$f.log" t0=$SECONDS
    if LEAN_PATH="$BASE_LP:$OUT/$dir" lake env lean --root="$E/lean/$dir" \
        -o "$OUT/$dir/$f.olean" "$src" > "$log" 2>&1; then
      printf 'ok    %-34s %3ss  (%s sorry warnings)\n' "$dir/$f" "$((SECONDS-t0))" \
        "$(grep -c "declaration uses .sorry." "$log" || true)"
    else
      printf 'FAIL  %-34s %3ss  see %s\n' "$dir/$f" "$((SECONDS-t0))" "$log"; fail=1
    fi
  done
}

want="${1:-all}"
run() { [ "$want" = all ] || [ "$want" = "$1" ]; }

# The review's own machine-checked findings (self-checking: no output means every fact holds).
if run probes; then
  if lake env lean "$E/ReviewProbes.lean" > "$OUT/ReviewProbes.log" 2>&1 && [ ! -s "$OUT/ReviewProbes.log" ]; then
    echo 'ok    ReviewProbes'
  else echo "FAIL  ReviewProbes  see $OUT/ReviewProbes.log"; fail=1; fi
fi
run statements && area statements StatementsV3 StatementsV3Deploy StatementsV3Falsifiers
run soundness  && area soundness  SoundnessV3 RawDecode ExitMeasure PointSets
run prooftech  && area prooftech  P1_Exec WP Lits WPBridge WPTac TR VK LAGP WPX E3
run reference  && area reference  D1_Grouping D2_Rotation RefModel RunLib RunABC RunD RunE RunF RunG \
                                  D4_CodecKats D5_KeyData D6_Render
run object     && area object     Cov1 Parse1 Plan1 Plan2 Consts2 ObjectV3Full Quot1 Key1
run tooling    && area tooling    Done T1 T7
echo "logs and outputs: $OUT"
exit $fail

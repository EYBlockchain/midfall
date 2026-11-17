#!/usr/bin/env bash
# check.sh - typecheck the PLAN-V3 evidence against the BUILT tree. Run from formal/:
#
#     bash docs/plans/V3-evidence/check.sh            # everything (about 6 minutes)
#     bash docs/plans/V3-evidence/check.sh statements # one area
#   areas: probes statements soundness prooftech reference object tooling widening
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
    if LEAN_PATH="$BASE_LP:$OUT/$dir${EXTRA_LP:-}" lake env lean --root="$E/lean/$dir" \
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
run statements && area statements StatementsV3 StatementsV3Deploy StatementsV3Falsifiers GeneratorTheorem
run soundness  && area soundness  SoundnessV3 RawDecode ExitMeasure PointSets
# D-P71: the block rows for every render. Imports StatementsV3 across areas.
if run soundness; then
  [ -f "$OUT/statements/StatementsV3.olean" ] || area statements StatementsV3
  EXTRA_LP=":$OUT/statements" area soundness GeneratorRows GeneratorRowsWitness
fi
run prooftech  && area prooftech  P1_Exec WP Lits WPBridge WPTac TR VK LAGP WPX E3 VKP LoopRule
run reference  && area reference  D1_Grouping D2_Rotation RefModel RunLib RunABC RunD RunE RunF RunG \
                                  D4_CodecKats D5_KeyData D6_Render
run object     && area object     Cov1 Parse1 Plan1 Plan2 Consts2 ObjectV3Full Quot1 Key1
# D-P73: the certified generator. Imports StatementsV3 and GeneratorTheorem across areas.
if run object; then
  [ -f "$OUT/statements/StatementsV3.olean" ]     || area statements StatementsV3
  [ -f "$OUT/statements/StatementsV3Falsifiers.olean" ] || area statements StatementsV3Falsifiers
  [ -f "$OUT/statements/GeneratorTheorem.olean" ] || area statements GeneratorTheorem
  EXTRA_LP=":$OUT/statements" area object GeneratorCertified CertMeasure
fi
run tooling    && area tooling    Done T1 T7
# D-P72: the class widening (accumulator mode, external evaluator). Imports StatementsV3 and
# SoundnessV3 across areas, so their interfaces are compiled first if this area runs alone.
if run widening; then
  [ -f "$OUT/statements/StatementsV3.olean" ] || area statements StatementsV3
  [ -f "$OUT/soundness/SoundnessV3.olean" ]   || area soundness  SoundnessV3
  EXTRA_LP=":$OUT/statements:$OUT/soundness" area widening WideningV3 WideningStages WideningTests IvcPartials
fi
echo "logs and outputs: $OUT"
exit $fail

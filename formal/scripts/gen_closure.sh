#!/usr/bin/env bash
# gen_closure.sh - regenerate the closure pin of the frozen statements (DG.3).
#
# WHY. Frozen.sha256 pins the TEXT of the frozen files. What the frozen statements MEAN also
# depends on every definition they reach outside them (`permissive`, the run relation, the
# vendored dialect, the decoder); none of that was pinned (review J-6), so an edit there could
# change the truth of a frozen statement with every hash still green.
#
# WHAT IS PINNED (signed: D-GATE4, 2026-11-22, orchestrator). The closure of the five frozen
# statements, exactly as `#closure_fingerprint` in scripts/Report.lean computes it:
#   Midfall.LoweringV2.LoweringEquivalence, Render.Valid, HypothesesInhabited,
#   EndToEnd, EntryFrameInhabited   under [Midfall, YulSemantics]
# at this commit 4823 declarations / 526 external leaves / digest bd27cd298a04fc1a. The card's
# 972 is the retired zone ESTIMATE; the closure is what the statements actually reach.
#
# WHAT IS NOT PINNED. The generator, verifier and Instances trees are NOT added as zone roots:
# a declaration there is pinned only when a frozen statement reaches it, so an EMIT ticket is
# not forced through this pin merely because it touched those trees. (The closure of the five
# statements does reach generator/verifier declarations; that reach is the point of a closure
# pin and is signed.)
#
# HOW THE GATE USES IT. checks.sh runs `--print` and diffs the result against
# Midfall/LoweringV2/Closure.manifest. A changed type or body changes that declaration's DECL
# line and the summary digest, so the gate's diff NAMES the definition. The manifest's sha256
# is one more line of Midfall/LoweringV2/Frozen.sha256, so regenerating it without a re-hash
# is also red. A deliberate change needs the new manifest, a new Frozen.sha256 line and a
# sign-off (W2).
#
# Usage: bash scripts/gen_closure.sh            write Midfall/LoweringV2/Closure.manifest
#        bash scripts/gen_closure.sh --print    print it (the gate's side)
set -euo pipefail
cd "$(dirname "$0")/.."

# Report.lean belongs to DG.2 and carries the single #closure_fingerprint command; running it
# here keeps one source of truth for the roots. It exits non-zero if any of its gates fail.
if ! out=$(lake env lean scripts/Report.lean 2>&1); then
  printf '%s\n' "$out" >&2
  echo 'gen_closure.sh: scripts/Report.lean failed' >&2
  exit 1
fi

# The summary line is the LAST line of the multi-line #closure_fingerprint header. Keep its
# count and digest in the manifest: an external leaf added or removed moves the digest without
# moving a DECL row, and that is a dependency change worth a gate.
summary=$(printf '%s\n' "$out" |
  sed -nE 's/^.*\]: ([0-9]+ project declarations, [0-9]+ external leaves, digest [0-9a-f]+)$/\1/p')
if [ -z "$summary" ]; then
  echo 'gen_closure.sh: no closure_fingerprint summary in scripts/Report.lean output' >&2
  printf '%s\n' "$out" | tail -20 >&2
  exit 1
fi

decls=$(printf '%s\n' "$out" | grep '^DECL ' | LC_ALL=C sort)
if [ -z "$decls" ]; then
  echo 'gen_closure.sh: no DECL rows in scripts/Report.lean output' >&2
  exit 1
fi

manifest=$(printf '# closure_fingerprint: %s\n%s\n' "$summary" "$decls")

if [ "${1:-}" = "--print" ]; then
  printf '%s\n' "$manifest"
else
  printf '%s\n' "$manifest" > Midfall/LoweringV2/Closure.manifest
  echo "gen_closure.sh: wrote $(printf '%s\n' "$decls" | grep -c .) declarations ($summary)" >&2
fi

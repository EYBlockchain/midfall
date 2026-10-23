#!/usr/bin/env bash
# Phase 1 exit gates (plan Section 3): frozen statements hash, sorry register,
# native_decide confinement, executable known-answer tests, axiom probe.
set -euo pipefail
cd "$(dirname "$0")/.."

echo '== frozen statements hash =='
sha256sum -c Midfall/Statements.sha256

echo '== sorry register =='
found=$(grep -rn --include='*.lean' -w sorry Midfall \
  | grep -v 'Midfall/Probe/' \
  | sed -E 's/^([^:]+):([0-9]+):.*/\1:\2/' | sort)
listed=$(sed -nE 's/^\| ([^ |]+) \| ([0-9]+) \|.*/\1:\2/p' SORRY.md | sort)
if [ "$found" != "$listed" ]; then
  echo 'sorry register out of sync with the tree'
  diff <(echo "$listed") <(echo "$found") || true
  exit 1
fi
echo "ok: $(echo "$found" | wc -l | tr -d ' ') tracked sorries"

echo '== native_decide confinement =='
bad=$(grep -rn --include='*.lean' native_decide Midfall | grep -v 'Midfall/Instances/' || true)
if [ -n "$bad" ]; then echo 'native_decide outside Instances/:'; echo "$bad"; exit 1; fi

echo '== known-answer tests =='
printf 'import Midfall.Common.Keccak\n#eval Midfall.keccak256_kats_ok\n#eval Midfall.abiSelectors_ok\n' > /tmp/midfall-kats.lean
out=$(lake env lean /tmp/midfall-kats.lean)
[ "$out" = "$(printf 'true\ntrue')" ] || { echo "KAT failure: $out"; exit 1; }
echo 'ok: keccak256 digest plus 8 ABI-selector cross-checks against the Rust-pinned constants'

echo '== axioms of the frozen statements =='
printf 'import Midfall.Statements\n#print axioms Midfall.Statements.verifyNative_iff_msgs\n#print axioms Midfall.Statements.verifyMsgs_iff_spec\n' > /tmp/midfall-ax.lean
lake env lean /tmp/midfall-ax.lean

#!/usr/bin/env bash
# Phase 1 exit gates (plan Section 3): frozen statements hash, sorry register,
# native_decide confinement, executable known-answer tests, axiom probe.
set -euo pipefail
cd "$(dirname "$0")/.."

echo '== frozen statements hash =='
sha256sum -c Midfall/Statements.sha256

echo '== sorry register =='
# The inventory comes from scripts/sorries.sh, which is also what generates the
# register table (scripts/gen_sorry.sh), so gate and register cannot drift apart.
found=$(bash scripts/sorries.sh)
listed=$(sed -nE 's/^\| ([^ |]+) \| ([0-9]+) \|.*/\1:\2/p' SORRY.md | sort)
if [ "$found" != "$listed" ]; then
  echo 'sorry register out of sync with the tree'
  diff <(echo "$listed") <(echo "$found") || true
  exit 1
fi
echo "ok: $(echo "$found" | wc -l | tr -d ' ') tracked sorries"

echo '== native_decide confinement =='
# scripts/lean_grep.py strips comments first, so prose that mentions the tactic
# (there is such a doc string in Security/Challenges.lean) is not a use of it.
bad=$(python3 scripts/lean_grep.py '\bnative_decide\b' \
  $(find Midfall -name '*.lean' | sort) | grep -v 'Midfall/Instances/' || true)
if [ -n "$bad" ]; then echo 'native_decide outside Instances/:'; echo "$bad"; exit 1; fi

echo '== known-answer tests =='
printf 'import Midfall.Common.Keccak\n#eval Midfall.keccak256_kats_ok\n#eval Midfall.abiSelectors_ok\n' > /tmp/midfall-kats.lean
out=$(lake env lean /tmp/midfall-kats.lean)
[ "$out" = "$(printf 'true\ntrue')" ] || { echo "KAT failure: $out"; exit 1; }
echo 'ok: keccak256 digest plus 8 ABI-selector cross-checks against the Rust-pinned constants'

echo '== axioms of the frozen statements =='
printf 'import Midfall.Statements\n#print axioms Midfall.Statements.verifyNative_iff_msgs\n#print axioms Midfall.Statements.verifyMsgs_iff_spec\n' > /tmp/midfall-ax.lean
lake env lean /tmp/midfall-ax.lean

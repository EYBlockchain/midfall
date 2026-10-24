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
# Every `#eval` in the tree is a KAT gate, not documentation. Before this change
# checks.sh asserted six hand-picked booleans, so the R-30 and R-32 regression
# tests - written precisely because those bugs survived sign-off - would NOT have
# failed CI if they regressed: a false #eval prints as an `info:` line and
# `lake build` still exits 0. Now the script harvests every qualified `#eval`
# expression from the sources, evaluates them in one pass and requires each to
# print `true`. Self-maintaining: adding a KAT adds a gate automatically.
# Every '#eval ... -- expect <value>' in the tree is a gate. See
# scripts/kat_gate.py for why: before this, checks.sh asserted six hand-picked
# booleans, so the R-30 and R-32 regression tests would not have failed CI if
# they regressed. Negative controls ('-- expect false') pass by returning false.
python3 scripts/kat_gate.py || exit 1
echo '== axioms of the frozen statements =='
printf 'import Midfall.Statements\n#print axioms Midfall.Statements.verifyNative_iff_msgs\n#print axioms Midfall.Statements.verifyMsgs_iff_spec\n' > /tmp/midfall-ax.lean
lake env lean /tmp/midfall-ax.lean
 | head -20
  exit 1
fi
echo "ok: all $ntrue known-answer checks in the tree evaluate to true"

echo '== axioms of the frozen statements =='
printf 'import Midfall.Statements\n#print axioms Midfall.Statements.verifyNative_iff_msgs\n#print axioms Midfall.Statements.verifyMsgs_iff_spec\n' > /tmp/midfall-ax.lean
lake env lean /tmp/midfall-ax.lean

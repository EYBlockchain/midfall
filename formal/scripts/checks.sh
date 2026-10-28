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
listed=$(sed -nE 's/^\| ([^ |]+) \| ([0-9]+) \|.*/\1:\2/p' SORRY.md | sort -t: -k1,1 -k2,2n)
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
echo '== module reachability =='
# kat_gate.py walks the filesystem, so an unimported module can pass its #eval gates
# while lake build never compiles it. Two had slipped through (R-50). This makes an
# orphan a hard failure.
python3 scripts/check_orphans.py || exit 1

if [ -n "$bad" ]; then echo 'native_decide outside Instances/:'; echo "$bad"; exit 1; fi

echo '== golden fixture provenance =='
# The Phase 6 golden gates compare an AST against a pinned string; nothing in Lean
# opens the .sol. This is the only thing that ties those pins to the artifact, so
# it is a hard gate: if the dump is regenerated or edited and YulGolden.lean is
# not, CI fails. See docs/REVIEW.md R-38.
python3 scripts/check_golden_provenance.py || exit 1

echo '== Instances/ import confinement =='
# A Generator or Exec file may import a model from Midfall/Instances/ to run a #eval
# gate (Vk.lean does, for the only runnable AdmissiblePairing). What must never happen
# is a THEOREM living in a file that imports a concrete model: the import cannot pollute
# axioms by itself, but a proof stated next to the KATs would silently acquire a
# dependence on the model. The rule is therefore scoped to files that state proofs, not
# to files that compute. See docs/design.md D-P17.
bad=""
for f in $(find Midfall -name '*.lean' -not -path 'Midfall/Instances/*'); do
  if grep -q '^import Midfall\.Instances\.' "$f" && grep -qE '^(theorem|lemma) ' "$f"; then
    bad="$bad $f"
  fi
done
if [ -n "$bad" ]; then
  echo 'files stating theorems while importing Instances/:'
  for f in $bad; do echo "  $f"; done
  exit 1
fi
echo 'ok: no theorem-bearing file imports Midfall/Instances/'

echo '== known-answer tests =='
# Every '#eval ... -- expect <value>' in the tree is a gate. See
# scripts/kat_gate.py for why: before this, checks.sh asserted six hand-picked
# booleans, so the R-30 and R-32 regression tests would not have failed CI if
# they regressed. Negative controls ('-- expect false') pass by returning false.
python3 scripts/kat_gate.py || exit 1

echo '== LoweringCorrect statement fingerprints =='
# Obligations.lean's fields are statements, not gated computations, so no #eval gate
# reads their text. Three paraphrases (ZeroAbove -> True, stmtsBeq -> a length equality,
# dropping the selector conjunct) all built clean with every gate green. This is the only
# automated defence against weakening a headline statement silently.
python3 scripts/check_statement_fingerprints.py || exit 1
echo '== duplicated-fact pins =='
# R-58's root cause: PlanView, Surface, LoweringPlan and GeneratorConfig each carry a
# COPY of a fact the Rust derives once - hasAccumulator, numInstances, the evaluator,
# encG2, the quotient/direct pair, the shell program - and a copy with no pin between
# the two sides is a free variable the reviewer demonstrated discharging 11 of 13
# PartialSpecs fields on a one-Bool lie. This gate asserts each such fact is either
# single-copy or has a named pin field mentioning BOTH sides, and that the carriers
# themselves have not been renamed or deleted. It is a dependency-structure gate: the
# fingerprint gate above pins text fragments and demonstrably let F1, F7 and F8
# through, and neither gate is a meaning check - only a proof is one.
python3 scripts/check_duplicate_facts.py || exit 1

echo '== axioms of the frozen statements =='
printf 'import Midfall.Statements\n#print axioms Midfall.Statements.verifyNative_iff_msgs\n#print axioms Midfall.Statements.verifyMsgs_iff_spec\n' > /tmp/midfall-ax.lean
lake env lean /tmp/midfall-ax.lean


#!/usr/bin/env bash
# Phase 1 exit gates (plan Section 3): frozen statements hash, sorry register,
# native_decide confinement, executable known-answer tests, axiom probe.
set -euo pipefail
cd "$(dirname "$0")/.."

echo '== memory headroom (report only, D-P31) =='
# A REPORT, NOT A GATE. This host has been taken down twice by a lean process: 8.7 GB
# peak RSS killed a session, and a per-unit native_decide reached 16.8 GB with swap past
# 50 GB. Those numbers used to live only as comments in Midfall/Lowering/RunEmitted.lean,
# so nothing carried them to the next package. This line makes headroom visible on every
# gate run, so drift shows up before it is fatal.
#
# It cannot fail the build, and that is deliberate: a memory report that reddens a green
# tree teaches people to delete the report. ram_guard.sh exits 0 whatever it finds, and
# the || true below covers even a broken guard. The budget that CAN kill is applied by
# whoever wraps a run: scripts/ram_guard.sh --limit 6G -- lake build.
#
# Scope is THIS process tree, never every process named lean: an earlier watchdog summed
# all lean and charged this session for two unrelated ones already running on the host.
# Measured cost of this section: 0.07 s per call (5 calls in 0.349 s), on a gate run
# that takes 450-480 s: unmeasurable. checks.sh went 480 s before this line and
# 451 s after it, and it still exits 0 (D-P31).
bash scripts/ram_guard.sh --quiet --limit 6G --warn 4G || true
echo '== frozen statements hash =='
sha256sum -c Midfall/Statements.sha256
sha256sum -c Midfall/LoweringV2/Frozen.sha256

echo '== frozen statement closure =='
# Frozen.sha256 pins the TEXT of the frozen files; what the statements MEAN also depends on every
# definition they reach outside them (`permissive`, the run relation, the vendored dialect,
# `decodeCalldata`), none of which was pinned (review J-6). Closure.manifest lists those
# declarations with a hash of type and body; its sha256 is a line of Frozen.sha256, and here it
# is recomputed, so a change is a diff that NAMES the definition.
#
# The roots are the five frozen statements and the zone is their closure, signed as D-GATE4
# (2026-11-22). The generator, verifier and Instances trees are NOT zone roots: a declaration
# there is listed only where a frozen statement reaches it (STATUS.md section 4 item 1).
if ! moved=$(diff <(bash scripts/gen_closure.sh --print) Midfall/LoweringV2/Closure.manifest); then
  echo 'the closure of the frozen statements changed (< tree, > manifest):'
  printf '%s\n' "$moved" | head -20
  echo 'a deliberate change needs gen_closure.sh, a new Frozen.sha256 line and a sign-off (W2)'
  exit 1
fi
echo "ok: $(grep -c '^DECL ' Midfall/LoweringV2/Closure.manifest) pinned declarations"

echo '== sorry register =='
# KEYED BY DECLARATION, READ FROM THE ENVIRONMENT (scripts/sorries.sh --env, which runs #sorry_sweep
# in scripts/Report.lean). The old file:line key reddened on an unrelated edit (2041977 moved
# PoseidonValid.lean 227 -> 252 and the tip stayed red, review J-8), said nothing about WHICH
# declaration was open (review J-10), and could not see a hole with no `sorry` token - `admit`, `stop`,
# a macro, a direct `sorryAx` (review J-2). The sweep reads elaborated terms, so all four are seen, and
# each row also carries the declaration's STATUS (OPEN / REFUTED / VACUOUS), whether it sits in the
# headline cone (ROOT), and a structural hash of its statement: a restated sorry moves its hash.
found=$(bash scripts/sorries.sh --env)
# The six pinned columns of every table row, in the same LC_ALL=C order the scan prints them in.
listed=$(sed -nE 's/^\| ([^ |]+) \| ([^ |]+) \| ([^ |]+) \| ([^ |]+) \| ([^ |]+) \| `([0-9a-f]{16})` \|.*/\1 \2 \3 \4 \5 \6/p' SORRY.md | LC_ALL=C sort)
if [ "$found" != "$listed" ]; then
  echo 'sorry register out of sync with the tree (< register, > tree): run scripts/gen_sorry.sh'
  diff <(echo "$listed") <(echo "$found") || true
  exit 1
fi
# CROSS-CHECK with the text scan: both must find sorries in the same MODULES (measured at 3a7c017:
# 19 = 19, and the per-module counts agree at 58 = 58). Text only: a `sorry` the build never
# elaborates. Environment only: a hole with no `sorry` token. Either disagreement is a real finding,
# not noise, so it is a hard failure.
textmods=$(bash scripts/sorries.sh | cut -d: -f1 | sed -e 's/\.lean$//' -e 's#/#.#g' | sort -u)
envmods=$(echo "$found" | awk '{print $2}' | sort -u)
if [ "$textmods" != "$envmods" ]; then
  echo 'text scan and environment scan disagree on the modules holding a sorry (< text, > environment):'
  diff <(echo "$textmods") <(echo "$envmods") || true
  exit 1
fi
# A hole in the headline cone must name the card that removes it (review I-10). gen_sorry.sh keys
# owners by declaration name, so a renamed cone sorry arrives UNOWNED and reddens this on purpose.
if grep -E '^\| [^|]+ \| [^|]+ \| [^|]+ \| [^|]+ \| ROOT \| [^|]+ \| UNOWNED' SORRY.md; then
  echo 'a sorry in the headline cone has no card (review I-10)'
  exit 1
fi
echo "ok: $(echo "$found" | grep -c .) sorried declarations, $(echo "$found" | grep -c ' ROOT ') in the headline cone, $(echo "$found" | grep -c ' REFUTED ') REFUTED"

echo '== native_decide confinement =='
# scripts/lean_grep.py strips comments first, so prose that mentions the tactic
# (there is such a doc string in Security/Challenges.lean) is not a use of it.
# ONE FILE IS EXEMPT, BY NAME - DG.1's exemption, KEPT by DG.2: Midfall/Tools/Done.lean is the tool
# that IMPLEMENTS this rule and the axiom sweep, so it carries the token as DATA - the generated-axiom
# name shape it matches on (`_native.native_decide.ax_*`), the tactic name it compares against, the
# strings it prints - in 9 places. lean_grep.py strips comments but not string literals, so those read
# as uses. A native_decide in a PROOF anywhere else under Midfall/ is still red, and the exemption is
# a filename, not a directory, so a new tool that needs it must say so here. The exemption is applied
# BEFORE the count below, so the number printed is uses of the tactic and not mentions of the word.
# The environment half of this rule is `#axiom_sweep` in scripts/Report.lean - already run by
# `sorries.sh --env` above - which ERRORS on any project axiom that is neither a D-P36a constant nor a
# native_decide axiom generated inside a declaration of a Midfall.Instances module, and reads the
# kernel rather than the text, so no exemption is needed there.
# The scanner's exit status is taken on its OWN line: `scan | grep -v ... || true` also swallowed a
# CRASH of the scanner and left the gate green (review J-12). `decide +native` generates the same
# axiom, so it is the same violation (control G: the old regex found 0 hits for it).
uses=$(python3 scripts/lean_grep.py '\bnative_decide\b|\bdecide\s*\+native\b' \
  $(find Midfall -name '*.lean' | sort))
scanned=$(printf '%s\n' "$uses" | grep -v '^Midfall/Tools/Done.lean:' || true)
bad=$(printf '%s\n' "$scanned" | grep -v '^Midfall/Instances/' | grep . || true)
if [ -n "$bad" ]; then echo 'native_decide outside Instances/:'; echo "$bad"; exit 1; fi
echo "ok: $(printf '%s\n' "$scanned" | grep -c .) uses, all under Midfall/Instances/"

echo '== module reachability =='
# kat_gate.py walks the filesystem, so an unimported module can pass its #eval gates
# while lake build never compiles it. Two had slipped through (R-50). This makes an
# orphan a hard failure.
python3 scripts/check_orphans.py || exit 1

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

echo '== headline hypothesis bundles =='
# R-60 S1: a hypothesis bundle can be individually inhabited and JOINTLY empty. Gate 6
# checked RunContractIR alone and stayed green while the fixture's irCheck was false of
# the very object the run was about, so every multi-hypothesis headline conjunction now
# needs either a JOINT exhibit - one Lean declaration naming every conjunct - or a named
# gap def saying which conjunct blocks it. A new multi-hypothesis field that nobody
# registered reddens this gate, which is the discovery half.
python3 scripts/check_hypothesis_bundles.py || exit 1

echo '== baseline SHA pins (tracked vs untracked) =='
python3 ../proofs/solidity-verifier/scripts/check_baseline_pins.py || exit 1

echo '== axioms of the frozen statements =='
# A GATE, NOT A PRINT (P-STATGATE). This section used to be two lines that printed three
# axiom sets and exited 0 whatever they said: it printed sorryAx three times and stayed
# green, which is a report wearing a gate's clothes. scripts/check_frozen_axioms.py now
# reads the declaration list FROM the frozen file - so a fourth statement cannot arrive
# unprobed, which the old hand-written probe could not see either - runs the same
# '#print axioms', and requires each axiom set to be EXACTLY propext, sorryAx,
# Classical.choice, Quot.sound. sorryAx is EXPECTED: these are spec statements, not
# proofs, and D-P27 kept all three 'sorry' deliberately, so a gate that failed on sorryAx
# would be red on every honest version of this file and would be deleted inside a week.
# What the rule is about is SHAPE: native_decide and Lean.ofReduceBool are named and
# rejected, and so is a statement that LOSES sorryAx, because filling a frozen hole needs
# a re-pin, a SORRY.md change and a decision - not a silent edit that looks like progress.
python3 scripts/check_frozen_axioms.py || exit 1


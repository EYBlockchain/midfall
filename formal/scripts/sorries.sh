#!/usr/bin/env bash
# The canonical sorry inventory, in two modes.
#
#   bash scripts/sorries.sh          TEXT scan: one "<file>:<line>" per real proof hole, sorted.
#   bash scripts/sorries.sh --env    ENVIRONMENT scan: one row per sorried DECLARATION.
#
# The environment scan is the register now (DG.2; reviews J-2, J-8, J-10). It runs `#sorry_sweep`
# from scripts/Report.lean, which reads the ELABORATED TERMS, so it is keyed by declaration NAME - an
# unrelated line shift no longer reddens the gate (2041977 moved PoseidonValid.lean 227 -> 252 and the
# tip stayed red for a day) - and it sees a hole with no `sorry` token: `admit`, `stop`, a direct
# `sorryAx`, or any macro that expands to one. Each row is
#   <declaration> <module> <kind> <OPEN|REFUTED|VACUOUS> <ROOT|-> <statement hash>
# which is exactly the first six columns of the table in SORRY.md, so the register (gen_sorry.sh) and
# the gate (checks.sh) read this one file and cannot drift apart.
#
# The text scan is KEPT as a cross-check: checks.sh requires both scans to name the same modules.
# Text-only finds a `sorry` the build never elaborates; environment-only finds a hole with no token.
#
# Matching goes through scripts/lean_grep.py, which strips comments first: a doc string that merely
# mentions the word is not a proof hole.
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "${1:-}" = "--env" ]; then
  # Report.lean's own verdicts are Lean errors, so they fail here: they are gates, not prints.
  if ! out=$(lake env lean scripts/Report.lean 2>&1); then
    printf '%s\n' "$out" >&2
    echo 'sorries.sh: scripts/Report.lean failed' >&2
    exit 1
  fi
  printf '%s\n' "$out" | sed -n 's/^SORRY //p' | LC_ALL=C sort
  exit 0
fi
# ONE FILE IS EXEMPT, BY NAME: Midfall/Tools/Done.lean is the axiom/sorry GATE TOOL, so the word
# `sorry` appears in it as DATA - inside the message strings it prints ("registered sorry
# statement(s)", :429) - and lean_grep.py strips comments but NOT string literals. The environment
# scan cannot be fooled by a string literal at all, so this exemption is only ever about the
# cross-check. It is a filename, not a directory: a new tool that needs it must say so here.
# Midfall/Probe/* is no longer skipped: Midfall.lean imports it (measured at 3a7c017: it holds no
# `sorry` token, so the cross-check is unaffected either way).
files=$(find Midfall -name '*.lean' -not -path 'Midfall/Tools/Done.lean' | sort)
# shellcheck-disable-next-line SC2086 - no whitespace in these paths
python3 scripts/lean_grep.py '\bsorry\b' $files | sort -t: -k1,1 -k2,2n

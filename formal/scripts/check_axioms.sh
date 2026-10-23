#!/usr/bin/env bash
# Every theorem listed in scripts/axioms.list must have an #print axioms result
# inside the trusted base (propext, Classical.choice, Quot.sound, plus the named
# hypotheses declared in Midfall/Assumptions/).
set -euo pipefail
cd "$(dirname "$0")/.."
test -f scripts/axioms.list || { echo 'no axioms.list yet'; exit 0; }
while read -r decl; do
  [ -n "$decl" ] || continue
  echo "#print axioms $decl" > /tmp/probe.lean
  lean /tmp/probe.lean
done < scripts/axioms.list

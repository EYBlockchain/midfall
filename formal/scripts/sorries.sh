#!/usr/bin/env bash
# The canonical sorry inventory: one "<file>:<line>" per real proof hole in the
# tree, in sorted order. Both scripts/checks.sh (gate) and scripts/gen_sorry.sh
# (register) read it through this file so the two can never disagree.
#
# Matching goes through scripts/lean_grep.py, which strips comments first: a
# doc string that merely mentions the word is not a proof hole.
set -euo pipefail
cd "$(dirname "$0")/.."
files=$(find Midfall -name '*.lean' -not -path 'Midfall/Probe/*' | sort)
# shellcheck-disable-next-line SC2086 - no whitespace in these paths
python3 scripts/lean_grep.py '\bsorry\b' $files | sort -t: -k1,1 -k2,2n

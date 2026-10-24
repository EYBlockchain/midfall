#!/usr/bin/env bash
# Regenerate the sorry register table in formal/SORRY.md from the tree.
#
# checks.sh compares the tree against this table, so run this whenever a sorry
# is added, removed, or shifted by an unrelated edit in the same file.
set -euo pipefail
cd "$(dirname "$0")/.."

# file -> "removed by" (plan Section 12: every sorry has an owning work package)
owner() {
  case "$1" in
    Midfall/Common/Codec.lean)        echo 'Phase 1 curve instance' ;;
    Midfall/Halo2/Exec/Native.lean)   echo 'BLOCKED: plan 9.2 arity lacks G1Codec/FieldConsts/delta - needs the D-P9 re-pin (see Midfall/Halo2/Exec/Native.lean header)' ;;
    Midfall/Halo2/Spec/Piop.lean)     echo 'Phase 4 (spec layer)' ;;
    Midfall/Halo2/Spec/Relation.lean) echo 'Phase 4 (spec layer)' ;;
    Midfall/Statements.lean)          echo 'frozen statements (S1..S7 land later)' ;;
    *)                                echo 'UNOWNED - assign a work package' ;;
  esac
}

BT='`'
table=$(while IFS=: read -r file line; do
      rest=$(sed -n "${line}p" "$file" | sed -E 's/^[[:space:]]*//; s/[[:space:]]*$//' | cut -c1-44)
      printf '| %s | %s | %s%s%s | %s |\n' "$file" "$line" "$BT" "$rest" "$BT" "$(owner "$file")"
    done < <(bash scripts/sorries.sh))

grep -q '^| file | line | declaration | removed by |$' SORRY.md || {
  echo 'gen_sorry.sh: SORRY.md has no table header row; restore it from git first' >&2
  exit 1
}
head=$(sed -n '1,/^| file | line |/p' SORRY.md)
tail=$(sed -n '/^## Upstream sorries/,$p' SORRY.md)
{
  printf '%s\n' "$head"
  printf '%s\n' "$table"
  printf '\n%s\n' "$tail"
} > SORRY.md.new
mv SORRY.md.new SORRY.md
printf '%s\n' "$table"

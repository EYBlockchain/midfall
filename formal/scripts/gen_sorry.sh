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
    Midfall/Halo2/Exec/Native.lean)   echo 'Phase 2: expose KZG read schedule and parameterise transcript hash (D-P9)' ;;
    Midfall/Halo2/Spec/Piop.lean)     echo 'Phase 4 (spec layer)' ;;
    Midfall/Halo2/Spec/Relation.lean) echo 'Phase 4 (spec layer)' ;;
    Midfall/Statements.lean)          echo 'frozen statements (S1..S7 land later)' ;;
    Midfall/Yul/*)                echo 'P-SE stage 1-2: Yul run/contracts layer (semantic equivalence)' ;;
    Midfall/Lowering/*)           echo 'P-SE: semantic equivalence obligations' ;;
    Midfall/Assumptions/*)        echo 'P-SE: named holes in assumption files' ;;
    Midfall/LoweringV2/Blocks/FinalPairing.lean) echo 'V2 (PLAN-V2): FP.0 FinalPairing skeleton - P.1 algebra, T.4 staticcall, T.5 steps' ;;
    Midfall/LoweringV2/*)         echo 'V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md' ;;
    Midfall/Instances/PoseidonV2.lean) echo 'V2 (PLAN-V2): C.1 headline lemmas - WP-M0 blocks, D.3 circuit gap' ;;
    Midfall/Instances/PoseidonValid.lean) echo 'V2 (PLAN-V2): C.4 Valid.model - no Inhabited Model, kernel cannot reduce poseidonModel' ;;
    *)                                echo 'UNOWNED - assign a work package' ;;
  esac
}

BT='`'
# The declaration column is cut at 44 CHARACTERS, and it has to be done in Python, not
# with `cut -c1-44`: on this host /usr/bin/cut is BSD cut, whose -c counts BYTES
# whenever LC_CTYPE is not a UTF-8 locale (LC_ALL=C is enough). Two rows carry
# non-ASCII characters - Midfall/Halo2/Spec/Piop.lean:67 (`G₁`) and
# Midfall/Statements.lean:123 (`Gₜ ... Gₜ`) - so under LC_ALL=C the byte cut landed
# one byte inside the last character and emitted `... := sorr` and `... keccak256 Feature`
# instead of the committed `... := sorry` and `... Features.s`. The register therefore
# rewrote itself differently depending on who ran it, which is how a table that is
# supposed to protect the sorry inventory ends up hiding a real hole under a mangled row.
# Python decodes UTF-8 explicitly and slices by codepoint, so the output is byte-identical
# in every locale (verified: regenerated under LC_ALL=C, C.UTF-8 and en_US.UTF-8 and
# diffed against the committed table).
table=$(while IFS=: read -r file line; do
      rest=$(sed -n "${line}p" "$file" | python3 -c 'import sys; sys.stdout.write(sys.stdin.buffer.read().decode("utf-8").strip()[:44])')
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

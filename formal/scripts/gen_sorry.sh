#!/usr/bin/env bash
# Regenerate the sorry register table in formal/SORRY.md from the tree.
#
# checks.sh compares the tree against this table, so run this whenever a sorry is added, removed, or
# restated. The table is NEVER hand-edited.
#
# KEYED BY DECLARATION, READ FROM THE ENVIRONMENT (DG.2). The inventory comes from
# `bash scripts/sorries.sh --env`, which runs `#sorry_sweep` in scripts/Report.lean: one row per
# user-facing declaration whose own type or value uses `sorryAx`, with its module, its kind, its
# status (OPEN / REFUTED / VACUOUS), whether it is in the headline cone (ROOT), and a structural hash
# of its statement. Four consequences worth knowing before editing this file:
#
#   * a line move is not a register change, so an unrelated edit in the same file cannot redden the
#     gate (the old file:line key did exactly that, twice: reviews J-8, J-2);
#   * a hole with no `sorry` token - `admit`, `stop`, a macro - is a row, because the scan reads the
#     elaborated term and not the text;
#   * a RESTATED sorry changes its statement hash, so it reads as a row whose `statement` column
#     moved: a paraphrase of a registered obligation is visible (review J-10);
#   * OWNERS ARE KEYED BY DECLARATION NAME. A renamed or moved sorry therefore reads as one REMOVED
#     and one ADDED, not as an edit: when you rename a registered declaration, carry its card ID to
#     the new name in the same commit, or the new row lands UNOWNED and - if it is in the headline
#     cone - reddens checks.sh on purpose.
#
# The old script sliced the source line to 44 CHARACTERS for the declaration column, in Python rather
# than `cut -c1-44` because BSD cut counts BYTES when LC_CTYPE is not UTF-8 and two rows carry
# non-ASCII identifiers (G1, Gt), which made the register rewrite itself differently depending on who
# ran it. Nothing is sliced from source text any more: the declaration column is a name the kernel
# printed, so the hazard is gone rather than worked around.
set -euo pipefail
cd "$(dirname "$0")/.."

# declaration -> "removed by". ROOT rows (the headline cone) name the PLAN-V3 card that takes them
# out of the cone; every other arm carries the owner the file:line register had, re-keyed by name.
owner() {
  case "$1" in
    # ---- the headline cone: one card ID per row (PLAN-V3 section 5, M0/M3/M5/M6/M7) ----
    Midfall.Instances.PoseidonV2.poseidon_valid)
      echo 'V3 PL.1 - deletes it: the negation poseidonRender_notValid is PROVED (REFUTED: as stated it proves False)' ;;
    Midfall.Instances.PoseidonV2.poseidon_quotient_block)
      echo 'V3 ROW.Q - the quotient row: the one block the generic hinge does not cover' ;;
    Midfall.Instances.PoseidonV2.poseidon_rejects)
      echo 'V3 PL.H via rejectsV3_of_rows - V2 C.3 staged rejection contracts' ;;
    Midfall.LoweringV2.blockContracts_of_valid)
      echo 'V3 SIM.7 - deletes the old composition (RV-10: false as stated until RECON.1 PayloadAgrees)' ;;
    Midfall.LoweringV2.bodyTotal_of_valid)
      echo 'V3 ST.5 - TotalV3: the totality conjunct D-P64 (f) lands with the four-obligation composition; discharged by the exit-discipline scan (ST.10/ST.12)' ;;
    Midfall.LoweringV2.noWriters_prog)
      echo 'V3 ST.12 - scans_prog_addr_indep removes it' ;;
    Midfall.LoweringV2.prefix_run_clean)
      echo 'V3 SIM.7 - deletes prefix_run_clean' ;;
    Midfall.LoweringV2.rejects_of_not_accepts)
      echo 'V3 ST.5 - deletes rejects_of_not_accepts' ;;
    Midfall.LoweringV2.runBody_iff_slices)
      echo 'V3 SIM.7 - deletes runBody_iff_slices' ;;
    Midfall.Yul.Bridge.Run_worldEq_of_noWriters)
      echo 'V3 SIM.5 - the shared Step induction (ST.10 cites it)' ;;
    # ---- ST.1: the four V3 staging obligations, landed in Midfall/LoweringV3/Statements.lean. ----
    # Each owner names the card that discharges it and the experiment its docstring gives.
    Midfall.LoweringV3.prog_slices_decompV3)
      echo 'V3 ST.11 - restated structural decomposition. Experiment: inline_append five times against noShadowB, List.filterMap_append for hoist, and hoist (preSlice) = hoist (mainLocalsInlined) = []' ;;
    Midfall.LoweringV3.twoOutcomes_of_exitDiscipline)
      echo 'V3 ST.10 - replaces rejects_of_not_accepts (WP-M5c). Experiment: one induction on Step in the shape of Bridge.Run_worldEq_of_noWriters (Bridge.lean:1221), then Step.stmts_append_inv at the tail and mstore/ret by simp [stepOp]' ;;
    Midfall.LoweringV3.scans_prog_addr_indep)
      echo 'V3 ST.12 - the two scans ignore the addresses the wrapper binds as let literals. Experiment: same cost class as noWriters_prog (Blocks.lean:340), which it subsumes' ;;
    Midfall.LoweringV3.runBody_mono)
      echo 'V3 ST.13 - monotonicity in the call relation (Bridge layer). Experiment: induction on Step; the call relation occurs only in externalCall (EVMExec.lean), in a positive position' ;;
# ---- T3.1b: the WPX statements that came with the wp_run port (Midfall/Yul/WpX.lean). ----
# The T3.1b card says "register WPX.lean's three sorries (owner: T3.2)". Only wpSS_exists was
# T3.2's, and T3.2 has now PROVED it - so its owner row is gone from this list and from the register,
# and the two rows below keep the cards PLAN-V3-cards.md actually names: :1312 and :1319 give
# loadWord_storeWord to T3.5 (the word and memory layer) and :1369, :1373 and :1375 give mulmod_toFr
# to T3.8 (the field-arithmetic bridge). The card's single-owner line for those two was a premise
# error, reported on the T3.1b ticket rather than copied into the register.
#
# CLOSED by T3.5. Midfall.Yul.WpX.loadWord_storeWord is PROVED in Midfall/Yul/WpX.lean, from the
# word and memory layer landed in Midfall/Yul/Word.lean: the equal 32-byte window reassembles the stored
# word, a disjoint window is invisible to the read, and the OVERLAP case is genuinely undetermined - it
# keeps the term itself, which is what the registered statement says. No hypothesis was added and the
# statement is verbatim the memo's 3.3 proposal. Its owner row is gone from this list and from the
# register.
#
# CLOSED by T3.8. Midfall.Yul.WpX.mulmod_toFr is PROVED in Midfall/Yul/WpX.lean - it was the last sorry
# in that file. EVM mulmod at the scalar modulus IS field multiplication in Fr r = ZMod r, and the
# registered statement needed NO canonicity hypothesis: the % qvmFrModulus the opcode applies is the
# reduction ZMod applies anyway (as in qvmToFr_add/qvmToFr_mul), and the result is already below
# 2^256, so the word wrap is the identity. The card's addmod twin (addmod_toFr), the named word
# operations (wMulmod/wAddmod/wSubFr) and their stepOp equalities, and subFr_toFr - the one bridge that
# DOES need x < r, with subFr_needsCanonicity showing the failure at r+1 - landed beside it. No
# hypothesis was added to the registered statement and it is verbatim what was registered.
# ---- GEN.0: the one sorry that came with the parametric-execution port (Midfall/Yul/VKP.lean). ----
# CLOSED by T3.2. The round-78 audit resolved the 3-way owner conflict to T3.2 (D-P71: "Also prove
# wpSS_exists_C"), and GEN.1 step 4 now has it: wpSS_exists_C and Midfall.Yul.WpX.wpSS_exists are both
# projections of the one fuel induction Midfall.Yul.WpX.wp_exists.
    # ---- everything else: the owner the register carried, re-keyed by declaration name ----
    Midfall.Halo2.Spec.*)         echo 'Phase 4 (spec layer)' ;;
    Midfall.Instances.PoseidonV2.*) echo 'V2 (PLAN-V2): C.1 headline lemmas - WP-M0 blocks, D.3 circuit gap' ;;
    Midfall.Instances.PoseidonValid.*) echo 'V2 (PLAN-V2): C.4 Valid.model - no Inhabited Model, kernel cannot reduce poseidonModel' ;;
    Midfall.Statements.*)         echo 'frozen statements (S1..S7 land later)' ;;
    Midfall.Yul.*)                echo 'P-SE stage 1-2: Yul run/contracts layer (semantic equivalence)' ;;
    Midfall.Lowering.*)           echo 'P-SE: semantic equivalence obligations' ;;
    Midfall.Assumptions.*)        echo 'P-SE: named holes in assumption files' ;;
    Midfall.LoweringV2.Blocks.FinalPairing.*) echo 'V2 (PLAN-V2): FP.0 FinalPairing skeleton - P.1 algebra, T.4 staticcall, T.5 steps' ;;
    Midfall.LoweringV2.Blocks.VkLoading.*)    echo 'V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md' ;;
    Midfall.LoweringV2.*)         echo 'V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md' ;;
    *)                            echo 'UNOWNED - assign a work package' ;;
  esac
}

BT='`'
table=$(while read -r decl mod kind status cone hash; do
      printf '| %s | %s | %s | %s | %s | %s%s%s | %s |\n' \
        "$decl" "$mod" "$kind" "$status" "$cone" "$BT" "$hash" "$BT" "$(owner "$decl")"
    done < <(bash scripts/sorries.sh --env))

HEADER='| declaration | module | kind | status | cone | statement | removed by |'
grep -q "^$HEADER$" SORRY.md || {
  echo 'gen_sorry.sh: SORRY.md has no table header row; restore it from git first' >&2
  exit 1
}
head=$(sed -n "1,/^| declaration | module |/p" SORRY.md)
tail=$(sed -n '/^## Upstream sorries/,$p' SORRY.md)
{
  printf '%s\n' "$head"
  printf '%s\n' "$table"
  printf '\n%s\n' "$tail"
} > SORRY.md.new
mv SORRY.md.new SORRY.md
printf '%s\n' "$table"

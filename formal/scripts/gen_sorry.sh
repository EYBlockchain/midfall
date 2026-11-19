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
      echo 'V3 SIM.7 - the V2 totality conjunct D-P64 (f); RECON.2 landed the V3 twin totalV3_of_stages (Composition.lean:214), so this V2 sorry retires with the old composition, not under ST.5' ;;
    Midfall.LoweringV2.noWriters_prog)
      echo 'V3 ST.12 - scans_prog_addr_indep removes it' ;;
    Midfall.LoweringV2.prefix_run_clean)
      echo 'V3 SIM.7 - deletes prefix_run_clean' ;;
    Midfall.LoweringV2.rejects_of_not_accepts)
      echo 'V3 SIM.7 with ST.5 - ST.5 (61b4f5e+): replacement rejectsV3_of_sims LANDED (Composition.lean:192) and F9 proves this statement derives False (StatementsV3Falsifiers.lean:476), but its only consumer is the V2 composition conjunct 3 (Blocks.lean:904) and LoweringV2/Blocks cannot import LoweringV3 (cycle: V3/Statements.lean:32), so W13 pairs the deletion with the consumer retirement' ;;
    Midfall.LoweringV2.runBody_iff_slices)
      echo 'V3 SIM.7 - deletes runBody_iff_slices' ;;
    Midfall.Yul.Bridge.Run_worldEq_of_noWriters)
      echo 'V3 SIM.5 - the shared Step induction (ST.10 cites it)' ;;
    # ---- SIM.1: the staged Lean view, landed in Midfall/Lowering/Stage.lean. ----
    # The scratch file records this leaf as ALG / Lean-only / NOT used by the glue, so it is outside
    # the headline cone; SIM.9 is the card that proves it (strengthened to field agreement).
    Midfall.Lowering.Stage.leanStage_prefix)
      echo 'V3 SIM.9 - leanStage coherence: the staged chain is a chain, with equal fields (leaf of SoundnessV3 section 1; not used by the glue)' ;;
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
    # ---- RECON.2: the ONE composition, landed in Midfall/LoweringV3/Composition.lean. ----
    # Three of the four V3 obligations are skeletons here: the composition is stated once, against the
    # single ValidV3 (LoweringV3/Statements.lean:1116), and the holes are the ROWS, which are SIM.2's
    # and SIM.6's to discharge. The fourth obligation, twoOutcomesV3_of_valid, is PROVED and so has no
    # row: its cone leaves are the ST.10 and ST.12 holes above. Each row carries its W12 witness and
    # falsifier in Composition.lean section 5.
    Midfall.LoweringV3.rejectsV3_of_sims)
      echo 'V3 SIM.2 + SIM.6 - the fourteen staged simulation rows sequenced, plus the prefix row; the proof is the evidence rejects_of_sims (SoundnessV3.lean:822) over StageBnd' ;;
    Midfall.LoweringV3.completeV3_of_progs)
      echo 'V3 SIM.2 + SIM.6 - the seven staged progress rows sequenced, plus the prefix progress row; the proof is the evidence completeness_of_progs (SoundnessV3.lean:1210) re-gated on G1CodecHeadlineLaws' ;;
    Midfall.LoweringV3.totalV3_of_stages)
      echo 'V3 SIM.2 + SIM.6 + ST.13 - existence from the sequenced progress rows, then runBody_mono to upgrade the zero gas oracle of the rows to the arbitrary total oracle TotalV3 quantifies over' ;;
    # ---- SIM.2: the staged boundary and the staged contracts, landed in Midfall/LoweringV2/Stages.lean.
    # The two prefix rows are SIM.6's: SIM.2 lands the split form they hand over, the sequenced chains
    # they compose with, and the PROVED fit (whole_program_sim / whole_program_prog), so each hole is one
    # row and not a shape. Neither is in the headline cone: nothing imports Stages.lean yet, and the three
    # RECON.2 holes that consume these leaves live in Composition.lean, whose bridge to this file is the
    # boundary-generic instantiation documented in the Stages.lean header.
    Midfall.LoweringV2.prefix_sim)
      echo 'V3 SIM.6 - the prefix row, soundness side: from an EntryFrame every run of Render.preBlock reverts or reaches Mid .start (Stages.lean); SIM.2 landed the split form and the fit' ;;
    Midfall.LoweringV2.prefix_prog)
      echo 'V3 SIM.6 - the prefix row, progress side: the prefix run exists and every run reaches StageInv .start (Stages.lean); SIM.2 landed the fit with slices_seq_prog' ;;
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
    # ---- T3.10: the quotient-interpreter CONTRACT landed in Midfall/Lowering/QuotientInterp.lean. ----
    # The card is a STATEMENT card: it lands QInterpRefines typechecked with W12 witnesses and falsifiers
    # and does NOT prove it. The one sorry is the row itself - the one-off lemma route B needs - and it is
    # ROW.Q's to discharge, not a shape gap: QPROBE measured that the emitted loop does not execute at any
    # fuel by unrolling, which is why the contract exists.
    Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop)
      echo 'V3 ROW.Q - T3.10 landed the contract (Midfall/Lowering/QuotientInterp.lean: QInterpRefines, ported from the evidence file GeneratorRows.lean:896 and adapted to D-P72 memory windows); this is route B one-off lemma: the emitted interpreter loop refines evalQuotientIdentity on one identity segment' ;;

    # ---- WID.1: the widening STATEMENTS, landed in Midfall/LoweringV3/Widening.lean and
    # Midfall/LoweringV3/WideningStages.lean (D-P72 clause 1: the class is widened for EVERY render,
    # never at a fixture, so D-P71's rule is respected - the IVC instance is a test, WID.4/WID.7).
    # None of the four is in the headline cone: nothing in the tree consumes `lowering_correctW` until
    # RECON.3 routes the rows into it, so the cone is still the same ten leaves. ----
    Midfall.LoweringW.lowering_correctW)
      echo 'V3 WID.H - THE TARGET: the widened generic theorem, stated with the evaluator contract as a hypothesis (hQ : isExternal R -> EvalContracts R Q) because without it the statement is false for an arbitrary Q (ValidW.emptyBody + evalModel_emptyBody, both PROVED). WID.6 ties Q to the generated body, WID.17 proves EvalContracts, WID.H drops hQ; the decomposition is lowering_equivalenceW_of plus the row families SimContractsW/ProgContractsW, which RECON.3 discharges' ;;
    Midfall.LoweringW.model_quotientMode)
      echo 'V3 WID.H - generator fact (Artifacts.lean:534-537): the model externalises the quotient exactly when the flag says so. W12 witness: #eval at one embedded and one external model' ;;
    Midfall.LoweringW.instWords_of_decoded)
      echo 'V3 WID.11 - ALG, Lean only: on a calldata that decodes, the decoder instance words are the raw ones (a statement about decodeCalldata alone); premise of accDecodes_of_leanAcceptsAcc in the vkLoading progress row' ;;
    # ---- RECON.3: the WIDENED COMPOSITION, landed in Midfall/LoweringV3/CompositionW.lean (D-P72
    # clause 1). Three skeletons, one per RECON.2 skeleton, each with its named leaves in its docstring;
    # the fourth obligation (twoOutcomesW_of_valid) and the glue are PROVED and have no row. None is in
    # the headline cone: the cone is rooted at lowering_equivalence_poseidon and nothing there reads a W
    # declaration, so the cone stays at ten leaves. Owners are the M6 row cards plus the WID arms.
    Midfall.LoweringW.rejectsW_of_sims)
      echo 'V3 SIM.2 + SIM.6 re-pointed at BlockSimW, with WID.13/WID.14/WID.15/WID.16 - the widened rejection; the proof is the rejectsV3_of_sims shape of RECON.2 (Composition.lean:192) over StageInvW and LeanAcceptsAcc' ;;
    Midfall.LoweringW.completeAnyGasW_of_progs)
      echo 'V3 SIM.2 + SIM.6 re-pointed at BlockProgSW, plus ST.13 (runBody_mono) and WID.19 - the widened completeness at EVERY total gas oracle (D-P72 clause 5); CompleteW is then PROVED from it by CompleteAnyGasW.toComplete' ;;
    Midfall.LoweringW.totalW_of_stages)
      echo 'V3 SIM.2 + SIM.6 re-pointed at BlockProgSW, plus WID.19 and EvalBodyTotal (WideningStages.lean:492 via evalRel_answers) - the widened totality; a separate leaf, not a projection of conjunct 2, for the reason RECON.2 gives at Composition.lean:207-213' ;;

    Midfall.LoweringW.batchedCheck_iff_contract)
      echo 'V3 WID.11 - ALG, no Yul: the batched check IS the contract pairing equation on the two batched inputs (batchedCheck_eq + dualMsm_check_iff_contract, same hn/hs pins as without an accumulator); the ALG half of the widened finalPairing row' ;;

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

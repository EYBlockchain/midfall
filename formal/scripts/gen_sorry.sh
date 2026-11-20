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
# FAILURE PATHS ARE GUARDED (GSHARD). This script was the instrument of a data loss at least three times
# (OBJ.6, OBJ.7, and a near-miss on ST.6), because the scan ran inside a PROCESS SUBSTITUTION:
#
#     table=$(while read ... done < <(bash scripts/sorries.sh --env))
#
# The shell DISCARDS the exit status of a process substitution, and the `while read` loop over the dead
# producer exits 0, so a `Report.lean` that failed - or that succeeded and printed no `SORRY ` line at
# all - looked exactly like a tree with no sorries: an empty table, and the header plus nothing written
# over a 79-row register. `set -euo pipefail` does not help: there is no pipe here and nothing non-zero
# ever reached the shell. Three guards now stand between a broken scan and the file:
#
#   * a scan that exits non-zero, that yields ZERO rows, or whose lines do not all render as well-formed
#     register rows aborts BEFORE SORRY.md is touched, exits 1, and names the cause;
#   * a table with FEWER rows than the file on disk aborts unless `--allow-shrink` is passed, and both
#     counts are printed either way: a card that closes a sorry shrinks the register by a few rows, a
#     broken scan shrinks it by all of them;
#   * the replacement is staged in a temp file in the same directory, re-read and re-counted from disk,
#     and only then `mv`d into place, so an interrupted or partial run cannot leave a truncated register
#     behind.
#
# The SUCCESS PATH IS UNCHANGED, and that is the acceptance test: on a healthy tree the bytes written are
# the bytes already committed, so `git diff formal/SORRY.md` after a normal run must stay empty.
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
    # ---- PL.H0 (D-P74): THE ROOT IS ONE TREE, SO THESE ARE THE ROOT LEAVES. ----
    # rejectsV3_of_sims, completeV3_of_progs and totalV3_of_stages were RECON.2's three skeletons.
    # PL.H0 PROVES the first two as glue and DELETES the third (BodyTotal quantifies over every
    # calldata while ProgRowsV3 assumes LeanAccepts), so no owner row stands under those names any
    # more. What the cone reads now is: fourteen row leaves (Rows.lean, one per block and direction),
    # the two prefix rows (Stages.lean, SIM.6), and four totality leaves (Totality.lean, TOT.1).
    Midfall.LoweringV3.vk_blockSim)
      echo 'V3 GEN.1 (WP A3) - the vkLoading simulation row at BlockSim over StageInv (Rows.lean); evidence GeneratorRows.lean:1096 at the V3 reading' ;;
    Midfall.LoweringV3.vk_blockProgS)
      echo 'V3 GEN.1 (WP A3) - the vkLoading progress row at BlockProgS (Rows.lean); evidence GeneratorRows.lean:1103' ;;
    Midfall.LoweringV3.tp_blockSim)
      echo 'V3 ROW.TP (WP A6) - the transcriptParser simulation row (Rows.lean); children tp_computes / tp_agrees / tp_poison land with ROW.TP; evidence GeneratorRows.lean:817' ;;
    Midfall.LoweringV3.tp_blockProgS)
      echo 'V3 ROW.TP (WP A6) - the transcriptParser progress row (Rows.lean); evidence GeneratorRows.lean:830, leaf ROW.TP.10' ;;
    Midfall.LoweringV3.lag_blockSim)
      echo 'V3 T3.9 (WP A4) - the lagrange simulation row (Rows.lean); children loops a-e, HLP.1.b, lag_agrees, lag_poison; evidence GeneratorRows.lean:621' ;;
    Midfall.LoweringV3.lag_blockProgS)
      echo 'V3 T3.9 (WP A4) - the lagrange progress row, the only reader of CompleteSide (Rows.lean); evidence GeneratorRows.lean:628' ;;
    Midfall.LoweringV3.pcs_blockSim)
      echo 'V3 ROW.PCS (WP A10) - the pcs simulation row (Rows.lean); evidence GeneratorRows.lean:1013' ;;
    Midfall.LoweringV3.pcs_blockProgS)
      echo 'V3 ROW.PCS (WP A10) - the pcs progress row; decode half is ROW.PCS decode_exists (Rows.lean); evidence GeneratorRows.lean:1019' ;;
    Midfall.LoweringV3.fp_blockSim)
      echo 'V3 ROW.FP (WP A11) - the finalPairing simulation row (Rows.lean); children ec_pairing_sem, fp_pairing_algebra, fp_poison; evidence GeneratorRows.lean:1077' ;;
    Midfall.LoweringV3.fp_blockProgS)
      echo 'V3 ROW.FP (WP A11) - the finalPairing progress row (Rows.lean); evidence GeneratorRows.lean:1083' ;;
    # tr_blockSim / tr_blockProgS have NO owner row: PL.H0 took the card's optional step-4 lift and
    # PROVED both from TraceReturn.tr_sound_clean_noarm / tr_poison_walk_noarm / tr_blockProgress,
    # with trRetMptr derived from ValidV3 (LoweringV3.returnMptr_of_valid). They left the register.
    Midfall.LoweringV3.prefix_simV3)
      echo 'V3 SIM.6 (WP A1) - prefix_sim (LoweringV2/Stages.lean:595) RESTATED over ValidV3 by PL.H0 Stop-if 2: ValidV3.toV2 fails on the program field (LoweringV3.programOk and LoweringV2.programOk are parallel copies, not defeq), so the V3 glue cannot spend the V2 row. Conclusion verbatim; only hR moves. Discharges the moment the programOk bridge lands.' ;;
    Midfall.LoweringV3.prefix_progV3)
      echo 'V3 SIM.6 (WP A1) - prefix_prog (LoweringV2/Stages.lean:612) RESTATED over ValidV3 by PL.H0 Stop-if 2, same reason and same verbatim conclusion as prefix_simV3.' ;;
    Midfall.LoweringV3.gasFree_of_valid)
      echo 'V3 TOT.1 (WP A12) - the program of a valid render executes no gas(): decidable scan GasFree (Totality.lean); evidence premise gap PG-GAS, GeneratorRows.lean:1260' ;;
    Midfall.LoweringV3.runBody_gas_oblivious)
      echo 'V3 TOT.1.a (WP A12) - a gas-free program has the same runs under every gas oracle; one Step induction in the shape of Bridge.Run_worldEq_of_noWriters (Totality.lean; evidence GeneratorRows.lean:1266)' ;;
    Midfall.LoweringV3.block_live)
      echo 'V3 TOT.1 (WP A12) - per-block existence from a boundary a run can actually be at (LivePre, Totality.lean); leaves TOT.1.b-h, one per block (evidence GeneratorRows.lean:1335)' ;;
    Midfall.LoweringV3.prefix_live)
      echo 'V3 TOT.1 with SIM.6 (WP A12/A1) - prefix existence: the ABI guard and the memory guard each revert or pass and both are runs (Totality.lean; evidence GeneratorRows.lean:1342)' ;;
    Midfall.LoweringV2.prog_slices_decomp)
      echo 'V3 ST.11 (retired by the re-point) - the shadow-free form of the structural decomposition. It is FALSE for a valid render (B-5/D-13) and nothing in the cone reaches it any more: run_splitV3/run_joinV3 (PrefixV3.lean §5) spend the PROVED prog_slices_decompV3 with noShadowB projected from ValidV3.program, and Composition.lean/Totality.lean cite those. The row stays OPEN as a text; Blocks.lean may not import LoweringV3, so deleting it is a V2-side edit (SIM.7 class), not this card''s' ;;
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
    # ---- ROW.Q: the quotient rows for every render, landed in Midfall/LoweringV3/QuotientRows.lean. ----
    # The card is a STATEMENT card: the two generic rows and their ROW.Q.1 leaf are the holes, each with
    # a PROVED witness and a PROVED falsifier in that file. None is in the headline cone (nothing in
    # Instances/ imports this file). The evidence file's SimPins/R.Valid pair is read as
    # ValidV3 + G1CodecHeadlineLaws, which is RECON.2's dissolution (Composition.lean:161), and the
    # refuted Midfall.Lowering.identityCorrespondence_of_bridge was DELETED here and replaced by the
    # PROVED identityCorrespondence_of_bridge_fixed in the same commit (card step 1, W13).
    Midfall.LoweringV3.QuotientRows.q_blockSim)
      echo 'V3 ROW.Q - the quotientLin simulation row for every render, route B: leaves are ROW.Q.1 (qlin_split_loop, this file), ROW.Q.3 (QuotientInterp.qinterpRefines_qvmLoop, T3.10), ROW.Q.4 (the frame valuation) and the builder rows Qvm.lean:631/:698/:713/:768/:995; ROW.Q.5 is NOT stated because the six generated line families have no AST twin (OBJ.15 splices them through YulParse, PG-Q-OBJECT)' ;;
    Midfall.LoweringV3.QuotientRows.q_blockProgS)
      echo 'V3 ROW.Q - the quotientLin progress row for every render: same leaves plus existence through the numerator (qvm_validated_noBoundsFault, Qvm.lean:768) and CompleteSide for the challenge values the scope reads' ;;
    Midfall.LoweringV3.QuotientRows.qlin_split_loop)
      echo 'V3 ROW.Q.1 - the split loop of the linearization scope (GeneratorRows.lean:875, ported verbatim): the squaring walk computing (x^(2^k-1), x^(2^k)); base case PROVED as qlin_split_loop_witness_base_case, pre-clause falsifier PROVED as qlin_split_loop_falsifier_pre_pins_x_pow_2i' ;;
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

    Midfall.Instances.g1CodecC_compressedEncoderFirst)
      echo 'B3 REF.9 + REF.10 (D-P62, the codec laws at the deployment) - the encoder-first compressed law at g1CodecC: fpSqrt recovers y from x and the sign bit (REF.9), then the law (REF.10). Stated by B2 (REF.4) because the deployment needs the computable codec g1CodecC to EXIST before the reference gate can decode a proof point, and the decoder-first half is proved there; the gate does not read this direction.' ;;

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

# ---- options ---------------------------------------------------------------------------------------
# `--allow-shrink` is the ONLY way this script will make the register shorter, and it has to be typed out
# on purpose: a card that CLOSES a sorry knows it is closing one, and a scan that failed does not.
ALLOW_SHRINK=0
for arg in "$@"; do
  case "$arg" in
    --allow-shrink) ALLOW_SHRINK=1 ;;
    -h|--help)
      printf '%s\n' \
        'usage: bash scripts/gen_sorry.sh [--allow-shrink]' \
        '' \
        'Regenerate the table in SORRY.md from `bash scripts/sorries.sh --env`. The table is never' \
        'hand-edited: this script is the only thing that writes it.' \
        '' \
        '  --allow-shrink   accept a new table with FEWER rows than the file on disk - the normal case' \
        '                   when a card closes sorries. Without it any shrink is refused and both counts' \
        '                   are printed, so a scan that failed cannot overwrite a healthy register.' \
        '  -h, --help       this text' \
        '' \
        'Every failure aborts BEFORE SORRY.md is touched and exits non-zero. The replacement is staged in' \
        'a temp file in this directory, re-read and re-counted from disk, and only then moved into place.'
      exit 0 ;;
    *) printf 'gen_sorry.sh: unknown argument: %s (known: --allow-shrink, --help)\n' "$arg" >&2; exit 2 ;;
  esac
done

BT='`'

# A register row, counted as checks.sh counts them: six plain columns, a 16-hex-digit statement hash,
# then the owner. Keeping this pattern in step with the gate's is what makes the guards below mean what
# the gate means - a row either of them cannot parse is a row that does not exist.
ROW_RE='^\| [^ |]+ \| [^ |]+ \| [^ |]+ \| [^ |]+ \| [^ |]+ \| `([0-9a-f]{16})` \|'
count_rows()      { grep -cE "$ROW_RE" "$1" || true; }   # grep -c prints 0 and exits 1 on a zero count
count_rows_text() { printf '%s\n' "$1" | grep -cE "$ROW_RE" || true; }

# ---- preconditions on the file we are about to replace ---------------------------------------------
HEADER='| declaration | module | kind | status | cone | statement | removed by |'
grep -q "^$HEADER$" SORRY.md || {
  echo 'gen_sorry.sh: SORRY.md has no table header row; restore it from git first' >&2
  exit 1
}
# Both anchors below are copied VERBATIM into the new file, so a missing anchor is not a formatting
# detail: the copy would silently drop everything after it. Same class of loss, same refusal.
grep -q '^## Upstream sorries' SORRY.md || {
  echo 'gen_sorry.sh: SORRY.md has no "## Upstream sorries" section; restore it from git first' >&2
  exit 1
}
old_rows=$(count_rows SORRY.md)

# ---- the scan: its exit status is now the FIRST thing checked --------------------------------------
# `if !` is the fix. The old form ran the scan in a process substitution, whose status the shell
# discards, so a failed Report.lean was indistinguishable from a tree with no holes in it.
if ! inventory=$(bash scripts/sorries.sh --env); then
  echo 'gen_sorry.sh: ABORT - scripts/sorries.sh --env exited non-zero: lake env lean' >&2
  echo 'gen_sorry.sh: scripts/Report.lean failed to build or to run (its verdicts are Lean errors on' >&2
  echo 'gen_sorry.sh: purpose, so a real gate failure lands here). SORRY.md NOT WRITTEN - the register' >&2
  echo "gen_sorry.sh: on disk is preserved byte-for-byte at $old_rows rows." >&2
  exit 1
fi

table=$(while read -r decl mod kind status cone hash; do
      # a blank line is not a declaration. The old form read to EOF and produced nothing; this one must
      # not manufacture a row of empty columns out of an empty inventory.
      [ -n "$decl" ] || continue
      printf '| %s | %s | %s | %s | %s | %s%s%s | %s |\n' \
        "$decl" "$mod" "$kind" "$status" "$cone" "$BT" "$hash" "$BT" "$(owner "$decl")"
    done <<< "$inventory")

new_rows=$(count_rows_text "$table")
inv_rows=$(printf '%s\n' "$inventory" | grep -cv '^[[:space:]]*$' || true)

# ---- guard 1: an empty inventory is never a register --------------------------------------------------
# There is NO flag for this one, and that is deliberate: a zero-row table is what a failed scan looks
# like, and no card in this plan is close enough to a sorry-free tree for the ambiguity to be worth
# trading away. The day the last sorry is proved is a change to this guard, made in one line with the
# register at one row, not a flag typed under pressure.
if [ "$new_rows" -eq 0 ]; then
  echo 'gen_sorry.sh: ABORT - the environment scan exited 0 but produced NO register rows' >&2
  echo "gen_sorry.sh: ($inv_rows non-blank inventory line(s), none of them a well-formed row). Writing" >&2
  echo "gen_sorry.sh: that would collapse SORRY.md from $old_rows rows to a header and nothing, which is" >&2
  echo 'gen_sorry.sh: the data loss this script is known for. SORRY.md NOT WRITTEN; the file on disk is' >&2
  echo "gen_sorry.sh: preserved byte-for-byte at $old_rows rows. First check whether the scan prints" >&2
  echo "gen_sorry.sh: 'SORRY ' lines at all: bash scripts/sorries.sh --env | wc -l." >&2
  exit 1
fi

# ---- guard 2: every inventory line must render as a well-formed row ---------------------------------
if [ "$new_rows" -ne "$inv_rows" ]; then
  echo "gen_sorry.sh: ABORT - the scan printed $inv_rows inventory line(s) but only $new_rows render as" >&2
  echo 'gen_sorry.sh: well-formed register rows (six plain columns and a 16-hex-digit statement hash, the' >&2
  echo "gen_sorry.sh: shape checks.sh parses). A row that does not parse would drop off the register" >&2
  echo "gen_sorry.sh: silently, i.e. a sorry would stop being gated. SORRY.md NOT WRITTEN; the file is" >&2
  echo "gen_sorry.sh: preserved at $old_rows rows." >&2
  exit 1
fi

# ---- guard 3: never shrink without being told to -----------------------------------------------------
if [ "$new_rows" -lt "$old_rows" ] && [ "$ALLOW_SHRINK" -ne 1 ]; then
  echo "gen_sorry.sh: ABORT - refusing to SHRINK the register: $old_rows rows on disk, $new_rows rows" >&2
  echo "gen_sorry.sh: from the scan, a loss of $((old_rows - new_rows)) rows. A card that legitimately" >&2
  echo 'gen_sorry.sh: closes sorries shrinks by a few rows and says so: re-run with --allow-shrink. A' >&2
  echo 'gen_sorry.sh: scan that half-failed shrinks by all of them, which is why this is a refusal and' >&2
  echo 'gen_sorry.sh: not a warning. SORRY.md NOT WRITTEN; the file is preserved at '"$old_rows"' rows.' >&2
  exit 1
fi
if [ "$new_rows" -lt "$old_rows" ]; then
  printf 'gen_sorry.sh: --allow-shrink: register %s -> %s rows (-%s), as instructed.\n' \
    "$old_rows" "$new_rows" "$((old_rows - new_rows))" >&2
else
  printf 'gen_sorry.sh: register rows: %s on disk -> %s from the scan.\n' "$old_rows" "$new_rows" >&2
fi

# ---- staged, verified, atomic replace ----------------------------------------------------------------
head=$(sed -n "1,/^| declaration | module |/p" SORRY.md)
tail=$(sed -n '/^## Upstream sorries/,$p' SORRY.md)
# Staged in THIS directory so the mv below is a rename on one filesystem and never a half-copied file.
tmp=$(mktemp "SORRY.md.new.XXXXXX") || {
  echo 'gen_sorry.sh: ABORT - could not create a staging file next to SORRY.md' >&2
  exit 1
}
trap 'rm -f "$tmp"' EXIT
trap 'rm -f "$tmp"; exit 130' INT TERM
{
  printf '%s\n' "$head"
  printf '%s\n' "$table"
  printf '\n%s\n' "$tail"
} > "$tmp"
# Re-read what actually reached the disk before it is allowed to BECOME the register: a partial write -
# disk full, a signal, a shell that died mid-printf - must never be moved into place.
if [ "$(count_rows "$tmp")" -ne "$new_rows" ] || ! grep -q "^$HEADER$" "$tmp"; then
  echo "gen_sorry.sh: ABORT - the staged file came back with $(count_rows "$tmp") rows, not the $new_rows" >&2
  echo 'gen_sorry.sh: the scan reported, or without its header row. SORRY.md NOT WRITTEN; the file is' >&2
  echo "gen_sorry.sh: preserved at $old_rows rows." >&2
  exit 1
fi
mv "$tmp" SORRY.md
trap - EXIT
printf '%s\n' "$table"
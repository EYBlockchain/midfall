# sorry register

Every proof hole in `formal/` is listed here with the work package that removes it. The gate
(`formal/scripts/checks.sh`; DG.7 wires it to a runner) fails if a hole appears that is not listed,
if a listed one disappears without this file being updated, or if a listed statement is RESTATED.

**THE REGISTER IS KEYED BY DECLARATION NAME AND READ FROM THE ENVIRONMENT** (DG.2, PLAN-V3 section 5).
The inventory is produced by `bash scripts/gen_sorry.sh`, which reads `bash scripts/sorries.sh --env`:
`#sorry_sweep` in `scripts/Report.lean`, which walks the ELABORATED TERMS of every project module and
prints one row per declaration whose own type or value uses `sorryAx`. Nothing on this table is a text
scan, and that is the point:

* a row is a DECLARATION, so an unrelated edit that moves lines in the same file does not touch the
  register (the old `file:line` key held the tip red for a day over a 227 -> 252 shift, review J-8);
* a hole with no `sorry` token - `admit`, `stop`, a direct `sorryAx`, or a macro that expands to one -
  is a row, because the kernel sees the term and not the text (review J-2: five such escapes were
  demonstrated against the old regex);
* `status` is OPEN, REFUTED or VACUOUS, computed from the tree: a sorried declaration whose negation a
  sorry-free project theorem proves is REFUTED - it proves `False`, so the cone count is not a
  distance - and one whose hypothesis is refuted for every instance is VACUOUS;
* `cone` is ROOT when the declaration lies in the dependency cone of the headline
  `Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon` (as `#cone_report` walks it, constructors
  included) and - otherwise;
* `statement` is a 64-bit structural hash of the declaration's TYPE (binder names not hashed), so a
  paraphrase of a registered obligation changes its row instead of hiding in it (review J-10).

A bare `sorry` outside this register is never allowed; a missing proof becomes a named hypothesis
structure in `Midfall/Assumptions/` instead (plan Section 3, gap policy). The Phase 1 exit criterion is
explicitly `Statements.lean compiles with sorry`, so what is listed here is the planned Phase 1 state,
not sloppiness.

Two cross-checks run with the table, both in `scripts/checks.sh`. (1) The TEXT scan
(`bash scripts/sorries.sh`, comment-stripped) must find sorries in the same MODULES the environment scan
does - 19 = 19 at `3a7c017`, with the per-module counts agreeing at 58 = 58. (2) No ROOT row may be
UNOWNED: a hole in the headline cone must name the card that takes it out (review I-10). Owners are
keyed by declaration name, so a RENAMED cone sorry reads as one row removed and one added and lands
UNOWNED on purpose. One file is exempt from the text scan by name, `Midfall/Tools/Done.lean`: it is the
gate tool, so it carries the word `sorry` in the message strings it prints, and the scanner strips
comments but not string literals. The environment scan needs no exemption.

| declaration | module | kind | status | cone | statement | removed by |
| Midfall.Generator.Certified.prog_callsResolved | Midfall.Generator.Certified | theorem | OPEN | - | `9421fd6429340074` | V3 CERT.5 - call-site lemma per emitter plus the helper signature table |
| Midfall.Generator.Certified.prog_closed | Midfall.Generator.Certified | theorem | OPEN | - | `bcbde4e04e492ed2` | V3 CERT.5 - from constsDeclared/constTable plus the inlineContractConstants free-name lemma |
| Midfall.Generator.Certified.prog_codegenStruct | Midfall.Generator.Certified | theorem | OPEN | - | `4f989eec634f4949` | V3 CERT.2 - route A: the emitted tree is the generator text (today false until WP-G1 is certified) |
| Midfall.Generator.Certified.prog_constLinesLiteral | Midfall.Generator.Certified | theorem | OPEN | - | `e812aa299d987237` | V3 CERT.6 - every Constants.sol line has a literal RHS; disappears when CERT.3 prints the table |
| Midfall.Generator.Certified.prog_constTable | Midfall.Generator.Certified | theorem | OPEN | - | `a896f0efd31c3e8e` | V3 CERT.6 with CERT.3 - constTableOf is expectedConsts once Constants.sol is printed from the table |
| Midfall.Generator.Certified.prog_constsDeclared | Midfall.Generator.Certified | theorem | OPEN | - | `48602e76f62df287` | V3 CERT.5 - free-name lemma per emitter against the fixed constant name list |
| Midfall.Generator.Certified.prog_gasCallOk | Midfall.Generator.Certified | theorem | OPEN | - | `6d1266c42d58757b` | V3 CERT.5 (D3, D-CERT1) - gas() occurs only as a call gas argument |
| Midfall.Generator.Certified.prog_gasFree | Midfall.Generator.Certified | theorem | OPEN | - | `f5badf6de19edb41` | V3 CERT.5 (D3, D-CERT1) - the whole program executes no gas() (D-GATE1) |
| Midfall.Generator.Certified.prog_hasMultiPointSet | Midfall.Generator.Certified | theorem | OPEN | - | `4c7363c40ef7ad06` | V3 CERT.6 (D4, D-CERT1) - intermediateSets has a point set of size at least two |
| Midfall.Generator.Certified.prog_noShadow | Midfall.Generator.Certified | theorem | OPEN | - | `21866adc2c2e6bcd` | V3 CERT.5 - every-binder scan: binder lemma per emitter (the tree name is noShadowProg) |
| Midfall.Generator.Certified.prog_noWriters | Midfall.Generator.Certified | theorem | OPEN | - | `028c6826839c483b` | V3 CERT.5 - scan lemma per emitter; inlining substitutes literals only |
| Midfall.Generator.Certified.prog_programFits | Midfall.Generator.Certified | theorem | OPEN | - | `f6caf92177936208` | V3 CERT.6 (D4, D-CERT1) - D-QVM1 address-fit: VK window and quotient interpreter |
| Midfall.Generator.Certified.prog_transcriptRegionOk | Midfall.Generator.Certified | theorem | OPEN | - | `72ca42ee18d1554a` | V3 CERT.6 (D4, D-CERT1) - PG-TPBUF: transcript window holds the longest absorb run and meets no walk window |
| Midfall.Generator.Certified.v3_closed | Midfall.Generator.Certified | theorem | OPEN | - | `4b3ac30edb4fe645` | V3 CERT.5 - mainClosed restricted to the main block |
| Midfall.Generator.Certified.v3_codegen | Midfall.Generator.Certified | theorem | OPEN | - | `dfc804e64b6ba392` | V3 CERT.2 - route A: CodegenAgrees (today false until WP-G1 is certified) |
| Midfall.Generator.Certified.v3_exitDiscipline | Midfall.Generator.Certified | theorem | OPEN | - | `1e98f03044edf5bb` | V3 CERT.5 - exit-scan lemma per emitter |
| Midfall.Generator.Certified.v3_noShadow | Midfall.Generator.Certified | theorem | OPEN | - | `6eebd740e722a4cd` | V3 CERT.5 - top-level binder scan, as prog_noShadow |
| Midfall.Halo2.Spec.accepts | Midfall.Halo2.Spec.Piop | def | OPEN | - | `6db1418cbda599b6` | Phase 4 (spec layer) |
| Midfall.Instances.PoseidonV2.poseidon_quotient_block | Midfall.Instances.PoseidonV2 | theorem | OPEN | - | `f2571a03d4164a52` | V3 ROW.Q - the quotient row: the one block the generic hinge does not cover |
| Midfall.Instances.PoseidonV2.poseidon_rejects | Midfall.Instances.PoseidonV2 | theorem | OPEN | - | `3e7a72dcd164821a` | V3 PL.H via rejectsV3_of_rows - V2 C.3 staged rejection contracts |
| Midfall.Instances.PoseidonValid.poseidonValid_model | Midfall.Instances.PoseidonValid | theorem | OPEN | - | `512589e39c0f0f04` | V2 (PLAN-V2): C.4 Valid.model - no Inhabited Model, kernel cannot reduce poseidonModel |
| Midfall.Lowering.Stage.leanStage_prefix | Midfall.Lowering.Stage | theorem | OPEN | - | `6a12d9b2e6313461` | V3 SIM.9 - leanStage coherence: the staged chain is a chain, with equal fields (leaf of SoundnessV3 section 1; not used by the glue) |
| Midfall.Lowering.builder_segments_total | Midfall.Lowering.Qvm | theorem | OPEN | - | `19417891ad4c8eb2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.decodeAcc_encode_pointPair | Midfall.Lowering.Accumulator | theorem | OPEN | - | `028ec007c2c32bbd` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.decodeAcc_injective | Midfall.Lowering.Accumulator | theorem | OPEN | - | `4b93d0d78ab51374` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.end_to_end_acc_complete | Midfall.Lowering.Obligations | theorem | VACUOUS | - | `5ecfad1c74fec97c` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.extcodehash_of_deployment | Midfall.Lowering.Surface | theorem | OPEN | - | `c9fe99e0842043ed` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.feToU256_frToRepr | Midfall.Lowering.VkDigest | theorem | OPEN | - | `114330cf0dcde246` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.finalPairing_acc_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `f54a5e65072fb645` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.finalPairing_progress_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `de274924b227a440` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.finalPairing_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `39f6b033b0de37f2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.lagrange_progress_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `0c43c28a48d340d3` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.lagrange_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `71994fd83543a20d` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.lowering_equivalence_noAcc | Midfall.Lowering.Obligations | theorem | OPEN | - | `6a837e6c7e393c3d` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.partialProgress_not_of_alwaysReverts | Midfall.Lowering.Partials | theorem | OPEN | - | `be6592a893f09eb2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.partialSound_of_alwaysReverts | Midfall.Lowering.Partials | theorem | OPEN | - | `a8d81d9728b159f8` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.pcs_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `cb944a2ab0dd5d56` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.quotientLin_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `1d49cb9e6cf29a90` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_certifier | Midfall.Lowering.Qvm | theorem | OPEN | - | `562667ac0251841e` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_identity | Midfall.Lowering.Qvm | theorem | OPEN | - | `c57c0bb96b4470d8` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_program | Midfall.Lowering.Qvm | theorem | OPEN | - | `872104589438bfc7` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_stream | Midfall.Lowering.QvmFold | theorem | OPEN | - | `190c993b2542362d` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_validated_noBoundsFault | Midfall.Lowering.QvmNoBounds | theorem | OPEN | - | `b3f52e40cfe6cea7` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.toExec_fixedScalarCount | Midfall.Lowering.AccEncoding | theorem | OPEN | - | `df38b488380809ce` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.toExec_fullyCollapsed | Midfall.Lowering.AccEncoding | theorem | OPEN | - | `65e5bf121fe62b7b` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.toExec_validFor | Midfall.Lowering.AccEncoding | theorem | OPEN | - | `b742d844c7aa9ae4` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.transcriptParser_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `cd8f5ff36e0746fd` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.vkLoading_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `c2f09d7df1c9e765` | P-SE: semantic equivalence obligations |
| Midfall.LoweringV2.Blocks.FinalPairing.ec_pairing_contract | Midfall.LoweringV2.Blocks.FinalPairing | theorem | OPEN | - | `dd0af6f267ae0d8d` | V2 (PLAN-V2): FP.0 FinalPairing skeleton - P.1 algebra, T.4 staticcall, T.5 steps |
| Midfall.LoweringV2.Blocks.VkLoading.vk_poison_walk | Midfall.LoweringV2.Blocks.VkLoading | theorem | OPEN | - | `26e8c971c0e3695b` | V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md |
| Midfall.LoweringV2.Blocks.VkLoading.vk_progress | Midfall.LoweringV2.Blocks.VkLoading | theorem | OPEN | - | `27383cf076f32568` | V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md |
| Midfall.LoweringV2.Blocks.VkLoading.vk_sound_clean | Midfall.LoweringV2.Blocks.VkLoading | theorem | OPEN | - | `af938e7c295cf4c2` | V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md |
| Midfall.LoweringV2.blockContracts_of_valid | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `cad933e437381137` | V3 SIM.7 - deletes the old composition (RV-10: false as stated until RECON.1 PayloadAgrees) |
| Midfall.LoweringV2.bodyTotal_of_valid | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `567141948b3e3b83` | V3 SIM.7 - the V2 totality conjunct D-P64 (f); RECON.2 landed the V3 twin totalV3_of_stages (Composition.lean:214), so this V2 sorry retires with the old composition, not under ST.5 |
| Midfall.LoweringV2.end_to_end | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `937db535983dbffe` | V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md |
| Midfall.LoweringV2.hoist_prog_addr_indep | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `9b58bf8246b39da5` | V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md |
| Midfall.LoweringV2.noWriters_prog | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `2b62208f4c1f0276` | V3 ST.12 - scans_prog_addr_indep removes it |
| Midfall.LoweringV2.prefix_prog | Midfall.LoweringV2.Stages | theorem | OPEN | - | `9d64b179f8090f6f` | V3 SIM.6 - the prefix row, progress side: the prefix run exists and every run reaches StageInv .start (Stages.lean); SIM.2 landed the fit with slices_seq_prog |
| Midfall.LoweringV2.prefix_run_clean | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `4e5f39adb62c935e` | V3 SIM.7 - deletes prefix_run_clean |
| Midfall.LoweringV2.prefix_sim | Midfall.LoweringV2.Stages | theorem | OPEN | - | `01da0b3c1307df4c` | V3 SIM.6 - the prefix row, soundness side: from an EntryFrame every run of Render.preBlock reverts or reaches Mid .start (Stages.lean); SIM.2 landed the split form and the fit |
| Midfall.LoweringV2.prog_slices_decomp | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `7c068b01308bc4df` | V3 ST.11 (retired by the re-point) - the shadow-free form of the structural decomposition. It is FALSE for a valid render (B-5/D-13) and nothing in the cone reaches it any more: run_splitV3/run_joinV3 (PrefixV3.lean §5) spend the PROVED prog_slices_decompV3 with noShadowB projected from ValidV3.program, and Composition.lean/Totality.lean cite those. The row stays OPEN as a text; Blocks.lean may not import LoweringV3, so deleting it is a V2-side edit (SIM.7 class), not this cards |
| Midfall.LoweringV2.rejects_of_not_accepts | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `126f21c9acf4e222` | V3 SIM.7 with ST.5 - ST.5 (61b4f5e+): replacement rejectsV3_of_sims LANDED (Composition.lean:192) and F9 proves this statement derives False (StatementsV3Falsifiers.lean:476), but its only consumer is the V2 composition conjunct 3 (Blocks.lean:904) and LoweringV2/Blocks cannot import LoweringV3 (cycle: V3/Statements.lean:32), so W13 pairs the deletion with the consumer retirement |
| Midfall.LoweringV2.runBody_iff_slices | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `90b03cbcf87a5e9b` | V3 SIM.7 - deletes runBody_iff_slices |
| Midfall.LoweringV3.QuotientRows.q_blockProgS | Midfall.LoweringV3.QuotientRows | theorem | OPEN | ROOT | `46a6d2313958c004` | V3 ROW.Q - the quotientLin progress row for every render: same leaves plus existence through the numerator (qvm_validated_noBoundsFault, Qvm.lean:768) and CompleteSide for the challenge values the scope reads |
| Midfall.LoweringV3.QuotientRows.q_blockSim | Midfall.LoweringV3.QuotientRows | theorem | OPEN | ROOT | `a20144c23b1b3bf7` | V3 ROW.Q - the quotientLin simulation row for every render, route B (ROW.Q.3 RETIRED by D-QVM2; replacement QInterpRefinesSegment): leaves are ROW.Q.1 (qlin_split_loop, this file), ROW.Q.3 RETIRED by D-QVM2 (replacement QuotientInterp.QInterpRefinesSegment), ROW.Q.4 (the frame valuation) and the builder rows Qvm.lean:631/:698/:713/:768/:995; ROW.Q.5 is NOT stated because the six generated line families have no AST twin (OBJ.15 splices them through YulParse, PG-Q-OBJECT) |
| Midfall.LoweringV3.QuotientRows.qlin_split_loop | Midfall.LoweringV3.QuotientRows | theorem | OPEN | - | `5ccf3ecbb557d9e2` | V3 ROW.Q.1 - the split loop of the linearization scope (GeneratorRows.lean:875, ported verbatim): the squaring walk computing (x^(2^k-1), x^(2^k)); base case PROVED as qlin_split_loop_witness_base_case, pre-clause falsifier PROVED as qlin_split_loop_falsifier_pre_pins_x_pow_2i |
| Midfall.LoweringV3.TranscriptRows.tp_agrees | Midfall.LoweringV3.TranscriptRows | theorem | OPEN | ROOT | `f96314e92d89f7e0` | V3 ROW.TP.8 (WP A6) - TpPost reaches StageInv .transcript via xcript_total/MirrorAt/XcriptSlots (TranscriptRows.lean); SIM.10 dependency named |
| Midfall.LoweringV3.TranscriptRows.tp_blockProgS | Midfall.LoweringV3.TranscriptRows | theorem | OPEN | - | `8fb584b32507e2a2` | V3 ROW.TP.10 (WP A6) - the transcriptParser progress row, stated in its own module (TranscriptRows.lean); children ROW.TP.2-9 |
| Midfall.LoweringV3.TranscriptRows.tp_computes | Midfall.LoweringV3.TranscriptRows | theorem | OPEN | ROOT | `4f583684660177c8` | V3 ROW.TP.7 (WP A6) - the transcriptParser SEM row: every run from StageInv .vk reverts or exits in TpPost (TranscriptRows.lean); glue of ROW.TP.2-5 |
| Midfall.LoweringV3.TranscriptRows.tp_poison | Midfall.LoweringV3.TranscriptRows | theorem | OPEN | ROOT | `c90122ac9c6f46ca` | V3 ROW.TP.9 (WP A6) - the poisoned boundary always reverts on success = 0 (TranscriptRows.lean) |
| Midfall.LoweringV3.block_live_case_lagrange | Midfall.LoweringV3.BlockLive | theorem | OPEN | ROOT | `84c69293d388689d` | V3 TOT.1.c (WP A12/A4) - the lagrange CASE of block_live: the unconditional progress row over StageInv (BlockLive.lean). Reduction ready: block_live_of_blockProgS; the landed Rows.lag_blockProgS still carries LeanAccepts/CompleteSide, which block_live cannot supply |
| Midfall.LoweringV3.block_live_case_pcs | Midfall.LoweringV3.BlockLive | theorem | OPEN | ROOT | `2f771b2a123628a5` | V3 TOT.1.e (WP A12/A9-A10) - the pcs CASE of block_live: the unconditional progress row over StageInv (BlockLive.lean). Reduction ready: block_live_pcs; the landed Rows.pcs_blockProgS still carries LeanAccepts/CompleteSide, which block_live cannot supply |
| Midfall.LoweringV3.block_live_case_quotientLin | Midfall.LoweringV3.BlockLive | theorem | OPEN | ROOT | `7e5dadd16655c28b` | V3 TOT.1.d (WP A12/QVM) - the quotientLin CASE of block_live: the unconditional progress row over StageInv (BlockLive.lean). Reduction ready: block_live_quotientLin_of_prog; the landed q_blockProgS still carries LeanAccepts/CompleteSide, which block_live cannot supply |
| Midfall.LoweringV3.block_live_case_transcriptParser | Midfall.LoweringV3.BlockLive | theorem | OPEN | ROOT | `98d8cdf22a6a1ab3` | V3 TOT.1.b (WP A12/A6) - the transcriptParser CASE of block_live: the unconditional progress row over StageInv (BlockLive.lean). Reduction ready: block_live_transcriptParser_of_prog; the landed Rows.tp_blockProgS still carries LeanAccepts/CompleteSide, which block_live cannot supply |
| Midfall.LoweringV3.lag_blockProgS | Midfall.LoweringV3.Rows | theorem | OPEN | ROOT | `058350ca1fe5bc23` | V3 T3.9 (WP A4) - the lagrange progress row, the only reader of CompleteSide (Rows.lean); evidence GeneratorRows.lean:628 |
| Midfall.LoweringV3.lag_blockSim | Midfall.LoweringV3.Rows | theorem | OPEN | ROOT | `8747ef4852d79700` | V3 T3.9 (WP A4) - the lagrange simulation row (Rows.lean); children loops a-e, HLP.1.b, lag_agrees, lag_poison; evidence GeneratorRows.lean:621 |
| Midfall.LoweringV3.pcs_blockProgS | Midfall.LoweringV3.Rows | theorem | OPEN | ROOT | `d8237b277e31e5fe` | V3 ROW.PCS (WP A10) - the pcs progress row; decode half is ROW.PCS decode_exists (Rows.lean); evidence GeneratorRows.lean:1019 |
| Midfall.LoweringV3.pcs_blockSim | Midfall.LoweringV3.Rows | theorem | OPEN | ROOT | `2df9ec3dc55d4316` | V3 ROW.PCS (WP A10) - the pcs simulation row (Rows.lean); evidence GeneratorRows.lean:1013 |
| Midfall.LoweringV3.tp_blockProgS | Midfall.LoweringV3.Rows | theorem | OPEN | ROOT | `8fb584b32507e2a2` | V3 ROW.TP (WP A6) - the transcriptParser progress row (Rows.lean); evidence GeneratorRows.lean:830, leaf ROW.TP.10 |
| Midfall.LoweringW.completeAnyGasW_of_progs | Midfall.LoweringV3.CompositionW | theorem | OPEN | - | `7f41adee570c333f` | V3 SIM.2 + SIM.6 re-pointed at BlockProgSW, plus ST.13 (runBody_mono) and WID.19 - the widened completeness at EVERY total gas oracle (D-P72 clause 5); CompleteW is then PROVED from it by CompleteAnyGasW.toComplete |
| Midfall.LoweringW.lowering_correctW | Midfall.LoweringV3.WideningStages | theorem | OPEN | - | `ee3437aee8c7eb5d` | V3 WID.H - THE TARGET: the widened generic theorem, stated with the evaluator contract as a hypothesis (hQ : isExternal R -> EvalContracts R Q) because without it the statement is false for an arbitrary Q (ValidW.emptyBody + evalModel_emptyBody, both PROVED). WID.6 ties Q to the generated body, WID.17 proves EvalContracts, WID.H drops hQ; the decomposition is lowering_equivalenceW_of plus the row families SimContractsW/ProgContractsW, which RECON.3 discharges |
| Midfall.LoweringW.model_quotientMode | Midfall.LoweringV3.Widening | theorem | OPEN | - | `098ad7677cf85cd2` | V3 WID.H - generator fact (Artifacts.lean:534-537): the model externalises the quotient exactly when the flag says so. W12 witness: #eval at one embedded and one external model |
| Midfall.LoweringW.rejectsW_of_sims | Midfall.LoweringV3.CompositionW | theorem | OPEN | - | `c91cab7b200f723a` | V3 SIM.2 + SIM.6 re-pointed at BlockSimW, with WID.13/WID.14/WID.15/WID.16 - the widened rejection; the proof is the rejectsV3_of_sims shape of RECON.2 (Composition.lean:192) over StageInvW and LeanAcceptsAcc |
| Midfall.LoweringW.totalW_of_stages | Midfall.LoweringV3.CompositionW | theorem | OPEN | - | `4b2892579c73f914` | V3 SIM.2 + SIM.6 re-pointed at BlockProgSW, plus WID.19 and EvalBodyTotal (WideningStages.lean:492 via evalRel_answers) - the widened totality; a separate leaf, not a projection of conjunct 2, for the reason RECON.2 gives at Composition.lean:207-213 |
| Midfall.Statements.contractRef_noAcc | Midfall.Statements | theorem | OPEN | - | `c1a70bb473847dd8` | frozen statements (S1..S7 land later) |
| Midfall.Statements.verifyMsgs_iff_spec | Midfall.Statements | theorem | OPEN | - | `3085a73fec19d53f` | frozen statements (S1..S7 land later) |
| Midfall.Yul.Bridge.Evaluator.rel_worldLocal | Midfall.Yul.Bridge | theorem | OPEN | - | `f77b57bbcc305a5b` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall.Yul.Bridge.RunCommitted_keccakOf | Midfall.Yul.Bridge | theorem | OPEN | - | `2e73797d4a998bae` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall.Yul.Bridge.keccakOf_invariant | Midfall.Yul.Bridge | theorem | OPEN | - | `d30baf9a5253b859` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |

## Upstream sorries we must not depend on

From docs/ecosystem.md: ArkLib admits 112 proof sorries. None of them may
appear in the #print axioms closure of a Midfall theorem unless it is listed
here as an explicit assumption. The known hazards are:

* ArkLib/AGM/Basic.lean:189 AGM.Adversary.run - we write our own AGM.
* ArkLib/OracleReduction/FiatShamir/Basic.lean:173 fiatShamir_completeness -
  we prove the FS step ourselves (S4).
* Security/Implications.lean:49 and :189, all liftContext_*, all append_* -
  S2 must not route through these.

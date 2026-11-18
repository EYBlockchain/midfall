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
| Midfall.Halo2.Spec.accepts | Midfall.Halo2.Spec.Piop | def | OPEN | - | `6db1418cbda599b6` | Phase 4 (spec layer) |
| Midfall.Instances.PoseidonV2.poseidon_quotient_block | Midfall.Instances.PoseidonV2 | theorem | OPEN | ROOT | `f2571a03d4164a52` | V3 ROW.Q - the quotient row: the one block the generic hinge does not cover |
| Midfall.Instances.PoseidonV2.poseidon_rejects | Midfall.Instances.PoseidonV2 | theorem | OPEN | ROOT | `3e7a72dcd164821a` | V3 PL.H via rejectsV3_of_rows - V2 C.3 staged rejection contracts |
| Midfall.Instances.PoseidonV2.poseidon_valid | Midfall.Instances.PoseidonV2 | theorem | REFUTED | ROOT | `278d212235ac6153` | V3 PL.1 - deletes it: the negation poseidonRender_notValid is PROVED (REFUTED: as stated it proves False) |
| Midfall.Instances.PoseidonValid.poseidonValid_model | Midfall.Instances.PoseidonValid | theorem | OPEN | - | `512589e39c0f0f04` | V2 (PLAN-V2): C.4 Valid.model - no Inhabited Model, kernel cannot reduce poseidonModel |
| Midfall.Lowering.builder_segments_total | Midfall.Lowering.Qvm | theorem | OPEN | - | `19417891ad4c8eb2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.calldata_canonical | Midfall.Lowering.Calldata | theorem | OPEN | - | `93ce23c8ec4508b3` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.calldata_roundtrip | Midfall.Lowering.Calldata | theorem | OPEN | - | `2946ab985d3e04ff` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.decodeAcc_encode_pointPair | Midfall.Lowering.Accumulator | theorem | OPEN | - | `028ec007c2c32bbd` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.decodeAcc_injective | Midfall.Lowering.Accumulator | theorem | OPEN | - | `4b93d0d78ab51374` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.end_to_end_acc_complete | Midfall.Lowering.Obligations | theorem | VACUOUS | - | `5ecfad1c74fec97c` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.extcodehash_of_deployment | Midfall.Lowering.Surface | theorem | OPEN | - | `c9fe99e0842043ed` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.feToU256_frToRepr | Midfall.Lowering.VkDigest | theorem | OPEN | - | `114330cf0dcde246` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.finalPairing_acc_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `f54a5e65072fb645` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.finalPairing_progress_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `de274924b227a440` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.finalPairing_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `39f6b033b0de37f2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.identityCorrespondence_of_bridge | Midfall.Lowering.QvmFold | theorem | OPEN | - | `3a8ae8cd932416d2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.lagrange_progress_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `0c43c28a48d340d3` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.lagrange_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `71994fd83543a20d` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.lowering_equivalence_noAcc | Midfall.Lowering.Obligations | theorem | OPEN | - | `6a837e6c7e393c3d` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.partialProgress_not_of_alwaysReverts | Midfall.Lowering.Partials | theorem | OPEN | - | `be6592a893f09eb2` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.partialSound_of_alwaysReverts | Midfall.Lowering.Partials | theorem | OPEN | - | `a8d81d9728b159f8` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.pcs_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `cb944a2ab0dd5d56` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.quotientFold_matches_linearization | Midfall.Lowering.QvmFold | theorem | OPEN | - | `0c02c670544a79fb` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.quotientLin_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `1d49cb9e6cf29a90` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_certifier | Midfall.Lowering.Qvm | theorem | OPEN | - | `562667ac0251841e` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_identity | Midfall.Lowering.Qvm | theorem | OPEN | - | `4855c6b810d4ec8b` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_program | Midfall.Lowering.Qvm | theorem | OPEN | - | `872104589438bfc7` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_compile_correct_stream | Midfall.Lowering.QvmFold | theorem | OPEN | - | `190c993b2542362d` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.qvm_validated_noBoundsFault | Midfall.Lowering.Qvm | theorem | OPEN | - | `523df718aa0e2305` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.repack_spec_of_decodeRust | Midfall.Lowering.Calldata | theorem | OPEN | - | `e9ac280126ce661a` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.snapshotOf_prepareMsgs | Midfall.Lowering.Snapshot | theorem | OPEN | - | `a2557e7fe0a1f84a` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.toExec_fixedScalarCount | Midfall.Lowering.AccEncoding | theorem | OPEN | - | `df38b488380809ce` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.toExec_fullyCollapsed | Midfall.Lowering.AccEncoding | theorem | OPEN | - | `65e5bf121fe62b7b` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.toExec_validFor | Midfall.Lowering.AccEncoding | theorem | OPEN | - | `b742d844c7aa9ae4` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.transcriptParser_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `cd8f5ff36e0746fd` | P-SE: semantic equivalence obligations |
| Midfall.Lowering.vkLoading_spec | Midfall.Lowering.Partials | theorem | OPEN | - | `c2f09d7df1c9e765` | P-SE: semantic equivalence obligations |
| Midfall.LoweringV2.Blocks.FinalPairing.ec_pairing_contract | Midfall.LoweringV2.Blocks.FinalPairing | theorem | OPEN | - | `dd0af6f267ae0d8d` | V2 (PLAN-V2): FP.0 FinalPairing skeleton - P.1 algebra, T.4 staticcall, T.5 steps |
| Midfall.LoweringV2.Blocks.FinalPairing.fp_pairing_algebra | Midfall.LoweringV2.Blocks.FinalPairing | theorem | OPEN | - | `ff71682088fb8833` | V2 (PLAN-V2): FP.0 FinalPairing skeleton - P.1 algebra, T.4 staticcall, T.5 steps |
| Midfall.LoweringV2.Blocks.FinalPairing.fp_stmt_steps | Midfall.LoweringV2.Blocks.FinalPairing | theorem | OPEN | - | `3a5e133d052af026` | V2 (PLAN-V2): FP.0 FinalPairing skeleton - P.1 algebra, T.4 staticcall, T.5 steps |
| Midfall.LoweringV2.Blocks.VkLoading.vk_poison_walk | Midfall.LoweringV2.Blocks.VkLoading | theorem | OPEN | - | `26e8c971c0e3695b` | V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md |
| Midfall.LoweringV2.Blocks.VkLoading.vk_progress | Midfall.LoweringV2.Blocks.VkLoading | theorem | OPEN | - | `27383cf076f32568` | V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md |
| Midfall.LoweringV2.Blocks.VkLoading.vk_sound_clean | Midfall.LoweringV2.Blocks.VkLoading | theorem | OPEN | - | `af938e7c295cf4c2` | V2 (PLAN-V2): S.4/S.9 vkLoading row - Q0.x/Q1.x cards, see docs/QUEUE.md |
| Midfall.LoweringV2.blockContracts_of_valid | Midfall.LoweringV2.Blocks | theorem | OPEN | ROOT | `cad933e437381137` | V3 SIM.7 - deletes the old composition (RV-10: false as stated until RECON.1 PayloadAgrees) |
| Midfall.LoweringV2.bodyTotal_of_valid | Midfall.LoweringV2.Blocks | theorem | OPEN | ROOT | `567141948b3e3b83` | V3 ST.5 - TotalV3: the totality conjunct D-P64 (f) lands with the four-obligation composition; discharged by the exit-discipline scan (ST.10/ST.12) |
| Midfall.LoweringV2.end_to_end | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `937db535983dbffe` | V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md |
| Midfall.LoweringV2.hoist_prog_addr_indep | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `9b58bf8246b39da5` | V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md |
| Midfall.LoweringV2.inline_append | Midfall.LoweringV2.ProgramLemmas | theorem | OPEN | - | `60d11701168a999f` | V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md |
| Midfall.LoweringV2.noWriters_prog | Midfall.LoweringV2.Blocks | theorem | OPEN | ROOT | `2b62208f4c1f0276` | V3 ST.12 - scans_prog_addr_indep removes it |
| Midfall.LoweringV2.prefix_run_clean | Midfall.LoweringV2.Blocks | theorem | OPEN | ROOT | `4e5f39adb62c935e` | V3 SIM.7 - deletes prefix_run_clean |
| Midfall.LoweringV2.prog_slices_decomp | Midfall.LoweringV2.Blocks | theorem | OPEN | - | `7c068b01308bc4df` | V2 (PLAN-V2): Q0.x/Q1.x cards - see docs/QUEUE.md |
| Midfall.LoweringV2.rejects_of_not_accepts | Midfall.LoweringV2.Blocks | theorem | OPEN | ROOT | `126f21c9acf4e222` | V3 ST.5 - deletes rejects_of_not_accepts |
| Midfall.LoweringV2.runBody_iff_slices | Midfall.LoweringV2.Blocks | theorem | OPEN | ROOT | `90b03cbcf87a5e9b` | V3 SIM.7 - deletes runBody_iff_slices |
| Midfall.LoweringV3.prog_slices_decompV3 | Midfall.LoweringV3.Statements | theorem | OPEN | - | `65c280cbb3b3d180` | V3 ST.11 - restated structural decomposition. Experiment: inline_append five times against noShadowB, List.filterMap_append for hoist, and hoist (preSlice) = hoist (mainLocalsInlined) = [] |
| Midfall.LoweringV3.runBody_mono | Midfall.LoweringV3.Statements | theorem | OPEN | - | `789d844c4becf6c1` | V3 ST.13 - monotonicity in the call relation (Bridge layer). Experiment: induction on Step; the call relation occurs only in externalCall (EVMExec.lean), in a positive position |
| Midfall.LoweringV3.scans_prog_addr_indep | Midfall.LoweringV3.Statements | theorem | OPEN | - | `c86ac19db9538c53` | V3 ST.12 - the two scans ignore the addresses the wrapper binds as let literals. Experiment: same cost class as noWriters_prog (Blocks.lean:340), which it subsumes |
| Midfall.LoweringV3.twoOutcomes_of_exitDiscipline | Midfall.LoweringV3.Statements | theorem | OPEN | - | `01a1088791717d4a` | V3 ST.10 - replaces rejects_of_not_accepts (WP-M5c). Experiment: one induction on Step in the shape of Bridge.Run_worldEq_of_noWriters (Bridge.lean:1221), then Step.stmts_append_inv at the tail and mstore/ret by simp [stepOp] |
| Midfall.Statements.contractRef_noAcc | Midfall.Statements | theorem | OPEN | - | `c1a70bb473847dd8` | frozen statements (S1..S7 land later) |
| Midfall.Statements.verifyMsgs_iff_spec | Midfall.Statements | theorem | OPEN | - | `3085a73fec19d53f` | frozen statements (S1..S7 land later) |
| Midfall.Yul.Bridge.Evaluator.rel_worldLocal | Midfall.Yul.Bridge | theorem | OPEN | - | `f77b57bbcc305a5b` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall.Yul.Bridge.RunCommitted_keccakOf | Midfall.Yul.Bridge | theorem | OPEN | - | `2e73797d4a998bae` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall.Yul.Bridge.Run_worldEq_of_noWriters | Midfall.Yul.Bridge | theorem | OPEN | ROOT | `e15a14387c645048` | V3 SIM.5 - the shared Step induction (ST.10 cites it) |
| Midfall.Yul.Bridge.keccakOf_invariant | Midfall.Yul.Bridge | theorem | OPEN | - | `d30baf9a5253b859` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall.Yul.WpX.loadWord_storeWord | Midfall.Yul.WpX | theorem | OPEN | - | `e9369d152b5a2708` | V3 T3.5 - the word and memory layer: loadWord over storeWord at equal and disjoint 32-byte windows (cards.md:1312, :1319) |
| Midfall.Yul.WpX.mulmod_toFr | Midfall.Yul.WpX | theorem | OPEN | - | `6ceb8a7f24adad12` | V3 T3.8 - the field-arithmetic bridge: mulmod at qvmFrModulus is Fr multiplication (cards.md:1369, :1373) |

## Upstream sorries we must not depend on

From docs/ecosystem.md: ArkLib admits 112 proof sorries. None of them may
appear in the #print axioms closure of a Midfall theorem unless it is listed
here as an explicit assumption. The known hazards are:

* ArkLib/AGM/Basic.lean:189 AGM.Adversary.run - we write our own AGM.
* ArkLib/OracleReduction/FiatShamir/Basic.lean:173 fiatShamir_completeness -
  we prove the FS step ourselves (S4).
* Security/Implications.lean:49 and :189, all liftContext_*, all append_* -
  S2 must not route through these.

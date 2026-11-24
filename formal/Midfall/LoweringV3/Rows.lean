/-
  Midfall.LoweringV3.Rows

  PL.H0 step 4 - **GEN.5's ROW HALF, ABSORBED: THE FOURTEEN ROW STATEMENTS AND THE TWO BUNDLES THAT
  SPEND THEM.** Ported from the evidence `GeneratorRows.lean` at the V3 reading ROW.Q already uses:
  `hR : R.Valid` becomes `ValidV3 R`, and `hpins : SimPins R` plus the seven-law `G1CodecLaws`
  become `hcodec : G1CodecHeadlineLaws R.E.g1` - RECON.2's dissolution, now a projection of the
  headline's own hypotheses (`pins_from_valid_and_headlineLaws`). The quotient pair is NOT restated
  here: `q_blockSim`/`q_blockProgS` (QuotientRows.lean:191, :204) are already at this shape.

  THESE ARE LEAVES, NOT WORK. Each row is a REGISTERED sorry whose OWNER is the card named in its
  docstring; PL.H0 proves none of them (the card: "Do not prove or restate any row: owner cards prove
  the step-4 leaves IN PLACE, so their statement is the leaf's"). `sim_rows` and `prog_rows` are the
  PROVED glue that turns the fourteen into the two bundles the root consumes - `cases q` and nothing
  more - which is what makes `lowering_correct` reach its leaves through proved glue (D-P74).

  W12 FOR THE FAMILY. WITNESS: `gap_lowering_correct_witness_unexhibited` (GeneratorTheorem.lean) -
  `ValidV3` has no inhabitant the tree can name until WP B4, and D-P75 item 5 allows the named gap as
  the witness of a statement over `ValidV3`. FALSIFIER: the family's postconditions are not
  satisfiable by a fall-through or an empty program - `finSim_refutes_empty` (Stages.lean:692),
  `exitSim_refutes_normal_traceReturn` (:704) and `exitProg_refutes_normal_traceReturn` (:714), all
  PROVED at exactly these contracts, plus `q_blockSim_falsifier_*`/`q_blockProgS_falsifier_*` at the
  quotient shape. Per-row falsifiers land with the row's owner WP (consumer first).

  D-P71: no fixture in any statement. GEN.5's old target `LoweringV2/RowsGen.lean` is obsolete: the
  rows need `ValidV3`, which `LoweringV2` cannot import (cycle: LoweringV3/Statements.lean:32).
-/
import Midfall.LoweringV3.Composition
import Midfall.LoweringV3.QuotientRows
import Midfall.LoweringV3.TranscriptRows
import Midfall.LoweringV3.VkClean
import Midfall.LoweringV3.FpWire
import Midfall.LoweringV3.FpInvTransfer
import Midfall.LoweringV3.FpConsts
import Midfall.LoweringV3.FpClean
import Midfall.LoweringV3.FpG2Width
import Midfall.LoweringV3.FpFit
import Midfall.LoweringV3.LagrangeBlock
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.LoweringV2.Blocks.FinalPairing
import Midfall.Tools.ConeSorries
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. vkLoading (owner GEN.1, WP A3) -/

/-- **LEAF (GEN.1, WP A3): the vkLoading simulation row - PROVED.** Evidence `GeneratorRows.lean:1096`,
    at the V3 reading. WITNESS: `gap_lowering_correct_witness_unexhibited`. FALSIFIER: header.
    The proof is `VkClean.vk_blockSimV3`: `VkClean.vk_clean_walkV3` composes the 13-statement clean
    walk with `stageInv_vk_of_clean` (D-QVM1's fits turn the copy into `Inv .vk`'s payload window),
    and `VkClean.vk_poison_walkV3'` is `VkRow.vk_poison_walkV3`. Standard three, cone 0. -/
theorem vk_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.vkLoading H vkAddr (permissive (callsOf product)) g cd :=
  VkClean.vk_blockSimV3 R product hR H vkAddr cd g

/-- **LEAF (GEN.1, WP A3): the vkLoading progress row.** Evidence `GeneratorRows.lean:1103`.

    **D-GATE1 LANDED; THE ROW STILL NEEDS THE TWO-HALF WALK.** `BlockProgS` has no revert arm, so
    every run under `LeanAccepts` must exit normally at `StageInv .vk`. The signed PG-VKHEADER
    repair is in the frozen clause now: `PayloadAgrees.constantsLength : 11 ≤ R.pv.vk.constants.length`
    (D-GATE1, `design.md`), and `VkClean.pg_vkheader_of_valid` reads it off `ValidV3`. With it,
    `VkClean.vk_hdr_word_read_of_valid` proves, for every header slot `i ≤ numAccLimbBits`,

      loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) = payloadWord R.pv i

    at exactly the copy state the section-4 walk leaves (`hmem` is `stageInv_vk_of_clean`'s copy
    equation with D-QVM1's fits applied, `hcode` is `Frame.vkCode`); `MemoryPairs.vkMptr_shape_of_generated`
    supplies the `Nat`-built pointer shape the address equation needs. The six header table lookups
    are `VkClean.vkHeaderLookupsV3` (the model's header table is the template's:
    `MemoryPairs.vkHeader_default_of_generated`), and `VkClean.vk_hdr_read_values` packages the six
    words S3-S8 read as the literals `vk_sliceV3` compares them to. The two progress pins at
    `ValidV3` are `VkClean.consts_lookup_EXPECTED_VK_LENGTH_V3` / `_CODEHASH_WORD_V3`.

    **THE UNIVERSAL HALF IS PROVED** (`VkClean.vk_all_normal`, cone 0, standard three): every run
    of the slice from `StageInv .start`, under `LeanAccepts`, exits `.normal` at `StageInv .vk`.
    `vkBody_normal` carries the 13 statements with `vkS1_skipT` (`vkGuard_zero` from
    `Frame.vkCode`/`vkHash`/`vkNonEmpty`, `consts_lookup_EXPECTED_VK_LENGTH_V3`/`_CODEHASH_WORD_V3`
    and `projectedCodeHash`), the six headers with `vk_hdr_succ_one`/`vk_hdr_read_values`, the three
    calldata checks with `vk_cdl_succ_one`/`vk_cdsz_succ_one` (`envelope_calldata_facts` from
    `LeanAccepts`'s `Decoded`), and `vkS9_skipT` for S9/S13; `vk_clean_walkV3` supplies the
    `StageInv .vk` transfer.

    **THE EXISTENCE HALF IS ALSO PROVED** (`VkClean.vk_exists_run`): an explicit thirteen-statement
    `ExecStmts` run from any `StageInv .start` boundary, built by `vk_step_s1` (the false guard eval
    `vkGuard_eval_zero`), `vk_step_s2` (`extcodecopy`), six `vk_step_hdr` assigns,
    `vk_step_gate` for S9/S13, and `vk_step_cdl`/`vk_step_cdsz` for S10-S12. The row is
    `StmtsTotal = ⟨vk_exists_run, vk_all_normal⟩`; standard three, cone 0. -/
theorem vk_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.vkLoading H vkAddr product cd := by
  have hacc' := hacc
  exact ⟨VkClean.vk_exists_run (c := callsOf product) R hR H vkAddr cd
      (ExternalGas.ofFun fun _ => 0) hacc',
    VkClean.vk_all_normal (c := callsOf product) R hR H vkAddr cd
      (ExternalGas.ofFun fun _ => 0) hacc'⟩

/-! ## 2. transcriptParser (owner ROW.TP, WP A6) -/

/-- **ROW.TP, WP A6: the transcriptParser simulation row - PROVED HERE, FROM THE MODULE'S
    `tp_blockSim`.** The row glue is `TranscriptRows.tp_blockSim`, which is the evidence's own
    twelve-line argument spent on `tp_computes` / `tp_agrees` / `tp_poison`
    (`TranscriptRows.lean` section 4). Those three are still registered leaves of ROW.TP, so the
    row carries their cone; nothing is added to the row's statement and the `product` permit is
    the only dialect input. -/
theorem tp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.transcriptParser H vkAddr (permissive (callsOf product)) g cd :=
  TranscriptRows.tp_blockSim R product hR hcodec hpc H vkAddr cd g

/-- **LEAF (ROW.TP, WP A6): the transcriptParser progress row.** Evidence `GeneratorRows.lean:830`. -/
theorem tp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.transcriptParser H vkAddr product cd := by
  sorry

/-! ### T3.9 ROW ASSEMBLY STATUS (exact residual)

The lagrange rows cannot yet be assembled from the tree. The blockers are NOT only A5:

1. **T3.9.f leaf coverage is complete except the call.** The five loop contracts
   (`lag_sq_loop`, `lag_denoms_loop`, `lag_second_pass_loop`, `lag_lblind_loop`,
   `lag_instance_loop`) are `StmtsContractAll` for segments 3, 7, 13, 16, 18, and every other
   inner statement now has its own one-statement `StmtsContractAll`: 0/1/2 (`k`, `x`, `x_n`),
   4/5/6 (`omega`, `mptr`, `mptr_end`), 8/9 (`x_n_minus_1`, `mptr_end` store), 11/12 (`mptr`
   reset, `l_i_common`), 14/15 (`l_blind`, `l_i_cptr`), 17 (`instance_eval`), 19/20/21
   (`x_n_minus_1_inv`, `l_last`, `l_0`), and 22-27 (the six slot stores). Statement 10 (the
   `batch_invert` call) is the only inner statement not yet discharged; A5's
   `batch_invert_summary` now exists (`ModexpGeneral.lean:4331`), so what remains there is the
   caller-side `Step.callOk`/`ysetN` bridge, not a missing summary. Its exact inputs are:
   `batchInvertDecl`/`lookupFun funs "batch_invert" = some (decl, cenv)` with
   `decl.body = helperBody consts emitBatchInvertAt` and the five params/two rets (provable by
   `kernel_rfl`, as `EcPairing.ecPairing_lookup` does); the argument evaluation of
   `success, LAGRANGE_DENOMS_MPTR, mptr_end + 0x20, BATCH_INV_SCRATCH_MPTR, r`; the A5 pre's
   `MODEXP_GAS` lookup, `hsp` (`lagScratchFits`), the window fits (`LagWindowFits`) and the
   CANONICAL FIRST DENOMINATOR WORD `(loadWord st.memory C.D).toNat < blsR`; then
   `BatchInvertPost` -> `BatchInvertCallPost` through `VEnv.setMany`. The canonical-word fact is
   the named PG-BATCHINVERT(3) premise (it follows from `x ∉ domain` on the progress side, and
   is not implied by `LagPre` on the soundness side).
2. **T3.9.h `lag_poison`'s inner half is now landed** as `LagrangeBlock.lag_poison` (with
   `lag_body_poison_contract` / `lag_block_poison_contract` / `lag_guard_poison_contract`): the
   body's `restore` keeps `success`/`lagrange_precompile_failed` (the two non-membership facts
   in 5d), and the guard reverts from `(0, 0)`. It is conditional on a `LagInnerContract` at
   `C.succ = 0`, which is exactly the remaining whole-block composition. The Render-level
   assembly `lagBlockPoisonContract_of_inner` below reduces `LagBlockPoisonContract` to the two
   named bridges `hpre : Poisoned → LagPre C` and `hinner : LagInnerContract C …`.
3. **PG-LAG-FITS is now an exact named predicate.** `LagrangeBlock.LagWindowFits` carries the
   denominator window end `D + 32(n+m+1) < 2^256`, the six slot fits, the four window
   disjointness clauses and the six pairwise slot separations; `lag_inner_contract_post_of_fits`
   derives `LagInnerContract` from it (all weaker arithmetic is `omega`). It is NOT a
   `ValidV3` projection: `MetaCountsBound` (`Generator/Certified.lean:207`) bounds `m` through
   `rotationLast < 2^32`, but nothing bounds `n = numInstances`; the generator's input predicate
   `CountBound` (`Certified.lean:286`) has `instances < 2^32` and `metaCounts`, and with a
   layout address below `2^200` it gives the denominator end
   (`LagrangeBlock.lagDenomEnd_of_countBound`). `Render` does not retain `CountBound`, so this
   remains an INPUT predicate, not a row/root hypothesis. The clean post also needs T3.9.g's
   actual premises: `lag_agrees` is landed (`LagrangeRows.lean:3515`) but consumes
   `hl : snapshotLagrangeStep = .ok l`, `hxn`, `hinst` and the `XcriptAlgebraRun`/`XcriptG1`
   parser facts, none of which `ValidV3` supplies.

Therefore `lag_blockSim`/`lag_blockProgS` remain the existing registered leaves; no row hypothesis
has been added and no new `sorry` is introduced here. When 1–3 land, the rows are pure glue.
-/

/-! ## 3. lagrange (owner T3.9, WP A4) -/

/-- **THE RENDER-LEVEL `LagBlockPoisonContract` ASSEMBLY.** The inner and guard units are
    `LagrangeBlock.lag_poison`; this theorem rewrites the real slice by
    `lag_slice`/`lag_slice_decomp` and supplies the three render facts (`ERR_PROOF_REJECTED`,
    `success` absent, the `fail` lookup). The two remaining bridges are explicit arguments, not
    row hypotheses: `hpre` is `Poisoned → LagPre C` (the `LagCfg`/frame bridge) and `hinner` is
    the whole-block contract at `C.succ = 0` (the T3.9.f composition under PG-LAG-FITS). -/
theorem lagBlockPoisonContract_of_inner (R : Render p G₁ G₂ Gₜ)
    (product : PairingProduct) (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (g : ExternalGas)
    (C : LagrangeBlock.LagCfg R.consts cd R.pv.k R.pv.numInstances R.pv.numNegLagranges)
    (hpre : ∀ V st, Poisoned R H vkAddr cd
      (c := permissive (callsOf product)) (g := g) V st → LagrangeBlock.LagPre C V st)
    (hinner : LagrangeBlock.LagInnerContract C (hoist
      (Bridge.Dialect (permissive (callsOf product)) g)
      (LagrangeRows.lagInner R.consts R.pv.k R.pv.numInstances R.pv.numNegLagranges) ::
      R.scope (permissive (callsOf product)) g))
    (hsucc0 : C.succ = 0) :
    LagrangeBlock.LagBlockPoisonContract R product g H vkAddr cd := by
  intro V st hpois V' st' o hrun
  rw [LagrangeRows.lag_slice, LagrangeBlock.lag_slice_decomp] at hrun
  exact LagrangeBlock.lag_poison (C := C) hinner hsucc0
    (consts_errProof_of_validV3 hR)
    (Midfall.LoweringV2.Blocks.TraceReturn.consts_succ_none R)
    (Midfall.LoweringV2.Blocks.TraceReturn.fail_lookup R)
    V st (hpre V st hpois) V' st' o hrun

#assert_axioms lagBlockPoisonContract_of_inner [propext, Classical.choice, Quot.sound]

/-- **THE `BlockSim` POISON CONJUNCT FOR LAGRANGE, FROM THE ZERO-SUCCESS COMPOSITION.** This is
    the second `StmtsContractAll` of `BlockSimAt R .lagrange`: every run from a poisoned boundary
    halts reverted. It is `LagrangeBlock.lagBlockPoisonContract_of_fits_zero`, whose inputs are the
    standard table lookups, PG-LAG-FITS and the two counts; no `Poisoned → LagPre C` bridge and no
    clean-parser fact is used. -/
theorem lag_poison_walk_of_fits_zero (R : Render p G₁ G₂ Gₜ)
    (product : PairingProduct) (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (g : ExternalGas)
    (C : LagrangeBlock.LagCfg R.consts cd R.pv.k R.pv.numInstances R.pv.numNegLagranges)
    (hr : R.consts.lookup "r" = none)
    (hX : R.consts.lookup "X_MPTR" = some C.aX)
    (hO : R.consts.lookup "OMEGA_MPTR" = some C.aO)
    (hL : R.consts.lookup "OMEGA_INV_TO_L_MPTR" = some C.aL)
    (hN : R.consts.lookup "N_INV_MPTR" = some C.aN)
    (hI : R.consts.lookup "INSTANCE_CPTR" = some C.aI)
    (hD : R.consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D)
    (hS : R.consts.lookup "BATCH_INV_SCRATCH_MPTR" = some C.s)
    (hXN : R.consts.lookup "X_N_MPTR" = some C.aXN)
    (hXN1 : R.consts.lookup "X_N_MINUS_1_INV_MPTR" = some C.aXN1)
    (hLL : R.consts.lookup "L_LAST_MPTR" = some C.aLL)
    (hLB : R.consts.lookup "L_BLIND_MPTR" = some C.aLB)
    (hL0 : R.consts.lookup "L_0_MPTR" = some C.aL0)
    (hIE : R.consts.lookup "INSTANCE_EVAL_MPTR" = some C.aIE)
    (hfits : LagrangeBlock.LagWindowFits C)
    (hm : 2 ≤ R.pv.numNegLagranges) (hn : 1 ≤ R.pv.numInstances)
    (hk : R.pv.k < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g)
      (R.scope (permissive (callsOf product)) g) (R.slice Partial.lagrange)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (Partial.lagrange ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) := by
  intro V st hpois V' st' o hrun
  exact Or.inl (LagrangeBlock.lagBlockPoisonContract_of_fits_zero R product hR H vkAddr cd g
    C hr hX hO hL hN hI hD hS hXN hXN1 hLL hLB hL0 hIE hfits hm hn hk
    V st hpois V' st' o hrun)

#assert_axioms lag_poison_walk_of_fits_zero [propext, Classical.choice, Quot.sound]


/-- **LEAF (T3.9, WP A4): the lagrange simulation row.** Evidence `GeneratorRows.lean:621`; children
    are loops a-e, HLP.1.b, `lag_agrees`, `lag_poison`. -/
theorem lag_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.lagrange H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **LEAF (T3.9, WP A4): the lagrange progress row** - the only reader of `CompleteSide`
    (`xⁿ ≠ 1`, `x ≠ ωⁱ`). Evidence `GeneratorRows.lean:628`. -/
theorem lag_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.lagrange H vkAddr product cd := by
  sorry

/-! ## 4. pcs (owner ROW.PCS, WP A9/A10) -/

/-- **LEAF (ROW.PCS, WP A10): the pcs simulation row.** Evidence `GeneratorRows.lean:1013`.

    THE ASSEMBLY SIDE IS IN `PcsRows`. `PcsRows.pcs_slice_of_ok` gives the one-outer-block
    shape; `PcsRows.computationsAst_ok_shape` names the exact emitted block list (block 1,
    optional block 2, the per-set block-3 list, block 4, block 5, block 6);
    `PcsRows.pcs_slice_body_contract_of_blocks` composes per-block `StmtContractAll`s at the
    fuel-62 inlined terms the slice carries. What is still missing is semantics, not glue:
    the whole `pcsBlock3Ast` contract (straight + rolled), `pcsBlock5Ast` (x4 powers, v fold,
    MSM/linearization staging, the `0x0c` call), `pcsBlock6Ast` (two `0x0c` MSM-1 and two
    `0x0b` G1ADD calls), the fuel-62 inlined faces of blocks 1 and 4 (the landed `pcs_b1_sem`
    and `pcsBlock_contract` are the raw ASTs), the coverage/ALG leaves, and PG-PCS-EMIT
    (fault-freedom/non-emptiness of `computationsAst`, not implied by `ValidV3`). No row
    hypothesis is taken here. -/
theorem pcs_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.pcs H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **LEAF (ROW.PCS, WP A10): the pcs progress row.** Evidence `GeneratorRows.lean:1019`; its decode
    half is ROW.PCS's `decode_exists`. The unconditional progress half additionally needs the
    explicit whole-slice run (block 5/6 included) and the `StageInv .pcs` transfer; see the
    `pcs_blockSim` docstring for the exact missing children. -/
theorem pcs_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.pcs H vkAddr product cd := by
  sorry

/-! ## 5. finalPairing (owner ROW.FP, WP A11) -/

/-- The V3 face of `VkLoading.pv_hasAcc_false`: `ValidV3` carries the same `supported.noAcc` and
    `inputs.accEncoding` clauses as the frozen `Render.Valid`, and `VkLoading`'s proof used only
    those. -/
theorem pv_hasAcc_falseV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.pv.hasAccumulator = false := by
  classical
  have h : R.cfg.accumulator = none := hR.supported.noAcc
  have h1 : R.pv = planViewOf R.plan R.model none := by
    show planViewOf R.plan R.model R.cfg.accumulator = _
    rw [h]
  rw [h1, planViewOf, planViewWithAccumulator]
  rfl

/-- The finalPairing slice read off the emitter at `ValidV3` (the V2 `fp_slice` uses `Render.Valid`;
    `ValidV3` is a parallel copy, so the row needs this face). -/
theorem fp_sliceV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.slice Partial.finalPairing =
      [Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
          [Stmt.exprStmt (Expr.call "fail"
            [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])],
        Stmt.assign ["success"] (Expr.call "ec_pairing"
          [Expr.var "success",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"])] := by
  have hacc : R.pv.hasAccumulator = false := pv_hasAcc_falseV3 R hR
  show Inline.inlineContractConstants R.consts
    (Midfall.Lowering.GenAst.emitPartial R.pv Partial.finalPairing) = _
  rw [Midfall.Lowering.GenAst.emitPartial, Midfall.Lowering.GenAst.emitFinalPairing, hacc]
  rw [Midfall.LoweringV2.Blocks.FinalPairing.fp_slice_raw]
  simp only [Midfall.LoweringV2.Blocks.FinalPairing.fpVal,
    Midfall.LoweringV2.Blocks.TraceReturn.consts_succ_none]

#assert_axioms Midfall.LoweringV3.pv_hasAcc_falseV3
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.fp_sliceV3
  [propext, Classical.choice, Quot.sound] native []

/-- **THE POISON ARM AT `ValidV3`.** From `Frame ∧ success = 0` the slice's first guard
    reverts; the V2 `fp_stmt_steps` only used `fp_slice`, so this is the same proof at the
    V3 face of the slice equation. -/
theorem fp_stmt_stepsV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.finalPairing)
        (fun V st => Midfall.LoweringV2.Frame R H vkAddr cd V st ∧
          VEnv.get V "success" = some (0 : U256))
        (fun _ _ V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
          (o = .normal ∧ Midfall.LoweringV2.Poisoned R H vkAddr cd V' st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨_hframe, hsucc⟩ := hpre
  rw [fp_sliceV3 R hR] at hrun
  have hfail : lookupFun (R.scope c g) "fail" =
      some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, R.scope c g) :=
    Midfall.LoweringV2.Blocks.TraceReturn.fail_lookup R
  have hfail' : lookupFun (hoist (Bridge.Dialect c g)
      [Stmt.exprStmt (Expr.call "fail"
        [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])] ::
        R.scope c g) "fail" = some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, R.scope c g) := by
    change lookupFun (R.scope c g) "fail" =
      some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, R.scope c g)
    exact hfail
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V₁, st₁, h₁, _⟩ | ⟨h₁, hne⟩
  · exact (Midfall.LoweringV2.Blocks.FinalPairing.fp_guard_normal_impossible (R := R) hfail' hsucc h₁).elim
  · obtain ⟨Vb, hbody⟩ := Midfall.LoweringV2.Blocks.FinalPairing.fp_guard_fire
      (funs := R.scope c g) hsucc h₁
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hbody with
        ⟨V₂, st₂, h₂, _⟩ | ⟨h₂, _⟩
    · obtain ⟨ho, _⟩ := Midfall.LoweringV2.Blocks.FinalPairing.fp_fail_reverts
        (e := Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED")
        (funs := hoist (Bridge.Dialect c g)
          [Stmt.exprStmt (Expr.call "fail"
            [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])] ::
            R.scope c g)
        (fun st₁ st₂ hh => Midfall.LoweringV2.Blocks.FinalPairing.fpErr_ne_halts hh) hfail' h₂
      exact absurd ho (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
    · obtain ⟨ho, hrev⟩ := Midfall.LoweringV2.Blocks.FinalPairing.fp_fail_reverts
        (e := Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED")
        (funs := hoist (Bridge.Dialect c g)
          [Stmt.exprStmt (Expr.call "fail"
            [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])] ::
            R.scope c g)
        (fun st₁ st₂ hh => Midfall.LoweringV2.Blocks.FinalPairing.fpErr_ne_halts hh) hfail' h₂
      exact Or.inl ⟨ho, hrev⟩

#assert_axioms Midfall.LoweringV3.fp_stmt_stepsV3
  [propext, Classical.choice, Quot.sound] native []


/-- `iszero(1)` evaluates to the literal 0. -/
theorem fp_iszero_one_val {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {r : EResult (Bridge.Dialect c g)}
    (hs : VEnv.get V "success" = some (1 : U256))
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var "success"]) r) : r = .vals [0] st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var hget =>
                  simp_all [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w]
                  exact hbi.1.symm
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var hget => simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w] at hbi
  | builtinArgsHalt hargs =>
      exact (Midfall.LoweringV2.Blocks.TraceReturn.trArgs1_halt_inv hargs
        (fun st₁ hh => Midfall.LoweringV2.Blocks.TraceReturn.trExprVar_ne_halts hh)).elim

/-- The clean call at a fixed state, with the whole render instantiation discharged:
    constants, declaration, source slices, scratch/source disjointness and the fits. -/
theorem fp_call_at_clean (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (S : Snapshot p G₁ G₂ Gₜ)
    (st : EvmState)
    (hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes)
    (hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n)
    (hRpin : bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128 =
      R.E.g1.toEip S.c.dual.right.eval)
    (hLpin : bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128 =
      R.E.g1.toEip S.c.dual.left.eval)
    (g : ExternalGas) :
    ∀ (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g))
      (r : EResult (Bridge.Dialect (permissive (callsOf product)) g)),
      VEnv.get V "success" = some (1 : U256) →
      EvalExpr (Bridge.Dialect (permissive (callsOf product)) g)
        (R.scope (permissive (callsOf product)) g) V st
        (Expr.call "ec_pairing"
          [Expr.var "success",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) r →
      (∃ st', r = .vals [1] st' ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, x < R.pv.memory.finalPairingScratchMptr ∨
          R.pv.memory.finalPairingScratchMptr + 768 ≤ x → st'.memory x = st.memory x) ∧
        product (Midfall.LoweringV2.Blocks.FinalPairing.fpFrame R S) = true) ∨
      (∃ st', r = .halt st' ∧ Midfall.LoweringV2.Reverted st') := by
  intro V r hsucc hev
  have hRhs : Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR" =
      Expr.lit (.number (cAddr R.pv.memory.pairingRhsMptr)) := by
    unfold Midfall.LoweringV2.Blocks.FinalPairing.fpVal
    rw [consts_lookup_PAIRING_RHS_MPTR R hR]
  have hLhs : Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR" =
      Expr.lit (.number (cAddr R.pv.memory.pairingLhsMptr)) := by
    unfold Midfall.LoweringV2.Blocks.FinalPairing.fpVal
    rw [consts_lookup_PAIRING_LHS_MPTR R hR]
  rw [hRhs, hLhs] at hev
  -- the declaration, its literal body and the fail lookup
  have hdecl := Midfall.LoweringV3.ecPairingDecl_eq_lit R hR
    (permissive (callsOf product)) g
  have hlook := Midfall.LoweringV2.Blocks.EcPairing.ecPairing_lookup (R := R)
    (c := permissive (callsOf product)) (g := g)
  have hfail := Midfall.LoweringV2.Blocks.TraceReturn.fail_lookup (R := R)
    (c := permissive (callsOf product)) (g := g)
  -- the four fits and the scratch constant
  have hfitR := pairingRhsMptr_toNat_of_valid R hR
  have hfitL := pairingLhsMptr_toNat_of_valid R hR
  have hfit := PG_PAIRINGFIT_of_valid R hR
  have hfp := generated_finalPairingScratchMptr R hR
  have hscratchWin : Midfall.Lowering.GenAst.pairingScratchOf R.pv + 768 < 2 ^ 256 := by
    unfold Midfall.Lowering.GenAst.pairingScratchOf
    rw [hfp]
    have : finalPairingScratchStart = 0x1240 := by decide
    omega
  -- the G2 slots are the params' encodings
  have hslots : vkG2Words R.pv vkG2BaseSlot = R.encG2 (R.params.nG2Prepared)⁻¹ ∧
      vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹ := by
    refine ⟨?_, ?_⟩
    · rw [hR.env.nG2, inv_inv]
      exact hR.payload.g2Base
    · rw [hR.env.sG2]
      exact hR.payload.negSG2
  -- the two G2 source slices
  have hGB := bytesAt_vkG2Base_of_valid R hR product hpc st hpayload hptr
  have hGN := bytesAt_vkNegSG2Base_of_valid R hR product hpc st hpayload hptr
  -- the floors
  have hvkFloor := generated_vkMptr_floor R hR
  have hthetaFloor := generated_theta_floor R hR
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, hvk, -⟩ :=
    plan_size_of_generated hR.generated
  have hthetaEq : ptrAddr R.pv.memory.thetaMptr =
      thetaStartOf meta_ R.pv.vk vkMptr := by
    rw [hmem, new_thetaMptr]
    exact MemoryPairs.ptrAddr_valueFromNat _
  have hthetaFloor' : 0x1560 ≤ thetaStartOf meta_ R.pv.vk vkMptr := by
    rw [← hthetaEq]; exact hthetaFloor
  have hcl : cAddr R.pv.memory.pairingLhsMptr = ptrAddr R.pv.memory.pairingLhsMptr := rfl
  have hcr : cAddr R.pv.memory.pairingRhsMptr = ptrAddr R.pv.memory.pairingRhsMptr := rfl
  have hcg : cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) =
      ptrAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) := rfl
  have hcn : cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) =
      ptrAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) := rfl
  have hlhsEq : cAddr R.pv.memory.pairingLhsMptr =
      thetaStartOf meta_ R.pv.vk vkMptr + 44 * Midfall.Generator.wordBytes := by
    rw [hmem]
    exact pairingLhsMptr_eq meta_ R.pv.vk vkMptr config
  have hrhsEq : cAddr R.pv.memory.pairingRhsMptr =
      thetaStartOf meta_ R.pv.vk vkMptr + 48 * Midfall.Generator.wordBytes := by
    rw [hmem]
    exact pairingRhsMptr_eq meta_ R.pv.vk vkMptr config
  have hvh := MemoryPairs.vkHeader_default_of_generated hR.generated
  have hvkAdd : ptrAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) =
      ptrAddr R.pv.memory.vkMptr + Midfall.Generator.wordBytes * 15 := by
    rw [Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer _ _ hptr, hvh]
    rfl
  have hvkAdd' : ptrAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) =
      ptrAddr R.pv.memory.vkMptr + Midfall.Generator.wordBytes * 23 := by
    rw [Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer _ _ hptr, hvh]
    rfl
  have hsrc1 : bytesAt st (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr)).toNat 128 =
      R.E.g1.toEip S.c.dual.right.eval := by
    rw [hfitR]; exact hRpin
  have hsrc2 : bytesAt st
      (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) % 2^256) 256 =
      vkG2Words R.pv vkG2BaseSlot := by
    rw [Nat.mod_eq_of_lt hfit.2.2.1]
    exact hGB
  have hsrc3 : bytesAt st (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)).toNat 128 =
      R.E.g1.toEip S.c.dual.left.eval := by
    rw [hfitL]; exact hLpin
  have hsrc4 : bytesAt st
      (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) % 2^256) 256 =
      vkG2Words R.pv vkNegSG2BaseSlot := by
    rw [Nat.mod_eq_of_lt hfit.2.2.2]
    exact hGN
  -- the four source windows are above the scratch window
  have hdisj1 : (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) + 768 ≤
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr)).toNat ∨
      (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr)).toNat + 128 ≤
        (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) := by
    left
    unfold Midfall.Lowering.GenAst.pairingScratchOf
    have hrhsP : ptrAddr R.pv.memory.pairingRhsMptr =
        thetaStartOf meta_ R.pv.vk vkMptr + 48 * Midfall.Generator.wordBytes := by
      rw [← hcr]; exact hrhsEq
    rw [hfp, hfitR, hrhsP]
    have h0 : finalPairingScratchStart = 0x1240 := by decide
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hw] at *
    omega
  have hdisj2 : (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) + 768 ≤
        (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) % 2^256) ∨
      (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) % 2^256) + 256 ≤
        (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) := by
    left
    unfold Midfall.Lowering.GenAst.pairingScratchOf
    rw [hfp, Nat.mod_eq_of_lt hfit.2.2.1, hcg, hvkAdd]
    have h0 : finalPairingScratchStart = 0x1240 := by decide
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hw] at *
    omega
  have hdisj3 : (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) + 768 ≤
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)).toNat ∨
      (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)).toNat + 128 ≤
        (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) := by
    left
    unfold Midfall.Lowering.GenAst.pairingScratchOf
    have hlhsP : ptrAddr R.pv.memory.pairingLhsMptr =
        thetaStartOf meta_ R.pv.vk vkMptr + 44 * Midfall.Generator.wordBytes := by
      rw [← hcl]; exact hlhsEq
    rw [hfp, hfitL, hlhsP]
    have h0 : finalPairingScratchStart = 0x1240 := by decide
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hw] at *
    omega
  have hdisj4 : (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) + 768 ≤
        (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) % 2^256) ∨
      (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) % 2^256) + 256 ≤
        (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) := by
    left
    unfold Midfall.Lowering.GenAst.pairingScratchOf
    rw [hfp, Nat.mod_eq_of_lt hfit.2.2.2, hcn, hvkAdd']
    have h0 : finalPairingScratchStart = 0x1240 := by decide
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hw] at *
    omega
  -- now apply the call contract
  have hc := Midfall.LoweringV3.ecPairing_call_clean_at (g := g) product
    (R.scope (permissive (callsOf product)) g)
    (decl := Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
      (permissive (callsOf product)) g)
    (cenv := R.scope (permissive (callsOf product)) g)
    (cenv' := R.scope (permissive (callsOf product)) g)
    (scratch := Midfall.Lowering.GenAst.pairingScratchOf R.pv)
    (g2 := cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base))
    (neg := cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base))
    (gas := R.model.templateConstants.gas.pairingTwoPair)
    (errPre := 0x84e81692) (errProof := 0xc3b0d8cd)
    (rhsNat := cAddr R.pv.memory.pairingRhsMptr)
    (lhsNat := cAddr R.pv.memory.pairingLhsMptr)
    (LA := R.E.g1.toEip S.c.dual.right.eval)
    (GB := vkG2Words R.pv vkG2BaseSlot)
    (LB := R.E.g1.toEip S.c.dual.left.eval)
    (GN := vkG2Words R.pv vkNegSG2BaseSlot)
    (st := st)
    hlook (by rw [hdecl]) (by rw [hdecl]) (by rw [hdecl]) hfail
    hsrc1 hsrc2 hsrc3 hsrc4 hdisj1 hdisj2 hdisj3 hdisj4
    hfit.2.2.1 hfit.2.2.2 hscratchWin
  -- rewrite the contract's width window to the render's scratch pointer
  have hwin : (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) =
      R.pv.memory.finalPairingScratchMptr := by
    unfold Midfall.Lowering.GenAst.pairingScratchOf
    rw [hfp]
    have h0 : finalPairingScratchStart = 0x1240 := by decide
    exact Nat.mod_eq_of_lt (by omega)
  have hc' := hc V r hsucc hev
  rcases hc' with ⟨st', hv, henv, hhalt, hmem, hprod⟩ | hhalt'
  · refine Or.inl ⟨st', hv, henv, hhalt, ?_, ?_⟩
    · intro x hx
      have hx' : x < (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) ∨
          (Midfall.Lowering.GenAst.pairingScratchOf R.pv % 2^256) + 768 ≤ x := by
        rw [hwin]; exact hx
      exact hmem x hx'
    · -- identify the wire frame with `fpFrame`
      rw [hslots.1, hslots.2] at hprod
      simpa [Midfall.LoweringV2.Blocks.FinalPairing.fpFrame] using hprod
  · exact Or.inr hhalt'


/-- The clean call contract with the result inferred from the `EvalExpr`. -/
theorem fp_call_at_clean_apply (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (S : Snapshot p G₁ G₂ Gₜ)
    (st : EvmState)
    (hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes)
    (hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n)
    (hRpin : bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128 =
      R.E.g1.toEip S.c.dual.right.eval)
    (hLpin : bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128 =
      R.E.g1.toEip S.c.dual.left.eval)
    (g : ExternalGas)
    {V : VEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    {r : EResult (Bridge.Dialect (permissive (callsOf product)) g)}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hev : EvalExpr (Bridge.Dialect (permissive (callsOf product)) g)
      (R.scope (permissive (callsOf product)) g) V st
      (Expr.call "ec_pairing"
        [Expr.var "success",
         Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
         Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) r) :
    (∃ st', r = .vals [1] st' ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
      (∀ x, x < R.pv.memory.finalPairingScratchMptr ∨
        R.pv.memory.finalPairingScratchMptr + 768 ≤ x → st'.memory x = st.memory x) ∧
      product (Midfall.LoweringV2.Blocks.FinalPairing.fpFrame R S) = true) ∨
    (∃ st', r = .halt st' ∧ Midfall.LoweringV2.Reverted st') :=
  fp_call_at_clean R product hR hpc S st hpayload hptr hRpin hLpin g V r hsucc hev

/-- A decoding is unique in the calldata. -/
theorem fp_decoded_unique {R : Render p G₁ G₂ Gₜ} {cd : Bytes}
    {ms ms' : List (Msg (Fr p) G₁)} {instW instW' : Array Word256}
    {inst inst' : Array (Fr p)}
    (h : Decoded R cd ms instW inst) (h' : Decoded R cd ms' instW' inst') :
    ms = ms' ∧ instW = instW' ∧ inst = inst' := by
  obtain ⟨hd, hi⟩ := h
  obtain ⟨hd', hi'⟩ := h'
  rw [hd] at hd'
  have hpair : (ms, instW) = (ms', instW') := Option.some.inj hd'
  have h1 : ms = ms' := congrArg Prod.fst hpair
  have h2 : instW = instW' := congrArg Prod.snd hpair
  subst h1
  subst h2
  rw [hi] at hi'
  exact ⟨rfl, rfl, Option.some.inj hi'⟩

/-- One decoding's prefix and invariant give `Agree` (for all decodings: there is only one). -/
theorem fp_agree_of_one {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes} {k : Checkpoint}
    {c : ExternalCalls} {g : ExternalGas} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    {S : Snapshot p G₁ G₂ Gₜ} (hdec : Decoded R cd ms instW inst)
    (hS : leanStage R H inst ms k = .ok S)
    (hinv : Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st) :
    Agree R H cd k V st := by
  intro ms' instW' inst' hdec'
  obtain ⟨rfl, rfl, rfl⟩ := fp_decoded_unique hdec hdec'
  exact ⟨S, hS, hinv⟩

/-- At `success = 1` every run of the slice's guard is normal and leaves the state alone. -/
theorem fp_guard_norm_inv {R : Render p G₁ G₂ Gₜ} {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (hs : VEnv.get V "success" = some (1 : U256))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
        [Stmt.exprStmt (Expr.call "fail"
          [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])])
      V' st' o) :
    V' = V ∧ st' = st ∧ o = .normal := by
  cases h with
  | ifTrue hc hgt _ =>
      have h0 := fp_iszero_one_val hs hc
      cases h0
      exact absurd rfl hgt
  | ifFalse hc _ =>
      have h0 := fp_iszero_one_val hs hc
      cases h0
      exact ⟨rfl, rfl, rfl⟩
  | ifHalt hc =>
      exact (Midfall.LoweringV2.Blocks.FinalPairing.fp_iszero_ne_halts hc).elim


set_option maxHeartbeats 4000000
/-- **LEAF (ROW.FP, WP A11): the finalPairing simulation row.** Evidence `GeneratorRows.lean:1077`;
    children are `ec_pairing_sem`, `fp_pairing_algebra`, `fp_poison`. -/
theorem fp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.finalPairing H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨hframe, hsucc, -, hraw, -, hagree⟩ := hpre
    have hrawP : LeanRaw R cd Checkpoint.pairing := hraw
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hstage, hinv⟩ := hagree ms instW inst hdec
    have hsnap : snapshotOf R.E H R.vk inst ms none = .ok S := hstage
    obtain ⟨hRpin, hLpin⟩ := inv_pcs_pairing_pins (calls := permissive (callsOf product))
      (gas := g) (E := R.E) (params := R.params) (PV := R.pv) (S := S) hinv
    have hpayload := inv_pcs_vk_payload (calls := permissive (callsOf product))
      (gas := g) (E := R.E) (params := R.params) (PV := R.pv) (S := S) hinv
    obtain ⟨meta_, vkMptr, config, vkBase, hmem, hvk, -⟩ :=
      plan_size_of_generated hR.generated
    have hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n := by
      refine ⟨vkBase, ?_⟩
      rw [hmem, MemoryPairs.new_vkMptr, hvk]
      rfl
    rw [fp_sliceV3 R hR] at hrun
    rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
        ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
    · obtain ⟨hgV, hgst, hgo⟩ := fp_guard_norm_inv (R := R)
        (c := permissive (callsOf product)) (g := g) hsucc h1
      rw [hgV, hgst] at hrest
      rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest with
          ⟨V2, st2, h2, hnil⟩ | ⟨h2, hne2⟩
      · cases hnil
        cases h2 with
        | assignVal hev hlen =>
            have hcase := fp_call_at_clean_apply R product hR hpc S st hpayload hptr hRpin hLpin g
              hsucc hev
            rcases hcase with
              ⟨stc, hv, henv, hhalt, hmem', hprod⟩ | ⟨stc, hv, _⟩
            · cases hv
              trace_state
              exact Or.inr (Or.inl ⟨rfl, by
                have hset : VEnv.setMany V ["success"] [1] = VEnv.set V "success" (1 : U256) := rfl
                have hframe' : Midfall.LoweringV2.Frame R H vkAddr cd
                    (VEnv.setMany V ["success"] [1]) st' := by
                  rw [hset]
                  exact Frame_env_congr
                    (Frame_set_success hframe 1) henv
                have hsucc' : VEnv.get (VEnv.setMany V ["success"] [1]) "success" =
                    some (1 : U256) := by
                  rw [hset]
                  exact Midfall.LoweringV2.Blocks.EcPairing.venv_get_set_same hsucc
                have hinv' : Midfall.Lowering.Inv (calls := permissive (callsOf product))
                    (gas := g) R.E R.params Checkpoint.pcs R.pv S
                    (VEnv.setMany V ["success"] [1]) st' := by
                  rw [hset]
                  exact Inv_pcs_of_mem_outside R hR hinv hmem' henv hhalt 1
                have hcheck : DualMSM.check S.c.dual R.params = true :=
                  (Midfall.LoweringV2.Blocks.FinalPairing.fp_pairing_algebra R product hpc S).mp hprod
                have hinvPair : Midfall.Lowering.Inv (calls := permissive (callsOf product))
                    (gas := g) R.E R.params Checkpoint.pairing R.pv S
                    (VEnv.setMany V ["success"] [1]) st' :=
                  Inv_pairing_of_pcs hinv' hsucc' hcheck
                have hstagePair : leanStage R H inst ms Checkpoint.pairing = .ok S :=
                  leanStage_pairing_of hsnap hcheck
                have hagreePair : Agree (c := permissive (callsOf product)) (g := g)
                    R H cd Checkpoint.pairing (VEnv.setMany V ["success"] [1]) st' :=
                  fp_agree_of_one hdec hstagePair hinvPair
                exact ⟨hframe', hsucc', trivial, hrawP, trivial, hagreePair⟩⟩)
            · cases hv
      · cases h2 with
        | assignVal _ _ => exact absurd rfl hne2
        | assignHalt hev =>
            have hcase := fp_call_at_clean_apply R product hR hpc S st hpayload hptr hRpin hLpin g
              hsucc hev
            rcases hcase with
              ⟨stc, hv, _⟩ | ⟨stc, hv, hrev⟩
            · cases hv
            · cases hv
              exact Or.inl ⟨rfl, hrev⟩
    · have hgv := fp_guard_norm_inv (R := R) (c := permissive (callsOf product))
        (g := g) hsucc h1
      rw [hgv.2.2] at hne
      exact absurd rfl hne
  · intro V st hpre V' st' o hrun
    rcases fp_stmt_stepsV3 R hR H vkAddr cd (permissive (callsOf product)) g
        V st hpre V' st' o hrun with hrev | ⟨ho, hp⟩
    · exact Or.inl hrev
    · exact Or.inr ⟨by decide, ho, hp⟩


#assert_axioms Midfall.LoweringV3.fp_blockSim
  [propext, Classical.choice, Quot.sound] native []

/-- `callsOf` is functional: every honest answer is the unique `honestOf` result. -/
theorem callsOf_functional (product : PairingProduct) : (callsOf product).Functional :=
  honestCalls_functional product 0 (fun _ _ _ => False)
    (fun _ _ _ _ h => h.elim) (by decide)

/-- **DETERMINISM OF THE FINALPAIRING SLICE** under the honest precompiles and the
    zero gas oracle: two runs from the same boundary agree on environment, state and
    outcome. -/
theorem fp_slice_det (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    {V : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))}
    {st : EvmState}
    {V₁ : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))}
    {st₁ : EvmState} {o₁ : Outcome}
    {V₂ : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))}
    {st₂ : EvmState} {o₂ : Outcome}
    (h₁ : ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (R.slice Partial.finalPairing) V₁ st₁ o₁)
    (h₂ : ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (R.slice Partial.finalPairing) V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  ExecStmts.det (dialect_deterministic (callsOf_functional product)
    (ofFun_functional (fun _ => 0))) h₁ h₂

/-! ### 5b. The `finalPairing` progress row's two byte-level ingredients

Two facts the honest call site needs, both proved here rather than assumed:

* `pairingValidInput (fpWireFrame R st) = true` - the wire frame the helper assembles is a
  well-formed PAIRING_CHECK input. This is NOT a consequence of `Eip2537.Holds` alone (`G2Enc`
  carries only an encoder, so an encoding could in principle be longer than 0x100 bytes); it
  uses the two `.pcs` G1 pins (which are `bytesAt ... 128`, hence exactly 0x80 bytes), the
  `PayloadAgrees.g2Base`/`negSG2` slots (exactly eight words, hence 0x100 bytes) and
  `g1Valid`/`g2Valid` for the four decoded points.
* `ecPairing_call_of_clean_normal` - the `Step.callOk` half of `Totality.ecPairing_call_of_body`
  with the body outcome KNOWN to be `.normal`, so the disjunction disappears and the call
  evaluates to the word 1 outright. -/

/-- Reading a buffer at 0 for its own length is the identity. -/
theorem bytesTake_self {b : Bytes} {n : Nat} (hn : b.size = n) : bytesTake b 0 n = some b := by
  subst hn
  unfold bytesTake
  rw [ite_eq_left (by omega)]
  congr 1
  apply ByteArray.ext
  rw [show 0 + b.size = b.size by omega, Array.extract_eq_self_of_le (by simp)]

/-- `bytesAt` returns exactly the requested number of bytes (memory is zero beyond the image). -/
theorem bytesAt_size (st : EvmState) (a n : Nat) : (bytesAt st a n).size = n := by
  unfold bytesAt readBytes
  simp only [ByteArray.size, Array.size, List.length_map, List.length_range]

/-- **THE TWO-PAIR FRAME DECODES.** With canonical widths 0x80/0x100 the pairing parser walks the
    left-nested frame in exactly two steps and recovers the four points the codecs put in. -/
theorem pairingPairs?_pairingFrame_two {LA GB LB GN : Bytes}
    {p1 p2 : Nat × Nat} {q1 q2 : (Nat × Nat) × (Nat × Nat)}
    (w1 : LA.size = 128) (w2 : GB.size = 256) (w3 : LB.size = 128) (w4 : GN.size = 256)
    (h1 : g1Of? LA = some p1) (h2 : g2Of? GB = some q1)
    (h3 : g1Of? LB = some p2) (h4 : g2Of? GN = some q2) :
    pairingPairs? (pairingFrame [(LA, GB), (LB, GN)]) = some [(p1, q1), (p2, q2)] := by
  have hsize : (pairingFrame [(LA, GB), (LB, GN)]).size = 768 := by
    rw [Midfall.LoweringV2.Blocks.EcPairing.pairingFrame_two]
    unfold bytesAppend
    simp only [ByteArray.size, Array.size] at w1 w2 w3 w4 ⊢
    simp only [Array.toList_append, List.length_append]
    omega
  unfold pairingPairs?
  simp only [hsize]
  have hc : (768 == 0 || 768 % Yul.pairingPairBytes != 0) = false := by
    norm_num [Yul.pairingPairBytes, Yul.g1Bytes, Yul.g2Bytes]
  rw [hc]
  simp only [Bool.false_eq_true, ite_false]
  rw [show 768 / Yul.pairingPairBytes = 2 by
    norm_num [Yul.pairingPairBytes, Yul.g1Bytes, Yul.g2Bytes]]
  have hframe : pairingFrame [(LA, GB), (LB, GN)] = LA ++ (GB ++ (LB ++ GN)) := by
    rw [Midfall.LoweringV2.Blocks.EcPairing.pairingFrame_two]
    simp only [bytesAppend_eq_append]
    apply ByteArray.ext
    simp
  rw [hframe]
  have hg1 : Yul.g1Bytes = 128 := by norm_num [Yul.g1Bytes]
  have hg2 : Yul.g2Bytes = 256 := by norm_num [Yul.g2Bytes]
  have hp : Yul.pairingPairBytes = 384 := by
    norm_num [Yul.pairingPairBytes, Yul.g1Bytes, Yul.g2Bytes]
  have hsN : (LB ++ GN).size = 384 := by rw [ByteArray.size_append, w3, w4]
  have hsGN : (GB ++ (LB ++ GN)).size = 640 := by
    rw [ByteArray.size_append, hsN, w2]
  have t1 : bytesTake (LA ++ (GB ++ (LB ++ GN))) 0 128 = some LA := by
    rw [bytesTake_append_left LA (GB ++ (LB ++ GN)) 0 128 (by omega)]
    exact bytesTake_self w1
  have t2 : bytesTake (LA ++ (GB ++ (LB ++ GN))) (0 + 128) 256 = some GB := by
    rw [show (0 + 128 : Nat) = LA.size + 0 by omega]
    rw [bytesTake_append_right LA (GB ++ (LB ++ GN)) 0 256 (by omega)]
    rw [bytesTake_append_left GB (LB ++ GN) 0 256 (by omega)]
    exact bytesTake_self w2
  rw [show (2 : Nat) = Nat.succ 1 from rfl, Midfall.Yul.pairingPairs?.go.eq_2]
  simp only [hg1, hg2, t1, t2, h1, h2]
  rw [show (0 + Yul.pairingPairBytes) = LA.size + GB.size by rw [hp, w1, w2]]
  have t3 : bytesTake (LA ++ (GB ++ (LB ++ GN))) (LA.size + GB.size) 128 = some LB := by
    rw [bytesTake_append_right LA (GB ++ (LB ++ GN)) GB.size 128 (by omega)]
    rw [show GB.size = GB.size + 0 by omega]
    rw [bytesTake_append_right GB (LB ++ GN) 0 128 (by omega)]
    rw [bytesTake_append_left LB GN 0 128 (by omega)]
    exact bytesTake_self w3
  have t4 : bytesTake (LA ++ (GB ++ (LB ++ GN))) (LA.size + GB.size + 128) 256 = some GN := by
    rw [show LA.size + GB.size + 128 = LA.size + (GB.size + 128) by omega]
    rw [bytesTake_append_right LA (GB ++ (LB ++ GN)) (GB.size + 128) 256 (by omega)]
    rw [bytesTake_append_right GB (LB ++ GN) 128 256 (by omega)]
    rw [show (128 : Nat) = LB.size + 0 by omega]
    rw [bytesTake_append_right LB GN 0 256 (by omega)]
    exact bytesTake_self w4
  rw [Midfall.Yul.pairingPairs?.go.eq_2]
  simp only [hg1, hg2, t3, t4, h3, h4]
  rw [show (LA.size + GB.size + Yul.pairingPairBytes) = 768 by rw [hp, w1, w2]]
  rw [Midfall.Yul.pairingPairs?.go.eq_1]
  rfl

/-- **THE TWO-PAIR FRAME IS A VALID PAIRING INPUT** given the four decodes and canonical widths. -/
theorem pairingValidInput_pairingFrame_two {LA GB LB GN : Bytes}
    (w1 : LA.size = 128) (w2 : GB.size = 256) (w3 : LB.size = 128) (w4 : GN.size = 256)
    (h1 : ∃ pt, g1Of? LA = some pt ∧ g1PointMsmValid pt = true)
    (h2 : ∃ pt, g2Of? GB = some pt ∧ g2PointValid pt = true)
    (h3 : ∃ pt, g1Of? LB = some pt ∧ g1PointMsmValid pt = true)
    (h4 : ∃ pt, g2Of? GN = some pt ∧ g2PointValid pt = true) :
    pairingValidInput (pairingFrame [(LA, GB), (LB, GN)]) = true := by
  obtain ⟨p1, hp1, hv1⟩ := h1
  obtain ⟨q1, hq1, hqv1⟩ := h2
  obtain ⟨p2, hp2, hv2⟩ := h3
  obtain ⟨q2, hq2, hqv2⟩ := h4
  unfold pairingValidInput
  rw [pairingPairs?_pairingFrame_two w1 w2 w3 w4 hp1 hq1 hp2 hq2]
  simp [hv1, hqv1, hv2, hqv2]

/-- **THE WIRE FRAME IS VALID AT THE CLEAN CALL SITE.** The G1 halves are the `.pcs` pins (hence
    `bytesAt ... 128`, exactly 0x80 bytes) and the G2 halves are the VK header slots, whose
    `PayloadAgrees` identifications give exactly 0x100 bytes (`vkHeaderBytes_size` plus the two
    `constants_length` floors). `g1Valid`/`g2Valid` supply the decodes and subgroup checks. No
    hypothesis beyond `ValidV3` and the pairing-product statement. -/
theorem pairingValidInput_fpWireFrame (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (product : PairingProduct)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (S : Snapshot p G₁ G₂ Gₜ)
    (st : EvmState)
    (hRpin : bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128 =
      R.E.g1.toEip S.c.dual.right.eval)
    (hLpin : bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128 =
      R.E.g1.toEip S.c.dual.left.eval) :
    pairingValidInput (fpWireFrame R st) = true := by
  have hslots : vkG2Words R.pv vkG2BaseSlot = R.encG2 (R.params.nG2Prepared)⁻¹ ∧
      vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹ := by
    refine ⟨?_, ?_⟩
    · rw [hR.env.nG2, inv_inv]
      exact hR.payload.g2Base
    · rw [hR.env.sG2]
      exact hR.payload.negSG2
  have hGBsize : (vkG2Words R.pv vkG2BaseSlot).size = 256 := by
    show (vkHeaderBytes R.pv vkG2BaseSlot 8).size = 256
    rw [vkHeaderBytes_size]
    have h := g2Base_constants_length R hR product hpc
    have hmin : min 8 (R.pv.vk.constants.length - vkG2BaseSlot) = 8 := by omega
    rw [hmin]
  have hGNsize : (vkG2Words R.pv vkNegSG2BaseSlot).size = 256 := by
    show (vkHeaderBytes R.pv vkNegSG2BaseSlot 8).size = 256
    rw [vkHeaderBytes_size]
    have h := negSG2_constants_length R hR product hpc
    have hmin : min 8 (R.pv.vk.constants.length - vkNegSG2BaseSlot) = 8 := by omega
    rw [hmin]
  obtain ⟨ptR, hptR, hvR⟩ := hpc.g1Valid S.c.dual.right.eval
  obtain ⟨ptL, hptL, hvL⟩ := hpc.g1Valid S.c.dual.left.eval
  obtain ⟨ptB, hptB, hvB⟩ := hpc.g2Valid (R.params.nG2Prepared)⁻¹
  obtain ⟨ptN, hptN, hvN⟩ := hpc.g2Valid (R.params.sG2Prepared)⁻¹
  unfold fpWireFrame
  exact pairingValidInput_pairingFrame_two
    (bytesAt_size st _ 128) hGBsize (bytesAt_size st _ 128) hGNsize
    ⟨ptR, by rw [hRpin]; exact hptR, hvR⟩
    ⟨ptB, by rw [hslots.1]; exact hptB, hvB⟩
    ⟨ptL, by rw [hLpin]; exact hptL, hvL⟩
    ⟨ptN, by rw [hslots.2]; exact hptN, hvN⟩

/-- **THE `ec_pairing` CALL FROM A CLEAN NORMAL BODY RUN.** The `Step.callOk` half of
    `Totality.ecPairing_call_of_body` with the body's outcome KNOWN (`.normal`), so the disjunction
    `vals / halt` collapses and the call evaluates to the word 1. The two literal `fpVal` heads are
    the render's `PAIRING_*_MPTR` constants, and the body's entry environment is the swapped
    `(lhs_mptr := RHS, rhs_mptr := LHS)` binder pair the slice's call produces. -/
theorem ecPairing_call_of_clean_normal
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    {V : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))}
    {st : EvmState}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    {Vend : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))}
    {stend : EvmState}
    (hstep : Step (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (["success", "lhs_mptr", "rhs_mptr"].zip
          [(1 : U256), BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr),
           BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)] ++
          bindZeros (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)) ["ret"]) st
        (.stmt (.block (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
          (GenAst.pairingScratchOf R.pv)
          (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base))
          (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base))
          R.model.templateConstants.gas.pairingTwoPair 0x0f 768 32 0x84e81692 0xc3b0d8cd)))
        (.sres Vend stend .normal))
    (hret : VEnv.get Vend "ret" = some (1 : U256)) :
    EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Expr.call "ec_pairing"
        [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
         Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) (.vals [1] stend) := by
  have hdecl := Midfall.LoweringV3.ecPairingDecl_eq_lit R hR
    (callsOf product) (ExternalGas.ofFun fun _ => 0)
  have hlook : lookupFun (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) "ec_pairing" =
      some (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
        (callsOf product) (ExternalGas.ofFun fun _ => 0),
        R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) :=
    Midfall.LoweringV2.Blocks.EcPairing.ecPairing_lookup R
  have hsuccE : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Expr.var "success") (.vals [(1 : U256)] st) :=
    Step.var hsucc
  have hRhs : Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR" =
      Expr.lit (.number (cAddr R.pv.memory.pairingRhsMptr)) := by
    unfold Midfall.LoweringV2.Blocks.FinalPairing.fpVal
    rw [consts_lookup_PAIRING_RHS_MPTR R hR]
  have hLhs : Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR" =
      Expr.lit (.number (cAddr R.pv.memory.pairingLhsMptr)) := by
    unfold Midfall.LoweringV2.Blocks.FinalPairing.fpVal
    rw [consts_lookup_PAIRING_LHS_MPTR R hR]
  have hRhsE : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR")
      (.vals [BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr)] st) := by
    rw [hRhs]; exact Step.lit
  have hLhsE : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR")
      (.vals [BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)] st) := by
    rw [hLhs]; exact Step.lit
  have hargs : Step (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (.args [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
        Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"])
      (.eres (.vals [1, BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr),
        BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)] st)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil hLhsE) hRhsE) hsuccE
  have hparams : (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
      (callsOf product) (ExternalGas.ofFun fun _ => 0)).params =
      ["success", "lhs_mptr", "rhs_mptr"] := by
    rw [hdecl]
  have hrets : (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
      (callsOf product) (ExternalGas.ofFun fun _ => 0)).rets = ["ret"] := by
    rw [hdecl]
  have hstep' : Step (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (["success", "lhs_mptr", "rhs_mptr"].zip [1, BitVec.ofNat 256
        (cAddr R.pv.memory.pairingRhsMptr),
        BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)] ++
        bindZeros (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)) ["ret"]) st
      (.stmt (.block (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
        (GenAst.pairingScratchOf R.pv)
        (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base))
        (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base))
        R.model.templateConstants.gas.pairingTwoPair 0x0f 768 32 0x84e81692 0xc3b0d8cd)))
      (.sres Vend stend .normal) := by
    simpa only [hdecl] using hstep
  have hlen : ([1, BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr),
      BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)] : List U256).length =
      (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
        (callsOf product) (ExternalGas.ofFun fun _ => 0)).params.length := by
    rw [hparams]; rfl
  have hcall := Step.callOk (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (funs := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (Vend := Vend) (st2 := stend) (o := .normal) hargs hlook hlen
      (by simpa only [hdecl] using hstep') (Or.inl rfl)
  simpa only [hdecl, List.map_cons, List.map_nil, hrets, hret, Option.getD_some] using hcall

set_option maxHeartbeats 800000 in
/-- **THE PAIRING CHECK FROM LEAN ACCEPTANCE.** `LeanAccepts` gives a decoding and an accepting
    `verifyMsgs`; `verifyMsgs` is `prepareMsgs` followed by the `DualMSM.check` gate, and
    `snapshotOf_prepareMsgs_ok` identifies that `prepareMsgs` answer with the snapshot's own
    `dual`. The two decodings agree by `fp_decoded_unique`, so the check is the one the boundary's
    snapshot carries. -/
theorem pairingCheck_of_accepts {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes}
    (hacc : LeanAccepts R H cd) {S : Snapshot p G₁ G₂ Gₜ}
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    (hdec : Decoded R cd ms instW inst)
    (hsnap : snapshotOf R.E H R.vk inst ms none = .ok S) :
    DualMSM.check S.c.dual R.params = true := by
  obtain ⟨ms', instW', inst', hdec'', hinst', hverify⟩ := hacc
  have hdec' : Decoded R cd ms' instW' inst' := ⟨hdec'', hinst'⟩
  obtain ⟨e1, e2, e3⟩ := fp_decoded_unique hdec' hdec
  subst ms'
  subst instW'
  subst inst'
  have hprep := snapshotOf_prepareMsgs_ok (Gₜ := Gₜ) R.E H R.vk inst ms none S hsnap
  unfold verifyMsgs at hverify
  rw [hprep] at hverify
  simp only [bind, Except.bind] at hverify
  by_cases hc : DualMSM.check S.c.dual R.params = true
  · exact hc
  · rw [if_neg hc] at hverify
    cases hverify

set_option maxHeartbeats 1600000 in
/-- **LEAF (ROW.FP, WP A11): the finalPairing progress row, PROVED.** Evidence
    `GeneratorRows.lean:1083`. The clean `.pcs` boundary decodes (`Agree`), and the decoded snapshot's
    `DualMSM.check` is read off `LeanAccepts` (`pairingCheck_of_accepts`) and turned into the wire
    answer by `fp_pairing_algebra`; the two `.pcs` G1 pins plus the `PayloadAgrees` G2 slots and
    `fpActualFrame_eq_fpWireFrame` then make the helper's frame valid and true, so
    `fpBodyRun_clean` supplies a NORMAL body run and `ecPairing_call_of_clean_normal` the `.vals [1]`
    call. The slice's two statements are `fp_slice_at`'s guard and assignment; the guard skips at
    `success = 1`, the assignment restores the invariant across the 768-byte scratch write
    (`Inv_pcs_of_mem_outside`) and `stageInv_pairing_of_pcs` puts the boundary at `.pairing`.
    Every OTHER honest run is collapsed to that witness by `fp_slice_det`, so the all-runs half is
    `o = .normal ∧ StageInv .pairing` with no extra case split. -/
theorem fp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.finalPairing H vkAddr product cd := by
  have hex : ∀ V st,
      StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
        R H vkAddr cd Checkpoint.pcs V st →
      ∃ V' st' o,
        ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
          (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
          (R.slice Partial.finalPairing) V' st' o ∧
        o = .normal ∧
          StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
            R H vkAddr cd Checkpoint.pairing V' st' := by
    intro V st hpre
    obtain ⟨hframe, hsucc, -, hraw, -, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hstage, hinv⟩ := hagree ms instW inst hdec
    have hsnap : snapshotOf R.E H R.vk inst ms none = .ok S := by
      simpa only [leanStage] using hstage
    have hRpin : bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128 =
        R.E.g1.toEip S.c.dual.right.eval :=
      (inv_pcs_pairing_pins (calls := callsOf product)
        (gas := ExternalGas.ofFun fun _ => 0) (E := R.E) (params := R.params)
        (PV := R.pv) (S := S) hinv).1
    have hLpin : bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128 =
        R.E.g1.toEip S.c.dual.left.eval :=
      (inv_pcs_pairing_pins (calls := callsOf product)
        (gas := ExternalGas.ofFun fun _ => 0) (E := R.E) (params := R.params)
        (PV := R.pv) (S := S) hinv).2
    have hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes :=
      inv_pcs_vk_payload (calls := callsOf product)
        (gas := ExternalGas.ofFun fun _ => 0) (E := R.E) (params := R.params)
        (PV := R.pv) (S := S) hinv
    obtain ⟨meta_, vkMptr, config, vkBase, hlayout, hvk, -⟩ :=
      plan_size_of_generated hR.generated
    have hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n := by
      refine ⟨vkBase, ?_⟩
      rw [hlayout, MemoryPairs.new_vkMptr, hvk]
      rfl
    have hfitR := pairingRhsMptr_toNat_of_valid R hR
    have hfitL := pairingLhsMptr_toNat_of_valid R hR
    have hfits := fpBodyEnvFits_of_valid R hR
    have hcheck : DualMSM.check S.c.dual R.params = true :=
      pairingCheck_of_accepts hacc hdec hsnap
    have hslots : vkG2Words R.pv vkG2BaseSlot = R.encG2 (R.params.nG2Prepared)⁻¹ ∧
        vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹ := by
      refine ⟨?_, ?_⟩
      · rw [hR.env.nG2, inv_inv]
        exact hR.payload.g2Base
      · rw [hR.env.sG2]
        exact hR.payload.negSG2
    have hframeWire : fpActualFrame R st
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr))
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)) = fpWireFrame R st :=
      fpActualFrame_eq_fpWireFrame R hR product hpc S st hpayload hptr hRpin hLpin hfitR hfitL
    have hvalidWire : pairingValidInput (fpWireFrame R st) = true :=
      pairingValidInput_fpWireFrame R hR product hpc S st hRpin hLpin
    have hvalid : pairingValidInput (fpActualFrame R st
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr))
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr))) = true := by
      rw [hframeWire]
      exact hvalidWire
    have hprodFrame : product (Midfall.LoweringV2.Blocks.FinalPairing.fpFrame R S) = true :=
      (Midfall.LoweringV2.Blocks.FinalPairing.fp_pairing_algebra R product hpc S).mpr hcheck
    have hframeEq : Midfall.LoweringV2.Blocks.FinalPairing.fpFrame R S = fpWireFrame R st := by
      unfold Midfall.LoweringV2.Blocks.FinalPairing.fpFrame fpWireFrame
      rw [hRpin, hLpin, hslots.1, hslots.2]
    have hprodWire : product (fpWireFrame R st) = true := hframeEq ▸ hprodFrame
    have hprodActual : product (fpActualFrame R st
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr))
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr))) = true := by
      rw [hframeWire]
      exact hprodWire
    obtain ⟨Vend, stend, hstep, hret, hmem, henv, hhalt, hprod'⟩ :=
      fpBodyRun_clean R product st
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr))
        (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)) hfits hvalid hprodActual
    have hev := ecPairing_call_of_clean_normal R product hR hsucc hstep hret
    have hguard : ExecStmt (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
        (Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
          [Stmt.exprStmt (Expr.call "fail"
            [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])])
        V st .normal :=
      vk_gate_skip_any R "ERR_PRECOMPILE_FAILED" hsucc (by decide)
    have hsucc' : VEnv.get (VEnv.setMany V ["success"] [1]) "success" = some (1 : U256) := by
      show VEnv.get (VEnv.set V "success" (1 : U256)) "success" = some 1
      exact Midfall.LoweringV2.Blocks.EcPairing.venv_get_set_same hsucc
    have hagree' : Agree (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
        R H cd Checkpoint.pcs (VEnv.setMany V ["success"] [1]) stend := by
      intro ms' instW' inst' hdec'
      obtain ⟨S', hstage', hinv'⟩ := hagree ms' instW' inst' hdec'
      refine ⟨S', hstage', ?_⟩
      rw [show VEnv.setMany V ["success"] [1] = VEnv.set V "success" (1 : U256) from rfl]
      exact Inv_pcs_of_mem_outside R hR hinv' hmem henv hhalt 1
    have hdual : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
        Decoded R cd ms instW inst →
        ∀ S, leanStage R H inst ms Checkpoint.pcs = .ok S →
          DualMSM.check S.c.dual R.params = true := by
      intro ms' instW' inst' hdec' S' hstage'
      obtain ⟨e1, e2, e3⟩ := fp_decoded_unique hdec' hdec
      subst ms'
      subst instW'
      subst inst'
      have hSS : S' = S := by
        rw [hstage] at hstage'
        exact (Except.ok.inj hstage').symm
      subst hSS
      exact hcheck
    have hframe' : Frame R H vkAddr cd (VEnv.setMany V ["success"] [1]) stend := by
      rw [show VEnv.setMany V ["success"] [1] = VEnv.set V "success" (1 : U256) from rfl]
      exact Frame_env_congr (Frame_set_success hframe 1) henv
    have hstagePair : StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
        R H vkAddr cd Checkpoint.pairing (VEnv.setMany V ["success"] [1]) stend :=
      stageInv_pairing_of_pcs R ⟨hframe', hsucc', trivial, ⟨ms, instW, inst, hdec⟩, trivial, hagree'⟩ hsucc' hdual
    refine ⟨VEnv.setMany V ["success"] [1], stend, .normal, ?_, rfl, hstagePair⟩
    rw [fp_slice_at R hR]
    exact Step.seqCons hguard (Step.seqCons (Step.assignVal hev (by rfl)) Step.seqNil)
  refine ⟨?_, ?_⟩
  · intro V st hpre
    obtain ⟨V', st', o, hrun, how, hpost⟩ := hex V st hpre
    exact ⟨V', st', o, hrun, how, hpost⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨Vw, stw, ow, hrunw, how, hpostw⟩ := hex V st hpre
    obtain ⟨e1, e2, e3⟩ := fp_slice_det R product hrun hrunw
    subst V'
    subst st'
    subst o
    exact ⟨how, hpostw⟩

#assert_axioms Midfall.LoweringV3.fp_blockProgS
  [propext, Classical.choice, Quot.sound] native []

/-- **THE MISSING `fpG2Slots` PREMISE, DERIVED FROM `ValidV3`.** FP.0 carried the two VK-header G2
    clauses as an explicit premise because V2's `Valid` has no `VkSlotsAgree`; V3's `PayloadAgrees`
    does (`g2Base`, `negSG2`), and `EnvAgrees.nG2` / `.sG2` are the prepared-form identifications
    the invariants use. This is the bridge between them, and it adds no hypothesis: the payload's
    `g₂` is `nG2Prepared⁻¹` because `nG2Prepared = g₂⁻¹`, and the `sG2` slot is already stated at
    `sG2gen⁻¹`. -/
theorem fpG2Slots_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    Midfall.LoweringV2.Blocks.FinalPairing.fpG2Slots R := by
  refine ⟨?_, ?_⟩
  · rw [hR.env.nG2, inv_inv]
    exact hR.payload.g2Base
  · rw [hR.env.sG2]
    exact hR.payload.negSG2

#assert_axioms Midfall.LoweringV3.fpG2Slots_of_valid
  [propext, Classical.choice, Quot.sound] native []

/-! ## 6. traceReturn - PROVED HERE (PL.H0 step 4's optional lift; SIM.7 owes nothing for this block) -/

/-- **THE TRACERETURN SIMULATION ROW, PROVED (PL.H0 step 4's optional lift, taken).** The evidence's
    `tr_blockSim` (`GeneratorRows.lean:1290`) ported verbatim: T.1's and T.2's arm-free walks
    (`tr_sound_clean_noarm`, `tr_poison_walk_noarm`) give the row at `StageInv` directly, with the
    closed Lean stage read off the boundary (`LeanRaw .pairing` + `Agree .pairing`) and handed out
    with the return. No new semantics, no pin, no `hR` - the block is render-shape only. -/
theorem tr_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (g : ExternalGas) (cd : Bytes) :
    BlockSim R Partial.traceReturn H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    have hclean : Clean R Checkpoint.pairing S H vkAddr cd V st := ⟨hinv, hframe, hsucc⟩
    rcases Blocks.TraceReturn.tr_sound_clean_noarm R product S H vkAddr cd g hclean hrun with
        hrev | hok
    · exact Or.inl hrev
    · obtain ⟨ho, hh⟩ := exitOk_traceReturn_apply hok
      exact Or.inr (Or.inl ⟨ho, hh, ms, instW, inst, hdec, S, hS⟩)
  · intro V st hpre V' st' o hrun
    exact Or.inl (Blocks.TraceReturn.tr_poison_walk_noarm R H vkAddr cd hpre hrun)

/-- **THE TRACERETURN PROGRESS ROW, PROVED (the same optional lift).** The evidence's
    `tr_blockProgS` (`GeneratorRows.lean:1304`) ported, with T.2's pin DERIVED rather than assumed:
    `trRetMptr R` is `∃ m, R.consts.lookup "RETURN_MPTR" = some m`, which is
    `LoweringV3.returnMptr_of_valid` on `ValidV3` - so the row takes `hR : ValidV3 R` and no free
    premise, exactly as `Consts.trRetMptr_of_valid` does on the frozen `R.Valid`. -/
theorem tr_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockProgS R Partial.traceReturn H vkAddr product cd := by
  have hpin : Blocks.TraceReturn.trRetMptr R := Midfall.LoweringV3.returnMptr_of_valid hR
  refine ⟨?_, ?_⟩
  · intro V st hpre
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    obtain ⟨V', st', o, hrun, hexit⟩ :=
      (Blocks.TraceReturn.tr_blockProgress R product hpin S H vkAddr cd).1 V st
        ⟨hinv, hframe, hsucc⟩
    exact ⟨V', st', o, hrun, exitOk_traceReturn_apply hexit⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    exact exitOk_traceReturn_apply
      ((Blocks.TraceReturn.tr_blockProgress R product hpin S H vkAddr cd).2 V st
        ⟨hinv, hframe, hsucc⟩ V' st' o hrun)

/-! ## 7. THE TWO BUNDLES, PROVED -/

/-- **THE SEVEN SIMULATION ROWS, PROVED from the fourteen** (`cases q`: one named leaf per block and
    direction, and nothing else). Evidence `GeneratorRows.lean:1111` at the V3 reading. -/
theorem sim_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    SimRowsV3 R product := by
  intro hR hcodec hpc H vkAddr cd hside q g
  cases q with
  | vkLoading => exact vk_blockSim R product hR hcodec hpc H vkAddr cd g
  | transcriptParser => exact tp_blockSim R product hR hcodec hpc H vkAddr cd g
  | lagrange => exact lag_blockSim R product hR hcodec hpc H vkAddr cd g
  | quotientLin => exact QuotientRows.q_blockSim R product hR hcodec hpc H vkAddr cd hside g
  | pcs => exact pcs_blockSim R product hR hcodec hpc H vkAddr cd g
  | finalPairing => exact fp_blockSim R product hR hcodec hpc H vkAddr cd g
  | traceReturn => exact tr_blockSim R product H vkAddr g cd

/-- **THE SEVEN PROGRESS ROWS, PROVED from the fourteen.** Evidence `GeneratorRows.lean:1125`; the
    TraceReturn arm takes `ValidV3` and derives T.2's pin from it. -/
theorem prog_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    ProgRowsV3 R product := by
  intro hR hcodec hpc H vkAddr cd hacc hcomp q
  cases q with
  | vkLoading => exact vk_blockProgS R product hR hcodec hpc H vkAddr cd hacc hcomp
  | transcriptParser => exact tp_blockProgS R product hR hcodec hpc H vkAddr cd hacc hcomp
  | lagrange => exact lag_blockProgS R product hR hcodec hpc H vkAddr cd hacc hcomp
  | quotientLin => exact QuotientRows.q_blockProgS R product hR hcodec hpc H vkAddr cd hacc hcomp
  | pcs => exact pcs_blockProgS R product hR hcodec hpc H vkAddr cd hacc hcomp
  | finalPairing => exact fp_blockProgS R product hR hcodec hpc H vkAddr cd hacc hcomp
  | traceReturn => exact tr_blockProgS R product hR H vkAddr cd

/-! ## 8. Cone lists and axiom prints -/

#cone_sorries Midfall.LoweringV3.sim_rows
#cone_sorries Midfall.LoweringV3.prog_rows

#print axioms Midfall.LoweringV3.sim_rows
#print axioms Midfall.LoweringV3.prog_rows
#print axioms Midfall.LoweringV3.vk_blockSim
#assert_axioms Midfall.LoweringV3.vk_blockSim
  [propext, Classical.choice, Quot.sound] native []

/- **WP A3 gate prints for the progress row: PROVED.** `vk_blockProgS` is
    `VkClean.vk_exists_run` (the explicit 13-statement run) paired with
    `VkClean.vk_all_normal` (every run exits normal at `StageInv .vk`), at the progress dialect
    `callsOf product` / `ExternalGas.ofFun 0`. Standard three, cone 0. -/
#check @Midfall.LoweringV3.vk_blockProgS
#print axioms Midfall.LoweringV3.vk_blockProgS
#cone_sorries Midfall.LoweringV3.vk_blockProgS
#assert_axioms Midfall.LoweringV3.vk_blockProgS
  [propext, Classical.choice, Quot.sound] native []
#print axioms Midfall.LoweringV3.VkClean.vk_hdr_word_read
#assert_axioms Midfall.LoweringV3.VkClean.vk_hdr_word_read
  [propext, Classical.choice, Quot.sound] native []

/-! ## 9. The canonical Lagrange `LagCfg` and the `Inv → LagPre` field assembly

The Render-level clean arm needs one `LagCfg` constructed from the snapshot the Lagrange
post talks about. `lagCfgOf` is that record. The four memory-word equalities (`x`, `omega`,
`omega_inv_to_l`, `n_inv`) are the only facts the assembly cannot read off `Inv` + `Frame`
directly here: `x` comes from the `.transcript` slot (decode-relative, via `Agree`), the three
header words from `Inv .vk`'s `bytesAt vkMptr = PV.vk.bytes` window plus `PayloadAgrees` and
the `readBytes`/`loadWord` bridge (`PG-LOADWORD-BYTES`). They are explicit arguments so the
missing bridge is named rather than guessed. -/

/-- `loadWord` is the `wordFrom` of the 32-byte `readBytes` window. -/
theorem loadWord_eq_wordFrom_readBytes (mem : Nat → UInt8) (p : Nat) :
    loadWord mem p = wordFrom (readBytes mem p 32) 0 := by
  unfold loadWord wordFrom readBytes byteFrom
  refine Midfall.Yul.Word.foldl_congr _ _ _ ?_ 0
  intro i hi acc
  have hi32 : i < 32 := List.mem_range.mp hi
  rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hi32), List.getElem_range]
  simp only [Option.map_some, Option.getD_some]

set_option maxHeartbeats 4000000 in
/-- **PG-LOADWORD-BYTES, the header-word core.** `bytesAt`/`readBytes` at the payload base
    gives every VK header word: `readBytes_vkHeader` slices the payload bytes and
    `wordFrom_wordToBytesBE` closes the one-word fold. This is the lemma the three `lagCfgOf`
    header slots (`omega`, `omega_inv_to_l`, `n_inv`) consume; the caller supplies the payload
    window from `Inv .vk`. -/
theorem loadWord_vkHeader_of_readBytes (PV : PlanView) (st : EvmState) (i : Nat)
    (hlen : 11 ≤ PV.vk.constants.length) (hi : i ≤ 10)
    (hpayload : readBytes st.memory (ptrAddr PV.memory.vkMptr) PV.vk.len =
      PV.vk.bytes.data.toList) :
    loadWord st.memory (ptrAddr PV.memory.vkMptr + 32 * i) =
      (PV.vk.constants.getD i ("", 0)).2 := by
  have hlenGe : 352 ≤ PV.vk.len := by
    rw [Midfall.Generator.Halo2VerifyingKey.len]
    omega
  have hfit : 32 * (i + 1) ≤ PV.vk.len := by omega
  have hread := Midfall.LoweringV3.readBytes_vkHeader st PV i 1 hpayload hfit (by omega)
  rw [loadWord_eq_wordFrom_readBytes, hread]
  unfold Midfall.Lowering.vkHeaderBytes
  rw [show (PV.vk.constants.drop i).take 1 = [(PV.vk.constants.getD i ("", 0))] from by
    rw [List.take_one, List.drop_eq_getElem_cons (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [Midfall.LoweringV3.VkClean.bytes_empty_append,
    Midfall.LoweringV3.VkClean.wordFrom_wordToBytesBE]

/-- The canonical Lagrange block configuration at a snapshot. -/
def lagCfgOf (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ) :
    LagrangeBlock.LagCfg R.consts cd R.pv.k R.pv.numInstances R.pv.numNegLagranges :=
  { D := R.pv.memory.lagrangeDenomsMptr
    s := R.pv.memory.batchInvertScratchMptr
    aX := ptrAddr R.pv.memory.xMptr
    aO := ptrAddr R.pv.memory.vkMptr + 32 * vkHeaderTemplateSlotsDefault.omega
    aL := ptrAddr R.pv.memory.vkMptr + 32 * vkHeaderTemplateSlotsDefault.omegaInvToL
    aN := ptrAddr R.pv.memory.vkMptr + 32 * vkHeaderTemplateSlotsDefault.nInv
    aI := R.pv.proofLayout.proofEnd + 32
    aXN := ptrAddr R.pv.memory.xNMptr
    aXN1 := ptrAddr R.pv.memory.xNMinus1InvMptr
    aLL := ptrAddr R.pv.memory.lLastMptr
    aLB := ptrAddr R.pv.memory.lBlindMptr
    aL0 := ptrAddr R.pv.memory.l0Mptr
    aIE := ptrAddr R.pv.memory.instanceEvalMptr
    rw := BitVec.ofNat 256 p
    succ := 1
    xw := Midfall.Halo2.frWord S.alg.x
    omw := Midfall.Halo2.frWord R.vk.domain.omega
    w0 := Midfall.Halo2.frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges)
    nInv := Midfall.Halo2.frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹) }

set_option maxHeartbeats 4000000 in
/-- PG-LOADWORD-BYTES at `OMEGA_MPTR`: the payload window gives the omega header word. -/
theorem lagCfgOf_aO_load (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (st : EvmState) (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ)
    (hpayload : readBytes st.memory (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len =
      R.pv.vk.bytes.data.toList) :
    loadWord st.memory (lagCfgOf R cd S).aO = (lagCfgOf R cd S).omw := by
  have h := loadWord_vkHeader_of_readBytes R.pv st vkHeaderTemplateSlotsDefault.omega
    hR.payload.constantsLength (by decide) hpayload
  have hpay : (R.pv.vk.constants.getD vkHeaderTemplateSlotsDefault.omega ("", 0)).2 =
      Midfall.Halo2.frWord R.vk.domain.omega := by
    simpa [payloadWord] using hR.payload.omega
  rw [hpay] at h
  simpa [lagCfgOf] using h

set_option maxHeartbeats 4000000 in
/-- PG-LOADWORD-BYTES at `N_INV_MPTR`: the payload window gives the barycentric-weight header
    word, which is exactly `LagCfg.nInv` (`PayloadAgrees.nInv`). -/
theorem lagCfgOf_aN_load (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (st : EvmState) (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ)
    (hpayload : readBytes st.memory (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len =
      R.pv.vk.bytes.data.toList) :
    loadWord st.memory (lagCfgOf R cd S).aN = (lagCfgOf R cd S).nInv := by
  have h := loadWord_vkHeader_of_readBytes R.pv st vkHeaderTemplateSlotsDefault.nInv
    hR.payload.constantsLength (by decide) hpayload
  have hpay : (R.pv.vk.constants.getD vkHeaderTemplateSlotsDefault.nInv ("", 0)).2 =
      Midfall.Halo2.frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹) := by
    simpa [payloadWord] using hR.payload.nInv
  rw [hpay] at h
  simpa [lagCfgOf] using h

set_option maxHeartbeats 4000000 in
/-- PG-LOADWORD-BYTES at `OMEGA_INV_TO_L_MPTR`. The payload word is
    `frWord (ω⁻¹ ^ rotationLast.natAbs)`; the block's `w0` is `frWord (ω⁻¹ ^ numNegLagranges)`.
    THE EXPONENT EQUALITY IS THE NAMED `PG-OMEGAINV-SLOT`: `EnvAgrees.negLagranges` gives
    `numNegLagranges = blindingFactors + 1`, but `rotationLast = -(blindingFactors + 1)` is a
    generator-input fact (`Certified.fromConstraintSystem_rotationLast`), not a `ValidV3`
    projection. It is an explicit premise, not a row/root hypothesis. -/
theorem lagCfgOf_aL_load (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (st : EvmState) (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ)
    (hrot : R.plan.meta_.rotationLast.natAbs = R.pv.numNegLagranges)
    (hpayload : readBytes st.memory (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len =
      R.pv.vk.bytes.data.toList) :
    loadWord st.memory (lagCfgOf R cd S).aL = (lagCfgOf R cd S).w0 := by
  have h := loadWord_vkHeader_of_readBytes R.pv st vkHeaderTemplateSlotsDefault.omegaInvToL
    hR.payload.constantsLength (by decide) hpayload
  have hpay : (R.pv.vk.constants.getD vkHeaderTemplateSlotsDefault.omegaInvToL ("", 0)).2 =
      Midfall.Halo2.frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges) := by
    simpa [payloadWord, hrot] using hR.payload.omegaInvToL
  rw [hpay] at h
  simpa [lagCfgOf] using h

/-- `bytesAt` is the `readBytes` window: the equality at `ByteArray` level is the equality of
    the underlying byte lists. -/
theorem readBytes_of_bytesAt {st : EvmState} {a n : Nat} {b : Bytes}
    (h : bytesAt st a n = b) : readBytes st.memory a n = b.data.toList := by
  unfold bytesAt at h
  exact congrArg (fun x : Bytes => x.data.toList) h


/-- **THE `Inv`/`Frame` → `LagPre` FIELD ASSEMBLY.** `Frame` supplies `r` (its `FR_MODULUS`
    word, `frModulus_of_valid` identifying the literal with `p`) and the calldata; `StageInv`'s
    success conjunct supplies `success = 1`; the prologue supplies `pf = 0`; the four explicit
    hypotheses are the memory words. This is the exact interface of the bridge: no row/root
    hypothesis, and the four word facts stay visible. -/
theorem lagPre_of_inv_transcript (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hframe : Frame R H vkAddr cd V st)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hpf : VEnv.get V "lagrange_precompile_failed" = some (0 : U256))
    (hX : loadWord st.memory (lagCfgOf R cd S).aX = (lagCfgOf R cd S).xw)
    (hO : loadWord st.memory (lagCfgOf R cd S).aO = (lagCfgOf R cd S).omw)
    (hL : loadWord st.memory (lagCfgOf R cd S).aL = (lagCfgOf R cd S).w0)
    (hN : loadWord st.memory (lagCfgOf R cd S).aN = (lagCfgOf R cd S).nInv) :
    LagrangeBlock.LagPre (lagCfgOf R cd S) V st := by
  obtain ⟨rv, hrv, hget⟩ := hframe.r
  have hrvp : rv = p := by
    have h := frModulus_of_valid hR
    rw [hrv] at h
    exact Option.some.inj h
  refine ⟨?_, hsucc, hpf, hX, hO, hL, hN, hframe.calldata⟩
  rw [hget, hrvp]
  rfl

#assert_axioms lagCfgOf_aO_load [propext, Classical.choice, Quot.sound]
#assert_axioms lagCfgOf_aN_load [propext, Classical.choice, Quot.sound]
#assert_axioms lagCfgOf_aL_load [propext, Classical.choice, Quot.sound]
#assert_axioms lagPre_of_inv_transcript [propext, Classical.choice, Quot.sound]

/-- **THE BRIDGE WITH THE PG-LOADWORD SLOTS SPENT.** Only three inputs remain: the payload
    window (`hpayload`, a projection of `Inv .vk`), the x-slot word (`hx`, the named SIM.10 /
    parser pin) and the `PG-OMEGAINV-SLOT` exponent equality. Everything else is
    `lagPre_of_inv_transcript` plus the three `lagCfgOf` slot lemmas. -/
theorem lagPre_of_inv_transcript_of_payload (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hframe : Frame R H vkAddr cd V st)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hpf : VEnv.get V "lagrange_precompile_failed" = some (0 : U256))
    (hx : loadWord st.memory (lagCfgOf R cd S).aX = (lagCfgOf R cd S).xw)
    (hrot : R.plan.meta_.rotationLast.natAbs = R.pv.numNegLagranges)
    (hpayload : readBytes st.memory (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len =
      R.pv.vk.bytes.data.toList) :
    LagrangeBlock.LagPre (lagCfgOf R cd S) V st :=
  lagPre_of_inv_transcript R hR cd S H vkAddr V st hframe hsucc hpf hx
    (lagCfgOf_aO_load R hR st cd S hpayload)
    (lagCfgOf_aL_load R hR st cd S hrot hpayload)
    (lagCfgOf_aN_load R hR st cd S hpayload)

#assert_axioms lagPre_of_inv_transcript_of_payload [propext, Classical.choice, Quot.sound]

/-! ## 10. THE PG-OMEGAINV SLOT AND THE PAYLOAD WINDOW FROM `Inv .vk` -/

/-- The generated model reads `numNegLagranges` off the plan meta (the Certified proof,
    re-derived below `GeneratorTheorem`). -/
theorem model_numNegLagranges_of_generated_lag {R : Render p G₁ G₂ Gₜ}
    (h : GeneratedBy R) :
    R.model.numNegLagranges = R.plan.meta_.rotationLast.natAbs := by
  have hg := Midfall.LoweringV3.MemoryPairs.gvfp_of_generated h
  simp only [Midfall.Generator.generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  · cases hg
  · cases hg
  · obtain ⟨_a1, _, h1⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp hg
    obtain ⟨_a2, _, h2⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h1
    obtain ⟨_a3, _, h3⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h2
    obtain ⟨_a4, _, h4⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h3
    obtain ⟨_a5, _, h5⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h4
    obtain ⟨_a6, _, h6⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h5
    obtain ⟨_a7, _, h7⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h6
    have hrec := Except.ok.inj h7
    simpa [Midfall.Generator.numNegLagrangesOf] using
      (congrArg (fun x => x.numNegLagranges) hrec).symm

#assert_axioms model_numNegLagranges_of_generated_lag [propext, Classical.choice, Quot.sound]

/-- **PG-OMEGAINV-SLOT**, from the generated model: the plan meta's rotation magnitude is the
    plan view's `numNegLagranges`. -/
theorem pg_omegainv_slot {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.plan.meta_.rotationLast.natAbs = R.pv.numNegLagranges := by
  have h := model_numNegLagranges_of_generated_lag hR.generated
  exact h.symm.trans (by rfl)

#assert_axioms pg_omegainv_slot [propext, Classical.choice, Quot.sound]

theorem blindingFactors_ok_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    ∃ bf, R.vk.cs.blindingFactors = .ok bf := by
  have hneg := hR.env.negLagranges
  have hge := negLagranges_of_valid hR
  cases h : R.vk.cs.blindingFactors with
  | error e =>
      simp [h, Except.toOption] at hneg
      omega
  | ok bf => exact ⟨bf, rfl⟩

theorem lagrangeTriple_exists_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (s2 : SnapAlgebra p G₁) :
    ∃ tri, lagrangeTriple (p := p) (G₁ := G₁) R.vk s2.alg.x s2.alg.xn = .ok tri := by
  obtain ⟨bf, hbf⟩ := blindingFactors_ok_of_valid R hR
  unfold lagrangeTriple
  rw [hbf]
  dsimp only [Bind.bind, Except.bind]
  let rots : List Int :=
    List.map (fun i => -((bf + 1 : Nat) : Int) + (i : Int))
      (List.flatMap (fun a => pure ((a : Nat) : Int)) (List.range (bf + 2)))
  have hone : ∀ (l : List Nat), (l.map (fun _ => 1)).sum = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        omega
  have hsz : (R.vk.domain.lIRange s2.alg.x s2.alg.xn rots).size = bf + 2 := by
    dsimp only [rots]
    rw [Midfall.LoweringV3.TranscriptRows.lIRange_size, List.length_map, List.length_flatMap]
    simp [List.length_range]
  have hcond : ((R.vk.domain.lIRange s2.alg.x s2.alg.xn rots).size == bf + 2) = true := by
    rw [hsz]
    exact beq_self_eq_true _
  rw [ite_eq_left hcond]
  exact ⟨_, rfl⟩

#assert_axioms blindingFactors_ok_of_valid [propext, Classical.choice, Quot.sound]
#assert_axioms lagrangeTriple_exists_of_valid [propext, Classical.choice, Quot.sound]

theorem snapshotLagrangeStep_exists_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (s2 : SnapAlgebra p G₁) :
    ∃ l, snapshotLagrangeStep (G₁ := G₁) R.vk s2 = .ok l := by
  obtain ⟨tri, htri⟩ := lagrangeTriple_exists_of_valid R hR s2
  let l : SnapLagrange p G₁ :=
    { toSnapAlgebra := s2, lagrange := tri, instanceEval := instanceEvalOf R.vk s2.alg }
  refine ⟨l, ?_⟩
  simp only [snapshotLagrangeStep, htri, Bind.bind, Except.bind, pure, Except.pure, l]

#assert_axioms snapshotLagrangeStep_exists_of_valid [propext, Classical.choice, Quot.sound]

open Midfall.LoweringV3.LagrangeRows Midfall.LoweringV3.LagrangeBlock

omit [Fact (Nat.Prime p)] in
theorem holdsFr_of_loadWord {st : EvmState} {a : Nat} {x : Fr p}
    (h : loadWord st.memory a = frWord x) : holdsFr st a x = true := by
  simp [holdsFr, wordAt, h]

/-- The five `.lagrange` `InvAt` slot clauses from `LagInnerPost`'s progress arm. The two
    parser-side data are named: `hxn` (the algebra's square) and `hinst`/`hInstEval` (the
    decoded instance row and its evaluation linkage). -/
theorem lagInnerPost_lagrange_slots
    {product : PairingProduct} {g : ExternalGas}
    (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hm : 2 ≤ R.pv.numNegLagranges) (hn : 1 ≤ R.pv.numInstances)
    (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ)
    (s2 : SnapAlgebra p G₁) (l : SnapLagrange p G₁)
    (hl : snapshotLagrangeStep (G₁ := G₁) R.vk s2 = .ok l)
    (hS_alg : S.alg = s2.alg)
    (hS_lag : S.lagrange = l.lagrange)
    (hS_inst : S.instanceEval = l.instanceEval)
    (hxn : s2.alg.xn = s2.alg.x ^ (2 ^ R.pv.k))
    (hinstWord : ∀ j, cdWord cd (R.pv.proofLayout.proofEnd + 32 + 32 * j) =
      frWord ((s2.alg.instanceEvals.getD 0 #[]).getD j 0))
    (hInstEval : ∀ W : LagWords,
      LagRel (BitVec.ofNat 256 p) (Midfall.Halo2.frWord s2.alg.x)
        (Midfall.Halo2.frWord R.vk.domain.omega)
        (Midfall.Halo2.frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges))
        (Midfall.Halo2.frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹)) R.pv.k
        R.pv.numInstances R.pv.numNegLagranges
        (fun j => Midfall.Halo2.frWord ((s2.alg.instanceEvals.getD 0 #[]).getD j 0)) W →
      ∀ e, l.instanceEval = some e → W.instEval = Midfall.Halo2.frWord e)
    {V : VEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    {st st' : EvmState}
    (hpost : LagInnerPost (lagCfgOf R cd S) V st st')
    (hsucc1 : VEnv.get V "success" = some (1 : U256)) :
    holdsFr st' (ptrAddr R.pv.memory.xNMptr) S.alg.xn = true ∧
    holdsFr st' (ptrAddr R.pv.memory.lLastMptr) S.lagrange.lLast = true ∧
    holdsFr st' (ptrAddr R.pv.memory.lBlindMptr) S.lagrange.lBlind = true ∧
    holdsFr st' (ptrAddr R.pv.memory.l0Mptr) S.lagrange.l0 = true ∧
    (match S.instanceEval with
     | none => True
     | some e => holdsFr st' (ptrAddr R.pv.memory.instanceEvalMptr) e = true) := by
  obtain ⟨ret, pf, hsucc', hpf', -, -, -, -, hinv⟩ := hpost
  have hret1 : ret = 1 := Option.some.inj (hsucc'.symm.trans hsucc1)
  subst hret1
  obtain ⟨W, hW, hxnSlot, -, hllSlot, hlbSlot, hl0Slot, hieSlot⟩ :=
    hinv (by decide : (1 : U256) ≠ 0)
  have hW' : LagRel (BitVec.ofNat 256 p) (Midfall.Halo2.frWord s2.alg.x)
      (Midfall.Halo2.frWord R.vk.domain.omega)
      (Midfall.Halo2.frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges))
      (Midfall.Halo2.frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹)) R.pv.k
      R.pv.numInstances R.pv.numNegLagranges
      (fun j => Midfall.Halo2.frWord ((s2.alg.instanceEvals.getD 0 #[]).getD j 0)) W := by
    simpa [lagCfgOf, hS_alg, hinstWord] using hW
  obtain ⟨bf, hbf⟩ := blindingFactors_ok_of_valid R hR
  obtain ⟨Lw, hval, hBlindW⟩ :=
    lag_agrees_hval R hR hm hn s2 l hl hxn (s2.alg.instanceEvals.getD 0 #[]) W rfl hW' bf hbf
  obtain ⟨hxnVal, hllVal, hlbVal, hl0Val, _⟩ :=
    lag_agrees R hR hm hn s2 l hl hxn (s2.alg.instanceEvals.getD 0 #[]) W rfl hW' bf hbf Lw hval hBlindW
      (hInstEval W hW')
  have hxnSlot' : loadWord st'.memory (ptrAddr R.pv.memory.xNMptr) = W.xn := by
    simpa [lagCfgOf] using hxnSlot
  have hllSlot' : loadWord st'.memory (ptrAddr R.pv.memory.lLastMptr) = W.lLast := by
    simpa [lagCfgOf] using hllSlot
  have hlbSlot' : loadWord st'.memory (ptrAddr R.pv.memory.lBlindMptr) = W.lBlind := by
    simpa [lagCfgOf] using hlbSlot
  have hl0Slot' : loadWord st'.memory (ptrAddr R.pv.memory.l0Mptr) = W.l0 := by
    simpa [lagCfgOf] using hl0Slot
  have hieSlot' : loadWord st'.memory (ptrAddr R.pv.memory.instanceEvalMptr) = W.instEval := by
    simpa [lagCfgOf] using hieSlot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [holdsFr, wordAt, hxnSlot', hxnVal, hS_alg]
  · simp [holdsFr, wordAt, hllSlot', hllVal, hS_lag]
  · simp [holdsFr, wordAt, hlbSlot', hlbVal, hS_lag]
  · simp [holdsFr, wordAt, hl0Slot', hl0Val, hS_lag]
  · cases h : S.instanceEval with
    | none => trivial
    | some e =>
        have hle : l.instanceEval = some e := by rw [← hS_inst]; exact h
        have hWe := hInstEval W hW' e hle
        simp [holdsFr, wordAt, hieSlot', hWe]

#assert_axioms lagInnerPost_lagrange_slots [propext, Classical.choice, Quot.sound]
/-- The table's `MODEXP_GAS` is the model's scheduled modexp gas. -/
theorem consts_lookup_MODEXP_GAS (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.consts.lookup "MODEXP_GAS" = some R.model.templateConstants.gas.modexp := by
  show (Midfall.LoweringV2.constTableOf R.model).lookup "MODEXP_GAS" =
    some R.model.templateConstants.gas.modexp
  rw [Midfall.LoweringV3.lookup_expectedConsts_of_programOkB (programOkB_of_valid hR)]
  cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
    cases h3 : R.model.expectedQuotientCodehash <;> cases h4 : R.model.expectedHasAccumulator <;>
      simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

#assert_axioms consts_lookup_MODEXP_GAS [propext, Classical.choice, Quot.sound]


/-- The `.vk` payload pin, extracted from `Inv .vk`. -/
theorem inv_vk_payload {calls : ExternalCalls} {gas : ExternalGas}
    {E : VerifierEnv p G₁ G₂ Gₜ} {params : ParamsVerifierKZG G₁ G₂}
    {PV : PlanView} {S : Snapshot p G₁ G₂ Gₜ} {V : VEnv (Bridge.Dialect calls gas)}
    {st : EvmState}
    (h : Midfall.Lowering.Inv E params Checkpoint.vk PV S V st) :
    bytesAt st (ptrAddr PV.memory.vkMptr) PV.vk.len = PV.vk.bytes := by
  have h1 := h
  unfold Midfall.Lowering.Inv at h1
  simp only [InvAt] at h1
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h1
  have hvv : (1 : Nat) ≤ 1 := by decide
  have htv : ¬ (2 : Nat) ≤ 1 := by decide
  have hiv : ¬ (3 : Nat) ≤ 1 := by decide
  have hlv : ¬ (4 : Nat) ≤ 1 := by decide
  have hqv : ¬ (5 : Nat) ≤ 1 := by decide
  simp only [hvv, htv, hiv, hlv, hqv, ite_true, ite_false, Bool.false_eq_true] at h1
  simp only [Bool.and_eq_true] at h1
  have hh := h1.1.1.1.1.1.2.1.1
  change ((bytesAt st (ptrAddr PV.memory.vkMptr) PV.vk.len).data == PV.vk.bytes.data) = true at hh
  exact ByteArray.ext (beq_iff_eq.mp hh)

/-- `lagPre_of_inv_transcript_of_payload` with the payload window read off `Inv .vk`. -/
theorem lagPre_of_inv_transcript_of_vk (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hframe : Frame R H vkAddr cd V st)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hpf : VEnv.get V "lagrange_precompile_failed" = some (0 : U256))
    (hinv : Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params Checkpoint.vk
      R.pv S V st)
    (hx : loadWord st.memory (lagCfgOf R cd S).aX = (lagCfgOf R cd S).xw) :
    LagrangeBlock.LagPre (lagCfgOf R cd S) V st :=
  lagPre_of_inv_transcript_of_payload R hR cd S H vkAddr V st hframe hsucc hpf hx
    (pg_omegainv_slot hR)
    (readBytes_of_bytesAt (inv_vk_payload hinv))


end Midfall.LoweringV3

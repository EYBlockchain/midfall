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
   `batch_invert` call) is the ONLY uncovered inner statement. The row still needs the
   whole-block composition whose post is
   `∃ W, LagRel … W ∧ <the six slots hold W's words> ∧ <memory outside the denominator/scratch/slot
   windows unchanged>`; that composition is the T3.9.f card and cannot be stated honestly until
   the call segment's post exists.
2. **T3.9.h `lag_poison` is absent.** Its proof needs the whole-block normal-run composition and
   the poison arm of the `batch_invert` call (A5). The fixed prelude itself is no longer the
   blocker: statements 0-9 bind `mptr`/`mptr_end` and write the denominator window inside the
   inner block, so the loop preconditions are reached by the landed segment contracts.
3. **A5 `batch_invert_summary` is absent.** It supplies statement 10's `success = 0` / `ret = 0`
   call fact (and the `ret = 1` arm for progress), hence both the whole-block post and
   `lag_poison`.

Therefore `lag_blockSim`/`lag_blockProgS` remain the existing registered leaves; no row hypothesis
has been added and no new `sorry` is introduced here. When 1–3 land, the rows are pure glue.
-/

/-! ## 3. lagrange (owner T3.9, WP A4) -/

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

/-- **LEAF (ROW.PCS, WP A10): the pcs simulation row.** Evidence `GeneratorRows.lean:1013`. -/
theorem pcs_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.pcs H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **LEAF (ROW.PCS, WP A10): the pcs progress row.** Evidence `GeneratorRows.lean:1019`; its decode
    half is ROW.PCS's `decode_exists`. -/
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

/-- **LEAF (ROW.FP, WP A11): the finalPairing progress row.** Evidence `GeneratorRows.lean:1083`. -/
theorem fp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.finalPairing H vkAddr product cd := by
  sorry

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

end Midfall.LoweringV3

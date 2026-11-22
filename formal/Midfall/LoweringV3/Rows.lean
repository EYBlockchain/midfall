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
import Midfall.LoweringV3.VkClean
import Midfall.LoweringV2.Blocks.TraceReturn
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

/-- **LEAF (GEN.1, WP A3): the vkLoading progress row.** Evidence `GeneratorRows.lean:1103`. -/
theorem vk_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.vkLoading H vkAddr product cd := by
  sorry

/-! ## 2. transcriptParser (owner ROW.TP, WP A6) -/

/-- **LEAF (ROW.TP, WP A6): the transcriptParser simulation row.** Evidence `GeneratorRows.lean:817`;
    its children (tp_computes, tp_agrees, tp_poison) land with ROW.TP (consumer first). -/
theorem tp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.transcriptParser H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **LEAF (ROW.TP, WP A6): the transcriptParser progress row.** Evidence `GeneratorRows.lean:830`. -/
theorem tp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.transcriptParser H vkAddr product cd := by
  sorry

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

/-- **LEAF (ROW.FP, WP A11): the finalPairing simulation row.** Evidence `GeneratorRows.lean:1077`;
    children are `ec_pairing_sem`, `fp_pairing_algebra`, `fp_poison`. -/
theorem fp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.finalPairing H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **LEAF (ROW.FP, WP A11): the finalPairing progress row.** Evidence `GeneratorRows.lean:1083`. -/
theorem fp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.finalPairing H vkAddr product cd := by
  sorry

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

end Midfall.LoweringV3

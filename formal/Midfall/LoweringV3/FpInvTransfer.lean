/-
  Midfall.LoweringV3.FpInvTransfer

  ROW.FP (WP A11) - the `Inv .pcs -> Inv .pairing` transfer.

  The two checkpoints differ in exactly two places: the `.pairing` arm adds
  `success = 1` and `DualMSM.check`, and the selector-bucket clause is live at
  `.pcs` but dropped at `.pairing`.  `selectorBucket_mono` handles the second;
  `hsucc`/`hdual` handle the first.  The chunk of work is extracting the
  quotient-evaluation `holdsFr` out of the thirty-clause `InvAt` conjunction, so
  the proof fixes the checkpoint indices to numerals, splits the chain, and reads
  the quotient arm's fifth leaf directly.  No new hypothesis; zero sorry.
-/
import Midfall.LoweringV3.FpWire

set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

namespace Midfall.Lowering

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

set_option maxHeartbeats 800000 in
theorem Inv_pairing_of_pcs {calls : ExternalCalls} {gas : ExternalGas}
    {E : VerifierEnv p G₁ G₂ Gₜ} {params : ParamsVerifierKZG G₁ G₂}
    {PV : PlanView} {S : Snapshot p G₁ G₂ Gₜ} {V : VEnv (Bridge.Dialect calls gas)}
    {st : EvmState}
    (h : Midfall.Lowering.Inv E params Checkpoint.pcs PV S V st)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hdual : DualMSM.check S.c.dual params = true) :
    Midfall.Lowering.Inv E params Checkpoint.pairing PV S V st := by
  unfold Midfall.Lowering.Inv at h ⊢
  simp only [InvAt] at h ⊢
  simp only [checkpoint_le_def, Checkpoint.idx] at h ⊢
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  have h16 : (1 : Nat) ≤ 6 := by decide
  have h26 : (2 : Nat) ≤ 6 := by decide
  have h36 : (3 : Nat) ≤ 6 := by decide
  have h46 : (4 : Nat) ≤ 6 := by decide
  have h56 : (5 : Nat) ≤ 6 := by decide
  simp only [h15, h25, h35, h45, h55, h16, h26, h36, h46, h56, if_true] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  cases hlin : S.lin with
  | none =>
      simp_all
  | some L =>
      simp only [Bool.and_eq_true] at h ⊢
      simp only [and_assoc] at h
      rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
      simp_all [hlin]
      have hif : (if Checkpoint.liveRegionNamed Checkpoint.pcs PV.memory "selector_accumulators"
          then holdsFrs st PV.memory.selectorAccMptr (linComBuckets L.linCom) else true) = true := by
        rcases h29.2 with hf | hp
        · simp [hf]
        · simp [hp]
      simpa using selectorBucket_mono PV.memory
        (holdsFrs st PV.memory.selectorAccMptr (linComBuckets L.linCom)) hif

#assert_axioms Midfall.Lowering.Inv_pairing_of_pcs
  [propext, Classical.choice, Quot.sound] native []

end Midfall.Lowering

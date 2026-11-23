/-
  Midfall.LoweringV3.FpClean

  ROW.FP (WP A11) - the two G1 slot reads `Inv .pcs` pins, extracted as named
  lemmas rather than re-derived at every clean-arm use site.  The extraction is
  the same checkpoint-index reduction and chain split as `Inv_pairing_of_pcs`.
-/
import Midfall.LoweringV3.FpConsts

set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

namespace Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

set_option maxHeartbeats 800000 in
theorem Inv_pcs_pairingLhs {calls : ExternalCalls} {gas : ExternalGas}
    {R : Render p G₁ G₂ Gₜ} {S : Snapshot p G₁ G₂ Gₜ}
    {V : VEnv (Bridge.Dialect calls gas)} {st : EvmState}
    (h : Midfall.Lowering.Inv R.E R.params Checkpoint.pcs R.pv S V st) :
    holdsG1 R.E st (ptrAddr R.pv.memory.pairingLhsMptr) S.c.dual.left.eval = true := by
  unfold Midfall.Lowering.Inv at h
  simp only [Midfall.Lowering.InvAt] at h
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  simp only [h15, h25, h35, h45, h55, if_true] at h
  simp only [Bool.and_eq_true] at h
  simp only [and_assoc] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  exact h32.2.1

set_option maxHeartbeats 800000 in
theorem Inv_pcs_pairingRhs {calls : ExternalCalls} {gas : ExternalGas}
    {R : Render p G₁ G₂ Gₜ} {S : Snapshot p G₁ G₂ Gₜ}
    {V : VEnv (Bridge.Dialect calls gas)} {st : EvmState}
    (h : Midfall.Lowering.Inv R.E R.params Checkpoint.pcs R.pv S V st) :
    holdsG1 R.E st (ptrAddr R.pv.memory.pairingRhsMptr) S.c.dual.right.eval = true := by
  unfold Midfall.Lowering.Inv at h
  simp only [Midfall.Lowering.InvAt] at h
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  simp only [h15, h25, h35, h45, h55, if_true] at h
  simp only [Bool.and_eq_true] at h
  simp only [and_assoc] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  exact h32.2.2.1

#assert_axioms Midfall.LoweringV3.Inv_pcs_pairingLhs
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.Inv_pcs_pairingRhs
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3

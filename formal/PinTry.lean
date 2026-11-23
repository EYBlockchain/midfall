import Midfall.LoweringV3.Totality
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage
open Midfall.Generator.PlanNew Midfall.Generator.QuotientEvaluator

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem inv_pcs_pairing_pins {calls : ExternalCalls} {gas : ExternalGas}
    {E : VerifierEnv p G₁ G₂ Gₜ} {params : ParamsVerifierKZG G₁ G₂}
    {PV : PlanView} {S : Snapshot p G₁ G₂ Gₜ} {V : VEnv (Bridge.Dialect calls gas)}
    {st : EvmState}
    (h : Midfall.Lowering.Inv E params Checkpoint.pcs PV S V st) :
    bytesAt st (ptrAddr PV.memory.pairingRhsMptr) 128 = E.g1.toEip S.c.dual.right.eval ∧
      bytesAt st (ptrAddr PV.memory.pairingLhsMptr) 128 = E.g1.toEip S.c.dual.left.eval := by
  have h1 := h
  unfold Midfall.Lowering.Inv at h1
  simp only [InvAt] at h1
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h1
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  have hpcs : (Checkpoint.pcs == Checkpoint.pairing) = false := by decide
  simp only [h15, h25, h35, h45, h55, ite_true, hpcs, Bool.false_eq_true, ite_false] at h1
  cases hlin : S.lin with
  | none =>
      simp only [hlin, Bool.and_eq_true] at h1
      refine ⟨?_, ?_⟩
      · have hh := h1.1.2.2
        change ((bytesAt st (ptrAddr PV.memory.pairingRhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.right.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)
      · have hh := h1.1.2.1.2
        change ((bytesAt st (ptrAddr PV.memory.pairingLhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.left.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)
  | some L =>
      simp only [hlin, Bool.and_eq_true] at h1
      refine ⟨?_, ?_⟩
      · have hh := h1.1.2.2
        change ((bytesAt st (ptrAddr PV.memory.pairingRhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.right.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)
      · have hh := h1.1.2.1.2
        change ((bytesAt st (ptrAddr PV.memory.pairingLhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.left.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)

end Midfall.LoweringV3

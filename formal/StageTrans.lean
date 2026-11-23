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

/-- The clean `.pcs → .pairing` boundary transport at the STAGED invariant: the frame, the
    success bit and the `.pcs`-to-`.pairing` compatibility of the raw/mirror clauses survive by
    construction; only `Agree` needs work, and that is `leanStage_pairing_of` plus
    `Inv_pairing_of_pcs`, both proved.  The `hdual` hypothesis is the pairing answer (the one
    semantic fact the helper supplies). -/
theorem stageInv_pairing_of_pcs {calls : ExternalCalls} {gas : ExternalGas}
    (R : Render p G₁ G₂ Gₜ) {H : Hash} {vkAddr : U256} {cd : Bytes}
    {V : VEnv (Bridge.Dialect calls gas)} {st : EvmState}
    (h : StageInv R H vkAddr cd Checkpoint.pcs V st)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hdual : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
      ∀ S, leanStage R H inst ms Checkpoint.pcs = .ok S →
        DualMSM.check S.c.dual R.params = true) :
    StageInv R H vkAddr cd Checkpoint.pairing V st := by
  obtain ⟨hframe, -, -, hraw, -, hagree⟩ := h
  refine ⟨hframe, hsucc, trivial, hraw, trivial, ?_⟩
  intro ms instW inst hdec
  obtain ⟨S, hstage, hinv⟩ := hagree ms instW inst hdec
  have hsnap : snapshotOf R.E H R.vk inst ms none = .ok S := by
    simpa only [leanStage] using hstage
  have hck := hdual ms instW inst hdec S hstage
  exact ⟨S, leanStage_pairing_of hsnap hck, Inv_pairing_of_pcs hinv hsucc hck⟩

end Midfall.LoweringV3

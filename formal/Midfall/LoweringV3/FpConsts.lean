/-
  Midfall.LoweringV3.FpConsts

  ROW.FP (WP A11) - the five constant-table lookups the `ec_pairing` helper reads,
  and the helper declaration at the explicit literal body.  Each lookup is the
  generic ValidV3 transfer applied to the `expectedConsts` entry; the entries sit
  in the trailing table, past the four optional-arm segments, so the proof cases
  those four fields and lets `List.lookup` reduce.  No new hypothesis.
-/
import Midfall.LoweringV3.FpInvTransfer

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

theorem consts_lookup_G2_BASE_MPTR (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.consts.lookup "G2_BASE_MPTR" =
      some (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base)) := by
  apply Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR
  cases h1 : R.model.expectedVkCodehash <;>
  cases h2 : R.model.quotientExternal <;>
  cases h3 : R.model.expectedQuotientCodehash <;>
  cases h4 : R.model.expectedHasAccumulator <;>
    simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

theorem consts_lookup_NEG_S_G2_BASE_MPTR (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.consts.lookup "NEG_S_G2_BASE_MPTR" =
      some (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base)) := by
  apply Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR
  cases h1 : R.model.expectedVkCodehash <;>
  cases h2 : R.model.quotientExternal <;>
  cases h3 : R.model.expectedQuotientCodehash <;>
  cases h4 : R.model.expectedHasAccumulator <;>
    simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

theorem consts_lookup_PAIRING_GAS_2PAIR (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.consts.lookup "PAIRING_GAS_2PAIR" = some R.model.templateConstants.gas.pairingTwoPair := by
  apply Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR
  cases h1 : R.model.expectedVkCodehash <;>
  cases h2 : R.model.quotientExternal <;>
  cases h3 : R.model.expectedQuotientCodehash <;>
  cases h4 : R.model.expectedHasAccumulator <;>
    simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

theorem consts_lookup_ERR_PRECOMPILE_FAILED (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.consts.lookup "ERR_PRECOMPILE_FAILED" = some 0x84e81692 := by
  apply Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR
  cases h1 : R.model.expectedVkCodehash <;>
  cases h2 : R.model.quotientExternal <;>
  cases h3 : R.model.expectedQuotientCodehash <;>
  cases h4 : R.model.expectedHasAccumulator <;>
    simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

theorem consts_lookup_ERR_PROOF_REJECTED (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.consts.lookup "ERR_PROOF_REJECTED" = some 0xc3b0d8cd := by
  apply Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR
  cases h1 : R.model.expectedVkCodehash <;>
  cases h2 : R.model.quotientExternal <;>
  cases h3 : R.model.expectedQuotientCodehash <;>
  cases h4 : R.model.expectedHasAccumulator <;>
    simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

theorem ecPairingDecl_eq_lit (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (c : ExternalCalls) (g : ExternalGas) :
    Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R c g =
      { params := ["success", "lhs_mptr", "rhs_mptr"], rets := ["ret"],
        body := Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
          (GenAst.pairingScratchOf R.pv)
          (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base))
          (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base))
          R.model.templateConstants.gas.pairingTwoPair 0x0f 768 32 0x84e81692 0xc3b0d8cd } := by
  rw [Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl_eq]
  congr 1
  apply Midfall.LoweringV2.Blocks.EcPairing.ecPairingBody_eq_lit
  · simp [Midfall.LoweringV2.Blocks.EcPairing.ecVal,
      consts_lookup_G2_BASE_MPTR R hR]
  · simp [Midfall.LoweringV2.Blocks.EcPairing.ecVal,
      consts_lookup_NEG_S_G2_BASE_MPTR R hR]
  · simp [Midfall.LoweringV2.Blocks.EcPairing.ecVal,
      consts_lookup_PAIRING_GAS_2PAIR R hR]
  · simp [Midfall.LoweringV2.Blocks.EcPairing.ecVal,
      consts_lookup_ERR_PRECOMPILE_FAILED R hR]
  · simp [Midfall.LoweringV2.Blocks.EcPairing.ecVal,
      consts_lookup_ERR_PROOF_REJECTED R hR]

#assert_axioms Midfall.LoweringV3.consts_lookup_G2_BASE_MPTR
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.consts_lookup_NEG_S_G2_BASE_MPTR
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.consts_lookup_PAIRING_GAS_2PAIR
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.consts_lookup_ERR_PRECOMPILE_FAILED
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.consts_lookup_ERR_PROOF_REJECTED
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ecPairingDecl_eq_lit
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3

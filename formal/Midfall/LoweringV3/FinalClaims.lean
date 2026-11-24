/-
  Midfall.LoweringV3.FinalClaims

  FINAL ASSEMBLY - **THE GENERIC CLAIM SURFACE, IN ONE PLACE.**

  This module states nothing new mathematically. It is the index and the gate for the GENERIC
  claims, i.e. the ones whose statements quantify over an arbitrary `Render`/`GenInput` and carry
  no fixture, no `native_decide` and no `Midfall.Instances` import (checks.sh's import-confinement
  rule). The four claims PLAN-V3 §6 asks for are:

    * `lowering_correct`          - the headline, `ValidV3 R -> LoweringEquivalenceV3 R product`
                                    (defined in `GeneratorTheorem.lean`, imported here);
    * `generator_correct_V3`      - the certified-generator form, hypotheses on `GenInput` only
                                    (defined in `Generator/Certified.lean`, imported here);
    * `EndToEndV3`                - the M8 endpoint. `EndToEndV3` itself is a definition in
                                    `Statements.lean`; `end_to_end_of_lowering_correct` below is
                                    the theorem that reaches it from `ValidV3` alone (plus the one
                                    named `PrepareLogSlots` bridge and the execution data), with
                                    the headline's `hEq` discharged by `lowering_correct` rather
                                    than assumed;
    * the GENERIC non-vacuity bridges (`hypothesesInhabitedV3_of_gateAtV3`,
                                    `returns_of_inhabited`) - exposed in §1, no fixture;
    * `DoneAt` at `f1PointRenderCCN n` - the F1-REAL claim. It is deliberately NOT in this module:
                                    it consumes F1 data and trust-boundary facts, so it lives in
                                    `Midfall.Instances.GeneratorDoneAt` (`f1PointRenderCCN_doneAt`)
                                    where the import-confinement rule keeps fixture computation
                                    out of every theorem-bearing generic file. The split is the
                                    PLAN-V3 one: generic claims here, F1-real data/trust claims
                                    under `Instances/`.

  The gates below are the D-P71 shape while the seven-block case table still has four open rows
  (`BlockLive.lean`): `sorryAx` is named because those leaves are open; the native list is EMPTY,
  which is the half of the gate D-P71 exists for - no fixture computation reaches a generic claim.
  Closing `BlockLive` deletes `sorryAx` from these lists and nothing else.
-/
import Midfall.LoweringV3.GeneratorTheorem
import Midfall.LoweringV3.EndToEnd
import Midfall.Generator.Certified
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. The headline and the certified generator, exposed on the final surface -/

#check @Midfall.LoweringV3.lowering_correct
#check @Midfall.Generator.Certified.generator_correct_V3
#check @Midfall.Generator.Certified.generator_certified

-- GENERIC NON-VACUITY (no fixture): a headline at a gated render gives an honest returning run.
-- `hypothesesInhabitedV3_of_gateAtV3` (the gate -> `HypothesesInhabitedV3` bridge) is stated in
-- `Instances/GeneratorDone.lean`; it is F1-adjacent by construction, so it is checked in
-- `Instances/FinalClaimsF1.lean`, not in this generic module.
#check @Midfall.LoweringV3.returns_of_inhabited

/-! ## 2. `EndToEndV3` from the headline, with `hEq` discharged -/

/-- **END TO END, FROM `ValidV3` ALONE (plus the one named `PrepareLogSlots` bridge).** This is
    `end_to_end_of_prepareLogSlots` with its `hEq : LoweringEquivalenceV3 R product` hypothesis
    supplied by `lowering_correct`, so the claim no longer assumes the headline. The statement is
    the full `EndToEndV3` signature; `PrepareLogSlots R` is the D1 read-schedule bridge, not a
    `ValidV3`/row/root hypothesis. No fixture occurs. -/
theorem end_to_end_of_lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd)
    (h : PrepareLogSlots R) :
    EndToEndV3 R product hR (lowering_correct R product hR) W Lyt vkAddr hdep hcv hpc hcodec
      inst π hn hside :=
  end_to_end_of_prepareLogSlots R product hR (lowering_correct R product hR)
    W Lyt vkAddr hdep hcv hpc hcodec inst π hn hside h

/-! ## 3. The gates -/

#check @Midfall.LoweringV3.end_to_end_of_lowering_correct

#cone_sorries Midfall.LoweringV3.lowering_correct
#cone_sorries Midfall.LoweringV3.end_to_end_of_lowering_correct
#cone_sorries Midfall.Generator.Certified.generator_correct_V3

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.lowering_correct
  [propext, Classical.choice, Quot.sound, sorryAx] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.end_to_end_of_lowering_correct
  [propext, Classical.choice, Quot.sound, sorryAx] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.Generator.Certified.generator_correct_V3
  [propext, Classical.choice, Quot.sound, sorryAx] native []

end Midfall.LoweringV3

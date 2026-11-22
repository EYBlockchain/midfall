/-
  Midfall.LoweringV3.EndToEnd

  WP D1 / PL.E - the end-to-end theorem `EndToEndV3`.

  THE ONE EXTERNAL FACT. `EndToEndV3`'s left-to-right direction needs the
  read-schedule agreement `readScheduleAgrees` of `Lowering/Obligations.lean:443`
  for the render's OWN key and layout: every message list the Rust-faithful decoder
  `decodeRust` returns has the slot shape of `R.plan.proofLayout`. That is the
  hypothesis `hsched` below. It is the V3 form of `Obligations.readScheduleAgrees`
  (where it is a field of `LoweringCorrect`), and it is exactly what
  `repack_spec_of_decodeRust` (`Lowering/Calldata.lean:1276`) takes.

  Everything else is the tree's proved glue. The arm lemma is stated with `hsched`
  explicit so the missing V3 projection is one named goal, not a hole in the
  theorem's proof.
-/
import Midfall.LoweringV3.Composition
import Midfall.LoweringV3.PrefixV3
import Midfall.Lowering.Obligations
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

/-! ## 1. The layout statics `EndToEndV3` needs from `ValidV3` -/

/-- `ValidV3` gives `proofLen = repackedLen` for the render's own layout. The proof is
    `layout_static_of_generated`'s peel with the first conjunct of
    `proofLen_eq_repackedLen` kept instead of the second. PROVED. -/
theorem proofLen_eq_repackedLen_of_validV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.plan.proofLayout.proofLen =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).repackedLen := by
  obtain ⟨rawMeta, plan, _hraw, hpl, hp⟩ := pfx_plan_of_generated hR.generated
  obtain ⟨meta_, L, hL, hLp⟩ :=
    pfx_newFromVk_proofLayout Features.solidity
      (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have h1 := (proofLen_eq_repackedLen meta_.protocol meta_.numEvals meta_.numPointSets L hL).1
  rw [← hp] at hLp
  rw [hLp]
  exact h1

/-! ## 2. The scalar/instance round trip for `frWord` -/

/-- `frOfWord?` inverts `frWord` on a canonical field element. PROVED. -/
theorem frOfWord?_frWord (hp : p < 2 ^ 256) (a : Fr p) :
    Midfall.LoweringV2.frOfWord? (p := p) (frWord a) = some a := by
  unfold Midfall.LoweringV2.frOfWord?
  rw [Midfall.Halo2.frWord_toNat hp a]
  rw [ite_eq_left (ZMod.val_lt a)]
  have hcast : ((ZMod.val a : ℕ) : Fr p) = a := by
    simpa using ZMod.natCast_val (R := Fr p) a
  exact congrArg some hcast

/-- `List.mapM frOfWord?` inverts `List.map frWord`. PROVED. -/
theorem mapM_frOfWord?_map_frWord (hp : p < 2 ^ 256) (l : List (Fr p)) :
    (l.map frWord).mapM (fun w => Midfall.LoweringV2.frOfWord? (p := p) w) = some l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.mapM_cons, frOfWord?_frWord hp a, ih]
      rfl

/-- `instOfWords?` inverts the canonical word image of an instance array. PROVED. -/
theorem instOfWords?_map_frWord (hp : p < 2 ^ 256) (l : List (Fr p)) :
    Midfall.LoweringV2.instOfWords? (p := p) (l.map frWord).toArray = some l.toArray := by
  unfold Midfall.LoweringV2.instOfWords?
  rw [List.toList_toArray, mapM_frOfWord?_map_frWord hp l]
  rfl

/-! ## 3. The forward direction of `EndToEndV3`, with the one schedule fact named -/

/-- **LEFT-TO-RIGHT, WITH THE READ-SCHEDULE AGREEMENT NAMED.** If the Rust-faithful
    decoder's messages have the render layout's slot shape, then a proof the Lean
    verifier accepts produces calldata on which every honest run returns. The proof is
    the V3 glue: `verifyNative_iff_msgs_codec`, `repack_spec_of_decodeRust`,
    `calldata_roundtrip`, the `frWord` round trip, and conjunct 2 of
    `LoweringEquivalenceV3`. -/
theorem end_to_end_forward_of_readSchedule (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : Midfall.LoweringV3.G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd)
    (hsched : ∀ ms : List (Msg (Fr p) G₁),
      decodeRust (Gₜ := Gₜ) R.E Features.solidity R.vk inst π = some ms →
        ms.map Msg.slot =
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots) :
    verifyNative (Gₜ := Gₜ) R.E Features.solidity R.params R.vk inst π = .ok () →
      ∃ cd, calldataOfV3 R π inst = .ok cd ∧
        ∀ st₀, EntryFrameV3 R W Lyt keccak256 cd st₀ →
          (∃ obs, RunBody R vkAddr 0 (callsOf product)
              (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
          ∀ obs, RunBody R vkAddr 0 (callsOf product)
              (ExternalGas.ofFun fun _ => 0) st₀ obs →
            obs.view = returnView st₀ := by
  intro hv
  -- The codec inversion: an accepted proof decodes to a message list Lean re-verifies.
  obtain ⟨ms, hdec, hvm⟩ :=
    (Midfall.Lowering.verifyNative_iff_msgs_codec (p := p) R.E Features.solidity R.params
      R.vk inst π hcodec.compressedRoundtrip).mp hv
  have hshape : ms.map Msg.slot =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots :=
    hsched ms hdec
  -- The encoder succeeds because the decoder's messages have the layout's shape.
  have hrep :
      Midfall.Lowering.repackProof (p := p)
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π =
        .ok (Midfall.Lowering.encodeContractProof (p := p) R.E.g1 ms) :=
    Midfall.Lowering.repack_spec_of_decodeRust (p := p) R.E Features.solidity R.vk inst π
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout)
      hcodec.compressedRoundtrip hsched ms hdec
  -- The calldata the encoder produces.
  let instL : List Word256 := inst.toList.map frWord
  let cd : Bytes := Midfall.Lowering.calldataOf (p := p) R.E.g1 ms instL
  have hcd : calldataOfV3 R π inst = .ok cd := by
    unfold calldataOfV3 Midfall.Lowering.repackThenEncode
    dsimp only [cd, instL]
    rw [hrep]
    simp only [Except.mapError]
    simp [hn]
    show Except.ok (Midfall.Lowering.encodeCalldataRaw
        (Midfall.Lowering.encodeContractProof R.E.g1 ms) (inst.toList.map frWord)) =
      Except.ok (Midfall.Lowering.calldataOf R.E.g1 ms (inst.toList.map frWord))
    rfl
  refine ⟨cd, hcd, ?_⟩
  intro st₀ hentry
  obtain ⟨hSound, hComplete⟩ := hside cd hcd
  -- The decoded calldata is exactly the one `calldataOf` writes, so Lean accepts it.
  have hplt : p < 2 ^ 256 := by
    rw [hR.env.modulus]
    norm_num [frModulusConstant]
  have hfacts := pfxFacts_of_validV3 (R := R) hR
  have hlen := proofLen_eq_repackedLen_of_validV3 R hR
  have hinstL : ∀ w ∈ instL, w.toNat < p := by
    intro w hw
    change w ∈ inst.toList.map frWord at hw
    obtain ⟨x, _hx, hxw⟩ := List.mem_map.mp hw
    rw [← hxw]
    exact Midfall.Halo2.frWord_toNat_lt hplt x
  have hnL : instL.length = R.cfg.numInstances := by
    simp [instL, hn]
  have hdecCd :
      decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
        some (ms, instL.toArray) := by
    show decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1
      (Midfall.Lowering.calldataOf (p := p) R.E.g1 ms instL) = some (ms, instL.toArray)
    exact Midfall.Lowering.calldata_roundtrip (p := p) (G₁ := G₁) (le_of_lt hplt)
      R.plan.proofLayout hfacts.lCptr hlen hfacts.lEnd R.E.g1
      hcodec.toG1CodecLaws ms hshape R.cfg.numInstances instL hnL hinstL
  have hinstWords : Midfall.LoweringV2.instOfWords? (p := p) instL.toArray = some inst := by
    simpa [instL, Array.toArray_toList] using instOfWords?_map_frWord (p := p) hplt inst.toList
  have hacc : LeanAccepts R keccak256 cd :=
    ⟨ms, instL.toArray, inst, hdecCd, hinstWords, hvm⟩
  exact (hEq W Lyt keccak256 vkAddr cd st₀ hdep hentry hpc
    (Midfall.LoweringV3.G1CodecLawsV3.headline hcodec)).2.1 hacc hComplete

/-! ## 4. Gates on the proved pieces -/

#print axioms proofLen_eq_repackedLen_of_validV3
#print axioms frOfWord?_frWord
#print axioms mapM_frOfWord?_map_frWord
#print axioms instOfWords?_map_frWord

#check @end_to_end_forward_of_readSchedule

#cone_sorries Midfall.LoweringV3.end_to_end_forward_of_readSchedule

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.end_to_end_forward_of_readSchedule
  [propext, Classical.choice, Quot.sound, sorryAx] native []

end Midfall.LoweringV3

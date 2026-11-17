/-
  ReviewProbes.lean - machine-checked evidence for docs/plans/REVIEW-V3.md and docs/plans/PLAN-V3.md.

  NOT part of the build: this file lives under docs/, which no gate scans and `lake build` does not
  compile. Check it from the formal/ directory, after `lake build`:

      lake env lean docs/plans/V3-evidence/ReviewProbes.lean

  It is SELF-CHECKING: every fact is a `#guard`, a proved `theorem`/`example`, or a `#guard_msgs`
  pin on `#print axioms`, so the file elaborates with no error exactly while the recorded facts
  hold. Measured at commit f2fe99b (2026-11-17), Lean 4.35.0. A fact that stops elaborating after a
  repair is the repair's evidence: delete or flip that probe in the same commit as the repair.

  Finding ids (RV-nn) refer to docs/plans/REVIEW-V3.md.
-/
import Midfall.Instances.PoseidonV2
import Midfall.Instances.PoseidonValid
import Midfall.Instances.PoseidonFixture
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.Lowering.LegacyVacuity
import Midfall.Lowering.Calldata
import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Statements

set_option autoImplicit false

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Instances
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid

namespace Midfall.ReviewV3

/-! ## 1. Status of the headline (RV-01, RV-02) -/

/-- info: 'Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 bls12_381Pairing,
 blsGT,
 blsGT_group,
 blsGT_module,
 blsGT_primeOrder,
 poseidonModel_isOk._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon

/-- RV-02. The headline's cone contains a PROVABLY FALSE member: the registered hole
    `poseidon_valid` contradicts the proved `poseidonRender_notValid`. So `False` follows from the
    tree's registered holes, and a cone count taken while this holds measures nothing. -/
theorem false_from_registered_holes : False :=
  poseidonRender_notValid poseidon_valid

/-! ## 2. One "transport" lemma carries all of rejection, for every render (RV-10) -/

section
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-- `rejects_of_not_accepts` (Blocks.lean) takes neither `SoundSide` nor `R.Valid`. On its own it
    yields `R.Rejects product` for EVERY render, valid or not. -/
theorem rejects_for_every_render (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    R.Rejects product :=
  fun W Lyt H vkAddr cd st₀ g obs hdep hentry hpc _hside hna hobs =>
    rejects_of_not_accepts R product W Lyt H vkAddr cd st₀ g obs hdep hentry hpc hna hobs

/-- Hence soundness WITHOUT the `SoundSide` exclusion and WITHOUT validity, for every render. The
    project's own note at Lowering/Inv.lean:698-706 says the contract accepts on the logup set
    where Lean panics, so this conclusion is false and the lemma it rests on cannot be proved. -/
theorem soundness_for_every_render_no_side (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (g : ExternalGas) (obs : Obs)
    (hobs : RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs) (hret : obs.isReturn) :
    LeanAccepts R H cd := by
  by_contra hna
  exact not_isRevertOrHalt_of_isReturn hret
    (rejects_of_not_accepts R product W Lyt H vkAddr cd st₀ g obs hdep hentry hpc hna hobs)
end

/-! ## 3. The Lean verifier is not Rust-faithful on the fixture key (RV-03, RV-04) -/

section Grouping
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- RV-03. Rust groups one-piece commitments by ALLOCATION (`std::ptr::eq`,
    proofs/src/poly/query.rs:125); the port groups by VALUE (`kzgCommitBeq`,
    Exec/Kzg/MultiOpen.lean:42). Five distinct allocations holding one value, opened at one point
    - the shape of the fixture key's identity fixed commitments 8, 10, 11, 12, 16 - are an
    `Error.opening` in Lean and five separate entries in Rust. -/
def fiveEqualAtOnePoint : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRef
      (#[vq17 1 0 2, vq17 1 0 3, vq17 1 0 4, vq17 1 0 5, vq17 1 0 6]) with
  | Except.error (Fault.error Error.opening) => true
  | _ => false

/-- What allocation identity sees: five entries, no error. -/
def fiveDistinctAtOnePoint : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRef
      (#[vq17 1 10 2, vq17 1 11 3, vq17 1 12 4, vq17 1 13 5, vq17 1 14 6]) with
  | Except.ok (cms, _) => cms.size == 5
  | Except.error _ => false

#guard fiveEqualAtOnePoint
#guard fiveDistinctAtOnePoint
end Grouping

/-- RV-04. Rust's `Rotation::cur()` is `Rotation(0)`; the Lean `Rotation` has structural equality,
    and the imported constraint system spells every rotation `Rotation.value r`. Looking up
    `Rotation.cur`, as `Permutation` does, hits a Rust panic site for ALL EIGHT permutation columns
    of the fixture; looking up `Rotation.value 0` succeeds for all eight. -/
def permColumnsLookup (rot : Rotation) : List Bool :=
  PoseidonFixture.poseidonCs.permutation.columns.toList.map fun c =>
    match PoseidonFixture.poseidonCs.getAnyQueryIndex c rot with
    | .ok _ => true
    | .error _ => false

#guard permColumnsLookup Rotation.cur == List.replicate 8 false
#guard permColumnsLookup (Rotation.value 0) == List.replicate 8 true

/-! ## 4. At the deployment instance the Lean verifier can read no G1 point (RV-05) -/

/-- The deployment codec decodes NO compressed point. -/
example (b : Bytes) : poseidonRender.E.g1.ofCompressed? b = none := rfl

/-- So every G1 read of the Lean transcript fails there. `verifyMsgs` re-serialises each message
    and re-reads it through this codec (Exec/Native.lean:269-292), and every proof carries a G1
    message, so `LeanAccepts poseidonRender H cd` holds for no `H`, `cd`. -/
theorem read_g1CodecZ_err (t : Transcript) :
    ∃ e, t.read (hashableG1 g1CodecZ) = .error e := by
  unfold Transcript.read
  cases bytesTake t.buffer t.pos (hashableG1 g1CodecZ).width <;> simp [hashableG1, g1CodecZ]

/-- info: 'Midfall.ReviewV3.read_g1CodecZ_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_g1CodecZ_err

/-! ## 5. Frozen statements that are false or unsatisfiable as written (RV-06 .. RV-09) -/

/-- RV-06. The frozen `calldataOf` (LoweringV2/Statements.lean:335-340) repacks the proof and then
    calls `Lowering.encodeCalldata`, which repacks AGAIN. On the in-tree toy data the frozen
    composition fails while `repackThenEncode` (the intended one, Calldata.lean:257) succeeds. -/
def frozenCompositionIsOk : Bool :=
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  match Midfall.Lowering.repackProof (p := 17) CdKats.katPlan CdKats.toyCodec CdKats.katCompressed with
  | .ok π' => (Midfall.Lowering.encodeCalldata (p := 17) 1 CdKats.katPlan CdKats.toyCodec π'
      #[(5 : Midfall.Fr 17)]).isOk
  | .error _ => false

def intendedCompositionIsOk : Bool :=
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  (Midfall.Lowering.repackThenEncode (p := 17) 1 CdKats.katPlan CdKats.toyCodec CdKats.katCompressed
    #[(5 : Midfall.Fr 17)]).isOk

#guard frozenCompositionIsOk == false
#guard intendedCompositionIsOk

/-- RV-07. `calldatasize` is the calldata length modulo 2^256 (vendor EVMExec.lean:792), while
    `decodeCalldata` compares sizes in `Nat` (Lowering/Calldata.lean:341). Padding an accepted
    calldata with 2^256 bytes leaves every modelled run unchanged and makes the decoder fail. -/
example (S : Nat) : BitVec.ofNat 256 (S + 2^256) = BitVec.ofNat 256 S := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]

/- RV-08. The frozen clause pair `Valid.circuitMeta` / `Valid.layout`: clause 1 forces the plan
    meta to be the raw `ConstraintSystemMeta.new`, whose `numPointSets` is 0, and clause 2 builds the
    layout from that count. The derived proof length is 4224; the deployed contract's is 4320. -/
#guard deciding_layout_derivedProofLen == 4224
#guard deciding_layout_planProofLen == 4320

/-! ## 6. The program at the deployment IS the generator's output (RV-12 CLOSED by M2; RV-13 closed by ST.3) -/

/- Statements per slice, in include order. `quotientLin` is FOUR statements since OBJ.2: the two
    `quotient_numerator` includes in front of the linearization scope. `pcs` is ONE block scope
    carrying the eight-block partition (G1.4b). -/
#guard ([Partial.vkLoading, .transcriptParser, .lagrange, .quotientLin, .pcs, .finalPairing,
    .traceReturn].map fun q => (sliceOf poseidonPv poseidonM q).length) == [1, 44, 3, 4, 1, 2, 3]

/- Function definitions: 15 at the top level of the emitted AST (8 AssemblyHelpers + 5
    AccumulatorHelpers, G1.1, plus the 2 the slices contribute), and 15 function keywords in the
    generator's text - the two quotient helpers are flat statements of the `.quotientLin` slice,
    which is exactly what ST.3's scope had to absorb. -/
#guard ((mainAsmRaw poseidonPv poseidonM).filter fun s =>
    match s with | YulSemantics.Stmt.funDef .. => true | _ => false).length == 15
#guard ((mainAssemblyTokens poseidonM).filter (· == "function")).length == 15

/- So the token-agreement clause `Valid.codegen` is TRUE at the deployment: RV-12 closed. -/
#guard codegenAgrees poseidonPv poseidonM == true

/- RV-13, the reason the splice and the scope were ONE re-hash: the generator's text defines
    `q_program_fail` and `q_pow5` AFTER `let success`, i.e. inside the slice region, so a scope that
    hoists only the helpers is the wrong scope. `Render.scope` now hoists helpers then slices. -/
#guard (let t := mainAssemblyTokens poseidonM
        t.idxOf "success" < t.idxOf "q_program_fail" && t.idxOf "success" < t.idxOf "q_pow5")

/-! ## 7. What is proved, on clean axioms (positive evidence) -/

/-- info: 'Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound

/-- info: 'Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress

/-- info: 'Midfall.LoweringV2.entryFrame_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Midfall.LoweringV2.entryFrame_inhabited

/-- info: 'Midfall.Statements.verifyNative_iff_msgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Midfall.Statements.verifyNative_iff_msgs

/-- info: 'Midfall.Lowering.LegacyVacuity.not_LoweringCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Midfall.Lowering.LegacyVacuity.not_LoweringCorrect

end Midfall.ReviewV3

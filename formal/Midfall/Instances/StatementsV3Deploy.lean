/-
  StatementsV3Deploy (SCRATCH - design area "statements", PLAN-V3)

  THE V3 SURFACE EVALUATED AT THE DEPLOYMENT DATA (`Midfall.Instances`). In the tree this content
  belongs in `Midfall/Instances/` (D-P17); it is a separate file here for the same reason.
  Imports the scratch module `StatementsV3` (compiled to an olean in the scratch directory).

  Every measurement below is a `*_ok : Bool` gate comparing the WHOLE measured value to the literal
  ST.1 printed (ST.1b); see the note at section (b) for why the print itself cannot be annotated.
-/
import Midfall.LoweringV3.Statements
import Midfall.Instances.PoseidonValid
import Midfall.Instances.CurveSurface
import Midfall.Generator.Vk
set_option autoImplicit false

namespace Midfall.LoweringV3.Deploy

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid
open Midfall.LoweringV2 Midfall.LoweringV3

/-! ## (b) circuitMeta / layout: the frozen pair and the repaired pair, at two plans -/

-- Where the names live.
#check @Midfall.Instances.PoseidonInputs.poseidonPlanV2
#check @Midfall.Generator.metaDataForStableStaticLayoutInputs
#check @Midfall.Generator.numPointSets
#check @Midfall.Generator.ConstraintSystemMeta.setNumPointSets

/-- Today's plan: `meta_` is the RAW `ConstraintSystemMeta.new` output (numPointSets = 0). -/
def planToday : LoweringPlan Unit Unit := poseidonPlanV2

/-- The faithful plan: the same record with the meta post-processed as `vk.rs:519` does. -/
def planFaithful : LoweringPlan Unit Unit :=
  { poseidonPlanV2 with meta_ := poseidonPlanV2.meta_.setNumPointSets 3 }

def derivedProofLen (plan : LoweringPlan Unit Unit) : Nat :=
  match ProofCalldataLayout.fromProtocol plan.meta_.protocol abiVerifyProofProofCptr
      plan.meta_.numEvals plan.meta_.numPointSets with
  | .ok l => l.proofLen | .error _ => 0

-- (frozen clause 1, frozen/unchanged clause 2, V3 clause 1, derived proofLen, plan proofLen)
-- HOW THESE MEASUREMENTS ARE GATED (ST.1b). A tuple or a list print cannot carry an expectation:
-- scripts/kat_gate.py:40 reads one as [^\s,]+, so a value containing a space or a comma is
-- inexpressible. The tree already has the answer (OBJ.1's mainRtLine_ok and guardRtLine_ok, OBJ.5's
-- ObjectFingerprint.lean, and ST.1's own calldataOfV3_witness_ok at LoweringV3/Statements.lean:168):
-- bind the measurement VERBATIM, then gate a Bool that compares the WHOLE measured value to the
-- literal ST.1 printed. Nothing is projected away, so the falsifiers keep their teeth -
-- faithfulTuple_detectsPerturbation_ok below is that claim, pinned as a gate of its own.
/-- The (b) measurement as a function of the plan, so a falsifier can mutate the plan and re-measure
    through the identical expression. -/
def planTupleB (label : String) (plan : LoweringPlan Unit Unit) :=
  (label, frozenCircuitMetaB poseidonVkExec.cs 1 plan, planLayoutB plan,
    planMetaB poseidonVkExec.cs 1 plan, derivedProofLen plan, plan.proofLayout.proofLen)

/-- Today's plan: frozen clause 1 holds, the layout clause and the V3 clause do not, and the length the
    layout would derive (4224) is not the deployed one (4320). -/
def todayTuple_ok : Bool :=
  planTupleB "today" planToday == ("today", true, false, false, 4224, 4320)
#eval todayTuple_ok -- expect true

/-- The faithful plan is the mirror image: frozen clause 1 fails, the layout and V3 clauses hold, and
    the derived length equals the deployed 4320. -/
def faithfulTuple_ok : Bool :=
  planTupleB "faithful" planFaithful == ("faithful", false, true, true, 4320, 4320)
#eval faithfulTuple_ok -- expect true

/-- THE TEETH OF THE TWO GATES ABOVE, pinned. setNumPointSets 2 is neither today's 0 nor the
    generator's 3: the layout clause and the V3 clause both go false and the derived length drops to
    4288, so faithfulTuple_ok moves with the point-set count and not with anything that survives it. -/
def faithfulTuple_detectsPerturbation_ok : Bool :=
  planTupleB "faithful" { poseidonPlanV2 with meta_ := poseidonPlanV2.meta_.setNumPointSets 2 } ==
    ("faithful", false, false, false, 4288, 4320)
#eval faithfulTuple_detectsPerturbation_ok -- expect true

/-- The Rust derivation itself, `vk.rs:525-547` through the port, with the memory-layout callee
    instantiated at the PORTED `VerifierMemoryLayout.new`. The three quotient callbacks are not
    reached by `metaDataForStableStaticLayout`. -/
def layoutEnv : VkBuildEnv Unit :=
  { newVerifierMemoryLayout := VerifierMemoryLayout.new
    compactQuotientProgramFor := fun _ _ => .error (Fault.panic "unused")
    quotientProgramPlan := fun _ _ => .error (Fault.panic "unused")
    buildQuotientProgramItems := fun _ => .error (Fault.panic "unused") }

def rawMeta : ConstraintSystemMeta :=
  match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
  | .ok m => m | .error _ => constraintSystemMetaDefault

def buildInputs : VerifierBuildInputs Yul.blsR G₁z Unit :=
  { params := { gLagrange := [], g2 := (), sG2 := () }
    vk := poseidonVkExec, numInstances := 1, numCommittedInstances := 1
    accEncoding := none, meta_ := rawMeta }

-- (vkMptr derived, vkMptr of the plan, numPointSets, numEvals, numDummyEvals,
--  derived meta == faithful plan meta, derived meta == today's plan meta)
/-- The Rust derivation itself: vkMptr 10496 = 0x2900 equal to the plan's own, numPointSets 3,
    numEvals 48, 0 dummy evals, and a meta equal to the faithful plan's and NOT to today's. -/
def rustDerivationB : Nat × Nat × Nat × Nat × Nat × Bool × Bool :=
  match metaDataForStableStaticLayoutInputs Features.solidity layoutEnv buildInputs poseidonPlanV2.vk with
  | .ok (vkMptr, m, _, _) =>
      (ptrAddr vkMptr, ptrAddr poseidonPlanV2.vkMptr, m.numPointSets, m.numEvals, m.numDummyEvals,
        m == planFaithful.meta_, m == planToday.meta_)
  | .error _ => (0, 0, 0, 0, 0, false, false)

def rustDerivation_ok : Bool := rustDerivationB == (10496, 10496, 3, 48, 0, true, false)
#eval rustDerivation_ok -- expect true

-- the ten layout bases `Data.new` reads: the Rust-faithful layout against the plan's own layout
/-- All ten base pointers Data.new reads (Encoding.lean:626-639) agree between the Rust-faithful
    layout and the plan's own layout at the deployment - the conjunct 2 gap the memo records as a
    deployment fact and not a theorem. -/
def layoutBasesB : List Bool :=
  match metaDataForStableStaticLayoutInputs Features.solidity layoutEnv buildInputs poseidonPlanV2.vk with
  | .ok (_, _, _, mem) =>
      let pm := poseidonPlanV2.memory
      [ptrAddr mem.vkMptr == ptrAddr pm.vkMptr, ptrAddr mem.challengeMptr == ptrAddr pm.challengeMptr,
       ptrAddr mem.thetaMptr == ptrAddr pm.thetaMptr,
       ptrAddr mem.reversedEvalsMptr == ptrAddr pm.reversedEvalsMptr,
       ptrAddr mem.commsMptrBase == ptrAddr pm.commsMptrBase,
       ptrAddr mem.lookupMCommsMptrBase == ptrAddr pm.lookupMCommsMptrBase,
       ptrAddr mem.permZCommsMptrBase == ptrAddr pm.permZCommsMptrBase,
       ptrAddr mem.lookupHelperCommsMptrBase == ptrAddr pm.lookupHelperCommsMptrBase,
       ptrAddr mem.lookupZCommsMptrBase == ptrAddr pm.lookupZCommsMptrBase,
       ptrAddr mem.trashcanCommsMptrBase == ptrAddr pm.trashcanCommsMptrBase]
  | .error _ => []

def layoutBasesAgree_ok : Bool :=
  layoutBasesB == [true, true, true, true, true, true, true, true, true, true]
#eval layoutBasesAgree_ok -- expect true

-- the `Data` conjunct of `PlanMeta`: `setNumDummyEvals 0` is the identity on the raw meta, and
-- `Data.new` of it on the plan's own payload and memory is `.ok` - `poseidonPlanV2.data` is by
-- definition that value (`DeployedProfile.lean:216 poseidonData`)
/-- The Data conjunct of PlanMeta at the deployment: setNumDummyEvals 0 is the identity on the raw
    meta, Data.new of it returns .ok with field counts 19/8/8, and those are the plan's own counts. -/
def dataConjunct_ok : Bool :=
  (rawMeta.setNumDummyEvals 0 == rawMeta,
    (match Data.new (rawMeta.setNumDummyEvals 0) poseidonPlanV2.vk poseidonPlanV2.memory with
     | .ok d => (true, d.fixedComms.length, d.permutationComms.length, d.adviceComms.length)
     | .error _ => (false, 0, 0, 0)),
    (poseidonPlanV2.data.fixedComms.length, poseidonPlanV2.data.permutationComms.length,
      poseidonPlanV2.data.adviceComms.length)) ==
    (true, (true, 19, 8, 8), (19, 8, 8))
#eval dataConjunct_ok -- expect true

/-! ## (c) PayloadAgrees at the deployment -/

theorem poseidonE_delta : poseidonRender.E.delta = 2 := rfl

-- the eight codec-free fields, in the order of `payloadScalarsB`:
-- numInstances, k, nInv, omega, omegaInv, omegaInvToL, accWords, delta
/-- The eight codec-free PayloadAgrees fields at today's render, in the order of payloadScalarsB:
    numInstances, k, nInv, omega, omegaInv, omegaInvToL, accWords all hold; delta does not. -/
def payloadScalarsPlaceholder_ok : Bool :=
  payloadScalarsB (p := Yul.blsR) poseidonPv 1 poseidonVkExec.domain.k
    poseidonVkExec.domain.omega poseidonVkExec.domain.omegaInv poseidonPlanV2.meta_.rotationLast
    poseidonConfig.accumulator (2 : Fr Yul.blsR) poseidonInputs.frDelta ==
    [true, true, true, true, true, true, true, false]
#eval payloadScalarsPlaceholder_ok -- expect true

-- the same with the field's real DELTA in place of the placeholder 2
/-- The same eight with the field's real DELTA in place of the placeholder 2: all eight hold, so the
    single refuting field of poseidon_payloadAgrees_not is delta and nothing else among the scalars. -/
def payloadScalarsRealDelta_ok : Bool :=
  payloadScalarsB (p := Yul.blsR) poseidonPv 1 poseidonVkExec.domain.k
    poseidonVkExec.domain.omega poseidonVkExec.domain.omegaInv poseidonPlanV2.meta_.rotationLast
    poseidonConfig.accumulator
    ((Inline.natOfLiteral poseidonInputs.frDelta : ℕ) : Fr Yul.blsR) poseidonInputs.frDelta ==
    [true, true, true, true, true, true, true, true]
#eval payloadScalarsRealDelta_ok -- expect true

-- the literal IS Fr::DELTA = 7^(2^32) mod r (multiplicative generator 7, two-adicity 32)
/-- The literal IS Fr::DELTA = 7^(2^32) mod r (multiplicative generator 7, two-adicity 32), and it
    is below r: both halves of the memo's (true, true). -/
def frDeltaIsGeneratorPow_ok : Bool :=
  (Inline.natOfLiteral poseidonInputs.frDelta == modPow 7 (2 ^ 32) Yul.blsR,
    decide (Inline.natOfLiteral poseidonInputs.frDelta < Yul.blsR)) == (true, true)
#eval frDeltaIsGeneratorPow_ok -- expect true

/-- The `delta` field is FALSE at today's render. Concrete deployment fact. -/
theorem poseidon_delta_not :
    ¬ (poseidonRender.E.delta.val = Inline.natOfLiteral poseidonRender.inputs.frDelta) := by
  show ¬ ((2 : Fr Yul.blsR).val = Inline.natOfLiteral poseidonInputs.frDelta)
  native_decide

/-- So `PayloadAgrees poseidonRender` is refuted, by its `delta` field alone. -/
theorem poseidon_payloadAgrees_not : ¬ PayloadAgrees poseidonRender :=
  fun h => poseidon_delta_not h.delta

-- commitments: (payload fixed count, Lean fixed count, payload perm count, Lean perm count)
/-- The commitment counts agree between the payload and the Lean key: 19 fixed and 8 permutation on
    both sides - the counts the two commitment fields of PayloadAgrees would have to match once a
    codec makes those two fields expressible. -/
def commitmentCounts_ok : Bool :=
  (poseidonPv.vk.fixedComms.length, poseidonVkExec.fixedCommitments.size,
    poseidonPv.vk.permutationComms.length, poseidonVkExec.permutation.commitments.size) ==
    (19, 19, 8, 8)
#eval commitmentCounts_ok -- expect true

-- which payload fixed commitments are the identity image (128 zero bytes): the Lean key has ALL
-- nineteen at the identity, the payload only these
/-- Which payload fixed commitments are the identity image (128 zero bytes): indices
    [8, 10, 11, 12, 14, 16], six of nineteen. The review lists five; index 14 is also all-zero in
    Halo2VerifyingKey.sol:189-192. The Lean key has ALL nineteen at the identity. -/
def identityFixedCommIndices_ok : Bool :=
  (poseidonPv.vk.fixedComms.zipIdx.filter
    (fun (w, _) => g1WordsBytes w == natToBytesBE 0 128)).map (·.2) ==
    [8, 10, 11, 12, 14, 16]
#eval identityFixedCommIndices_ok -- expect true
/-- ... and NONE of the eight payload permutation commitments is the identity image: the count is 0. -/
def identityPermCommCount_ok : Bool :=
  ((poseidonPv.vk.permutationComms.filter
    (fun w => g1WordsBytes w == natToBytesBE 0 128)).length) == 0
#eval identityPermCommCount_ok -- expect true

-- the three base slots hold non-zero images of the right widths (content needs the codec)
/-- The three base slots hold images of the right widths - 128 bytes for the G1 word, 256 for each G2
    word - and the G2 base and the negated sG2 generator are DIFFERENT words, so the two slots are not
    a single placeholder repeated. Content needs the codec; widths and distinctness do not. -/
def baseSlotWidths_ok : Bool :=
  ((vkG1Words poseidonPv vkG1BaseSlot).size, (vkG2Words poseidonPv vkG2BaseSlot).size,
    (vkG2Words poseidonPv vkNegSG2BaseSlot).size,
    vkG2Words poseidonPv vkG2BaseSlot == vkG2Words poseidonPv vkNegSG2BaseSlot) ==
    (128, 256, 256, false)
#eval baseSlotWidths_ok -- expect true

/-! ## (j) WellFormedV3 at the deployment -/

-- (VK sigma commitments, permutation columns [V3 clause], divCeil columns (csDegree-2) [frozen clause])
/-- WellFormed.permutationCommitmentsMatch at the deployment: (8, 8, 3) = sigma commitments in the VK,
    permutation columns (the V3 clause, which agrees), and divCeil columns (csDegree - 2) (the frozen
    clause's right-hand side, which does not). This is the field the supported lemma refutes. -/
def wellFormedPermCounts_ok : Bool :=
  (poseidonVkExec.permutation.commitments.size, poseidonVkExec.cs.permutation.columns.size,
    divCeil poseidonVkExec.cs.permutation.columns.size (poseidonVkExec.csDegree - 2)) == (8, 8, 3)
#eval wellFormedPermCounts_ok -- expect true

/-! ## (d), (i), (e) the three new decidable clauses at the deployment AST -/

-- noShadow
#eval noShadowCore poseidonPv poseidonM -- expect true

-- exitDiscipline: the tail is found, and the scan passes (fuel 20000 as for noWriters)
/-- ExitDiscipline at the deployment AST: the return tail is found, the scan passes at fuel 20000 and
    FAILS at fuel 200 - so the triple is (true, true, false), which is what the memo
    (V3-evidence/design/statements.md section (i), repeated at section 4) records.

    RE-PINNED BY ST.1c ONTO THE POST-M2 BASELINE. On the pre-M2 tree this gate read (true, true, true):
    WP-G1/OBJ.2 (cards G1.1, G1.2, M2) emit the three regions `mainAsmRaw` used to omit - the five
    accumulator-codec definitions, `q_program_fail`/`q_pow5`, and the 6,384-token quotient numerator -
    so the scanned block grew and the fuel-bounded scan now needs more fuel. Measured at this baseline:
    the scan fails at fuel 298 and passes at 299, so 200 is below the threshold and 20000 above it.
    ST.1b's finding was correct against the tree it measured; the memo line needs NO correction here -
    the tree moved to the memo, not the other way round. The statement `ExitDiscipline` is unchanged:
    it is `\exists n, exitDisciplineFuel n b = true`, and 20000 still witnesses it. -/
def exitDisciplineAtDeploy_ok : Bool :=
  ((returnTail? (asmOf poseidonPv poseidonM 0 0)).isSome,
    exitDisciplineFuel 20000 (asmOf poseidonPv poseidonM 0 0),
    exitDisciplineFuel 200 (asmOf poseidonPv poseidonM 0 0)) == (true, true, false)
#eval exitDisciplineAtDeploy_ok -- expect true

-- the same discipline read off the GENERATOR'S TEXT (the text-side cross-check of the AST gate
-- above: since WP-G1/OBJ.2 the AST carries these regions too, so the two readings are of one block):
-- token counts of (return, stop, selfdestruct, invalid, gas, call, delegatecall, callcode, create,
-- create2, staticcall) in the main assembly block
/-- The same discipline read off the GENERATOR'S TEXT (a cross-check of the AST gate above: since
    WP-G1/OBJ.2 the AST emits these regions too, so both readings are of one block):
    token counts of return, stop, selfdestruct, invalid, gas, call, delegatecall, callcode, create,
    create2, staticcall in the main block = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]. One return (the tail),
    no stop / selfdestruct / invalid outside it, no gas() at all (so the partial oracle is never
    reached), no call / delegatecall / callcode / create / create2, and nine staticcalls - all of them
    to 0x05, 0x0b, 0x0c or 0x0f, which the honest relation answers. -/
def mainBlockTokenCounts_ok : Bool :=
  (["return", "stop", "selfdestruct", "invalid", "gas", "call", "delegatecall", "callcode",
    "create", "create2", "staticcall"].map fun t => (mainAssemblyTokens poseidonM).count t) ==
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]
#eval mainBlockTokenCounts_ok -- expect true

-- cdBound: the expected calldata length
/-- cdBound: the expected calldata length is 4484 at the deployment, and it is below 2^256 - the bound
    that makes EntryFrameV3'.cdSize do work at this render. -/
def cdBound_ok : Bool :=
  (poseidonPlanV2.proofLayout.proofEnd + 32 + 32 * poseidonConfig.numInstances,
    decide (poseidonPlanV2.proofLayout.proofEnd + 32 + 32 * poseidonConfig.numInstances < 2 ^ 256)) ==
    (4484, true)
#eval cdBound_ok -- expect true

-- the g1_identity pin of the EntryFrameV3' option
/-- The g1_identity pin of the EntryFrameV3' option: TRANSCRIPT_MPTR is 4096 and the g1 identity slot
    sits at 21760, so 4096 <= 21760 holds at the deployment - the premise g1IdentityAbove needs. -/
def transcriptMptrPin_ok : Bool :=
  ((constTableOf poseidonM).lookup "TRANSCRIPT_MPTR",
    ptrAddr poseidonPv.memory.g1IdentityMptr) == (some 4096, 21760)
#eval transcriptMptrPin_ok -- expect true

/-! ## (g) the codec laws at the deployment codec -/

-- The tree's own proof that the placeholder codec satisfies all seven FROZEN laws.
#check (Midfall.Instances.CurveSurface.g1CodecZ_laws : G1CodecLaws g1CodecZ)

/-- FALSIFIER: it does not satisfy the V3 headline laws. PROVED. -/
theorem g1CodecZ_not_headlineLaws : ¬ G1CodecHeadlineLaws g1CodecZ := by
  intro h
  have h1 := h.compressedEncoderFirst 1
  have h2 : g1CodecZ.ofCompressed? (g1CodecZ.toCompressed 1) = none := rfl
  rw [h2] at h1
  cases h1

/-- So the repaired gate is RED at today's render, for every product: the gate cannot be met by a
    codec that decodes nothing. PROVED. -/
theorem poseidon_notInhabitedV3 (product : PairingProduct) :
    ¬ HypothesesInhabitedV3 poseidonRender product := by
  rintro ⟨_, _, _, _, _, _, _, _, hcodec, _⟩
  exact g1CodecZ_not_headlineLaws hcodec

/-- An injective 48-byte image of `G₁z` exists: the carrier has `blsR < 256^48` elements. -/
theorem exists_injective_comp :
    ∃ comp : G₁z → Bytes, Function.Injective comp ∧ ∀ Q, (comp Q).size = g1CompressedWidth := by
  classical
  have hcard : Nat.card G₁z = Yul.blsR := PrimeOrderWith.hCard
  have hpos : 0 < Nat.card G₁z := by rw [hcard]; decide
  have hfin : Finite G₁z := Nat.finite_of_card_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  obtain ⟨e⟩ : Nonempty (G₁z ≃ Fin (Nat.card G₁z)) := ⟨Finite.equivFin G₁z⟩
  refine ⟨fun Q => bytesNatBE (e Q).val 48, ?_, fun Q => bytesNatBE_size _ _⟩
  intro Q Q' h
  have h' := congrArg bytesToNatBE h
  simp only [bytesToNatBE_bytesNatBE] at h'
  have hle : Nat.card G₁z ≤ 256 ^ 48 := by rw [hcard]; decide
  have hlt : ∀ X : G₁z, (e X).val < 256 ^ 48 := fun X => lt_of_lt_of_le (e X).isLt hle
  rw [Nat.mod_eq_of_lt (hlt Q), Nat.mod_eq_of_lt (hlt Q')] at h'
  exact e.injective (Fin.ext h')

/-- WITNESS (joint satisfiability at the deployment carrier). A codec on `G₁z` with the SAME
    EIP half as `g1CodecZ` - the half `Eip2537.Holds` is exhibited for - satisfies all eight V3
    laws. PROVED, with no curve arithmetic. Its compressed half is an abstract injection, NOT the
    ZCash format: enough for `LoweringEquivalenceV3`, not for `EndToEndV3`'s link to Rust bytes. -/
theorem lawsV3_satisfiable_at_G1z :
    ∃ c : G1Codec G₁z, c.toEip = g1CodecZ.toEip ∧ c.ofEip? = g1CodecZ.ofEip? ∧ G1CodecLawsV3 c := by
  obtain ⟨comp, hinj, hw⟩ := exists_injective_comp
  exact ⟨withCompressed g1CodecZ comp, rfl, rfl, withCompressed_lawsV3 g1CodecZ Midfall.Instances.CurveSurface.g1CodecZ_laws comp hinj hw⟩

#print axioms lawsV3_satisfiable_at_G1z
#print axioms poseidon_notInhabitedV3
#print axioms poseidon_payloadAgrees_not

end Midfall.LoweringV3.Deploy

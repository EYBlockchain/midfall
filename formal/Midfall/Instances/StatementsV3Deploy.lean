/-
  StatementsV3Deploy (SCRATCH - design area "statements", PLAN-V3)

  THE V3 SURFACE EVALUATED AT THE DEPLOYMENT DATA (`Midfall.Instances`). In the tree this content
  belongs in `Midfall/Instances/` (D-P17); it is a separate file here for the same reason.
  Imports the scratch module `StatementsV3` (compiled to an olean in the scratch directory).
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
#check @Midfall.Generator.metaDataForStableStaticLayout
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
#eval ("today", frozenCircuitMetaB poseidonVkExec.cs 1 planToday, planLayoutB planToday,
  planMetaB poseidonVkExec.cs 1 planToday, derivedProofLen planToday, planToday.proofLayout.proofLen)
#eval ("faithful", frozenCircuitMetaB poseidonVkExec.cs 1 planFaithful, planLayoutB planFaithful,
  planMetaB poseidonVkExec.cs 1 planFaithful, derivedProofLen planFaithful,
  planFaithful.proofLayout.proofLen)

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
#eval (match metaDataForStableStaticLayout Features.solidity layoutEnv buildInputs poseidonPlanV2.vk with
  | .ok (vkMptr, m, _, _) =>
      (ptrAddr vkMptr, ptrAddr poseidonPlanV2.vkMptr, m.numPointSets, m.numEvals, m.numDummyEvals,
        m == planFaithful.meta_, m == planToday.meta_)
  | .error _ => (0, 0, 0, 0, 0, false, false))

-- the ten layout bases `Data.new` reads: the Rust-faithful layout against the plan's own layout
#eval (match metaDataForStableStaticLayout Features.solidity layoutEnv buildInputs poseidonPlanV2.vk with
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
  | .error _ => [])

-- the `Data` conjunct of `PlanMeta`: `setNumDummyEvals 0` is the identity on the raw meta, and
-- `Data.new` of it on the plan's own payload and memory is `.ok` - `poseidonPlanV2.data` is by
-- definition that value (`DeployedProfile.lean:216 poseidonData`)
#eval (rawMeta.setNumDummyEvals 0 == rawMeta,
  (match Data.new (rawMeta.setNumDummyEvals 0) poseidonPlanV2.vk poseidonPlanV2.memory with
   | .ok d => (true, d.fixedComms.length, d.permutationComms.length, d.adviceComms.length)
   | .error _ => (false, 0, 0, 0)),
  (poseidonPlanV2.data.fixedComms.length, poseidonPlanV2.data.permutationComms.length,
    poseidonPlanV2.data.adviceComms.length))

/-! ## (c) PayloadAgrees at the deployment -/

theorem poseidonE_delta : poseidonRender.E.delta = 2 := rfl

-- the eight codec-free fields, in the order of `payloadScalarsB`:
-- numInstances, k, nInv, omega, omegaInv, omegaInvToL, accWords, delta
#eval payloadScalarsB (p := Yul.blsR) poseidonPv 1 poseidonVkExec.domain.k
  poseidonVkExec.domain.omega poseidonVkExec.domain.omegaInv poseidonPlanV2.meta_.rotationLast
  poseidonConfig.accumulator (2 : Fr Yul.blsR) poseidonInputs.frDelta

-- the same with the field's real DELTA in place of the placeholder 2
#eval payloadScalarsB (p := Yul.blsR) poseidonPv 1 poseidonVkExec.domain.k
  poseidonVkExec.domain.omega poseidonVkExec.domain.omegaInv poseidonPlanV2.meta_.rotationLast
  poseidonConfig.accumulator
  ((Inline.natOfLiteral poseidonInputs.frDelta : ℕ) : Fr Yul.blsR) poseidonInputs.frDelta

-- the literal IS Fr::DELTA = 7^(2^32) mod r (multiplicative generator 7, two-adicity 32)
#eval (Inline.natOfLiteral poseidonInputs.frDelta == modPow 7 (2 ^ 32) Yul.blsR,
  decide (Inline.natOfLiteral poseidonInputs.frDelta < Yul.blsR))

/-- The `delta` field is FALSE at today's render. Concrete deployment fact. -/
theorem poseidon_delta_not :
    ¬ (poseidonRender.E.delta.val = Inline.natOfLiteral poseidonRender.inputs.frDelta) := by
  show ¬ ((2 : Fr Yul.blsR).val = Inline.natOfLiteral poseidonInputs.frDelta)
  native_decide

/-- So `PayloadAgrees poseidonRender` is refuted, by its `delta` field alone. -/
theorem poseidon_payloadAgrees_not : ¬ PayloadAgrees poseidonRender :=
  fun h => poseidon_delta_not h.delta

-- commitments: (payload fixed count, Lean fixed count, payload perm count, Lean perm count)
#eval (poseidonPv.vk.fixedComms.length, poseidonVkExec.fixedCommitments.size,
  poseidonPv.vk.permutationComms.length, poseidonVkExec.permutation.commitments.size)

-- which payload fixed commitments are the identity image (128 zero bytes): the Lean key has ALL
-- nineteen at the identity, the payload only these
#eval (poseidonPv.vk.fixedComms.zipIdx.filter
  (fun (w, _) => g1WordsBytes w == natToBytesBE 0 128)).map (·.2)
#eval ((poseidonPv.vk.permutationComms.filter
  (fun w => g1WordsBytes w == natToBytesBE 0 128)).length)

-- the three base slots hold non-zero images of the right widths (content needs the codec)
#eval ((vkG1Words poseidonPv vkG1BaseSlot).size, (vkG2Words poseidonPv vkG2BaseSlot).size,
  (vkG2Words poseidonPv vkNegSG2BaseSlot).size,
  vkG2Words poseidonPv vkG2BaseSlot == vkG2Words poseidonPv vkNegSG2BaseSlot)

/-! ## (j) WellFormedV3 at the deployment -/

-- (VK sigma commitments, permutation columns [V3 clause], divCeil columns (csDegree-2) [frozen clause])
#eval (poseidonVkExec.permutation.commitments.size, poseidonVkExec.cs.permutation.columns.size,
  divCeil poseidonVkExec.cs.permutation.columns.size (poseidonVkExec.csDegree - 2))

/-! ## (d), (i), (e) the three new decidable clauses at the deployment AST -/

-- noShadow
#eval noShadowCore poseidonPv poseidonM

-- exitDiscipline: the tail is found, and the scan passes (fuel 20000 as for noWriters)
#eval ((returnTail? (asmOf poseidonPv poseidonM 0 0)).isSome,
  exitDisciplineFuel 20000 (asmOf poseidonPv poseidonM 0 0),
  exitDisciplineFuel 200 (asmOf poseidonPv poseidonM 0 0))

-- the same discipline read off the GENERATOR'S TEXT (which has the regions the AST still lacks):
-- token counts of (return, stop, selfdestruct, invalid, gas, call, delegatecall, callcode, create,
-- create2, staticcall) in the main assembly block
#eval (["return", "stop", "selfdestruct", "invalid", "gas", "call", "delegatecall", "callcode",
  "create", "create2", "staticcall"].map fun t => (mainAssemblyTokens poseidonM).count t)

-- cdBound: the expected calldata length
#eval (poseidonPlanV2.proofLayout.proofEnd + 32 + 32 * poseidonConfig.numInstances,
  decide (poseidonPlanV2.proofLayout.proofEnd + 32 + 32 * poseidonConfig.numInstances < 2 ^ 256))

-- the g1_identity pin of the EntryFrameV3' option
#eval ((constTableOf poseidonM).lookup "TRANSCRIPT_MPTR", ptrAddr poseidonPv.memory.g1IdentityMptr)

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

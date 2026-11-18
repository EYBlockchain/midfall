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
import Midfall.Instances.GeneratedKats
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

-- the eight codec-free fields, in the order of `payloadScalarsB`:
-- numInstances, k, nInv, omega, omegaInv, omegaInvToL, accWords, delta
/-- OBJ.8 step 2 moved the render's DELTA off the placeholder 2 and onto the field constant, so
    the pin now reads against `poseidonDelta` - and it is still an `rfl`, which is the point: the
    render carries the constant and not a copy of it. -/
theorem poseidonE_delta : poseidonRender.E.delta = poseidonDelta := rfl

/-- The literal the render carries as `frDelta` IS Fr::DELTA = 7^(2^32) mod r (multiplicative
    generator 7, two-adicity 32), and it is below r: both halves of the memo's (true, true). -/
def frDeltaIsGeneratorPow_ok : Bool :=
  (Inline.natOfLiteral poseidonInputs.frDelta == modPow 7 (2 ^ 32) Yul.blsR,
    decide (Inline.natOfLiteral poseidonInputs.frDelta < Yul.blsR)) == (true, true)
#eval frDeltaIsGeneratorPow_ok -- expect true

/-- **THE REFUTATION THAT DIED (OBJ.8 step 2).** RECON.1 measured the opposite of this: that the
    render's DELTA was the placeholder 2 and NOT the literal the artifact's quotient blocks print,
    and named that as the reason `generated` fails at the fixture. Step 2 replaces the placeholder
    with the field constant, so the equation now HOLDS and the old `poseidon_delta_not` is retired
    with it. Under the single text this was never a `PayloadAgrees` field (RECON.1 step 3 drops
    `delta`); it is the `generated` clause that reads `E.delta`, and the two #check lines below are
    its witness and falsifier. -/
theorem poseidon_delta_is :
    poseidonRender.E.delta.val = Inline.natOfLiteral poseidonRender.inputs.frDelta := by
  show poseidonDelta.val = Inline.natOfLiteral poseidonInputs.frDelta
  native_decide

/-! ## (RECON.1) THE CLAUSE TABLE AT F1: one witness line and one falsifier line per clause of the
    single `ValidV3`. W12/W15: a clause with no falsifier is a clause that cannot fail.

    Read with the per-clause verdicts of `§V` of `Midfall/LoweringV3/Statements.lean`. The fixture
    render itself is `noncomputable` (its model is the typed-in artifact value), so every line below
    evaluates the clause at the COMPUTABLE fixture data - `poseidonPv`, `poseidonM`,
    `poseidonPlanV2`, `poseidonConfig`, `poseidonVkExec` - which are the render's own fields
    (`poseidonRender_plan_isD1`, `poseidonRender_vk_isD2`). -/

/-- The program clause's decidable bundle at F1: `programOkB`, and each conjunct that RECON.1 added or
    folded, all TRUE. One line, seven facts. -/
def recon1_programOkB_ok : Bool :=
  (Midfall.LoweringV3.programOkCore poseidonPv poseidonM poseidonConfig.numInstances
      poseidonVkExec,
    Midfall.LoweringV3.constsCoherent poseidonPv poseidonM,
    Midfall.LoweringV3.callsResolved (mainAsmRaw poseidonPv poseidonM),
    Midfall.LoweringV3.transcriptRegionOk poseidonPv poseidonConfig.numInstances,
    Midfall.LoweringV3.g1IdentityFloor poseidonPv,
    Midfall.LoweringV3.negLagrangesFloor poseidonPv,
    Midfall.LoweringV3.permCommMatchRepaired poseidonVkExec) ==
    (true, true, true, true, true, true, true)
#eval recon1_programOkB_ok -- expect true

/-- FALSIFIER of the `constsCoherent` conjunct: move the plan view's transcript base and the table no
    longer equals the data table (`Consts2.lean`'s `pvShifted`, ported). -/
def recon1_constsCoherent_falsifier_ok : Bool :=
  ! Midfall.LoweringV3.constsCoherent
      { poseidonPv with memory := { poseidonPv.memory with
          transcriptMptr := poseidonPv.memory.transcriptMptr + 32 } } poseidonM
#eval recon1_constsCoherent_falsifier_ok -- expect true

/-- FALSIFIER of PG-G1ID (addition 3): the default layout's `g1IdentityMptr` is 0
    (`Layout.lean:1732`), and 0x80 ≤ 0 is false - so the clause excludes a real shape, it does not
    merely describe the deployment. -/
def recon1_g1Identity_falsifier_ok : Bool :=
  ! Midfall.LoweringV3.g1IdentityFloor { poseidonPv with memory :=
      { poseidonPv.memory with g1IdentityMptr := ptrMemory (valueFromNat 0x40) } }
#eval recon1_g1Identity_falsifier_ok -- expect true

/-- FALSIFIER of PG-NEGLAG (addition 4): `numNegLagranges = 1` is what
    `EnvAgrees.negLagranges` allows when `blindingFactors` is an error
    (`blindingFactors.getD 0 + 1 = 1`), and the clause refuses it. -/
def recon1_negLagranges_falsifier_ok : Bool :=
  ! Midfall.LoweringV3.negLagrangesFloor { poseidonPv with numNegLagranges := 1 }
#eval recon1_negLagranges_falsifier_ok -- expect true

/-- FALSIFIER of `cdBound`: an instance count that pushes the expected calldata length past a word.
    The clause is the arithmetic that makes the contract's `calldatasize` test and
    `decodeCalldata`'s `Nat` test the same test, and it can fail. -/
def recon1_cdBound_falsifier_ok : Bool :=
  ! Midfall.LoweringV3.cdBoundB poseidonPv (2 ^ 256)
#eval recon1_cdBound_falsifier_ok -- expect true

/-- FALSIFIER of PG-TPBUF (addition 2), both halves: a walk window moved into the transcript region,
    and an absorb run longer than the region. -/
def recon1_tpbuf_falsifier_ok : Bool :=
  ! Midfall.LoweringV3.transcriptRegionOk { poseidonPv with memory :=
      { poseidonPv.memory with
          adviceCommsMptrBase := ptrMemory (valueFromNat poseidonPv.memory.transcriptMptr) } }
      poseidonConfig.numInstances &&
  ! Midfall.LoweringV3.transcriptRegionOk { poseidonPv with proofLayout :=
      { poseidonPv.proofLayout with evals :=
          { poseidonPv.proofLayout.evals with byteLen := 99999 } } }
      poseidonConfig.numInstances
#eval recon1_tpbuf_falsifier_ok -- expect true

/-- The PG-TPBUF numbers, printed: the transcript region is (4096, 4096) - start 0x1000, 128 words -
    and the longest absorb run at F1 is 1536 bytes, so the capacity half holds with room; the nine
    walk windows are all above it. -/
def recon1_tpbuf_numbers_ok : Bool :=
  (Midfall.LoweringV3.longestAbsorbRunOf poseidonPv poseidonConfig.numInstances,
    (poseidonPv.memory.map.region "transcript_buffer").map fun r => (r.start, r.len),
    (Midfall.LoweringV3.walkWindowsOf poseidonPv).all fun w => w.1 ≥ 0x1000 + 4096) ==
    (1536, some (4096, 4096), true)
#eval recon1_tpbuf_numbers_ok -- expect true

/-- **`hasMultiPointSet`: WITNESS at F1 and a falsifier of the test it runs.** The clause asks that
    SOME static point set has two points; at F1 the sets are [[0],[0,1],[0,-9]] (`SoundnessV3`'s
    measurement) so it holds. The falsifier is the predicate itself on the other shape - a plan whose
    sets are all singletons fails it, and the `.error` arm of the definition fails it too. A
    render-level mutation (a real `Data` with only singleton sets) is NOT landed here: it needs a
    second fixture plan, and this card is a statement card. -/
def recon1_multiPoint_ok : Bool :=
  (Midfall.LoweringV3.hasMultiPointSet poseidonPv,
    ([[0],[1]].any fun ps => decide (2 ≤ ps.length)),
    ([[0],[0,1]].any fun ps => decide (2 ≤ ps.length))) == (true, false, true)
#eval recon1_multiPoint_ok -- expect true

/-- WITNESS and FALSIFIER of the two program scans `programOkB` runs on the AST, as evaluations (the
    kernel cannot reduce `List.contains` on strings, so these are not `decide` proofs).
    `callsResolved`: a call to a declared function resolves; an undeclared call does not; a function
    named after a built-in does not (the definition's second conjunct - a `.call` node can never be a
    mis-spelled built-in). `noShadowProg`: a binder named after a contract constant is refused, as a
    `let` and as a function parameter; a plain binder passes (the B-5 hazard `inline_append` needs). -/
def recon1_scans_ok : Bool :=
  (Midfall.LoweringV3.callsResolved
      [Stmt.funDef "g" [] [] [], Stmt.exprStmt (Expr.call "g" [])],
    Midfall.LoweringV3.callsResolved [Stmt.exprStmt (Expr.call "g" [])],
    Midfall.LoweringV3.callsResolved
      [Stmt.funDef "add" [] [] [], Stmt.exprStmt (Expr.call "add" [])],
    Midfall.LoweringV3.noShadowProg [("FR_MODULUS", 5)]
      [Stmt.letDecl ["FR_MODULUS"] (some (Expr.lit (Literal.number 1)))],
    Midfall.LoweringV3.noShadowProg [("FR_MODULUS", 5)]
      [Stmt.funDef "ff" ["FR_MODULUS"] [] [Stmt.letDecl ["y"] (some (Expr.lit (Literal.number 1)))]],
    Midfall.LoweringV3.noShadowProg [("FR_MODULUS", 5)]
      [Stmt.letDecl ["r"] (some (Expr.lit (Literal.number 1)))]) ==
    (true, false, false, false, false, true)
#eval recon1_scans_ok -- expect true
/-- WITNESS of PG-GAS (addition 1) at F1: the emitted program passes the scan at fuel 20000. The
    token count of `gas` in the main block is 0 (`mainBlockTokenCounts_ok`), so F1 is the EASY case -
    the clause's teeth are for the external-evaluator render, and the scan-level witness and
    falsifier are `gasCallOk_witness` / `gasCallOk_refuses` in the staging module (a call's own
    `gas()` passes; a `gas()` as a value, as a second argument, or nested in an offset fails). -/
def recon1_gas_ok : Bool := Midfall.LoweringV3.gasScan 20000 (.b (asmOf poseidonPv poseidonM 0 0))
#eval recon1_gas_ok -- expect true

/-- FALSIFIER of `permCommMatchRepaired`: three sigma commitments against eight columns - the frozen
    clause's own number - is refused. -/
def recon1_permComm_falsifier_ok : Bool :=
  ! Midfall.LoweringV3.permCommMatchRepaired { poseidonVkExec with permutation :=
      { poseidonVkExec.permutation with
          commitments := poseidonVkExec.permutation.commitments.extract 0 3 } }
#eval recon1_permComm_falsifier_ok -- expect true

/- **`generated`: WITNESS and FALSIFIER, both OBJ.7's gates - AND OBJ.8'S MEASUREMENT.** Gate 4
    (`generateAll_textIsTheArtifactButForBuildId_ok`): with the fixture's real DELTA the generator's
    text IS the artifact but for BUILD_ID. Gate 9 (`generateAll_falsifierDeltaAndOmega_ok`): with
    `delta := 2` the generated quotient blocks are NOT the render's - and `delta := 2` USED to be
    what `poseidonRender.E.delta` carried, which is why RECON.1 could name gate 9 as this fixture's
    refutation of `generated`. **OBJ.8 step 2 set `poseidonE.delta` to the field constant
    (`poseidonDelta`), so gate 9 no longer refutes the clause at this render: the DELTA refutation
    DIED.** What refutes `generated` now is the PAYLOAD, measured sorry-free as
    `PoseidonValid.poseidonValid_generated_not`: `Render.generated` reads the generator's payload from
    `R.plan.vk`, this render's plan carries the parsed artifact payload, and `generateAll` refuses it
    at quotient.rs:202 (OBJ.7 gate 11). Step 3 - the render rebuilt from `generateAll` - is the row
    that closes it; it needs a frozen decision about where the payload lives, and it is recorded
    rather than forced. Gate 9 remains the card's falsifier of the GENERATOR (delta reaches the text);
    it is no longer a statement about this render. -/
#check @Midfall.Instances.GeneratedKats.generateAll_textIsTheArtifactButForBuildId_ok
#check @Midfall.Instances.GeneratedKats.generateAll_falsifierDeltaAndOmega_ok

/-- **`payload`, the seven decidable fields at F1** (`digest` measured separately below): all hold.
    The five codec-bearing fields (`g1Base`, `g2Base`, `negSG2`, `fixedComms`, `permutationComms`)
    compare payload bytes with `toEip` of group elements and `toEip` is noncomputable at the
    placeholder codec, so they are neither proved nor refuted here - which is why the 18-clause text's
    refutation of `PayloadAgrees poseidonRender` (carried by the `delta` field alone) is GONE with that
    field, and the F1 refutation of the single text now sits in `generated`. -/
def recon1_payload_scalars_ok : Bool :=
  payloadScalarsB (p := Yul.blsR) poseidonPv 1 poseidonVkExec.domain.k
    poseidonVkExec.domain.omega poseidonVkExec.domain.omegaInv poseidonPlanV2.meta_.rotationLast
    poseidonConfig.accumulator == [true, true, true, true, true, true, true]
#eval recon1_payload_scalars_ok -- expect true

/-- FALSIFIER of `payload` that needs no codec: flip the payload's OMEGA word. The generator still
    accepts the perturbed payload (that is OBJ.7's NON-falsifier, gate 9's second half), so this is
    exactly the hole `PayloadAgrees` exists to close - and it closes it. -/
def recon1_payload_flipOmega_ok : Bool :=
  let bump (i : Nat) (v : Halo2VerifyingKey) : Halo2VerifyingKey :=
    { v with constants := v.constants.zipIdx.map fun (c, j) =>
        if j == i then (c.1, c.2 + 1) else c }
  payloadScalarsB (p := Yul.blsR) { poseidonPv with vk := bump 4 poseidonPv.vk } 1
    poseidonVkExec.domain.k poseidonVkExec.domain.omega poseidonVkExec.domain.omegaInv
    poseidonPlanV2.meta_.rotationLast poseidonConfig.accumulator ==
    [true, true, true, false, true, true, true]
#eval recon1_payload_flipOmega_ok -- expect true

/-- WITNESS of `payload.digest` at F1: header word 0 is the exec key's transcript representation. -/
def recon1_payload_digest_ok : Bool :=
  Midfall.LoweringV3.payloadWord poseidonPv vkHeaderTemplateSlotsDefault.vkDigest ==
    frWord poseidonVkExec.transcriptRepr
#eval recon1_payload_digest_ok -- expect true

/-- FALSIFIER of `payload.digest`: bump word 0. -/
def recon1_payload_digest_falsifier_ok : Bool :=
  let v := poseidonPv.vk
  Midfall.LoweringV3.payloadWord { poseidonPv with vk :=
      { v with constants := v.constants.zipIdx.map fun (c, j) =>
          if j == 0 then (c.1, c.2 + 1) else c } }
      vkHeaderTemplateSlotsDefault.vkDigest != frWord poseidonVkExec.transcriptRepr
#eval recon1_payload_digest_falsifier_ok -- expect true

/-- **`supported` at F1: THE THREE COUNTS, RE-MEASURED AFTER R.7.** The tuple is unchanged - 8 sigma
    commitments, 8 permutation columns, and `divCeil 8 3` = 3 - but the CLAUSE moved: since R.7
    (D-P59) `SupportedV2.wf.permutationCommitmentsMatch` compares the first two and so HOLDS, and
    the third is what used to refute it. `supported` is now PROVED at the render
    (`PoseidonValid.poseidonValid_supported`); `permCommMatchRepaired` remains in `programOkB` as
    the same fact, computed. -/
def recon1_supported_gap_ok : Bool :=
  (poseidonVkExec.permutation.commitments.size, poseidonVkExec.cs.permutation.columns.size,
    divCeil poseidonVkExec.cs.permutation.columns.size
      (poseidonVkExec.csDegree - 2)) == (8, 8, 3)
#eval recon1_supported_gap_ok -- expect true

/- **THE FIVE CLAUSES THAT ARE THEOREMS AT THE FIXTURE, RE-LISTED BY OBJ.9 (GEN/PROOF).**
    `inputs`, `env`, `noWriters`, `supported` and - since OBJ.9 step 3 - `program` are PROVED at the
    fixture. Until this card `program` was the one clause whose decidable bundle existed HERE, as
    the VM `def` `recon1_programOkB_ok` above, and nowhere as a theorem: OBJ.9 lands
    `poseidonValid_program` - that bundle plus `GasCallOk` and `ExitDiscipline`, each scan witnessed
    at fuel 20000 - as a proposition at the render, and it moves the `program` cell OPEN -> PROVED.
    OBJ.9 step 5 likewise promotes the eight codec-free payload facts measured by
    `recon1_payload_scalars_ok` and `recon1_payload_digest_ok` into the theorem
    `poseidonValid_payload_scalars`; `payload` STAYS HALF, the five point fields are codec-blocked.
    `supported` was REFUTED through the ONE frozen field `permutationCommitmentsMatch` (8 sigma
    commitments against `divCeil 8 3` = 3); R.7 restated that field as the column comparison the
    Rust VK actually makes, which `permCommMatchRepaired` had kept true in `programOkB` all along.
    `generated` replaces the three frozen clauses whose verdicts were `layout_not`,
    `invariants_not` and `model` (two REFUTED, one SORRY): at the derived render the generator run IS
    the artifact but for BUILD_ID (OBJ.7 gate 4), and at today's typed-in render the PARSED PAYLOAD
    refutes it (OBJ.8 step 2, quotient.rs:202). OBJ.9 ATTEMPTED step 1 through `Except.eq_ok_getOk`
    and found the hypothesis it needs decided FALSE - see `PoseidonValid.lean` section V3 for the
    exact goal state and the plan-ordering finding. -/
#check @Midfall.Instances.PoseidonValid.poseidonValid_inputs
#check @Midfall.Instances.PoseidonValid.poseidonValid_slots
#check @Midfall.Instances.PoseidonValid.poseidonValid_noWriters
#check @Midfall.Instances.PoseidonValid.poseidonValid_supported
#check @Midfall.Instances.PoseidonValid.poseidonValid_program
#check @Midfall.Instances.PoseidonValid.poseidonValid_payload_scalars
#check @Midfall.Instances.PoseidonValid.poseidonValid_decidableHalf
#check @Midfall.Instances.PoseidonValid.poseidonValid_returnMptr
#check @Midfall.Instances.PoseidonValid.poseidonValid_transcriptMptr

/- The ONE exit scan (addition 5): the rows' `ExitShape` is the same `exitScan` the clause uses, and
    the staging module proves `exitShape_of_exitDiscipline`, so no second scan exists in the tree. -/
#check @Midfall.LoweringV3.exitShape_of_exitDiscipline
#check @Midfall.LoweringV3.gasCallOk_of_valid
#check @Midfall.LoweringV3.frModulus_of_valid
#check @Midfall.LoweringV3.returnMptr_of_valid
#check @Midfall.LoweringV3.g1IdentityFloor_of_valid
#check @Midfall.LoweringV3.negLagranges_of_valid
#check @Midfall.LoweringV3.cdBound_of_valid
#check @Midfall.LoweringV3.hasMultiPointSet_of_valid
#check @Midfall.LoweringV3.transcriptMptr_of_valid

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
    permutation columns (the clause R.7/D-P59 now states, and which therefore HOLDS), and divCeil
    columns (csDegree - 2) (the retired right-hand side, the PROOF's chunk count, which does not). -/
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
theorem g1CodecZ_not_headlineLaws : ¬ Midfall.LoweringV3.G1CodecHeadlineLaws g1CodecZ := by
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
    ∃ c : G1Codec G₁z, c.toEip = g1CodecZ.toEip ∧ c.ofEip? = g1CodecZ.ofEip? ∧
      Midfall.LoweringV3.G1CodecLawsV3 c := by
  obtain ⟨comp, hinj, hw⟩ := exists_injective_comp
  exact ⟨Midfall.LoweringV3.withCompressed g1CodecZ comp, rfl, rfl,
    Midfall.LoweringV3.withCompressed_lawsV3 g1CodecZ
      Midfall.Instances.CurveSurface.g1CodecZ_laws comp hinj hw⟩

#print axioms lawsV3_satisfiable_at_G1z
#print axioms poseidon_notInhabitedV3

end Midfall.LoweringV3.Deploy

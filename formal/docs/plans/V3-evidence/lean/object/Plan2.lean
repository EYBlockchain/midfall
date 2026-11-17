import Midfall.Instances.PoseidonValid
import Midfall.Generator.Vk
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldCompute
set_option autoImplicit false

/-!
  SCRATCH PORT of the glue of `LoweringPlan::new` (plan.rs:235-329) that is NOT in the tree:
  quotient_program_plan (QRS:425-527), build_quotient_program_items(_with_limb_ops) (QRS:2101-2147),
  native_callback_scratch_words (QRS:1402-1465), quotient_stack_words_for_build (QRS:314-323),
  quotient_opcode_usage / quotient_mem_usage (QRS:259-311), quotient_template_program (QRS:189-238),
  and the constructor itself. Everything else is the tree's own port.
  INPUTS: cs.json (via PoseidonFixture.poseidonCs), the VK PAYLOAD parsed from the Rust-generated
  Halo2VerifyingKey.sol (generate_vk needs curve arithmetic), numInstances = 1, no accumulator.
-/

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.LoweringV2 Midfall.Lowering
open Midfall.Generator.ContractKats Midfall.Generator.VerifierPartialKats
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientBlocks
open Midfall.Generator.QuotientEvaluator Midfall.Generator.QuotientRecognizers

namespace PlanProbe2

def pn (p : Ptr) : Nat := Value.asUsizeNat p.value

/-- BLS12-381 Fr field dictionary. DELTA = Fq::DELTA (curves/src/bls12_381/fq.rs:492). -/
def blsFieldCtx : FieldCtx (Fr Yul.blsR) :=
  { zero := 0, one := 1, add := fun a b => a + b, mul := fun a b => a * b, neg := fun a => -a
    eqF := fun a b => a == b, isZero := fun a => a == 0, powNat := fun b e => b ^ e
    repr := fun v => bytesToNats (frToRepr v)
    delta := (0x08634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7 : Fr Yul.blsR) }

def cs : ConstraintSystem (Fr Yul.blsR) := Midfall.Instances.PoseidonFixture.poseidonCs

def envB : VkBuildEnv Unit :=
  { newVerifierMemoryLayout := VerifierMemoryLayout.new
    compactQuotientProgramFor := fun _ _ => .error (Fault.panic "scratch: unported")
    quotientProgramPlan := fun _ _ => .error (Fault.panic "scratch: unported")
    buildQuotientProgramItems := fun _ => .error (Fault.panic "scratch: unported") }

def inputsB : VerifierBuildInputs Yul.blsR G₁z Unit :=
  { params := { gLagrange := [], g2 := (), sG2 := () }
    vk := poseidonVkExec, numInstances := 1, numCommittedInstances := 1
    accEncoding := none, meta_ := poseidonMeta }

/-- rust: QRS:425-527 quotient_program_plan (validate_execution_manifest omitted) -/
def quotientProgramPlanS (meta_ : ConstraintSystemMeta) (dat : Data) :
    Except Fault QuotientProgramPlan := do
  let parts ← quotientIdentityParts blsFieldCtx cs meta_ dat
  let all := parts.allIdentities
  let selectorFold ← liftQVM (selectorFoldPlan all parts.sortedSimple.length)
  let inlineCount := min parts.gates.length defaultHybridQuotientInlineIdentities
  let inlineIdentities := parts.gates.take inlineCount
  let remaining := parts.gates.drop inlineCount
  let nativeIdx ← liftQVM (nativeGateIndices remaining)
  let nativePermutation := meta_.numPermutationZs > 0
  let nativeLookup := meta_.numLookups > 0
  let structuredTrashTail := meta_.numTrashcans > 0
  let selected := remaining.zipIdx.filter (fun q => nativeIdx.contains q.2)
  let nativeIdentities := selected.map (fun q => q.1)
  let nativeIndexByGate : List (Nat × Nat) := selected.zipIdx.map (fun q => (q.1.2, q.2))
  let gateItems := remaining.zipIdx.map fun q =>
    match nativeIndexByGate.lookup q.2 with
    | some n => QuotientProgramItem.nativeIdentity n
    | none => QuotientProgramItem.identity q.1
  let permItems := if nativePermutation then [QuotientProgramItem.nativePermutation]
    else parts.permutation.map QuotientProgramItem.identity
  let lookupItems := if nativeLookup then [QuotientProgramItem.nativeLookup]
    else parts.lookup.map QuotientProgramItem.identity
  let trashItems := if structuredTrashTail then [] else parts.trash.map QuotientProgramItem.identity
  pure { inlineIdentities := inlineIdentities
         items := gateItems ++ permItems ++ lookupItems ++ trashItems
         nativeIdentities := nativeIdentities
         nativePermutationIdentities := if nativePermutation then parts.permutation else []
         nativeLookupIdentities := if nativeLookup then parts.lookup else []
         structuredTailIdentities := if structuredTrashTail then parts.trash else []
         sortedSimple := parts.sortedSimple
         hasNativePermutation := nativePermutation
         hasNativeLookup := nativeLookup
         selectorFold := selectorFold }

/-- rust: QRS:2120-2146 build_quotient_program_items_with_limb_ops -/
def buildItemsS (items : List QuotientProgramItem) (selectorFold : SelectorFoldPlan)
    (limb : Bool) : Except Fault QuotientProgramBuild := liftQVM do
  let s ← items.foldlM (fun s item =>
    match item with
    | QuotientProgramItem.identity identity =>
        identityExpr shapeRecognizers s identity.expr identity.target (selectorFold.gapFor identity)
    | QuotientProgramItem.nativePermutation => nativePermutation s
    | QuotientProgramItem.nativeLookup => nativeLookup s
    | QuotientProgramItem.nativeIdentity n => nativeIdentity s n) (withLimbVmOps limb)
  finish s

/-- rust: QRS:1402-1465 native_callback_scratch_words -/
def nativeCallbackScratchWordsS (meta_ : ConstraintSystemMeta) (dat : Data)
    (plan : QuotientProgramPlan) : Except Fault Nat := do
  let permWords :=
    if plan.hasNativePermutation then
      (if meta_.numPermutationZs == 0 then 0 else
        2 * meta_.permutationColumns.length + 2 * meta_.numPermutationZs
          + (meta_.numPermutationZs - 1) + 1)
    else 0
  let (maxPar, _) ← (structuredLookupMaxParallel (F := Fr Yul.blsR) meta_).run
    (Evaluator.new blsFieldCtx cs meta_ dat)
  let lookupWords := if plan.hasNativeLookup then maxPar * 3 else 0
  pure (max permWords lookupWords)

def has (bs : Bytes) (op : Nat) : Bool := (bytesToNats bs).contains op

/-- rust: QRS:259-311 -/
def opUsageS (u : Bytes) : QuotientVmOpcodeUsage :=
  { pushConst := has u qOpPushConst, pushMemLiteral := has u qOpPushMemLiteral
    pushMemToken := has u qOpPushMemToken, pushMemTokenOffset := has u qOpPushMemTokenOffset
    pushMemU16 := has u qOpPushMemU16, add := has u qOpAdd, mul := has u qOpMul, neg := has u qOpNeg
    pushConstU8 := has u qOpPushConstU8, foldMain := has u qOpFoldMain
    foldSelector := has u qOpFoldSelector, addConstU8 := has u qOpAddConstU8
    mulConstU8 := has u qOpMulConstU8, addConst := has u qOpAddConst, mulConst := has u qOpMulConst
    addMemU16 := has u qOpAddMemU16, mulMemU16 := has u qOpMulMemU16
    addMulMemMemConstU8 := has u qOpAddMulMemMemConstU8
    addMulConstU8MemU16 := has u qOpAddMulConstU8MemU16, addMulMemMem := has u qOpAddMulMemMem
    runAddMulMemMemConstU8 := has u qOpRunAddMulMemMemConstU8
    runAddMulConstU8MemU16 := has u qOpRunAddMulConstU8MemU16, affineSum := has u qOpAffineSum
    nativePermutation := has u qOpNativePermutation, nativeLookup := has u qOpNativeLookup
    nativeIdentity := has u qOpNativeIdentity, lin7 := has u qOpLin7, bilin7Row := has u qOpBilin7Row
    bilin7Pairwise := has u qOpBilin7Pairwise, modarith7 := has u qOpModarith7, pow5 := has u qOpPow5 }

def memUsageS (u : Bytes) : QuotientVmMemUsage :=
  { l0 := has u qMemL0, lLast := has u qMemLLast, lBlind := has u qMemLBlind, beta := has u qMemBeta
    gamma := has u qMemGamma, x := has u qMemX, theta := has u qMemTheta
    trashChallenge := has u qMemTrashChallenge, instanceEval := has u qMemInstanceEval }

/-- rust: QRS:189-238 quotient_template_program -/
def quotientTemplateProgramS (build : QuotientProgramBuild) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (memory : VerifierMemoryLayout) (selectorFold : SelectorFoldPlan)
    (opModel : QuotientValidator.QuotientOperandModel) :
    Except Fault (QuotientProgram × Nat × QuotientStateSlots) := do
  let chunks := PackedProgramCodec.encodeWords build.bytes
  let constOff ← match vk.quotientConstOffsetWords with
    | some o => pure o | none => throw (Fault.panic "quotient.rs:204")
  let progOff ← match vk.quotientProgramOffsetWords with
    | some o => pure o | none => throw (Fault.panic "quotient.rs:206")
  unless build.consts.length ≤ vk.quotientConstWords do throw (Fault.panic "quotient.rs:207")
  unless chunks.length ≤ vk.quotientProgramWords do throw (Fault.panic "quotient.rs:211")
  let stackMptr := memory.quotientStackMptr
  let stateSlots := QuotientStateSlots.new memory.quotientTmpMptr
  let guards ← quotientVmGuards opModel memory
  pure ({ len := build.bytes.size, opUsage := opUsageS build.usedOps
          memUsage := memUsageS build.usedMemTokens
          constMptr := pn (vkMptr.add constOff)
          evalNumerMptr := stateSlots.evalNumerMptr, traceIdMptr := stateSlots.traceIdMptr
          selectorPowerMptr := stateSlots.selectorPowerMptr
          selectorMaxPower := selectorFold.maxPower
          selectorTailUpdates := selectorTailUpdates selectorFold
          stackMptr := stackMptr, programMptr := pn (vkMptr.add progOff), guards := guards },
        stackMptr, stateSlots)

/-- rust: plan.rs:235-306 LoweringPlan::new, with `generate_vk` replaced by the given payload. -/
def planNewS (vk : Halo2VerifyingKey) : Except Fault (LoweringPlan Unit Unit) := do
  let (vkMptr, meta_, dat, _) ← metaDataForStableStaticLayout Features.solidity envB inputsB vk
  let proofLayout ← ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr
    meta_.numEvals meta_.numPointSets
  let qplan ← quotientProgramPlanS meta_ dat
  let build ← buildItemsS qplan.items qplan.selectorFold defaultQuotientLimbVmOps
  let nativeWords ← nativeCallbackScratchWordsS meta_ dat qplan
  let stackWords := max build.maxStack nativeWords
  let stateWords := quotientStateWords qplan.selectorFold
  let pcsReq ← memoryRequirements meta_ dat
  let accTerms ← accMsmTerms inputsB.accEncoding inputsB.numInstances
  let memory ← memoryLayoutFor envB inputsB meta_ vk vkMptr
    { verifierMemoryLayoutConfigDefault with
      quotientStateWords := stateWords, quotientStackWords := stackWords,
      accMsmTerms := accTerms, pcs := pcsReq }
  let opModel ← quotientOperandModel meta_ dat vk vkMptr memory build qplan.selectorFold
  let (program, stackMptr, stateSlots) ←
    quotientTemplateProgramS build vk vkMptr memory qplan.selectorFold opModel
  pure (LoweringPlan.mk vk vkMptr meta_ dat proofLayout QuotientLowering.vm qplan.sortedSimple
    (some { plan := qplan, build := build, program := program, stackMptr := stackMptr,
            stateSlots := stateSlots }) none pcsReq memory)

/-- The parsed payload with the four NON-RENDERED reservation fields that `generate_vk`
    (vk.rs:400-431) sets and `vkModelFromArtifact` (Contracts.lean:868-871) leaves at none/0.
    Offsets from the port's own `VkPayloadLayout.forVk`. -/
def vkFilled : Except Fault Halo2VerifyingKey := do
  let hdr := (poseidonVkGen.constants.filter (fun c => c.1 != "quotient_const" && c.1 != "quotient_program")).length
  let nC := (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_const")).length
  let nP := (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_program")).length
  let lay ← unwrapAt "scratch:forVk" (VkPayloadLayout.forVk hdr nC nP
    poseidonVkGen.fixedComms.length poseidonVkGen.permutationComms.length)
  let qc ← unwrapAt "scratch:qc" (lay.wordOffset PayloadSectionKind.quotientConstants)
  let qp ← unwrapAt "scratch:qp" (lay.wordOffset PayloadSectionKind.quotientProgram)
  pure { poseidonVkGen with quotientConstOffsetWords := some qc, quotientConstWords := nC, quotientProgramOffsetWords := some qp, quotientProgramWords := nP }

def planS : Except Fault (LoweringPlan Unit Unit) := vkFilled >>= planNewS

def showE {α : Type} (e : Except Fault α) (f : α → String) : String :=
  match e with
  | .ok a => f a
  | .error (Fault.panic s) => "PANIC " ++ s
  | .error _ => "ERR(other)"

-- C0. it runs
#eval showE planS fun L => s!"ok vkMptr={pn L.vkMptr} proofLen={L.proofLayout.proofLen} numPointSets={L.meta_.numPointSets} sortedSimple={L.sortedSimple}"

-- C1. quotient plan shape
#eval showE planS fun L => match L.quotient with
  | some q => s!"inline={q.plan.inlineIdentities.length} items={q.plan.items.length} native={q.plan.nativeIdentities.length} perm={q.plan.nativePermutationIdentities.length} lookup={q.plan.nativeLookupIdentities.length} tail={q.plan.structuredTailIdentities.length} hasPerm={q.plan.hasNativePermutation} hasLookup={q.plan.hasNativeLookup} maxPower={q.plan.selectorFold.maxPower} tails={q.plan.selectorFold.tailExponents}"
  | none => "no quotient"

-- C2. the VM build against the VK PAYLOAD words (Rust-generated Halo2VerifyingKey.sol)
#eval showE planS fun L => match L.quotient with
  | some q =>
      let payloadConsts := (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_const")).map (·.2)
      let payloadProg := (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_program")).map (·.2)
      s!"len={q.build.bytes.size} (0x58={0x58}) consts={q.build.consts.length} maxStack={q.build.maxStack} constsEqPayload={q.build.consts == payloadConsts} programEqPayload={PackedProgramCodec.encodeWords q.build.bytes == payloadProg} payloadProgWords={payloadProg.length}"
  | none => "no quotient"

-- C3. the template program against the typed-in `quotientDeployedProgram`
#eval showE planS fun L => match L.quotient with
  | some q =>
      let d := quotientDeployedProgram
      let p := q.program
      s!"len {p.len}/{d.len} constMptr {p.constMptr}/{d.constMptr} evalNumer {p.evalNumerMptr}/{d.evalNumerMptr} traceId {p.traceIdMptr}/{d.traceIdMptr} selPow {p.selectorPowerMptr}/{d.selectorPowerMptr} maxPow {p.selectorMaxPower}/{d.selectorMaxPower} stack {p.stackMptr}/{d.stackMptr} prog {p.programMptr}/{d.programMptr} guards {p.guards == d.guards} tails {p.selectorTailUpdates.map (fun t => (t.selectorOffset, t.powerOffset)) == d.selectorTailUpdates.map (fun t => (t.selectorOffset, t.powerOffset))}"
  | none => "no quotient"

-- C4. generator invariants on the DERIVED plan (frozen clause 3)
#eval showE planS fun L => match L.validateGeneratorInvariants with
  | .ok (.ok ()) => "invariants OK"
  | .ok (.error s) => "invariants REFUSED: " ++ s
  | .error (Fault.panic s) => "invariants PANIC " ++ s
  | .error _ => "invariants ERR"

-- C5. memory: derived vs the plan the tree carries
#eval showE planS fun L =>
  s!"memory.vkMptr {pn L.memory.vkMptr}/{pn poseidonPlanV2.memory.vkMptr} qTmp {L.memory.quotientTmpMptr}/{poseidonPlanV2.memory.quotientTmpMptr} qStack {L.memory.quotientStackMptr}/{poseidonPlanV2.memory.quotientStackMptr} qStackHi {L.memory.quotientStackHi}/{poseidonPlanV2.memory.quotientStackHi} selAcc {L.memory.selectorAccMptr}/{poseidonPlanV2.memory.selectorAccMptr}"

end PlanProbe2

namespace PlanProbe2
#eval showE vkFilled fun v => s!"{v.quotientConstOffsetWords} {v.quotientConstWords} {v.quotientProgramOffsetWords} {v.quotientProgramWords} len={v.len}"
-- C6. what the parsed payload carries
#eval (poseidonVkGen.quotientConstOffsetWords, poseidonVkGen.quotientConstWords,
       poseidonVkGen.quotientProgramOffsetWords, poseidonVkGen.quotientProgramWords,
       poseidonVkGen.constants.length, poseidonVkGen.constants.map (·.1) |>.drop 28)
end PlanProbe2

namespace PlanProbe2

/-! ## D. From the derived plan to the text, with NO quotient text from the artifact -/

/-- rust: plan.rs:381-394 compact_quotient_blocks -/
def compactBlocksS (L : LoweringPlan Unit Unit) (trace : Bool) :
    Except Fault QuotientComputationBlocks := do
  match L.quotient with
  | none => throw (Fault.panic "plan.rs:vm_quotient")
  | some q =>
      let (blocks, _) ← compactQuotientComputationBlocks blsFieldCtx cs L.meta_ L.data q.plan
        q.stackMptr q.stateSlots trace
      pure blocks

def blocksS : Except Fault QuotientComputationBlocks := planS >>= fun L => compactBlocksS L false

-- D1. the ported QRS:2000 on the derived plan against the blocks SLICED from the artifact
#eval showE blocksS fun b =>
  let a := poseidonQBlocks
  s!"inline {b.inlineComputations == a.inlineComputations} ({b.inlineComputations.map List.length}/{a.inlineComputations.map List.length}) evalNumer {b.evalNumerComputations == a.evalNumerComputations} postVm {b.postVmComputations == a.postVmComputations} ({b.postVmComputations.map List.length}/{a.postVmComputations.map List.length}) perm {b.nativePermutationComputation == a.nativePermutationComputation} ({b.nativePermutationComputation.length}/{a.nativePermutationComputation.length}) lookup {b.nativeLookupComputation == a.nativeLookupComputation} ({b.nativeLookupComputation.length}/{a.nativeLookupComputation.length}) nativeId {b.nativeIdentityComputations == a.nativeIdentityComputations} ({b.nativeIdentityComputations.map List.length}/{a.nativeIdentityComputations.map List.length})"

/-- The model from the derived plan and the derived blocks. Build inputs as in the tree. -/
def modelS : Except Fault Model := do
  let L ← planS
  let b ← compactBlocksS L false
  generateVerifierFromPlan (fun _ _ => b) poseidonInputs poseidonFlags L

def diffLines (a b : String) : List (Nat × String × String) :=
  ((a.splitOn "\n").zip (b.splitOn "\n")).zipIdx.filterMap fun ((x, y), i) =>
    if x == y then none else some (i + 1, x, y)

-- D2. THE GATE: the whole Halo2Verifier.sol from the derived model, nothing from the artifact
#eval showE modelS fun m =>
  let r := renderHalo2Verifier (rootCtxOfVerifier m) (partsOf m)
  let d := diffLines r poseidonVerifierDump
  s!"equal={r == poseidonVerifierDump} len={r.length}/{poseidonVerifierDump.length} lines={(r.splitOn "\n").length}/{(poseidonVerifierDump.splitOn "\n").length} differingLines={d.length} first={d.take 2}"

-- D3. layout validation (artifacts.rs:338) on the derived model
#eval showE modelS fun m => s!"validateLayout ok = {(Halo2Verifier.validateLayout m).isOk}"

-- D4. the VK contract from the payload with reservation fields
#eval showE vkFilled fun v => s!"vk render equal = {renderHalo2VerifyingKey v == poseidonVkDump}"

-- D5. dual-build certification (plan.rs:310-325)
#eval showE planS fun L => match L.quotient with
  | some q => match buildItemsS q.plan.items q.plan.selectorFold false with
      | .ok base => (match QuotientCertify.certifyQuotientBuildsAgree q.plan q.build base L.vk with
          | .ok () => s!"certify OK (baseline len {base.bytes.size})"
          | .error e => "certify REFUSED " ++ e)
      | .error _ => "baseline build failed"
  | none => "no quotient"

-- D6. the program of the theorem at the derived render
#eval showE (do let L ← planS; let m ← modelS; pure (L, m)) fun (L, m) =>
  let pv := planViewOf L m none
  s!"codegenAgrees={codegenAgrees pv m} astTokens={(yulTokens (YulSemantics.EVM.print (mainAsmRaw pv))).length} textTokens={(mainAssemblyTokens m).length} mainClosed={mainClosed pv m} constTable={(constTableOf m).length} sameConstTable={constTableOf m == constTableOf poseidonM}"

end PlanProbe2

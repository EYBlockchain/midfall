-- |
-- Midfall.Instances.PlanNewKats
--
-- OBJ.6 (PLAN-V3, V3 row 40): THE GATES FOR Generator/PlanNew.lean. Every claim below is
-- checked against DATA THE RUST EMITTED, not against a value re-derived by reading the Rust.
-- The three sources are named once here and each gate says which it uses:
--
--   (S1) THE VK PAYLOAD. proofs/solidity-verifier/target/poseidon-fixture-dump/
--        Halo2VerifyingKey.sol, tracked in git, written by the Rust generator at
--        vk.rs:443-448 (the quotient const table and the packed program words) and re-read
--        by vk.rs:456-463 before it is emitted. Parsed here by vkModelFromArtifact, so the
--        words are the bytes the Rust put in the contract. This is the ONLY source for the
--        build KAT: the const table and the program chunks the port emits must equal them.
--   (S2) THE DEPLOYED VERIFIER. Halo2Verifier.sol, same directory, 175,908 bytes.
--        quotientDeployedProgram (VerifierPartials.lean:1068) is read out of it by
--        quotientProgram_derivedFromArtifact_ok - the five base pointers, the program
--        length, the spill ceiling, the bucket count, the selector max power and all four
--        tail pairs - with the two fields the dump cannot show derived at
--        quotientProgram_inertFieldsDerived_ok. This is the source for the template-program
--        KAT and for the stack-region KAT.
--   (S3) THE CONSTRAINT SYSTEM. fixtures/conformance/poseidon/cs.json, written by the F.1
--        exporter out of the live halo2 ConstraintSystem, rebuilt by PoseidonFixture.
--        poseidonCs and fed to the ported ConstraintSystemMeta.new. The protocol's quotient
--        identity counts (gates 11, permutation 7, lookup 3, trash 1) and the sorted simple-
--        selector columns (13, 14, 15, 17) are therefore Rust output and not this file's
--        guess. This is the source for the plan-shape KAT.
--
-- WHY THESE ARE GATES AND NOT A RESTATEMENT. The port could be wrong in a way that agrees
-- with itself: quotientProgramPlan, buildQuotientProgramItemsWithLimbOps and
-- quotientTemplateProgram are three Lean functions, and a KAT that compared one against
-- another would prove nothing. Every gate below compares a port output against S1, S2 or S3,
-- and the two falsifiers (a different inline count, a perturbed reservation) show the
-- comparison can actually fail.
--
-- WHAT IS NOT EVIDENCE, STATED. The plan's own SHAPE (which identities went inline, which
-- became native markers) is an internal compiler decision the Rust never prints. There is no
-- Rust-produced artifact that says 'inline = 4'. What the Rust DOES emit is the consequence:
-- the bytecode, the const table and the twelve program fields. So quotientPlan_shape_ok is
-- pinned against S3 for the four identity counts it must preserve and against S2 for the
-- selector max power, and the inline/native split is pinned only indirectly - by the fact
-- that the item stream it produces lowers to S1's bytes. A card that wanted the split itself
-- pinned would have to export the manifest from Rust; that export does not exist and is
-- named in the report as the one place this card has no direct Rust witness.
--
-- native_decide lives nowhere in this file: the gates are #eval booleans, so kat_gate.py
-- reports the value that moved. The pipeline that produces the memory layout and the operand
-- model is assembled here and not shipped: OBJ.7 owns newFromVk, and until it lands this is
-- the only place the fixture's plan can be built.

import Midfall.Instances.PoseidonValid
import Midfall.Generator.Vk
import Midfall.Generator.PlanNew

set_option autoImplicit false

namespace Midfall.Instances.PlanNewKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances
open Midfall.Instances.PoseidonValid Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonFixture
open Midfall.Generator.ContractKats Midfall.Generator.VerifierPartialKats
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientBlocks
open Midfall.Generator.QuotientEvaluator Midfall.Generator.QuotientRecognizers
open Midfall.Generator.EvmKats
open Midfall.Generator.PlanNew

/-- The fixture's field dictionary, built by the ported frFieldCtx. DELTA is read out of the
    build inputs (DeployedProfile.lean:154, whose own note says the value is observable in the
    artifact at D:1975) rather than pasted, and gate 1 re-pins it against the literal in
    curves/src/bls12_381/fq.rs:492. -/
def frDeltaHex : String := poseidonInputs.frDelta

def frDeltaNat : Nat := hexNatOf (String.ofList (frDeltaHex.toList.drop 2))

def frDelta : Fr Yul.blsR := Nat.cast frDeltaNat

def field : FieldCtx (Fr Yul.blsR) := frFieldCtx frDelta

/-- S3: the constraint system the F.1 exporter wrote out. -/
def cs : ConstraintSystem (Fr Yul.blsR) := Midfall.Instances.PoseidonFixture.poseidonCs

/-- The four reservation fields vk.rs:400-431 sets and vkModelFromArtifact
    (Contracts.lean:868-871) cannot read back, because the artifact renders the words but not
    the offsets. Filled from VkPayloadLayout.forVk over the counts the parsed payload shows -
    the same 31 / 1 / 32 / 3 OBJ.7's guidance predicts, and gate 2 prints them. -/
def vkFilled : Except Fault Halo2VerifyingKey := do
  let hdr := (poseidonVkGen.constants.filter
    fun c => c.1 != "quotient_const" && c.1 != "quotient_program").length
  let nC := (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_const")).length
  let nP := (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_program")).length
  let lay <- unwrapAt "PlanNewKats:forVk"
    (VkPayloadLayout.forVk hdr nC nP poseidonVkGen.fixedComms.length
      poseidonVkGen.permutationComms.length)
  let qc <- unwrapAt "PlanNewKats:qc" (lay.wordOffset PayloadSectionKind.quotientConstants)
  let qp <- unwrapAt "PlanNewKats:qp" (lay.wordOffset PayloadSectionKind.quotientProgram)
  pure { poseidonVkGen with
    quotientConstOffsetWords := some qc
    quotientConstWords := nC
    quotientProgramOffsetWords := some qp
    quotientProgramWords := nP }

/-- The env the memory-layout helpers need. Three of its four callbacks are the OBJ.6 ports,
    which is the point of VkBuildEnv: OBJ.7 fills them for real, and until then the layout
    helper only ever calls newVerifierMemoryLayout. -/
def envB : VkBuildEnv Unit :=
  { newVerifierMemoryLayout := VerifierMemoryLayout.new
    compactQuotientProgramFor := fun _ _ => .error (Fault.panic "PlanNewKats: unused")
    quotientProgramPlan := fun _ _ => .error (Fault.panic "PlanNewKats: unused")
    buildQuotientProgramItems := fun _ => .error (Fault.panic "PlanNewKats: unused") }

def inputsB : VerifierBuildInputs Yul.blsR G₁z Unit :=
  { params := { gLagrange := [], g2 := (), sG2 := () }
    vk := poseidonVkExec, numInstances := 1, numCommittedInstances := 1
    accEncoding := none, meta_ := poseidonMeta }

/-- Everything the gates read, assembled once. The shape mirrors plan.rs:238-300 and is NOT a
    port - it is the test harness that holds the fixture's pieces together. -/
structure Probe where
  vk : Halo2VerifyingKey
  vkMptr : Ptr
  meta_ : ConstraintSystemMeta
  dat : Data
  parts : QuotientIdentityParts
  plan : QuotientProgramPlan
  build : QuotientProgramBuild
  nativeWords : Nat
  stackWords : Nat
  memory : VerifierMemoryLayout
  program : QuotientProgram
  opModel : QuotientValidator.QuotientOperandModel
  stateSlots : QuotientStateSlots
  manifest : List QuotientExecutionManifestEntry

def probe : Except Fault Probe := do
  let vk <- vkFilled
  -- OBJ.7's receiver refactor (card Do 1) moved the four layout helpers off
  -- VerifierBuildInputs and onto (meta, numInstances). This is the &self wrapper, so the
  -- gate's content is unchanged; GeneratedKats gate 1 pins wrapper == core for all four.
  let (vkMptr, meta_, dat, _) <-
    metaDataForStableStaticLayoutInputs Features.solidity envB inputsB vk
  let parts <- quotientIdentityParts field cs meta_ dat
  let plan <- quotientProgramPlan field cs meta_ dat
  let build <- buildQuotientProgramItems plan.items plan.selectorFold
  let nativeWords <- nativeCallbackScratchWords field cs meta_ dat plan
  let stackWords := quotientStackWordsForBuild build nativeWords
  let pcsReq <- memoryRequirements meta_ dat
  let accTerms <- accMsmTerms inputsB.accEncoding inputsB.numInstances
  let memory <- memoryLayoutForInputs envB inputsB meta_ vk vkMptr
    { verifierMemoryLayoutConfigDefault with
      quotientStateWords := quotientStateWords plan.selectorFold
      quotientStackWords := stackWords
      accMsmTerms := accTerms
      pcs := pcsReq }
  let opModel <- quotientOperandModel meta_ dat vk vkMptr memory build plan.selectorFold
  let (program, _, stateSlots) <-
    quotientTemplateProgram build vk vkMptr memory plan.selectorFold opModel
  let manifest <- match executionManifest plan with
    | .ok m => .ok m
    | .error e => .error (Fault.panic e)
  pure
    { vk := vk
      vkMptr := vkMptr
      meta_ := meta_
      dat := dat
      parts := parts
      plan := plan
      build := build
      nativeWords := nativeWords
      stackWords := stackWords
      memory := memory
      program := program
      opModel := opModel
      stateSlots := stateSlots
      manifest := manifest }

/-- A fault anywhere in the pipeline makes EVERY gate below red rather than passing on a
    default. That is deliberate: the alternative - a fallback Probe - is a second guess at the
    fixture, which is the thing this card is not allowed to be. -/
def atFixture (f : Probe -> Bool) : Bool := match probe with | .ok p => f p | .error _ => false

/-- S1, the two quotient sections of the payload the Rust wrote. -/
def payloadConsts : List Word256 :=
  (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_const")).map (·.2)

def payloadProg : List Word256 :=
  (poseidonVkGen.constants.filter (fun c => c.1 == "quotient_program")).map (·.2)

/-! ## THE GATES -/

/-- Square-and-multiply, written out by hand so gate 1 compares two algorithms and not one
    against itself: the Rust's Field::pow is a bit loop, and b ^ e is Lean's generic Monoid.pow.
    If the two ever disagree the dictionary is wrong, and every number downstream is wrong
    with it. -/
def sqMul (b : Fr Yul.blsR) (e : Nat) : Fr Yul.blsR :=
  let nbits := if e == 0 then 1 else Nat.log2 e + 1
  let bits := (List.range nbits).map fun i => (e / 2 ^ i) % 2
  ((bits.foldl (fun (q : Fr Yul.blsR × Fr Yul.blsR) bit =>
      (if bit == 1 then q.1 * q.2 else q.1, q.2 * q.2)) (1, b)) |>.1)

/-- A Bytes built from a list of byte values - the fixture the two usage tables are probed
    with, one opcode at a time. -/
def bytesOfNats (xs : List Nat) : Bytes :=
  xs.foldl (fun acc b => acc.push (UInt8.ofNat b)) Bytes.empty

/-- The 31 (opcode, field) pairs of quotient_opcode_usage, in the Rust's declaration order
    (QRS:262-292). This list IS the field count: quotientOpcodeUsage_table_ok walks it, so a
    32nd opcode added to either side without a row here reddens, and a row whose projection
    names the wrong field reddens on its own singleton. -/
def opcodeFields : List (Nat × (QuotientVmOpcodeUsage -> Bool)) :=
  [ (qOpPushConst, fun u => u.pushConst),
    (qOpPushMemLiteral, fun u => u.pushMemLiteral),
    (qOpPushMemToken, fun u => u.pushMemToken),
    (qOpPushMemTokenOffset, fun u => u.pushMemTokenOffset),
    (qOpPushMemU16, fun u => u.pushMemU16),
    (qOpAdd, fun u => u.add),
    (qOpMul, fun u => u.mul),
    (qOpNeg, fun u => u.neg),
    (qOpPushConstU8, fun u => u.pushConstU8),
    (qOpFoldMain, fun u => u.foldMain),
    (qOpFoldSelector, fun u => u.foldSelector),
    (qOpAddConstU8, fun u => u.addConstU8),
    (qOpMulConstU8, fun u => u.mulConstU8),
    (qOpAddConst, fun u => u.addConst),
    (qOpMulConst, fun u => u.mulConst),
    (qOpAddMemU16, fun u => u.addMemU16),
    (qOpMulMemU16, fun u => u.mulMemU16),
    (qOpAddMulMemMemConstU8, fun u => u.addMulMemMemConstU8),
    (qOpAddMulConstU8MemU16, fun u => u.addMulConstU8MemU16),
    (qOpAddMulMemMem, fun u => u.addMulMemMem),
    (qOpRunAddMulMemMemConstU8, fun u => u.runAddMulMemMemConstU8),
    (qOpRunAddMulConstU8MemU16, fun u => u.runAddMulConstU8MemU16),
    (qOpAffineSum, fun u => u.affineSum),
    (qOpNativePermutation, fun u => u.nativePermutation),
    (qOpNativeLookup, fun u => u.nativeLookup),
    (qOpNativeIdentity, fun u => u.nativeIdentity),
    (qOpLin7, fun u => u.lin7),
    (qOpBilin7Row, fun u => u.bilin7Row),
    (qOpBilin7Pairwise, fun u => u.bilin7Pairwise),
    (qOpModarith7, fun u => u.modarith7),
    (qOpPow5, fun u => u.pow5) ]

/-- The 9 (token, field) pairs of quotient_mem_usage (QRS:300-308). -/
def memFields : List (Nat × (QuotientVmMemUsage -> Bool)) :=
  [ (qMemL0, fun u => u.l0),
    (qMemLLast, fun u => u.lLast),
    (qMemLBlind, fun u => u.lBlind),
    (qMemBeta, fun u => u.beta),
    (qMemGamma, fun u => u.gamma),
    (qMemX, fun u => u.x),
    (qMemTheta, fun u => u.theta),
    (qMemTrashChallenge, fun u => u.trashChallenge),
    (qMemInstanceEval, fun u => u.instanceEval) ]

def opcodeFlags (u : QuotientVmOpcodeUsage) : List Bool := opcodeFields.map fun q => q.2 u

def memFlags (u : QuotientVmMemUsage) : List Bool := memFields.map fun q => q.2 u

/-- GATE 1 (the dictionary). frFieldCtx is the R9 record the reference gets from the Field
    impls. Every field is checked against an independent computation, and DELTA against the
    literal in curves/src/bls12_381/fq.rs:492 - the value the artifact's own frDelta string
    carries, so the constant is Rust-observed on both sides. -/
def frFieldCtx_matchesArtifact_ok : Bool :=
  let r : Fr Yul.blsR := 12345
  let q : Fr Yul.blsR := 987654321
  frDelta.val == 0x08634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7
    && frDeltaHex == "0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7"
    && field.delta == frDelta && field.zero == 0 && field.one == 1
    && field.add r q == r + q && field.mul r q == r * q && field.neg r == -r
    && field.eqF r q == false && field.eqF r r == true && field.isZero 0 == true
    && field.repr r == bytesToNats (frToRepr r) && (field.repr r).length == 32
    && field.powNat r 0 == (1 : Fr Yul.blsR)
    && field.powNat r 13 == sqMul r 13 && field.powNat q 40 == sqMul q 40
#eval frFieldCtx_matchesArtifact_ok -- expect true

/-- GATE 2 (S3 + S2). The plan's shape. The four identity-family counts are the ones the F.1
    exporter wrote into cs.json and the ported ConstraintSystemMeta.new derived - the Rust
    produced them and quotientIdentityParts asserts against them (QRS:941-960) - so a plan that
    loses an identity cannot pass. The selector max power 21 is read out of Halo2Verifier.sol
    by quotientProgram_derivedFromArtifact_ok, so it too is Rust output. The inline/native
    SPLIT has no direct Rust witness (header); it is pinned here as a value and falsified by
    gate 12. -/
def quotientPlan_shape_ok : Bool := atFixture fun pp =>
  let q := pp.plan
  let m := pp.meta_
  q.inlineIdentities.length == 4 && q.items.length == 9
    && q.nativeIdentities.length == 3
    && q.nativePermutationIdentities.length == 7 && q.nativeLookupIdentities.length == 3
    && q.structuredTailIdentities.length == 1
    && q.hasNativePermutation == true && q.hasNativeLookup == true
    && q.selectorFold.maxPower == 21
    && q.sortedSimple == [13, 14, 15, 17]
    -- S3: the four families, against the counts cs.json's protocol plan yields.
    && pp.parts.gates.length == m.protocol.quotient.gates
    && pp.parts.permutation.length == m.protocol.quotient.permutation
    && pp.parts.lookup.length == m.protocol.quotient.lookup
    && pp.parts.trash.length == m.protocol.quotient.trash
    && m.protocol.quotient.gates == 11 && m.protocol.quotient.permutation == 7
    && m.protocol.quotient.lookup == 3 && m.protocol.quotient.trash == 1
    -- The stream is preserved: 4 inline + the 7 gate items + the two markers expanded to the
    -- 7 permutation and 3 lookup identities they replace + the 1 structured tail = 22.
    && q.inlineIdentities.length + (q.items.length - 2)
        + q.nativePermutationIdentities.length + q.nativeLookupIdentities.length
        + q.structuredTailIdentities.length == pp.parts.allIdentities.length
#eval quotientPlan_shape_ok -- expect true

/-- GATE 3 (S1, THE CARD'S HEADLINE). The build the ported lowering emits IS the pair of
    sections the Rust generator wrote into the VK payload at vk.rs:443-448: the const table
    word for word, and the packed program word for word. 88 bytes, 1 const, max stack 2. -/
def quotientBuild_matchesPayload_ok : Bool := atFixture fun pp =>
  pp.build.bytes.size == 88 && pp.build.consts.length == 1 && pp.build.maxStack == 2
    && pp.build.consts == payloadConsts
    && PackedProgramCodec.encodeWords pp.build.bytes == payloadProg
    && payloadProg.length == 3 && payloadConsts.length == 1
#eval quotientBuild_matchesPayload_ok -- expect true

/-- GATE 4 (S2). All twelve fields of the template program, against the program read out of
    Halo2Verifier.sol. Field by field because QuotientProgram derives no BEq - the same reason
    PoseidonInputs compares the plan field by field - and the two usage records are compared
    through the flag lists gate 8 pins. -/
def quotientProgram_matchesTypedIn_ok : Bool := atFixture fun pp =>
  let a := pp.program
  let d := quotientDeployedProgram
  a.len == d.len && a.constMptr == d.constMptr && a.evalNumerMptr == d.evalNumerMptr
    && a.traceIdMptr == d.traceIdMptr && a.selectorPowerMptr == d.selectorPowerMptr
    && a.selectorMaxPower == d.selectorMaxPower && a.stackMptr == d.stackMptr
    && a.programMptr == d.programMptr && a.guards == d.guards
    && opcodeFlags a.opUsage == opcodeFlags d.opUsage
    && memFlags a.memUsage == memFlags d.memUsage
    && (a.selectorTailUpdates.map fun t => (t.selectorOffset, t.powerOffset))
        == (d.selectorTailUpdates.map fun t => (t.selectorOffset, t.powerOffset))
    && a.len == 88 && a.selectorMaxPower == 21 && a.guards.numSelectorBuckets == 4
#eval quotientProgram_matchesTypedIn_ok -- expect true

/-- GATE 5 (S2). The native scratch table and the stack region it forces. 25 is not a number
    this file chooses: 2 * 8 permutation columns + 2 * 3 perm_z + 2 + 1 = 25, and the deployed
    artifact's own spill ceiling guards.stack_last = 0x6c60 is q_stack_hi - 32, so the region
    the Rust reserved is exactly 25 words wide. The interpreted max_stack is 2, so the max in
    quotient_stack_words_for_build is doing real work: without it the region would be 2 words
    and the artifact's 0x6c60 would be unreachable. -/
def quotientNativeScratchWords_matchesStackRegion_ok : Bool := atFixture fun pp =>
  pp.nativeWords == 25 && pp.stackWords == 25
    && pp.build.maxStack == 2 && pp.stackWords == pp.nativeWords
    && pp.memory.quotientStackHi - pp.memory.quotientStackMptr == 25 * wordBytes
    && pp.program.guards.stackLast == pp.memory.quotientStackHi - wordBytes
    && pp.program.guards.stackLast == 0x6c60
    && structuredPermutationScratchWords pp.meta_ == 25
    && quotientStackWordsForBuild pp.build 0 == 2
    && quotientStackWordsForBuild pp.build 99 == 99
#eval quotientNativeScratchWords_matchesStackRegion_ok -- expect true

/-- GATE 6 (S1 + S3). compact_quotient_program_for returns the pair the Rust returns, and the
    pair agrees with the plan and build the pipeline produced - i.e. the helper is a composition
    and not a second implementation. The second component is the plan's sorted_simple, which is
    cs.json's selector-column order. -/
def compactQuotientProgramFor_matchesBuild_ok : Bool := atFixture fun pp =>
  match compactQuotientProgramFor field cs pp.meta_ pp.dat with
  | .ok (b, ss) => b == pp.build && ss == pp.plan.sortedSimple && ss == [13, 14, 15, 17]
  | .error _ => false
#eval compactQuotientProgramFor_matchesBuild_ok -- expect true

/-- GATE 7 (the bridge). The manifest the ported execution_manifest builds is the identity
    stream with an execution mode spliced in: same length, same (global_index, source, target)
    triples in the same order, and the ported validator accepts it. The Rust runs this same
    check on every generator run (QRS:523-524) and PANICS if it fails, so the existence of the
    artifact is the Rust-produced evidence that the check passes for the plan the Rust built;
    this gate says the Lean plan passes it too, and that the modes the split assigns add up. -/
def quotientManifest_preservesStream_ok : Bool := atFixture fun pp =>
  let all := pp.parts.allIdentities
  pp.manifest.length == all.length && pp.manifest.length == 22
    && ((pp.manifest.zip all).all fun q =>
        q.1.globalIndex == q.2.meta_.globalIndex && q.1.source == q.2.meta_.source
          && q.1.target == q.2.target)
    && (validateExecutionManifest pp.plan all).isOk
    && (pp.manifest.filter fun e => match e.execution with
        | QuotientExecutionKind.nativeIdentity _ => true
        | _ => false).length == 3
    && (pp.manifest.map fun e => e.execution).count QuotientExecutionKind.inline == 4
    && (pp.manifest.map fun e => e.execution).count
        QuotientExecutionKind.nativePermutation == 7
    && (pp.manifest.map fun e => e.execution).count QuotientExecutionKind.nativeLookup == 3
    && (pp.manifest.map fun e => e.execution).count
        QuotientExecutionKind.structuredTail == 1
    && (pp.manifest.map fun e => e.execution).count
        QuotientExecutionKind.interpreted == 4
#eval quotientManifest_preservesStream_ok -- expect true

/-- GATE 8 (the table itself). For each of the 31 opcodes, a program whose used_ops is exactly
    that one byte must set exactly that one flag and no other. This is the only gate that can
    see a transposed row: gate 4 compares the fixture's program, where 10 of the 31 flags are
    set, and a swap between two of the ten would move a bit gate 4 cannot see because
    quotientDeployedProgram.opUsage was read off the artifact by the same 31-name shape. The
    list length is pinned too, so a 32nd opcode in either language reddens until a row is added.

    The Rust's own used_ops at the fixture is [0x05, 0x06, 0x08, 0x0b, 0x0d, 0x10, 0x11, 0x19,
    0x1b, 0x1f] - ten bytes, and gate 4 says the artifact's flags agree with what the port
    derives from them. -/
def quotientOpcodeUsage_table_ok : Bool :=
  opcodeFields.length == 31
    && (opcodeFields.zipIdx.all fun ((op, f), i) =>
        let u := quotientOpcodeUsage (bytesOfNats [op])
        f u == true && (opcodeFields.zipIdx.all fun ((_op2, g), j) =>
          if j == i then g u == true else g u == false)
          && op < 256)
#eval quotientOpcodeUsage_table_ok -- expect true

/-- GATE 9: the same for the nine memory tokens (QRS:296-310). The fixture's used_mem_tokens is
    EMPTY - the deployed program touches no Q_MEM_* token at all, which is why
    quotientDeployedProgram.memUsage is the default - so gate 4 alone could not tell a correct
    mem table from an all-false one. This can. -/
def quotientMemUsage_table_ok : Bool :=
  memFields.length == 9
    && (memFields.zipIdx.all fun ((tok, f), i) =>
        let u := quotientMemUsage (bytesOfNats [tok])
        f u == true && (memFields.zipIdx.all fun ((_tok2, g), j) =>
          if j == i then g u == true else g u == false) && tok < 256)
    && memFlags (quotientMemUsage Bytes.empty) == List.replicate 9 false
#eval quotientMemUsage_table_ok -- expect true

/-- The site string a Fault carries, or "ok". -/
def faultSiteOf {A : Type} (x : Except Fault A) : String :=
  match x with
  | .ok _ => "ok"
  | .error (Fault.panic site) => site
  | .error _ => "other"

def qrs : String := "proofs/solidity-verifier/src/lowering/quotient.rs"

/-- The template program for an ARBITRARY vk, so gate 10 can perturb one reservation field at a
    time. The operand model is rebuilt from the same perturbed vk because quotient_vm_guards
    reads the model and the memory together; the four aborts fire before it is consulted, so
    the arm only has to be well-typed. -/
def programAt (pp : Probe) (v : Halo2VerifyingKey) : Except Fault QuotientProgram := do
  let (program, _, _) <-
    quotientTemplateProgram pp.build v pp.vkMptr pp.memory pp.plan.selectorFold pp.opModel
  Except.ok program

/-- GATE 10 (the four aborts, FIRED). The bounds checks are the reason the function exists -
    QRS:185-188 says they live here so the standalone evaluator and the in-verifier VM paths
    cannot drift - so a gate that only checks the happy path would let the whole guard block be
    deleted. Each perturbation is one field of the VK reservation, and the site each must report
    is named. The four are QRS:202, :204, :205, :209 (header: :202 is the CONSTANT offset, not
    :204 as the card's OBJ.7 note predicts). -/
def quotientTemplateProgram_reservationAborts_ok : Bool := atFixture fun pp =>
  faultSiteOf (programAt pp { pp.vk with quotientConstOffsetWords := none }) ==
    qrs ++ ":202 (VK must carry quotient constants)"
    && faultSiteOf (programAt pp { pp.vk with quotientProgramOffsetWords := none }) ==
      qrs ++ ":204 (VK must carry quotient program)"
    && faultSiteOf (programAt pp { pp.vk with quotientConstWords := 0 }) ==
      qrs ++ ":205 (quotient const table exceeded VK payload reservation)"
    && faultSiteOf (programAt pp { pp.vk with quotientProgramWords := 0 }) ==
      qrs ++ ":209 (quotient program length exceeded VK payload reservation)"
    && faultSiteOf (programAt pp pp.vk) == "ok"
#eval quotientTemplateProgram_reservationAborts_ok -- expect true

/-- GATE 11 (R4, the sites against the Rust). quotient.rs read at #eval time, exactly the way
    panicSites_areTheRecordedOnes_ok reads plan.rs. Each cited line must hold the construct the
    port names, so a re-cite cannot drift and the header's correction of the card's :204
    prediction is the file's own statement and not this file's claim. -/
def quotientRsCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient.rs",
   "proofs/solidity-verifier/src/lowering/quotient.rs"]

def readQuotientRs : IO String :=
  quotientRsCandidates.foldl (init := pure "") fun acc path =>
    acc >>= fun got => if got != "" then pure got
      else Midfall.Generator.QuotientVmKats.readFileOrEmpty path

def rsLine (src : String) (n : Nat) : String :=
  match (src.splitOn "\n").drop (n - 1) |>.head? with
  | some l => l
  | none => ""

def templateProgramPanicSites_areTheRecordedOnes_ok : IO Bool :=
  readQuotientRs >>= fun src => pure (
        src.length > 60000
     && (src.splitOn "\n").length == 2148
     && (rsLine src 202).contains "quotient_const_offset_words.expect"
     && (rsLine src 202).contains "VK must carry quotient constants"
     && (rsLine src 204).contains "quotient_program_offset_words.expect"
     && (rsLine src 204).contains "VK must carry quotient program"
     && (rsLine src 205).contains "assert!"
     && (rsLine src 207).contains "quotient const table exceeded VK payload reservation"
     && (rsLine src 209).contains "assert!"
     && (rsLine src 211).contains "quotient program length exceeded VK payload reservation"
     && (rsLine src 523).contains "validate_execution_manifest"
     && (rsLine src 524).contains "quotient execution plan must preserve the identity stream"
     && (rsLine src 972).contains "fn quotient_identity_expr"
     && (rsLine src 973).contains "identity.expr.clone()")
#eval templateProgramPanicSites_areTheRecordedOnes_ok -- expect true

/-- A LOCAL COPY of quotientProgramPlan whose inline count is a parameter, so the card's
    falsifier can run without editing the port. At the fixture both native flags are true and
    the trash tail is structured, so the permutation/lookup/trash items do not depend on the
    inline count and only the gate-item prefix changes - which is exactly why the copy is short.
    planWithInlineAt_reproducesThePort_ok is what says the copy is a copy. -/
def planWithInlineAt (n : Nat) : Except Fault QuotientProgramPlan := do
  let pp <- probe
  let parts := pp.parts
  let allIdentities <- Except.ok parts.allIdentities
  let selectorFold <- liftQVM (selectorFoldPlan allIdentities parts.sortedSimple.length)
  let inlineCount := min parts.gates.length n
  let remaining := parts.gates.drop inlineCount
  let nativeIdx <- liftQVM (nativeGateIndices remaining)
  let selected := remaining.zipIdx.filter (fun q => nativeIdx.contains q.2)
  let nativeIndexByGate : List (Nat × Nat) := selected.zipIdx.map (fun q => (q.1.2, q.2))
  let gateItems := remaining.zipIdx.map fun q =>
    match nativeIndexByGate.lookup q.2 with
    | some k => QuotientProgramItem.nativeIdentity k
    | none => QuotientProgramItem.identity q.1
  pure { pp.plan with
    inlineIdentities := parts.gates.take inlineCount
    items := gateItems ++ [QuotientProgramItem.nativePermutation,
      QuotientProgramItem.nativeLookup]
    nativeIdentities := selected.map (fun q => q.1)
    selectorFold := selectorFold }

/-- GATE 12 (THE CARD'S FALSIFIER, both halves). First the copy is checked against the port at
    the real constant - otherwise the falsifier would be testing a different function. Then the
    card's perturbation: DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES := 3 gives one more gate item
    and one fewer inline identity, and the emitted bytecode MUST change. If it did not, the
    inline/native split would be decoration and gate 3 would be proving nothing about it. -/
def quotientPlan_inlineCountFalsifier_ok : Bool := atFixture fun pp =>
  match planWithInlineAt defaultHybridQuotientInlineIdentities with
  | .error _ => false
  | .ok same =>
    same.items == pp.plan.items && same.inlineIdentities == pp.plan.inlineIdentities
      && defaultHybridQuotientInlineIdentities == 4
      &&
    match planWithInlineAt 3 >>= fun q =>
      buildQuotientProgramItems q.items q.selectorFold with
    | .error _ => false
    | .ok b => bytesToNats b.bytes != bytesToNats pp.build.bytes
        && b.bytes.size != pp.build.bytes.size
#eval quotientPlan_inlineCountFalsifier_ok -- expect true

/-- GATE 13: the Debug renderers the manifest's error message uses. Pinned against the Rust's
    derive-Debug shape (variant name, brace, field: value, strings quoted) so a message this port
    reports is the message the reference would report. -/
def showSourceDebug_shapes_ok : Bool :=
  showTargetDebug QuotientTarget.main == "Main"
    && showTargetDebug (QuotientTarget.selector 3) == "Selector(3)"
    && showSourceDebug (QuotientIdentitySource.permutation 2) ==
      "Permutation { identity_index: 2 }"
    && showSourceDebug (QuotientIdentitySource.trash 1 "t") ==
      "Trash { trash_index: 1, trash_name: \"t\" }"
    && showSourceDebug (QuotientIdentitySource.lookup 0 4 "lk") ==
      "Lookup { identity_index: 0, lookup_index: 4, lookup_name: \"lk\" }"
    && showSourceDebug (QuotientIdentitySource.gate 1 "g" 2 "c" 3) ==
      "Gate { gate_index: 1, gate_name: \"g\", constraint_index: 2, constraint_name: \"c\", polynomial_index: 3 }"
#eval showSourceDebug_shapes_ok -- expect true

/-- GATE 14: the two Err messages of validate_execution_manifest, fired. A validator that never
    rejects is a comment. The length arm drops one identity; the position arm swaps the first
    two, which is the exact fault the check exists for. Both messages are the Rust's format!
    text, so this gate is also the pin that says the Err payloads survived the port (header). -/
def validateExecutionManifest_rejects_ok : Bool := atFixture fun pp =>
  let all := pp.parts.allIdentities
  let swapped : List QuotientIdentity :=
    match all with
    | a :: b :: rest => b :: a :: rest
    | _ => all
  match validateExecutionManifest pp.plan (all.drop 1),
        validateExecutionManifest pp.plan swapped with
  | .error m1, .error m2 =>
      m1 == "quotient execution manifest length mismatch: got 22, expected 21"
        && (m2.startsWith
          "quotient execution manifest mismatch at position 0: got index 0, source ")
  | _, _ => false
#eval validateExecutionManifest_rejects_ok -- expect true

end Midfall.Instances.PlanNewKats

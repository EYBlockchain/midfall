-- |
-- Midfall.Instances.GeneratedKats
--
-- OBJ.7 (PLAN-V3, V3 row 41): THE GATES FOR THE GENERATOR RUN END TO END.
--
-- What is under test is Midfall.Generator.PlanNew.newFromVk + compactBlocksOf and
-- Midfall.LoweringV2.Generated.generateAll: the port of plan.rs:235-329, plan.rs:391-406 and
-- the ART:77-341 + ART:337-339 seam. Every gate says WHICH RUST ARTIFACT it is pinned to, and
-- where no Rust artifact exists it says so out loud instead of implying a fixation it does
-- not have. The sources, named once:
--
--   (S1) Halo2VerifyingKey.sol - the VK payload the Rust generator wrote (tracked, 26,018
--        bytes), parsed by vkModelFromArtifact into poseidonVkGen and reservation-filled by
--        OBJ.6's vkFilled. This is what vkCarriesBuild checks the lowered build against.
--   (S2) Halo2Verifier.sol - the deployed verifier (tracked, 175,908 bytes / 3,024 lines).
--        Read four ways here: as TEXT (gate 4), through the artifact readers solConstant /
--        solPinnedProofLen / solPinnedNumInstances (gate 2), through quotientDeployedProgram
--        (gate 7) and through the block slicer poseidonQBlocks (gate 8).
--   (S3) fixtures/conformance/poseidon/cs.json - the F.1 export of the live ConstraintSystem,
--        i.e. poseidonVkExec.cs, the constraint system generateAll is handed.
--   (S4) the Rust SOURCES - plan.rs, vk.rs, artifacts.rs, quotient.rs - read at #eval time by
--        gate 12, which is what pins every site string this card fires.
--
-- THREE GATES HAVE NO DIRECT RUST WITNESS and say so in place: gate 1 (a Lean signature
-- refactor has no Rust counterpart), gate 5's pass half and gate 13's pass half (both
-- validators print nothing on success; the artifact's existence is the indirect evidence).
-- Everything else is compared against S1-S4.
--
-- THE FAULT-STRING CONVENTION, as decided on this card: path:line PLUS the Rust's message,
-- the siteQ form (QuotientBlocks.lean:144-148), extended to plan.rs / vk.rs / artifacts.rs by
-- sitePlan / siteVk / siteArt. Gates 10 and 11 assert the FULL fired string, so the
-- convention is pinned and not just claimed. Gates 10/11 also record the two places where
-- the card's predicted string is not what fires: the card says "PANIC vk.rs:457" (the site is
-- right, the message is additional) and "PANIC quotient.rs:204" (the site is :202 - the
-- constant offset aborts before the program offset, exactly as OBJ.6's handoff warned).
--
-- native_decide lives nowhere in this file (D-P17). Every gate is a #eval Bool or IO Bool so
-- kat_gate.py reports the value that moved.

import Midfall.Instances.PlanNewKats
import Midfall.LoweringV2.Generated

set_option autoImplicit false

namespace Midfall.Instances.GeneratedKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances
open Midfall.Instances.PlanNewKats Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.Generator.ContractKats Midfall.Generator.VerifierPartialKats
open Midfall.Generator.EvmKats Midfall.Generator.QuotientFold Midfall.Generator.PlanNew
open Midfall.Generator.QuotientCertify Midfall.LoweringV2

/-- The fixture's DELTA, from OBJ.6's gate 1 (pinned there against fq.rs:492). -/
def delta : Fr Yul.blsR := frDelta

/-- S1 plus the four reservation fields (OBJ.6's vkFilled). -/
def payload : Except Fault Halo2VerifyingKey := vkFilled

/-- THE GENERATOR RUN at the fixture: Features.solidity, the verifier's own constraint system
    (S3), the config, the payload, the artifact build inputs, the render flags. -/
def genAt (d : Fr Yul.blsR) (f : Halo2VerifyingKey -> Halo2VerifyingKey) : Except Fault GenOut :=
  payload >>= fun v =>
    generateAll Features.solidity d poseidonVkExec poseidonConfig (f v) poseidonInputs
      poseidonFlags

def gen : Except Fault GenOut := genAt delta id

def atGen (f : GenOut -> Bool) : Bool :=
  match gen with | .ok o => f o | .error _ => false

/-- The whole contract text the generator's model renders - the same call
    poseidonRender_bytesExact_ok makes, on the DERIVED model instead of the typed-in one. -/
def textOf (o : GenOut) : String :=
  renderHalo2Verifier (rootCtxOfVerifier o.model) (partsOf o.model)

def diffCount (a b : String) : Nat :=
  let ls := (a.splitOn "\n").zip (b.splitOn "\n")
  (ls.filter fun q => q.1 != q.2).length

def diffLines (a b : String) : List (String × String) :=
  let ls := (a.splitOn "\n").zip (b.splitOn "\n")
  ls.filterMap fun q => if q.1 == q.2 then none else some (q.1, q.2)

/-- A run's outcome as text, so a falsifier gate can name the site it expects. -/
def outcomeOf {A : Type} (x : Except Fault A) : String :=
  match x with
  | .ok _ => "ok"
  | .error (Fault.panic s) => "PANIC " ++ s
  | .error _ => "ERR"

def qOf (o : GenOut) : Option PlannedQuotient :=
  match o.plan.vmQuotient with | .ok q => some q | .error _ => none

/-- One payload word bumped by 1, the perturbation gates 9 and 10 share. Index 33 is the
    first quotient_program word; index 4 is omega, a header word. -/
def bumpWord (i : Nat) (v : Halo2VerifyingKey) : Halo2VerifyingKey :=
  { v with constants := (v.constants.zipIdx).map fun q =>
      if q.2 == i then (q.1.1, q.1.2 + 1) else q.1 }

/-! ## GATE 1 - the OBJ.7 receiver refactor: the four &self wrappers still mean the cores.

    NO DIRECT RUST WITNESS, AND IT WOULD BE WRONG TO WANT ONE. This gate is about a Lean
    signature change (card Do 1): the four Vk.lean defs now take (meta, numInstances) and the
    VerifierBuildInputs form is kept as a wrapper. The reference has no such split - they are
    methods on &self - so the honest claim is the one made here: wrapper and core return the
    same values at the fixture, i.e. the refactor preserved the computation. What the
    REFACTORED forms are pinned against is every other gate in this file and OBJ.6's, all of
    which run through them and against S1/S2/S3. The two numbers the gate also fixes are the
    static working size BEFORE convergence (10400) and the converged vk_mptr (10496): the
    loop of VK:537-544 moves the first into the second, and pinning both says the wrapper and
    the core agree about a loop that actually iterated. -/
def vkReceiverRefactor_wrapperEqualsCore_ok : Bool :=
  match payload with
  | .error _ => false
  | .ok vk =>
    let m := inputsB.meta_
    let n := inputsB.numInstances
    let sameMem (x y : VerifierMemoryLayout) : Bool :=
      x.quotientStackMptr == y.quotientStackMptr && x.quotientStackHi == y.quotientStackHi
        && x.quotientTmpMptr == y.quotientTmpMptr && x.lagrangeDenomsMptr == y.lagrangeDenomsMptr
        && x.accMsmScratch == y.accMsmScratch && x.traceU256Mptr == y.traceU256Mptr
        && x.pcsQEvalSourceTableMptr == y.pcsQEvalSourceTableMptr
    (match staticWorkingMemorySizeForInputs inputsB m,
          staticWorkingMemorySizeForMeta m n with
     | .ok a, .ok b => a == b && a == 10400
     | _, _ => false)
      && (match memoryLayoutForInputs envB inputsB m vk poseidonVkMptr
                verifierMemoryLayoutConfigDefault,
              memoryLayoutFor envB m n vk poseidonVkMptr verifierMemoryLayoutConfigDefault with
     | .ok x, .ok y => sameMem x y
     | _, _ => false)
      && (match metaDataForVkInputs Features.solidity envB inputsB vk poseidonVkMptr,
                metaDataForVk Features.solidity envB m n vk poseidonVkMptr with
     | .ok (mx, dx, vx), .ok (my, dy, vy) =>
          mx == my && pn dx.challengeMptr == pn dy.challengeMptr && sameMem vx vy
     | _, _ => false)
      && (match metaDataForStableStaticLayoutInputs Features.solidity envB inputsB vk,
                metaDataForStableStaticLayout Features.solidity envB m n vk with
     | .ok (px, mx, dx, vx), .ok (py, my, dy, vy) =>
          pn px == pn py && pn px == 10496 && mx == my
            && pn dx.challengeMptr == pn dy.challengeMptr && sameMem vx vy
     | _, _ => false)
#eval vkReceiverRefactor_wrapperEqualsCore_ok -- expect true

/-! ## GATE 2 (S2). The plan's addresses and proof shape ARE the deployed contract's.
    VK_MPTR, the PROOF_LEN check and the instance count are read out of Halo2Verifier.sol by
    the artifact readers at Evm.lean:228-252 - not pasted. sorted_simple's LENGTH is the
    artifact's own selector-bucket count (gate 7 pins numSelectorBuckets = 4 against S2); the
    column indices themselves come from S3, and NO Rust artifact prints [13, 14, 15, 17] -
    stated because it is the one field of this gate the contract cannot confirm. -/
def generateAll_planFields_matchesArtifact_ok : Bool := atGen fun o =>
  solConstant poseidonVerifierDump "VK_MPTR" == some (pn o.plan.vkMptr)
    && solPinnedProofLen poseidonVerifierDump == some o.plan.proofLayout.proofLen
    && solPinnedNumInstances poseidonVerifierDump == some poseidonConfig.numInstances
    && pn o.plan.vkMptr == 10496 && o.plan.proofLayout.proofLen == 4320
    && o.plan.sortedSimple == [13, 14, 15, 17]
    && o.plan.sortedSimple.length == o.plan.meta_.numSimpleSelectors
    && o.plan.proofLayout.proofEnd == o.plan.proofLayout.proofCptr + 4320
#eval generateAll_planFields_matchesArtifact_ok -- expect true

/-! ## GATE 3 (S2). The meta the plan carries is the CONVERGED one, not the raw one - the
    REVIEW-V3 A-1 finding, pinned to the artifact instead of argued. The raw
    ConstraintSystemMeta.new (BAPI:64) has num_point_sets = 0; the plan's has 3; and the
    deployed contract's PROOF_LEN check says 4320, which is what from_protocol yields only
    with 3 point sets - with 0 it is 4224, computed here rather than asserted. So the
    artifact itself refutes frozen clause 1's equation of the plan's meta with the raw new. -/
def generateAll_metaIsConverged_ok : Bool :=
  match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs
        poseidonConfig.numCommittedInstances, gen with
  | .ok raw, .ok o =>
      raw.numPointSets == 0 && raw.numDummyEvals == 0
        && o.plan.meta_.numPointSets == 3 && o.plan.meta_.numEvals == 48
        && o.plan.meta_ != raw
        && (match ProofCalldataLayout.fromProtocol raw.protocol abiVerifyProofProofCptr
                raw.numEvals raw.numPointSets with
           | .ok l => l.proofLen == 4224 && l.proofLen != o.plan.proofLayout.proofLen
           | .error _ => false)
        && (match ProofCalldataLayout.fromProtocol o.plan.meta_.protocol
                abiVerifyProofProofCptr o.plan.meta_.numEvals o.plan.meta_.numPointSets with
           | .ok l => l.proofLen == 4320
           | .error _ => false)
  | _, _ => false
#eval generateAll_metaIsConverged_ok -- expect true

/-! ## GATE 4 (S2, THE CARD'S HEADLINE). The contract the generator renders IS the deployed
    artifact except for the BUILD_ID line: 175,908 characters against 175,908, 3,024 lines
    against 3,024, exactly one line differing, and the differing pair NAMED - both sides
    carry the BUILD_ID constant, so the one difference is the build stamp and not a line of
    Yul. Nothing is sliced from the artifact: the text is rendered from the model the
    generator built, which is what makes this the gate the card is about. -/
def generateAll_textIsTheArtifactButForBuildId_ok : Bool := atGen fun o =>
  let t := textOf o
  let d := diffLines t poseidonVerifierDump
  diffCount t poseidonVerifierDump == 1
    && t.length == 175908 && poseidonVerifierDump.length == 175908
    && (t.splitOn "\n").length == 3024
    && (poseidonVerifierDump.splitOn "\n").length == 3024
    && d.length == 1
    && (d.all fun q => q.1.contains "BUILD_ID" && q.2.contains "BUILD_ID")
#eval generateAll_textIsTheArtifactButForBuildId_ok -- expect true

/-- Two plans perturbed by ONE field each, so gate 5 can show the invariant checker rejects.
    Top-level defs because Lean's anonymous-structure-update parser will not nest three. -/
def driftProgramLen (q : PlannedQuotient) : PlannedQuotient :=
  { q with program := { q.program with len := q.program.len + 1 } }

def driftConsts (q : PlannedQuotient) : PlannedQuotient :=
  { q with build := { q.build with consts := q.build.consts ++ [1] } }

def planDrifted (o : GenOut) (f : PlannedQuotient -> PlannedQuotient)
    : LoweringPlan Unit Unit :=
  { o.plan with quotient := o.plan.quotient.map f }

/-! ## GATE 5. The generator's own invariant validation passes - AND has teeth.
    NO DIRECT RUST WITNESS for the pass: validate_generator_invariants (PL:413-523) prints
    nothing when it succeeds; the Rust panics on a failure, so the artifact's existence is the
    indirect evidence that the reference's run passed. What this gate adds is the half the
    artifact cannot give: a plan whose program length drifted, or whose const table overruns
    the reservation, is REJECTED with the Rust's own message - so the check is not a no-op
    that returns ok for every plan. -/
def generateAll_invariantsOk_ok : Bool := atGen fun o =>
  (match o.plan.validateGeneratorInvariants with | .ok (.ok ()) => true | _ => false)
    &&
    (match (planDrifted o driftProgramLen).validateGeneratorInvariants with
     | .ok (.error m) => m.startsWith "quotient program length drifted"
     | _ => false)
    &&
    (match (planDrifted o driftConsts).validateGeneratorInvariants with
     | .ok (.error m) => m.startsWith "quotient const table exceeds VK reservation"
     | _ => false)
#eval generateAll_invariantsOk_ok -- expect true

/-- The eleven limb superinstruction opcodes (VmTypes.lean:1060-1096). Listed by name and not
    by a range, because 0x1f is Q_OP_NATIVE_LOOKUP and a range would sweep it in and make the
    claim below false. -/
def limbOpcodes : List Nat :=
  [ qOpAddMulMemMemConstU8, qOpAddMulConstU8MemU16, qOpAddMulMemMem,
    qOpRunAddMulMemMemConstU8, qOpRunAddMulConstU8MemU16, qOpLin7, qOpBilin7Row,
    qOpBilin7Pairwise, qOpPow5, qOpModarith7, qOpAffineSum ]

/-! ## GATE 6 (S1 + S4). The dual-build certification runs, and what it is worth AT THIS
    FIXTURE, STATED PLAINLY. The card's acceptance says "certify OK". It is OK - and the
    honest measurement is that at poseidon the certification is VACUOUS: the baseline build
    (limb superinstructions off, QRS:2114-2146) is BYTE-IDENTICAL to the optimized one,
    because no limb opcode appears in the program the Rust itself emitted - used_ops is
    [0x05,0x06,0x08,0x0b,0x0d,0x10,0x11,0x19,0x1b,0x1f], all ten of them pinned against S2 by
    OBJ.6's gate 4, and none of them is in limbOpcodes. So the two builds agree because they
    are the same program - and the same holds in the Rust, which runs the same flag on the
    same items: this is a property of the fixture and not a port difference, and it is the
    finding this card reports rather than hides. The gate therefore pins three things: the
    certification passes; the two builds are byte-identical WITH the reason (no limb opcode
    in used_ops); and the certification is not a no-op FUNCTION - a baseline built from a
    DIFFERENT item stream (OBJ.6's inline-count copy at 3) is rejected with the Rust's own
    message. The last conjunct is also the pin that the payload carries the optimized build.
    -/
def generateAll_certificationOk_ok : Bool := atGen fun o =>
  match qOf o with
  | none => false
  | some q =>
    let ops := bytesToNats q.build.usedOps
    (match certifyQuotientBuildsAgree q.plan q.build q.build o.plan.vk with
       | .ok () => true | .error _ => false)
      && (match buildQuotientProgramItemsWithLimbOps q.plan.items q.plan.selectorFold false with
           | .ok b => b.bytes == q.build.bytes && b.consts == q.build.consts
               && (ops.any fun x => limbOpcodes.contains x) == false
               && ops.length == 10 && b.bytes.size == 88
           | .error _ => false)
      && (match planWithInlineAt 3 >>= fun p3 =>
                buildQuotientProgramItemsWithLimbOps p3.items p3.selectorFold false with
           | .ok b3 => b3.bytes != q.build.bytes
               && (match certifyQuotientBuildsAgree q.plan q.build b3 o.plan.vk with
                   | .error m => m.startsWith "quotient limb superinstructions changed"
                   | .ok () => false)
           | .error _ => false)
      && vkCarriesBuild o.plan.vk q.build
#eval generateAll_certificationOk_ok -- expect true

/-! ## GATE 7 (S2). The program the CONSTRUCTOR produced is the deployed one, field by field.
    OBJ.6's gate 4 pinned the same twelve fields for the hand-assembled pipeline; this pins
    them for newFromVk's plan, which is the difference between "the pieces are right" and
    "the generator runs". quotientDeployedProgram is read out of Halo2Verifier.sol. The two
    derived pointers (stackMptr, state slots) are compared against the plan's own bundle,
    which is what PL:280-289's destructuring asserts. -/
def newFromVk_programIsTheDeployedOne_ok : Bool := atGen fun o =>
  match qOf o with
  | none => false
  | some q =>
    let a := q.program
    let d := quotientDeployedProgram
    a.len == d.len && a.constMptr == d.constMptr && a.evalNumerMptr == d.evalNumerMptr
      && a.traceIdMptr == d.traceIdMptr && a.selectorPowerMptr == d.selectorPowerMptr
      && a.selectorMaxPower == d.selectorMaxPower && a.stackMptr == d.stackMptr
      && a.programMptr == d.programMptr && a.guards == d.guards
      && ((a.selectorTailUpdates.map fun t => (t.selectorOffset, t.powerOffset))
          == (d.selectorTailUpdates.map fun t => (t.selectorOffset, t.powerOffset)))
      && q.stackMptr == a.stackMptr && q.stateSlots.evalNumerMptr == a.evalNumerMptr
      && a.len == 88 && a.guards.numSelectorBuckets == 4
#eval newFromVk_programIsTheDeployedOne_ok -- expect true

/-! ## GATE 8 (S2). compactBlocksOf reproduces the quotient blocks the artifact carries.
    poseidonQBlocks is the Rust's own Yul sliced out of Halo2Verifier.sol by
    quotientDeployedCtx + poseidonBlocks (PoseidonInputs.lean:105, :111), so every line here
    is Rust output. Five of the six families match EXACTLY. The inline family matches only
    flattened, and the reason is a slicing artefact and not a port bug: the artifact slicer
    cannot see the boundaries between the four inline blocks - they are emitted as one
    contiguous run - so it hands back one list of 99 lines where the port emits four of
    44/20/17/18. The flattened text is identical, which is what the contract contains, and
    gate 4 pins the whole contract anyway. -/
def compactBlocksOf_matchesArtifact_ok : Bool := atGen fun o =>
  let g := o.qblocks
  let a := poseidonQBlocks
  g.postVmComputations == a.postVmComputations
    && g.nativePermutationComputation == a.nativePermutationComputation
    && g.nativeLookupComputation == a.nativeLookupComputation
    && g.nativeIdentityComputations == a.nativeIdentityComputations
    && g.evalNumerComputations == a.evalNumerComputations
    && g.inlineComputations.flatten == a.inlineComputations.flatten
    && (g.inlineComputations.map fun l => l.length) == [44, 20, 17, 18]
    && (a.inlineComputations.map fun l => l.length) == [99]
    && (g.postVmComputations.map fun l => l.length) == [193]
    && g.nativePermutationComputation.length == 82
    && g.nativeLookupComputation.length == 43
    && (g.nativeIdentityComputations.map fun l => l.length) == [37, 37, 37]
#eval compactBlocksOf_matchesArtifact_ok -- expect true

/-! ## GATE 9 (THE CARD'S FIRST FALSIFIER, plus the card's NON-falsifier).
    delta := 2 - the placeholder DELTA of today's poseidonE - still generates a contract, and
    it differs from the artifact in 3 lines and not 1: the two extra are the field-inverse
    code the quotient blocks print DELTA into, which is why the block record itself changed.
    So the delta argument reaches the emitted program - the fact OBJ.8's generated-by clause
    needs (H-7) - and the proof layout is untouched, which says the perturbation is in the
    quotient code and nowhere else. THE NON-FALSIFIER, measured and not argued: flipping the
    payload's OMEGA word is NOT refused - vkCarriesBuild polices the two quotient sections
    and nothing else - and the only trace it leaves is 2 differing lines, BUILD_ID and the
    pinned VK codehash. That is the hole PayloadAgrees exists to close. -/
def deltaTwoIsDifferent : Bool :=
  match genAt (2 : Fr Yul.blsR) id with
  | .ok o => diffCount (textOf o) poseidonVerifierDump == 3 && o.qblocks != poseidonQBlocks
      && o.plan.proofLayout.proofLen == 4320
  | .error _ => false

def omegaFlipIsAcceptedButVisible : Bool :=
  match genAt delta (bumpWord 4) with
  | .ok o =>
    let hits := (diffLines (textOf o) poseidonVerifierDump).filter fun q =>
      (Prod.fst q).contains "EXPECTED_VK_CODEHASH"
    diffCount (textOf o) poseidonVerifierDump == 2 && hits.length == 1
  | .error _ => false

def generateAll_falsifierDeltaAndOmega_ok : Bool :=
  deltaTwoIsDifferent && omegaFlipIsAcceptedButVisible
#eval generateAll_falsifierDeltaAndOmega_ok -- expect true

/-! ## GATE 10 + 11 (THE CARD'S OTHER TWO FALSIFIERS, with the sites named).
    10: flip ONE WORD of the payload's quotient_program section (index 33, the first) and the
    generator refuses at vk.rs:457 - the assert_eq! at VK:456-459, ported as vkCarriesBuild.
    Without that check the run would emit a contract whose VK points at bytecode the plan
    never lowered. 11: hand it the payload AS PARSED (poseidonVkGen, whose four reservation
    fields vkModelFromArtifact leaves empty) and the first abort is the CONSTANT offset at
    quotient.rs:202 - NOT the card's :204, which is the program offset: OBJ.6's handoff
    correction, re-measured here. Both strings carry the message: the fault-string convention
    is siteQ's, path:line PLUS message, and these two gates are where it is pinned. -/
def generateAll_falsifierPayloadWord_ok : Bool :=
  outcomeOf (genAt delta (bumpWord 33)) ==
    "PANIC " ++ siteVk 457 "quotient bytecode changed after VK payload materialization"
#eval generateAll_falsifierPayloadWord_ok -- expect true

def generateAll_falsifierNoReservation_ok : Bool :=
  outcomeOf (generateAll Features.solidity delta poseidonVkExec poseidonConfig poseidonVkGen
    poseidonInputs poseidonFlags) ==
    "PANIC " ++ qrs ++ ":202 (VK must carry quotient constants)"
#eval generateAll_falsifierNoReservation_ok -- expect true

/-! ## GATE 12 (S4). Every site this card fires is the line the Rust actually panics on.
    plan.rs, vk.rs and artifacts.rs are read at #eval time - the pattern OBJ.6's gate 11 sets
    for quotient.rs - so a re-cite reddens a gate instead of drifting. The four new sites:
    PL:310 (the invariant unwrap), PL:326 (the certification unwrap), VK:457 (the bytes
    assert_eq!), ART:339 (the validate_layout unwrap). VK:461 is the consts twin of :457 and
    Vk.lean:1250-1252 already cites both; the convention that file uses is the line holding
    the COMPARED operands, not the macro, and this card follows it rather than inventing a
    second one. The three constructor lines (PL:238, :392, :398) are pinned too, because the
    port's line-by-line claims name them - including the card's own off-by-one: :381-394 is
    quotient_external_frame plus this item's signature head, and the body is :396-406. -/
def readLoweringRs (rel : String) : IO String :=
  Midfall.Generator.EvmKats.readFileOrEmpty
    ("../proofs/solidity-verifier/src/lowering/" ++ rel)

def generatedPanicSites_areTheRecordedOnes_ok : IO Bool := do
  let plan <- readLoweringRs "plan.rs"
  let vk <- readLoweringRs "vk.rs"
  let art <- readLoweringRs "artifacts.rs"
  pure (plan.length > 10000 && vk.length > 10000 && art.length > 5000
    && (rsLine plan 238).contains "meta_data_for_stable_static_layout"
    && (rsLine plan 309).contains "validate_generator_invariants"
    && (rsLine plan 310).contains "generator invariant violation"
    && (rsLine plan 326).contains "quotient dual-build certification failed"
    && (rsLine plan 381).contains "fn quotient_external_frame"
    && (rsLine plan 392).contains "fn compact_quotient_blocks"
    && (rsLine plan 398).contains "compact_quotient_computation_blocks"
    && (rsLine vk 456).contains "assert_eq!"
    && (rsLine vk 457).contains "final_quotient_build.bytes"
    && (rsLine vk 458).contains "quotient bytecode changed after VK payload materialization"
    && (rsLine vk 461).contains "final_quotient_build.consts"
    && (rsLine art 77).contains "fn generate_verifier_from_plan"
    && (rsLine art 338).contains "validate_layout()"
    && (rsLine art 339).contains "invalid generated verifier layout")
#eval generatedPanicSites_areTheRecordedOnes_ok -- expect true

/-! ## GATE 13. The ART:337-339 guard has teeth. The model the generator returns validates
    (the Rust would have panicked otherwise, so the artifact is the indirect witness - NO
    DIRECT RUST WITNESS for the pass, stated: validate_layout prints nothing on success), and
    a model with one drifted length, or a drifted instance pointer, is REJECTED by the same
    validator with the Rust's own message - which is what makes the seam's validate-then-return
    step a check and not a formality. -/
def generateAll_layoutValidate_ok : Bool := atGen fun o =>
  (match Halo2Verifier.validateLayout o.model with | .ok () => true | .error _ => false)
    && o.model.proofLen == 4320
    && (match Halo2Verifier.validateLayout { o.model with proofLen := o.model.proofLen + 1 } with
       | .error m => m.startsWith "proof length mismatch"
       | .ok () => false)
    && (match Halo2Verifier.validateLayout
            { o.model with numInstanceCptr := o.model.numInstanceCptr + 1 } with
       | .error m => m.startsWith "proof calldata layout mismatch"
       | .ok () => false)
#eval generateAll_layoutValidate_ok -- expect true

end Midfall.Instances.GeneratedKats

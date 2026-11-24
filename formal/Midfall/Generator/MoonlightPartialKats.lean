-- |
-- Midfall.Generator.MoonlightPartialKats
--
-- Moonlight artifact-conformance probe: the seven verifier partials rendered at
-- the DEPLOYED Sepolia Moonlight-wrap context and measured against the deployed
-- source of record,
--
--   proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol
--
-- This is a KAT/gate module, not a proof. The deployed source is an OLDER
-- generator artifact (pragma ^0.8.24 although the deployment record says solc
-- 0.8.30, bare `revert(0,0)`/`gas()` spellings, no BUILD_ID, TRANSCRIPT_MPTR =
-- 0x80, accumulator call returning one value), so the current render functions
-- are not expected to be byte-equal to it. The measurements below say exactly
-- which partials occur, where they do not, and how many bytes differ. The
-- expected values are recorded, so a future generator change that accidentally
-- starts matching (or changes the stale-profile shape) reddens the record gate.
--
-- The context is read from the deployed source, not from the tracked IVC
-- fixture: 19 instances, k = 20, accumulator offset 11, 7 x 56-bit limbs, the
-- advice/multiplicity/permutation/lookup/trash/quotient/eval/q_eval/pi proof
-- layout, TRANSCRIPT_MPTR/RETURN_MPTR = 0x80, VK at 0x2700, batch pointer
-- 0x0100, final-pairing scratch 0x0300. The deployment is an EMBEDDED quotient
-- VM with a SEPARATE VK. The embedded VM's QuotientProgram record is not
-- recoverable from the emitted source (its program/constant bytes live in the
-- VK payload), so the quotient partial is measured on its linearization tail
-- with empty helper/numerator arguments; the missing VM inputs are recorded in
-- formal/docs/MOONLIGHT-ARTIFACT.md. The deployed VK runtime header and the
-- verifier runtime's embedded VK address/codehash are cross-checked as well, so
-- the context is tied to the fetched-back bytecode and not only to the source.
import Midfall.Generator.VerifierPartials
set_option autoImplicit false
open Midfall.Generator Midfall.Generator.VerifierPartialKats

namespace Midfall.Generator.MoonlightPartialKats

/-! ## The deployed source of record -/

/-- The checked-in deployed Moonlight-wrap verifier source. A missing file is a
    red gate, not a silent pass: every occurrence count below is then 0. -/
def moonlightDumpCandidates : List String :=
  ["../proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol",
   "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol"]

def readMoonlightDump : IO String := EvmKats.readFirst moonlightDumpCandidates

/-- The fetched-back deployed VK runtime (`INVALID || payload`), for the header
    cross-check below. -/
def moonlightVkRuntimeCandidates : List String :=
  ["../proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2VerifyingKey.runtime.bytecode.hex",
   "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2VerifyingKey.runtime.bytecode.hex"]

def readMoonlightVkRuntime : IO String := EvmKats.readFirst moonlightVkRuntimeCandidates

/-- The fetched-back deployed verifier runtime, for the deployment tie below. -/
def moonlightVerifierRuntimeCandidates : List String :=
  ["../proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.runtime.bytecode.hex",
   "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.runtime.bytecode.hex"]

def readMoonlightVerifierRuntime : IO String := EvmKats.readFirst moonlightVerifierRuntimeCandidates

/-! ## A minimal hex reader for the deployed VK runtime header -/

private def hexNibble (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

private def hexChars (s : String) : List Char :=
  let cs := s.toList.filter (fun c => c != '\n' && c != '\r' && c != ' ')
  match cs with
  | '0' :: 'x' :: rest => rest
  | _ => cs

private def hexAt (chars : List Char) (start width : Nat) : Nat :=
  ((chars.drop start).take width).foldl (fun acc c => acc * 16 + hexNibble c) 0

private def hexByte (chars : List Char) (off : Nat) : Nat :=
  hexAt chars (2 * off) 2

/-- Payload word `n`, counting from byte 1 of runtime (the `INVALID` prefix is
    byte 0), as the VK header source lays them out. -/
private def hexPayloadWord (chars : List Char) (n : Nat) : Nat :=
  hexAt chars (2 * (1 + 32 * n)) 64

/-! ## Deployed constant transcription -/

/-- The deployed proof layout, read from the parser's own `add(proof_cptr, 0x..)`
    lines (D:1074-1310). It tiles exactly to NUM_INSTANCE_CPTR = 0x1ec4:
    advice 15 G1, lookup multiplicities 2 G1, permutation Z 6 G1, two lookups
    of 1 helper + 1 accumulator each, 1 trashcan, 4 quotient limbs, 102 eval
    words, 1 f_com, 5 q_eval words, 1 pi. proofLen = 0x1ec4 - 0x64 = 0x1e60. -/
def moonlightProofLayout : ProofCalldataLayout :=
  { proofCptr := 0x64
    advicePhases := [ProofSection.new 0x64 15 g1Bytes]
    lookupMultiplicities := ProofSection.new 0x7e4 2 g1Bytes
    permutationProducts := ProofSection.new 0x8e4 6 g1Bytes
    lookups := [ { lookup := 0, helpers := ProofSection.new 0xbe4 1 g1Bytes,
                   accumulator := ProofSection.new 0xc64 1 g1Bytes },
                 { lookup := 1, helpers := ProofSection.new 0xce4 1 g1Bytes,
                   accumulator := ProofSection.new 0xd64 1 g1Bytes } ]
    trash := ProofSection.new 0xde4 1 g1Bytes
    quotientLimbs := ProofSection.new 0xe64 4 g1Bytes
    evals := ProofSection.new 0x1064 102 wordBytes
    fCom := ProofSection.new 0x1d24 1 g1Bytes
    qEvals := ProofSection.new 0x1da4 5 wordBytes
    pi := ProofSection.new 0x1e44 1 g1Bytes
    quotientCommCptr := 0xe64
    evalCptr := 0x1064
    wCptr := 0x1d24
    qEvalCptr := 0x1da4
    proofEnd := 0x1ec4
    proofLen := 0x1e60 }

/-- The deployed verifier memory layout: every slot the contract's constant
    block names (D:58-166), plus the two scratch addresses the deployed partials
    use literally (`ec_pairing` at 0x0300, the batch pointer at 0x0100). The
    PCS/quotient-VM scratch capacities are NOT observable as named constants in
    the emitted source; they stay at their Lean defaults here and are inert for
    the seven partial renders below (they feed Constants.sol/PrecompileSmoke).
    Reconstructing them is part of the blocked full-render path. -/
def moonlightMemoryLayout : VerifierMemoryLayout :=
  { poseidonMemoryLayout with
    transcriptMptr := 0x80
    verifierReturnMptr := 0x80
    quotientReturnMptr := 0x80
    constructorSmokeScratchMptr := 0x80
    constructorG1msmSmokeScratchMptr := 0xa1c0
    constructorG1msmSmokeInputBytes := 0x30c0
    pcsPairingScratchMptr := 0x0300
    vkMptr := ptrMemory (valueFromNat 0x2700)
    scalarInvScratchMptr := 0x2600
    challengeMptr := ptrMemory (valueFromNat 0x6980)
    thetaMptr := ptrMemory (valueFromNat 0x6980)
    betaMptr := ptrMemory (valueFromNat 0x69a0)
    gammaMptr := ptrMemory (valueFromNat 0x69c0)
    trashChallengeMptr := ptrMemory (valueFromNat 0x69e0)
    yMptr := ptrMemory (valueFromNat 0x6a00)
    xMptr := ptrMemory (valueFromNat 0x6a20)
    x1Mptr := ptrMemory (valueFromNat 0x6a40)
    x2Mptr := ptrMemory (valueFromNat 0x6a60)
    x3Mptr := ptrMemory (valueFromNat 0x6a80)
    x4Mptr := ptrMemory (valueFromNat 0x6aa0)
    fComMptr := ptrMemory (valueFromNat 0x6ac0)
    piMptr := ptrMemory (valueFromNat 0x6b40)
    accLhsMptr := ptrMemory (valueFromNat 0x6bc0)
    accRhsMptr := ptrMemory (valueFromNat 0x6c40)
    xNMptr := ptrMemory (valueFromNat 0x6cc0)
    xNMinus1InvMptr := ptrMemory (valueFromNat 0x6ce0)
    lLastMptr := ptrMemory (valueFromNat 0x6d00)
    lBlindMptr := ptrMemory (valueFromNat 0x6d20)
    l0Mptr := ptrMemory (valueFromNat 0x6d40)
    instanceEvalMptr := ptrMemory (valueFromNat 0x6d60)
    quotientEvalMptr := ptrMemory (valueFromNat 0x6d80)
    quotientMptr := ptrMemory (valueFromNat 0x6da0)
    fEvalMptr := ptrMemory (valueFromNat 0x6e40)
    vMptr := ptrMemory (valueFromNat 0x6e60)
    finalComMptr := ptrMemory (valueFromNat 0x6e80)
    pairingLhsMptr := ptrMemory (valueFromNat 0x6f00)
    pairingRhsMptr := ptrMemory (valueFromNat 0x6f80)
    rotPointsMptr := ptrMemory (valueFromNat 0x7000)
    x1PowersMptr := ptrMemory (valueFromNat 0x7380)
    qComMptr := ptrMemory (valueFromNat 0x7ba0)
    qEvalSetMptr := ptrMemory (valueFromNat 0x7ba0)
    qEvalCptrMptr := ptrMemory (valueFromNat 0x82a0)
    g1IdentityMptr := ptrMemory (valueFromNat 0x83a0)
    reversedEvalsMptr := ptrMemory (valueFromNat 0x8500)
    commsMptrBase := ptrMemory (valueFromNat 0x91c0)
    adviceCommsMptrBase := ptrMemory (valueFromNat 0x91c0)
    lookupMCommsMptrBase := ptrMemory (valueFromNat 0x9940)
    permZCommsMptrBase := ptrMemory (valueFromNat 0x9a40)
    lookupHelperCommsMptrBase := ptrMemory (valueFromNat 0x9d40)
    lookupZCommsMptrBase := ptrMemory (valueFromNat 0x9e40)
    trashcanCommsMptrBase := ptrMemory (valueFromNat 0x9f40)
    quotientLimbCommsMptrBase := ptrMemory (valueFromNat 0x9fc0)
    selectorAccMptr := 0xa1c0
    batchInvertScratchMptr := 0xa1c0
    lagrangeDenomsMptr := 0x6cc0
    accMsmScratch := 0xa1c0
    accumulatorPairingBatchMptr := 0x0100
    finalPairingScratchMptr := 0x0300
    traceU256Mptr := 0xd3c0 }

/-- The MoonlightPartialCtx: the deployed Sepolia Moonlight-wrap constants. The
    profile is a 19-instance/k=20 wrap key with a public accumulator at instance
    offset 11 (7 x 56-bit limbs, no carried scalars, no fixed-base tail), an
    external VK (`embeddedVk = none`) and an embedded quotient VM (no
    `expectedQuotientCodehash`, no external evaluator). `quotientProgram` stays
    none because its program/constant table lives in the VK payload, not in the
    emitted source; only the linearization tail of the quotient partial is
    renderable from this context.

    `templateConstants` stays at the current generator's Rust default. It is the
    generator's fixed protocol-constant set, not a deployed-context knob: the
    deployed artifact's pre-I-7 batch offsets and 0x0220 hash length are a
    generator-version difference, recorded by the FinalPairing diff, not an
    input this record can select. -/
def MoonlightPartialCtx : PartialCtx :=
  { poseidonCtx with
    vkMptr := 0x2700
    scalarInvScratchMptr := 0x2600
    finalPairingScratchMptr := 0x0300
    accumulatorPairingBatchMptr := 0x0100
    expectedHasAccumulator := true
    expectedHasAccumulatorWord := 1
    expectedAccOffset := 11
    expectedNumAccLimbs := 7
    expectedNumAccLimbBits := 56
    expectedAccHasCarriedScalars := false
    accFixedBases := []
    accMsmScratch := 0xa1c0
    expectedQuotientCodehash := none
    quotientExternal := none
    quotientDirect := none
    quotientProgram := none
    quotientInlineComputations := []
    quotientEvalNumerComputations := []
    quotientPostVmComputations := []
    quotientNativePermutationComputation := []
    quotientNativeLookupComputation := []
    quotientNativeIdentityComputations := []
    quotientIdentityTraceBase := 0
    quotientPow5Helper := true
    quotientLimb7Helper := false
    quotientWideLimb7Helper := false
    limb7YulCoeffs := []
    wideLimb7YulCoeffs := []
    k := 20
    numInstances := 19
    numNegLagranges := 10
    numQuotients := 4
    proofLen := 0x1e60
    simpleSelectorCols := List.range 10
    fixedCommMptr := 0x5a00
    userPhases := [{ adviceBytes := 0x780, numChallenges := 0, challengeOffset := 0 }]
    proofLayout := moonlightProofLayout
    numLookups := 2
    numPermutationZs := 6
    lookupHPlusAcc := 4
    numTrashcans := 1
    truncatedChallenges := true
    proofCommitTraceBase := 0
    proofEvalTraceBase := 0
    memory := moonlightMemoryLayout
    vkLen := 17024
    expectedVkCodehash := some 0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009
    buildId := 0
    constructorG1msmSmokeGas := 0
    constructorG1msmSmokeInputBytes := 0x30c0
    accRhsMsmGas := 0
    expectedQuotientLen := none
    proofCptr := ptrCalldata (valueFromNat 0x64)
    numInstanceCptr := 0x1ec4
    instanceCptr := 0x1ee4
    selectorTraceBase := 0 }

/-- Short alias used by the measurement definitions. -/
abbrev moonlightCtx : PartialCtx := MoonlightPartialCtx

/-! ## Measurements -/

/-- One partial's measured status against the deployed source. `occurrences` is
    `occ` from VerifierPartials; `includeBoundary` is the same two-sided
    include check the F1/F2 gates use; `renderBytes` is the current-generator
    render length at `moonlightCtx`. -/
structure MoonlightPartialMeasurement where
  partialName : String
  renderBytes : Nat
  occurrences : Nat
  includeBoundary : Bool
  deriving Repr, BEq

def measureMoonlight (sol render : String) (name : String) : MoonlightPartialMeasurement :=
  { partialName := name
    renderBytes := render.utf8ByteSize
    occurrences := occ sol render
    includeBoundary := includeBoundary sol render }

def moonlight_assemblyHelpers : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderAssemblyHelpers moonlightCtx) "AssemblyHelpers")

def moonlight_accumulatorHelpers : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderAccumulatorHelpers moonlightCtx) "AccumulatorHelpers")

def moonlight_vkLoading : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderVkLoading moonlightCtx) "VkLoading")

def moonlight_transcriptProofParser : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderTranscriptProofParser moonlightCtx) "TranscriptProofParser")

def moonlight_lagrange : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderLagrange moonlightCtx) "Lagrange")

/-- The quotient partial's own bytes at the embedded-VM profile are its
    linearization tail; the VM helpers/numerator are passed in by the caller in
    the current generator and cannot be reconstructed without `quotientProgram`.
    Empty arguments isolate the tail, which is what is measurable from the
    deployed source alone. -/
def moonlight_quotientLinearization : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderQuotientAndLinearization moonlightCtx "" "") "QuotientAndLinearization(linearization tail)")

def moonlight_finalPairing : IO MoonlightPartialMeasurement :=
  readMoonlightDump >>= fun sol =>
  pure (measureMoonlight sol (renderFinalPairing moonlightCtx) "FinalPairing")

def moonlightMeasurements : IO (List MoonlightPartialMeasurement) :=
  readMoonlightDump >>= fun sol =>
  pure
    [ measureMoonlight sol (renderAssemblyHelpers moonlightCtx) "AssemblyHelpers"
    , measureMoonlight sol (renderAccumulatorHelpers moonlightCtx) "AccumulatorHelpers"
    , measureMoonlight sol (renderVkLoading moonlightCtx) "VkLoading"
    , measureMoonlight sol (renderTranscriptProofParser moonlightCtx) "TranscriptProofParser"
    , measureMoonlight sol (renderLagrange moonlightCtx) "Lagrange"
    , measureMoonlight sol (renderQuotientAndLinearization moonlightCtx "" "") "QuotientAndLinearization(linearization tail)"
    , measureMoonlight sol (renderFinalPairing moonlightCtx) "FinalPairing" ]

/-! ## Gates -/

/-- The context numbers are read from the deployed source, not copied from the
    F2/IVC fixture. This is the anchor that makes the measurements below a
    statement about Moonlight: 19/20/11/7/56, the 0x80 transcript/return roots,
    the 0x1e60 proof length, the 0x1ec4 instance cursor, the 0x0780 advice phase,
    and the pinned VK runtime length/codehash. -/
def moonlight_ctx_readFromSource_ok : IO Bool :=
  readMoonlightDump >>= fun sol =>
  pure (sol.contains "eq(mload(NUM_INSTANCES_MPTR), 19)"
    && sol.contains "eq(mload(K_MPTR), 20)"
    && sol.contains "eq(mload(HAS_ACCUMULATOR_MPTR), 1)"
    && sol.contains "eq(mload(ACC_OFFSET_MPTR), 11)"
    && sol.contains "eq(mload(NUM_ACC_LIMBS_MPTR), 7)"
    && sol.contains "eq(mload(NUM_ACC_LIMB_BITS_MPTR), 56)"
    && sol.contains "TRANSCRIPT_MPTR = 0x80;"
    && sol.contains "RETURN_MPTR = 0x80;"
    && sol.contains "eq(0x1e60, calldataload(PROOF_LEN_CPTR))"
    && sol.contains "NUM_INSTANCE_CPTR = 0x1ec4;"
    && sol.contains "INSTANCE_CPTR = 0x1ee4;"
    && sol.contains "add(proof_cptr, 0x0780)"
    && sol.contains "add(proof_cptr, 0x0100)"
    && sol.contains "add(proof_cptr, 0x0300)"
    && sol.contains "add(proof_cptr, 0x0200)"
    && sol.contains "add(proof_cptr, 0x0cc0)"
    && sol.contains "add(proof_cptr, 0xa0)"
    && sol.contains "// lookup 0: 1 helper(s) + 1 acc"
    && sol.contains "// lookup 1: 1 helper(s) + 1 acc"
    && sol.contains "// ---- trashcans ----"
    && sol.contains "add(mptr, 0x03a0)"
    && sol.contains "add(X_N_MPTR, 0x0140)"
    && sol.contains "add(instance_cptr, 0x0260)"
    && sol.contains "add(INSTANCE_CPTR, 0x0160)"
    && sol.contains "let acc_scratch := 0xa1c0"
    && sol.contains "Already-collapsed point-pair layout: carried scalars are"
    && sol.contains "there is no fixed-base scalar"
    && sol.contains "let batch_ptr := 0x0100"
    && sol.contains "let p := 0x2600"
    && sol.contains "function ec_pairing(success, lhs_mptr, rhs_mptr) -> ret"
    && sol.contains "let scratch := 0x0300"
    && sol.contains "mcopy(scratch,              lhs_mptr,                 0x80)"
    && sol.contains "VK_MPTR = 0x2700;"
    && sol.contains "add(SELECTOR_ACC_MPTR, 0x120)"
    && sol.contains "mcopy(0xbf20, 0x5a00, 0x80)"
    && sol.contains "EXPECTED_VK_PAYLOAD_LENGTH = 17024;"
    && sol.contains "EXPECTED_VK_LENGTH = 17025;"
    && sol.contains "EXPECTED_VK_CODEHASH_WORD = 0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009;")

/-- The deployed VK runtime really carries the header this context transcribes:
    17025 bytes, leading INVALID byte, and payload words 0..10 matching the
    source's `mstore` lines. This is the payload-side tie, independent of the
    verifier source's own constants. -/
def moonlight_vkPayloadHeader_ok : IO Bool :=
  readMoonlightVkRuntime >>= fun hex =>
  let chars := hexChars hex
  pure (chars.length == 2 * 17025
    && hexByte chars 0 == 0xfe
    && hexPayloadWord chars 0 == 0x56c0824fcff237dd8dc7b15f527346d9e1647d191815acb142500b0293e84f66
    && hexPayloadWord chars 1 == 19
    && hexPayloadWord chars 2 == 20
    && hexPayloadWord chars 7 == 1
    && hexPayloadWord chars 8 == 11
    && hexPayloadWord chars 9 == 7
    && hexPayloadWord chars 10 == 56)

/-- The deployed verifier runtime is the fetched-back 21161-byte artifact and
    pins the deployed VK address, VK runtime codehash word, and batch domain tag
    that the source/context name. This is the runtime-side tie for the source
    measurements. -/
def moonlight_deployedRuntime_ok : IO Bool :=
  readMoonlightVerifierRuntime >>= fun hex =>
  let chars := hexChars hex
  pure (chars.length == 2 * 21161
    && hexByte chars 0 == 0x61
    && hex.contains "80b32f68a333df55da60bec44c498477a8311ede"
    && hex.contains "24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009"
    && hex.contains "70616972696e672d62617463682d6163632d6b7a67")

/-- The measured status of the seven renders, pinned as a KAT. The deployed
    source is a stale-generator artifact, so every current render is expected to
    miss; the recorded occurrence counts and byte lengths make the miss
    checkable rather than a claim. A generator/template change that alters the
    numbers reddens this gate. -/
def moonlight_recordedStatus_ok : IO Bool :=
  moonlightMeasurements >>= fun ms =>
  pure (ms ==
    [ { partialName := "AssemblyHelpers", renderBytes := 16226, occurrences := 0, includeBoundary := false }
    , { partialName := "AccumulatorHelpers", renderBytes := 17009, occurrences := 0, includeBoundary := false }
    , { partialName := "VkLoading", renderBytes := 5821, occurrences := 0, includeBoundary := false }
    , { partialName := "TranscriptProofParser", renderBytes := 17968, occurrences := 0, includeBoundary := false }
    , { partialName := "Lagrange", renderBytes := 4745, occurrences := 0, includeBoundary := false }
    , { partialName := "QuotientAndLinearization(linearization tail)", renderBytes := 1901, occurrences := 1, includeBoundary := false }
    , { partialName := "FinalPairing", renderBytes := 4221, occurrences := 0, includeBoundary := false } ])

end Midfall.Generator.MoonlightPartialKats

#eval Midfall.Generator.MoonlightPartialKats.moonlight_ctx_readFromSource_ok -- expect true
#eval Midfall.Generator.MoonlightPartialKats.moonlight_assemblyHelpers
#eval Midfall.Generator.MoonlightPartialKats.moonlight_accumulatorHelpers
#eval Midfall.Generator.MoonlightPartialKats.moonlight_vkLoading
#eval Midfall.Generator.MoonlightPartialKats.moonlight_transcriptProofParser
#eval Midfall.Generator.MoonlightPartialKats.moonlight_lagrange
#eval Midfall.Generator.MoonlightPartialKats.moonlight_quotientLinearization
#eval Midfall.Generator.MoonlightPartialKats.moonlight_finalPairing
#eval Midfall.Generator.MoonlightPartialKats.moonlight_vkPayloadHeader_ok -- expect true
#eval Midfall.Generator.MoonlightPartialKats.moonlight_deployedRuntime_ok -- expect true
#eval Midfall.Generator.MoonlightPartialKats.moonlight_recordedStatus_ok -- expect true once recorded

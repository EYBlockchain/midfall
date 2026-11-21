-- |
-- Midfall.Generator.IvcPartialKats
--
-- WID.2 (C1 first tranche): the ported verifier partials at an F2-shaped (IVC
-- decider) context. The evidence source is
-- docs/plans/V3-evidence/lean/widening/IvcPartials.lean, a read-only scratch
-- probe that rendered the seven ported partials at a context whose numbers were
-- read by hand from the tracked IVC artifact
-- proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol.
-- This module lands that probe as gates: each render must occur EXACTLY ONCE in
-- the tracked artifact and carry the include boundary, and the F1-context
-- AccumulatorHelpers render must NOT carry the boundary (negative control).
--
-- Seven positive gates + one negative control, one per line the evidence probe
-- printed. That probe was run at base 1460013 before this port and printed, in
-- order:
--
--   AssemblyHelpers: len 16223, occ F2 1, includeBoundary F2 true, occ F1 0
--   AccumulatorHelpers: len 17544, occ F2 1, includeBoundary F2 true, occ F1 0
--   VkLoading: len 5820, occ F2 1, includeBoundary F2 true, occ F1 0
--   TranscriptProofParser: len 17968, occ F2 1, includeBoundary F2 true, occ F1 0
--   Lagrange: len 4745, occ F2 1, includeBoundary F2 true, occ F1 0
--   QuotientAndLinearization(external): len 4579, occ F2 1, includeBoundary F2 true, occ F1 0
--   FinalPairing: len 4221, occ F2 1, includeBoundary F2 true, occ F1 0
--   F1 ctx AccumulatorHelpers vs F2: len 8962, occ F2 1, includeBoundary F2 false, occ F1 1
--
-- so every partial is a regression-detectable byte gate on the IVC artifact, and
-- the last line is NOT: the F1 (poseidon) AccumulatorHelpers render is a prefix
-- of the F2 render and occurs once in F2 too, but never at an include boundary.
-- That is exactly why the control is includeBoundary and not occ.
--
-- This is a KAT/#eval module, not a proof and not a theorem: nothing here is a
-- fixture inside a statement (D-P71), and no statement/frozen file is touched.
-- WID.5 replaces the hand-read context by the exported key (WID.3's bundle);
-- until then f2Ctx is the evidence file's transcription and the gates below are
-- the only tie to the artifact. A partial occurring zero or two times, or a
-- boundary change, reddens its gate - that is a port divergence (WID.2's Stop
-- condition), not something to fix in the generator from here.
import Midfall.Generator.VerifierPartials
set_option autoImplicit false
open Midfall.Generator Midfall.Generator.VerifierPartialKats

namespace Midfall.Generator.IvcPartialKats

/-! ## The F2 context (evidence: IvcPartials.lean) -/

/-- The tracked IVC artifact, read at #eval time (D-P19). The relative path
    resolves from formal/ (where lake runs) and from the repo root, the
    EvmKats.readFirst pattern. A missing file is a red gate, not a silent pass:
    every occurrence count below is then 0. -/
def f2DumpCandidates : List String :=
  ["../proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol",
   "proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol"]

def readF2Dump : IO String := EvmKats.readFirst f2DumpCandidates

-- F2 proof layout: advice 15 G1, lookupM 2, permZ 6, 2 lookups x (1 helper, 1 acc), trash 1,
-- quotient limbs 4, evals 102, fCom, qEvals 5, pi; proofLen 0x1e60, end 0x1ec4.
def f2ProofLayout : ProofCalldataLayout :=
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

/-- The F2-shaped context: poseidonCtx with the accumulator / external-evaluator
    fields the IVC decider profile needs, exactly as the evidence file read them
    off the tracked artifact (advice 15, two lookups, six permutation sets, 16
    instances, k = 20, seven 56-bit accumulator limbs, external quotient frame).
    The fields not overridden here are inert for these seven renders. -/
def f2Ctx : PartialCtx :=
  { poseidonCtx with
    vkMptr := 0x3680
    scalarInvScratchMptr := 0x3680 - modexpScratchBytes
    expectedHasAccumulator := true
    expectedHasAccumulatorWord := 1
    expectedAccOffset := 4
    expectedNumAccLimbs := 7
    expectedNumAccLimbBits := 56
    expectedAccHasCarriedScalars := true
    accFixedBases := []
    accMsmScratch := 0xb140
    expectedQuotientCodehash := some 0
    quotientExternal := some { frameBase := 0x3680, frameLen := 0x6ac0, outputLen := 0x180,
                               magic := quotientExternalMagic }
    k := 20
    numInstances := 16
    numNegLagranges := 10
    numQuotients := 4
    proofLen := 0x1e60
    simpleSelectorCols := List.range 10
    userPhases := [{ adviceBytes := 0x780, numChallenges := 0, challengeOffset := 0 }]
    proofLayout := f2ProofLayout
    numLookups := 2
    numPermutationZs := 6
    lookupHPlusAcc := 4
    numTrashcans := 1 }

/-! ## The F2 byte gates

Each gate is "the render occurs exactly once in the tracked IVC artifact AND
carries the include boundary", the same shape as the F1 gates in
VerifierPartials.lean. occ and includeBoundary are that module's, not a second
comparison layer. -/

/-- GATE 1 (TEXTUAL). AssemblyHelpers at F2 (16,223 bytes) occurs once and is a
    standalone include of the IVC artifact. -/
def f2_assemblyHelpers_bytesExact_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (occursOnce sol (renderAssemblyHelpers f2Ctx) && includeBoundary sol (renderAssemblyHelpers f2Ctx))

/-- GATE 2 (TEXTUAL). AccumulatorHelpers at F2 (17,544 bytes) occurs once and is a
    standalone include. The F1 render of the same partial is NOT a byte match at
    the boundary; f2_f1CtxAccumulatorHelpers_noBoundary_ok pins that. -/
def f2_accumulatorHelpers_bytesExact_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (occursOnce sol (renderAccumulatorHelpers f2Ctx) && includeBoundary sol (renderAccumulatorHelpers f2Ctx))

/-- GATE 3 (TEXTUAL). VkLoading at F2 (5,820 bytes) occurs once and is a
    standalone include. -/
def f2_vkLoading_bytesExact_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (occursOnce sol (renderVkLoading f2Ctx) && includeBoundary sol (renderVkLoading f2Ctx))

/-- GATE 4 (TEXTUAL). TranscriptProofParser at F2 (17,968 bytes) occurs once and
    is a standalone include. -/
def f2_transcriptProofParser_bytesExact_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (occursOnce sol (renderTranscriptProofParser f2Ctx) && includeBoundary sol (renderTranscriptProofParser f2Ctx))

/-- GATE 5 (TEXTUAL). Lagrange at F2 (4,745 bytes) occurs once and is a
    standalone include. -/
def f2_lagrange_bytesExact_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (occursOnce sol (renderLagrange f2Ctx) && includeBoundary sol (renderLagrange f2Ctx))

/-- GATE 6 (TEXTUAL). QuotientAndLinearization in the EXTERNAL arm (4,579 bytes:
    the evidence's own `renderQuotientAndLinearization f2Ctx "" ""`, whose
    quotient_external match takes the Some arm because f2Ctx sets it) occurs once
    and is a standalone include. -/
def f2_quotientAndLinearization_external_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  let r := renderQuotientAndLinearization f2Ctx "" ""
  pure (occursOnce sol r && includeBoundary sol r)

/-- GATE 7 (TEXTUAL). FinalPairing at F2 (4,221 bytes, the accumulator-batched
    arm) occurs once and is a standalone include. -/
def f2_finalPairing_bytesExact_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (occursOnce sol (renderFinalPairing f2Ctx) && includeBoundary sol (renderFinalPairing f2Ctx))

/-- GATE 8 (NEGATIVE CONTROL, expect false). The F1-context AccumulatorHelpers
    render against the F2 artifact: it occurs once (it is a prefix of the F2
    render) but it does NOT carry the include boundary, so `occursOnce` alone
    would have been a false positive. The gate is deliberately the boundary
    measurement and its expectation is false; a change that makes this true is
    either an artifact replacement or a context leak, both worth a red.
    This is the last line the evidence probe printed. -/
def f2_f1CtxAccumulatorHelpers_noBoundary_ok : IO Bool :=
  readF2Dump >>= fun sol =>
  pure (includeBoundary sol (renderAccumulatorHelpers poseidonCtx))

end Midfall.Generator.IvcPartialKats

#eval Midfall.Generator.IvcPartialKats.f2_assemblyHelpers_bytesExact_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_accumulatorHelpers_bytesExact_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_vkLoading_bytesExact_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_transcriptProofParser_bytesExact_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_lagrange_bytesExact_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_quotientAndLinearization_external_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_finalPairing_bytesExact_ok -- expect true
#eval Midfall.Generator.IvcPartialKats.f2_f1CtxAccumulatorHelpers_noBoundary_ok -- expect false, the negative control: the F1 AccumulatorHelpers render occurs in the F2 artifact but NOT at an include boundary (see the docstring)

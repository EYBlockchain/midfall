import Midfall.Generator.VerifierPartials
set_option autoImplicit false
open Midfall.Generator Midfall.Generator.VerifierPartialKats

/-! F2 probe: render the ported verifier partials at an F2-shaped context (numbers read from
    proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol) and test whether
    each render occurs exactly once in the F2 artifact. Read-only scratch probe. -/

def f2Path : String :=
  "../proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol"

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

def probe : IO Unit := do
  let sol ← IO.FS.readFile f2Path
  let f1 ← readDump
  let report (name : String) (r : String) : IO Unit :=
    IO.println s!"{name}: len {r.length}, occ F2 {occ sol r}, includeBoundary F2 {includeBoundary sol r}, occ F1 {occ f1 r}"
  report "AssemblyHelpers" (renderAssemblyHelpers f2Ctx)
  report "AccumulatorHelpers" (renderAccumulatorHelpers f2Ctx)
  report "VkLoading" (renderVkLoading f2Ctx)
  report "TranscriptProofParser" (renderTranscriptProofParser f2Ctx)
  report "Lagrange" (renderLagrange f2Ctx)
  report "QuotientAndLinearization(external)" (renderQuotientAndLinearization f2Ctx "" "")
  report "FinalPairing" (renderFinalPairing f2Ctx)
  -- the poseidon (F1) renders, as a control, against the F2 artifact
  report "F1 ctx AccumulatorHelpers vs F2" (renderAccumulatorHelpers poseidonCtx)

#eval probe

-- |
-- Midfall.Instances.SurfaceFixture
--
-- HAZARD 1 OF P-SE STAGE 4, DISCHARGED BY EXHIBIT. The stage-4 brief is explicit that
-- a fixture Surface with no witness behind it is the F1 failure class for a fifth
-- time: every per-partial theorem in Lowering/Partials.lean takes SupportedS S S.o0 as
-- a hypothesis and irCheck as a gate, and a Supported nothing satisfies makes all
-- seven vacuously true. So this file builds one Surface and then PROVES - not
-- evaluates - that SupportedS holds of it, that irCheck returns true on an object that
-- exists and false on ones that do not, and that DeploymentW is inhabited and
-- refutable.
--
-- WHY HERE AND NOT IN Lowering/. The Surface record is parameterised by an
-- AdmissiblePairing, and the only model of one in the tree is the exponent model
-- (R-28). The Instances confinement gate greps DIRECT imports in theorem-bearing
-- files, so a witness has to live in Instances/ itself, exactly as InvFixture.lean
-- does for the invariant (hazard 3). Nothing outside Instances/ cites anything here.
--
-- WHY p = r. The per-partial theorems are only usable where EnvAgrees.modulus pins p
-- to the FR_MODULUS literal, which is the BLS12-381 scalar field, so a fixture at a
-- toy prime would exhibit a Surface no theorem can ever be applied to. The exponent
-- model is generic in the prime, so the same construction runs at r, and hazard 2 (Fr
-- 17 is too small for magnitude and width gates) is satisfied a fortiori.
--
-- WHAT THE FIXTURE DOES NOT EXERCISE, stated rather than glossed:
--
--   1. R-58 F4 DELETED the qvmValidated slot this note used to describe. It was
--      True here, which is exactly the defect: a Prop field the only Surface in the
--      tree discharges with `trivial` is a field that cannot fail. The QVM
--      obligation that CAN fail is LoweringCorrect.qvm_validated_noBoundsFault,
--      which quantifies over a real LoweringPlan and LoweringPlan.supportedQvm.
--
--   6. R-58 added five pin fields to Surface - shell_unfolds, plan_hasAccumulator,
--      plan_numInstances, evaluator_agrees, encG2_shape (named encG2_eip until R-60 S4
--      renamed it for overclaiming) - and this fixture meets all
--      five. Four are rfl, because the fixture was built so that the shell, the
--      plan, the render and the deployment agree by construction; encG2_shape needed
--      the encoder itself changed, from `fun _ => Bytes.empty` to the EIP-2537
--      infinity encoding, and THAT is the pin doing its job: the old fixture could
--      not be written. shellPinsKats_ok, planPinsKats_ok, encG2AtFixture_ok and
--      accFixedBasesKats_ok below give each pin its refutation, because a pin that
--      only ever meets one fixture is how we got here (R-41).
--      R-60 S4, stated rather than glossed: encG2_shape is met by a CONSTANT function,
--      which is exactly what this fixture uses. That is not a defect in the fixture, it
--      is the pin's ceiling - it constrains the output bytes, not the map. The
--      strengthening it does not make is `Function.Injective encG2`, and this fixture
--      cannot meet it, so it is a named gap at Surface.encG2_shape and in
--      scripts/check_hypothesis_bundles.py rather than a satisfied claim.
--      R-60 S3 strengthened evaluator_agrees from the isSome agreement to the runtime
--      BLOCK equation (L.evaluator.map Object.codeBlock = evaluatorRuntime.map
--      Prod.fst); it is still rfl HERE because both sides are none, and
--      planPinsKats_ok now refutes it with a block mismatch rather than with an
--      isSome mismatch.
--   2. cfg.accumulator is none, so SupportedS.acc is vacuous in the exhibit. The
--      accumulator arm needs a Generator AccumulatorEncoding whose validate passes,
--      which is D-P16 territory and is exercised in Lowering/AccEncoding.lean.
--   3. P-4a2 CLOSED THIS. EnvAgrees WAS not exhibited: its truncWidth clause needed
--      a FieldConsts with numBits 255, its omegaOrder clause a genuine root of unity in
--      Fr r, its baryWeight clause the inverse of 2^k, and its negLagranges clause a
--      PlanView that agreed with its own ConstraintSystem. All four are now discharged:
--      see fxEnvAgrees below, Midfall/Assumptions/TwoAdicity.lean, and the repaired fxFc,
--      fxDom and fxPlan. The one hypothesis of the headline bundle that is STILL
--      unexhibited is Eip2537.Holds, for the reason note 7 gives.
--      P-ENV THEN STRENGTHENED `omegaOrder` from `omega ^ n = 1` to
--      `orderExactly omega n`, because P-4a2 measured that the old text was satisfied by
--      `omega = omegaInv = 1` with the CORRECT barycentricWeight - a hypothesis a
--      degenerate object satisfies, which is the D-P23 class. The exhibit survives
--      (`fxEnvAgrees.omegaOrder` is `frOmega4_order`), the separate non-vacuity theorem
--      `fxOmegaOrderExactly` is GONE because the structure now carries the fact, and
--      `fxDomDegenerate` is the object the old clause accepted and the new one refutes
--      (`fxEnvAgreesRejectsDegeneratePair`).
--   4. P-AST CHANGED THIS ONE, P-AST2 AND P-AST3a EXTENDED IT. blk no longer returns what
--      the fixture declares: it is Midfall/Lowering/GenAst.lean's emitPartial, and main is
--      that file's emitMain, so main_concat and the new BlkIsEmitter pin are rfl here by
--      construction rather than by assertion. FOUR slices are real: finalPairing (the
--      deployed arm of FinalPairing.yul, with fail and ec_pairing defined in main's helper
--      prefix so the slice can actually run), lagrange (the three-statement Lagrange.yul
--      block, whose inner scope carries the five Fr loops and the MF-4 two-value
--      batch_invert), quotientLin (the linearization scope: nine statements, one squaring
--      walk, the two-word QUOTIENT_MPTR payload - and, note this, ONE top-level statement,
--      the same length as the placeholder it replaced, so nothing in main's LENGTH can see
--      the conversion) and traceReturn (the production terminal arm: guard, mstore 1,
--      return 32 bytes). The other THREE are still one-statement placeholders - vkLoading,
--      transcriptParser and pcs - because GenAst.emittedPartials is
--      [lagrange, quotientLin, finalPairing, traceReturn]. The placeholders moved out of
--      this file into the emitter so that the emitter is the only source of blk in the
--      tree; a pin against a blk the fixture still declared by hand would pin nothing.
--      What P-AST2 and P-AST3a add to THIS file is the plant class each conversion makes
--      possible: before it, a Surface whose blk .lagrange was the placeholder satisfied
--      BlkIsEmitter, because the placeholder WAS the emitter's answer.
--      blkPinBitesLagrangePlaceholder, blkPinBitesTraceReturnPlaceholder and
--      blkPinBitesQuotientLinPlaceholder are the three theorems that say it no longer does.
--   7. Eip2537.Holds is still NOT exhibited as a single term, and P-4a2 did not change
--      that - but the reason P-GAPFIX re-pointed. It used to be "the missing BLS12-381
--      curve model (D-P1, R-28)". A curve model now EXISTS (Instances/G1Agreement.lean
--      works over ZMod blsP and exhibits four of the six Holds clauses at a real-curve
--      codec, g1CodecZ_g1_four), so what keeps Holds unexhibited here is that THIS
--      fixture's pairing model is the exponent model: Surface is parameterised at
--      RP = Exp rp, VerifierEnv.g1 is typed over that pairing, and a curve codec cannot
--      be installed without a curve AdmissiblePairing (D-P36). The other two open clauses
--      are g2Valid - no Fp2 model, gap_g2_no_fp2_model - and pairing2 at real points.
--      See ObligationsGates.gap_holds_unexhibited and encG2AtFixture_ok.
--   5. irCheck inspects top-level statements only. A full alpha-equivalence check
--      modulo constant substitution is M8 work and is blocked on the same D-P15
--      import; what is here is the decidable fragment that can already distinguish a
--      resolved call from an unresolved one, which is the distinction the gate needs.

import Midfall.Lowering.Partials
import Midfall.Assumptions.TwoAdicity
import Midfall.Instances.ExponentModel
import Midfall.Generator.LayoutMemory
import Midfall.Generator.VerifierPartials
import YulSemantics.Object

namespace Midfall.Instances.SurfaceFixture
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Generator Midfall.Yul Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

/-- The prime every statement in this file is at: the scalar field the contract
    hard-codes. Fact (Nat.Prime r) comes from CompPoly through Assumptions.Pairing. -/
abbrev rp : ℕ := Midfall.Assumptions.r

/-- The point type: the exponent model, generic in the prime, so it is a group and a
    pairing carrier at r exactly as it is at 17. -/
abbrev RP : Type := Exp rp

/-- The element of a given exponent. -/
def fx (n : Nat) : RP := Multiplicative.ofAdd (n : ZMod rp)

/-- Field constants for the environment: the BLS12-381 scalar field's REAL constants,
    discharged in Midfall/Assumptions/TwoAdicity.lean. Before P-4a2 this was
    `{ numBits := 255, s := 32, rootOfUnity := 3, zeta := 2 }` - `numBits` was right, and
    the other two were the ZMod 17 values (where 3 does have order 16 = 2^4) pasted at the
    real modulus, where 3 is not a primitive 2^32-th root and 2 has no order-3 property at
    all. Nothing checked either claim, which is R-3's trust boundary. The values now come
    from the exhibit in TwoAdicity, which PROVES in the kernel that the root has order
    exactly 2^32 (its 2^32-th power is 1 and its 2^31-st is -1) and that zeta has order
    exactly 3. -/
def fxFc : FieldConsts (Fr rp) := Midfall.Assumptions.frFc

/-- THE REPAIRED HYPOTHESIS, discharged at the fixture's own constants: `rootOfUnity` has
    order exactly `2^s` and `zeta` has order 3. This is the R-3/R-47 trust boundary closed
    at the real modulus, by the kernel rather than by `native_decide`. -/
theorem fxFc_isWellFormed : fxFc.IsWellFormed := Midfall.Assumptions.frFc_isWellFormed

/-- The verifier environment. -/
def fxE : VerifierEnv rp RP RP RP :=
  { g1 := expG1Codec, field := fxFc, delta := 2, fewerPointSetsRuntime := false }

/-- The pairing parameters, in the shape EnvAgrees nG2 and sG2 describe: nG2Prepared is
    the inverse of g2 and sG2Prepared is the sG2 generator itself, named apart. -/
def fxParams : ParamsVerifierKZG RP RP :=
  { sG2 := fx 5, nG2Prepared := (fx 1)⁻¹, sG2Prepared := fx 5 }

/-- THE SIZE-4 DOMAIN, REPAIRED. It used to be
    `{ omega := 1, omegaInv := 1, ..., barycentricWeight := 4 }`, which is not a domain:
    a generator equal to 1 satisfies `omega ^ n = 1` for every n, so `EnvAgrees.omegaOrder`
    passed vacuously, and `barycentricWeight := 4` is not the inverse of 2^k in `Fr r`
    (4 * 4 = 16 != 1), so `EnvAgrees.baryWeight` was FALSE. The brief's own diagnosis,
    measured rather than assumed.

    The values are what the PORTED constructor produces: `EvaluationDomain.new fxFc 3 2`
    at the repaired constants (j = csDegree = 3, k = 2) computes extendedK = 3,
    omega = root^(2^30) of order exactly 4, barycentricWeight = 4^-1, and the two
    `t_evaluations` of the zeta coset. `fxDomMatchesPort_ok` below re-runs the constructor
    in the VM and compares all fifteen fields, so the literals are checked against the port
    rather than asserted alongside it. Written out by hand rather than extracted from the
    `Except` because `decide` cannot reduce a `ZMod` inversion at 255-bit `r` - the same
    limit TwoAdicity's header records - and a `getD`-style extraction would have made the
    domain's definition depend on a computation the kernel cannot check. -/
def fxDom : EvaluationDomain (Fr rp) :=
  { n := 4, k := 2, extendedK := 3,
    omega := Midfall.Assumptions.frOmega4,
    omegaInv := Midfall.Assumptions.frOmega4Inv,
    extendedOmega := Midfall.Assumptions.frRootOfUnity ^ 2 ^ 29,
    extendedOmegaInv := 0x1333b22e5ce11044babc5affca86bf658e74903694b04fd86037fe81ae99502e,
    gCoset := Midfall.Assumptions.frZeta,
    gCosetInv := Midfall.Assumptions.frZeta * Midfall.Assumptions.frZeta,
    quotientPolyDegree := 2,
    ifftDivisor := Midfall.Assumptions.frInv4,
    extendedIfftDivisor := 0x656ff268c469cd9f2cd29d07086d9d04a945ef829ffe907f1fffffff20000001,
    tEvaluations := #[0x4d491a377113a8daccd13ab0066be558a911e156fffe5bfeaaaaaaa9aaaaaaab,
                      0xac45a4010001a40200000000ffffffff],
    barycentricWeight := Midfall.Assumptions.frInv4 }

/-- Two instance columns, one advice, one fixed, no challenges: the shape
    SupportedS.instShape, advice and singlePhase demand. Both instance queries are at
    rotation 0, which is noRotInst; a query at rotation 1 would make the exhibit fail
    rather than pass quietly.

    P-SCHED: `adviceColumnPhase` IS NOW SET, AND IT USED TO BE AN EMPTY VECTOR. It came
    from `ConstraintSystem.default` (`#[]`) while `numAdviceColumns := 1`, which is not
    a constraint system the reference could produce: the phase loop in
    `Verifier.parseTrace` (Exec/Verifier.lean:148-171) picks the advice columns of phase
    `ph` with `cs.adviceColumnPhase[i]?`, so an empty vector picks NONE,
    `scatterIndexed 1 []` finds a hole at advice column 0, and `prepare` faults with
    `Fault.panic "proofs/src/plonk/verifier.rs:118"` BEFORE ANY PROOF BYTE IS CONSUMED -
    the fault does not depend on the stream at all. Measured consequence: `decodeRust`
    answered `none` for every byte string at the deployment (63 buffers tried, including
    the artifact's own 2640-byte compressed stream and the 4484-byte calldata), so the
    whole byte-level decode path was untested at the only computable Surface in the tree,
    and every `LoweringCorrect` field of the shape `decodeRust ... = some ms -> ...` was
    vacuous for that reason rather than for a reason anyone had written down. With the
    vector set to the one phase the system has, `prepare` runs to completion at the
    fixture, consumes 336 bytes, and `decodeRust` returns `some` - see
    `Midfall/Instances/ObligationsGates.lean`, `decodeRust_some_at_deployment`. The shape
    is the one every other constraint system in the tree already uses
    (Instances/NativeE2E.lean:96, Instances/ExponentModel.lean:496,
    Halo2/Spec/Relation.lean:176): one advice column, phase 0. -/
def fxCs : ConstraintSystem (Fr rp) :=
  { ConstraintSystem.default with
    numFixedColumns := 1, numAdviceColumns := 1, numInstanceColumns := 2,
    adviceColumnPhase := #[⟨0⟩],
    numChallenges := 0,
    instanceQueries := #[(vCol 0 Any.instance, Rotation.value 0),
                         (vCol 1 Any.instance, Rotation.value 0)] }

/-- The verifying key. csDegree 3 is what fxCs.degree computes - the gate below checks
    it rather than assuming it - which makes domainConsistent quotientPolyDegree 2 and
    SupportedS.hLimbs the same arithmetic. The single fixed commitment is the IDENTITY
    point: vkPoints asks that the embedded bytes decode and that the MSM precompile
    accepts them, and the exponent codec encodes a point as its exponent in 128 bytes,
    so only the identity (all-zero bytes, which EIP-2537 reads as infinity) passes a
    curve check. vkPointsKats_ok shows a non-identity commitment REFUTES the clause, so
    the identity choice is the clause working rather than a clause dodged. -/
def fxVk : VerifyingKey (Fr rp) RP :=
  { domain := fxDom, fixedCommitments := #[1], permutation := { commitments := #[] },
    cs := fxCs, csDegree := 3, transcriptRepr := 7 }

/-- THE G2 ENCODER, hoisted out of realSurface so the VK header derivation below and the
    Surface field are ONE term and cannot drift. It is the degenerate encoder the exponent
    model can supply (R-58 G2): every G2 point is the EIP-2537 infinity encoding, 256 zero
    bytes. That is stated here because it is a LIMIT of the exhibit, not a detail: at this
    Surface EnvAgrees.g2BaseWords and negSG2Words are satisfied by a constant function, so
    they are exercised vacuously and only the G1 slot distinguishes anything. -/
def fxEncG2 : RP → Bytes := fun _ => Midfall.Yul.bytesZero Midfall.Yul.g2Bytes

/-- The contract positive-base table, hoisted out of realSurface for the same reason:
    EnvAgrees.accBasesInVk must be exhibited at the table the Surface actually carries
    (R-58 F7: the -G row is what makes accFixedBases_producer non-vacuous here). -/
def fxAccFixedBases : Array (AccFixedBase RP) :=
  #[{ name := "-G", base := fx 1, negate := true },
    { name := "b0", base := 1, negate := false }]

/-- The i-th 32-byte big-endian word of a byte string: the inverse of the
    `wordToBytesBE` fold `vkHeaderBytes` performs, so a point written into the header
    through these words reads back through `vkG1Words` as the same bytes. -/
def fxWordAt (bs : Bytes) (i : Nat) : Word256 :=
  BitVec.ofNat 256 (Midfall.bytesToNatBE
    (ByteArray.mk (((bs.toList.drop (i * 32)).take 32).toArray)))

/-- The first `n` words of a byte string, in order. -/
def fxWordsOf (bs : Bytes) (n : Nat) : List Word256 := (List.range n).map (fxWordAt bs)

/-- THE VK PAYLOAD IMAGE, and P-RESTORE2 made it thirty-one words instead of two.

    WHY IT GREW. The sketch's EnvAgrees names the G1 base slot, the G2 base slot and the
    NEG_S_G2 slot (header words 11, 15, 23 - `vkHeaderTemplateSlotsDefault`), and
    `accBasesInVk` says every fixed-base entry is a point some header slot encodes. A
    two-word payload cannot satisfy any of that: `vkHeaderBytes` of a slice that runs off
    the end is `Bytes.empty`, never a zero-padded stand-in, so the clauses were FALSE at
    this fixture and the only reason nobody noticed is that the clauses had been dropped.
    That is the finding P-RESTORE2 was told to report rather than route around: the
    fixture had been built small to fit the weakened hypothesis, and it is now built to fit
    the strong one. The shape is the reference's own - eleven scalars, four G1 words, eight
    G2 words, eight NEG_S_G2 words, exactly `syntheticVkConstants` at Models.lean:1168 -
    and the point words are DERIVED from the codecs rather than transcribed from them, so
    a codec change moves the payload with it.

    THE COST, stated because stage 3 recorded it: the .vk clause of Inv copies
    `PV.vk.len` bytes and a kilobyte of payload was said to push the kernel over its
    recursion limit. It does not: the copy is a `ByteArray` slice, not a per-byte kernel
    reduction, and `fxInvSatKats_ok` below evaluates Inv at this plan view in the
    interpreter. If that ever changes, the fix is a smaller clause, not a smaller payload.
    -/
def fxHeaderScalars : List (String × Word256) :=
  [("vk_digest", 7), ("num_instances", 1), ("k", 2), ("n_inv", 4), ("omega", 5),
   ("omega_inv", 6), ("omega_inv_to_l", 7), ("has_accumulator", 0), ("acc_offset", 0),
   ("num_acc_limbs", 0), ("num_acc_limb_bits", 0)]

/-- The three point slots, each filled from the codec that the clause names. The G1 slot
    is `fxToEip` of the pairing generator; the two G2 slots are `fxEncG2` of the G2
    generator and of the inverse of the sG2 the params carry - which at this fixture are
    the same 256 zero bytes, because the encoder is constant (see fxEncG2). -/
def fxHeaderPointWords : List (String × Word256) :=
  ((fxWordsOf ((expG1Codec (p := rp)).toEip ((inferInstance :
      Midfall.AdmissiblePairing (p := rp) RP RP RP).g₁)) 4).zipIdx.map
      fun (w, i) => ("g1_base_" ++ toString i, w)) ++
  ((fxWordsOf (fxEncG2 ((inferInstance :
      Midfall.AdmissiblePairing (p := rp) RP RP RP).g₂)) 8).zipIdx.map
      fun (w, i) => ("g2_base_" ++ toString i, w)) ++
  ((fxWordsOf (fxEncG2 ((fx 5 : RP)⁻¹)) 8).zipIdx.map
      fun (w, i) => ("neg_s_g2_" ++ toString i, w))

def fxPayload : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0x6000,
    constants := fxHeaderScalars ++ fxHeaderPointWords,
    fixedComms := [], permutationComms := [],
    quotientConstOffsetWords := none, quotientConstWords := 0,
    quotientProgramOffsetWords := none, quotientProgramWords := 0,
    quotientConstLabels := [], quotientConstHeaders := [] }

/-- The fixture plan's Data, DERIVED the same way the witness plan's is: Data.new over the
    default meta, the fixture payload and the fixture layout. The fixture has no circuit, so
    the honest Data is the one an empty circuit produces - and it is produced by the
    reference's own constructor rather than transcribed, which is what makes it a derivation
    at the fixture too. -/
def fxPlanData : Midfall.Generator.Data :=
  match Midfall.Generator.Data.new Midfall.Generator.constraintSystemMetaDefault fxPayload
      Midfall.Generator.LayoutMemoryKats.poseidonLayout with
  | .ok d => d
  | .error _ => Midfall.Lowering.emptyDataAt
    Midfall.Generator.LayoutMemoryKats.poseidonLayout

/-- The plan view: the deployed poseidon memory layout (whose WellFormed and validate
    both decide true, LayoutMemory.lean:869), the payload above, one public instance, a
    size-4 domain, no accumulator arm. -/
def fxPlan : PlanView :=
  -- P-AST3b: built through Inv.lean's constructor, so the four accumulator words and the
  -- hasAccumulator Bool are the ones accWordsOfEncoding reads off the fixture's own
  -- accumulator configuration (none, matching realSurface.cfg) and not four zeros typed
  -- in. Surface.plan_accExpectations is rfl here because it is a derivation and not a
  -- choice, and planAccExpectationsKats_ok shows the equation can fail.
  Midfall.Lowering.planViewWithAccumulator
    (vk := fxPayload)
    (vkMptr := Midfall.Generator.LayoutMemoryKats.poseidonLayout.vkMptr)
    (memory := Midfall.Generator.LayoutMemoryKats.poseidonLayout)
    (proofLayout := Midfall.Generator.poseidonProofLayout)
    (numInstances := 1) (k := 2)
    -- P-4a2: this was 2, which is what a circuit with ONE blinding factor would walk.
    -- fxCs.blindingFactors is ok 6 (Circuit.lean:1593, and the exhibit below recomputes
    -- it), so EnvAgrees.negLagranges - PV.numNegLagranges = blindingFactors + 1, the
    -- l_blind window of Lagrange.yul:57 - demanded 7 and the fixture was silently
    -- disagreeing with its own ConstraintSystem. Found by trying to exhibit EnvAgrees,
    -- not by reading it: the clause had never been evaluated at this Surface because the
    -- root-of-unity blocker meant nobody got that far.
    (numNegLagranges := 7)
    (acc := none)
    -- P-AST4: the empty-plan parser facts, for the same reason witnessPlanView carries them:
    -- the fixture plan's job is the theorem surface, and no gate here compares its
    -- transcriptParser slice against the deployed artifact.
    (facts := Midfall.Lowering.emptyParserFacts)
    -- P-PLANVIEW: the default meta and the Data derived from it. The fixture's pcs slice is
    -- therefore empty, for the same reason the witness plan's is, and blkPinBitesPcsPlaceholder
    -- below is what makes that decidable at the pin.
    (meta_ := Midfall.Generator.constraintSystemMetaDefault) (dat := fxPlanData)

/-! ### The seven blocks: the emitter, not a hand-written table -/

/-- THE FIXTURE'S blk IS THE GENERATOR FUNCTION: Midfall/Lowering/GenAst.lean's
    emitPartial, at this fixture's own plan view. Before P-AST this was a hand-written
    table of seven one-statement dummies, which is the R-62 defect in the only Surface in
    the tree: blk was free, so every *_spec theorem quantified over every block. Now the
    fixture's blk, its main block and the BlkIsEmitter pin all come from one function, so
    the pin is rfl HERE and the exhibits below are about surfaces that DEVIATE from it.

    vkLoading, finalPairing, lagrange, quotientLin and traceReturn are real slices; the
    other two are GenAst's
    placeholders, one statement each with a distinct literal, so a blk that returned the
    same block for two partials or dropped one still changes main and is caught by
    mainConcatKats_ok. -/
def fxPartialBlocks : Partial → YulBlock := fun q => GenAst.emitPartial fxPlan q

/-- The same function, at the plan view the record carries - the form the pin states. -/
def fxBlk : Partial → PlanView → YulBlock := fun q pv => GenAst.emitPartial pv q

/-- The main block: the two emitted AssemblyHelpers definitions, then the seven slices in
    include order. main_concat and BlkIsEmitter are both rfl against this definition,
    which is what makes them pins rather than claims: the moment blk and main come from
    two different functions the field stops being a definition and becomes a theorem. -/
def fxMain : YulBlock := GenAst.emitMain fxPlan

/-- The head guard the dispatcher runs first: the free-memory-pointer check the
    memoryguard bound is about. -/
def fxHeadGuard : YulBlock :=
  [Stmt.cond (Expr.builtin Op.gt [Expr.builtin Op.mload [Expr.lit (.number 0x40)],
      Expr.lit (.number 0x1000)])
    [Stmt.exprStmt (Expr.builtin Op.revert
      [Expr.lit (.number 0), Expr.lit (.number 0)])]]

/-! ### irCheck -/

-- R-60 S1: `declaredTops` and `unresolvedTop` used to live here and were moved to
-- Midfall/Lowering/Surface.lean, where `Surface.irCheck` is now a PROJECTION of
-- `S.runtimeName` rather than a free field that could hard-code a different naming
-- convention. Everything below is the fixture data that projection is exercised on.

/-- The fixture runtime: one declared helper, one call to it, and a terminating stop.
    Everything resolves. -/
def fxRuntime : YulBlock :=
  [Stmt.funDef "fail" ["code"] []
    [Stmt.exprStmt (Expr.builtin Op.revert
      [Expr.var "code", Expr.lit (.number 0)])],
   Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number 1)]),
   Stmt.exprStmt (Expr.builtin Op.stop [])]

/-- The same runtime with the declaration renamed and the call left alone: the planted
    rename, which must not pass irCheck. -/
def fxRuntimeRenamed : YulBlock :=
  [Stmt.funDef "fali" ["code"] []
    [Stmt.exprStmt (Expr.builtin Op.revert
      [Expr.var "code", Expr.lit (.number 0)])],
   Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number 1)]),
   Stmt.exprStmt (Expr.builtin Op.stop [])]

/-- The same runtime with a memoryguard let-initialiser, which is what a real via-ir
    import contains and what the vendored dialect cannot express: the name resolves to
    nothing, so irCheck rejects it and D-P15 is visible rather than silent. -/
def fxRuntimeMemoryguard : YulBlock :=
  [Stmt.letDecl ["m"] (some (Expr.call "memoryguard" [Expr.lit (.number 0x100)])),
   Stmt.exprStmt (Expr.builtin Op.mstore
     [Expr.lit (.number 0x40), Expr.var "m"])]

/-- The solc naming convention: the runtime is a sub-object called name_id_deployed. -/
def fxRuntimeName (n : String) : String := n ++ "_1_deployed"

/-- The fixture IR object: empty constructor code, the runtime as the deployed
    sub-object. -/
def fxIr : YulObject :=
  Object.mk "Halo2Verifier" ([] : YulBlock)
    [Object.mk (fxRuntimeName "Halo2Verifier") fxRuntime [] []] []

/-- The same with the planted rename in the runtime. -/
def fxIrRenamed : YulObject :=
  Object.mk "Halo2Verifier" ([] : YulBlock)
    [Object.mk (fxRuntimeName "Halo2Verifier") fxRuntimeRenamed [] []] []

/-- The same with a memoryguard prologue store. -/
def fxIrMemoryguard : YulObject :=
  Object.mk "Halo2Verifier" ([] : YulBlock)
    [Object.mk (fxRuntimeName "Halo2Verifier") fxRuntimeMemoryguard [] []] []

/-! ### The deployment -/

/-- The VK runtime image: the 0xfe deployment prefix followed by the payload, exactly
    as vkRuntime_spec states it, so the pin is rfl and the gate on it is about the
    prefix rather than about the definition. -/
def fxVkRuntime : Bytes := ByteArray.append (ByteArray.mk #[0xfe]) fxPayload.bytes

/-- The quotient evaluator runtime image, for the externalised-quotient render. -/
def fxQuotientRuntime : Bytes := ByteArray.mk #[0xfe, 0x01, 0x02, 0x03]

/-- The addresses: distinct from each other and from the four precompile keys, which is
    what DeploymentW.disjoint and honestCalls_functional need. -/
def fxVkAddr : U256 := 0x1234

def fxQuotientAddr : U256 := 0x1235

/-- The shell runtime layout: the solc prologue bytes (PUSH1 0x80, PUSH1 0x40, MSTORE -
    the memoryguard lowering the bound is about), the data maps, and the immutable map
    that names the two addresses. -/
def fxShellLayout : EVM.Layout :=
  { code := (Midfall.Generator.bytesFromNats [0x60, 0x80, 0x60, 0x40, 0x52]).data.toList
    dataOffset := fun _ => 0
    dataSize := fun _ => 0
    immutable := fun k =>
      if k == litValue (.string "AUTHORIZED_VK") then fxVkAddr
      else if k == litValue (.string "AUTHORIZED_QUOTIENT") then fxQuotientAddr
      else 0 }

/-- **THE ARM THE SHELL CARRIES** (D-P39). The head guard, then the two shell locals BOUND, then the
    emitted main with the 90 contract-level constants INLINED at every use site including inside the
    eight helper bodies. This is the block `RunShell` runs, and `shell_unfolds` is `rfl` about it. -/
def fxArmOf (m : YulBlock) : YulBlock :=
  Midfall.Lowering.Inline.inlineContractConstants Midfall.Lowering.Inline.contractConstants
    (fxHeadGuard ++ Midfall.Lowering.Inline.shellLocalLets ++ m)

/-- The shell object: the ARM block, constants inlined (D-P39). -/
def fxShell : YulObject := Object.mk "Halo2Verifier" (fxArmOf fxMain) [] []

/-- The lowered program. -/
def fxLowered : Lowered :=
  { headGuard := fxHeadGuard, main := fxMain, vkRuntime := fxVkRuntime,
    evaluator := none }

/-- The render function the fixture supplies: production options yield the lowered
    program, a trace or gas-checkpoint render is refused. That is what makes lower_ok a
    pin rather than a tautology - a lower that returned .ok for every option would
    satisfy lower_ok while o0 pinned nothing about L. -/
def fxLower (o : RenderOptions) :
    Except Midfall.Generator.GeneratorError Lowered :=
  if o.diagnostics.trace || o.diagnostics.gasCheckpoints then
    .error (Midfall.Generator.GeneratorError.noAdviceColumns)
  else
    .ok fxLowered

/-- The render options: embedded VK, inline quotient, VM lowering, no diagnostics. -/
def fxOptions : RenderOptions :=
  { vk := RenderVk.embedded, quotient := RenderQuotient.inline,
    quotientLowering := QuotientLowering.vm,
    diagnostics := RenderDiagnostics.default, provenance := none }

/-- The trace variant, which fxLower refuses and SupportedS.production refuses. -/
def fxOptionsTrace : RenderOptions :=
  { vk := RenderVk.embedded, quotient := RenderQuotient.inline,
    quotientLowering := QuotientLowering.vm,
    diagnostics := { trace := true, gasCheckpoints := false }, provenance := none }

/-- A gas-checkpoint render with trace OFF. This is the option that distinguishes the
    two shapes of astOfMain: the old one keyed only on `trace`, so it answered
    `some fxMain` here while `fxLower` refuses, and render_eq_print is exactly the
    equation that catches it. -/
def fxOptionsGas : RenderOptions :=
  { vk := RenderVk.embedded, quotient := RenderQuotient.inline,
    quotientLowering := QuotientLowering.vm,
    diagnostics := { trace := false, gasCheckpoints := true }, provenance := none }

/-- The world the verifier is deployed into, before the codehash projection. -/
def fxW0 : ExecEnv :=
  { keccakOf := hashOfBytes keccak256
    extCodeOf := fun a =>
      if accountKey a == accountKey fxVkAddr then fxVkRuntime.data.toList
      else if accountKey a == accountKey fxQuotientAddr then fxQuotientRuntime.data.toList
      else []
    balanceOf := fun _ => 0 }

/-- The deployment world, with the codehash map DERIVED from the code map. That is what
    makes ExecEnv.WF provable by reflexivity, and the point of doing it that way is that
    a world whose codehash map disagrees with its code map cannot exhibit DeploymentW
    at all - the wf field is not decoration. -/
def fxW : ExecEnv :=
  { fxW0 with extCodeHashOf := fun a => projectedCodeHash fxW0 fxW0.balanceOf a }

/-- P-RESTORE3, THE WITNESS FOR THE RESTORED 'Surface.hProofLayout' PIN. The three
    numbers after the protocol are the fromProtocol arguments the sketch's pin
    existentially quantifies over: 48 eval words (D:1405, 0x600 = 48 * 32) and 3 point
    sets (D:1460, 0x60 = 3 * 32). The protocol is the poseidon commitment stream - one
    advice phase of 8 G1s (D:1275), one lookup with one helper (D:1332) and its
    accumulator (D:1343), three permutation products (D:1314), one trashcan (D:1357),
    four quotient limbs (D:1380) - i.e. exactly the counts 'poseidonMeta' records as
    OBSERVATIONS of the artifact. So this is not a self-round-trip: the layout on the
    right is transcribed from the deployed dump's own 'add(proof_cptr, 0x..)' lines and
    the layout on the left is what the ported Rust generator computes from the counts.
    They agree field for field, which is the cross-check. -/
def fxProofProtocol : ProtocolPlan := Midfall.Generator.AbiKats.protocolShape [8] [1] 3 1 4

/-! ### The fixture Surface -/

/-- THE FIXTURE. Every field is data the exhibit can point at, and every pin field is
    rfl - which is the point: a pin that needed a proof here would be a claim about a
    renderer that does not exist yet. blk returns the seven slices and L.main is their
    concatenation, so main_concat is rfl and the record describes a verifier whose entry
    path is the seven partials rather than nothing. -/
def realSurface : Surface rp RP RP RP :=
  { E := fxE, params := fxParams, vk := fxVk,
    cfg := { numInstances := 1, numCommittedInstances := 1, accumulator := none },
    -- R-58 F7: the table carries the -G row the producer clause is stated about.
    -- Before this it was a one-entry table with no -G row, which is why
    -- ObligationsGates could PROVE the second conjunct of accFixedBases_producer
    -- was vacuous here. base := fx 1 is expGen, i.e. P.g1 at this model, which is
    -- what the clause demands of a -G row together with negate := true.
    accFixedBases := fxAccFixedBases,
    vkDigest := frWord fxVk.transcriptRepr,
    sG2gen := fx 5,
    -- R-58 G2: the encoder used to be `fun _ => Midfall.Bytes.empty`, which is
    -- not an EIP-2537 encoding of anything, so no Eip2537.Holds was satisfiable
    -- at this Surface and every field carrying one was vacuous. The all-zero
    -- 256-byte word is the EIP infinity encoding: valid, and the degenerate
    -- encoder the exponent model can actually supply.
    encG2 := fxEncG2,
    o₀ := fxOptions, L := fxLowered, lower := fxLower, lower_ok := rfl,
    bindLocals := Midfall.Lowering.Inline.shellLocalLets, shell := fxShell,
    shellLayout := fxShellLayout,
    evaluatorRuntime := none, runtimeName := fxRuntimeName,
    -- R-58 F8: astOfMain is now DEFINED as the main block of what the render
    -- produces, which is exactly the equation render_eq_print states, so the
    -- field discharges by rfl and the pin says something about the pair of
    -- functions rather than about a block compared with itself. The old form
    -- keyed off o.diagnostics.trace only, so it returned `some fxMain` for an
    -- option the render refuses - a gas-checkpoint render - and the pin caught
    -- that.
    astOfMain :=
      fun o => match fxLower o with | .ok l => some l.main | .error _ => none,
    blk := fxBlk, plan := fxPlan,
    expectedVkCodehash := some (keccak256 fxVkRuntime),
    quotientRuntime := some fxQuotientRuntime,
    expectedQuotientCodehash := some (keccak256 fxQuotientRuntime),
    vkDigest_spec := rfl, vkRuntime_spec := rfl,
    -- The helpers slot of main_concat is no longer empty and no longer a free choice: it
    -- is the two AssemblyHelpers definitions the emitter produces, so the existential of
    -- main_concat is witnessed by the generator and not by nothing.
    main_concat := ⟨GenAst.emitHelpers fxPlan, rfl⟩,
    -- The R-58 pins. Every one is rfl HERE, which is the point: the fixture is
    -- built so that the shell, the plan and the render agree by construction,
    -- and a Surface that did not agree could not be written at all. Each has a
    -- refutation in the gates below, so none of them is satisfied by a constant.
    shell_unfolds := rfl,
    plan_hasAccumulator := rfl, plan_numInstances := rfl,
    -- P-AST3b: rfl because fxPlan was built by planViewWithAccumulator from the SAME
    -- Option the cfg carries. A plan whose four words disagreed with cfg cannot be written
    -- into this record at all, and planAccExpectationsKats_ok exhibits the lie.
    plan_accExpectations := rfl,
    evaluator_agrees := rfl,
    encG2_shape := fun x => by unfold fxEncG2; native_decide,
    -- P-RESTORE3: restored pin. rfl because the witness above IS the computation.
    hProofLayout := ⟨fxProofProtocol, 48, 3, rfl⟩ }

/-! ### 1. Supported is INHABITED -/

/-- THE HEADLINE EXHIBIT: SupportedS realSurface.o0 holds, as a kernel-checked term.
    Every one of the TEN fields is discharged from the fixture data above - advice,
    instShape, noRotInst, acc, singlePhase, hLimbs, vkPoints, layout, production, wf,
    which is what `#check @SupportedS.mk` reports and what R-60 S9 corrects this
    comment from: it used to say "eleven fields" and to name `qvm` among them, and
    R-58 F4 deleted that field, so the count and the list were both stale. Only ONE
    field is trivial by construction here: `acc`, discharged from
    `cfg.accumulator = none`; the file header says so rather than leaving a reader to
    find it. R-60 S9 also records that the frozen placeholder in Lowering/Types.lean
    STILL carries the deleted `qvm` field (Types.lean:63, `qvm : qvmValidated`): it is
    frozen because Statements.lean elaborates against it, so the placeholder and the
    live SupportedS disagree by design, and that is a note in the code now rather than
    a surprise for the next reader.

    This is the gate the stage-4 brief asks for. A Surface whose Supported could not be
    inhabited would make all seven per-partial theorems vacuous, which is the F1 class
    the programme has now hit four times. -/
theorem supportedInhabited : SupportedS realSurface realSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [realSurface, fxVk, List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- The trace render is REFUTED at the SupportedS level, not merely unprovable:
    production is a conjunct of SupportedS, so a Surface asked about a trace render
    fails the exhibit. Without this the production field could be decoration - a
    SupportedS whose production clause nobody ever inverted would be the F1 class again. -/
theorem supportedRefutedForTraceRender : ¬ SupportedS realSurface fxOptionsTrace := by
  intro h
  have hprod := h.production
  have : fxOptionsTrace.diagnostics.trace = false := hprod.1
  exact Bool.noConfusion this

/-! ### 2. irCheck is REACHABLE -/

/-! ### 2. irCheck is REACHABLE, and it rejects -/

/-- irCheck on the fixture Surface, evaluated on concrete objects: true on the
    well-formed one, false on a planted rename, false on a memoryguard prologue, false
    on an object with no runtime sub-object. The brief asks for reachability rather than
    well-typedness, and the first line is it. -/
def irCheckKats_ok : Bool :=
  (realSurface.irCheck fxIr) &&
    -- a planted rename fails it
    ! (realSurface.irCheck fxIrRenamed) &&
    -- and so does a memoryguard call: the D-P15 class made visible
    ! (realSurface.irCheck fxIrMemoryguard) &&
    -- an object with no runtime sub-object fails rather than passing vacuously
    ! (realSurface.irCheck (Object.mk "Halo2Verifier" ([] : YulBlock) [] [])) &&
    -- the check is a function of the object, not a constant
    (unresolvedTop fxRuntime == false) && (unresolvedTop fxRuntimeRenamed == true) &&
    (unresolvedTop fxRuntimeMemoryguard == true) &&
    -- astOfMain is reachable too, and refuses the trace render
    (realSurface.astOfMain realSurface.o₀).isSome &&
    ! (realSurface.astOfMain fxOptionsTrace).isSome

#eval irCheckKats_ok                      -- expect true

/-! ### 3. DeploymentW is inhabited, and the memoryguard field bites -/

/-- The memoryguard bound on the fixture layout, as a computation. -/
theorem surfaceMemguardOk : memoryguardOk realSurface.shellLayout.code := by
  simp only [realSurface, fxShellLayout, memoryguardOk, memoryguardValue]
  decide

/-- The deployment, inhabited as a kernel-checked term. vkHash and qHash are the two
    fields a pasted codehash constant would fail: the fixture pins the expected hashes
    to the hash of its own runtime images, so the field is a real equation rather than a
    placeholder, and a wrong constant is a term that does not typecheck. -/
theorem deploymentInhabited :
    DeploymentW realSurface fxW keccak256 fxVkAddr fxQuotientAddr :=
  { keccak := rfl
    wf := ⟨fun a => rfl, rfl⟩
    callvalue := rfl
    static := rfl
    vkImm := fun _ => by native_decide
    vkCode := fun _ => by
      simp [fxW, fxW0, realSurface, fxLowered, fxVkRuntime]
    -- P-RESTORE2: 'by decide' became 'by native_decide'. The payload image grew from two
    -- header words to the reference's thirty-one, and the kernel can no longer reduce the
    -- size comparison inside its recursion budget (maxRecDepth, measured). See fxPayload.
    vkNonEmpty := by native_decide
    vkHash := fun _ h => by
      have := Option.some.inj h
      subst this
      rfl
    qImm := fun _ => by native_decide
    qCode := fun cd h => by
      simp only [realSurface] at h
      have := Option.some.inj h
      subst this
      rfl
    qHash := fun cd _ h1 h2 => by
      simp only [realSurface] at h1 h2
      have := Option.some.inj h1
      subst this
      exact (Option.some.inj h2).symm ▸ rfl
    qNonEmpty := fun cd h => by
      simp only [realSurface] at h
      have := Option.some.inj h
      subst this
      decide
    memguard := surfaceMemguardOk
    disjoint := ⟨by decide, by decide, by decide⟩ }

/-- THE MEMGUARD FIELD IS LOAD-BEARING. Swap the shell prologue for one that raises the
    free-memory pointer above TRANSCRIPT_MPTR and the deployment is no longer
    inhabitable: this is the exhibit that answers the stage-4 blocker, and it is the
    difference between a named gap and a True field. -/
def deploymentMemguardKats_ok : Bool :=
  -- the fixture prologue satisfies the bound
  memoryguardOk realSurface.shellLayout.code &&
    -- a 0x2000 memoryguard does not, and that is the only thing that changed
    ! memoryguardOk ((Midfall.Generator.bytesFromNats
      [0x61, 0x20, 0x00, 0x60, 0x40, 0x52]).data.toList) &&
    -- the immutable pins are separate facts, and they name the right keys
    (fxShellLayout.immutable (litValue (.string "AUTHORIZED_VK")) == fxVkAddr) &&
    (fxShellLayout.immutable (litValue (.string "AUTHORIZED_QUOTIENT")) == fxQuotientAddr) &&
    -- an empty immutable map pins nothing, which is what makes vkImm conditional
    (({ code := []
        dataOffset := fun _ => 0
        dataSize := fun _ => 0 } : EVM.Layout).immutable
        (litValue (.string "AUTHORIZED_VK")) == 0) &&
    -- R-60 S7: the byte-level bound and the AST-level guard are pinned to ONE number.
    -- The shell's head guard reverts above transcriptMptr and the shell's deployed
    -- bytes install 0x80, which is under it; a prologue that ships nothing (none) or
    -- that installs a pointer above the guard's own threshold fails here, which is the
    -- hole the old `memoryguardOk []  =  true` left open.
    (headGuardThreshold realSurface.shell.codeBlock == some transcriptMptr) &&
    (memoryguardValue realSurface.shellLayout.code == some 0x80) &&
    memoryguardOk realSurface.shellLayout.code &&
    -- and a shell whose guard tests a different number is not this shell
    (headGuardThreshold fxHeadGuard == some transcriptMptr)

#eval deploymentMemguardKats_ok           -- expect true

/-! ### 4. The pins are not decoration -/

/-- main_concat, checked rather than assumed: the seven blocks the fixture blk returns
    really do tile the main block, the concatenation is not empty, and the seven slices
    are pairwise distinct so a duplicated or dropped slice is visible. -/
def mainConcatKats_ok : Bool :=
  -- no BEq on Stmt at this dialect (Ast.lean derives Repr only), so the checks are
  -- structural: lengths and the literal each slice stores, not an equality of blocks.
  -- main is the SIX emitted AssemblyHelpers definitions followed by the seven slices:
  -- FORTY-SIX statements. P-AST3a and P-AST3b did NOT change the then-FOURTEEN - the
  -- quotientLin slice and the vkLoading slice are each ONE statement before (a placeholder
  -- mstore) and ONE statement after (a SCOPE), so both conversions are invisible to any
  -- length count and the structural clauses below are the only thing in this gate that can
  -- see them. P-AST4 DOES change it, twice over: four more helper definitions
  -- (transcript_init, common_word, common_uncompressed_g1, squeeze_to) and a transcriptParser
  -- slice that is no longer one statement. Note the size of that slice HERE: TWENTY-NINE, not
  -- the deployed forty-four, because fxPlan carries emptyParserFacts - no phases, no lookups,
  -- no perm products, no lookup helpers, no trashcans, no truncation - and each guard deletes
  -- its own section. That is the six new PlanView fields showing up in main's shape, and it is
  -- why the count is pinned rather than described: at the deployed facts the same expression
  -- gives 61, and GenAst's gate 44 pins that one.
  -- The composition is eight helpers, the one-statement vkLoading scope, the twenty-nine
  -- statement transcriptParser slice, the three-statement Lagrange, the one-statement
  -- quotientLin scope, the one-statement pcs placeholder, the two-statement FinalPairing arm
  -- and the three-statement TraceReturn arm; the pre-P-AST fixture carried seven dummies and
  -- no helpers at all, so a real finalPairing slice could not have resolved fail or ec_pairing.
  realSurface.L.main.length == 47 &&
    -- and the first EIGHT statements really are those definitions, in the template's own
    -- order, i.e. mainScope - which hoists main - can see them: the two EIP-precondition
    -- helpers fail and ec_pairing, the four the parser calls, and the two modexp helpers
    -- P-HELPERS added, scalar_inv where the render puts it and batch_invert where the render
    -- puts it. This is the pin's second conjunct as a computation; P-AST4 widened it from two
    -- names to six and P-HELPERS to eight, and the ORDER is part of it - a permutation of the
    -- helper list now reddens here as well as at GenAst's gate 51.
    (match realSurface.L.main with
     | Stmt.funDef "fail" _ _ _ :: Stmt.funDef "scalar_inv" _ _ _ ::
         Stmt.funDef "transcript_init" _ _ _ :: Stmt.funDef "common_word" _ _ _ ::
         Stmt.funDef "common_uncompressed_g1" _ _ _ :: Stmt.funDef "squeeze_to" _ _ _ ::
         Stmt.funDef "batch_invert" _ _ _ :: Stmt.funDef "ec_pairing" _ _ _ :: _ => true
     | _ => false) &&
    -- THE VKLOADING CLAUSE (P-AST3b), structural for the same reason the quotientLin one
    -- below is: the placeholder it replaced was one statement and the real slice is one
    -- statement, so main's LENGTH cannot see this conversion either. What can: a scope of
    -- THIRTEEN with the extcodecopy at index 1 and no loop, and the HAS_ACCUMULATOR cross-
    -- check carrying the FIXTURE's own derived word - 0 here because realSurface.cfg
    -- .accumulator is none, which is the derivation and not four typed zeros;
    -- planAccExpectationsKats_ok is what says so.
    (match realSurface.blk Partial.vkLoading realSurface.plan with
     | [Stmt.block body] =>
         body.length == 13 && (body.filter GenAst.stmtIsFor).length == 0 &&
         (match body[1]? with
          | some (Stmt.exprStmt (Expr.builtin Op.extcodecopy
              [Expr.var "vk", Expr.var "VK_MPTR", Expr.lit (Literal.number 1),
               Expr.var "EXPECTED_VK_PAYLOAD_LENGTH"])) => true
          | _ => false) &&
         (match body[4]? with
          | some (Stmt.assign ["success"]
              (Expr.builtin Op.and [Expr.var "success",
                Expr.builtin Op.eq
                  [Expr.builtin Op.mload [Expr.var "HAS_ACCUMULATOR_MPTR"],
                   Expr.lit (Literal.number 0)]])) => true
          | _ => false)
     | _ => false) &&
    -- the four partials the emitter implements are NOT one-statement dummies: the deployed
    -- FinalPairing arm is the precompile guard and the swapped ec_pairing call, the Lagrange
    -- slice is the MF-4 flag, the 28-statement computation scope and the section boundary,
    -- the quotientLin slice is a nine-statement scope, and TraceReturn is the guard, the
    -- ABI-true store and the terminal return.
    (realSurface.blk Partial.finalPairing realSurface.plan).length == 2 &&
    (realSurface.blk Partial.lagrange realSurface.plan).length == 3 &&
    (realSurface.blk Partial.quotientLin realSurface.plan).length == 1 &&
    (realSurface.blk Partial.traceReturn realSurface.plan).length == 3 &&
    -- THE QUOTIENTLIN CLAUSE, and the reason it is structural and not a count: one
    -- statement that is a scope of NINE, holding exactly one for-loop and the two-word
    -- QUOTIENT_MPTR payload in the template's order, at the FIXTURE's own k (2, not the
    -- deployed 6 - so a slice hard-coded to the artifact's constant would pass gate 25 and
    -- fail here). The placeholder is one statement too; it is a flat mstore and matches none
    -- of this.
    (match realSurface.blk Partial.quotientLin realSurface.plan with
     | [Stmt.block body] =>
         body.length == 9 && (body.filter GenAst.stmtIsFor).length == 1 &&
         (match body[1]? with
          | some (Stmt.letDecl ["k"] (some (Expr.lit (Literal.number 2)))) => true
          | _ => false) &&
         (match body[7]? with
          | some (Stmt.exprStmt (Expr.builtin Op.mstore
              [Expr.var "QUOTIENT_MPTR", Expr.var "x_split"])) => true
          | _ => false)
     | _ => false) &&
    -- and the Lagrange scope really is a scope with loops in it, not three flat statements:
    -- the fixture's own plan (k = 2, seven negative rotations) is what this measures, so a
    -- placeholder that merely had three statements would still fail here.
    (match realSurface.blk Partial.lagrange realSurface.plan with
     | _ :: Stmt.block body :: _ =>
         body.length == 28 && (body.filter GenAst.stmtIsFor).length == 5
     | _ => false) &&
    (List.zipIdx [Partial.vkLoading, Partial.transcriptParser, Partial.lagrange,
        Partial.quotientLin, Partial.pcs, Partial.finalPairing,
        Partial.traceReturn]).all
      -- each slice is nonempty, and no two slices are the same statement, so a duplicated
      -- or dropped partial is visible. Compared through Repr because Stmt carries no BEq
      -- at this dialect (Ast.lean derives Repr only).
      fun (q, _i) => ((fxPartialBlocks q).length > 0 || q == Partial.pcs) &&
        (List.zipIdx [Partial.vkLoading, Partial.transcriptParser, Partial.lagrange,
            Partial.quotientLin, Partial.pcs, Partial.finalPairing,
            Partial.traceReturn]).all
          fun (q2, _j) => q == q2 ||
            toString (fxPartialBlocks q) != toString (fxPartialBlocks q2)

#eval mainConcatKats_ok                   -- expect true

/-- The lower pin bites: production options give the program, a trace render is
    refused. A lower that returned .ok for every option would satisfy lower_ok while o0
    pinned nothing about L. The count was 14 through P-AST3a and P-AST3b and that was a
    measurement and not an oversight: the quotientLin and vkLoading slices are each one
    statement before their conversion (a flat mstore) and one after (a scope), so main's
    LENGTH could not see either - mainConcatKats_ok's structural clauses are what could, and
    they are the gates that redden when the emitter ignores its plan (measured: hard-coding
    k = 6 in emitQuotientLinAt flips mainConcatKats_ok and blkPinKats_ok to false while this
    gate stays green, because 14 was still 14). P-AST4 moves the number to 46, and it moves
    for TWO reasons at once - four more helper definitions and a parser slice that grew from
    one statement to twenty-nine - so this gate can now see the transcriptParser conversion by
    length alone. That is the easy direction and it is stated as the easy direction: the two
    conversions this gate still CANNOT see are quotientLin and vkLoading, and the
    transcriptParser placeholder plant is a stmtsBeq exhibit for the same reason. -/
def lowerPinKats_ok : Bool :=
  (match fxLower fxOptions with | .ok l => l.main.length == 47 | .error _ => false) &&
    (match fxLower fxOptionsTrace with | .ok _ => false | .error _ => true) &&
    (match realSurface.lower realSurface.o₀ with
     | .ok l => l.main.length == 47 | .error _ => false)

#eval lowerPinKats_ok                     -- expect true

/-- The codec-side clause of SupportedS does real work: the identity point passes and a
    non-identity exponent does not, so vkPoints is a constraint on the payload rather
    than a formality. -/
def fxToEip : RP → Bytes := (expG1Codec (p := rp)).toEip

def vkPointsKats_ok : Bool :=
  (match Midfall.Yul.g1Of? (fxToEip (1 : RP)) with
   | some pt => Midfall.Yul.g1PointMsmValid pt
   | none => false) &&
    (match Midfall.Yul.g1Of? (fxToEip (fx 3)) with
     | some pt => ! Midfall.Yul.g1PointMsmValid pt
     | none => true)

#eval vkPointsKats_ok                     -- expect true

/-- The two codehash fields are equations and not placeholders: the pinned constant is
    the hash of the runtime image, and a wrong word is a different word. -/
def codehashKats_ok : Bool :=
  realSurface.expectedVkCodehash == some (keccak256 fxVkRuntime) &&
    realSurface.expectedQuotientCodehash == some (keccak256 fxQuotientRuntime) &&
    realSurface.expectedVkCodehash != some 0 &&
    realSurface.L.vkRuntime.size > 0 &&
    -- the 0xfe prefix is there, which is what vkRuntime_spec pins
    realSurface.L.vkRuntime.data[0]? == some 0xfe

#eval codehashKats_ok                     -- expect true

/-! ### 5. The R-58 pins, each with its refutation -/

/-- R-58 F3. The shell pin is a decision about two fields, not a definition of one:
    the shell code block equals headGuard ++ bindLocals ++ main (line 1, which is why
    the field discharges by rfl), and a shell that carries only the main block - the
    shape `shell` had when nothing constrained it - refutes it (line 2). Line 3 says
    the head guard is really in the comparison, so a pin that dropped it would show
    up here. Compared through Repr because Stmt carries no BEq at this dialect. -/
def shellPinsKats_ok : Bool :=
  toString realSurface.shell.codeBlock ==
    toString (fxArmOf realSurface.L.main) &&
    -- the ARM form, not the raw concatenation: the pin cites the embedding, so a shell carrying the
    -- uninlined fragment - which is what made RunShell empty - refutes it (D-P39)
    ! (toString (realSurface.L.headGuard ++ realSurface.bindLocals ++ realSurface.L.main) ==
      toString (fxArmOf realSurface.L.main)) &&
    ! (toString fxMain ==
      toString (realSurface.L.headGuard ++ realSurface.bindLocals ++ realSurface.L.main)) &&
    ! (toString fxMain == toString (fxHeadGuard ++ fxMain)) &&
    -- and the pin is about THIS shell: a shell built from a different main refutes it
    ! (toString (YulSemantics.Object.codeBlock
        (Object.mk "Halo2Verifier" (fxArmOf (fxMain.drop 1)) [] [] : YulObject)) ==
      toString (fxArmOf realSurface.L.main))

#eval shellPinsKats_ok                    -- expect true

/-- The evaluator the render says it produced: an object whose code block is fxRuntime. -/
def evRendered : Option YulObject := some (Object.mk "ev" fxRuntime [] [])

/-- The evaluator the deployment would answer staticcalls with: the SAME presence, a
    DIFFERENT block (the planted-rename runtime). R-60 S3: agreeing on isSome while
    disagreeing here is the defeat the strengthened pin closes. -/
def evDeployed : Option (YulBlock × EVM.Layout) := some (fxRuntimeRenamed, fxShellLayout)

/-- R-58 F2 and F6. Each of the three plan/render pins is an equation between two
    fields, and each line pair shows both halves: the two sides agree at the fixture,
    and the value one side COULD have had refutes it. The second line of each pair is
    the lie the review demonstrated - a PlanView with hasAccumulator := true while
    cfg.accumulator is none, a plan claiming two instances while cfg says one, a
    deployment carrying an evaluator runtime the render never produced. A Surface
    that lied like that cannot be written any more, which is what the pin buys. -/
def planPinsKats_ok : Bool :=
  realSurface.plan.hasAccumulator == realSurface.cfg.accumulator.isSome &&
    ! (true == realSurface.cfg.accumulator.isSome) &&
    realSurface.plan.numInstances == realSurface.cfg.numInstances &&
    ! (realSurface.plan.numInstances == 2) &&
    -- R-60 S3: the evaluator pin is an equation between RUNTIME BLOCKS now, so its
    -- refutation is a block mismatch and not an isSome mismatch. evRendered and
    -- evDeployed below are the pair the OLD pin let through: an evaluator the render
    -- produced and a DIFFERENT one the deployment answers staticcalls with. Both are
    -- present, so isSome agreed and the blocks did not. The last line is the fixture
    -- itself: both sides none, so the pin is rfl and the two really are the same
    -- (non-)evaluator.
    (evRendered.isSome == evDeployed.isSome) &&
    ! (SyntaxEq.stmtsBeq ((evRendered.map Object.codeBlock).getD [])
      ((evDeployed.map Prod.fst).getD [])) &&
    (match realSurface.L.evaluator.map Object.codeBlock,
        realSurface.evaluatorRuntime.map Prod.fst with
      | none, none => true
      | _, _ => false)

#eval planPinsKats_ok                     -- expect true

/-- P-AST3b, THE FOUR ACCUMULATOR WORDS AND THE PIN THAT RELATES THEM TO cfg, each half as
    a computation. Line 1: the fixture's four words ARE accWordsOfEncoding applied to its
    own cfg.accumulator - the same function the constructor used, so the pin is rfl and not
    a coincidence. Line 2: the deployed profile's configuration is none, so the four words
    are the artifact's zeros BECAUSE the derivation says so. Line 3 is THE LIE, forward: a
    plan carrying offset 7 while cfg says none refutes the pin, which is what makes the
    four fields constrained data rather than four free Nats. Lines 4-5 are the lie in the
    OTHER direction, and the one that matters for this package: a plan built from a REAL
    accumulator encoding carries 1 / 2 / 7 / 56 and not the deployed zeros, so a converter
    that hard-coded four zeros would be caught by the pin and by GenAst's
    emitVkLoadingAccWordsDerived_ok rather than by a reviewer's reading of a comment.
    Line 6: the two spellings of "is there an accumulator" - the Bool Inv reads and the Nat
    the template interpolates - agree at the fixture, which is automatic only because both
    come out of one match on one Option. -/
def planAccExpectationsKats_ok : Bool :=
  let words (pv : PlanView) : Nat × Nat × Nat × Nat :=
    (pv.expectedHasAccumulatorWord, pv.expectedAccOffset,
      pv.expectedNumAccLimbs, pv.expectedNumAccLimbBits)
  words realSurface.plan ==
    Midfall.Lowering.accWordsOfEncoding realSurface.cfg.accumulator &&
    realSurface.cfg.accumulator == none &&
    words realSurface.plan == (0, 0, 0, 0) &&
    ! (words { realSurface.plan with expectedAccOffset := 7 } ==
        Midfall.Lowering.accWordsOfEncoding realSurface.cfg.accumulator) &&
    (let acc := some (Midfall.Generator.AccumulatorEncoding.new 2 7 56)
      let pv := Midfall.Lowering.planViewWithAccumulator
        (vk := fxPayload)
        (vkMptr := Midfall.Generator.LayoutMemoryKats.poseidonLayout.vkMptr)
        (memory := Midfall.Generator.LayoutMemoryKats.poseidonLayout)
        (proofLayout := Midfall.Generator.poseidonProofLayout)
        (numInstances := 1) (k := 2) (numNegLagranges := 7)
        (acc := acc) (facts := Midfall.Lowering.emptyParserFacts)
        (meta_ := Midfall.Generator.constraintSystemMetaDefault) (dat := fxPlanData);
      words pv == Midfall.Lowering.accWordsOfEncoding acc &&
        words pv == (1, 2, 7, 56) &&
        words pv != (0, 0, 0, 0) &&
        ! (words pv == Midfall.Lowering.accWordsOfEncoding none)) &&
    (realSurface.plan.expectedHasAccumulatorWord ==
      if realSurface.plan.hasAccumulator then 1 else 0)

#eval planAccExpectationsKats_ok          -- expect true
/-! ### P-RESTORE3: the restored hProofLayout pin, exhibited and perturbed -/

/-- The witness as a computation: does the generator, at the ABI proof pointer and these
    counts, produce EXACTLY the layout the fixture plan carries? Bool so a gate can read
    it; the Prop form is the Surface field itself. -/
def fxFromProtocolIsFixtureLayout (protocol : ProtocolPlan) (numEvals numPointSets : Nat) : Bool :=
  match ProofCalldataLayout.fromProtocol protocol abiVerifyProofProofCptr numEvals numPointSets with
  | .ok L => L == fxPlan.proofLayout
  | .error _ => false

/-- D-P23, BOTH HALVES, AND THE LIMIT WITH THEM.

    WITNESS (first three conjuncts): the poseidon counts produce the fixture layout, and
    the two Surfaces in the tree carry that layout, so 'realSurface.hProofLayout' and
    'curveSurface.hProofLayout' are inhabited by 'rfl' on 'fxProofProtocol'. This is not
    a self-round-trip: the right-hand side is transcribed from the deployed dump's own
    'add(proof_cptr, 0x..)' lines and the left-hand side is what the ported Rust
    generator computes from the counts, so agreement is a cross-check between two
    independent channels.

    FALSIFICATION (the rest): the witness is not free. Dropping an advice commitment,
    a permutation product, a trashcan, a quotient limb, a lookup chunk, the eval count
    or the point-set count each changes the produced layout, so no conjunct of the
    witness equation is satisfied by accident.

    WHAT THIS DOES NOT CLAIM, said plainly because the last package was told to claim no
    coverage it does not have: no Surface that FAILS the pin is exhibited. Refuting the
    existential needs an inversion lemma for 'fromProtocol' (its output's 'proofCptr' is
    the pointer it was handed), and this package did not prove one - the do-block's match
    tower defeated 'split at h' after four attempts. What IS proved instead, as the two
    theorems below, is the consequence the pin exists to keep out, which is the part that
    matters for vacuity: at a layout that breaks either guard the decoder answers 'none'
    for EVERY calldata, so 'hcd' is unsatisfiable and every spec that takes it is true
    because nothing decodes. -/
def hProofLayoutKats_ok : Bool :=
  fxFromProtocolIsFixtureLayout fxProofProtocol 48 3 &&
  (realSurface.plan.proofLayout == fxPlan.proofLayout) &&
  -- the three witnesses are each pinned
  (! fxFromProtocolIsFixtureLayout fxProofProtocol 47 3) &&
  (! fxFromProtocolIsFixtureLayout fxProofProtocol 49 3) &&
  (! fxFromProtocolIsFixtureLayout fxProofProtocol 48 2) &&
  (! fxFromProtocolIsFixtureLayout fxProofProtocol 48 4) &&
  -- and every count the protocol carries is pinned
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [7] [1] 3 1 4) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [9] [1] 3 1 4) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [1] 2 1 4) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [1] 4 1 4) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [1] 3 0 4) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [1] 3 2 4) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [1] 3 1 3) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [1] 3 1 5) 48 3) &&
  (! fxFromProtocolIsFixtureLayout (AbiKats.protocolShape [8] [2] 3 1 4) 48 3) &&
  -- a skewed layout is not what the witness produces, and the skew is the guard the pin
  -- vouches against: proofEnd is not proofCptr + proofLen
  (match ProofCalldataLayout.fromProtocol fxProofProtocol abiVerifyProofProofCptr 48 3 with
   | .ok L => L != { fxPlan.proofLayout with proofLen := 7 }
   | .error _ => false)

#eval hProofLayoutKats_ok                 -- expect true

/-- THE CONSEQUENCE THE PIN KEEPS OUT, as a theorem and not a paragraph, first half: a
    layout whose proof pointer is not the ABI one decodes NOTHING - the second guard of
    'decodeCalldata' fails before any byte is read. This is what 'hcd' would mean at such
    a Surface: an unsatisfiable hypothesis, and ten specs that hold because no calldata
    ever decodes. -/
theorem decodeCalldata_none_of_pointer_mismatch (L : ProofCalldataLayout)
    (h : L.proofCptr ≠ abiVerifyProofProofCptr) (cd : Bytes) :
    decodeCalldata (p := rp) L realSurface.cfg.numInstances realSurface.E.g1 cd = none := by
  unfold decodeCalldata
  simp [h]

/-- Second half: a layout whose length word and proof region disagree - the hand-built
    case attack.md's calldata_canonical FIX is about, and the one the pin's witness
    equation rules out for a generator-produced layout. -/
theorem decodeCalldata_none_of_len_skew (L : ProofCalldataLayout)
    (h : L.proofEnd ≠ L.proofCptr + L.proofLen) (cd : Bytes) :
    decodeCalldata (p := rp) L realSurface.cfg.numInstances realSurface.E.g1 cd = none := by
  unfold decodeCalldata
  simp [h]

/-- And the fixture's own layout satisfies both guards the pin vouches for, by
    computation and not by inspection of the transcription. -/
theorem fixtureLayout_satisfies_the_guards :
    fxPlan.proofLayout.proofCptr = abiVerifyProofProofCptr ∧
    fxPlan.proofLayout.proofEnd = fxPlan.proofLayout.proofCptr + fxPlan.proofLayout.proofLen ∧
    (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).repackedLen =
      fxPlan.proofLayout.proofLen := ⟨rfl, rfl, rfl⟩

/-! ### P-RESTORE3: the '*_faithful' obligation, stated where it can be stated -/

/-- The message list the deployment's own slot schedule names: one message per slot,
    the identity in every G1 slot and zero in every scalar slot. 72 slots, so a dropped
    or duplicated slot changes the length and every byte after it. -/
def fxSlotWitnessMsgs : List (Msg (Fr rp) RP) :=
  (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).slots.map fun s =>
    match s with
    | WireSlot.g1 => Msg.g1 (1 : RP)
    | WireSlot.fr => Msg.fr (0 : Fr rp)

/-- The compressed proof stream fxSlotWitnessMsgs repacks to: 48 bytes per G1 slot, 32
    little-endian bytes per scalar slot, in the plan's order. -/
def fxCompressedProof : Bytes :=
  (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).slots.foldl
    (fun (acc : Bytes) (s : WireSlot) =>
      acc ++ match s with
        | WireSlot.g1 => realSurface.E.g1.toCompressed (1 : RP)
        | WireSlot.fr => Midfall.natToBytesLE 0 32)
    Midfall.Bytes.empty

/-- The two byte strings the faithfulness claims are about: the full calldata the model
    builds for the deployment's layout, and the repacked proof region inside it. -/
def fxLayoutCalldata : Bytes :=
  calldataOf (p := rp) realSurface.E.g1 fxSlotWitnessMsgs [BitVec.ofNat 256 1]

def fxLayoutRepacked : Bytes :=
  encodeContractProof (p := rp) realSurface.E.g1 fxSlotWitnessMsgs

/-- THE encodeCalldata_faithful OBLIGATION, in the only form the tree can state. The
    sketch (Q:2285) wrote 'S.encodeCalldata pi inst = Midfall.Lowering.encodeCalldata
    ...' - a pin from a Surface codec field to the spec function. Stage 4 deleted the
    codec fields (Surface.lean deviation 2), so that left-hand side does not exist and
    the literal field is unstatable; what the obligation MEANS - the calldata the model
    builds is the calldata the model's decoder reads back, AT THE DEPLOYMENT'S OWN
    LAYOUT, instance count and codec - is stated and exhibited here. Four conjuncts:
    the envelope decodes; it is the artifact's own 4484 bytes (the poseidon dump's
    calldata size, Generator/Calldata.lean:844), so the layout is not a toy; the slot
    schedule is the layout's; and the head words the decoder guards on are the ones the
    encoder wrote. -/
def encodeCalldata_faithful_at_layout : Bool :=
  (decodeCalldata (p := rp) fxPlan.proofLayout realSurface.cfg.numInstances realSurface.E.g1
    fxLayoutCalldata).isSome &&
  fxLayoutCalldata.size == 4484 &&
  (fxSlotWitnessMsgs.map Msg.slot).length ==
    (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).slots.length &&
  (cdWord fxLayoutCalldata 4).toNat == 0x40 &&
  (cdWord fxLayoutCalldata 0x44).toNat == fxPlan.proofLayout.proofLen &&
  (cdWord fxLayoutCalldata fxPlan.proofLayout.proofEnd).toNat == realSurface.cfg.numInstances

#eval encodeCalldata_faithful_at_layout -- expect true

/-- THE repackProof_faithful OBLIGATION, same treatment (sketch Q:2283). repackProof at
    the deployment's plan produces exactly the contract bytes of the messages decodeWire
    reads from the same stream - the wire-level half of repack_spec_wire, instantiated at
    the layout the contract is deployed with rather than at the 4-slot KAT plan. -/
def repackProof_faithful_at_layout : Bool :=
  (match repackProof (p := rp)
          (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout) realSurface.E.g1
          fxCompressedProof with
   | .ok out => out == fxLayoutRepacked
   | .error _ => false) &&
  (decodeWire (p := rp)
      (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout) realSurface.E.g1
      fxCompressedProof).map (fun ms => ms.length) == some 72 &&
  fxCompressedProof.size =
    (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).compressedLen &&
  fxLayoutRepacked.size =
    (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).repackedLen

#eval repackProof_faithful_at_layout    -- expect true

/-- THE FALSIFICATION HALF FOR BOTH, and it is a refutation and not a perturbation:
    delete a slot from the schedule and the stream no longer repacks to the contract
    bytes of the message list; drop the last byte of the calldata and the decoder
    refuses it. A faithfulness claim nothing could break would be the decoration the
    brief names, so each is shown to bite. -/
def faithfulnessRefutations_ok : Bool :=
  -- a truncated calldata: the size guard is the last defence, since calldataload pads
  (! (decodeCalldata (p := rp) fxPlan.proofLayout realSurface.cfg.numInstances
        realSurface.E.g1 ((bytesTake fxLayoutCalldata 0 4483).getD Midfall.Bytes.empty)).isSome) &&
  -- a calldata with one trailing byte: EXACT in both directions, so this too refuses
  (! (decodeCalldata (p := rp) fxPlan.proofLayout realSurface.cfg.numInstances
        realSurface.E.g1 (fxLayoutCalldata ++ Midfall.natToBytesBE 0 1)).isSome) &&
  -- a compressed stream one word short: the exact-length guard fires
  (match repackProof (p := rp)
          (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout) realSurface.E.g1
          ((bytesTake fxCompressedProof 0 2608).getD Midfall.Bytes.empty) with
   | Except.error _ => true
   | Except.ok _ => false) &&
  -- and the message list is not the empty one, so the walk is real and not a zero-case
  (fxSlotWitnessMsgs.length == 72) && (fxCompressedProof.size == 2640)

#eval faithfulnessRefutations_ok        -- expect true

/-! ### P-MC-CALLDATA: the four exhibits above that became THEOREMS

    The Bool gates stay, because a gate is what a CI run can read. What is new is that
    three of their conjuncts are now propositions proved by the kernel rather than by
    the interpreter, and one of them is the anti-vacuity claim the whole 'hcd' layer
    rests on. -/

/-- **THE CHAIN CLOSES AT THE DEPLOYMENT'S OWN LAYOUT.** 'hcd' - the hypothesis of all
    ten partial specs, of 'LeanAccepts' and of all three side conditions - is
    SATISFIABLE at the real 4484-byte calldata over the real 72-slot layout. This is
    the theorem form of the first conjunct of 'encodeCalldata_faithful_at_layout', and
    it is what 'Surface.hProofLayout' was restored to make provable: without the two
    guards 'decodeCalldata' insists on, 'hcd' would be an unsatisfiable hypothesis and
    every spec that takes it would be true because nothing decodes. -/
theorem hcd_satisfiable_at_deployment :
    (decodeCalldata (p := rp) fxPlan.proofLayout realSurface.cfg.numInstances
      realSurface.E.g1 fxLayoutCalldata).isSome := by
  native_decide

/- The same claim at the toy layout this file's decoder KATs are built on, so the
    anti-vacuity witness exists at BOTH sizes. It lives here and not in
    `Midfall/Lowering/Calldata.lean` only because reducing the toy bytes needs
    `native_decide`, which the confinement gate keeps out of theorem-bearing files;
    the portable half of the same story (`decodeCalldata_none_of_layout_skew`,
    `decodeCalldata_none_of_pointer_skew`, `decodeCalldata_hend_of_some`) is
    proved by unfolding alone and stays there. -/

section ToyCalldataWitnesses
local instance cdFact17 : Fact (Nat.Prime 17) := ⟨by decide⟩
open Midfall.Lowering Midfall.Lowering.CdKats

theorem hcd_satisfiable_toy :
    (decodeCalldata (p := 17) katLayout 1 toyCodec
       (calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 7])).isSome := by
  native_decide

/-- Refutation companion: an over-long compressed stream is rejected by BOTH sides of
    `repack_spec_wire`, which is the arm the iff loses if `decodeWire` drops
    its exact-length guard. Perturbation evidence: with that guard deleted, this is the
    theorem `native_decide` refutes. -/
theorem repack_wire_refuted_length_toy :
    (decodeWire (p := 17) katPlan toyCodec
       (katCompressed ++ Midfall.natToBytesLE 1 32)).isNone := by
  native_decide
end ToyCalldataWitnesses

/-- The same two guards, for the same layout, as a CONSEQUENCE of
    'proofLen_eq_repackedLen' rather than as a computation over a transcription. The
    difference matters: 'fixtureLayout_satisfies_the_guards' checks the numbers this
    package transcribed from the deployed dump, while this says any layout the
    generator produces at the ABI pointer satisfies them, so the pin's witness cannot
    be the only layout for which the decoder is usable. -/
theorem fixtureLayout_guards_from_theorem :
    fxPlan.proofLayout.proofCptr = abiVerifyProofProofCptr ∧
      fxPlan.proofLayout.proofLen =
        (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout).repackedLen ∧
      fxPlan.proofLayout.proofEnd =
        fxPlan.proofLayout.proofCptr + fxPlan.proofLayout.proofLen := by
  obtain ⟨h1, h2⟩ := Midfall.Lowering.proofLen_eq_repackedLen fxProofProtocol 48 3
    fxPlan.proofLayout rfl
  exact ⟨rfl, h1, h2⟩

/-- The theorem form of 'repackProof_faithful_at_layout''s first conjunct: at the
    deployment's plan the repacker's output IS the contract bytes of the message list
    the schedule decodes to. Spelled as a match because 'Except' over 'RepackError'
    carries no BEq, so the equation is not directly decidable. -/
theorem repackProof_faithful_at_layout_is_ok :
    (match repackProof (p := rp)
          (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout) realSurface.E.g1
          fxCompressedProof with
     | .ok out => out == fxLayoutRepacked
     | .error _ => false) = true := by
  native_decide

/-- And the decodeWire half of the same claim, at the deployment's 72 slots rather
    than at the 4-slot KAT plan. -/
theorem decodeWire_faithful_at_layout_is_ok :
    (decodeWire (p := rp)
        (RepackedProofLayoutPlan.fromProofLayout fxPlan.proofLayout) realSurface.E.g1
        fxCompressedProof).map (fun ms => ms.length) == some 72 := by
  native_decide

/-- R-58 G2. The encoder now returns EIP-2537-shaped bytes for every point, and the
    value it replaced - the empty byte string - does not, so the pin is what forced
    the change rather than a note next to it.

    THE HONEST HALF, stated because the review asked for the field to be exhibited
    and it still is not: fixing encG2 does NOT make `Eip2537.Holds` satisfiable at
    this Surface. The blocking clause at THIS codec is g1Valid, not g2Valid - the
    exponent codec sends a non-identity exponent to bytes no curve check accepts
    (last line below, the same fact vkPointsKats_ok uses to show the clause bites).
    Re-pointed by P-GAPFIX, because the reason this note used to give for there being
    no replacement codec is no longer true: D-P1/R-28 said the tree has no BLS12-381
    model, and it now has one whose codec discharges all four G1-side clauses
    (g1CodecZ_g1_four). What the tree still has no instance of is a curve
    AdmissiblePairing (D-P36), and since VerifierEnv.g1 is typed over the Surface's own
    pairing, that is what keeps the exponent codec installed here. So every field that
    carries Holds is still unexhibited, for a named reason that is a model and not a
    missing pin - just a different model than this note claimed. encG2_shape removed ONE
    cause of that; it did not remove the only cause. -/
def encG2AtFixture_ok : Bool :=
  encG2IsEip (realSurface.encG2 (fx 5)) && encG2IsEip (realSurface.encG2 (fx 0)) &&
    -- R-60 S4, the limitation as a computation: the pin is met by a CONSTANT encoder,
    -- which is what this fixture uses, so encG2_shape constrains the bytes and not the
    -- map. Function.Injective encG2 is the strengthening this pin does not make and
    -- this fixture cannot meet - a named gap, not a satisfied claim.
    (realSurface.encG2 (fx 5) == realSurface.encG2 (fx 0)) &&
    ! (encG2IsEip Midfall.Bytes.empty) &&
    -- the remaining blocker: a non-identity exponent is not a curve point
    (match Midfall.Yul.g1Of? (fxToEip (fx 3)) with
     | some pt => ! Midfall.Yul.g1PointMsmValid pt
     | none => true)

#eval encG2AtFixture_ok                   -- expect true

/-- R-58 F7. The table carries the -G row, so the existence conjunct of
    accFixedBases_producer is exhibited here instead of being proved vacuous (the
    old gate in ObligationsGates.lean did the latter). Line 2 is the refutation: the
    one-entry table this fixture used to have fails the existence test. -/
def accFixedBasesKats_ok : Bool :=
  realSurface.accFixedBases.toList.map (fun b => b.name) == ["-G", "b0"] &&
    (realSurface.accFixedBases.toList.any fun b => b.name == "-G" && b.negate) &&
    ! ((#[{ name := "b0", base := (1 : RP), negate := false }]
        : Array (AccFixedBase RP)).toList.any fun b => b.name == "-G")

#eval accFixedBasesKats_ok              -- expect true

/-- R-58 F8. render_eq_print at the fixture: astOfMain IS lower.map main for every
    option, including the two the render refuses, which is the case the old
    conjunct could not see (an option with no `L` contributes nothing). Line 3 is
    the refutation the old form allowed: an accessor that answers some for a refused
    option. -/
def renderEqPrintPinKats_ok : Bool :=
  -- compared through Repr: Stmt has no BEq at this dialect, so the equation is
  -- displayed and matched as text rather than decided as a list.
  toString (realSurface.astOfMain realSurface.o₀) ==
    toString ((match realSurface.lower realSurface.o₀ with
      | .ok l => some l.main | .error _ => none) : Option YulBlock) &&
    toString (realSurface.astOfMain fxOptionsTrace) ==
    toString ((match realSurface.lower fxOptionsTrace with
      | .ok l => some l.main | .error _ => none) : Option YulBlock) &&
    -- and the option that separates the two shapes: a gas-checkpoint render with
    -- trace OFF. fxLower refuses it, so the pin demands none; the old accessor keyed
    -- only on trace and answered some fxMain, which is the refutation.
    (realSurface.astOfMain fxOptionsGas).isNone &&
    ! (toString ((if fxOptionsGas.diagnostics.trace then none else some fxMain : Option YulBlock)) ==
      toString ((match fxLower fxOptionsGas with
        | .ok l => some l.main | .error _ => none) : Option YulBlock))

#eval renderEqPrintPinKats_ok           -- expect true

/-! ### 6. The blk pin (R-62): inhabited, and it bites -/

/-- THE SATISFIABILITY WITNESS FOR THE PIN (D-P23, first half). BlkIsEmitter holds of the
    fixture as a kernel-checked term with no tactic in it, because the fixture's blk IS
    GenAst.emitPartial and its main IS GenAst.emitMain. That is the point of wiring the
    emitter into the record rather than describing it: a pin the only Surface in the tree
    cannot satisfy would make all ten *_spec theorems vacuous, which is the failure class
    this programme keeps hitting. -/
theorem blkPinInhabited : BlkIsEmitter realSurface := ⟨fun _q _pv => rfl, rfl⟩

/-- R-62's counterexample block: the slice RETURNS instead of verifying. A run of this
    halts with a return record, so it is neither a revert nor a normal exit into the next
    checkpoint, which is what refutes the conclusion of finalPairing_spec - and it is
    exactly what the pin now excludes. -/
def plantReturnBlock : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.ret [Expr.lit (.number 0), Expr.lit (.number 0)])]

/-- The plant: blk .finalPairing returns, every other slice is the emitter's. -/
def plantBlkCounterexample : Partial → PlanView → YulBlock
  | .finalPairing, _ => plantReturnBlock
  | q, pv => GenAst.emitPartial pv q

/-- The replanted main. main is free - it comes from lower - so a planted blk has to move
    main with it for the Surface to be a Surface at all. That is the whole defect: nothing
    in the record could tell the difference before the pin existed. -/
def plantMainCounterexample : YulBlock :=
  GenAst.emitHelpers fxPlan ++
    Midfall.Lowering.partials.foldl (init := [])
      fun acc q => acc ++ plantBlkCounterexample q fxPlan

def plantLowered : Lowered := { fxLowered with main := plantMainCounterexample }

/-- The render of the planted program: refuses the same two options fxLower refuses, so
    lower_ok, astOfMain and SupportedS.production all still behave. -/
def plantLower (o : RenderOptions) : Except Midfall.Generator.GeneratorError Lowered :=
  if o.diagnostics.trace || o.diagnostics.gasCheckpoints then
    .error Midfall.Generator.GeneratorError.noAdviceColumns
  else
    .ok plantLowered

def plantShellCounterexample : YulObject :=
  Object.mk "Halo2Verifier" (fxArmOf plantMainCounterexample) [] []

/-- THE COUNTEREXAMPLE SURFACE, as a genuine Surface: every field of the record still
    discharges - main_concat with the emitted helpers, shell_unfolds, lower_ok - and
    SupportedS still holds of it (next theorem), so the pin is the ONLY thing in the
    hypothesis bundle that excludes it. -/
def plantCounterexampleSurface : Surface rp RP RP RP :=
  { realSurface with
    blk := plantBlkCounterexample, L := plantLowered, lower := plantLower,
    shell := plantShellCounterexample,
    astOfMain := fun o => match plantLower o with
      | .ok l => some l.main | .error _ => none,
    lower_ok := rfl,
    main_concat := ⟨GenAst.emitHelpers fxPlan, rfl⟩,
    shell_unfolds := rfl }

/-- THE PIN IS NOT REDUNDANT. Every hypothesis of finalPairing_spec that this fixture can
    exhibit at all still holds of the planted Surface: SupportedS is unchanged, because
    none of the ten fields it reads mentions blk or main. So the plant is not excluded by
    anything that was in the bundle before P-AST - which is precisely R-62's claim - and
    it is excluded by the pin alone. -/
theorem plantedStillSupported :
    SupportedS plantCounterexampleSurface plantCounterexampleSurface.o₀ := by
  -- The same ten fields supportedInhabited discharges, discharged again here rather than
  -- transported by a congruence lemma: every one of them reads vk, cfg, plan, E or o₀, and
  -- the plant changes none of those - it changes blk, L, lower, shell and astOfMain. A
  -- transport lemma would have been nicer, but SupportedS carries the section's nine
  -- instance arguments and the two statements do not unify up to them, so the direct
  -- exhibit is the honest one. Each bullet is a computation on the plant's own projections.
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantCounterexampleSurface, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantCounterexampleSurface, realSurface, fxVk, List.mem_append,
        List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- THE PIN BITES, on R-62's own plant (D-P23, second half). -/
theorem blkPinBitesCounterexample : ¬ BlkIsEmitter plantCounterexampleSurface := by
  intro h
  have h1 := h.1 Partial.finalPairing fxPlan
  have h4 : SyntaxEq.stmtsBeq (plantCounterexampleSurface.blk Partial.finalPairing fxPlan)
      plantReturnBlock = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.finalPairing)
      plantReturnBlock = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- THE PIN IS NOT IMPLIED BY main_concat, which is the only constraint the record used to
    carry on blk. The boundary plant moves the join between the lagrange and quotientLin
    slices and nothing else: main is UNCHANGED, so main_concat holds with the same
    witness, shell_unfolds holds, lower holds - and blk is wrong for two partials. A pin
    that a plant like this passes would be decoration; this one fails it. -/
def plantBlkBoundary : Partial → PlanView → YulBlock
  | .lagrange, pv => GenAst.emitPartial pv .lagrange ++ GenAst.emitPartial pv .quotientLin
  | .quotientLin, _ => []
  | q, pv => GenAst.emitPartial pv q

def plantBoundarySurface : Surface rp RP RP RP :=
  { realSurface with
    blk := plantBlkBoundary,
    main_concat := ⟨GenAst.emitHelpers fxPlan, rfl⟩ }

theorem blkPinBitesBoundary : ¬ BlkIsEmitter plantBoundarySurface := by
  intro h
  have h1 := h.1 Partial.quotientLin fxPlan
  have h4 : SyntaxEq.stmtsBeq (plantBoundarySurface.blk Partial.quotientLin fxPlan)
      [] = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.quotientLin)
      [] = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-! #### The placeholder plants: a real slice put back to its own placeholder

    WHY THESE FOUR EXIST. Every plant above this section attacks a pin that was already
    carrying weight: finalPairing was real when P-AST planted a 'return(0, 0)' over it, and
    the boundary plant works because it moves a join whose two sides are DIFFERENT from
    what blk claims - since P-AST3a the quotientLin side is a nine-statement scope and not a
    dummy, which makes that plant bite harder and not less. P-AST2 made lagrange and
    traceReturn real and P-AST3a made quotientLin real, and each conversion creates a NEW
    plant class the older exhibits cannot express: a blk whose slice for a now-real partial
    is the emitter's OWN placeholder. Before the conversion that plant satisfied BlkIsEmitter,
    because the placeholder was the emitter's answer for that partial - the pin was true of
    it by accident, not by design. D-P30 clause 6 is the instruction to re-check exactly
    this at every conversion, and the three theorems below are the re-check: the same plant,
    now excluded, with main replanted so that main_concat, lower_ok and shell_unfolds all
    still discharge and the pin remains the only thing that refuses it. The quotientLin one
    is the sharpest of the three: placeholder and real slice are both ONE statement, so the
    replanted main has the same LENGTH as the emitted main and only the statement inside it
    differs. -/

/-- The replanted main for an arbitrary planted blk: the emitted helpers, then the planted
    slices in include order. This is what keeps a plant a genuine Surface - main is free, it
    comes from lower, and main_concat has to be satisfiable by SOME helpers tail. -/
def plantMainWith (b : Partial → PlanView → YulBlock) : YulBlock :=
  GenAst.emitHelpers fxPlan ++
    Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++ b q fxPlan

/-- The replanted render: refuses the two diagnostic options exactly as fxLower does, so
    SupportedS.production and the astOfMain equation still behave, and returns the replanted
    main for the production option. -/
def plantLowerWith (m : YulBlock) :
    RenderOptions → Except Midfall.Generator.GeneratorError Lowered := fun o =>
  if o.diagnostics.trace || o.diagnostics.gasCheckpoints then
    .error Midfall.Generator.GeneratorError.noAdviceColumns
  else
    .ok { fxLowered with main := m }

/-- THE PLANT BUILDER: a Surface that differs from the emitter in blk and nowhere else that
    a hypothesis can see. Everything except blk, L, lower, shell and astOfMain is the
    fixture's own, and the five that are not are re-supplied so the record still closes -
    lower_ok, main_concat and shell_unfolds are all rfl against the replanted main, exactly
    as in plantCounterexampleSurface. -/
def plantSurfaceWith (b : Partial → PlanView → YulBlock) : Surface rp RP RP RP :=
  let m := plantMainWith b
  let low := plantLowerWith m
  { realSurface with
    blk := b, L := { fxLowered with main := m }, lower := low,
    shell := Object.mk "Halo2Verifier" (fxArmOf m) [] [],
    astOfMain := fun o => match low o with | .ok l => some l.main | .error _ => none,
    lower_ok := rfl,
    main_concat := ⟨GenAst.emitHelpers fxPlan, rfl⟩,
    shell_unfolds := rfl }

/-- The plant P-AST2 makes possible: lagrange back to its placeholder, everything else the
    emitter's. -/
def plantBlkLagrangePlaceholder : Partial → PlanView → YulBlock
  | .lagrange, _pv => GenAst.emitPlaceholder .lagrange
  | q, pv => GenAst.emitPartial pv q

def plantLagrangePlaceholderSurface : Surface rp RP RP RP :=
  plantSurfaceWith plantBlkLagrangePlaceholder

/-- THE PIN BITES THE PLACEHOLDER PLANT, LAGRANGE (D-P23, second half for the new slice).
    The plant's blk is the emitter's own dummy for lagrange, so the ONLY thing that refuses
    it is that the emitter no longer returns that dummy. -/
theorem blkPinBitesLagrangePlaceholder : ¬ BlkIsEmitter plantLagrangePlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.lagrange fxPlan
  have h4 : SyntaxEq.stmtsBeq
      (plantLagrangePlaceholderSurface.blk Partial.lagrange fxPlan)
      (GenAst.emitPlaceholder .lagrange) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.lagrange)
      (GenAst.emitPlaceholder .lagrange) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- The same plant on the other newly real slice. -/
def plantBlkTraceReturnPlaceholder : Partial → PlanView → YulBlock
  | .traceReturn, _pv => GenAst.emitPlaceholder .traceReturn
  | q, pv => GenAst.emitPartial pv q

def plantTraceReturnPlaceholderSurface : Surface rp RP RP RP :=
  plantSurfaceWith plantBlkTraceReturnPlaceholder

/-- THE PIN BITES THE PLACEHOLDER PLANT, TRACE_RETURN. Note what the placeholder and the
    real slice have in common: BOTH end in a 'ret' builtin, and the placeholder's is
    'return(0x1000, 0x20)' - the same LENGTH as the real terminal return, from a different
    address and with no guard before it. A length-only check cannot tell them apart, which
    is why this is a stmtsBeq exhibit and not a count. -/
theorem blkPinBitesTraceReturnPlaceholder :
    ¬ BlkIsEmitter plantTraceReturnPlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.traceReturn fxPlan
  have h4 : SyntaxEq.stmtsBeq
      (plantTraceReturnPlaceholderSurface.blk Partial.traceReturn fxPlan)
      (GenAst.emitPlaceholder .traceReturn) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.traceReturn)
      (GenAst.emitPlaceholder .traceReturn) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- The plant P-AST3a makes possible: quotientLin back to its placeholder, everything else
    the emitter's. -/
def plantBlkQuotientLinPlaceholder : Partial → PlanView → YulBlock
  | .quotientLin, _pv => GenAst.emitPlaceholder .quotientLin
  | q, pv => GenAst.emitPartial pv q

def plantQuotientLinPlaceholderSurface : Surface rp RP RP RP :=
  plantSurfaceWith plantBlkQuotientLinPlaceholder

/-- THE PIN BITES THE PLACEHOLDER PLANT, QUOTIENTLIN (D-P23, second half for the new slice).
    WHAT MAKES THIS PLANT DIFFERENT FROM THE OTHER TWO, and why it needed its own theorem
    rather than a third conjunct: the placeholder and the real slice are BOTH one statement,
    so plantMainWith of this plant has the SAME LENGTH as GenAst.emitMain fxPlan - 47
    statements either way - and every length-based argument in this file is blind to it. The
    second conjunct below is the witness that the replanted main is length-identical and still
    not the emitted main, i.e. that the pin is refusing this plant on CONTENT alone. Before
    P-AST3a the plant passed BlkIsEmitter outright: 'mstore(0x2300, 4)' WAS the emitter's
    answer for quotientLin. -/
theorem blkPinBitesQuotientLinPlaceholder :
    ¬ BlkIsEmitter plantQuotientLinPlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.quotientLin fxPlan
  have h4 : SyntaxEq.stmtsBeq
      (plantQuotientLinPlaceholderSurface.blk Partial.quotientLin fxPlan)
      (GenAst.emitPlaceholder .quotientLin) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.quotientLin)
      (GenAst.emitPlaceholder .quotientLin) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- THE LENGTH BLINDNESS, as a computation next to the theorem above: the plant's main and
    the emitted main have the same number of statements, differ under stmtsBeq, and differ in
    exactly one slice. This is the falsifiability of the plant class - a pin that only looked
    at main's shape or length would let the plant through, and these three lines are what
    says so. -/
def plantQuotientLinLengthBlind_ok : Bool :=
  (plantMainWith plantBlkQuotientLinPlaceholder).length =
    (GenAst.emitMain fxPlan).length &&
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkQuotientLinPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkQuotientLinPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != Partial.quotientLin)) &&
    -- and the two one-statement shapes are distinguishable only from the inside:
    (plantBlkQuotientLinPlaceholder Partial.quotientLin fxPlan).length == 1 &&
    (GenAst.emitPartial fxPlan Partial.quotientLin).length == 1

#eval plantQuotientLinLengthBlind_ok      -- expect true

/-- EVERY OTHER HYPOTHESIS STILL HOLDS OF THE THREE PLACEHOLDER PLANTS, so the pin is
    again the only thing that refuses them. Stated as three exhibits rather than transported
    from plantedStillSupported: that transport was TRIED and FAILS to typecheck (measured -
    'Type mismatch' at both 'exact plantedStillSupported' sites), for the reason
    plantedStillSupported's own comment gives: SupportedS carries the section's nine instance
    arguments and the statements do not unify up to them. So each plant gets the direct ten-
    bullet exhibit, and each bullet is a computation on the plant's own projections. -/
theorem plantedLagrangePlaceholderStillSupported :
    SupportedS plantLagrangePlaceholderSurface plantLagrangePlaceholderSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantLagrangePlaceholderSurface, plantSurfaceWith, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantLagrangePlaceholderSurface, plantSurfaceWith, realSurface, fxVk,
        List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

theorem plantedTraceReturnPlaceholderStillSupported :
    SupportedS plantTraceReturnPlaceholderSurface plantTraceReturnPlaceholderSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantTraceReturnPlaceholderSurface, plantSurfaceWith, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantTraceReturnPlaceholderSurface, plantSurfaceWith, realSurface, fxVk,
        List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- P-AST3a: the third plant, same ten bullets, same reason for being written out
    directly rather than transported. Nothing SupportedS reads mentions blk, L, lower, shell
    or astOfMain, and this plant changes only those five. -/
theorem plantedQuotientLinPlaceholderStillSupported :
    SupportedS plantQuotientLinPlaceholderSurface plantQuotientLinPlaceholderSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantQuotientLinPlaceholderSurface, plantSurfaceWith, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantQuotientLinPlaceholderSurface, plantSurfaceWith, realSurface, fxVk,
        List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- The plant P-AST3b makes possible: vkLoading back to its own placeholder, everything
    else the emitter's. Declared BEFORE the two KATs below because both of them name it. -/
def plantBlkVkLoadingPlaceholder : Partial → PlanView → YulBlock
  | .vkLoading, _pv => GenAst.emitPlaceholder .vkLoading
  | q, pv => GenAst.emitPartial pv q

def plantVkLoadingPlaceholderSurface : Surface rp RP RP RP :=
  plantSurfaceWith plantBlkVkLoadingPlaceholder

/-- The plant P-AST4 makes possible: transcriptParser back to its own placeholder,
    everything else the emitter's. -/
def plantBlkTranscriptParserPlaceholder : Partial → PlanView → YulBlock
  | .transcriptParser, _pv => GenAst.emitPlaceholder .transcriptParser
  | q, pv => GenAst.emitPartial pv q

def plantTranscriptParserPlaceholderSurface : Surface rp RP RP RP :=
  plantSurfaceWith plantBlkTranscriptParserPlaceholder

/-- All four placeholder plants keep their replanted main DISTINCT from the emitted main,
    which is the price of being a Surface at all: main_concat is existential over the helper
    prefix only, so a blk change that left main alone would not be a Surface whose slices
    tile the tail of its program. The quotientLin and vkLoading lines are the ones that
    matter most, because for those two plants the two mains have the same LENGTH - the
    placeholder and the real slice are each one statement - and only stmtsBeq can tell them
    apart. -/
def plantPlaceholderMainsDiffer_ok : Bool :=
  ! SyntaxEq.stmtsBeq (plantMainWith plantBlkLagrangePlaceholder) (GenAst.emitMain fxPlan) &&
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkTraceReturnPlaceholder)
      (GenAst.emitMain fxPlan) &&
    -- and each plant differs from the emitter in EXACTLY one slice, so the plant is about
    -- the slice and not about the whole program being different.
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkLagrangePlaceholder q fxPlan) (GenAst.emitPartial fxPlan q) ==
        (q != .lagrange)) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkTraceReturnPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .traceReturn)) &&
    -- P-AST3a: the third plant, and the extra line that says what is special about it - the
    -- replanted main has the SAME LENGTH as the emitted main (47 either way), so this is the
    -- only plant in
    -- the file whose difference stmtsBeq can see and a length count cannot.
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkQuotientLinPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (plantMainWith plantBlkQuotientLinPlaceholder).length =
      (GenAst.emitMain fxPlan).length &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkQuotientLinPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .quotientLin)) &&
    -- P-AST3b: the fourth plant. It differs from the emitter on exactly vkLoading, keeps
    -- main's LENGTH - 47 either way, because the placeholder and the real slice are both
    -- one statement - and is therefore invisible to every count in this file.
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkVkLoadingPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (plantMainWith plantBlkVkLoadingPlaceholder).length =
      (GenAst.emitMain fxPlan).length &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkVkLoadingPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .vkLoading)) &&
    -- P-AST4: the fifth plant, and the one whose replanted main is NOT length-identical -
    -- 19 statements against 47, because the placeholder is one statement and the real slice
    -- at the fixture plan is twenty-nine. Stated as a difference and not a coincidence: the
    -- two plants above it are length-blind and this one is not, and plantTranscriptParser
    -- LengthVisible_ok below pins which side of that line it falls on.
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkTranscriptParserPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkTranscriptParserPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .transcriptParser))

#eval plantPlaceholderMainsDiffer_ok      -- expect true

/-- THE PIN BITES THE PLACEHOLDER PLANT, VKLOADING (D-P23, second half for the new slice).
    Before this package the plant satisfied BlkIsEmitter outright: 'mstore(0x2000, 1)' WAS
    the emitter's answer for vkLoading, so the pin was true of it by accident and not by
    design - which is exactly the plant class D-P30 clause 6 says to re-check at every
    conversion. What makes this the sharpest of the four: the placeholder and the real slice
    are BOTH one top-level statement, and the real one is a thirteen-statement scope whose
    second inner statement is an extcodecopy, so nothing but stmtsBeq on the CONTENT
    separates them and main's length is 47 either way. plantVkLoadingLengthBlind_ok below
    is that blindness as a computation. -/
theorem blkPinBitesVkLoadingPlaceholder :
    ¬ BlkIsEmitter plantVkLoadingPlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.vkLoading fxPlan
  have h4 : SyntaxEq.stmtsBeq
      (plantVkLoadingPlaceholderSurface.blk Partial.vkLoading fxPlan)
      (GenAst.emitPlaceholder .vkLoading) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.vkLoading)
      (GenAst.emitPlaceholder .vkLoading) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- THE LENGTH BLINDNESS OF THE VKLOADING PLANT, as a computation next to the theorem
    above: the replanted main and the emitted main have the SAME number of statements,
    differ under stmtsBeq, and differ in exactly one slice - and the two slices that differ
    are both one statement long. A pin that looked at main's shape or length would let this
    plant through; this is the falsification of the plant class. -/
def plantVkLoadingLengthBlind_ok : Bool :=
  (plantMainWith plantBlkVkLoadingPlaceholder).length =
    (GenAst.emitMain fxPlan).length &&
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkVkLoadingPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkVkLoadingPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != Partial.vkLoading)) &&
    (plantBlkVkLoadingPlaceholder Partial.vkLoading fxPlan).length == 1 &&
    (GenAst.emitPartial fxPlan Partial.vkLoading).length == 1

#eval plantVkLoadingLengthBlind_ok        -- expect true

/-- EVERY OTHER HYPOTHESIS STILL HOLDS OF THE VKLOADING PLANT, so the pin is the ONLY thing
    that refuses it - the second half of D-P23 / R-41 for this slice. Written as a direct
    ten-bullet exhibit and NOT transported from plantedStillSupported: P-AST3a measured that
    the transport fails to typecheck at both 'exact plantedStillSupported' sites, because
    SupportedS carries the section's nine instance arguments and the statements do not
    unify up to them. Nothing SupportedS reads mentions blk, L, lower, shell or astOfMain,
    and this plant changes only those five. -/
theorem plantedVkLoadingPlaceholderStillSupported :
    SupportedS plantVkLoadingPlaceholderSurface plantVkLoadingPlaceholderSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantVkLoadingPlaceholderSurface, plantSurfaceWith, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantVkLoadingPlaceholderSurface, plantSurfaceWith, realSurface, fxVk,
        List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- THE PIN BITES THE PLACEHOLDER PLANT, TRANSCRIPTPARSER (D-P23, second half for the new
    slice). Before this package the plant satisfied BlkIsEmitter outright: 'mstore(0x2100, 2)'
    WAS the emitter's answer for transcriptParser, so the pin was true of it by accident and
    not by design - the plant class D-P30 clause 6 says to re-check at every conversion.
    WHAT MAKES THIS PLANT DIFFERENT FROM THE QUOTIENTLIN AND VKLOADING ONES, and the
    difference is a measurement and not a preference: at the FIXTURE plan the real slice is
    TWENTY-NINE statements and the placeholder is one, so the replanted main has a DIFFERENT
    LENGTH from the emitted main and a count would have caught it. That is the easy case, and
    it is why the theorem is still written the hard way, with stmtsBeq on the slice: the plant
    class has to be excluded by the pin and not by an accident of size, because the next
    conversion might be one statement again. plantTranscriptParserLengthVisible_ok below
    records which side of that line this plant falls on, so a later package that shrinks the
    slice cannot silently move it across. -/
theorem blkPinBitesTranscriptParserPlaceholder :
    ¬ BlkIsEmitter plantTranscriptParserPlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.transcriptParser fxPlan
  have h4 : SyntaxEq.stmtsBeq
      (plantTranscriptParserPlaceholderSurface.blk Partial.transcriptParser fxPlan)
      (GenAst.emitPlaceholder .transcriptParser) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.transcriptParser)
      (GenAst.emitPlaceholder .transcriptParser) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- THE LENGTH FACT for this plant, stated because it is the opposite of the two plants
    above it: the replanted main is SHORTER than the emitted main - 19 against 47 - so this
    plant is not length-blind. Both halves are computations: the two lengths, and the fact
    that the plant still differs from the emitter on exactly one slice. -/
def plantTranscriptParserLengthVisible_ok : Bool :=
  (plantMainWith plantBlkTranscriptParserPlaceholder).length ≠ (GenAst.emitMain fxPlan).length &&
    (plantMainWith plantBlkTranscriptParserPlaceholder).length == 19 &&
    (GenAst.emitMain fxPlan).length == 47 &&
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkTranscriptParserPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkTranscriptParserPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != Partial.transcriptParser)) &&
    (plantBlkTranscriptParserPlaceholder Partial.transcriptParser fxPlan).length == 1 &&
    (GenAst.emitPartial fxPlan Partial.transcriptParser).length == 29

#eval plantTranscriptParserLengthVisible_ok -- expect true

/-- EVERY OTHER HYPOTHESIS STILL HOLDS OF THE TRANSCRIPTPARSER PLANT, so the pin is the ONLY
    thing that refuses it - the second half of D-P23 / R-41 for this slice. Written as a
    direct ten-bullet exhibit and NOT transported from plantedStillSupported. P-AST3a and
    P-AST3b both measured that the transport fails to typecheck, and P-AST4 RE-MEASURED it on
    a copy of the tree rather than inheriting it: inserting 'exact plantedStillSupported'
    above this exhibit fails with "Type mismatch / plantedStillSupported has type SupportedS
    plantCounterexampleSurface plantCounterexampleSurface.o₀ but is expected to have type
    SupportedS plantTranscriptParserPlaceholderSurface ...", because SupportedS carries the
    section's nine instance arguments and the statements do not unify up to them. Third
    package in a row with the same measurement; the transport needs a lemma that is
    polymorphic in the Surface, which nobody has written. Nothing SupportedS reads mentions
    blk, L, lower, shell or astOfMain, and this plant changes only those five - the fourth
    package in a row for which the ten bullets have been written out by hand, which is the
    re-measurement the brief asked for and it reproduces. -/
theorem plantedTranscriptParserPlaceholderStillSupported :
    SupportedS plantTranscriptParserPlaceholderSurface plantTranscriptParserPlaceholderSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantTranscriptParserPlaceholderSurface, plantSurfaceWith, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantTranscriptParserPlaceholderSurface, plantSurfaceWith, realSurface, fxVk,
        List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩


/-- THE PLANT P-PLANVIEW MAKES POSSIBLE, AND THE ONE ITS PREDECESSORS COULD NOT: pcs put
    back to its own placeholder. Before this package the plant was UNFORMULABLE - the
    placeholder WAS the emitter's answer for pcs, so a blk returning it satisfied
    BlkIsEmitter by construction and the pin had nothing to refuse. That is D-P30 clause 6's
    class exactly, and it is why every conversion has to re-check the plant rather than
    inherit it.

    WHAT MAKES THIS PLANT THE SHARPEST OF THE FIVE, and it is not the length. The fixture's
    own plan view has no circuit, so 'GenAst.emitPartial fxPlan .pcs' is the EMPTY block and
    the placeholder is one statement - a plant a length check would catch for free, and the
    weakest possible evidence. So the theorem below does not plant at fxPlan: BlkIsEmitter
    quantifies over EVERY plan view, and the pin is refuted at pcsFixturePlan, where the
    emitter returns a program of more than a hundred statements and the plant still returns
    the one-statement dummy. The second theorem is the same plant at the fixture, kept because
    the empty-vs-one case is the one a fall-through could produce by accident and it too has
    to be refused. -/
def plantBlkPcsPlaceholder : Partial → PlanView → YulBlock
  | .pcs, _pv => GenAst.emitPlaceholder .pcs
  | q, pv => GenAst.emitPartial pv q

def plantPcsPlaceholderSurface : Surface rp RP RP RP :=
  plantSurfaceWith plantBlkPcsPlaceholder

/-- THE PIN BITES THE PLACEHOLDER PLANT, PCS, AT A PLAN VIEW WITH A CIRCUIT (D-P23, second
    half for the seventh slice). The plant's blk is the emitter's own dummy for pcs; the only
    thing that refuses it is that the emitter no longer returns that dummy - and at the Kzg
    fixture plan the dummy is one statement against a real multi-block program. -/
theorem blkPinBitesPcsPlaceholder : ¬ BlkIsEmitter plantPcsPlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.pcs GenAst.pcsFixturePlan
  have h4 : SyntaxEq.stmtsBeq (plantPcsPlaceholderSurface.blk Partial.pcs
      GenAst.pcsFixturePlan) (GenAst.emitPlaceholder .pcs) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial GenAst.pcsFixturePlan Partial.pcs)
      (GenAst.emitPlaceholder .pcs) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- THE SAME PLANT AT THE FIXTURE PLAN VIEW, where the emitted slice is EMPTY because the
    fixture carries no circuit. Stated separately rather than folded into the theorem above
    because the two cases are different failures of a would-be emitter: one is a placeholder
    standing in for a real program, the other is a placeholder standing in for an early return.
    Both are refused, and the pin is what refuses them. -/
theorem blkPinBitesPcsPlaceholderAtFixture : ¬ BlkIsEmitter plantPcsPlaceholderSurface := by
  intro h
  have h1 := h.1 Partial.pcs fxPlan
  have h4 : SyntaxEq.stmtsBeq (plantPcsPlaceholderSurface.blk Partial.pcs fxPlan)
      (GenAst.emitPlaceholder .pcs) = true := by native_decide
  have h5 : SyntaxEq.stmtsBeq (GenAst.emitPartial fxPlan Partial.pcs)
      (GenAst.emitPlaceholder .pcs) = false := by native_decide
  rw [← h1] at h5
  rw [h4] at h5
  exact Bool.noConfusion h5

/-- EVERY OTHER HYPOTHESIS STILL HOLDS OF THE PCS PLANT, so the pin is the only thing that
    refuses it - the second half of D-P23 / R-41 for the seventh slice. Written as a DIRECT
    ten-bullet exhibit and not transported from plantedStillSupported: P-AST3a, P-AST3b and
    P-AST4 each measured that the transport fails to typecheck, and P-PLANVIEW re-measured it
    a fourth time on this very goal - inserting 'exact plantedStillSupported' here gives
    "plantedStillSupported has type SupportedS plantCounterexampleSurface
    plantCounterexampleSurface.o₀ but is expected to have type SupportedS
    plantPcsPlaceholderSurface plantPcsPlaceholderSurface.o₀". Nothing SupportedS reads
    mentions blk, L, lower, shell or astOfMain, and this plant changes only those five. -/
theorem plantedPcsPlaceholderStillSupported :
    SupportedS plantPcsPlaceholderSurface plantPcsPlaceholderSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [plantPcsPlaceholderSurface, plantSurfaceWith, realSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : RP) := by
      simpa [plantPcsPlaceholderSurface, plantSurfaceWith, realSurface, fxVk,
        List.mem_append, List.mem_singleton] using hC
    subst hnil
    refine ⟨(0, 0), ?_, ?_⟩ <;> native_decide
  · exact ⟨by native_decide, by native_decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- THE LENGTH FACT for the pcs plant, stated because it is the opposite of the quotientLin
    and vkLoading plants and the same as the transcriptParser one: at the FIXTURE plan the
    emitted slice is empty and the placeholder is one statement, so the replanted main is
    LONGER than the emitted main by exactly one - and a length check would catch this plant
    at the fixture. That is the easy case. The line that matters is the last one: at the Kzg
    fixture plan the same plant differs by more than a hundred statements - counted DEEP since
    G1.4b, because the emission is one region block at the top level - and in both cases
    the plant differs from the emitter on exactly the slice it plants and on no other. -/
def plantPcsPlaceholderLengthVisible_ok : Bool :=
  (plantMainWith plantBlkPcsPlaceholder).length = (GenAst.emitMain fxPlan).length + 1 &&
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkPcsPlaceholder) (GenAst.emitMain fxPlan) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkPcsPlaceholder q fxPlan) (GenAst.emitPartial fxPlan q) ==
        (q != Partial.pcs)) &&
    (GenAst.emitPartial fxPlan Partial.pcs).isEmpty &&
    (plantBlkPcsPlaceholder Partial.pcs fxPlan).length == 1 &&
    -- G1.4b: the same shape fact as GenAstDispatch.emitPlaceholderIsTotal_ok. Since the pcs arm
    -- emits the partition as `Stmt.block` scopes instead of flattening it, the real slice is ONE
    -- region statement at the top level - the same length as the plant - so it is the DEEP count
    -- that says the plant differs from the emitter by more than a hundred statements here, and it
    -- additionally pins the ten-block partition the flat length check never could.
    (match GenAst.emitPartial GenAst.pcsFixturePlan Partial.pcs with
     | [Stmt.block body] => body.length == 10 &&
         (body.map (fun s => match s with
           | Stmt.block inner => inner.length
           | _ => 1)).foldl (fun n k => n + k) 0 > 100
     | _ => false) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkPcsPlaceholder q GenAst.pcsFixturePlan)
        (GenAst.emitPartial GenAst.pcsFixturePlan q) == (q != Partial.pcs))

#eval plantPcsPlaceholderLengthVisible_ok   -- expect true

/-- The pin's two halves as a computation, next to the two plants as theorems. Line 1:
    the fixture's blk agrees with the emitter for every partial under stmtsBeq, the
    authoritative relation. Line 2: the emitted finalPairing slice is the real program -
    a guard on success and an assignment from a USER call to ec_pairing - which no
    placeholder could imitate, and the user-call spelling is the distinction the token
    comparator cannot make. Lines 3-4: both plants differ from the emitter under the same
    relation, which is the decidable shadow of the two theorems above. Line 5: the
    boundary plant keeps main - so main_concat cannot see it. Line 6: the counterexample
    plant changes main - so the plant is invisible to every field except the pin. Line 7:
    hoist of the fixture's main resolves fail and ec_pairing, and hoist of the slices
    alone does not, which is the pin's second conjunct doing the work it was added for.
    Lines 8-10 are P-AST2: the Lagrange slice is a program and not a length, the TraceReturn
    slice equals the artifact's quotation, and the two placeholder plants differ from the
    emitter on exactly the slice they plant. Lines 11-12 are P-AST3a: the quotientLin slice
    equals the artifact's own quotation at the FIXTURE's k, and its placeholder plant
    differs from the emitter on exactly that slice while keeping main's LENGTH - the
    length-blindness the pin alone has to overcome. -/
def blkPinKats_ok : Bool :=
  (Midfall.Lowering.partials.all fun q =>
    SyntaxEq.stmtsBeq (realSurface.blk q realSurface.plan)
      (GenAst.emitPartial realSurface.plan q)) &&
    (match realSurface.blk Partial.finalPairing realSurface.plan with
     | [Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"]) _,
         Stmt.assign ["success"] (Expr.call "ec_pairing" _)] => true
     | _ => false) &&
    ! SyntaxEq.stmtsBeq plantReturnBlock (GenAst.emitPartial fxPlan Partial.finalPairing) &&
    ! SyntaxEq.stmtsBeq (plantBlkBoundary Partial.quotientLin fxPlan)
      (GenAst.emitPartial fxPlan Partial.quotientLin) &&
    SyntaxEq.stmtsBeq plantBoundarySurface.L.main (GenAst.emitMain fxPlan) &&
    ! SyntaxEq.stmtsBeq plantMainCounterexample (GenAst.emitMain fxPlan) &&
    (let c : ExternalCalls := ⟨fun _ _ _ => False⟩
     let g : ExternalGas := ExternalGas.ofFun fun _ => 0
     let d := Bridge.Dialect c g
     (lookupFun (hoist d realSurface.L.main :: []) "fail").isSome &&
       (lookupFun (hoist d realSurface.L.main :: []) "ec_pairing").isSome &&
       ! (lookupFun (hoist d (GenAst.emitSlices fxPlan) :: []) "ec_pairing").isSome) &&
    -- Line 8 (P-AST2): the Lagrange slice at the FIXTURE's plan is the real program - the
    -- MF-4 flag, a 28-statement scope with five loops, and the section-boundary guard - and
    -- not three flat statements that happen to have the right length.
    (match realSurface.blk Partial.lagrange realSurface.plan with
     | Stmt.letDecl ["lagrange_precompile_failed"]
         (some (Expr.lit (Literal.number 0))) :: Stmt.block body :: Stmt.cond _ _ :: [] =>
         body.length == 28 && (body.filter GenAst.stmtIsFor).length == 5
     | _ => false) &&
    -- Line 9 (P-AST2): the TraceReturn slice the fixture runs IS the yul% quotation of the
    -- deployed artifact's terminal arm (VerifierPartialKats.traceReturn_ast, transcribed from
    -- D:3010-3021 by P-13e and gated there against the render). This is the cross-check the
    -- converter does not control: TraceReturn is the one real slice whose emitted shape is
    -- plan-independent, so the snapshot is comparable at the fixture itself.
    SyntaxEq.stmtsBeq (realSurface.blk Partial.traceReturn realSurface.plan)
      VerifierPartialKats.traceReturn_ast &&
    -- Line 10 (P-AST2): the decidable shadow of the two new theorems - each placeholder
    -- plant differs from the emitter on its own slice and agrees with it on the other six.
    ! SyntaxEq.stmtsBeq (plantBlkLagrangePlaceholder Partial.lagrange fxPlan)
      (GenAst.emitPartial fxPlan Partial.lagrange) &&
    ! SyntaxEq.stmtsBeq (plantBlkTraceReturnPlaceholder Partial.traceReturn fxPlan)
      (GenAst.emitPartial fxPlan Partial.traceReturn) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkLagrangePlaceholder q fxPlan) (GenAst.emitPartial fxPlan q) ==
        (q != .lagrange)) &&
    -- Line 11 (P-AST3a): the quotientLin slice the fixture runs is the artifact's own
    -- quotation (VerifierPartialKats.qalLinearization_ast) EXCEPT for k - the fixture plan is
    -- k = 2 and the snapshot is the deployed k = 6, so the cross-check here is that the SHAPE
    -- is the snapshot's and the NUMBER is the plan's. Both halves are asserted: the emitted
    -- slice at k = 6 IS the snapshot, and at the fixture's own plan it is the snapshot with
    -- the loop bound replaced and nothing else changed. That is the converter not controlling
    -- its own comparison, which is what D-P30 clause 2 asks for.
    (match GenAst.emitQuotientLinAt 6 with
     | [Stmt.block body] =>
         body.length == 9 &&
         (match (realSurface.blk Partial.quotientLin realSurface.plan)[0]?, body[1]? with
          | some (Stmt.block fxB), some (Stmt.letDecl ["k"]
              (some (Expr.lit (Literal.number 6)))) =>
              fxB.length == 9 &&
                (match fxB[1]? with
                 | some (Stmt.letDecl ["k"] (some (Expr.lit (Literal.number 2)))) => true
                 | _ => false)
          | _, _ => false)
     | _ => false) &&
    -- Line 12 (P-AST3a): the decidable shadow of the third theorem, and the length-blindness
    -- the pin alone has to overcome.
    ! SyntaxEq.stmtsBeq (plantBlkQuotientLinPlaceholder Partial.quotientLin fxPlan)
      (GenAst.emitPartial fxPlan Partial.quotientLin) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkQuotientLinPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .quotientLin)) &&
    (plantMainWith plantBlkQuotientLinPlaceholder).length =
      (GenAst.emitMain fxPlan).length &&
    -- Line 13 (P-AST3b): the deployed vkLoading slice the emitter produces IS the
    -- artifact's own quotation (VerifierPartialKats.vkLoading_ast, gated in that file
    -- against the render by their gate 90, which re-reads the size, the single occurrence
    -- and the six header words from the dump). That is the cross-check this converter does
    -- not control. At the FIXTURE's own plan the same thirteen-statement scope carries the
    -- fixture's k (2, not the deployed 6) and the fixture's DERIVED accumulator words (all
    -- zero because cfg.accumulator is none), so the numbers come from the plan and not from
    -- the snapshot - the same shape-versus-number split line 11 records for quotientLin.
    SyntaxEq.stmtsBeq (GenAst.emitVkLoadingArms false 1 6 0 0 0 0 0x10e0)
      VerifierPartialKats.vkLoading_ast &&
    (match realSurface.blk Partial.vkLoading realSurface.plan with
     | [Stmt.block fxB] =>
         fxB.length == 13 &&
         (match fxB[3]? with
          | some (Stmt.assign ["success"]
              (Expr.builtin Op.and [Expr.var "success",
                Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.var "K_MPTR"],
                  Expr.lit (Literal.number 2)]])) => true
          | _ => false) &&
         (match fxB[7]? with
          | some (Stmt.assign ["success"]
              (Expr.builtin Op.and [Expr.var "success",
                Expr.builtin Op.eq [Expr.builtin Op.mload
                  [Expr.var "NUM_ACC_LIMB_BITS_MPTR"], Expr.lit (Literal.number 0)]])) => true
          | _ => false)
     | _ => false) &&
    -- Line 14 (P-AST3b): the decidable shadow of the fourth theorem, and the length
    -- blindness the pin alone has to overcome.
    ! SyntaxEq.stmtsBeq (plantBlkVkLoadingPlaceholder Partial.vkLoading fxPlan)
      (GenAst.emitPartial fxPlan Partial.vkLoading) &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkVkLoadingPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .vkLoading)) &&
    (plantMainWith plantBlkVkLoadingPlaceholder).length =
      (GenAst.emitMain fxPlan).length

#eval blkPinKats_ok                       -- expect true
/-! ### 7. EnvAgrees: the hypothesis P-4a2 closes (note 3: this used to be unexhibited) -/

/-- THE DOMAIN IS THE PORT'S OWN OUTPUT, checked in the VM. `EvaluationDomain.new fxFc 3 2`
    at the repaired constants (j = csDegree = 3, k = 2) produces all fifteen fields of
    fxDom exactly, so the literals above were derived from the port and not invented
    beside it. A `#eval` gate rather than a theorem because the batch inversion inside
    `new` does not reduce in the kernel at 255-bit `r` - the same limit TwoAdicity's
    header records for `⁻¹`. Deleting any field comparison, or changing any literal, makes
    this print false. -/
def fxDomMatchesPort_ok : Bool :=
  match EvaluationDomain.new fxFc 3 2 with
  | .error _ => false
  | .ok d =>
      d.n == fxDom.n && d.k == fxDom.k && d.extendedK == fxDom.extendedK &&
        d.omega == fxDom.omega && d.omegaInv == fxDom.omegaInv &&
        d.extendedOmega == fxDom.extendedOmega &&
        d.extendedOmegaInv == fxDom.extendedOmegaInv &&
        d.gCoset == fxDom.gCoset && d.gCosetInv == fxDom.gCosetInv &&
        d.quotientPolyDegree == fxDom.quotientPolyDegree &&
        d.ifftDivisor == fxDom.ifftDivisor &&
        d.extendedIfftDivisor == fxDom.extendedIfftDivisor &&
        d.tEvaluations == fxDom.tEvaluations &&
        d.barycentricWeight == fxDom.barycentricWeight

#eval fxDomMatchesPort_ok               -- expect true

/-- THE DEGENERATE PAIR, KEPT AS THE FALSIFICATION (P-ENV, D-P23 second half). This is
    the object P-4a2 measured: `omega := 1` **and** `omegaInv := 1` with everything else
    of the REPAIRED domain left alone - the right `n`, the right `k`, and above all the
    CORRECT `barycentricWeight`, so the one clause that used to fail on `fxDomOld` passes
    here. Before P-ENV this satisfied all ten `EnvAgrees` clauses; now `omegaOrder`
    rejects it. `fxDomOld` cannot serve this purpose: it fails `baryWeight` as well, so a
    rejection of it says nothing about WHICH clause did the work. -/
def fxDomDegenerate : EvaluationDomain (Fr rp) :=
  { fxDom with omega := 1, omegaInv := 1 }

/-- The fixture key with the degenerate domain and nothing else changed, so that every
    clause of `EnvAgrees` that does not read the domain is the same clause it was. -/
def fxVkDegenerate : VerifyingKey (Fr rp) RP :=
  { fxVk with domain := fxDomDegenerate }

/-- The new clause fails on it: the order of 1 is 1, not 4. -/
theorem fxDegenerateNotExactOrder :
    ¬ Midfall.Assumptions.orderExactly fxDomDegenerate.omega fxDomDegenerate.n := by
  intro h
  have hlt : 1 < fxDomDegenerate.n := by decide
  exact h.pow_ne_one (m := 1) (by decide) hlt (by decide)

/-- THE OLD CLAUSE TEXT, STILL GREEN HERE: `omega ^ n = 1`. This is the line that makes
    the demonstration a demonstration and not a claim - the pre-P-ENV `omegaOrder` type
    is proved of the degenerate pair, so the term that used to elaborate still would, and
    the only thing that changed is that the structure no longer asks for that. -/
theorem fxDegeneratePassesOldOmegaOrder :
    fxDomDegenerate.omega ^ fxDomDegenerate.n = 1 := by decide

/-- And the neighbouring domain clauses it still satisfies, so the rejection below is
    attributable to `omegaOrder` alone: `omegaInvMul` (1 * 1 = 1), `baryWeight` (the
    weight was deliberately left correct), and both halves of `domainN`. -/
theorem fxDegeneratePassesOtherDomainClauses :
    fxDomDegenerate.omegaInv * fxDomDegenerate.omega = 1 ∧
      fxDomDegenerate.barycentricWeight = ((2 ^ fxDomDegenerate.k : ℕ) : Fr rp)⁻¹ ∧
      fxDomDegenerate.n = 2 ^ fxDomDegenerate.k ∧ fxDomDegenerate.k = fxPlan.k :=
  ⟨by decide, Midfall.Assumptions.frInv4_eq_inv, rfl, rfl⟩

/-- The exactness check that the placeholder passes and a real generator fails: the
    intermediate power is NOT 1. This is the decidable half of `EnvAgrees.omegaOrder`
    (P-ENV strengthened that clause to `orderExactly`, whose second conjunct is exactly
    this for every proper divisor), and it is what would have caught the original bug. -/
theorem fxOmegaSquareNe : fxDom.omega ^ 2 ≠ (1 : Fr rp) := by decide

/-- `barycentricWeight` really is the inverse of the domain size, which is the clause that
    was FALSE before the repair. Stated as the multiplication because `decide` cannot
    reduce `⁻¹` at `r`; `EnvAgrees.baryWeight` below converts it through
    `eq_inv_iff_mul_eq_one`. -/
theorem fxBaryWeightTimesN : fxDom.barycentricWeight * (2 ^ fxDom.k : Fr rp) = 1 := by decide

/-- The clause the repaired PlanView had to move for: recomputed from the ConstraintSystem
    rather than asserted, which is how the 2-vs-7 disagreement was found. -/
theorem fxNegLagrangesAgree :
    fxPlan.numNegLagranges = fxCs.blindingFactors.toOption.getD 0 + 1 := by decide

/-- THE OLD PLACEHOLDER, KEPT AS A COUNTEREXAMPLE rather than deleted, so the vacuity this
    package removed stays visible and re-testable. It is a perfectly good
    `EvaluationDomain` record - which is exactly the problem: nothing in the type
    distinguishes it from the repaired one. -/
def fxDomOld : EvaluationDomain (Fr rp) :=
  { n := 4, k := 2, extendedK := 2, omega := 1, omegaInv := 1, extendedOmega := 1,
    extendedOmegaInv := 1, gCoset := 1, gCosetInv := 1, quotientPolyDegree := 2,
    ifftDivisor := 4, extendedIfftDivisor := 4, tEvaluations := #[0, 0, 0, 0],
    barycentricWeight := 4 }

/-- The naive gate is green on it: `omega ^ n = 1` holds, and so does the inverse clause.
    This is the shape of the bug, stated as a theorem so nobody re-introduces a check that
    cannot fail. -/
theorem fxDomOldPassesVacuousClauses :
    fxDomOld.omega ^ fxDomOld.n = 1 ∧ fxDomOld.omegaInv * fxDomOld.omega = 1 :=
  ⟨by decide, by decide⟩

/-- And the exactness clause refutes it: order 1, not 4. -/
theorem fxDomOldNotAChain : ¬ Midfall.Assumptions.orderExactly fxDomOld.omega (2 ^ fxDomOld.k) := by
  intro h
  have hlt : 1 < 2 ^ 2 := by decide
  exact h.pow_ne_one (m := 1) (by decide) hlt (by decide)

/-- The baryWeight clause fails on it too, which is the FALSE clause P-4a2's brief names:
    4 is not the inverse of 4 in Fr r, because 4 * 4 = 16 and r does not divide 15. -/
theorem fxDomOldBaryFails :
    fxDomOld.barycentricWeight ≠ ((2 ^ fxDomOld.k : ℕ) : Fr rp)⁻¹ := by
  intro h
  have h4 : (4 : Fr rp) = (4 : Fr rp)⁻¹ := h
  have h5 : (4 : Fr rp) * 4 = (4 : Fr rp)⁻¹ * 4 := congrArg (· * (4 : Fr rp)) h4
  have h6 : (4 : Fr rp)⁻¹ * 4 = 1 := inv_mul_cancel₀ (by decide : (4 : Fr rp) ≠ 0)
  have hc : (16 : Fr rp) = 1 := by
    rw [show (16 : Fr rp) = (4 : Fr rp) * 4 by norm_num, h5, h6]
  exact (by decide : ¬ ((16 : Fr rp) = (1 : Fr rp))) hc

/-- THE HEADLINE EXHIBIT: `EnvAgrees` holds of the fixture, as a kernel-checked term.
    Every clause that was vacuous or false at the placeholder is now discharged from a
    generator of exact order 2^k, an inverse that is an inverse, a numBits that gives the
    contract's 16-byte truncation width, and a PlanView that agrees with its own
    ConstraintSystem. The per-partial theorems in Lowering/Partials.lean therefore no
    longer carry an unexhibited hypothesis for the field-arithmetic reason - the remaining
    unexhibited hypothesis of the headline bundle is Eip2537.Holds, which is the pairing
    model at this fixture plus the missing G2/Fp2 model (note 7), not this. -/
theorem fxEnvAgrees : EnvAgrees fxE fxVk fxPlan fxParams (fx 5) :=
  { modulus := rfl
    truncWidth := by decide
    domainN := ⟨rfl, rfl⟩
    baryWeight := Midfall.Assumptions.frInv4_eq_inv
    omegaInvMul := Midfall.Assumptions.frOmega4Inv_mul
    omegaOrder := Midfall.Assumptions.frOmega4_order
    negLagranges := by decide
    nG2 := rfl
    sG2 := rfl
    vkDigestWord := rfl }

/-- THE FOUR RESTORED CLAUSES, EXHIBITED AT THE FIXTURE. P-RESTORE2 restored them from
    the sketch (they are the sketch's g1BaseWords, g2BaseWords, negSG2Words and
    accBasesInVk); they live in Lowering/Inv.lean's VkSlotsAgree and the reason for the
    split is recorded there. THE COST OF THE RESTORATION, reported rather than hidden:
    the fixture's payload image used to be two header words, which cannot satisfy a clause
    about word 11, so fxPayload now carries the reference's thirty-one. -/
theorem fxVkSlotsAgree :
    VkSlotsAgree fxE fxPlan (fx 5) fxEncG2 fxAccFixedBases :=
  { -- THE FOUR CLAUSES P-RESTORE2 RESTORED, each discharged by computation over the
    -- payload built above. native_decide and not decide: the kernel cannot reduce a
    -- 128-byte natToBytesBE fold inside its recursion budget - measured, an rfl on the
    -- same equation fails with maxRecDepth raised to 20000 - and the alternative, a
    -- hand-proved ByteArray split/concat lemma, would be a proof about the helper and
    -- not about the payload. This is the same trust boundary encG2_shape already crosses
    -- in this record, and fxHeaderSlotsKats_ok below re-checks all four as a Bool
    -- computation so a regression shows up in checks.sh and not only in a proof term.
    -- THE LIMIT, stated: fxEncG2 is a CONSTANT function here (every G2 point is the
    -- infinity encoding), so g2BaseWords and negSG2Words are satisfied by zeros and
    -- distinguish nothing at this fixture. They are exercised properly only by
    -- fxHeaderSlotsKats_ok lines 3-4, which moves the slot contents and shows the
    -- clauses change, and by the G1 slot, which is not constant.
    g1BaseWords := by native_decide
    g2BaseWords := by native_decide
    negSG2Words := by native_decide
    accBasesInVk := by
      intro b hb
      have hcases : b = { name := "-G", base := fx 1, negate := true } ∨
          b = { name := "b0", base := (1 : RP), negate := false } := by
        simpa [fxAccFixedBases, List.mem_cons, List.mem_singleton] using hb
      cases hcases with
      | inl e => subst e; exact ⟨Midfall.Lowering.vkG1BaseSlot, by native_decide⟩
      | inr e => subst e; exact ⟨Midfall.Lowering.vkG2BaseSlot, by native_decide⟩ }

/-- FALSIFICATION OF THE FOUR RESTORED CLAUSES (D-P23, second half). A clause nobody can
    break is a clause nobody can rely on, and these four were last removed on the
    strength of an argument that turned out to be wrong, so each gets a computation here
    that says it can fail. Lines 1-2: the G1 slot holds the generator encoding, and
    changing ONE WORD of it breaks the equation - so the clause is about the payload and
    not about the length of the payload. Line 3: a payload that stops before slot 11
    gives an empty slice and fails, which is the vkHeaderBytes no-silent-zero rule doing
    its job. Line 4: the fixed-base clause is not satisfied by an arbitrary table - a
    third entry naming a point no slot encodes is refuted over every slot the payload
    has. Line 5: the two G2 slots are equal to each other here ONLY because fxEncG2 is
    constant; the KAT says so explicitly rather than letting the exhibit look stronger
    than it is. -/
def fxHeaderSlotsKats_ok : Bool :=
  let cs := fxPlan.vk.constants
  let pv (ws : List (String × Word256)) : PlanView :=
    { fxPlan with vk := { fxPlan.vk with constants := ws } }
  let offTable := fxAccFixedBases.push { name := "not_in_vk", base := fx 3, negate := false }
  -- 1 the slot holds the generator encoding
  (Midfall.Lowering.vkG1Words fxPlan Midfall.Lowering.vkG1BaseSlot == fxToEip (fx 1)) &&
    -- 2 one word moved and the clause is gone
    (Midfall.Lowering.vkG1Words (pv (cs.take 11 ++ [("g1_base_0", 9)] ++ cs.drop 12))
       Midfall.Lowering.vkG1BaseSlot != fxToEip (fx 1)) &&
    -- 3 a payload that stops short gives an empty slice, not a zero-padded one
    (Midfall.Lowering.vkG1Words (pv (cs.take 11)) Midfall.Lowering.vkG1BaseSlot
       != fxToEip (fx 1)) &&
    (Midfall.Lowering.vkG1Words (pv (cs.take 11)) Midfall.Lowering.vkG1BaseSlot
       == Midfall.Bytes.empty) &&
    -- 4 the fixed-base clause can fail: a table entry no slot encodes
    (offTable.toList.any fun b =>
       !(List.range 31).any fun slot =>
         Midfall.Lowering.vkG1Words fxPlan slot == fxToEip b.base) &&
    -- and the two entries the real table DOES carry are each found
    (fxAccFixedBases.toList.all fun b =>
       (List.range 31).any fun slot =>
         Midfall.Lowering.vkG1Words fxPlan slot == fxToEip b.base) &&
    -- 5 the G2 slots: equal here because the encoder is constant, stated as a
    --   computation so the degeneracy is visible rather than implied
    (fxEncG2 (fx 1) == fxEncG2 ((fx 5 : RP)⁻¹)) &&
    (Midfall.Lowering.vkG2Words fxPlan Midfall.Lowering.vkG2BaseSlot == fxEncG2 (fx 1)) &&
    (Midfall.Lowering.vkG2Words fxPlan Midfall.Lowering.vkNegSG2BaseSlot
       == fxEncG2 ((fx 5 : RP)⁻¹)) &&
    -- and the two G2 slots are DIFFERENT regions of the payload, so a render that
    -- aliased them would still be caught by the slot indices themselves
    (Midfall.Lowering.vkG2BaseSlot != Midfall.Lowering.vkNegSG2BaseSlot)


/-- FALSIFICATION OF THE RESTORED CLAUSES, AS A THEOREM (D-P23, second half - the Bool
    KAT above is the computation; this is the kernel-checked form). The first statement is
    the transfer: any payload whose G1 base slot does not encode the generator fails
    VkSlotsAgree, by the g1BaseWords clause alone. The second instantiates it at a
    payload that differs from the fixture payload in ONE WORD, which is the measurement
    that says the clause is about the slot contents and not about the slot count. -/
theorem fxVkSlotsAgree_needs_the_g1_slot (ws : List (String × Word256))
    (h : Midfall.Lowering.vkG1Words { fxPlan with vk := { fxPlan.vk with constants := ws } }
          Midfall.Lowering.vkG1BaseSlot
        ≠ fxE.g1.toEip (inferInstance : Midfall.AdmissiblePairing RP RP RP).g₁) :
    ¬ VkSlotsAgree fxE { fxPlan with vk := { fxPlan.vk with constants := ws } } (fx 5)
        fxEncG2 fxAccFixedBases :=
  fun hv => h hv.g1BaseWords

/-- THE ONE-WORD PERTURBATION, discharged. -/
theorem fxVkSlotsAgreeRejectsMovedG1Slot :
    ¬ VkSlotsAgree fxE
        { fxPlan with vk := { fxPlan.vk with
            constants := (fxPlan.vk.constants.take 11) ++ [("g1_base_0", 9)]
              ++ (fxPlan.vk.constants.drop 12) } } (fx 5) fxEncG2 fxAccFixedBases :=
  fxVkSlotsAgree_needs_the_g1_slot
    ((fxPlan.vk.constants.take 11) ++ [("g1_base_0", 9)] ++ (fxPlan.vk.constants.drop 12))
    (by native_decide)

#eval fxHeaderSlotsKats_ok              -- expect true

/-- THE EXACTNESS IS NOW A FIELD, NOT A NEIGHBOUR (P-ENV). P-4a2 carried this fact as a
    standalone theorem `fxOmegaOrderExactly` beside an `EnvAgrees` whose `omegaOrder`
    clause the degenerate pair satisfied - i.e. non-vacuity lived OUTSIDE the structure the
    theorems carry. That standalone theorem is DELETED, and this recovers the same statement
    FROM `fxEnvAgrees.omegaOrder`, which is the evidence that deleting it lost nothing: the
    structure now implies on its own what used to have to be asserted next to it. -/
theorem fxEnvAgrees_carriesExactOrder :
    Midfall.Assumptions.orderExactly fxDom.omega (2 ^ fxDom.k) :=
  fxEnvAgrees.omegaOrder

/-- THE STRENGTHENED CLAUSE, SPENT AT THE FIXTURE. This is the in-tree consumer of
    `EnvAgrees.xNotRoot_iff_notDomainPoint`, and it is the concrete form the
    `lagrange_progress_spec` side condition needs: for this size-4 domain over `Fr r`, x
    misses the roots of X^4 - 1 EXACTLY when it misses the four points 1, ω, ω², ω³. Not
    derivable before P-ENV: the old `omega ^ n = 1` clause was silent about whether the
    powers repeat, and at `omega := 1` they do. -/
theorem fxXNotRoot_iff_notDomainPoint (x : Fr rp) :
    x ^ fxDom.n ≠ 1 ↔ ∀ i : ℕ, i < fxDom.n → x ≠ fxDom.omega ^ i :=
  fxEnvAgrees.xNotRoot_iff_notDomainPoint (x := x)

/-- THE DEGENERATE PAIR IS REJECTED (D-P23, falsifiability half - the point of P-ENV).
    Where the old clause typechecked, this object is now refuted, and the proof uses
    `omegaOrder` and NOTHING ELSE: `fxDegeneratePassesOldOmegaOrder` and
    `fxDegeneratePassesOtherDomainClauses` above show the pre-P-ENV text and the three
    neighbouring domain clauses all still hold of it, and the five clauses that do not
    read the domain are the same five as for `fxVk`, which `fxEnvAgrees` discharges. So no
    clause other than `omegaOrder` could have produced this rejection. -/
theorem fxEnvAgreesRejectsDegeneratePair :
    ¬ EnvAgrees fxE fxVkDegenerate fxPlan fxParams (fx 5) :=
  fun h => fxDegenerateNotExactOrder h.omegaOrder

/-- THE SAME DEMONSTRATION AS A COMPUTATION, so a regression shows up in `checks.sh` and
    not only in a proof term. Lines 1-3 are the OLD gate applied to the degenerate pair:
    green, which is the bug P-4a2 measured. Line 4 is the exactness test the strengthened
    clause adds: red, which is the repair. Lines 5-7 are the repaired generator, where both
    halves are green. What this KAT cannot see is the clause type itself - a weakening of
    `EnvAgrees.omegaOrder` back to `omega ^ n = 1` leaves every boolean here unchanged, and
    it is the fingerprint fragment on the clause type in
    `scripts/check_statement_fingerprints.py` that reddens that. -/
def fxDegenerateRejectionKats_ok : Bool :=
  -- the degenerate pair passes every check the OLD structure could ask for...
  (fxDomDegenerate.omega ^ fxDomDegenerate.n == 1) &&
    (fxDomDegenerate.omegaInv * fxDomDegenerate.omega == 1) &&
    (fxDomDegenerate.barycentricWeight * (2 ^ fxDomDegenerate.k : Fr rp) == 1) &&
    -- ...and fails the one the new structure asks for: 1^2 == 1, so its order is 1, not 4
    (fxDomDegenerate.omega ^ 2 == 1) &&
    -- the repaired generator: top power 1 AND intermediate power not 1
    (fxDom.omega ^ fxDom.n == 1) && (fxDom.omega ^ 2 != 1) &&
    (fxDom.omegaInv * fxDom.omega == 1) &&
    -- and the two domains differ in exactly the two generator fields
    (fxDomDegenerate.n == fxDom.n) && (fxDomDegenerate.k == fxDom.k) &&
    (fxDomDegenerate.barycentricWeight == fxDom.barycentricWeight) &&
    (fxDomDegenerate.omega != fxDom.omega)

#eval fxDegenerateRejectionKats_ok      -- expect true

/-- THE EXHIBIT BITES: the same ten clauses evaluated on the OLD domain are not all
    satisfiable - baryWeight fails outright, and the PRE-P-ENV omegaOrder text held only
    because the generator is 1 (see fxDegenerateRejectionKats_ok for the degenerate pair
    with the weight left correct). Stated as a computation over the two records side by
    side, which is what a regression would show up in. -/
def fxEnvAgreesKats_ok : Bool :=
  -- the repaired domain: every clause a computation can check, checked
  (fxDom.omega ^ fxDom.n == 1) && (fxDom.omega ^ 2 != 1) &&
    (fxDom.omegaInv * fxDom.omega == 1) &&
    (fxDom.barycentricWeight * (2 ^ fxDom.k : Fr rp) == 1) &&
    (fxDom.n == 2 ^ fxDom.k) && (fxDom.k == fxPlan.k) &&
    (divCeil (divCeil fxFc.numBits 8) 2 == 16) &&
    (rp == Midfall.Generator.frModulusConstant) &&
    (fxPlan.numNegLagranges == fxCs.blindingFactors.toOption.getD 0 + 1) &&
    -- the old domain: passes the vacuous gate, fails the barycentric one
    (fxDomOld.omega ^ fxDomOld.n == 1) && (fxDomOld.omega ^ 2 == 1) &&
    (fxDomOld.barycentricWeight * (2 ^ fxDomOld.k : Fr rp) != 1) &&
    -- and the constants: s is the two-adicity, and the root has that order exactly
    (fxFc.s == 32) && ((rp - 1) % 2 ^ 32 == 0) && ((rp - 1) % 2 ^ 33 != 0)

#eval fxEnvAgreesKats_ok                -- expect true

end Midfall.Instances.SurfaceFixture

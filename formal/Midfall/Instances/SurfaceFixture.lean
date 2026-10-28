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
--   7. Eip2537.Holds is still NOT exhibited, and P-4a2 did not change that: the
--      blocker is the missing BLS12-381 curve model (D-P1, R-28), not the field
--      arithmetic. See ObligationsGates.gap_holds_unexhibited and encG2AtFixture_ok.
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
    rather than pass quietly. -/
def fxCs : ConstraintSystem (Fr rp) :=
  { ConstraintSystem.default with
    numFixedColumns := 1, numAdviceColumns := 1, numInstanceColumns := 2,
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

/-- The payload image VkLoading copies: two header words, no commitments. Small on
    purpose, for the reason stage 3 gave: the .vk clause of Inv copies the whole
    payload, and a kilobyte of synthetic words makes the kernel exceed its recursion
    limit. -/
def fxPayload : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0x6000,
    constants := [("digest", 7), ("g2base", 8)],
    fixedComms := [], permutationComms := [],
    quotientConstOffsetWords := none, quotientConstWords := 0,
    quotientProgramOffsetWords := none, quotientProgramWords := 0,
    quotientConstLabels := [], quotientConstHeaders := [] }

/-- The plan view: the deployed poseidon memory layout (whose WellFormed and validate
    both decide true, LayoutMemory.lean:869), the payload above, one public instance, a
    size-4 domain, no accumulator arm. -/
def fxPlan : PlanView :=
  { vk := fxPayload,
    vkMptr := Midfall.Generator.LayoutMemoryKats.poseidonLayout.vkMptr,
    memory := Midfall.Generator.LayoutMemoryKats.poseidonLayout,
    proofLayout := Midfall.Generator.poseidonProofLayout,
    numInstances := 1, k := 2,
    -- P-4a2: this was 2, which is what a circuit with ONE blinding factor would walk.
    -- fxCs.blindingFactors is ok 6 (Circuit.lean:1593, and the exhibit below recomputes
    -- it), so EnvAgrees.negLagranges - PV.numNegLagranges = blindingFactors + 1, the
    -- l_blind window of Lagrange.yul:57 - demanded 7 and the fixture was silently
    -- disagreeing with its own ConstraintSystem. Found by trying to exhibit EnvAgrees,
    -- not by reading it: the clause had never been evaluated at this Surface because the
    -- root-of-unity blocker meant nobody got that far.
    numNegLagranges := 7,
    hasAccumulator := false }

/-! ### The seven blocks: the emitter, not a hand-written table -/

/-- THE FIXTURE'S blk IS THE GENERATOR FUNCTION: Midfall/Lowering/GenAst.lean's
    emitPartial, at this fixture's own plan view. Before P-AST this was a hand-written
    table of seven one-statement dummies, which is the R-62 defect in the only Surface in
    the tree: blk was free, so every *_spec theorem quantified over every block. Now the
    fixture's blk, its main block and the BlkIsEmitter pin all come from one function, so
    the pin is rfl HERE and the exhibits below are about surfaces that DEVIATE from it.

    finalPairing, lagrange and traceReturn are real slices; the other four are GenAst's
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

/-- The shell object: the dispatcher block. -/
def fxShell : YulObject := Object.mk "Halo2Verifier" (fxHeadGuard ++ fxMain) [] []

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
    accFixedBases :=
      #[{ name := "-G", base := fx 1, negate := true },
        { name := "b0", base := 1, negate := false }],
    vkDigest := frWord fxVk.transcriptRepr,
    sG2gen := fx 5,
    -- R-58 G2: the encoder used to be `fun _ => Midfall.Bytes.empty`, which is
    -- not an EIP-2537 encoding of anything, so no Eip2537.Holds was satisfiable
    -- at this Surface and every field carrying one was vacuous. The all-zero
    -- 256-byte word is the EIP infinity encoding: valid, and the degenerate
    -- encoder the exponent model can actually supply.
    encG2 := fun _ => Midfall.Yul.bytesZero Midfall.Yul.g2Bytes,
    o₀ := fxOptions, L := fxLowered, lower := fxLower, lower_ok := rfl,
    bindLocals := [], shell := fxShell, shellLayout := fxShellLayout,
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
    evaluator_agrees := rfl,
    encG2_shape := fun _ => by native_decide }

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
    vkNonEmpty := by decide
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
  -- main is the two emitted AssemblyHelpers definitions followed by the seven slices:
  -- FOURTEEN statements, and P-AST3a did NOT change that number - measured, not assumed:
  -- the quotientLin slice is ONE statement before (the placeholder mstore) and ONE statement
  -- after (the linearization SCOPE), so the conversion is invisible to any length count and
  -- the structural clause below is the only thing in this gate that can see it. The
  -- composition is two helpers, three one-statement placeholders, the one-statement
  -- quotientLin scope, the three-statement Lagrange, the two-statement FinalPairing arm and
  -- the three-statement TraceReturn arm; the pre-P-AST fixture carried seven dummies and no
  -- helpers at all, so a real finalPairing slice could not have resolved fail or ec_pairing.
  realSurface.L.main.length == 14 &&
    -- and the first two statements really are those definitions, i.e. mainScope - which
    -- hoists main - can see them. This is the pin's second conjunct as a computation.
    (match realSurface.L.main with
     | Stmt.funDef "fail" _ _ _ :: Stmt.funDef "ec_pairing" _ _ _ :: _ => true
     | _ => false) &&
    (realSurface.blk Partial.vkLoading realSurface.plan).length == 1 &&
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
      fun (q, _i) => (fxPartialBlocks q).length > 0 &&
        (List.zipIdx [Partial.vkLoading, Partial.transcriptParser, Partial.lagrange,
            Partial.quotientLin, Partial.pcs, Partial.finalPairing,
            Partial.traceReturn]).all
          fun (q2, _j) => q == q2 ||
            toString (fxPartialBlocks q) != toString (fxPartialBlocks q2)

#eval mainConcatKats_ok                   -- expect true

/-- The lower pin bites: production options give the program, a trace render is
    refused. A lower that returned .ok for every option would satisfy lower_ok while o0
    pinned nothing about L. The 14 is UNCHANGED by P-AST3a and that is a measurement and not an
    oversight: the quotientLin slice is one statement before the conversion (a flat mstore) and
    one statement after (a scope), so main's LENGTH cannot see this conversion at all -
    mainConcatKats_ok's structural clause is what can, and it is the gate that reddens when the
    emitter ignores its plan (measured: hard-coding k = 6 in emitQuotientLinAt flips
    mainConcatKats_ok and blkPinKats_ok to false while this gate stays green, because 14 is
    still 14). -/
def lowerPinKats_ok : Bool :=
  (match fxLower fxOptions with | .ok l => l.main.length == 14 | .error _ => false) &&
    (match fxLower fxOptionsTrace with | .ok _ => false | .error _ => true) &&
    (match realSurface.lower realSurface.o₀ with
     | .ok l => l.main.length == 14 | .error _ => false)

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
    toString (realSurface.L.headGuard ++ realSurface.bindLocals ++ realSurface.L.main) &&
    ! (toString fxMain ==
      toString (realSurface.L.headGuard ++ realSurface.bindLocals ++ realSurface.L.main)) &&
    ! (toString fxMain == toString (fxHeadGuard ++ fxMain)) &&
    -- and the pin is about THIS shell: a shell built from a different main refutes it
    ! (toString (YulSemantics.Object.codeBlock
        (Object.mk "Halo2Verifier" (fxHeadGuard ++ fxMain.drop 1) [] [] : YulObject)) ==
      toString (realSurface.L.headGuard ++ realSurface.bindLocals ++ realSurface.L.main))

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

/-- R-58 G2. The encoder now returns EIP-2537-shaped bytes for every point, and the
    value it replaced - the empty byte string - does not, so the pin is what forced
    the change rather than a note next to it.

    THE HONEST HALF, stated because the review asked for the field to be exhibited
    and it still is not: fixing encG2 does NOT make `Eip2537.Holds` satisfiable at
    this Surface. The blocking clause is g1Valid, not g2Valid - the exponent codec
    sends a non-identity exponent to bytes no curve check accepts (last line below,
    the same fact vkPointsKats_ok uses to show the clause bites), and D-P1/R-28 say
    there is no BLS12-381 model in the tree to replace it with. So every field that
    carries Holds is still unexhibited, for a named reason that is a model, not a
    missing pin. encG2_shape removed ONE cause of that; it did not remove the only
    cause. -/
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
  Object.mk "Halo2Verifier" (fxHeadGuard ++ plantMainCounterexample) [] []

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

    WHY THESE THREE EXIST. Every plant above this section attacks a pin that was already
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
    shell := Object.mk "Halo2Verifier" (fxHeadGuard ++ m) [] [],
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
    so plantMainWith of this plant has the SAME LENGTH as GenAst.emitMain fxPlan - 14
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

/-- All three placeholder plants keep their replanted main DISTINCT from the emitted main,
    which is the price of being a Surface at all: main_concat is existential over the helper
    prefix only, so a blk change that left main alone would not be a Surface whose slices
    tile the tail of its program. The quotientLin line is the one that matters most, because
    for that plant the two mains have the same LENGTH and only stmtsBeq can tell them apart. -/
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
    -- replanted main has the SAME LENGTH as the emitted main, so this is the only plant in
    -- the file whose difference stmtsBeq can see and a length count cannot.
    ! SyntaxEq.stmtsBeq (plantMainWith plantBlkQuotientLinPlaceholder)
      (GenAst.emitMain fxPlan) &&
    (plantMainWith plantBlkQuotientLinPlaceholder).length =
      (GenAst.emitMain fxPlan).length &&
    (Midfall.Lowering.partials.all fun q =>
      SyntaxEq.stmtsBeq (plantBlkQuotientLinPlaceholder q fxPlan)
        (GenAst.emitPartial fxPlan q) == (q != .quotientLin))

#eval plantPlaceholderMainsDiffer_ok      -- expect true

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
    unexhibited hypothesis of the headline bundle is Eip2537.Holds, which is the curve
    model (note 7), not this. -/
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

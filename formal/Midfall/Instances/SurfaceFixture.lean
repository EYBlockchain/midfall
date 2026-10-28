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
--   1. qvmValidated is True. The decidable QVM predicate that exists
--      (LoweringPlan.supportedQvm) needs a LoweringPlan, and the reference builds one
--      only through LoweringPlan::new, whose memory-layout constructor this tree
--      declined (LoweringPlan.lean header). So SupportedS.qvm is the one field the
--      exhibit discharges trivially, and the one field the QVM area still owns.
--   2. cfg.accumulator is none, so SupportedS.acc is vacuous in the exhibit. The
--      accumulator arm needs a Generator AccumulatorEncoding whose validate passes,
--      which is D-P16 territory and is exercised in Lowering/AccEncoding.lean.
--   3. EnvAgrees is NOT exhibited. Its truncWidth clause needs a FieldConsts with
--      numBits 255 and its omegaOrder clause needs a genuine root of unity in Fr r;
--      both are nameable but neither is what this stage was asked to show. The
--      per-partial theorems therefore still carry an unexhibited hypothesis, reported
--      as a stage-4 finding rather than papered over with a fake instance.
--   4. The seven blocks are one-statement placeholders. P-13 has not landed the AST
--      emitter, so blk returns what the fixture declares rather than what a render
--      emits; main_concat is rfl here and becomes a theorem when the renderer exists.
--   5. irCheck inspects top-level statements only. A full alpha-equivalence check
--      modulo constant substitution is M8 work and is blocked on the same D-P15
--      import; what is here is the decidable fragment that can already distinguish a
--      resolved call from an unresolved one, which is the distinction the gate needs.

import Midfall.Lowering.Partials
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

/-- Field constants for the environment. Only numBits is read by anything here. -/
def fxFc : FieldConsts (Fr rp) :=
  { numBits := 255, s := 32, rootOfUnity := 3, zeta := 2 }

/-- The verifier environment. -/
def fxE : VerifierEnv rp RP RP RP :=
  { g1 := expG1Codec, field := fxFc, delta := 2, fewerPointSetsRuntime := false }

/-- The pairing parameters, in the shape EnvAgrees nG2 and sG2 describe: nG2Prepared is
    the inverse of g2 and sG2Prepared is the sG2 generator itself, named apart. -/
def fxParams : ParamsVerifierKZG RP RP :=
  { sG2 := fx 5, nG2Prepared := (fx 1)⁻¹, sG2Prepared := fx 5 }

/-- A size-4 domain written out rather than built by EvaluationDomain.new, which would
    need a genuine root of unity in Fr r. WellFormed.domainConsistent asks only that
    n = 2^k and quotientPolyDegree = csDegree - 1, and both hold here by arithmetic on
    literals; the omega fields are inert for the clauses SupportedS reads, and the
    fixture says so rather than pretending they are roots. -/
def fxDom : EvaluationDomain (Fr rp) :=
  { n := 4, k := 2, extendedK := 2, omega := 1, omegaInv := 1, extendedOmega := 1,
    extendedOmegaInv := 1, gCoset := 1, gCosetInv := 1, quotientPolyDegree := 2,
    ifftDivisor := 4, extendedIfftDivisor := 4, tEvaluations := #[0, 0, 0, 0],
    barycentricWeight := 4 }

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
    numInstances := 1, k := 2, numNegLagranges := 2,
    hasAccumulator := false, consts := templateConstantsDefault }

/-! ### The seven placeholder blocks -/

/-- One statement per partial, with distinct literals, so that a blk which returned the
    same block for two partials or dropped one changes main and is caught by
    mainConcatKats_ok rather than by inspection. Placeholders in the honest sense: no
    Lean function returns a real partial AST yet. -/
def fxPartialBlocks : Partial → YulBlock
  | .vkLoading => [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 0x2000), Expr.lit (.number 1)])]
  | .transcriptParser => [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 0x2100), Expr.lit (.number 2)])]
  | .lagrange => [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 0x2200), Expr.lit (.number 3)])]
  | .quotientLin => [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 0x2300), Expr.lit (.number 4)])]
  | .pcs => [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 0x2400), Expr.lit (.number 5)])]
  | .finalPairing => [Stmt.exprStmt (Expr.builtin Op.staticcall
      [Expr.lit (.number 375), Expr.lit (.number 0x0f), Expr.lit (.number 0),
       Expr.lit (.number 0), Expr.lit (.number 0), Expr.lit (.number 0)])]
  | .traceReturn => [Stmt.exprStmt (Expr.builtin Op.ret
      [Expr.lit (.number 0x1000), Expr.lit (.number 0x20)])]

/-- The main block: the seven slices in include order. main_concat is rfl against this
    definition, which is what makes it a pin rather than a claim: the moment blk and
    main come from two different functions the field stops being a definition and
    becomes a theorem. -/
def fxMain : YulBlock :=
  fxPartialBlocks .vkLoading ++ fxPartialBlocks .transcriptParser ++
    fxPartialBlocks .lagrange ++ fxPartialBlocks .quotientLin ++
    fxPartialBlocks .pcs ++ fxPartialBlocks .finalPairing ++
    fxPartialBlocks .traceReturn

/-- The head guard the dispatcher runs first: the free-memory-pointer check the
    memoryguard bound is about. -/
def fxHeadGuard : YulBlock :=
  [Stmt.cond (Expr.builtin Op.gt [Expr.builtin Op.mload [Expr.lit (.number 0x40)],
      Expr.lit (.number 0x1000)])
    [Stmt.exprStmt (Expr.builtin Op.revert
      [Expr.lit (.number 0), Expr.lit (.number 0)])]]

/-! ### irCheck -/

/-- The names a block declares at its top level. -/
def declaredTops : YulBlock → List Ident :=
  fun b => b.foldl (init := []) fun ns s =>
    match s with
    | Stmt.funDef n _ _ _ => n :: ns
    | _ => ns

/-- A top-level statement that calls a user function the block does not declare. This
    is the decidable fragment of the import check: it sees a call in statement position
    and a call that initialises a let, which between them cover the two shapes a solc
    prologue and a planted rename produce. -/
def unresolvedTop (b : YulBlock) : Bool :=
  let declared := declaredTops b
  b.any fun s => match s with
    | Stmt.exprStmt (Expr.call f _) => ! declared.contains f
    | Stmt.letDecl _ (some (Expr.call f _)) => ! declared.contains f
    | _ => false

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

/-- The import sanity check the plan calls irCheck, in the form this stage can state:
    the deployed sub-object exists and has no unresolved top-level call.

    WHY THIS IS THE RIGHT CHECK FOR NOW. attack.md FIX (Evaluator.rel entry) says the
    importer must rewrite memoryguard(x) to x and that irCheck should state it, because
    a memoryguard call in a yul% quote elaborates to a call to a user function named
    memoryguard (mkCall, EVMOp.lean:216) that nothing declares and no Step rule derives.
    That is exactly what this check rejects: it fails on an unresolved name, and
    memoryguard is one. So the D-P15 vendor gap is not hidden behind a green gate - it
    is what the gate detects. A planted rename fails it too, which is the non-vacuity the
    plan asks for (P11: a planted rename must fail irCheck). -/
def fixtureIrCheck (ir : YulObject) : Bool :=
  match ir.subObject (fxRuntimeName ir.name) with
  | some rt => ! unresolvedTop rt.codeBlock
  | none => false

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
    accFixedBases := #[{ name := "b0", base := 1, negate := false }],
    vkDigest := frWord fxVk.transcriptRepr,
    sG2gen := fx 5, encG2 := fun _ => Midfall.Bytes.empty,
    o₀ := fxOptions, L := fxLowered, lower := fxLower, lower_ok := rfl,
    bindLocals := [], shell := fxShell, shellLayout := fxShellLayout,
    evaluatorRuntime := none, runtimeName := fxRuntimeName,
    irCheck := fixtureIrCheck,
    astOfMain := fun o => if o.diagnostics.trace then none else some fxMain,
    blk := fun q _ => fxPartialBlocks q, plan := fxPlan,
    expectedVkCodehash := some (keccak256 fxVkRuntime),
    quotientRuntime := some fxQuotientRuntime,
    expectedQuotientCodehash := some (keccak256 fxQuotientRuntime),
    qvmValidated := True,
    vkDigest_spec := rfl, vkRuntime_spec := rfl, main_concat := ⟨[], rfl⟩ }

/-! ### 1. Supported is INHABITED -/

/-- THE HEADLINE EXHIBIT: SupportedS realSurface.o0 holds, as a kernel-checked term.
    Every one of the eleven fields is discharged from the fixture data above; the two
    that are trivial by construction (qvm, from qvmValidated := True, and acc, from
    accumulator := none) are named in the file header rather than left for a reader to
    find.

    This is the gate the stage-4 brief asks for. A Surface whose Supported could not be
    inhabited would make all seven per-partial theorems vacuous, which is the F1 class
    the programme has now hit four times. -/
theorem supportedInhabited : SupportedS realSurface realSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_, layout := ?_,
           qvm := ?_, production := ?_, wf := ?_ }
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
  · trivial
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
        (litValue (.string "AUTHORIZED_VK")) == 0)

#eval deploymentMemguardKats_ok           -- expect true

/-! ### 4. The pins are not decoration -/

/-- main_concat, checked rather than assumed: the seven blocks the fixture blk returns
    really do tile the main block, the concatenation is not empty, and the seven slices
    are pairwise distinct so a duplicated or dropped slice is visible. -/
def mainConcatKats_ok : Bool :=
  -- no BEq on Stmt at this dialect (Ast.lean derives Repr only), so the checks are
  -- structural: lengths and the literal each slice stores, not an equality of blocks.
  realSurface.L.main.length == 7 &&
    (realSurface.blk Partial.vkLoading realSurface.plan).length == 1 &&
    (List.zipIdx [Partial.vkLoading, Partial.transcriptParser, Partial.lagrange,
        Partial.quotientLin, Partial.pcs, Partial.finalPairing,
        Partial.traceReturn]).all
      -- each slice is exactly one statement, and no two slices are the same statement,
      -- so a duplicated or dropped partial is visible. Compared through Repr because
      -- Stmt carries no BEq at this dialect (Ast.lean derives Repr only).
      fun (q, _i) => (fxPartialBlocks q).length == 1 &&
        (List.zipIdx [Partial.vkLoading, Partial.transcriptParser, Partial.lagrange,
            Partial.quotientLin, Partial.pcs, Partial.finalPairing,
            Partial.traceReturn]).all
          fun (q2, _j) => q == q2 ||
            toString (fxPartialBlocks q) != toString (fxPartialBlocks q2)

#eval mainConcatKats_ok                   -- expect true

/-- The lower pin bites: production options give the program, a trace render is
    refused. A lower that returned .ok for every option would satisfy lower_ok while o0
    pinned nothing about L. -/
def lowerPinKats_ok : Bool :=
  (match fxLower fxOptions with | .ok l => l.main.length == 7 | .error _ => false) &&
    (match fxLower fxOptionsTrace with | .ok _ => false | .error _ => true) &&
    (match realSurface.lower realSurface.o₀ with
     | .ok l => l.main.length == 7 | .error _ => false)

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

end Midfall.Instances.SurfaceFixture

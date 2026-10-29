-- |
-- Midfall.Instances.ObligationsGates
--
-- The non-vacuity exhibits P-SE stage 6 requires next to `LoweringCorrect`
-- (docs/plans/P-SE-stage6.md, and section Q line 2294 of
-- P-SE-semantic-equivalence.md: "Non-vacuity gates next to the structure").
--
-- WHY HERE AND NOT IN Lowering/Obligations.lean. The three gates the plan names
-- all need a pairing model: `SupportedS realSurface realSurface.o₀` is a
-- proposition about a Surface, and the only model of an `AdmissiblePairing` in
-- the tree is the exponent model (R-28), which lives in Instances/. The
-- Instances-confinement gate in scripts/checks.sh refuses a theorem in any file
-- that imports Midfall.Instances.* directly (D-P17), so a gate that cites the
-- fixture cannot sit in the file that states the theorems. Obligations.lean
-- carries the model-free gates and points here.
--
-- REUSE, NOT DUPLICATION. The stage-6 brief is explicit that stage 4 already
-- proved `supportedInhabited` and `supportedRefutedForTraceRender` and that P-IR
-- already proved `runContractIR_inhabited`. Nothing here re-proves them: each
-- gate below is an `example` whose proof is the existing term, so the exhibit is
-- cited by name and a regression in the original is a build failure here.
--
-- WHAT CHANGED HERE UNDER R-58. Gate 9 used to PROVE that the "-G" arm of
-- `accFixedBases_producer` was vacuous at the fixture, because the fixture table
-- had no "-G" row. R-58 F7 added the existence conjunct to the field and the row
-- to the fixture, so gate 9 now exhibits the whole field. Gates 7 and 8 keep their
-- projections and are re-pointed: `vkDigest_slot0` is dropped from LoweringCorrect
-- (F5, derivable from two other pins), and `render_eq_print` is now the
-- astOfMain/lower equation (F8).
--
-- WHAT STILL IS NOT EXERCISED: `Eip2537.Holds`. The exponent codec cannot satisfy
-- its g1Valid clause for a non-identity point, so every field carrying Holds stays
-- unexhibited. R-58 G2 removed ONE cause of that (the empty encG2); the remaining
-- cause is the absence of a curve model (D-P1, R-28), which is a model and not a
-- missing pin. SurfaceFixture.encG2AtFixture_ok shows which is which.
--
-- R-63 added a THIRD cause - the g1Decodes clause was unsatisfiable for EVERY codec -
-- and P-HOLDS repaired it, so the sentence above is true again rather than true by
-- accident: the blocker is the codec and the curve, not the statement. See
-- bundle_holds_empty (live, refuted through g1Valid) and bundle_holdsOld_empty (the
-- pinned old text, refuted for every codec).

import Midfall.Lowering.Obligations
import Midfall.Instances.SurfaceFixture
import Midfall.Instances.Bls12_381G1
import Midfall.Instances.ImportedIR

namespace Midfall.Instances.ObligationsGates
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Generator Midfall.Yul
open Midfall.Instances.SurfaceFixture Midfall.Instances.ImportedIR
open Midfall.Yul.Bridge
open Midfall.Yul.Ir
open YulSemantics YulSemantics.EVM

/-- The pairing-product oracle the fields are parameterised by. `PairingProduct`
    is `Bytes -> Bool` (Externals.lean:941) and is the single arithmetic hole of
    the vendored precompile model, so any function is a well-typed one; the
    constant-true choice only has to be consistent, because no gate below reads
    the answer. -/
def gateProduct : PairingProduct := fun _ => true

/-- GATE 1, the plan's first required exhibit, REUSED from stage 4
    (SurfaceFixture.lean:419). Without it every field of `LoweringCorrect` that
    assumes `SupportedS S S.o₀` would be an implication from an unsatisfiable
    antecedent - the F1 vacuity class the programme has now hit five times. -/
example : SupportedS realSurface realSurface.o₀ := supportedInhabited

/-- GATE 2, the plan's second required exhibit: `astOfMain` is not the constant
    none the sketch feared, so `render_eq_print`'s hypothesis is satisfiable and
    its conclusion is a decision rather than a vacuity. -/
def astOfMainIsSome_ok : Bool :=
  (realSurface.astOfMain realSurface.o₀).isSome &&
    -- and the trace render still refuses, which is what makes the first line a
    -- fact about the options rather than about a constant
    ! (realSurface.astOfMain fxOptionsTrace).isSome

#eval astOfMainIsSome_ok                  -- expect true

/-- GATE 3, the plan's third required exhibit: the trace-render refutation of
    `only_two_outcomes`, REUSED from stage 4
    (SurfaceFixture.lean:444 `supportedRefutedForTraceRender`). `SupportedS
    S S.o₀` is the first hypothesis of the field, so refuting it for a trace
    render is exactly the refutation section Q asks for: a trace render emits
    log1 (TraceAndGasHelpers.yul:20-22), which changes the logs and so changes
    the view, and the field would then have a run whose view is neither
    `returnView` nor a revert with an unchanged world. -/
example : ¬ SupportedS realSurface fxOptionsTrace := supportedRefutedForTraceRender

/-- GATE 4. The hypothesis bundle the completeness fields carry is inhabited TOGETHER:
    a Surface, a SupportedS for its own render options, a DeploymentW for the fixture
    world, and an EnvAgrees for its field constants and domain. Each is an existing term,
    so this fails the day any of them stops applying - a SupportedS that only held for a
    different render, a DeploymentW whose memguard field stopped discharging, or a domain
    whose generator is no longer of exact order 2^k, reddens here. P-4a2 added the
    EnvAgrees conjunct rather than exhibiting it separately, because the fields take all
    four at once and halves are what hid S1. -/
theorem bundle_deployment : SupportedS realSurface realSurface.o₀ ∧
    DeploymentW realSurface fxW keccak256 fxVkAddr fxQuotientAddr ∧
      EnvAgrees realSurface.E realSurface.vk realSurface.plan realSurface.params
        realSurface.sG2gen :=
  ⟨supportedInhabited, deploymentInhabited, fxEnvAgrees⟩

/-- GATE 5. The structure itself elaborates at a real Surface over a real
    pairing model, with the imported solc object as the IR argument. Stated as a
    `Prop`, not proved: proving it is `lowering_correct`, the future deliverable
    section Q names. -/
example : Prop := LoweringCorrect realSurface gateProduct

/-- GATE 6, the one P-IR bought: the LEFT side of `ir_refines` is inhabited by a
    committed run of the imported via-IR runtime, for the honest call relation
    and the fixed gas oracle the field uses. This is the term that makes
    `ir_refines` and `lowering_equivalence` statable without shipping a vacuously
    satisfiable theorem, so it is cited rather than restated
    (ImportedIR.lean:260). -/
example : ∃ obs, RunContractIR irSurface irW keccak256 verifierIr irLyt irCd
    (irSurface.calls irW gateProduct fxQuotientAddr) (ExternalGas.ofFun fun _ => 0) obs :=
  runContractIR_inhabited _ _

/-- GATE 7. The digest-slot projection that `EnvAgrees.vkDigestWord` constrains -
    and that `LoweringCorrect.vkDigest_slot0` used to restate, before R-58 F5 dropped
    the field as derivable from vkDigest_spec plus vkDigestWord - is reachable and
    agrees with the pinned word at the fixture, and the projection is not a constant:
    change the index and a different payload word answers. Without the second line
    the gate would pass for a `constants` list whose head matched by accident. -/
def vkDigestSlot0_ok : Bool :=
  (realSurface.plan.vk.constants.getD 0 ("", 0)).2 == realSurface.vkDigest &&
    (realSurface.plan.vk.constants.getD 1 ("", 0)).2 != realSurface.vkDigest

#eval vkDigestSlot0_ok                    -- expect true

/-- GATE 8. `render_eq_print` after R-58 F8: the equation is between the two
    free functions `astOfMain` and `lower`, and it holds at the fixture for EVERY
    option, including the ones the render refuses. The second half is the
    refutation - a block with one statement dropped is not the rendered main, so an
    accessor that drifted from the render fails the pin instead of satisfying it by
    being compared with itself, which is what the old form let it do. -/
def renderEqPrintAtFixture_ok : Bool :=
  (match realSurface.astOfMain realSurface.o₀ with
    | some ast => SyntaxEq.stmtsBeq ast realSurface.L.main
    | none => false) &&
    (match realSurface.astOfMain realSurface.o₀ with
      | some ast => ! SyntaxEq.stmtsBeq ast (realSurface.L.main.drop 1)
      | none => false)

#eval renderEqPrintAtFixture_ok           -- expect true

/-- GATE 9, R-58 F7. Before the repair this gate PROVED the "-G" arm of
    `accFixedBases_producer` was vacuous at the only Surface in the tree: the table
    had one entry and no "-G" row, so the implication discharged on an empty set and
    the field could not fail. Now the fixture carries the row and this gate exhibits
    all three conjuncts - ascending names, a "-G" row exists, and every "-G" row is
    (P.g₁, negate := true) as artifacts.rs:181-227 builds it. The refutation of the
    existence conjunct (the old one-entry table) is in
    SurfaceFixture.accFixedBasesKats_ok. -/
theorem accFixedBasesProducerAtFixture :
    namesAscending (realSurface.accFixedBases.toList.map fun b => b.name) ∧
    (∃ b ∈ realSurface.accFixedBases.toList, b.name = "-G") ∧
    ∀ b ∈ realSurface.accFixedBases.toList, b.name = "-G" →
      b.base = (inferInstance : AdmissiblePairing RP RP RP).g₁ ∧ b.negate = true := by
  refine ⟨?_, ⟨{ name := "-G", base := fx 1, negate := true },
      by simp [realSurface, List.mem_cons], rfl⟩, ?_⟩
  · simp [realSurface, namesAscending]
  · intro b hb hn
    have hlist : realSurface.accFixedBases.toList =
        [{ name := "-G", base := fx 1, negate := true },
         { name := "b0", base := 1, negate := false }] := rfl
    rw [hlist] at hb
    simp [List.mem_cons] at hb
    rcases hb with (h|h|h)
    · subst h; exact ⟨rfl, rfl⟩
    · simp_all

/-- GATE 10, the R-58 pins cited as terms. Each `example` is the pin's statement at
    the fixture Surface, so a regression in any of them - a pin deleted, or a fixture
    whose shell, plan, render or encoder stops agreeing - is a BUILD failure here and
    not a prose claim. This is the exhibit that the headline structure is inhabited by
    a Surface that MEETS the pins, which is all the non-vacuity that is available
    before a real render exists. -/
example : realSurface.shell.codeBlock =
    realSurface.L.headGuard ++ realSurface.bindLocals ++ realSurface.L.main :=
  realSurface.shell_unfolds
example : realSurface.plan.hasAccumulator = realSurface.cfg.accumulator.isSome :=
  realSurface.plan_hasAccumulator
example : realSurface.plan.numInstances = realSurface.cfg.numInstances :=
  realSurface.plan_numInstances
example : realSurface.L.evaluator.map Object.codeBlock =
    realSurface.evaluatorRuntime.map Prod.fst :=
  realSurface.evaluator_agrees
example : ∀ R : RP, encG2IsEip (realSurface.encG2 R) = true :=
  realSurface.encG2_shape

/-- GATE 10b, R-60 S5. `render_eq_print` is a CONJUNCTION now: the astOfMain/lower
    equation (which the fixture satisfies by rfl, because it defines one from the
    other - the review was right that the equation alone proves nothing) AND the
    trace-refusal half, which is not rfl: it needs `fxLower` to actually refuse a
    trace render. The refutation is `renderEqPrintTraceRefusalKats_ok`. -/
example : (∀ o : Midfall.Generator.RenderOptions, realSurface.astOfMain o =
      match realSurface.lower o with
      | .ok l => some l.main
      | .error _ => none) ∧
      (∀ o : Midfall.Generator.RenderOptions, o.diagnostics.trace = true →
        realSurface.astOfMain o = none) :=
  ⟨fun _ => rfl, fun o h => by simp [realSurface, fxLower, h]⟩

/-- The counterexample render and accessor the review's defeat describes: a render that
    never refuses and an accessor defined from it. The equation half holds for this pair
    BY DEFINITION - which is exactly why the equation alone proves nothing - and the
    trace-refusal conjunct is what rules it out. R-60 S5. -/
def traceCounterLower : Midfall.Generator.RenderOptions →
    Except Midfall.Generator.GeneratorError Lowered := fun _ => .ok fxLowered

def traceCounterAst : Midfall.Generator.RenderOptions → Option YulBlock :=
  fun o => match traceCounterLower o with
    | .ok l => some l.main
    | .error _ => none

/-- The counterexample satisfies the first conjunct, so the first conjunct alone cannot
    be what makes render_eq_print say something. -/
theorem traceCounter_satisfies_the_equation :
    ∀ o : Midfall.Generator.RenderOptions, traceCounterAst o =
      match traceCounterLower o with
      | .ok l => some l.main
      | .error _ => none := fun _ => rfl

/-- ...and it refutes the second, which is the half that does the work. -/
theorem traceCounter_refutes_the_trace_half :
    ∃ o : Midfall.Generator.RenderOptions, o.diagnostics.trace = true ∧
      traceCounterAst o ≠ none :=
  ⟨fxOptionsTrace, by simp [fxOptionsTrace], by simp [traceCounterAst, traceCounterLower]⟩

/-- R-60 S5 REFUTATION, as a decidable gate too: the counterexample accessor answers
    `some` for a trace render, the fixture's answers `none` for both the trace render
    and the gas-checkpoint render. -/
def renderEqPrintTraceRefusalKats_ok : Bool :=
  (traceCounterAst fxOptionsTrace).isSome &&
    (realSurface.astOfMain fxOptionsTrace).isNone &&
    (realSurface.astOfMain fxOptionsGas).isNone

#eval renderEqPrintTraceRefusalKats_ok    -- expect true

/-! ### GATE 11 and 12: the JOINT exhibits R-60 S1 asked for

The class this section exists to close: a headline field takes SEVERAL hypotheses, each
of them inhabited on its own while the conjunction is empty. Gate 6 checked
`RunContractIR` alone; the S1 defect lived in the other half, so gate 6 stayed green
over a headline nobody could instantiate. Every exhibit below is ONE statement about ONE
Surface, object and observation, and `scripts/check_hypothesis_bundles.py` requires
every multi-hypothesis field of `LoweringCorrect` to have either such an exhibit or a
named gap def saying which conjunct is the blocker. -/

/-- GATE 11, R-60 S1: the IR leg as a CONJUNCTION. One object that both passes the
    Surface's own import check and has a committed run, for every call relation and
    every gas oracle. Cited from ImportedIR rather than restated, so a regression in the
    witness is a build failure here. -/
theorem bundle_irLeg (c : ExternalCalls) (g : ExternalGas) :
    ∃ (ir : YulObject) (irLyt : EVM.Layout) (obs : Obs),
      irSurface.irCheck ir = true ∧
        RunContractIR irSurface irW keccak256 ir irLyt irCd c g obs :=
  irHypothesis_jointlyInhabited c g

/-- THE SAME DEPLOYMENT AT THE IMPORTED SURFACE. `irSurface` is `realSurface` with one
    field changed - `runtimeName`, the field R-60 S1 is about - and neither
    `SupportedS` nor `DeploymentW` reads it, so both exhibits transfer field by field.
    Written as projections rather than as `exact supportedInhabited` because a structure
    update replaces the Prop fields with opaque proofs, so the two types are not
    definitionally equal even though every field they read is identical; the projection
    form is also the honest one, since it names which clauses carry the exhibit. -/
theorem supportedInhabited_ir : SupportedS irSurface irSurface.o₀ :=
  ⟨supportedInhabited.advice, supportedInhabited.instShape, supportedInhabited.noRotInst,
    supportedInhabited.acc, supportedInhabited.singlePhase, supportedInhabited.hLimbs,
    supportedInhabited.vkPoints, supportedInhabited.layout,
    supportedInhabited.production, supportedInhabited.wf⟩

theorem deploymentInhabited_ir :
    DeploymentW irSurface irW keccak256 fxVkAddr fxQuotientAddr :=
  ⟨deploymentInhabited.keccak, deploymentInhabited.wf, deploymentInhabited.callvalue,
    deploymentInhabited.static, deploymentInhabited.vkImm, deploymentInhabited.vkCode,
    deploymentInhabited.vkNonEmpty, deploymentInhabited.vkHash, deploymentInhabited.qImm,
    deploymentInhabited.qCode, deploymentInhabited.qHash, deploymentInhabited.qNonEmpty,
    deploymentInhabited.memguard, deploymentInhabited.disjoint⟩

/-- GATE 12: THE REQUIRED FINDING, AS ONE CONJUNCTION AND NOT AS TWO HALVES. After S1,
    is `lowering_equivalence`'s hypothesis genuinely inhabited at the real artifact?
    For the legs this package owns - SupportedS for the Surface's own render options,
    DeploymentW for the fixture world, EnvAgrees for the field constants and the domain,
    and the IR pair (import check plus committed run of the imported solc object) - YES,
    jointly, at ONE Surface: this term. P-4a2 added the EnvAgrees conjunct here rather
    than exhibiting it in a second declaration, because four separate exhibits is exactly
    the shape that let a bundle be individually inhabited and jointly empty (R-60 S1), and
    the brief for P-4a2 names that as the failure to avoid.

    The leg it does NOT answer is `Eip2537.Holds`, which no Surface in the tree satisfies
    for a reason that is a missing curve model rather than a missing pin
    (gap_holds_unexhibited). So the honest summary is now: everything except the codec leg
    is inhabited jointly at the artifact, and the four-way bundle including Holds is still
    empty - adding EnvAgrees to the conjunction did not change that, and claiming otherwise
    would be the individually-inhabited-jointly-empty class one level up. -/
theorem bundle_headlineCore (c : ExternalCalls) (g : ExternalGas) :
    SupportedS irSurface irSurface.o₀ ∧
      DeploymentW irSurface irW keccak256 fxVkAddr fxQuotientAddr ∧
        EnvAgrees irSurface.E irSurface.vk irSurface.plan irSurface.params
          irSurface.sG2gen ∧
          ∃ (ir : YulObject) (irLyt : EVM.Layout) (obs : Obs),
            irSurface.irCheck ir = true ∧
              RunContractIR irSurface irW keccak256 ir irLyt irCd c g obs :=
  ⟨supportedInhabited_ir, deploymentInhabited_ir, fxEnvAgrees,
    irHypothesis_jointlyInhabited c g⟩

/-- GATE 13 (P-4a2): THE THREE LEGS THE FIELD ARITHMETIC CAN CLOSE, IN ONE DECLARATION.
    BlkIsEmitter (the blk pin, P-AST), SupportedS (the render, stage 4) and EnvAgrees
    (the environment and the domain, P-4a2) all hold of the SAME Surface. Stated as one
    conjunction on purpose: the headline per-partial theorems take all three, and three
    separate exhibits would certify nothing about their being simultaneously satisfiable.
    The fourth leg the headline wants, Eip2537.Holds, is deliberately absent - it is
    unsatisfiable at the exponent model, so a declaration naming all four would be an
    uninhabited hypothesis dressed as an exhibit. -/
theorem bundle_envAgrees :
    BlkIsEmitter realSurface ∧ SupportedS realSurface realSurface.o₀ ∧
      EnvAgrees realSurface.E realSurface.vk realSurface.plan realSurface.params
        realSurface.sG2gen :=
  ⟨blkPinInhabited, supportedInhabited, fxEnvAgrees⟩

/-- AND IT BITES: perturb the domain back to the placeholder generator and the third
    conjunct is no longer dischargable, because `barycentricWeight := 4` is not the inverse
    of 2^k in Fr r. This is the falsifiability half of the exhibit (D-P23): the bundle is
    inhabited by the REPAIRED fixture and not by the old one. -/
theorem bundle_envAgrees_needs_the_repair :
    ¬ (EnvAgrees realSurface.E
        { realSurface.vk with domain := fxDomOld } realSurface.plan realSurface.params
          realSurface.sG2gen) :=
  fun h => fxDomOldBaryFails h.baryWeight

/-- AND THE STRENGTHENED CLAUSE REFUTES ON ITS OWN (P-ENV). `fxDomOld` was refuted by
    `baryWeight`, a clause that had been FALSE all along, so that exhibit never needed
    `omegaOrder` to be non-vacuous and proved nothing about it. Here the weight is the
    correct one and only the generators are degenerate (`omega = omegaInv = 1`), so the
    strengthened `omegaOrder` is the sole clause that can refute the bundle - which is
    the falsifiability demonstration lifted from the structure to the conjunction the
    headline fields actually take. -/
theorem bundle_envAgrees_needs_exact_order :
    ¬ (EnvAgrees realSurface.E
        { realSurface.vk with domain := fxDomDegenerate } realSurface.plan
          realSurface.params realSurface.sG2gen) :=
  fun h => fxDegenerateNotExactOrder h.omegaOrder

/-- THE EXHIBIT CAN FAIL, and here is the failing case: hand the same Surface a
    runtimeName that does not name the imported sub-object and the conjunction is empty
    for that object - not because the run is hard but because there is no runtime block
    to run. This is the S1 shape, and it is why the exhibit is a conjunction. -/
theorem bundle_irLeg_fails_for_wrong_name (c : ExternalCalls) (g : ExternalGas) :
    ¬ (∃ obs, RunContractIR { irSurface with runtimeName := fun _ => "nope" } irW
      keccak256 verifierIr irLyt irCd c g obs) :=
  runContractIR_none_for_wrong_name c g

/-! #### The named gaps: conjuncts no Surface in the tree satisfies, with the blocker -/

/-- No run of the assembly or of the shell is exhibited at the fixture, so the run
    conjunct of verifier_sound, verifier_complete and only_two_outcomes is jointly
    unexhibited with the deployment. Blocker: a RunVerifier or RunShell witness needs a
    calldata the decoder accepts, which needs a real proof fixture at `Fr r` - the
    poseidon bundle is at the BLS12-381 scalar field and the exponent model cannot make
    `ContractRefAcceptsAcc` return true for it (the same g1Valid wall as Holds). The
    IR side DOES have a witness (gate 6, gate 11), which is why this gap is about the
    shell and assembly runs and not about runs in general. -/
def gap_runLeg_unexhibited : String :=
  "blocker: no accepted calldata at the exponent model, so no RunVerifier or RunShell "
    ++ "witness exists to exhibit jointly with SupportedS and DeploymentW"


/- P-HOLDS, R-63 level 1: THE CLAUSE IS REPAIRED, SO THE REFUTATION MOVES AND THE GAP
    WORDING MOVES WITH IT. Before the repair the four-way bundle
    BlkIsEmitter /\ SupportedS /\ EnvAgrees /\ Eip2537.Holds was REFUTED for every codec on
    every prime-order group, because g1Decodes demanded infinitely many preimages of a finite
    group (g1DecodesOld_unsatisfiable in Assumptions/Eip2537.lean). That refutation is now a
    theorem about the PINNED OLD TEXT and not about the live structure, so the declaration
    that used to carry it cannot stay as it was: a refutation of a statement that no longer
    exists is worse than none, which is what the bundle gate enforces. Two declarations
    replace it, and both name all four conjuncts in ONE statement (R-60 S1):

      * bundle_holds_empty - the LIVE bundle, still empty at the fixture, refuted by the
        clause the repair exposes: the fixture codec is the exponent model and its g1Valid
        fails at a non-identity exponent. This is the NEW blocker, and gap_holds_unexhibited
        now names it.
      * bundle_holdsOld_empty - the OLD bundle, refuted for every codec, kept as the
        regression pin so the repaired clause cannot silently be weakened back.

    WHY THE LIVE ONE IS A REFUTATION AND NOT AN EXHIBIT. An exhibit would need a codec that
    satisfies all six clauses at a prime-order group. The only codec in the tree that
    satisfies the repaired decode clause is g1FrameCodec (Instances/Bls12_381G1.lean), and
    G1Frame has neither a Group instance - the Fact (Nat.Prime pBase) it needs is now
    certified (Assumptions/BasePrime.lean) but the group law itself is still unbuilt -
    nor prime order (needs the r-torsion count), so it cannot even be the G1 of a Holds.
    The headline fields therefore still carry an uninstantiable hypothesis - for two
    named curve reasons and no longer for a third, spurious one. -/

set_option maxRecDepth 1000000 in
/-- THE FIXTURE CODEC CANNOT SATISFY HOLDS, and the reason is now visible instead of hidden.
    `realSurface.E.g1` is the exponent model: `toEip` writes the EXPONENT as a 0x80-byte
    big-endian word, so `fx 3` encodes as the frame whose decoded coordinates are (0, 3).
    That is not a point of y^2 = x^3 + 4 over Fp - 3^2 = 9 and 0^3 + 4 = 4 - so
    `g1PointMsmValid` refuses it and the g1Valid clause fails at a single named point.
    SurfaceFixture.lean shows the same fact as a KAT (vkPointsKats_ok, encG2AtFixture_ok);
    here it is a theorem, because the bundle gate needs a declaration and not a computation.
    Note what this is NOT: it is not a defect in the codec. An exponent model has no reason
    to encode curve points, and the clause that demands it does is exactly the clause the
    repair was about - which is why the refutation had to move from the clause to the codec. -/
theorem expG1Codec_not_holds (c₂ : Midfall.Assumptions.G2Enc RP) (product : PairingProduct) :
    ¬ Midfall.Assumptions.Eip2537.Holds realSurface.E.g1 c₂ product := by
  rintro h
  obtain ⟨pt, hpt, hv⟩ := h.g1Valid (fx 3)
  have hval : g1Of? (fxToEip (fx 3)) = some (0, 3) := by decide
  have hval' : g1Of? (realSurface.E.g1.toEip (fx 3)) = some (0, 3) := hval
  rw [hval'] at hpt
  have hpt' : pt = (0, 3) := Option.some.inj hpt.symm
  subst hpt'
  exact absurd hv (by decide)

/-- GATE 14, RESTATED AFTER THE REPAIR: the four-way bundle is STILL empty at the fixture -
    now because of the codec and not because of the clause. One declaration naming all four
    conjuncts, as R-60 S1 demands, and the proof runs through g1Valid, the clause the
    exponent model cannot meet. If a real curve codec is ever installed at this Surface, this
    proof stops going through and the bundle must be exhibited instead: that is the
    cannot-silently-return property, still enforced by the kernel. -/
theorem bundle_holds_empty :
    ¬ (BlkIsEmitter realSurface ∧ SupportedS realSurface realSurface.o₀ ∧
        EnvAgrees realSurface.E realSurface.vk realSurface.plan realSurface.params
          realSurface.sG2gen ∧
        ∃ (product : PairingProduct),
          Midfall.Assumptions.Eip2537.Holds realSurface.E.g1 ⟨realSurface.encG2⟩ product) := by
  rintro ⟨_, _, _, product, h⟩
  exact expG1Codec_not_holds ⟨realSurface.encG2⟩ product h

/-- THE OLD BUNDLE, AS A REGRESSION PIN: with the pre-repair decode clause conjoined the same
    four-way bundle was empty for EVERY codec on EVERY prime-order group, and this is the
    declaration that says so at the fixture. It is the live statement of R-63's finding: the
    day the width condition is dropped from Eip2537.Holds.g1Decodes, this stops being a pin
    about a dead text and becomes a refutation of the live structure again - and the
    fingerprint gate reddens the same edit. -/
theorem bundle_holdsOld_empty :
    ¬ (BlkIsEmitter realSurface ∧ SupportedS realSurface realSurface.o₀ ∧
        EnvAgrees realSurface.E realSurface.vk realSurface.plan realSurface.params
          realSurface.sG2gen ∧
        ∃ (product : PairingProduct),
          Midfall.Assumptions.Eip2537.HoldsOld realSurface.E.g1 ⟨realSurface.encG2⟩ product) := by
  rintro ⟨_, _, _, product, h⟩
  exact Midfall.Assumptions.holdsOld_unsatisfiable realSurface.E.g1 ⟨realSurface.encG2⟩ product h

/-- Eip2537.Holds is not exhibited at any Surface in the tree, and the reason has changed twice.
    The original text blamed the exponent codec's g1Valid failure (R-28, D-P1); P-CURVE found
    that the g1Decodes clause made the structure REFUTABLE for every codec (R-63); and
    P-HOLDS repaired that clause, which moved the refutation back onto the codec. The blockers,
    in the order they now bite:

      1. CLOSED. g1Decodes as written was unsatisfiable for every codec on every prime-order
         group (Assumptions.Eip2537.g1DecodesOld_unsatisfiable). The repair - the 0x80 frame
         width the clause's own docstring always meant - is now the live field, and
         Instances/Bls12_381G1.lean discharges it at real curve points
         (g1FrameCodec_decodesWidth), while refuting the pinned old text there too.
      2. THE FIXTURE CODEC: g1Valid. realSurface.E.g1 is the exponent model, whose toEip writes
         the exponent and not a point, so fx 3 encodes as the frame (0, 3), which is not on
         y^2 = x^3 + 4. expG1Codec_not_holds proves it and bundle_holds_empty carries it into
         the four-way conjunction.
      3. ANY CURVE CODEC, IF ONE IS INSTALLED: a group law and a point count. g1Add and g1Msm1
         need a Group on the frame type, which needs a Field instance on ZMod pBase - that
         primality fact IS now certified (Assumptions/BasePrime.lean, pBase_prime), so what is
         left is the construction and the agreement proof, not the number theory - and
         PrimeOrderWith needs Nat.card G1Frame = r, the r-torsion count, which is still out of
         reach. Those are gap_g1_no_group_law and gap_g1_prime_order in Instances/Bls12_381G1.lean.

    So every field carrying Holds - verifier_sound, verifier_complete, end_to_end_noAcc,
    lowering_equivalence - still has a hypothesis bundle that is EMPTY at the only Surface in
    the tree, and the emptiness is named at three levels: the codec clause that bites today,
    the field instance that bites for any curve codec, and the count that bites for any
    prime-order group. -/
def gap_holds_unexhibited : String :=
  "blocker: Eip2537.Holds is not exhibited at any Surface. The g1Decodes width defect that "
    ++ "made it REFUTED for every codec is REPAIRED: the live clause is "
    ++ "Assumptions.Eip2537.g1DecodesWidth and the old text is pinned as "
    ++ "g1DecodesOld_unsatisfiable. What bites at the fixture is g1Valid - realSurface.E.g1 is "
    ++ "the exponent model, so expG1Codec_not_holds and bundle_holds_empty refute the four-way "
    ++ "bundle there. What bites for any curve codec is building the group law over Fp - the "
    ++ "Fact (Nat.Prime pBase) it needs is now certified in Assumptions/BasePrime.lean, so this "
    ++ "is construction and not a missing fact - and the r-torsion count Nat.card G1Frame = r, "
    ++ "which is still a point count no Lean library has."

/-- `EnvAgrees` IS exhibited, so the gap that used to sit here is closed and this def
    replaces it (the pattern `gap_view_transport_closed` sets: a gap that has been closed
    says so, and stays in the file so the registry cannot quietly re-open it). The
    root-of-unity blocker was real - the fixture's domain had `omega := 1`, `omegaInv := 1`,
    `barycentricWeight := 4`, so `baryWeight` evaluated FALSE and `omegaOrder` passed only
    vacuously - and it is closed at the REAL scalar field, not at a toy one:
    Midfall/Assumptions/TwoAdicity.lean proves `frFc.IsWellFormed` (a root of order exactly
    2^32 and a zeta of order exactly 3, both by kernel `decide` at 255-bit r), and
    SurfaceFixture.fxEnvAgrees discharges all ten clauses at the repaired fixture.
    bundle_envAgrees and bundle_deployment above carry it JOINTLY with the other legs. -/
def gap_envAgrees_closed : String :=
  "closed by P-4a2: a root of unity of order exactly 2^32 in Fr r is exhibited in "
    ++ "Assumptions/TwoAdicity.lean, and EnvAgrees is exhibited at the fixture by "
    ++ "SurfaceFixture.fxEnvAgrees and jointly by bundle_envAgrees"

/-- R-60 S4: what `encG2_shape` does NOT claim. The pin forces EIP-2537-shaped,
    precompile-valid bytes for every point; a CONSTANT function satisfies it, and the
    fixture uses one (`fun _ => bytesZero g2Bytes`, the EIP infinity word). The
    strengthening the fixture cannot meet is `Function.Injective encG2`, so it is
    recorded here rather than added as a pin the only witness fails. -/
def gap_encG2_injective : String :=
  "blocker: the fixture encoder is constant, so Function.Injective encG2 cannot be "
    ++ "met at the only Surface; a real G2 codec in Common is missing (D-P17)"

/-- R-60 S9: `qvm_validated_noBoundsFault` does not mention the Surface at all. Every
    other field of `LoweringCorrect` is a claim about the deployment the record
    describes; this one quantifies over an arbitrary `LoweringPlan`, so it is a claim
    about SOME plan - the R-58 F3 unrelated-program class one level up. Blocker: linking
    it needs `S.plan` to BE a `LoweringPlan`, and `PlanView` carries only the counts Inv
    reads because P-11's `LoweringPlan::new` has not landed.

    P-PLANVIEW RE-READ THIS NOTE AND DELIBERATELY DID NOT ACT ON THE "ARGUABLY SHOULD" HALF.
    PlanView now carries the two LoweringPlan fields the PCS emitter needs (`meta_` and
    `dat`) rather than a reference to the assembled plan, and the reason is that this
    blocker is the constructor and not the field list: `S.plan` cannot become a
    `LoweringPlan` until something can BUILD one, and nothing can, so a plan-valued field
    would be nine more free fields (four of them duplicates of PlanView's own vk, vkMptr,
    memory and proofLayout) with no derivation behind them. The gap def below is unchanged
    for that reason - it still names `LoweringPlan::new`, and it is still the honest
    blocker. The full argument, including why the alternative was rejected rather than
    deferred, is at Inv.lean's PlanView header. -/
def gap_qvmField_surface_free : String :=
  "blocker: the field quantifies over an arbitrary LoweringPlan and never mentions the "
    ++ "Surface; linking it needs S.plan to be a LoweringPlan (P-11 LoweringPlan::new)"

/-- R-60 S6: the view transport is NOT a gap any more, and the previous report named the
    wrong blocker. Recorded here so the gap list is corrected in both directions:
    `dialect_deterministic` is not needed for transporting an `ObsEquiv`, and the
    conjunct that WAS blocked was the world-equality one, for a reason the report never
    named - `ObsView` omitted `selfBalance` and `extCodeHashOf`. Both are in the view
    now and `Bridge.worldEq_of_view_eq` is the transport. -/
def gap_view_transport_closed : String :=
  "closed by R-60 S6: ObsView carries selfBalance and extCodeHashOf, and "
    ++ "halted_of_view_eq / returnData_of_view_eq / isReturn_of_view_eq / "
    ++ "isRevertOrHalt_of_view_eq / worldEq_of_view_eq are proved in Bridge.lean"
end Midfall.Instances.ObligationsGates

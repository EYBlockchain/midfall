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
-- WHAT STILL IS NOT EXERCISED: a single `Eip2537.Holds` TERM, and the reason is no
-- longer the reason this header gave for two rounds. R-58 G2 removed one cause (the
-- empty encG2); R-63 found a third - g1Decodes was unsatisfiable for EVERY codec - and
-- P-HOLDS repaired it; and the cause blamed above, "the absence of a curve model
-- (D-P1, R-28)", is no longer the whole story either. A real-curve model EXISTS and
-- discharges all FOUR G1-side clauses at one codec on one carrier (g1CodecZ_g1_four,
-- Instances/G1PointCount.lean), so what keeps every field carrying Holds unexhibited
-- is now ONE other clause: pairing2 at real points, which needs an AdmissiblePairing
-- on the curve groups and is D-P36's standing decision. g2Valid was the other one and it
-- is CLOSED: the Fp2 model landed in P-G2 (Instances/Fp2.lean) and the codec in P-G2B
-- (Instances/G2Codec.lean, the exponent-fold carrier G2fold with encoder g2foldToEip),
-- and the wording gap_g2_no_fp2_model used for it while it was open was an over-statement
-- that the same record now corrects: the constant all-zero encoder satisfied g2Valid all
-- along, so what was missing was a non-degenerate codec and not a field. The exponent codec's g1Valid
-- failure is still what refutes the four-way bundle AT THIS FIXTURE - see
-- bundle_holds_empty - but that is a fact about which codec the fixture installs, and
-- expG1Codec_not_holds is about the EXPONENT codec and stays true however good the
-- curve codec gets. bundle_holdsOld_empty pins the repaired decode defect.
-- SurfaceFixture.encG2AtFixture_ok shows which is which.

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

    The leg it does NOT answer is `Eip2537.Holds`, which no Surface in the tree satisfies -
    for reasons that are ONE missing MODEL (a curve AdmissiblePairing for pairing2) and not a
    missing pin, and no longer for anything on the G1 side or the G2 side: g2Valid is discharged
    at the exponent-fold codec in Instances/G2Codec.lean (gap_holds_unexhibited,
    gap_g2_no_fp2_model). So the honest summary is now:
    everything except the Holds leg is inhabited jointly at the artifact, and the four-way
    bundle including Holds is still empty - adding EnvAgrees to the conjunction did not change
    that, and claiming otherwise would be the individually-inhabited-jointly-empty class one
    level up. -/
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
        fails at a non-identity exponent. That is a fact about WHICH CODEC THE FIXTURE
        INSTALLS, and gap_holds_unexhibited says so - it is no longer the open mathematics.
      * bundle_holdsOld_empty - the OLD bundle, refuted for every codec, kept as the
        regression pin so the repaired clause cannot silently be weakened back.

    WHY THE LIVE ONE IS STILL A REFUTATION AND NOT AN EXHIBIT - RE-READ BY P-GAPFIX, because
    the paragraph this def used to carry is now false in its middle. It said the only codec in
    the tree satisfying the repaired decode clause was g1FrameCodec, and that G1Frame had
    neither a Group instance nor prime order, "so it cannot even be the G1 of a Holds". Two
    of those three claims are overtaken: the r-torsion count is a theorem
    (torsion_eq_zpowers_gen), and there IS a codec on a prime-order real-curve carrier that
    satisfies all four G1-side clauses jointly - g1CodecZ on G₁z, exhibited by
    g1CodecZ_g1_four (Instances/G1PointCount.lean). What is still true, and is the whole
    reason this declaration stays a refutation, is that an exhibit AT THIS SURFACE needs
    `realSurface.E.g1` to be that codec, and `VerifierEnv.g1` is typed over the Surface's own
    `AdmissiblePairing`: the only pairing model in the tree is the exponent model (R-28), so
    installing the curve codec means installing a curve pairing, which is D-P36's open
    decision and not a field assignment. The headline fields therefore still carry an
    uninstantiable hypothesis - for the pairing and the G2 model, and no longer for anything
    about G1's group law, its base primality or its count. -/

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

/-- Eip2537.Holds is not exhibited at any Surface in the tree, and the reason has changed
    three times. The original text blamed the exponent codec's g1Valid failure (R-28, D-P1);
    P-CURVE found that the g1Decodes clause made the structure REFUTABLE for every codec
    (R-63); P-HOLDS repaired that clause, which moved the refutation back onto the codec; and
    P-POINTCOUNT then closed the last G1-side item, which is why this record had to be
    re-pointed rather than left alone. A gap that recites closed blockers reads to the next
    agent as a current claim, and that is the failure this project keeps hitting. The items,
    in the order they now bite:

      1. CLOSED (R-63 / P-HOLDS). g1Decodes as written was unsatisfiable for every codec on
         every prime-order group (Assumptions.Eip2537.g1DecodesOld_unsatisfiable). The repair -
         the 0x80 frame width the clause's own docstring always meant - is now the live field,
         and Instances/Bls12_381G1.lean discharges it at real curve points
         (g1FrameCodec_decodesWidth), while refuting the pinned old text there too.
      2. CLOSED (P-CURVE / P-G1CODEC / P-POINTCOUNT). The whole G1 side is FOUR OF FOUR at a
         real-curve codec: g1CodecZ_g1_four exhibits g1Valid, g1Add, g1Msm1 and g1Decodes
         TOGETHER at g1CodecZ on the zpowers carrier G₁z of the published generator, with no
         new named assumption. The two blockers this record used to blame for any curve codec
         are theorems now: the Fact (Nat.Prime pBase) the group law needs is certified by a
         Lucas/Pratt certificate (Assumptions/BasePrime.lean, pBase_prime), and the r-torsion
         count is proved elementarily (Instances/G1PointCount.lean, torsion_eq_zpowers_gen,
         from #E(Fp) <= 2p+1 < r^2). gap_g1_no_group_law and gap_g1_prime_order in
         Instances/Bls12_381G1.lean are re-pointed to match: the first is still open as
         construction at the FRAME type, the second is closed as mathematics.
      3. CLOSED (P-G2 then P-G2B): g2Valid. The Fp2 model is Instances/Fp2.lean and the codec is
         Instances/G2Codec.lean (the exponent-fold carrier G2fold, encoder g2foldToEip). THE
         WORDING THIS RECORD CARRIED WHILE IT WAS OPEN WAS AN OVER-STATEMENT, and it is corrected
         in the body rather than deleted: g2Valid was never a clause with an empty domain, because
         the constant all-zero encoder satisfies it on any carrier. What was missing was a
         NON-DEGENERATE codec, not a field. gap_g2_no_fp2_model below carries the durable half of
         the old record - the G1 pigeonhole does NOT transfer over Fp2, so the count argument must
         not be re-run by analogy, which is why the carrier is cyclic-by-exponent.
      4. OPEN, SECOND REMAINING CLAUSE: pairing2 at real points. The clause is discharged only
         at the exponent model (Instances/PairingProduct.lean,
         pairing2_holds_for_the_defined_product), whose toEip writes an exponent and not a
         curve point, so it is not an exhibit at a curve group. What is needed is an
         AdmissiblePairing on the exhibited groups, and D-P36 stands: assume it as a named
         hypothesis or construct Fp12, and construction is larger than this project.
      5. AND A THIRD, SEPARATE FACT ABOUT THE FIXTURE - not an open theorem. realSurface.E.g1
         IS the exponent codec, so expG1Codec_not_holds and bundle_holds_empty still refute
         the four-way bundle at the only Surface in the tree. That is a statement about which
         codec the fixture installs, and installing a curve codec is not free: VerifierEnv.g1
         is typed over the Surface's own pairing, so it needs the same AdmissiblePairing as
         item 4. The two open clauses and the fixture wall are TWO walls, not three.

    So every field carrying Holds - verifier_sound, verifier_complete, end_to_end_noAcc,
    lowering_equivalence - still has a hypothesis bundle that is EMPTY at the only Surface in
    the tree, and the emptiness is named at ONE open level and three closed ones: the pairing
    instance no Surface has (open), and - no longer - anything about G1's group law, its base
    primality or its point count, or about a G2 field or a G2 codec (all closed). The fixture wall
    of item 5 is a fourth fact and it is not an open theorem. -/
def gap_holds_unexhibited : String :=
  "blocker: Eip2537.Holds is still not exhibited as a single term at any Surface, and the open half "
    ++ "is no longer a G1 question and no longer a G2 question either. The G1 side is FOUR OF FOUR "
    ++ "at a real-curve codec: g1CodecZ_g1_four (Instances/G1PointCount.lean) exhibits g1Valid, "
    ++ "g1Add, g1Msm1 and g1Decodes together at g1CodecZ on the zpowers carrier G₁z of the published "
    ++ "generator, with no new named assumption. So the three blockers this record used to name are "
    ++ "CLOSED and must not be read as open: the g1Decodes width defect is repaired (live clause "
    ++ "Assumptions.Eip2537.g1DecodesWidth, old text pinned as g1DecodesOld_unsatisfiable), the "
    ++ "Fact (Nat.Prime pBase) the group law needs is certified by a Pratt certificate "
    ++ "(Assumptions/BasePrime.lean, pBase_prime), and the r-torsion count Nat.card G1Frame = r is a "
    ++ "theorem (torsion_eq_zpowers_gen, from #E(Fp) <= 2p+1 < r^2). The G2 side is CLOSED TOO: the "
    ++ "Fp[u]/(u^2+1) model landed in P-G2 (Instances/Fp2.lean, with the agreement between mathlib's "
    ++ "group law and the byte model fp2Ops) and the codec landed on top of it in P-G2B (Instances/"
    ++ "G2Codec.lean: the exponent-fold carrier G2fold and its encoder g2foldToEip, discharging "
    ++ "g2Valid non-degenerately). ONE clause remains: pairing2 at real points. The clause is "
    ++ "discharged only at the exponent model (Instances/PairingProduct.lean), whose toEip writes an "
    ++ "exponent and not a curve point, so it is not an exhibit at a curve group; what is needed is "
    ++ "an AdmissiblePairing on the exhibited groups, and D-P36 stands - assume it as a named "
    ++ "hypothesis or construct Fp12, and construction is larger than this project. WHAT IS STAGED "
    ++ "(P-G2B): holds_staged in Instances/HoldsStaging.lean exhibits Eip2537.Holds as ONE term at "
    ++ "g1CodecZ and g2CodecFold given exactly that hypothesis as a binder, so the distance to the "
    ++ "landmark is one named assumption and not a construction - and the encoder-first FrameLaws "
    ++ "law P-G2B was told could stall it holds (g1zToEip_injective, via ptPair_injective). Second, and "
    ++ "separate: at the FIXTURE the four-way bundle is refuted because realSurface.E.g1 IS the "
    ++ "exponent codec, so expG1Codec_not_holds and bundle_holds_empty still hold there. That is "
    ++ "about WHICH CODEC THE FIXTURE INSTALLS and not about a missing G1 or G2 theorem - and it is "
    ++ "not free to change either, because VerifierEnv.g1 is typed over the Surface's own pairing, "
    ++ "so installing the curve codec means installing a curve AdmissiblePairing: the remaining "
    ++ "clause again, and so ONE wall, not three. Third, a correction to this record's own history, "
    ++ "kept because a gap that over-states its blocker is the same defect as one that under-states "
    ++ "it: while g2Valid was open this record described it as a clause with an empty domain, which "
    ++ "was too strong - the constant all-zero encoder satisfies it on ANY carrier "
    ++ "(g2Valid_degenerate_constant_encoder), because g2PointValid short-circuits on the infinity "
    ++ "branch and g2Of? accepts the 0x100 zero frame. What was missing was a non-degenerate codec, "
    ++ "not a field. And the G1 squeeze still does not transfer to G2: over Fp2 the same elementary "
    ++ "fiber bound is 2p^2 + 1 while r^2 is about p^(4/3), so 2p^2 + 1 > r^2 and the pigeonhole "
    ++ "that made the G1 count elementary is vacuous there - see gap_g2_no_fp2_model."

/-- THE G2 BLOCKER AS A NAMED REGISTRY RECORD (P-GAPFIX). gap_holds_unexhibited names g2Valid
    as one of the two open clauses, and a blocker that lives only inside another gap's prose
    is a blocker nobody is held to: the registry can enforce tokens against a NAMED def and
    against nothing else. This is that def.

    WHY IT IS A MODEL AND NOT A PIN, AND WHY THE NAME IS STALE. The def is called
    'gap_g2_no_fp2_model' because when P-GAPFIX wrote it the tree really had only the BYTE half of
    Fp2 - 'fp2Ops', integer arithmetic on pairs over 'ZMod blsP'. P-G2 landed the ALGEBRAIC half
    (Instances/Fp2.lean: 'Fp[u]/(u^2+1)' as a Field, with the agreement between 'fp2Ops' and
    mathlib's group law) and P-G2B landed the codec, so the name outlived the claim and the body
    says so. The name is kept rather than renamed because the registry keys on it and a renamed gap
    is a deleted gap; the body is what carries the claim.

    WHAT THE CLAUSE ACTUALLY ASKS. g2Valid quantifies over R : G₂ and asks that the encoder's bytes
    decode through the precompile's own validators (g2Of? / g2PointValid, Midfall/Yul/Externals.lean)
    - which, as the body records, the DEGENERATE all-zero encoder already satisfies. The content of
    the item was never a quantifier with an empty domain; it was a non-degenerate codec.

    THE FINDING THAT DECIDES THE COST, recorded so the next package does not re-derive it.
    P-POINTCOUNT made the G1 count elementary with one squeeze: #E(Fp) <= 2p+1 < r^2, so two
    independent r-torsion points would not fit. Over Fp2 the same elementary bound is
    2p^2 + 1 and r^2 is about p^(4/3), i.e. far BELOW it, so the pigeonhole is vacuous and
    the G1 route cannot be re-run for G2. Both inequalities are pinned as a COMPUTATION by
    gapHoldsBlockers_ok below rather than asserted in prose.

    AND THE CHEAPER ROUTE THE FAILURE DOES NOT BLOCK, because recording only the wall would
    over-state it: Holds has no g2Decodes clause, so a G2 carrier taken as the CYCLIC subgroup
    generated by a published H2 needs r • H2 = 0 and H2 <> 1 and NO count at all - D-P34's
    route, Assumptions.Eip2537.primeOrderWith_zpowers, the same lemma that made the G1 side
    prime-order without a count. The count route is closed for G2; the cyclic-subgroup route
    is open, and it is the one to walk. -/
def gap_g2_no_fp2_model : String :=
  "closed by P-G2B: g2Valid, the second clause of Eip2537.Holds, is discharged at a non-degenerate "
    ++ "codec. And the wording of this record, while it was open, was an OVER-STATEMENT that "
    ++ "is corrected here rather than quietly replaced. THE OVER-STATEMENT: the record said g2Valid "
    ++ "had no model to be discharged at because the tree had no Fp2. The Fp2 model landed in P-G2 "
    ++ "(Instances/Fp2.lean: Fp[u]/(u^2+1), pBase % 4 = 3 so the quotient is a field, and the "
    ++ "agreement between mathlib's group law and the byte model fp2Ops), but the claim was too "
    ++ "strong even before that. g2Valid is satisfied by the CONSTANT all-zero encoder on ANY "
    ++ "carrier, because g2PointValid short-circuits on the infinity branch and g2Of? accepts the "
    ++ "0x100 zero frame - proved as g2Valid_degenerate_constant_encoder, with g2Valid_zero_frame "
    ++ "doing the byte work, in Instances/G2Codec.lean. What was missing was a non-degenerate "
    ++ "codec, not a field. THE NON-DEGENERATE CODEC IS WHAT P-G2B LANDED: the exponent-fold carrier "
    ++ "G2fold with encoder g2foldToEip, injective because addOrderOf (emb2 h2Frame) = blsR, whose "
    ++ "bytes are the smulFrame2 fold at the published H2, so canonicity is smulFrame2_canonic and "
    ++ "no AdjoinRoot quotient is ever read back. THE FINDING THAT DECIDES THE COST is kept because "
    ++ "it is durable and independent of the codec: the G1 count route does NOT transfer. The G1 "
    ++ "count followed from #E(Fp) <= 2p+1 < r^2, while over Fp2 the same elementary fiber bound is "
    ++ "2p^2 + 1 against r^2 ~ p^(4/3), so 2p^2 + 1 > r^2 and the pigeonhole proves nothing there - "
    ++ "which is why the carrier is cyclic-by-exponent (D-P34's route, "
    ++ "Assumptions.Eip2537.primeOrderWith_zpowers) and no G2 point count is attempted."

/-- D-P23 FOR THE GAP RECORDS THEMSELVES (P-GAPFIX). A rewritten gap is a claim, and a claim
    with no way to fail is decoration. This gate is the Lean-side twin of the body-only tokens
    in scripts/check_hypothesis_bundles.py: the registry reddens from outside the build, and
    this reddens lake build itself if a token is dropped or if a record reverts to the closed
    G1 or G2 blame. The first six conjuncts pin the clauses and the models they needed and the
    exhibit that closed the G1 side; the next four pin the same for the G2 record; the four after
    that pin the P-G2B CORRECTION ITSELF - the codec's name 'g2foldToEip', 'non-degenerate',
    'all-zero encoder', 'closed by P-G2B' - so the record cannot be rewritten back to the old
    over-statement while still naming the tokens; then come the COUNT of open clauses and the
    acknowledgement that the G1 side is closed, because the wording that IS the finding cannot be
    inverted while a token list still passes; then the forbidden phrases - blame for items since
    closed, which no required-token check can ever catch because required tokens only force a
    record to say MORE; and the last three conjuncts pin the ARITHMETIC the transfer failure rests
    on rather than trusting the prose - 2p+1 < r^2 over Fp (the squeeze that WORKED),
    r^2 < 2p^2 + 1 over Fp2 (the squeeze that does NOT), and p ≡ 3 mod 4 (which makes u^2 + 1
    irreducible and the quotient a field). -/
def gapHoldsBlockers_ok : Bool :=
  (gap_holds_unexhibited.contains "g2Valid") &&
    (gap_holds_unexhibited.contains "pairing2") &&
    (gap_holds_unexhibited.contains "Fp[u]/(u^2+1)") &&
    (gap_holds_unexhibited.contains "2p^2 + 1") &&
    (gap_holds_unexhibited.contains "AdmissiblePairing") &&
    (gap_holds_unexhibited.contains "g1CodecZ_g1_four") &&
    (gap_g2_no_fp2_model.contains "g2Valid") &&
    (gap_g2_no_fp2_model.contains "Fp[u]/(u^2+1)") &&
    (gap_g2_no_fp2_model.contains "2p^2 + 1") &&
    (gap_g2_no_fp2_model.contains "fp2Ops") &&
    -- P-G2B: the over-statement correction is part of the claim, so it is pinned too. A rewrite
    -- that drops "non-degenerate" or drops the codec's name has quietly re-opened the old blame.
    (gap_g2_no_fp2_model.contains "non-degenerate") &&
    (gap_g2_no_fp2_model.contains "g2foldToEip") &&
    (gap_g2_no_fp2_model.contains "all-zero encoder") &&
    (gap_g2_no_fp2_model.contains "closed by P-G2B") &&
    -- and the retired blame must not come back into either record.
    ! (gap_g2_no_fp2_model.contains "has no Fp2") &&
    ! (gap_g2_no_fp2_model.contains "nothing to quantify over") &&
    -- the COUNT of open clauses is part of the claim, so it is pinned as a token and not left
    -- to prose: a rewrite that keeps every blocker name while saying "one clause remains", or
    -- that un-closes the G1 side, reddens here and in the registry.
    (gap_holds_unexhibited.contains "ONE clause remains") &&
    (gap_holds_unexhibited.contains "FOUR OF FOUR") &&
    (gap_holds_unexhibited.contains "g2foldToEip") &&
    -- and the staged landmark: the record must name the term that exhibits Holds under the one
    -- remaining hypothesis, so it cannot be rewritten back to "nothing is staged".
    (gap_holds_unexhibited.contains "holds_staged") &&
    (gap_holds_unexhibited.contains "g1zToEip_injective") &&
    -- and the mirror image: phrases that named a now-CLOSED blocker as open. The registry can
    -- force a gap to say more; only a forbidden-phrase check stops a record re-adding a
    -- retired blame while keeping every required token.
    ! (gap_holds_unexhibited.contains "no Lean library has") &&
    ! (gap_holds_unexhibited.contains "still out of reach") &&
    ! (gap_holds_unexhibited.contains "nothing to quantify over") &&
    ! (gap_holds_unexhibited.contains "no Fp2 model in the tree") &&
    (2 * blsP + 1 < blsR * blsR) &&
    (blsR * blsR < 2 * blsP * blsP + 1) &&
    (blsP % 4 == 3)

#eval gapHoldsBlockers_ok                   -- expect true

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

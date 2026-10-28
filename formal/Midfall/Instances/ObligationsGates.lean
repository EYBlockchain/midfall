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
-- WHAT THE FIXTURE DOES NOT EXERCISE, stated rather than glossed: the fixture's
-- `accFixedBases` is a one-entry table with no "-G" row, so the second conjunct
-- of `accFixedBases_producer` is VACUOUS at the only Surface in the tree. That
-- is recorded as a proved refutation below, not left for a reader to find.

import Midfall.Lowering.Obligations
import Midfall.Instances.SurfaceFixture
import Midfall.Instances.ImportedIR

namespace Midfall.Instances.ObligationsGates
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Generator Midfall.Yul
open Midfall.Instances.SurfaceFixture Midfall.Instances.ImportedIR
open Midfall.Yul.Ir
open YulSemantics YulSemantics.EVM

/-- The pairing-product oracle the fields are parameterised by. `PairingProduct`
    is `Bytes -> Bool` (Externals.lean:941) and is the single arithmetic hole of
    the vendored precompile model, so any function is a well-typed one; the
    constant-true choice only has to be consistent, because no gate below reads
    the answer. -/
def gateProduct : PairingProduct := fun _ => true

/-- GATE 1, the plan's first required exhibit, REUSED from stage 4
    (SurfaceFixture.lean:372). Without it every field of `LoweringCorrect` that
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
    (SurfaceFixture.lean:398 `supportedRefutedForTraceRender`). `SupportedS
    S S.o₀` is the first hypothesis of the field, so refuting it for a trace
    render is exactly the refutation section Q asks for: a trace render emits
    log1 (TraceAndGasHelpers.yul:20-22), which changes the logs and so changes
    the view, and the field would then have a run whose view is neither
    `returnView` nor a revert with an unchanged world. -/
example : ¬ SupportedS realSurface fxOptionsTrace := supportedRefutedForTraceRender

/-- GATE 4. The hypothesis bundle the completeness fields carry is inhabited
    TOGETHER: a Surface, a SupportedS for its own render options, and a
    DeploymentW for the fixture world. Each is an existing term, so this fails
    the day any of them stops applying - a `SupportedS` that only held for a
    different render, or a `DeploymentW` whose memguard field stopped
    discharging, reddens here. -/
example : SupportedS realSurface realSurface.o₀ ∧
    DeploymentW realSurface fxW keccak256 fxVkAddr fxQuotientAddr :=
  ⟨supportedInhabited, deploymentInhabited⟩

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

/-- GATE 7. `vkDigest_slot0`'s left-hand projection is reachable and agrees with
    the pinned word at the fixture, and the projection is not a constant: change
    the index and a different payload word answers. Without the second line the
    gate would pass for a `constants` list whose head happened to match by
    accident. -/
def vkDigestSlot0_ok : Bool :=
  (realSurface.plan.vk.constants.getD 0 ("", 0)).2 == realSurface.vkDigest &&
    (realSurface.plan.vk.constants.getD 1 ("", 0)).2 != realSurface.vkDigest

#eval vkDigestSlot0_ok                    -- expect true

/-- GATE 8. `render_eq_print`'s conclusion holds at the fixture's placeholder
    program - the AST `astOfMain` returns IS the `L.main` the render pin
    produces - and fails for a program with one statement dropped, so the
    conjunct is a decision and not a tautology. -/
def renderEqPrintAtFixture_ok : Bool :=
  (match realSurface.astOfMain realSurface.o₀ with
    | some ast => SyntaxEq.stmtsBeq ast realSurface.L.main
    | none => false) &&
    (match realSurface.astOfMain realSurface.o₀ with
      | some ast => ! SyntaxEq.stmtsBeq ast (realSurface.L.main.drop 1)
      | none => false)

#eval renderEqPrintAtFixture_ok           -- expect true

/-- GATE 9, THE FINDING ABOUT `accFixedBases_producer`. The first conjunct is
    satisfiable at the fixture - a one-entry table is ascending, and the
    producer's own ordering is what `namesAscending` pins. The second conjunct
    is VACUOUS here, and this proves it rather than admitting it in prose: the
    fixture table has no "-G" row, so no Surface in the tree exercises the
    `b.name = "-G"` arm. The exhibit that would discharge it is the
    artifacts.rs:181-227 producer, a generator-side deliverable, not a
    statement obligation. -/
theorem accFixedBasesFirstConjunct_ok :
    namesAscending (realSurface.accFixedBases.toList.map fun b => b.name) := by
  simp [realSurface, namesAscending]

theorem accFixedBasesNegGArmIsVacuous :
    ¬ ∃ b ∈ realSurface.accFixedBases.toList, b.name = "-G" := by
  intro h
  exact absurd h (by simp [realSurface])

end Midfall.Instances.ObligationsGates

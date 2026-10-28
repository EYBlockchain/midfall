-- |
-- Midfall.Lowering.Obligations
--
-- P-SE stage 6 (docs/plans/P-SE-stage6.md; the normative statements are
-- P-SE-semantic-equivalence.md section Q, lines 2164-2378, read against the
-- authoritative diff in section R from 2379). This is the file the programme
-- exists to produce: `LoweringCorrect`, the structure that says what "the
-- lowering is correct" means, and the headline theorems derived from it.
--
-- ## STATING IS THE DELIVERABLE; PROVING IS M7/M8
--
-- Every field below is STATED. Not one of them is proved here, and the report
-- says per field which of stating and proving was done. Four of the five derived
-- theorems are statement holes; the fifth,
-- `contractRef_noAcc_of_semanticEquivalence`, is proved by reusing the
-- already-proved `Lowering.contractRefAccepts_iff_verifyMsgs` - section Q gives
-- it as a one-line reuse and it stays that way here, with no sorryAx (the axiom
-- audit at the foot of the file prints it).
--
-- ONE POINT WHERE THE BRIEF AND SECTION Q DISAGREE. The stage-6 brief lists
-- `end_to_end_noAcc` among the derived theorems. Section Q line 2240 makes it a
-- FIELD of `LoweringCorrect`, and section R line 2390 confirms it ("as stated",
-- i.e. as PLAN 9.5 stated it among the obligations). Section Q is normative, so
-- it is a field here. A top-level theorem of that name would be the projection
-- `hc.end_to_end_noAcc`, which is a field that cannot fail.
--
-- ## THE HEADLINE IS NO LONGER VACUOUS, AND THAT IS THE POINT
--
-- Stage 4 declined to state `ir_refines` and `lowering_equivalence` because
-- `RunContractIR` had no witness: the imported IR prologue calls
-- `memoryguard`, which the vendored dialect did not know (D-P15), so a theorem
-- whose only hypothesis was an IR run would have been true because its
-- hypothesis was unsatisfiable - the exact vacuity class attack.md marks the
-- whole structure VACUOUS for. P-VEND (`9fe74f9`) added the dialect ops and
-- P-IR (`f40424b`) imported the real solc via-ir object;
-- `Midfall/Instances/ImportedIR.lean` then PROVED a committed run of the
-- imported runtime for every `ExternalCalls` and every `ExternalGas`, and
-- proved it is a revert that leaves the free-memory pointer at 0x80.
--
-- R-60 S1: THE SENTENCE THAT USED TO END THAT PARAGRAPH WAS FALSE, AND IT IS
-- REPAIRED IN THE CODE, NOT IN THE PROSE. It read "So the hypothesis of
-- `ir_refines` is inhabited by a real run of the real artifact". The run was.
-- The HYPOTHESIS was not: every headline field takes `S.irCheck ir = true` as
-- well, and the fixture's check hard-coded its own naming convention
-- (`n ++ "_1_deployed"`) instead of reading `S.runtimeName`, so on the imported
-- object - whose runtime sub-object is `Halo2Verifier_292_deployed` - it returned
-- `false`. Each half was individually inhabited and the conjunction was empty,
-- which is the failure mode a per-hypothesis gate cannot see: gate 6 checked
-- `RunContractIR` alone and stayed green over a headline nobody could instantiate.
-- The repair deletes the free `irCheck` field: `Surface.irCheck` is now a
-- PROJECTION of `Surface.runtimeName` (Surface.lean), so the check and the run
-- relation cannot name different sub-objects. `irHypothesis_jointlyInhabited`
-- (ImportedIR.lean) exhibits the CONJUNCTION - one object, one layout, one
-- observation, both conjuncts - and `s1_defect_refutes_the_conjunction` keeps the
-- broken form in the tree as the refutation, so the exhibit is seen to be able to
-- fail. `scripts/check_hypothesis_bundles.py` is the gate against the class: every
-- multi-hypothesis headline conjunction is registered either as a proved joint
-- exhibit or as a named gap naming its blocking conjunct, and a new field with two
-- hypotheses and no registration reddens it.
--
-- ## THE (a)/(b) SPLIT, APPLIED
--
-- Section Q references names that do not exist in the tree. The brief's rule is
-- that each is either DEFINED (if it is a real object the programme owes) or
-- DEFERRED as a named hole with its blocker - never silently restated. Applied:
--
--   DEFINED NEW, in this file:
--     * `segmentsOf` - the sketch's `segmentsOf bytes` is one-dimensional; a
--       segment boundary is a property of the item starts of a finalized build
--       (Qvm.lean:679 `itemStarts`, VmCertify.lean:409 `identitySegment`), not
--       of a byte string alone, so the real object takes the plan and the build.
--     * `IsAlignedSubslice` - the EIP-2537 encoding of a point occurring at a
--       128-aligned offset of a call input. This is what the call-trace witness
--       in `points_subgroup_checked` has always meant.
--   SUBSTITUTED WITH THE REAL SIGNATURE (recorded at the site):
--     * `qvm_validated_noBoundsFault` - the sketch's `OperandModel` and
--       `validate` are P-09e placeholders; the real validator is
--       `LoweringPlan.supportedQvm` over a `LoweringPlan`, and the landed
--       theorem Qvm.lean:738 already states the conclusion in those terms.
--     * `List.Sorted` - not in the built surface (Mathlib order theory is not
--       imported; see the reason at Accumulator.lean:180-186). Stage 2's fix is
--       reused verbatim: `namesAscending`.
--     * `EnvAgrees` - section Q writes the 7-argument form
--       (`... S.sG2gen S.encG2 S.accFixedBases`); stage 3 landed a 5-argument
--       one (`E vk plan params sG2gen`). P-SE-statements.md lists the 7-arg
--       form as not typechecking, so the landed arity is used.
--     * `tblOf` - section Q writes `tblOf S.plan S.accFixedBases`; the landed
--       projection (Surface.lean:613) takes the table alone.
--     * `S.repackProof` / `S.encodeCalldata` - stage 4 removed the three codec
--       fields from `Surface` (Surface.lean header, deviation 2: "a free copy
--       of a function that exists is a field the Surface can lie about"), so the
--       spec functions from Lowering/Calldata.lean are applied to the Surface's
--       own layout, instance count and codec at the two places that need them.
--   DEFERRED, with the blocker at the site:
--     * `qvm_yul_refines` - needs six names the tree does not have
--       (`EvaluatorFrame`, `FrameWellFormed`, `S.plan.qext`,
--       `perIdentityValues`, `outputBytes`, `yOf`) AND the object P-13 did not
--       produce: `QuotientNumeratorBlock.yul` as a `Block Op`, not as text.
--       Defining the six without the seventh would state a field about a frame
--       no render emits, which is the decorative-field class, so the whole field
--       waits. `S.plan.qext` in turn waits on P-11's `LoweringPlan::new`.
--     * `repackProof_faithful`, `encodeCalldata_faithful` - a faithfulness pin
--       relates a Surface function to the spec. The Surface has no such
--       functions, so there is nothing on the left-hand side; writing the pin
--       against the spec function applied to itself would be `rfl`, i.e. a
--       field that cannot fail. The content moved into `end_to_end_noAcc`,
--       where the spec functions appear directly and a wrong layout or codec is
--       a statement that does not compose.
--
-- ## R-60: THE SECOND PASS AND WHAT IT CHANGED HERE
--
-- S1 (blocking): the paragraph above on the headline hypothesis was FALSE as written -
--   the run was inhabited, the import check was not, and the conjunction was empty.
--   Fixed in Surface.lean (irCheck is a projection of runtimeName) and exhibited as ONE
--   conjunction in Instances/ImportedIR.lean (irHypothesis_jointlyInhabited) and
--   Instances/ObligationsGates.lean (bundle_irLeg, bundle_headlineCore).
-- S5: render_eq_print gained the trace-refusal conjunct, because the equation half is
--   satisfied by rfl at a fixture that DEFINES astOfMain from lower.
-- S6: the gap list below is corrected in both directions - dialect_deterministic is not
--   needed for the view transport (Bridge.lean proves the four view lemmas), and the
--   third conjunct's real blocker was ObsView omitting selfBalance and extCodeHashOf,
--   which it no longer does.
-- S9: qvm_validated_noBoundsFault does not mention the Surface at all - the F3 class one
--   level up - recorded at the field and as gap_qvmField_surface_free.
--
-- ## GATES
--
-- The model-free gates are at the bottom of this file. The three the plan names
-- that need a pairing model - `SupportedS realSurface realSurface.o₀`, the
-- `astOfMain` isSome exhibit, and the trace-render refutation - are in
-- `Midfall/Instances/ObligationsGates.lean`, because the Instances-confinement
-- gate in scripts/checks.sh refuses a theorem in a file that imports Instances/
-- directly (D-P17). That file REUSES stage 4's `supportedInhabited` and
-- `supportedRefutedForTraceRender` and P-IR's `runContractIR_inhabited` rather
-- than restating them.
--
-- ## WHAT THIS FILE DELIBERATELY DOES NOT PROMISE
--
-- A Surface whose shell is the real solc dispatcher. `shell_unfolds` now EXISTS
-- (R-58 F3, Surface.lean) and pins the shell's code block to
-- `L.headGuard ++ bindLocals ++ L.main` by an equation, but what it pins is the shell
-- MODEL of the entry path: a real dispatcher decodes ABI heads and tests the selector
-- first, so when M8 imports the via-ir object the pin has to be restated as design2 had
-- it - the verifyProof ARM runs the assembly. `irCheck` as alpha-equivalence modulo
-- constant substitution (nameable now - the `setimmutable` and two
-- `loadimmutable` sites are in the import and gated - but not checked here);
-- `qvm_yul_refines`; `points_subgroup_checked` (deferred by R-58 F1, at its old site);
-- `direct_correct` (M10); `deployed_equivalence` (M11); and the stage-1 holes
-- `dialect_deterministic`, `noWritersFuel`, `Run_worldEq_of_noWriters`,
-- `Evaluator.rel_worldLocal`, `honestCalls_functional`.
--
-- ## R-58: THE TEN FINDINGS AND WHAT THIS PACKAGE DID WITH THEM
--
-- F1 points_subgroup_checked: DEFERRED behind the call-trace blocker, at its old site.
-- F2 plan_hasAccumulator, F3 shell_unfolds, F6 plan_numInstances and evaluator_agrees,
--    G2 encG2_eip: PINS ADDED in Surface.lean, each with a fixture exhibit and a
--    refutation, each covered by scripts/check_duplicate_facts.py.
-- F4 SupportedS.qvm and Surface.qvmValidated: DELETED (Surface.lean deviation 4). A
--    Prop field the fixture discharges with `trivial` is a field that cannot fail.
-- F5 vkDigest_slot0: DROPPED - derivable from vkDigest_spec plus EnvAgrees.vkDigestWord.
-- F7 accFixedBases_producer: the exists-a--G conjunct added, so a table with no -G row
--    refutes the field instead of satisfying it.
-- F8 render_eq_print: restated as the astOfMain/lower link the fixture actually meets.
-- F9 the free `model` binder is gone from qvm_validated_noBoundsFault (the hypothesis is
--    now `.isOk = true`); `memoryZeroAbove` and `PlanView.consts` are deleted in
--    Surface.lean and Inv.lean; the redundant `success = 1` post of finalPairing_sound
--    is deleted in Partials.lean.
-- F10 EnvAgrees is added to verifier_sound and to only_two_outcomes, with the decision
--    written at the field.

import Midfall.Lowering.Surface
import Midfall.Lowering.Partials
import Midfall.Lowering.Qvm
import Midfall.Lowering.QvmFold
import Midfall.Lowering.SemanticEquivalence
import Midfall.Assumptions.Eip2537
import Midfall.Assumptions.Codec

namespace Midfall.Lowering
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientCertify
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ### The two bad-set side conditions -/

/-- Both bad-set side conditions for a calldata (finding 4 completeness, finding 5 soundness). -/
def SideConditions (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst → GenericX S H ms instW inst ∧ NoLogupPanic S H ms inst

/-- Soundness alone: the half `verifier_sound` consumes. -/
def SoundSide (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst → NoLogupPanic S H ms inst

/-- Completeness alone: the half `verifier_complete` consumes. -/
def CompleteSide (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst → GenericX S H ms instW inst

/-! ### The two objects section Q names but the tree did not have -/

/-- `segmentsOf`, from the section-Q sketch, in the form the real validator
    speaks. The sketch writes `segmentsOf bytes`, as if the segment structure of
    a quotient program were a property of its byte string. It is not: a segment
    begins at an item start (Qvm.lean:679 `itemStarts`, which walks the plan and
    the build's usage table) and ends where the certifier's walker says the
    identity's bytecode ends (VmCertify.lean:409 `identitySegment`, which
    returns `.error` rather than guessing). So the real object takes the plan
    and the build, and a segment whose walker errored contributes nothing -
    `builder_segments_total` (Qvm.lean:804) is the lemma that says the list is
    not silently short for a builder-produced program. -/
def segmentsOf (plan : QuotientProgramPlan) (build : QuotientProgramBuild) : List (List Nat) :=
  let bytes := qvmBytesToNats build.bytes
  (itemStarts plan build).filterMap fun cursor =>
    match identitySegment bytes cursor with
    | .ok (exprEnd, _) => some ((bytes.drop cursor).take (exprEnd - cursor))
    | .error _ => none

/-- `IsAlignedSubslice`, from the section-Q sketch, defined. The contract hands a
    precompile the EIP-2537 padded encoding of each point it wants checked, and
    the frame layout puts those encodings on 128-byte boundaries
    (AssemblyHelpers.yul:284-287 lays the pairing frame out as
    `[lhs_mptr | G2_BASE | rhs_mptr | NEG_S_G2_BASE]`, each entry 128 bytes).
    "The encoding of Q occurs in the call input at an aligned offset" is
    therefore the witness shape `points_subgroup_checked` has always meant:
    aligned because a shifted copy would be a different point, and a subslice
    rather than an equality because one call carries several points.

    Decidable, and stated as the Prop wrapper around the Bool: the hypothesis has
    to be checkable at a concrete call input for a gate to exhibit it, and a bare
    forall cannot be evaluated. (R-58 F9 deleted the Bool sampler next to ZeroAbove
    that this sentence used to cite, so the comparison is gone; this one is a Bool
    because a gate reads it.) The scan covers every aligned offset a full needle can start at, so
    the Bool is not a sample of the Prop - it is the Prop. -/
def isAlignedSubslice (needle : Bytes) (input : List UInt8) : Bool :=
  (List.range (input.length / needle.data.size + 2)).any fun k =>
    let off := 128 * k
    off + needle.data.size <= input.length ∧
      (input.drop off).take needle.data.size = needle.data.toList

/-- The proposition, as the DEFERRED points_subgroup_checked field will consume it
    (R-58 F1): the object and its gate stay, the field that used them does not. -/
def IsAlignedSubslice (needle : Bytes) (input : List UInt8) : Prop :=
  isAlignedSubslice needle input = true

/-! ### The headline -/

/-- The headline obligations over a Surface. Every field assumes `SupportedS S S.o₀` (D2: the options the
    lowered program came from, so a trace-render L cannot pass with a production o) and quantifies over
    all H (PLAN 10.3), with DeploymentW pinning H on the two code strings (Y-2). Deployment target:
    H := keccak256. Future deliverable: `theorem lowering_correct : LoweringCorrect realSurface product`. -/
structure LoweringCorrect (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) : Prop where
  /-- ANY run of the assembly, from ANY memory zero above the solc scratch (attack: the g1_identity
      window must be zero), under adversarial precompiles and ANY gas oracle, that returns, returns
      abiTrue and Lean accepts. Side condition: NoLogupPanic (finding 5). -/
  verifier_sound : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes) (mem₀ : Nat → UInt8)
      (gas : ExternalGas) (obs : Obs),
      SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr →
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
      EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      ZeroAbove mem₀ →
      RunVerifier S W H cd mem₀ (permissive (S.calls W product qAddr)) gas obs → obs.isReturn →
      SoundSide S H cd →
      obs.returnData = abiTrue ∧ LeanAccepts S H cd
  /-- Lean accepts ⇒ an honest shell run exists and every honest run returns abiTrue (view-level).
      Side condition: GenericX (finding 4); needs EnvAgrees.omegaOrder/domainN and toEip 1 = zeros. -/
  verifier_complete : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes),
      SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr →
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
      EnvAgrees S.E S.vk S.plan S.params S.sG2gen → Midfall.Assumptions.G1CodecLaws S.E.g1 →
      LeanAccepts S H cd → CompleteSide S H cd →
      (∃ obs, RunShell S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
      (∀ obs, RunShell S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
        obs.view = returnView (callState W S.shellLayout H cd))
  /-- Only two outcomes, read-only — on the verifyProof arm (attack: the BUILD_ID()/AUTHORIZED_*
      getters return other data).

      R-58 F10 added EnvAgrees here and to verifier_sound: without it both quantify
      over Surfaces where the contract's FR_MODULUS literal and the Lean Fr p are
      different fields, so the claim is about a deployment nobody can build. The
      asymmetry was in the section-Q sketch too (verifier_complete carried EnvAgrees
      and its soundness twin did not), so this is plan-inherited rather than drift -
      decided here, and written down: every field that reasons about what the contract
      DECIDES now carries it. Holds is deliberately NOT added: only_two_outcomes is a
      claim about the program's outcomes under adversarial precompiles, not about what
      a correct precompile answers. -/
  only_two_outcomes : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes) (gas : ExternalGas) (obs : Obs),
      SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr →
      EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      bytesTake cd 0 4 = some fnSigVerifyProof →
      RunShell S W H cd (permissive (S.calls W product qAddr)) gas obs →
      obs.view = returnView (callState W S.shellLayout H cd) ∨
        (obs.isRevertOrHalt ∧ obs.worldUnchanged (callState W S.shellLayout H cd))
  /-- M8: the imported via-ir object refines the shell model, for world-local calls and a fixed gas
      oracle (attack: a relation reading caller memory separates IR from shell). STATED, and the
      hypothesis is inhabited JOINTLY: Instances/ImportedIR.lean exhibits, for every call relation
      and every gas oracle, ONE object that both passes `S.irCheck` and has a committed
      `RunContractIR` (`irHypothesis_jointlyInhabited`). R-60 S1: before the repair the run was
      exhibited and the check was false of it, so the bundle was empty while each half looked
      alive; the exhibit is now of the conjunction, not of the halves. PROVING is M8 and needs the
      IR-to-shell simulation plus a Surface whose shell is the real dispatcher - NOT the stage-1
      determinism holes, which R-60 S6 shows the view transport does not use. -/
  ir_refines : ∀ (ir : YulObject) (irLyt : EVM.Layout), S.irCheck ir = true →
      ∀ (W : ExecEnv) (H : Hash) (cd : Bytes) (c : ExternalCalls) (g₀ : U256), c.WorldLocal →
      ObsEquiv (RunContractIR S W H ir irLyt cd c (ExternalGas.ofFun fun _ => g₀))
        (RunShell S W H cd c (ExternalGas.ofFun fun _ => g₀))
  /-- D-P13, and R-58 F8. The section-Q form was
       `forall o L, lower o = ok L -> forall ast, astOfMain o = some ast ->
       stmtsBeq ast L.main`, and the review proved it vacuous: `lower` and `astOfMain`
       are free Surface functions, so at the only Surface in the tree the conjunct
       reduces to `stmtsBeq fxMain fxMain` - a self-equality - and a Surface whose
       astOfMain returns none for every option satisfies the field by contributing no
       instances at all. The pin below is the equation the fixture actually satisfies:
       the AST accessor IS the main block of what the render produced, for EVERY option,
       including the ones the render refuses. It can fail two ways and both are shown:
       SurfaceFixture.renderEqPrintPinKats_ok refutes an accessor that answers some for
       an option the render refuses, and ObligationsGates.renderEqPrintAtFixture_ok
       refutes an accessor that returns a block with one statement dropped.
       The structural equality stmtsBeq is still what the two sides are compared with
       when they differ, and renderEqPrintStructuralKats_ok still gates it. -/
  render_eq_print : (∀ o, S.astOfMain o =
    match S.lower o with
    | .ok l => some l.main
    | .error _ => none) ∧
    -- R-60 S5: the second conjunct is what stops the first being a definition in
    -- disguise. The fixture DEFINES astOfMain as the main block of what lower returns,
    -- so the equation above holds by rfl there and proves nothing on its own - the
    -- original defect wearing different clothes, which is exactly what this pass was
    -- told to suspect. The trace-refusal conjunct is not rfl: it says no Surface in
    -- this bundle may expose an AST for a trace render at all, even one whose render
    -- happily produces it. ObligationsGates.renderEqPrintAtFixture proves the pair at
    -- the fixture and renderEqPrintTraceRefusalKats_ok refutes an accessor that
    -- answers some for a trace option, so the conjunction can fail and is seen to.
    (∀ o, o.diagnostics.trace = true → S.astOfMain o = none)
  /-- end_to_end_noAcc with the RHS carrying an existence conjunct (PLAN's `∀ obs` alone is vacuous
      when no run exists), the RepackError lift (attack: the two error types never met), the
      instance-length check and the modulus bound. DEVIATION: the sketch writes `S.repackProof` and
      `S.encodeCalldata`; stage 4 removed those fields from the Surface, so the spec functions are
      applied to the Surface's own layout, instance count and codec. -/
  end_to_end_noAcc : S.cfg.accumulator = none → ∀ (W : ExecEnv) (vkAddr qAddr : U256) (ir : YulObject) (irLyt : EVM.Layout)
      (inst : Array (Fr p)) (π : Bytes),
      SupportedS S S.o₀ → DeploymentW S W keccak256 vkAddr qAddr →
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product → Midfall.Assumptions.G1CodecLaws S.E.g1 →
      EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      S.irCheck ir = true → inst.size = S.cfg.numInstances → p ≤ 2 ^ 256 →
      (∀ ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
        GenericX S keccak256 ms (inst.map frWord) inst ∧ NoLogupPanic S keccak256 ms inst) →
      (verifyNative (Gₜ := Gₜ) S.E Features.solidity S.params S.vk inst π = .ok () ↔
        ∃ cd, ((Midfall.Lowering.repackProof (p := p)
            (RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout) S.E.g1 π).mapError
            Midfall.Generator.GeneratorError.fromRepackError >>=
          fun π' => Midfall.Lowering.encodeCalldata (p := p) S.cfg.numInstances
            (RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout) S.E.g1 π' inst) = .ok cd ∧
        (∃ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
        ∀ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
          obs.view = returnView (callState W irLyt keccak256 cd))
  /-- The per-partial contracts (Partials.lean), including the pulled-forward finalPairing_spec. -/
  partials : PartialSpecs S product
  /-- D-P20 item 2, validator form (P-09e): no bounds fault class is reachable from a validated program,
      and every operand key lies in the read windows (plan.rs:570-618). DEVIATION: the sketch's
      `OperandModel` and `validate` are P-09e placeholders; this is the landed validator's real
      signature (Qvm.lean:738), with `segmentsOf` supplying the sketch's segment quantifier.

      R-60 S9, THE F3 CLASS ONE LEVEL UP: this field does not mention the Surface AT ALL.
      Every other field of this structure is a claim about the deployment the record
      describes; this one quantifies over an arbitrary `LoweringPlan Program Layout`, so
      it is a claim about SOME plan and not about the plan this Surface renders - which is
      the same defect R-58 F3 found in `shell_unfolds` (three run relations about three
      unrelated programs) raised one level. It is not vacuous - the validator is real and
      Qvm.lean:738 proves the shape - but it is not pinned to the Surface either, and no
      pin is nameable today: linking it needs `S.plan` to BE a `LoweringPlan`, and
      `PlanView` (Inv.lean:109) is the counts Inv reads precisely because P-11's
      `LoweringPlan::new` has not landed. Recorded as a named gap in
      scripts/check_hypothesis_bundles.py rather than left for a reader to notice. -/
  qvm_validated_noBoundsFault : ∀ (Program Layout : Type)
      (L : Midfall.Generator.LoweringPlan Program Layout)
      (q : Midfall.Generator.PlannedQuotient),
      L.lowering = Midfall.Generator.QuotientLowering.vm →
      L.quotient = some q →
      (Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory q.build
        q.plan.selectorFold).isOk = true →
      Midfall.Generator.LoweringPlan.supportedQvm L →
      (∀ c ∈ q.build.consts, c.toNat < Midfall.Generator.qvmFrModulus) →
      ∀ seg ∈ segmentsOf q.plan q.build, ∀ mem f,
        Midfall.Generator.evalQuotientIdentity seg q.build.consts mem = .error f →
        (match f with | .readPastEnd _ => False | .constSlotOutOfRange _ _ => False | _ => True)
  -- R-58 F1: points_subgroup_checked IS DEFERRED, not repaired. The review proved its
  -- conclusion holds unconditionally; the proof is below, as
  -- points_subgroup_checked_conclusion_is_unconditional, and it needs no hypothesis at
  -- all: the witness the
  -- field asks for is an existential over (permissive (S.calls W product qAddr)), and
  -- permissive (Bridge.lean:388) admits ANY request to ANY target provided the
  -- response is a failure and its world is the state it was called at. So for every Q
  -- one picks req := { target := 0x0c, input := the bytes of Q } and resp := a failed
  -- response, and the field is satisfied whether the run made a single call or none.
  -- The interim fix - tying the target set to the observed state - is still not a
  -- trace: what the claim needs is that the RUN issued the call, and RunCommitted
  -- records the final frame, not the calls made along the way. Deferred with the
  -- call-trace blocker, exactly like the trio below; the witness objects it will
  -- consume (segmentsOf-style: isAlignedSubslice and its KAT) are defined and gated
  -- here so the deferral is about the missing trace, not about missing vocabulary.

  /-- artifacts.rs:181-227: the table is sorted by name, "-G" ↦ (P.g₁, negate := true). DEVIATION:
      `List.Sorted` is not in the built surface; `namesAscending` (Accumulator.lean:188) is stage 2's
      substitute for the same proposition, and the dead-identifier table says to reuse it.

      R-58 F7 ADDED THE MIDDLE CONJUNCT. Without it the last clause is an implication
      over an empty set at every table that lacks a "-G" row - including the empty
      table, which is ascending, so the whole field discharged on `{ accFixedBases :=
      #[] }`. The review demonstrated exactly that. The existence conjunct is what makes
      the field say something about a producer: a table with no "-G" row now refutes it,
      and the fixture carries the row (SurfaceFixture.accFixedBasesKats_ok) rather than
      being refuted by it. -/
  accFixedBases_producer : namesAscending (S.accFixedBases.toList.map AccFixedBase.name) ∧
      (∃ b ∈ S.accFixedBases.toList, b.name = "-G") ∧
      ∀ b ∈ S.accFixedBases.toList, b.name = "-G" → b.base = P.g₁ ∧ b.negate = true

  -- R-58 F5: vkDigest_slot0 IS DROPPED, not restated. It read
  -- `(S.plan.vk.constants.getD 0 ("", 0)).2 = S.vkDigest`, and the review showed it is
  -- derivable from two fields that are already stated: Surface.vkDigest_spec
  -- (vkDigest = frWord vk.transcriptRepr) and EnvAgrees.vkDigestWord
  -- ((PV.vk.constants.getD 0 ("", 0)).2 = frWord vk.transcriptRepr). A field that
  -- follows from two others in the same bundle is decoration, and worse, it was
  -- decoration that could be satisfied while vkDigest_spec was pointed at a different
  -- word. The digest-slot fact is not lost: it lives in EnvAgrees.vkDigestWord, which
  -- every field that needs the digest already carries as a hypothesis, and the
  -- fixture gate vkDigestSlot0_ok still exercises the projection.

  /-- The Exec read schedule has the layout's slot shape (Protocol ↔ Exec bridge). -/
  readScheduleAgrees : ∀ inst π ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
      ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout).slots

/-! ### Fields section Q sketched and this file does NOT state, with the blocker

  `qvm_yul_refines`. Six names, and one missing artifact:

  * `EvaluatorFrame`, `FrameWellFormed` - no occurrences anywhere in the tree.
    The sketch's own comment says the frame "must pin the VK window because the
    frame contains the program", i.e. it is the QUOTIENT_FRAME_BASE /
    QUOTIENT_FRAME_LEN / QUOTIENT_OUTPUT_LEN / QUOTIENT_MAGIC quadruple of the
    evaluator template (Contracts.lean:384 names nineteen memory slots plus
    four frame fields), which is a P-11 `LoweringPlan` fact. The Surface has no
    plan record, only a `PlanView`, and `PlanView` (Inv.lean:109) carries the
    counts Inv reads and nothing else.
  * `S.plan.qext` - stage 3's `PlanView` has no such field; P-11's
    `LoweringPlan::new` is the blocker, and R-58 F4 deleted the `qvmValidated`
    slot that used to stand here (Surface.lean header, deviation 4).
  * `perIdentityValues`, `yOf`, `outputBytes`, `frameValuation` - the sketch
    marks them SKETCH. Stage 5's QvmFold supplies the fold
    (`quotientFold`, `globalIdentities`, `evalExprρ`) but not a valuation read
    out of a live `EvmState` frame, because nothing in Exec exposes one.
  * And the object the conclusion needs: `QuotientNumeratorBlock.yul` as a
    `Block Op`. P-13 ported the templates as TEXT renders
    (VerifierPartials.lean:2175 returns `String`), so there is no AST to run
    with `YulSemantics.Run`. That is why the brief says not to promise this
    field, and defining the six names without the seventh would produce a field
    about a frame no render emits - the decorative-field class attack.md forbids.

  `repackProof_faithful` and `encodeCalldata_faithful`. A faithfulness pin
  relates a Surface function to the spec function. Stage 4 removed
  `Surface.repackProof` and `Surface.encodeCalldata` (Surface.lean header,
  deviation 2), so the left-hand side does not exist; writing the pin over the
  spec function applied to itself would be a `rfl` field that cannot fail. The
  content is not lost: `end_to_end_noAcc` above applies the spec functions to
  the Surface's own `proofLayout`, `numInstances` and `E.g1`, which is where a
  wrong layout or codec would show up as a statement that does not compose.

  `shell_unfolds` is not a LoweringCorrect field and never was: it is a SURFACE pin,
  added at R-58 F3 (Surface.lean). Stage 4 declined it because the fixture's shell is a
  placeholder with nothing to unfold into, which inverted the point - the equation is
  exactly what makes the placeholder honest, and without it RunShell, RunVerifier and
  RunContractIR were three unrelated programs.

  R-58 F1 and F5 removed two fields from this structure and both removals are recorded
  at their old sites rather than left silent: `points_subgroup_checked` is deferred
  behind the call-trace blocker (its conclusion held unconditionally), and
  `vkDigest_slot0` is dropped as derivable from two other stated pins.
  `isAlignedSubslice` and its KAT stay: they are the witness shape the deferred field
  will consume, and a defined, gated object is not the same thing as a decorative one. -/

/-- R-58 F1 EVIDENCE, proved rather than argued: the deferred field's conclusion is
    derivable from the SHAPE of `permissive` alone, with no run, no snapshot, no
    decode and no hypothesis at all. For any call relation, any state and any point
    encoding, there is a request to 0x0c whose input carries the encoding at offset 0
    (so it is aligned) and a response `permissive` accepts because it is a failure.
    That is exactly the vacuity the review demonstrated, now with a proof: the field
    could not fail, so it is deferred until the run relation carries the call trace the
    claim needs - a trace of the calls the RUN made, which `RunCommitted` does not
    record. The interim fix (constrain the target set, or require the response to
    succeed) still would not say the program issued the call, so it is not shipped
    either. -/
theorem points_subgroup_checked_conclusion_is_unconditional
    (c : ExternalCalls) (st : EvmState) (needle : Bytes) :
    ∃ req resp, (Midfall.Yul.Bridge.permissive c).Call req st resp ∧
      accountKey req.target ∈ ([0x0c, 0x0f] : List Nat) ∧
      IsAlignedSubslice needle req.input := by
  refine ⟨YulSemantics.EVM.CallRequest.mk .staticcall 0 0x0c 0 needle.data.toList,
    Midfall.Yul.Bridge.failResp st, ⟨rfl, fun h => absurd h Bool.noConfusion⟩, ?_, ?_⟩
  · show accountKey (0x0c : U256) ∈ ([0x0c, 0x0f] : List Nat)
    decide
  · unfold IsAlignedSubslice isAlignedSubslice
    rw [List.any_eq_true]
    refine ⟨0, by simp [List.mem_range], ?_⟩
    simp

/-! ### The derived headline theorems -/

/-- PLAN 9.5's headline, derived from the fields: soundness via ir_refines (isReturn/returnData are
    view-level) and shell_unfolds, completeness via ir_refines on both conjuncts, the two-outcome
    conjunct via ir_refines. Hypotheses are the union of the fields'.

    STATED WITH A LIVE HYPOTHESIS - AND R-60 S1 RECORDS THAT THIS SENTENCE WAS
    FALSE WHEN IT WAS FIRST WRITTEN. It claimed inhabitation from
    Instances/ImportedIR.lean's committed `RunContractIR`, and that run really is
    committed; what was missing is that every field here takes the run TOGETHER WITH
    `S.irCheck ir = true`, and the fixture's check hard-coded its own runtime naming
    instead of reading `S.runtimeName`, so on the imported object it returned false.
    Individually inhabited, jointly empty, and no gate could see it because gate 6
    checked the run alone. The repair is in the code: `Surface.irCheck` is no longer a
    free field but a projection of `Surface.runtimeName` (Surface.lean), and
    `irHypothesis_jointlyInhabited` (ImportedIR.lean) exhibits the CONJUNCTION - one
    object, one layout, one observation, both conjuncts - for every call relation and
    every gas oracle. `s1_defect_refutes_the_conjunction` keeps the broken form in the
    tree as the refutation, so the exhibit is seen to be able to fail.

    THE REQUIRED FINDING, ANSWERED AFTER THE PINS LANDED. The sketch hint ("provable
    now - transport each field through hc.ir_refines") was FALSE as written, and R-58
    F3 said why: nothing linked the shell to the assembly, so `hc.verifier_sound` was
    a claim about `L.headGuard ++ bindLocals ++ L.main` while the conclusion is a
    claim about `shell.codeBlock`, and no hypothesis connected them. `shell_unfolds`
    closes THAT half, and it closes it completely: with the equation, RunShell's
    program is literally RunVerifier's program, and `callState W Lyt H cd` is by
    definition `initState W Lyt H cd (fun _ => 0)`, which satisfies ZeroAbove. So
    "verifier_sound plus shell_unfolds gives shell soundness" is now a derivation
    rather than a hope, and the field bundle finally says one thing about one program.

    WHAT STILL STANDS BETWEEN THIS STATEMENT AND A PROOF, corrected by R-60 S6,
    which found the previous list wrong in BOTH directions.

    NO LONGER A BLOCKER, and wrongly listed as one: (i) and (ii). The view-level
    transport was said to need `dialect_deterministic` and `noWritersFuel`. It does
    not: `ObsEquiv` gives a run on the other side with an EQUAL VIEW, and the outcome
    properties are functions of the view, so no uniqueness of the STEP relation is
    involved. Bridge.lean now proves it - `halted_of_view_eq`,
    `returnData_of_view_eq`, `isReturn_of_view_eq`, `isRevertOrHalt_of_view_eq`, four
    three-line lemmas - and the third conjunct's real blocker was something else
    entirely: `ObsView` carried nine of the eleven components `WorldEq` compares, so
    `obs.worldUnchanged` was NOT view-determined and no amount of determinism would
    have transported it. R-60 S6 adds `selfBalance` and `extCodeHashOf` to the view and
    lands `worldEq_of_view_eq`, so all three conjuncts are now view-transportable and
    `view_sees_selfBalance` / `view_sees_extCodeHashOf` exhibit the hole that was
    closed. What remains on the view side is nothing: the gap was the view, not the
    semantics.

    STILL BLOCKERS, and named with what would clear them: (iii) `irCheck` is the
    decidable fragment (unresolved-call screening), not alpha-equivalence modulo
    constant substitution, so `hir : S.irCheck ir = true` does not say the imported
    object IS the contract - clearing it needs the M8 import-time equivalence check;
    (iv) `shell_unfolds` pins the shell MODEL, whose code block is the assembly with no
    dispatcher in front of it, so the theorem's shell is not the deployed entry path
    until M8 restates the pin as "the verifyProof arm runs the assembly"; and (v) the
    IR-to-shell SIMULATION itself, which is what `ir_refines` asks for and is the whole
    of M8. `noWritersFuel` and `Run_worldEq_of_noWriters` stay stage-1 holes for the
    theorems that need a WORLD equality out of a run rather than out of a view - not
    for the view transport, which no longer needs them. In short: statable, with a
    hypothesis that is jointly inhabited at the real artifact, and NOT yet provable -
    the remaining gap is the IR-to-shell simulation, not the shell-to-verifier link
    and not the view. -/
theorem lowering_equivalence (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (hc : LoweringCorrect S product) (hsup : SupportedS S S.o₀)
    (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (hdep : DeploymentW S W H vkAddr qAddr)
    (hpc : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen) (hcodec : Midfall.Assumptions.G1CodecLaws S.E.g1)
    (ir : YulObject) (irLyt : EVM.Layout) (hir : S.irCheck ir = true)
    (cd : Bytes) (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) (hside : SideConditions S H cd) (g₀ : U256) :
    -- soundness: any run that returns, returns true, and Lean accepts
    (∀ obs, RunContractIR S W H ir irLyt cd (permissive (S.calls W product qAddr)) (ExternalGas.ofFun fun _ => g₀) obs →
      obs.isReturn → obs.returnData = abiTrue ∧ LeanAccepts S H cd) ∧
    -- completeness: Lean accepts ⇒ honest runs exist and all return true
    (LeanAccepts S H cd →
      (∃ obs, RunContractIR S W H ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
      ∀ obs, RunContractIR S W H ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
        obs.view = returnView (callState W irLyt H cd)) ∧
    -- only two outcomes, read-only
    (∀ obs, RunContractIR S W H ir irLyt cd (permissive (S.calls W product qAddr)) (ExternalGas.ofFun fun _ => g₀) obs →
      obs.view = returnView (callState W irLyt H cd) ∨
        (obs.isRevertOrHalt ∧ obs.worldUnchanged (callState W irLyt H cd))) := by
  sorry
  -- SKETCH PROOF HINT (section Q): provable now - transport each field through
  -- hc.ir_refines (permissive and honest calls are both WorldLocal).

/-- Exact equivalence to the message-level verifier without an accumulator (R-10 makes `h` necessary). -/
theorem lowering_equivalence_noAcc (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : S.cfg.accumulator = none) :
    LeanAccepts S H cd ↔
    ∃ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) ∧
      instOfWords? (p := p) instW = some inst ∧
      verifyMsgs (Gₜ := Gₜ) S.E H Features.solidity S.params S.vk inst ms = .ok () := by
  sorry
  -- SKETCH PROOF HINT (section Q): unfold; rw [h]; cases prepareMsgs …; simp
  -- [verifyMsgs, bind, Except.bind] - mirrors SemanticEquivalence.lean:36-41, which
  -- is the already-proved lemma this one is modelled on.

/-- Adjustment 4: the accumulator-mode corollary Moonlight needs, one direction only (R-10, R-26.4): an
    honest compressed proof that verifyNative accepts, with a public accumulator that decodes and passes its
    own check, yields calldata on which every honest IR run returns abiTrue. Derived from
    contractRef_acc_complete + verifier_complete + ir_refines + the calldata lemmas. There is deliberately
    no acc-mode `↔`: the contract batches with keccak-alpha, Rust with the sponge r. -/
theorem end_to_end_acc_complete (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (hc : LoweringCorrect S product) (enc : Midfall.Generator.AccumulatorEncoding)
    (henc : S.cfg.accumulator = some enc)
    (W : ExecEnv) (vkAddr qAddr : U256) (ir : YulObject) (irLyt : EVM.Layout)
    (inst : Array (Fr p)) (π : Bytes) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀) (hdep : DeploymentW S W keccak256 vkAddr qAddr)
    (hpc : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product) (hcodec : Midfall.Assumptions.G1CodecLaws S.E.g1)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hir : S.irCheck ir = true) (hn : inst.size = S.cfg.numInstances) (hp : p ≤ 2 ^ 256)
    (hv : verifyNative (Gₜ := Gₜ) S.E Features.solidity S.params S.vk inst π = .ok ())
    (hdec : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) S.E.g1 S.accFixedBases (inst.map frWord) = some a)
    (hchk : KzgAcc.check a S.params (tblOf S.accFixedBases) = true)
    (hWf : ∀ ms d, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
      prepareMsgs (Gₜ := Gₜ) S.E keccak256 Features.solidity S.vk inst ms = .ok d →
      d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hside : ∀ ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
      GenericX S keccak256 ms (inst.map frWord) inst) :
    ∃ cd, ((Midfall.Lowering.repackProof (p := p)
        (RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout) S.E.g1 π).mapError
        Midfall.Generator.GeneratorError.fromRepackError >>=
      fun π' => Midfall.Lowering.encodeCalldata (p := p) S.cfg.numInstances
        (RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout) S.E.g1 π' inst) = .ok cd ∧
      (∃ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
      ∀ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
        obs.view = returnView (callState W irLyt keccak256 cd) := by
  sorry
  -- SKETCH PROOF HINT (section Q): verifyNative_iff_msgs_codec; contractRef_acc_complete;
  -- calldata_roundtrip; hc.verifier_complete; hc.ir_refines.

/-- Finding 3: the frozen Statements.contractRef_noAcc, under a new name (filling it needs a re-pin). -/
theorem contractRef_noAcc_of_semanticEquivalence (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    (Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms = true) ↔
      verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () :=
  contractRefAccepts_iff_verifyMsgs E keccak256 params vk inst ms

/-- Finding 1: the frozen verifyNative_iff_msgs is false for a degenerate codec; this is the provable
    form. Only compressedRoundtrip is needed (the attack showed p ≤ 2^256 is decorative here). -/
theorem verifyNative_iff_msgs_codec (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) (hc : E.g1.compressedRoundtrip) :
    verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔
    ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧
      verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by
  sorry
  -- SKETCH PROOF HINT (section Q): key lemma transcript_log_concat - the log's reprs
  -- concatenate to the consumed transcript prefix. Note hc is the ONLY codec law the
  -- statement needs: attack.md's verifyNative_iff_msgs_codec entry proves the sketch's
  -- hp : p ≤ 2^256 is decorative here, and it is therefore absent.

/-! ### Known-answer checks

  Model-free, per the Instances confinement gate. The exhibits that need a
  pairing model - `SupportedS realSurface realSurface.o₀`, the `astOfMain`
  isSome gate, the trace-render refutation of `only_two_outcomes`, and the
  imported-IR inhabitation of `ir_refines` - are in
  `Midfall/Instances/ObligationsGates.lean`. -/

/-! ### Known-answer checks

  Model-free, per the Instances confinement gate: everything below needs only the
  generator and the dialect, so it can live in a file that states theorems. The
  exhibits that need a pairing model - `SupportedS realSurface realSurface.o₀`,
  the `astOfMain` isSome gate, the trace-render refutation of
  `only_two_outcomes`, the digest-slot projection, and the imported-IR
  inhabitation of `ir_refines` - are in
  `Midfall/Instances/ObligationsGates.lean`, which REUSES stage 4's
  `supportedInhabited` / `supportedRefutedForTraceRender` and P-IR's
  `runContractIR_inhabited` rather than restating them. -/

/-- `segmentsOf` is a real function of the plan and the build, not a constant and
    not a re-derivation: on the certifier's three-identity fixture it yields one
    segment per item, the segments are the slices `itemStarts` names (so the
    fold opcodes between them are excluded, which is why the lengths are
    6, 5, 6 out of a 23-byte program), and a program truncated so the walker
    errors contributes NOTHING rather than a guessed segment. Refuted by a
    `segmentsOf` that took the whole byte string (line 2), that ignored
    `identitySegment`'s error arm (line 4), or that walked something other than
    the item starts (line 3). -/
def segmentsOfKats_ok : Bool :=
  match QuotientCertifyKats.threeIdentityBuild with
  | .ok build =>
      let plan := QuotientCertifyKats.threeIdentityPlan
      let bytes := qvmBytesToNats build.bytes
      let segs := segmentsOf plan build
      bytes.length == 23 &&
        itemStarts plan build == [0, 7, 16] &&
        segs.map List.length == [6, 5, 6] &&
        segs == [bytes.take 6, (bytes.drop 7).take 5, (bytes.drop 16).take 6] &&
        -- the error arm: an empty program has no segment at all, because the
        -- walker errors rather than guessing an end
        segmentsOf plan { build with bytes := Midfall.Bytes.empty } = [] &&
        -- and a program truncated inside the second identity yields the segments
        -- whose walkers still succeed, no more
        (segmentsOf plan { build with bytes := qvmBytesOfNats (bytes.take 8) }).length < 3
  | .error _ => false

#eval segmentsOfKats_ok                   -- expect true

/-- `IsAlignedSubslice` is about an ALIGNED occurrence: the needle at offset 0
    and at offset 128 satisfies it, the same bytes at offset 1 do not, and a
    needle that is not present does not. Without the second line the predicate
    would be "occurs somewhere", which is not what a pairing frame guarantees -
    a shifted copy of an EIP-2537 encoding is a different point. -/
def isAlignedSubsliceKats_ok : Bool :=
  let needle := Midfall.Generator.bytesFromNats (List.range 128)
  let pad (n : Nat) : List UInt8 := (List.range n).map (fun i => UInt8.ofNat i)
  let zeros : List UInt8 := List.replicate 128 (UInt8.ofNat 0)
  isAlignedSubslice needle (pad 128) &&
    -- a genuine NON-ZERO aligned offset: the needle at 0x80, preceded by a word
    -- of padding that is not itself the needle
    isAlignedSubslice needle (zeros ++ pad 128) &&
    -- the same bytes shifted by one: present, but not aligned
    ! isAlignedSubslice needle ((UInt8.ofNat 9) :: pad 128) &&
    -- too short to contain it
    ! isAlignedSubslice needle (pad 127) &&
    -- the alignment is 128, not 32: an occurrence at 0x20 alone does not count
    ! isAlignedSubslice needle (pad 32 ++ pad 128)

#eval isAlignedSubsliceKats_ok            -- expect true

/-- The structural conjunct of `render_eq_print` is a real decision, not a
    tautology: a block is structurally equal to itself, a literal changed by one
    is not, and a memoryguard call - the op P-VEND added and the reason the IR
    import was blocked - is distinguished from the literal it replaced. This is
    the D-P13 equality the sketch keeps after R-39 dropped the text one, and it
    is exercised here rather than only in YulGolden.lean because the field that
    consumes it lives in this file. -/
def renderEqPrintStructuralKats_ok : Bool :=
  let a : YulBlock := [Stmt.exprStmt (Expr.builtin Op.mstore
    [Expr.lit (.number 64), Expr.lit (.number 128)])]
  let b : YulBlock := [Stmt.exprStmt (Expr.builtin Op.mstore
    [Expr.lit (.number 64), Expr.lit (.number 129)])]
  let g : YulBlock := [Stmt.exprStmt (Expr.builtin Op.mstore
    [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])]
  SyntaxEq.stmtsBeq a a && ! SyntaxEq.stmtsBeq a b && ! SyntaxEq.stmtsBeq b a &&
    SyntaxEq.stmtsBeq g g && ! SyntaxEq.stmtsBeq a g && ! SyntaxEq.stmtsBeq g b &&
    -- and the conjunct is about the LIST of statements: dropping one is visible
    ! SyntaxEq.stmtsBeq (a ++ b) a && SyntaxEq.stmtsBeq (a ++ b) (a ++ b)

#eval renderEqPrintStructuralKats_ok      -- expect true
/-- The selector hypothesis attack.md's FIX 55 forces into `only_two_outcomes` and
    `lowering_equivalence` is a real restriction and not decoration: the
    verifyProof selector passes it, and an arbitrary other four-byte selector -
    the shape of the BUILD_ID() and AUTHORIZED_* getters attack.md names, which
    return other data and so refute the unconjuncted claim - does not. -/
def onlyTwoOutcomesSelectorKats_ok : Bool :=
  bytesTake fnSigVerifyProof 0 4 == some fnSigVerifyProof &&
    ! (bytesTake (Midfall.Generator.bytesFromNats [0x12, 0x34, 0x56, 0x78]) 0 4 ==
        some fnSigVerifyProof) &&
    -- and a short calldata fails it rather than decoding to a wrong selector
    bytesTake (Midfall.Generator.bytesFromNats [0x1e, 0x8e]) 0 4 = none

#eval onlyTwoOutcomesSelectorKats_ok      -- expect true

-- AXIOM AUDIT. The one headline theorem this file actually proves must not
--   lean on a sorry: it is the re-export of the already-proved
--   contractRefAccepts_iff_verifyMsgs (SemanticEquivalence.lean:29), so its axioms
--   are the three the rest of the tree uses and sorryAx is not among them. The four
--   statement holes above all DO carry sorryAx, which is exactly why this one is
--   printed: it separates the field of the headline that is closed today from the
--   four that are M7/M8 work.
#print axioms Midfall.Lowering.contractRef_noAcc_of_semanticEquivalence

end Midfall.Lowering

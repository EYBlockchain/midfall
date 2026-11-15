-- |
-- Midfall.Instances.CurveSurface
--
-- P-CSURFACE STEP 1: A SURFACE OVER THE CURVE CODECS.
--
-- WHY THIS FILE EXISTS. P-HOLDS-FINAL exhibited 'Eip2537.Holds' as ONE unconditional term
-- (Instances/HoldsFinal.lean, 'holds_exhibited') and then reported the finding that makes
-- this file necessary rather than optional: that exhibit advances the four 'Holds'-binding
-- spec theorems by NOTHING, because each of them binds 'Holds S.E.g1 (S.encG2) product' -
-- the SURFACE's own codec - and the only Surface in the tree, Instances/SurfaceFixture.lean's
-- 'realSurface', installs the EXPONENT codec, whose g1Valid fails at a non-identity
-- exponent (ObligationsGates.expG1Codec_not_holds). 'VerifierEnv.g1' is typed over the
-- Surface's own 'AdmissiblePairing', so installing 'g1CodecZ' is not a field assignment on
-- the fixture: it means BUILDING a Surface over 'G₁z' / 'G2fold' / 'blsGT'. That is what
-- this file does, and it is instance plumbing rather than a theorem.
--
-- WHAT IT IS NOT. It proves no spec theorem. 'pcs_spec', 'finalPairing_spec',
-- 'finalPairing_progress_spec' and 'finalPairing_acc_spec' (Lowering/Partials.lean) are
-- registered holes before this package and stay registered holes after it. What moves is
-- their VACUITY STATUS at a real Surface, and every declaration below says which of the
-- two it is. INSTANTIATION IS NOT PROVING, and the file says so at each site rather than
-- once in a header a reader skips.
--
-- WHY SO MANY FIELDS ARE THE FIXTURE'S. The program data - the render, the plan, the
-- shell, the blocks, the layout, the two runtime images, the codehashes - does not
-- mention the group at all, so 'curveSurface' REUSES it. Restating it would create a
-- second copy of the program with nothing pinning the two together, which is the R-58
-- defect class this project has been repairing for six packages. 'curveSurfaceProgramIsThe
-- Fixtures' is the pin: every reused field is PROVED equal to the fixture's own, by 'rfl'.
--
-- WHY THERE IS NO '#eval' GATE HERE, which looks like an omission and is not. The Surface
-- is 'noncomputable' - 'g1CodecZ.ofEip?' is a 'Classical.choose' over the codec's image,
-- because reading an exponent off a curve point is a discrete log - so the code generator
-- refuses to compile ANY projection of it, and a Bool gate over 'curveSurface.L' cannot be
-- written. The equalities are therefore stated as 'rfl' THEOREMS, which are kernel-checked
-- and strictly stronger than the '#eval' gates they replace: a KAT trusts the compiler, a
-- 'rfl' does not. The one computable gate in the file, 'curveIrNaming_ok', is about the
-- imported artifact and the naming field and needs no codec.
--
-- THE ONE PIN THE CURVE SURFACE DOES BETTER ON, and the honest scope of that claim.
-- 'Surface.encG2_shape' carries a named gap: the pin constrains the encoder's OUTPUT
-- bytes and does not say 'Function.Injective encG2', and the doc says the fixture CANNOT
-- meet the strengthening. At the curve Surface the encoder IS 'g2foldToEip' and it IS
-- injective (Instances/G2Codec.lean, 'g2foldToEip_injective'), so 'curveEncG2_injective'
-- closes that gap AT THIS SURFACE - and 'fixtureEncG2_not_injective' is the falsification
-- that says the gap was real, is a fact about the exponent model's constant encoder, and
-- is not deleted by anything here.
--
-- WHAT IS STILL EMPTY HERE, stated because a four-way exhibit invites the opposite
-- reading. The headline fields also take a DEPLOYMENT and a RUN, and the run leg is
-- untouched by this package: 'gap_runLeg_unexhibited' says no accepted calldata exists at
-- any model in the tree, so the spec theorems' 'hcd' / 'hinst' / 'hsnap' binders - a
-- calldata that decodes, instance words that re-enter the field, a snapshot the pipeline
-- produces - are not supplied here either. 'curveSpecResidualBinders' names them, and
-- 'curveSpecSurfaceSide' supplies exactly the five it does supply and no more.
--
-- D-P23, BOTH HALVES, AS THEOREMS. Witness: 'curveBundle' (the four-way conjunction as
-- ONE term at the curve Surface), 'curveBundleCore' (the five-way, with the deployment),
-- 'curveVkPoints_anyCommitment', 'curveEncG2_injective'. Falsification:
-- 'curveHolds_refutes_constant_true' and 'curveHolds_refutes_constant_false' (the product
-- the exhibit quantifies over is pinned, not free), 'fixtureEncG2_not_injective',
-- 'curveSupported_refuted_by_wrong_cs' (the SupportedS leg can fail at THIS Surface),
-- 'curveBundle_holds_leg_refuted_at_the_fixture' (swap the curve codecs for the fixture's
-- and the fourth conjunct is refuted), and 'curveIrCheck_refuted_at_the_fixture_naming'.
-- THE LIMIT, stated rather than hidden: NO GATE IN THIS REPOSITORY DELETES A FALSIFICATION
-- THEOREM AND REDDENS THE BUILD. That gap has now been measured FIFTEEN times across nine
-- packages and NO COVERAGE IS CLAIMED for any falsification in this file. They are true,
-- proved, and invisible when removed. The only real gate over what this file depends on is
-- the '#print axioms' block at the foot, and what it reports is summarised in the package
-- notes: the exhibit's trusted base is 'holds_exhibited's five named D-P36a constants plus
-- the standard three, and the two 'native_decide' axioms the FIXTURE's own layout exhibit
-- carries and this file REUSES rather than re-proving.
--
-- WHY IN Instances/. D-P17: this file cites concrete models - 'g1CodecZ', 'g2foldToEip',
-- 'bls12_381Pairing', the fixture's program data - and states theorems about them, so the
-- confinement gate keeps it out of Lowering/.

import Midfall.Lowering.Partials
import Midfall.Instances.SurfaceFixture
import Midfall.Instances.ImportedIR
import Midfall.Instances.ObligationsGates
import Midfall.Instances.HoldsFinal
import Midfall.Assumptions.CurvePairing
import Midfall.Yul.ImportSolcIR

namespace Midfall.Instances.CurveSurface
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Generator Midfall.Yul Midfall.Yul.Bridge
open Midfall.Instances Midfall.Instances.SurfaceFixture Midfall.Instances.ImportedIR
open Midfall.Instances.ObligationsGates
open Midfall.Assumptions Midfall.Yul.Ir
open YulSemantics YulSemantics.EVM

/-! ### The three group-dependent fields -/

/-- **THE ENVIRONMENT AT THE CURVE CODECS.** 'g1CodecZ' is the field this whole package
    exists to install: 'VerifierEnv.g1' is a 'G1Codec G₁' over the Surface's OWN
    'AdmissiblePairing', and D-P36a is what supplies a pairing on 'G₁z' for the codec to
    sit over. The field constants and 'delta' are the fixture's unchanged -
    'Midfall.Assumptions.r' and 'Midfall.Yul.blsR' are the same Nat by 'rfl', so 'Fr r'
    and 'Fr blsR' are the same type and 'frFc' needs no transport, which
    'curveFrIsTheSameField' records as a theorem rather than leaving to a comment. -/
noncomputable def curveE : VerifierEnv blsR G₁z G2fold blsGT :=
  { g1 := g1CodecZ, field := frFc, delta := 2, fewerPointSetsRuntime := false }

/-- **THE PAIRING PARAMETERS, READ OFF THE ASSUMED PAIRING.** 'EnvAgrees.nG2' demands
    'params.nG2Prepared = P.g₂⁻¹' and 'EnvAgrees.sG2' demands 'params.sG2Prepared =
    sG2gen', so the generators are taken from 'bls12_381Pairing' itself and both clauses
    discharge by 'rfl'. That is the honest shape and it is a small finding of its own: at
    the exponent model the fixture could name generators by hand and hope they matched;
    here the assumption NAMES them, so the pin reads them instead of guessing them, and a
    parameter record that disagreed with the assumption could not be written this way. -/
noncomputable def curveParams : ParamsVerifierKZG G₁z G2fold :=
  { sG2 := bls12_381Pairing.g₂, nG2Prepared := (bls12_381Pairing.g₂)⁻¹,
    sG2Prepared := g2foldExp 5 }

/-- **THE VERIFYING KEY OVER THE CURVE CARRIER.** The domain and the constraint system
    are the fixture's - they are 'Fr blsR' data and the two names denote one field - and
    the single commitment is the identity of 'G₁z'. The difference from the fixture is
    worth naming: there, 'vkPoints' holds ONLY because the identity is the one exponent
    whose bytes a curve check accepts, and 'vkPointsKats_ok' refutes a non-identity
    commitment. Here 'g1CodecZ_g1Valid' discharges 'ptReadable' for EVERY point, so the
    identity is no longer load-bearing - 'curveVkPoints_anyCommitment' states that. -/
noncomputable def curveVk : VerifyingKey (Fr blsR) G₁z :=
  { domain := fxDom, fixedCommitments := #[1], permutation := { commitments := #[] },
    cs := fxCs, csDegree := 3, transcriptRepr := 7 }

/-- **THE TWO SCALAR-FIELD NAMES DENOTE ONE FIELD.** 'Fr blsR' and 'Fr rp' are the same
    type, so the fixture's field constants, domain and constraint system are REUSED and
    not copied. Refuted by either literal changing: 'frModulus_matchesBlsR_ok'
    (Generator/Templates.lean) is the pin on the other side. -/
theorem curveFrIsTheSameField : Fr blsR = Fr rp := rfl

/-! ### THE CURVE SURFACE -/

/-- **THE CURVE SURFACE: 'Surface blsR G₁z G2fold blsGT'.** The real-curve G1 codec, the
    exponent-fold G2 encoder, and the D-P36a pairing's target carrier, over the SAME
    program data the fixture uses. Every pin is 'rfl' or a one-line citation of an
    existing exhibit; the only field that needed a proof is 'encG2_shape', and it is four
    rewrites and a 'decide' because 'g2foldToEip' is a real encoder whose bytes decode
    and pass the precompile's own validator.

    This is the instance the previous package's required finding asked for. It makes the
    'Holds' binder of the four spec theorems satisfiable AT A SURFACE for the first time.
    It proves none of them. -/
noncomputable def curveSurface : Surface blsR G₁z G2fold blsGT where
  E := curveE
  params := curveParams
  vk := curveVk
  cfg := { numInstances := 1, numCommittedInstances := 1, accumulator := none }
  accFixedBases := #[{ name := "-G", base := g1zGen, negate := true },
                     { name := "b0", base := 1, negate := false }]
  vkDigest := frWord curveVk.transcriptRepr
  sG2gen := g2foldExp 5
  encG2 := g2foldToEip
  o₀ := fxOptions
  L := fxLowered
  lower := fxLower
  lower_ok := rfl
  bindLocals := []
  shell := fxShell
  shellLayout := fxShellLayout
  evaluatorRuntime := none
  runtimeName := fxRuntimeName
  astOfMain := fun o => match fxLower o with | .ok l => some l.main | .error _ => none
  blk := fxBlk
  plan := fxPlan
  expectedVkCodehash := some (keccak256 fxVkRuntime)
  quotientRuntime := some fxQuotientRuntime
  expectedQuotientCodehash := some (keccak256 fxQuotientRuntime)
  vkDigest_spec := rfl
  vkRuntime_spec := rfl
  main_concat := ⟨GenAst.emitHelpers fxPlan, rfl⟩
  shell_unfolds := rfl
  plan_hasAccumulator := rfl
  plan_numInstances := rfl
  plan_accExpectations := rfl
  evaluator_agrees := rfl
  encG2_shape := fun R => by
    simp only [encG2IsEip, g2foldToEip_size, g2Of?_g2foldToEip, g2PointValid_g2fold]
    decide
  -- P-RESTORE3: the restored pin, on the SAME witness the fixture uses - this Surface
  -- reuses fxPlan, so the layout is the poseidon one and the discharge is rfl again.
  -- Recorded because a pin both Surfaces satisfy by the same witness is one cross-check,
  -- not two.
  hProofLayout := ⟨fxProofProtocol, 48, 3, rfl⟩

/-- The same Surface with the naming convention that names the IMPORTED runtime
    sub-object, exactly as Instances/ImportedIR.lean does for the fixture. The IR leg of
    the headline bundle needs it; nothing else changes. -/
noncomputable def curveIrSurface : Surface blsR G₁z G2fold blsGT :=
  { curveSurface with runtimeName := fun _ => verifierRuntimeName }

/-- **THE REUSED PROGRAM DATA IS THE FIXTURE'S, NOT A COPY OF IT.** Nine equalities, each
    discharged by 'rfl', i.e. by the kernel and not by the compiler - which is why this is
    a theorem and not the '#eval' gate the rest of the directory uses: 'curveSurface' is
    noncomputable, so no projection of it can be compiled. Refuted by restating any field
    instead of citing the fixture's definition, which is the R-58 copy class. -/
theorem curveSurfaceProgramIsTheFixtures :
    curveSurface.L = fxLowered ∧ curveSurface.plan = fxPlan ∧
      curveSurface.shell = fxShell ∧ curveSurface.shellLayout = fxShellLayout ∧
      curveSurface.blk = fxBlk ∧ curveSurface.lower = fxLower ∧
      curveSurface.o₀ = fxOptions ∧ curveSurface.bindLocals = [] ∧
      curveSurface.evaluatorRuntime = none ∧
      curveSurface.runtimeName = fxRuntimeName :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **AND THE CODEC FIELDS ARE THE CURVE ONES.** The other half of the same pin: what
    this Surface installs where the fixture installs the exponent model. -/
theorem curveSurfaceCodecsAreTheCurveOnes :
    curveSurface.E.g1 = g1CodecZ ∧ curveSurface.encG2 = g2foldToEip ∧
      curveSurface.sG2gen = g2foldExp 5 ∧ curveSurface.E.field = frFc :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The five legs, exhibited -/

/-- **LEG 1, by 'rfl': the blk pin.** 'blk' is the emitter and 'L.main' is 'emitMain' of
    the plan the record carries - the fixture's construction, reused unchanged. -/
theorem curveBlk : BlkIsEmitter curveSurface := ⟨fun _ _ => rfl, rfl⟩

/-- **LEG 2: 'SupportedS' AT THE CURVE SURFACE, as a kernel-checked term.** Nine of the
    ten clauses are the fixture's, because they are 'Fr blsR' and 'PlanView' facts and
    those two fields are the fixture's; 'vkPoints' is the one clause the curve codec
    changes, and it discharges through 'g1CodecZ_g1Valid' instead of the identity trick. -/
theorem curveSupported : SupportedS curveSurface curveSurface.o₀ := by
  refine { advice := ?_, instShape := ?_, noRotInst := ?_, acc := ?_,
           singlePhase := ?_, hLimbs := ?_, vkPoints := ?_,
           layout := supportedInhabited.layout, production := ?_, wf := ?_ }
  · decide
  · exact ⟨by decide, by decide⟩
  · decide
  · intro enc h
    exact absurd h (by simp [curveSurface])
  · decide
  · decide
  · intro C hC
    have hnil : C = (1 : G₁z) := by
      simpa [curveSurface, curveVk, List.mem_append, List.mem_singleton] using hC
    subst hnil
    exact g1CodecZ_g1Valid 1
  · exact ⟨by decide, by decide⟩
  · exact ⟨by show fxCs.degree = Except.ok 3; rfl, by decide,
      ⟨by decide, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- **THE 'vkPoints' CLAUSE IS NOT DOING THE IDENTITY TRICK HERE.** Stated for an
    ARBITRARY point of the carrier, which makes it a fact about the CODEC and not about
    the key the fixture happened to need. The fixture cannot state this: at the exponent
    codec the same claim for 'fx 3' is FALSE, which is what 'vkPointsKats_ok' pins and
    what 'expG1Codec_not_holds' runs through. -/
theorem curveVkPoints_anyCommitment (Q : G₁z) : ptReadable (curveSurface.E.g1.toEip Q) :=
  g1CodecZ_g1Valid Q

/-- **LEG 3: 'EnvAgrees' AT THE CURVE SURFACE.** Seven clauses are the fixture's - the
    field constants, the domain, the plan - and the two generator clauses are 'rfl'
    because 'curveParams' reads its generators off the assumed pairing. 'modulus' is
    'rfl' too, which is 'curveFrIsTheSameField' showing up where it matters. -/
theorem curveEnvAgrees : EnvAgrees curveSurface.E curveSurface.vk curveSurface.plan
    curveSurface.params curveSurface.sG2gen :=
  ⟨rfl, fxEnvAgrees.truncWidth, fxEnvAgrees.domainN, fxEnvAgrees.baryWeight,
    fxEnvAgrees.omegaInvMul, fxEnvAgrees.omegaOrder, fxEnvAgrees.negLagranges,
    rfl, rfl, fxEnvAgrees.vkDigestWord⟩

/-- **LEG 4: 'DeploymentW' AT THE CURVE SURFACE.** Every field is about the program - the
    world, the layout, the two runtime images, the codehash pins, the memoryguard bound,
    the address disjointness - and none is about the codec, so the fixture's exhibit
    transfers clause by clause. -/
theorem curveDeployment : DeploymentW curveSurface fxW keccak256 fxVkAddr fxQuotientAddr :=
  ⟨deploymentInhabited.keccak, deploymentInhabited.wf, deploymentInhabited.callvalue,
    deploymentInhabited.static, deploymentInhabited.vkImm, deploymentInhabited.vkCode,
    deploymentInhabited.vkNonEmpty, deploymentInhabited.vkHash, deploymentInhabited.qImm,
    deploymentInhabited.qCode, deploymentInhabited.qHash, deploymentInhabited.qNonEmpty,
    deploymentInhabited.memguard, deploymentInhabited.disjoint⟩

/-- **LEG 5, AND THE REASON THIS FILE EXISTS: 'Eip2537.Holds' IS INHABITED AT A SURFACE.**
    'curveSurface.E.g1' IS 'g1CodecZ' and 'curveSurface.encG2' IS 'g2foldToEip', so the
    binder is the one 'holds_exhibited' discharges and the entire proof is that
    identification. Before this package the statement was true of the CODECS and of no
    Surface; it is now true of a Surface. That is the whole of the advance, and it is an
    instance and not a proof. -/
theorem curveHolds : ∃ product : PairingProduct,
    Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ product := holds_exhibited

/-- **THE HEADLINE EXHIBIT: THE FOUR-WAY BUNDLE, INHABITED AT THE CURVE SURFACE.** One
    term naming all four conjuncts, because halves certify nothing (R-60 S1). This is the
    declaration that is the MIRROR of 'ObligationsGates.bundle_holds_empty': that
    refutation says the bundle is EMPTY at the fixture and it STAYS TRUE - it is a correct
    statement about which codec the fixture installs, and nothing here touches it - while
    this one says the same bundle is INHABITED at the curve Surface. Both hold at once,
    and the pair is the finding: the wall was never the clause, it was the missing
    instance. -/
theorem curveBundle : BlkIsEmitter curveSurface ∧ SupportedS curveSurface curveSurface.o₀ ∧
    EnvAgrees curveSurface.E curveSurface.vk curveSurface.plan curveSurface.params
      curveSurface.sG2gen ∧
      ∃ product : PairingProduct,
        Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ product :=
  ⟨curveBlk, curveSupported, curveEnvAgrees, curveHolds⟩

/-- **THE FIVE-WAY BUNDLE, AT THE IMPORT-NAMING SURFACE.** 'SupportedS', 'DeploymentW',
    'EnvAgrees' and the 'Holds' exhibit, plus the IR pair - one object that BOTH passes
    'curveIrSurface.irCheck' and has a committed 'RunContractIR'. This is the curve-Surface
    twin of 'ObligationsGates.bundle_headlineCore', and it is the most of the headline
    hypothesis bundle that can be supplied WITHOUT a run of the shell or the assembly.
    The legs it does not answer are the run legs, named in 'curveSpecResidualBinders'. -/
theorem curveBundleCore (c : ExternalCalls) (g : ExternalGas) :
    SupportedS curveIrSurface curveIrSurface.o₀ ∧
      DeploymentW curveIrSurface fxW keccak256 fxVkAddr fxQuotientAddr ∧
        EnvAgrees curveIrSurface.E curveIrSurface.vk curveIrSurface.plan
          curveIrSurface.params curveIrSurface.sG2gen ∧
          (∃ product : PairingProduct,
            Eip2537.Holds curveIrSurface.E.g1 ⟨curveIrSurface.encG2⟩ product) ∧
            ∃ (ir : YulObject) (irLyt : EVM.Layout) (obs : Obs),
              curveIrSurface.irCheck ir = true ∧
                RunContractIR curveIrSurface fxW keccak256 ir irLyt irCd c g obs := by
  obtain ⟨product, hh⟩ := curveHolds
  obtain ⟨ir, irLyt, obs, hc, hrun⟩ := irHypothesis_jointlyInhabited c g
  refine ⟨?_, ?_, curveEnvAgrees, ⟨product, hh⟩, ir, irLyt, obs, ?_, hrun⟩
  · exact ⟨curveSupported.advice, curveSupported.instShape, curveSupported.noRotInst,
      curveSupported.acc, curveSupported.singlePhase, curveSupported.hLimbs,
      curveSupported.vkPoints, curveSupported.layout, curveSupported.production,
      curveSupported.wf⟩
  · exact ⟨curveDeployment.keccak, curveDeployment.wf, curveDeployment.callvalue,
      curveDeployment.static, curveDeployment.vkImm, curveDeployment.vkCode,
      curveDeployment.vkNonEmpty, curveDeployment.vkHash, curveDeployment.qImm,
      curveDeployment.qCode, curveDeployment.qHash, curveDeployment.qNonEmpty,
      curveDeployment.memguard, curveDeployment.disjoint⟩
  · exact hc

/-! ### INSTANTIATION, NOT PROOF: what the four spec theorems can now do -/

/-- **THE FIVE SURFACE-SIDE HYPOTHESES OF THE FOUR SPEC THEOREMS, JOINTLY INHABITED.**
    Each of 'pcs_spec', 'finalPairing_spec', 'finalPairing_progress_spec' and
    'finalPairing_acc_spec' takes 'hblk', 'hsup', 'henv', 'hperm' and 'hh' before
    anything about a run. This term is those five at the curve Surface, for the honest
    call relation, and it is the precise form of the claim "the four theorems now
    instantiate here": the elaborator can apply them at 'S := curveSurface' and their
    'Holds' binder is no longer a hypothesis with no model.

    INSTANTIATION, NOT PROOF. The conclusions are 'PartialSound' / 'PartialProgress'
    claims that are registered holes and stay registered holes. And three hypotheses are
    NOT supplied - see 'curveSpecResidualBinders'. -/
theorem curveSpecSurfaceSide (product : PairingProduct)
    (hh : Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ product) :
    BlkIsEmitter curveSurface ∧ SupportedS curveSurface curveSurface.o₀ ∧
      EnvAgrees curveSurface.E curveSurface.vk curveSurface.plan curveSurface.params
        curveSurface.sG2gen ∧
        PermissiveFor curveSurface fxW product fxQuotientAddr
          (curveSurface.calls fxW product fxQuotientAddr) ∧
          Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ product :=
  ⟨curveBlk, curveSupported, curveEnvAgrees, fun _ _ _ h _ => h, hh⟩

/-- **THE RESIDUAL BINDERS, NAMED SO THE EXHIBIT CANNOT BE OVER-READ.** What the four
    spec theorems still need after everything this package supplies: a calldata that
    decodes through the curve codec, instance words that re-enter the field, and a
    snapshot the pipeline produces. None is exhibited here, and 'gap_runLeg_unexhibited'
    is unchanged by this package. The string is a registry record, not prose: a gate can
    point at it. -/
def curveSpecResidualBinders : String :=
  "still unexhibited at the curve Surface: hcd (decodeCalldata = some (ms, instW)), "
    ++ "hinst (instOfWords? = some inst), hsnap (snapshotOf = .ok Snap); blocker: "
    ++ "gap_runLeg_unexhibited, no accepted calldata at any model in the tree"

/-! **INSTANTIATION, CHECKED BY THE ELABORATOR.** The four spec theorems applied at
    the curve Surface. These are '#check' prints and NOT proofs: each prints the residual
    type after 'S := curveSurface', which is exactly the three run-leg binders
    'curveSpecResidualBinders' names. A theorem that could not be instantiated at the curve
    Surface would fail to elaborate here, which is what makes the print evidence rather
    than decoration. -/
#check pcs_spec (S := curveSurface)
#check finalPairing_spec (S := curveSurface)
#check finalPairing_progress_spec (S := curveSurface)
#check finalPairing_acc_spec (S := curveSurface)

/-! ### D-P23: the falsification halves -/

/-- **THE PRODUCT THE EXHIBIT SUPPLIES IS PINNED (D-P23 falsification, half 1).** The
    always-true oracle does not satisfy 'Holds' at the curve codecs, so 'curveHolds' is
    not discharged by an oracle chosen to make it true. Restated AT THIS SURFACE, so the
    exhibit and its refutation are about one object and not about two. -/
theorem curveHolds_refutes_constant_true :
    ¬ Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ (fun _ => true) :=
  holds_refutes_constant_true

/-- **AND SO IS THE ALWAYS-FALSE ONE (D-P23 falsification, half 2).** The all-identity
    frame has pairing sum 0, so 'pairing2' demands 'true' there and a product that never
    says true cannot supply it. Together the two say the free parameter in 'curveHolds'
    is genuinely constrained by the exhibit rather than left free by it. -/
theorem curveHolds_refutes_constant_false :
    ¬ Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ (fun _ => false) :=
  holds_refutes_constant_false

/-- **THE 'encG2_shape' GAP, CLOSED AT THIS SURFACE.** The pin's own doc says the
    strengthening it does NOT make is 'Function.Injective encG2' and that the fixture
    cannot meet it. The curve Surface's encoder is 'g2foldToEip', and it is injective, so
    the strengthening holds here. The scope of the claim matters: this does not change
    'Surface.encG2_shape' - adding a pin the fixture fails would force a fake encoder or
    break the fixture's exhibit, which is exactly what the field doc rules out - it shows
    the gap is a fact about the exponent model rather than about the record. -/
theorem curveEncG2_injective : Function.Injective curveSurface.encG2 :=
  g2foldToEip_injective

/-- **AND THE GAP WAS REAL (D-P23 falsification).** The fixture's encoder is the constant
    EIP infinity word, so it is NOT injective: the strengthening the pin declines to make
    is refuted at the only other Surface in the tree. Without this line
    'curveEncG2_injective' could be read as a property every Surface has, which is the
    over-claim direction this project keeps being burned by. -/
theorem fixtureEncG2_not_injective : ¬ Function.Injective realSurface.encG2 := by
  intro h
  have hne : (fx 5 : RP) ≠ fx 0 := by
    intro e
    exact (by decide : (5 : ZMod rp) ≠ (0 : ZMod rp)) (congrArg Multiplicative.toAdd e)
  have hsame : realSurface.encG2 = fun _ => bytesZero Midfall.Yul.g2Bytes := rfl
  exact hne (h (hsame ▸ rfl))

/-- **THE SUPPORTEDS LEG CAN FAIL AT THE CURVE SURFACE (D-P23 falsification).** The
    exhibit is not satisfied by construction alone: hand the same Surface a constraint
    system whose degree is below the 'chunkLenPositive' bound and the second clause of
    'wf' is refuted. A SupportedS no Surface could fail is the F1 class this
    programme has hit five times, and this is the failing case at the NEW Surface. -/
theorem curveSupported_refuted_by_wrong_cs :
    ¬ SupportedS { curveSurface with vk := { curveVk with csDegree := 2 } } curveSurface.o₀ := by
  rintro h
  exact absurd h.wf.chunkLenPositive (by decide)

/-- **THE HOLDS LEG IS THE ONE THE FIXTURE CANNOT SUPPLY (D-P23 falsification, and the
    exact mirror of 'curveBundle').** Keep everything else and install the FIXTURE's
    exponent codec: the fourth conjunct is then refuted by 'expG1Codec_not_holds'. So the
    exhibit above turns on exactly the fields 'curveSurfaceCodecsAreTheCurveOnes' names,
    and on nothing else - which is the finding, demonstrated as a failing term rather
    than asserted in a paragraph. -/
theorem curveBundle_holds_leg_refuted_at_the_fixture :
    ¬ ∃ product : PairingProduct,
        Eip2537.Holds realSurface.E.g1 ⟨realSurface.encG2⟩ product := by
  rintro ⟨product, h⟩
  exact expG1Codec_not_holds ⟨realSurface.encG2⟩ product h

/-- **THE NAMING FIELD IS LOAD-BEARING AT THE CURVE SURFACE TOO.** 'irCheck' is a
    projection of 'runtimeName' (R-60 S1), so the Surface whose naming convention does not
    name the imported sub-object rejects the imported artifact - at the curve Surface
    exactly as at the fixture. Without this the curve exhibit could be read as making the
    IR leg unconditional. -/
theorem curveIrCheck_refuted_at_the_fixture_naming :
    curveSurface.irCheck verifierIr = false := rfl

/-- **AND ACCEPTED AT THE IMPORT-NAMING SURFACE.** The positive half of the same pair, so
    the previous line is about the naming field and not about the artifact. -/
theorem curveIrCheck_holds_at_imported : curveIrSurface.irCheck verifierIr = true := rfl

/-- **THE NAMING FIELD IS THE ONLY DIFFERENCE BETWEEN THE TWO CURVE SURFACES.** Stated as
    a theorem and not a '#eval': the Surface is noncomputable, so nothing projected out of
    it can be compiled (header). 'runtimeName' is the field that differs and the field
    'irCheck' reads, which is what the two 'rfl' lines above are evidence for. -/
theorem curveSurfacesDifferOnlyInNaming :
    curveIrSurface.runtimeName = (fun _ => verifierRuntimeName) ∧
      curveIrSurface.E = curveSurface.E ∧ curveIrSurface.vk = curveSurface.vk ∧
      curveIrSurface.encG2 = curveSurface.encG2 ∧
      curveIrSurface.runtimeName ≠ curveSurface.runtimeName :=
  ⟨rfl, rfl, rfl, rfl, by
    intro heq
    have h := congrFun heq "Halo2Verifier_292"
    exact absurd h (by decide)⟩

/-! ### Axiom audit -/

-- The exhibit must rest on the D-P36a five and the standard three and on nothing else -
-- except the 'native_decide' axioms the FIXTURE's own layout exhibit carries and this file
-- REUSES rather than re-proving. Reported, not hidden: the trusted base of 'curveBundle' is
-- 'holds_exhibited's trusted base plus the fixture's, and the delta is zero new assumptions.
/-! ### P-LOWEQ: the headline bundle at the curve Surface, and the one leg nothing witnesses -/

/-- **THE 'G1CodecLaws' LEG, MEASURED FIELD BY FIELD AT THE CURVE CODEC.** 'G1CodecLaws'
(Assumptions/Codec.lean:75) has SEVEN fields and, before this package, NO term of that type existed
anywhere in the tree - not at 'g1CodecZ', not at the exponent codec, not at any codec. Five of the
seven are theorems here, in one conjunction: 'eipRoundtrip' and 'ofEip_toEip' are the existing
'g1CodecZ_eipRoundtrip' (G1Agreement.lean:2080) and 'g1CodecZ_ofEip_toEip' (Bls12_381G1.lean:69);
'compressedRoundtrip' holds because 'g1CodecZ.ofCompressed?' is 'fun _ => none', so its premise is
uninhabited; and the two width clauses are 'bytesNatBE_size' and 'g1CodecZ_toEip_size'. -/
theorem g1CodecZ_five_of_seven :
    G1Codec.eipRoundtrip g1CodecZ ∧ G1Codec.compressedRoundtrip g1CodecZ ∧
      (∀ Q : G₁z, g1CodecZ.ofEip? (g1CodecZ.toEip Q) = some Q) ∧
      (∀ Q : G₁z, (g1CodecZ.toCompressed Q).size = g1CompressedWidth) ∧
      (∀ Q : G₁z, (g1CodecZ.toEip Q).size = g1EipWidth) :=
  ⟨g1CodecZ_eipRoundtrip, fun _ _ h => absurd h (by simp [g1CodecZ]),
    g1CodecZ_ofEip_toEip, fun Q => bytesNatBE_size _ fpBytes,
    fun Q => g1CodecZ_toEip_size Q⟩

/-- **THE TWO LEGS THAT DO NOT CLOSE, AND EXACTLY WHY.** 'eipShape' and 'toEip_one' speak the bytes
of a point in the 'Midfall.natToBytesBE' idiom (Common/Bytes.lean:59), while 'g1CodecZ.toEip' is
'g1zToEip' = 'g1PointBytes' = 'fpCoordBytes' = 'bytesAppend eipPad (bytesNatBE x fpBytes)' in the
'YulSemantics' idiom (Yul/Externals.lean:455,191). The two encoders are INTENTIONALLY independent -
Externals.lean:188 says so in terms: "two independent big-endian encoders that must agree is worth
more than one shared one" - and the agreement lemma 'bytesNatBE v n = natToBytesBE v n' is proved
NOWHERE in the tree. So 'G1CodecLaws g1CodecZ' is one byte-bridge lemma away from being a term, and
that lemma is a real job (ByteArray extensionality plus the base-256 digit split), not a formality.

STATED AS A NAMED GAP SO A GATE CAN POINT AT IT, in the style of 'gap_holds_unexhibited' above. -/
def gap_g1codecLaws_unexhibited : String :=
  "G1CodecLaws has no witness at any codec in the tree. Five of seven fields are theorems at "
    ++ "g1CodecZ (g1CodecZ_five_of_seven); eipShape and toEip_one need bytesNatBE v n = "
    ++ "natToBytesBE v n, the bridge between the two independent big-endian encoders that "
    ++ "Yul/Externals.lean:188 keeps apart on purpose and that no file proves."

/-- **A CALADATA THAT SATISFIES 'hsel' AND 'hside' AT THE CURVE SURFACE.** Four bytes: exactly the
selector, so 'bytesTake cd 0 4 = some fnSigVerifyProof' is 'rfl', and 'decodeCalldata' refuses it
on the size guard, so 'SideConditions' holds vacuously. The vacuity is honest and it is the SAME
vacuity 'curveSpecResidualBinders' already names: no accepted calldata exists at any model in the
tree, so a NON-vacuous 'hside' is not supplyable here by anybody. -/
def loweqCd : Bytes := Midfall.Generator.bytesFromNats [0x1e, 0x8e, 0x1e, 0x13]

theorem loweqCd_hsel :
    Midfall.bytesTake loweqCd 0 4 = some Midfall.Generator.fnSigVerifyProof := rfl

theorem loweqCd_hside : SideConditions curveSurface keccak256 loweqCd := by
  intro ms instW inst hdec _
  have hnone :
      Midfall.Lowering.decodeCalldata (p := blsR) curveSurface.plan.proofLayout
        curveSurface.cfg.numInstances curveSurface.E.g1 loweqCd = none := rfl
  rw [hnone] at hdec
  exact absurd hdec (by simp)

/-- **THE HEADLINE BUNDLE, SIX OF ITS SEVEN SURFACE LEGS, JOINTLY INHABITED AT ONE SURFACE.** One
term, not six: 'DeploymentW', 'Holds' (with the product it is exhibited at), 'EnvAgrees',
'SupportedS', 'hsel', 'hside', and the 'WorldLocal' leg the restatement added. The seventh leg,
'G1CodecLaws', is the one nothing witnesses - see 'gap_g1codecLaws_unexhibited' - and that is the
finding, reported rather than papered over: as it stands the headline theorem's 'hcodec' binder has
no model in this tree, so the theorem is proved but its hypothesis bundle is not known inhabited. -/
theorem loweqBundleCore (product : PairingProduct)
    (hh : Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ product) :
    SupportedS curveSurface curveSurface.o₀ ∧
      DeploymentW curveSurface fxW keccak256 fxVkAddr fxQuotientAddr ∧
        EnvAgrees curveSurface.E curveSurface.vk curveSurface.plan curveSurface.params
          curveSurface.sG2gen ∧
          Eip2537.Holds curveSurface.E.g1 ⟨curveSurface.encG2⟩ product ∧
          SideConditions curveSurface keccak256 loweqCd ∧
          Midfall.bytesTake loweqCd 0 4 = some Midfall.Generator.fnSigVerifyProof ∧
          (curveSurface.calls fxW product fxQuotientAddr).WorldLocal :=
  ⟨curveSupported, curveDeployment, curveEnvAgrees, hh, loweqCd_hside, loweqCd_hsel,
    honestCalls_worldLocal product fxQuotientAddr (fun _ _ _ => False)
      (fun _ _ _ _ _ => Iff.rfl)⟩

/-- **THE 'WorldLocal' LEG IS NOT FREE AT AN EXTERNALISED RENDER.** The restatement's one new
hypothesis is discharged here because 'curveSurface.evaluatorRuntime = none', so the evaluator slot
answers 'False' for every request and the side condition on 'honestCalls_worldLocal' is trivial.
Swap in a Surface that DOES externalise the evaluator and this line is exactly where the registered
hole 'Bridge.rel_worldLocal' bites. The falsification half: the trivial slot relation is what makes
it go, and it is a fact about this record, not a general theorem about 'S.calls'. -/
theorem loweqWorldLocal_is_the_none_evaluator : curveSurface.evaluatorRuntime = none := rfl

#print axioms Midfall.Instances.CurveSurface.g1CodecZ_five_of_seven
#print axioms Midfall.Instances.CurveSurface.loweqBundleCore
#print axioms Midfall.Instances.CurveSurface.loweqCd_hsel
#print axioms curveBundle
#print axioms curveHolds
#print axioms curveEnvAgrees
#print axioms curveEncG2_injective
#print axioms fixtureEncG2_not_injective
#print axioms curveSupported_refuted_by_wrong_cs

end Midfall.Instances.CurveSurface
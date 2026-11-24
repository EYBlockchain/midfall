/-
  Midfall.Instances.ValidV3F1Real

  **B4V3: THE F1-REAL `ValidV3`, ASSEMBLED FROM B3'S POINT HALF.**

  `PayloadPointsF1.f1PointRenderCN n` is F1's render with three data lanes re-sourced:
  the Lean key's 19/8 commitments are the payload's decoded points (`f1VkResourced`), the KZG
  parameters carry the payload's `s·H2` (`f1ParamsResourced n`), and `sG2gen` is that point's
  inverse. Its point half is B3's `f1PointRenderCN_payloadPointHalf n hpay`, where the ONE data
  input is

      hpay : vkG2Words f1Pv vkNegSG2BaseSlot = g2foldToEip (g2foldExp n)

  - the tracked artifact's NEG_S_G2 bytes name the exponent `n`. This file assembles the OTHER
  six clauses and the nine scalar payload fields at that render and combines the two halves:

      f1PointRenderCN_validV3 (n) (hpay) : ValidV3 (f1PointRenderCN n)

  No hypothesis is added to `ValidV3`: `hpay` is a DATA statement about the artifact's own bytes,
  consumed through B3's point-half theorem, and the assembly below re-proves every clause at the
  render's own computable faces.

  WHAT TRANSFERS AND WHY. `Render.pv` is derived (`planViewOf R.plan R.model R.cfg.accumulator`,
  `LoweringV2/Statements.lean:162`) and the render carries the same plan/model/cfg as
  `f1GeneratedRender`, so `f1PointRenderC_pv` gives `pv = f1Pv` by `rfl`: the program, the scans,
  the no-writers clause, the layout and the payload's nine scalar fields are the F1 measurements.
  What changes is the Lean key (`poseidonVkExec` -> `f1VkResourced`), the KZG parameters, the
  `sG2gen` slot and `Gₜ` (the constructed pairing `pairingF1`, whose generators are `g1zGen` and
  `g2foldExp 1` by `rfl`), so `generated`, `env` and `supported` are re-established:
  * `generated`: `generateAll` on the re-sourced key is `.ok genFilledOut` - the generator reads
    the commitment COUNTS and the payload, not the commitment elements, and the run's three
    projections are `genFilledOut`'s by `rfl` (`f1ResOut_eq`). Computed, not assumed:
    `f1ResRun_isOk`.
  * `env`: nine fields read only the key/cfg/domain (unchanged by the re-source); `nG2`/`sG2` are
    `rfl` at `f1ParamsResourced n`/`pairingF1`; the plan-view fields are F1's.
  * `supported`: `wf` is D.2's `WellFormed` proof (the re-source changes commitment ELEMENTS, not
    any count, domain or CS face), `vkPoints` is `g1CodecZ_g1Valid` applied to every element of
    the carrier (`ptReadable_g1zToEip`), and the layout pair is F1's plan.

  THE RESIDUAL. This is `ValidV3` at an F1-real render; it is NOT `Done`. `Done` additionally
  needs the gate (`GateAtV3`, which requires `G1CodecLawsV3` - FALSE at this render's codec
  `g1CodecZ`, `VacuityWitnesses.f1_codec_headline_false`), totality, and artifact equality. Those
  are named at the foot.
-/
import Midfall.Instances.PayloadPointsF1
import Midfall.Instances.GeneratorDone
import Midfall.Instances.NativeReplay

set_option autoImplicit false

namespace Midfall.Instances.ValidV3F1Real

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.Instances
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1 Midfall.Instances.ValidV3InhabitationF1Completion
open Midfall.Instances.PayloadPointsF1

/-! ## 1. The generator at the re-sourced key.

  `generateAll` is run on `f1VkResourced` instead of `poseidonVkExec`. The two keys differ only in
  the ELEMENTS of the two commitment arrays (the sizes are 19/8 on both), and the generator's
  output projections are `genFilledOut`'s by `rfl` - the measurement below is the machine-checked
  face of that, and `f1ResOut_eq` is the kernel equality the `generated` clause consumes. -/

/-- The generator run at the re-sourced key and the F1 payload. -/
def f1ResRun : Except Fault GenOut :=
  generateAll Features.solidity poseidonDelta f1VkResourced poseidonConfig f1FilledPayload
    poseidonInputs poseidonFlags

/-- **THE GENERATOR ACCEPTS THE RE-SOURCED KEY.** AXIOM:
    f1ResRun_isOk._native.native_decide.ax_1_1. -/
theorem f1ResRun_isOk : f1ResRun.isOk = true := by native_decide

/-- The accepted output. -/
def f1ResOut : GenOut := f1ResRun.getOk f1ResRun_isOk

/-- **THE RUN'S OUTPUT IS F1's OUTPUT, BY THE KERNEL.** The change of commitment elements does not
    reach any projection the generator returns. -/
theorem f1ResOut_eq : f1ResOut = genFilledOut := rfl

theorem f1ResRun_eq_ok : f1ResRun = .ok genFilledOut := by
  rw [Except.eq_ok_getOk f1ResRun f1ResRun_isOk]
  exact congrArg Except.ok f1ResOut_eq

/-! ## 1b. The tracked F1 fixture, decoded and checked at the render's own faces

  `poseidonFixtureCalldata` is the tracked `calldata.bin` as a pure term. `f1FixtureDecoded` is
  `decodeCalldata` at the F1 plan/layout and the computable codec `g1CodecC`; the two Bool checks
  are the same `prepareMsgs`/`snapshotOf` computations the verifier runs, evaluated once (the
  `native_decide` facts below) so the universal `SoundSide`/`CompleteSide` clauses never need the
  message list as an explicit term. They are defined OUTSIDE the `noncomputable section` below:
  `prepareMsgs` at the global computable pairing instance is executable, and its value is
  definitionally the same at the section's `pairingF1` (both have `g₁ = g1zGen`,
  `g₂ = g2foldExp 1`). -/

def f1FixtureDecoded : Option (List (Msg (Fr blsR) G₁z) × Array Word256) :=
  Midfall.Lowering.decodeCalldata (p := blsR) genFilledOut.plan.proofLayout
    poseidonConfig.numInstances g1CodecC Midfall.Instances.GeneratorDone.poseidonFixtureCalldata

/-- The fixture decode's `prepareMsgs` is panic-free (the tracked proof is honest). -/
def f1FixtureSoundCheck : Bool :=
  match f1FixtureDecoded with
  | some (ms, instW) =>
      match Midfall.LoweringV2.instOfWords? (p := blsR) instW with
      | some inst =>
          match prepareMsgs (Gₜ := G₁z) Midfall.Instances.NativeReplay.envReal keccak256
              Features.solidity f1VkResourced inst ms with
          | .error (.panic msg) => false
          | _ => true
      | none => true
  | none => true

/-- The two `ChallengesGood` fields at the fixture snapshot, as a Bool. -/
def f1FixtureChallengesGoodB (S : Snapshot blsR G₁z G2fold G₁z) : Bool :=
  decide (S.alg.x ^ f1VkResourced.domain.n ≠ 1) && decide (S.alg.x ≠ 0)

/-- The fixture snapshot's `ChallengesGood` computation. -/
def f1FixtureCompleteCheck : Bool :=
  match f1FixtureDecoded with
  | some (ms, instW) =>
      match Midfall.LoweringV2.instOfWords? (p := blsR) instW with
      | some inst =>
          match snapshotOf Midfall.Instances.NativeReplay.envReal keccak256 f1VkResourced
              inst ms none with
          | .ok S => f1FixtureChallengesGoodB S
          | .error _ => true
      | none => true
  | none => true

theorem f1FixtureSoundCheck_eq : f1FixtureSoundCheck = true := by native_decide
theorem f1FixtureCompleteCheck_eq : f1FixtureCompleteCheck = true := by native_decide

/-- The fixture snapshot exists at the render's own key/params (the same `snapshotOf` run). -/
def f1FixtureSnapshotCheck : Bool :=
  match f1FixtureDecoded with
  | some (ms, instW) =>
      match Midfall.LoweringV2.instOfWords? (p := blsR) instW with
      | some inst =>
          match snapshotOf Midfall.Instances.NativeReplay.envReal keccak256 f1VkResourced
              inst ms none with
          | .ok _ => true
          | .error _ => false
      | none => false
  | none => false

theorem f1FixtureSnapshotCheck_eq : f1FixtureSnapshotCheck = true := by native_decide

theorem f1FixtureChallengesGood_of_b (S : Snapshot blsR G₁z G2fold G₁z)
    (h : f1FixtureChallengesGoodB S = true) : ChallengesGood f1VkResourced S := by
  have hh := h
  simp only [f1FixtureChallengesGoodB, Bool.and_eq_true] at hh
  exact ⟨of_decide_eq_true hh.1, of_decide_eq_true hh.2⟩

/-! ## 1c. The key mismatch, named on both sides

  `f1VkResourced` IS the production key: its two commitment arrays are the decoded
  `poseidon/vk.json` commitments and its transcript representation is that file's. The tracked
  `poseidon-testsrs` proof was produced for the test-SRS key `NativeReplay.vkF1`, whose three
  fields differ (`f1FixtureVk_differs`). This is why the fixture can discharge the
  decode/sound/complete clauses at the render but not `LeanAccepts`: the latter runs `verifyMsgs`
  at the render's key. The final theorem below makes the failure a COMPUTATION at the test-SRS
  parameter point, not an absence of proof: even when the render's parameters are the bundle's own
  trapdoor, the tracked proof still fails at the production key. -/

/-- The production `vk.json` fixed commitments, decoded into the carrier by the computable codec.
    This is the list `f1VkResourced` carries. -/
def f1ProductionFixedCommitments : List G₁z :=
  Midfall.Instances.PoseidonFixture.poseidonVkData.fixedCommitmentHex.toList.map
    (fun b => (g1CodecC.ofCompressed? b).getD 1)

/-- The production `vk.json` permutation commitments, decoded. -/
def f1ProductionPermutationCommitments : List G₁z :=
  Midfall.Instances.PoseidonFixture.poseidonVkData.permutationCommitmentHex.toList.map
    (fun b => (g1CodecC.ofCompressed? b).getD 1)

/-- **THE RENDER'S FIXED COMMITMENTS ARE THE PRODUCTION KEY'S.** AXIOM:
    f1VkResourced_fixed_eq_production._native.native_decide.ax_1_1. -/
theorem f1VkResourced_fixed_eq_production :
    f1VkResourced.fixedCommitments.toList = f1ProductionFixedCommitments := by
  native_decide

/-- **THE RENDER'S PERMUTATION COMMITMENTS ARE THE PRODUCTION KEY'S.** AXIOM:
    f1VkResourced_perm_eq_production._native.native_decide.ax_1_1. -/
theorem f1VkResourced_perm_eq_production :
    f1VkResourced.permutation.commitments.toList = f1ProductionPermutationCommitments := by
  native_decide

/-- The render's transcript representation is the production `vk.json` field. -/
theorem f1VkResourced_transcript_eq_production :
    f1VkResourced.transcriptRepr =
      (bytesToNatBE Midfall.Instances.PoseidonFixture.poseidonVkData.transcriptReprBytes :
        Fr blsR) := rfl

/-- The render's CS degree is the production `vk.json` field (and the test-SRS key's too: this is
    the one key field the two bundles share). -/
theorem f1VkResourced_csDegree_eq_production :
    f1VkResourced.csDegree =
      Midfall.Instances.PoseidonFixture.poseidonVkData.csDegree := rfl

/-- **THE ONE KEY FIELD THE FIXTURE AND THE RENDER SHARE.** `csDegree` is 5 in both bundles; the
    mismatch in `f1FixtureVk_differs` is therefore exactly the commitment arrays and the
    transcript representation, not a degree difference. -/
theorem f1FixtureVk_csDegree_agrees :
    (Midfall.Instances.NativeReplay.vkF1.getD f1VkResourced).csDegree =
      f1VkResourced.csDegree := by
  native_decide

/-- `f1ParamsResourced` with the `noncomputable` marker peeled off. The body only uses group
    inversion and the exponent fold, so it is executable; the equality is `rfl`. -/
def f1ParamsC (n : Nat) : ParamsVerifierKZG G₁z G2fold :=
  { sG2 := (g2foldExp n)⁻¹
    nG2Prepared := (g2foldExp 1)⁻¹
    sG2Prepared := (g2foldExp n)⁻¹ }

theorem f1ParamsResourced_eq_C : f1ParamsResourced = f1ParamsC := rfl

/-- The tracked test-SRS verifier parameters, named from the bundle's exported trapdoor:
    `sG2 = sTest·H2` and `nG2Prepared = -H2`. -/
def f1TestSrsParams : ParamsVerifierKZG G₁z G2fold :=
  ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd (sTest : ZMod blsR))

/-- **`n = r - sTest` IS THE TEST-SRS PARAMETER POINT.** The render's computable parameters at
    that exponent are the bundle's own trapdoor. AXIOM:
    f1ParamsC_testExponent_eq._native.native_decide.ax_1_1 (three fields). -/
theorem f1ParamsC_testExponent_eq :
    f1ParamsC (blsR - sTest) = f1TestSrsParams := by
  have h1 : (f1ParamsC (blsR - sTest)).sG2 = f1TestSrsParams.sG2 := by native_decide
  have h2 : (f1ParamsC (blsR - sTest)).nG2Prepared = f1TestSrsParams.nG2Prepared := by
    native_decide
  have h3 : (f1ParamsC (blsR - sTest)).sG2Prepared = f1TestSrsParams.sG2Prepared := by
    native_decide
  exact ParamsVerifierKZG.mk.injEq _ _ _ _ _ _ |>.mpr ⟨h1, h2, h3⟩

/-- `verifyMsgs` at the render's key, the tracked decode, and the test-SRS parameter point
    (`n = r - sTest`, so `sG2Prepared` is the bundle's own `s·H2`): the run is a closed
    computation, and it is NOT `.ok ()`. -/
def f1FixtureVerifyAtTestExponentCheck : Bool :=
  match f1FixtureDecoded with
  | some (ms, instW) =>
      match Midfall.LoweringV2.instOfWords? (p := blsR) instW with
      | some inst =>
          match verifyMsgs (Gₜ := G₁z) Midfall.Instances.NativeReplay.envReal keccak256
              Features.solidity (f1ParamsC (blsR - sTest)) f1VkResourced inst ms with
          | .ok () => true
          | _ => false
      | none => false
  | none => false

/-- **THE FIXTURE'S `verifyMsgs` IS FALSE AT THE RENDER'S KEY.** AXIOM:
    f1FixtureVerifyAtTestExponentCheck_eq_false._native.native_decide.ax_1_1. -/
theorem f1FixtureVerifyAtTestExponentCheck_eq_false :
    f1FixtureVerifyAtTestExponentCheck = false := by native_decide

/-- **THE TRACKED FIXTURE IS NOT ACCEPTED AT THE RENDER'S KEY.** At the test-SRS parameter point
    (`n = r - sTest`, `f1ParamsC_testExponent_eq`) the render's parameters ARE the bundle's own
    trapdoor, and the proof still fails: `f1VkResourced` carries the production commitments, while
    the proof was produced for `NativeReplay.vkF1`. This is the exact data mismatch behind
    `LeanAccepts`; it is not a missing proof step, and it does not weaken any statement. -/
theorem f1PointRenderCCN_not_leanAccepts_testExponent :
    ¬ LeanAccepts (f1PointRenderCCN (blsR - sTest)) keccak256
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata := by
  rintro ⟨ms, instW, inst, hdec, hinst, hver⟩
  have hdec' : f1FixtureDecoded = some (ms, instW) := by
    rw [← show Midfall.Lowering.decodeCalldata (p := blsR)
        (f1PointRenderCCN (blsR - sTest)).plan.proofLayout
        (f1PointRenderCCN (blsR - sTest)).cfg.numInstances
        (f1PointRenderCCN (blsR - sTest)).E.g1
        Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = f1FixtureDecoded from rfl]
    exact hdec
  cases hd : f1FixtureDecoded with
  | none => rw [hd] at hdec'; cases hdec'
  | some p =>
      obtain ⟨ms0, instW0⟩ := p
      have hpair : (ms0, instW0) = (ms, instW) :=
        Option.some.inj (by rw [hd] at hdec'; exact hdec')
      obtain ⟨hms, hinstW⟩ := Prod.mk.inj hpair
      subst hms hinstW
      cases hi : Midfall.LoweringV2.instOfWords? (p := blsR) instW0 with
      | none => rw [hi] at hinst; cases hinst
      | some inst0 =>
          have hinst0 : inst0 = inst :=
            Option.some.inj (by rw [hi] at hinst; exact hinst)
          subst hinst0
          have hver' : verifyMsgs (Gₜ := G₁z) Midfall.Instances.NativeReplay.envReal
              keccak256 Features.solidity (f1ParamsC (blsR - sTest)) f1VkResourced inst0 ms0 =
              .ok () := hver
          have hcheck := f1FixtureVerifyAtTestExponentCheck_eq_false
          unfold f1FixtureVerifyAtTestExponentCheck at hcheck
          simp only [hd, hi] at hcheck
          rw [hver'] at hcheck
          exact Bool.noConfusion hcheck

/-! ## 2. The clauses at `f1PointRenderCN n` -/

noncomputable section

/-- The constructed pairing `pairingF1` is the instance the point render is stated at; it is the
    same term `PayloadPointsF1` used, repeated locally so this module does not perturb the global
    instance search (a second `AdmissiblePairing ... G₁z` instance makes the `blsGT` search
    diverge - `PayloadPointsF1`'s §3 note). -/
local instance : AdmissiblePairing G₁z G2fold G₁z := pairingF1

/-- `ptReadable` at the exhibit codec's encoder, for EVERY carrier element. This is
    `g1CodecZ_g1Valid` (all four `G1CodecLaws` at the real-curve codec, `G1Agreement.lean`) read
    as the `ptReadable` predicate: no hypothesis, no computation at the render. -/
theorem ptReadable_g1zToEip (Q : G₁z) :
    Midfall.LoweringV2.ptReadable (g1zToEip Q) :=
  g1CodecZ_g1Valid Q

/-- **`generated` AT THE RE-SOURCED RENDER.** The run is `f1ResRun`; the payload argument is the
    render's own plan vk, which is the filled payload by F1's fixed point. -/
theorem f1PointRenderCN_generated (n : Nat) :
    Midfall.LoweringV3.GeneratedBy (f1PointRenderCN n) := by
  refine ⟨genFilledOut, ?_, rfl, rfl, rfl⟩
  show generateAll Features.solidity poseidonDelta f1VkResourced poseidonConfig
    genFilledOut.plan.vk poseidonInputs poseidonFlags = .ok genFilledOut
  rw [genFilledOut_plan_vk_is_the_payload_it_was_given]
  exact f1ResRun_eq_ok

/-- **`inputs` AT THE RE-SOURCED RENDER.** The key's domain is `poseidonVkExec`'s (the re-source
    changes only the commitment arrays), and the inputs/cfg are F1's. -/
theorem f1PointRenderCN_inputs (n : Nat) :
    (f1PointRenderCN n).inputs.numInstances = (f1PointRenderCN n).cfg.numInstances ∧
      (f1PointRenderCN n).inputs.accEncoding = (f1PointRenderCN n).cfg.accumulator ∧
      (f1PointRenderCN n).inputs.k = (f1PointRenderCN n).vk.domain.k ∧
      (f1PointRenderCN n).inputs.truncatedChallenges =
        Features.solidity.truncatedChallenges :=
  poseidonValid_inputs

/-- **THE DECIDABLE BUNDLE AT THE RE-SOURCED RENDER.** The view is `f1Pv` and the model is
    `genFilledOut`'s; the only re-sourced input the bundle reads is `permCommMatchRepaired`, a
    count comparison (19/8 unchanged). AXIOM:
    f1PointRenderCN_deciding_programOkB._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_deciding_programOkB (n : Nat) :
    Midfall.LoweringV3.programOkB (f1PointRenderCN n) = true := by
  show Midfall.LoweringV3.programOkCore f1Pv f1M poseidonConfig.numInstances
    f1VkResourced = true
  native_decide

/-- **THE PROGRAM CLAUSE.** The program is built from `pv`/`model` only, so the three scans and
    the address fit are F1's; the bundle is re-decided above. -/
theorem f1PointRenderCN_program (n : Nat) :
    Midfall.LoweringV3.programOk (f1PointRenderCN n) := by
  refine ⟨f1PointRenderCN_deciding_programOkB n, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.GasCallOk (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasCallOk
  · show Midfall.LoweringV3.GasFree (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasFree
  · show Midfall.LoweringV3.ExitDiscipline (asmOf f1Pv f1M 0 0)
    exact f1_deciding_exitDiscipline
  · show Midfall.LoweringV3.programFits f1Pv f1M
    exact f1_deciding_programFit

/-- **`noWriters` AT THE RE-SOURCED RENDER.** Same program as F1's. -/
theorem f1PointRenderCN_noWriters (n : Nat) :
    Midfall.Yul.Bridge.NoWriters ((f1PointRenderCN n).prog 0 0) := by
  show Midfall.Yul.Bridge.NoWriters (asmOf f1Pv f1M 0 0)
  exact f1_noWriters

/-- **`env` AT THE RE-SOURCED RENDER.** Domain, CS, field constants and delta are unchanged; the
    two pairing-parameter fields are `rfl` at `f1ParamsResourced n` and `pairingF1`; the three
    plan-view fields are F1's. AXIOM:
    f1PointRenderCN_env._native.native_decide.ax_1_1 through ax_1_3. -/
theorem f1PointRenderCN_env (n : Nat) :
    EnvAgrees (f1PointRenderCN n).E (f1PointRenderCN n).vk (f1PointRenderCN n).pv
      (f1PointRenderCN n).params (f1PointRenderCN n).sG2gen := by
  obtain ⟨hmod, htrunc, hd1, _hd2, hbary, homega, horder, _hng2, _hsg2, _hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, ?_⟩, hbary, homega, horder, ?_, rfl, rfl, ?_⟩
  · rw [show (f1PointRenderCN n).pv = f1Pv from f1PointRenderC_pv _ _ _]
    show poseidonVkExec.domain.k = f1Pv.k
    native_decide
  · rw [show (f1PointRenderCN n).pv = f1Pv from f1PointRenderC_pv _ _ _]
    show f1Pv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
    native_decide
  · rw [show (f1PointRenderCN n).pv = f1Pv from f1PointRenderC_pv _ _ _]
    show (f1Pv.vk.constants.getD 0 ("", 0)).2 = frWord poseidonVkExec.transcriptRepr
    native_decide

/-- **THE NINE SCALAR PAYLOAD FIELDS AT THE RE-SOURCED RENDER.** Same payload, same view, same
    plan meta; the fields that read `vk` read its domain/transcript representation, which the
    re-source does not change. Re-decided at the render's computable faces rather than transferred,
    so the key's changed commitment elements are not assumed away. AXIOM:
    f1PointRenderCN_payloadScalars._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_payloadScalars (n : Nat) :
    PayloadScalarHalf (f1PointRenderCN n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.vkDigest =
      frWord poseidonVkExec.transcriptRepr
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.numInstances =
      BitVec.ofNat 256 poseidonConfig.numInstances
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.k =
      BitVec.ofNat 256 poseidonVkExec.domain.k
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.nInv =
      frWord (((2 ^ poseidonVkExec.domain.k : ℕ) : Fr blsR))⁻¹
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.omega =
      frWord poseidonVkExec.domain.omega
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.omegaInv =
      frWord poseidonVkExec.domain.omegaInv
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.omegaInvToL =
      frWord (poseidonVkExec.domain.omegaInv ^
        genFilledOut.plan.meta_.rotationLast.natAbs)
    native_decide
  · show ((Midfall.LoweringV3.payloadWord f1Pv
        vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
      accWordsOfEncoding poseidonConfig.accumulator
    native_decide
  · show 11 ≤ f1Pv.vk.constants.length
    native_decide

set_option maxHeartbeats 1000000 in
/-- **`WellFormed` AT THE RE-SOURCED KEY.** Every field is a count, a domain fact or a CS fact;
    the re-source changes only the commitment ELEMENTS. AXIOM:
    f1VkResourced_wf._native.native_decide.ax_1_1 through ax_1_3 (plus
    `deciding_supported_degree_eq`). -/
theorem f1VkResourced_wf : f1VkResourced.WellFormed Features.solidity where
  csDegreeMatches := deciding_supported_degree_eq
  chunkLenPositive := by native_decide
  domainConsistent := by native_decide
  permutationCommitmentsMatch := by native_decide
  fixedCommitmentsMatch := by native_decide
  singlePhase := by native_decide
  committedInstancesOn := rfl
  advicePhaseTotal := by native_decide
  challengePhaseTotal := by native_decide
  lookupChunkable := by native_decide
  fixedSelectorBound := by native_decide
  fixedQueriesBound := by native_decide
  simpleSelectorQueriesBound := by native_decide
  instanceRotZero := by native_decide
  instanceQueriesBound := by native_decide
  advicePhaseColumnOrder := by native_decide


/-- **`supported` AT THE RE-SOURCED RENDER.** `wf` is D.2's `WellFormed` (the re-source changes
    the commitment ELEMENTS; every count, domain and CS face is unchanged), `vkPoints` is
    `ptReadable_g1zToEip`, and the layout pair is F1's plan. AXIOM:
    f1PointRenderCN_supported_layout._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_supported (n : Nat) : SupportedV2 (f1PointRenderCN n) := by
  obtain ⟨hadvice, hinst1, hinst2, hsphase, hlimbs, _hlay1, _hlay2, hprod1, hprod2, hnoacc,
    hemb1, hemb2, hsep, _hci, hnorot⟩ := poseidonValid_supported_rest
  refine ⟨hadvice, ⟨hinst1, hinst2⟩, hnorot, hsphase, hlimbs, ?_, ⟨?_, ?_⟩,
    ⟨hprod1, hprod2⟩, f1VkResourced_wf, hnoacc, ⟨hemb1, hemb2⟩, hsep⟩
  · intro C _hC
    exact ptReadable_g1zToEip C
  · show genFilledOut.plan.memory.map.WellFormed
    native_decide
  · show genFilledOut.plan.memory.validate.isOk = true
    native_decide

/-- **THE SIX CLAUSES AND THE SCALAR HALF AT THE RE-SOURCED RENDER, PROVED.** -/
theorem f1PointRenderCN_validV3ExceptPayload (n : Nat) :
    ValidV3ExceptPayload (f1PointRenderCN n) :=
  ⟨f1PointRenderCN_generated n, f1PointRenderCN_inputs n, f1PointRenderCN_program n,
    f1PointRenderCN_noWriters n, f1PointRenderCN_env n, f1PointRenderCN_payloadScalars n,
    f1PointRenderCN_supported n⟩

/-- **THE F1-REAL `ValidV3`, FROM THE ONE PAYLOAD DATA STATEMENT.** `hpay` is B3's data input: the
    artifact's NEG_S_G2 bytes are the EIP encoding of `g2foldExp n`. Everything else is proved. -/
theorem f1PointRenderCN_validV3 (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCN n) :=
  (validV3_iff_exceptPayload_and_points (f1PointRenderCN n)).2
    ⟨f1PointRenderCN_validV3ExceptPayload n, f1PointRenderCN_payloadPointHalf n hpay⟩

/-- The residual expressed as an equivalence: at the re-sourced render, `ValidV3` is EXACTLY
    B3's one data statement about the artifact's neg-S-G2 slot. -/
theorem f1PointRenderCN_validV3_iff (n : Nat) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCN n)
      ↔ Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
          = g2foldToEip (g2foldExp n) := by
  constructor
  · intro h
    exact (f1PointRenderCN_payloadPointHalf_iff n).1
      ((validV3_iff_exceptPayload_and_points (f1PointRenderCN n)).1 h).2
  · intro h
    exact f1PointRenderCN_validV3 n h

/-! ## 2b. THE PARALLEL RENDER WITH THE COMPUTABLE CODEC

  `f1PointRenderCCN n` is `f1PointRenderCN n` with `E.g1 := g1CodecC`; the key, parameters,
  carrier, plan, model and program are unchanged. `f1PointRenderCCN_codec_lawsV3` is B3's
  `g1CodecC_lawsV3`. Every `ValidV3` clause is re-established here: the four clauses that do not
  mention `E` transfer definitionally, and `env`/`payloadScalars`/`supported` are rebuilt from
  the same F1 measurements. The point half is B3's, transported through `toEip = g1zToEip`. -/

theorem f1PointRenderCCN_generated (n : Nat) :
    Midfall.LoweringV3.GeneratedBy (f1PointRenderCCN n) :=
  f1PointRenderCN_generated n

theorem f1PointRenderCCN_inputs (n : Nat) :
    (f1PointRenderCCN n).inputs.numInstances = (f1PointRenderCCN n).cfg.numInstances ∧
      (f1PointRenderCCN n).inputs.accEncoding = (f1PointRenderCCN n).cfg.accumulator ∧
      (f1PointRenderCCN n).inputs.k = (f1PointRenderCCN n).vk.domain.k ∧
      (f1PointRenderCCN n).inputs.truncatedChallenges =
        Features.solidity.truncatedChallenges :=
  f1PointRenderCN_inputs n

theorem f1PointRenderCCN_program (n : Nat) :
    Midfall.LoweringV3.programOk (f1PointRenderCCN n) :=
  f1PointRenderCN_program n

theorem f1PointRenderCCN_noWriters (n : Nat) :
    Midfall.Yul.Bridge.NoWriters ((f1PointRenderCCN n).prog 0 0) :=
  f1PointRenderCN_noWriters n

/-- `env` at the computable-codec render: every field is the F1 measurement at the same key,
    domain and plan view; only `E.g1` differs and no `EnvAgrees` field reads it. -/
theorem f1PointRenderCCN_env (n : Nat) :
    EnvAgrees (f1PointRenderCCN n).E (f1PointRenderCCN n).vk
      (f1PointRenderCCN n).pv (f1PointRenderCCN n).params (f1PointRenderCCN n).sG2gen := by
  have h := f1PointRenderCN_env n
  refine ⟨h.modulus, h.truncWidth, h.domainN, h.baryWeight, h.omegaInvMul, h.omegaOrder,
    h.negLagranges, h.nG2, h.sG2, h.vkDigestWord⟩

/-- The nine scalar payload fields at the computable-codec render. -/
theorem f1PointRenderCCN_payloadScalars (n : Nat) :
    PayloadScalarHalf (f1PointRenderCCN n) := by
  have h := f1PointRenderCN_payloadScalars n
  refine ⟨h.digest, h.numInstances, h.k, h.nInv, h.omega, h.omegaInv, h.omegaInvToL,
    h.accWords, h.constantsLength⟩

/-- `supported` at the computable-codec render. `vkPoints` is the same `ptReadable` face
    because `g1CodecC.toEip` is `g1zToEip`; the remaining fields are the F1 measurements. -/
theorem f1PointRenderCCN_supported (n : Nat) :
    SupportedV2 (f1PointRenderCCN n) := by
  have h := f1PointRenderCN_supported n
  refine ⟨h.advice, h.instShape, h.noRotInst, h.singlePhase, h.hLimbs, ?_, h.layout,
    h.production, h.wf, h.noAcc, h.embeddedQuotient, h.separateVk⟩
  intro C hC
  show Midfall.LoweringV2.ptReadable (g1zToEip C)
  exact h.vkPoints C hC

theorem f1PointRenderCCN_validV3ExceptPayload (n : Nat) :
    ValidV3ExceptPayload (f1PointRenderCCN n) :=
  ⟨f1PointRenderCCN_generated n, f1PointRenderCCN_inputs n, f1PointRenderCCN_program n,
    f1PointRenderCCN_noWriters n, f1PointRenderCCN_env n, f1PointRenderCCN_payloadScalars n,
    f1PointRenderCCN_supported n⟩

/-- **`ValidV3` AT THE COMPUTABLE-CODEC F1 RENDER.** The codec conjunct is now PROVED
    (`f1PointRenderCCN_codec_lawsV3`); the only data input is the same `hpay` as at
    `f1PointRenderCN`. -/
theorem f1PointRenderCCN_validV3 (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCCN n) := by
  rw [validV3_iff_exceptPayload_and_points]
  exact ⟨f1PointRenderCCN_validV3ExceptPayload n, f1PointRenderCCN_payloadPointHalf n hpay⟩

/-- **THE CODEC CONJUNCT OF `GateAtV3`, PROVED.** The rest of the gate is carried as the named
    inputs of `GateAtV3`; the codec slot is `f1PointRenderCCN_codec_lawsV3`. -/
theorem f1PointRenderCCN_gateAtV3_of
    (n : Nat) (product : PairingProduct) (cd : Bytes)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256) (st₀ : EvmState)
    (hdep : DeploymentV2 (f1PointRenderCCN n) W keccak256 vkAddr)
    (hentry : EntryFrameV3 (f1PointRenderCCN n) W Lyt keccak256 cd st₀)
    (hpc : Eip2537.Holds (f1PointRenderCCN n).E.g1 ⟨(f1PointRenderCCN n).encG2⟩ product)
    (hacc : LeanAccepts (f1PointRenderCCN n) keccak256 cd)
    (hss : SoundSide (f1PointRenderCCN n) keccak256 cd)
    (hcs : CompleteSide (f1PointRenderCCN n) keccak256 cd)
    (hdec : ∃ ms instW inst Snap,
      decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
          (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1 cd = some (ms, instW) ∧
      Midfall.Lowering.instOfWords? (p := blsR) instW = some inst ∧
      snapshotOf (f1PointRenderCCN n).E keccak256 (f1PointRenderCCN n).vk inst ms none = .ok Snap) :
    GateAtV3 (f1PointRenderCCN n) product cd :=
  ⟨W, Lyt, vkAddr, st₀, hdep, hentry, hpc, f1PointRenderCCN_codec_lawsV3 n, hacc, hss, hcs, hdec⟩

/-! ## 2c. The tracked fixture at `f1PointRenderCCN n`

  The decode succeeds at the F1 plan and the computable codec; the `prepareMsgs`/`snapshotOf`
  checks are the fixture's own. `LeanAccepts` itself is NOT available: the tracked proof is for
  `NativeReplay.vkF1` (the test-SRS key), while the render's key is `f1VkResourced` (the payload's
  production commitments). `f1FixtureVk_differs` records the exact differing fields, and
  `f1PointRenderCCN_not_leanAccepts_testExponent` makes the failure a computation at the test-SRS
  parameter point: even with the bundle's own trapdoor, `verifyMsgs` at the render's key is not
  `.ok ()`. -/

/-- **THE TRACKED CALLDATA DECODES AT THE F1 RENDER.** The two non-verification conjuncts of
    `LeanAccepts` hold with explicit witnesses (the decoded message list and the parsed instance
    column). The final `verifyMsgs` conjunct is the one the key mismatch blocks. -/
theorem f1PointRenderCCN_decodes_fixture (n : Nat) :
    ∃ ms instW inst,
      Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
          (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
          Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = some (ms, instW) ∧
      Midfall.LoweringV2.instOfWords? (p := blsR) instW = some inst := by
  have hcheck : (match f1FixtureDecoded with
      | some p => (Midfall.LoweringV2.instOfWords? (p := blsR) p.2).isSome
      | none => false) = true := by native_decide
  rw [← show Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
      (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = f1FixtureDecoded from rfl] at hcheck
  cases h : Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
      (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata with
  | none => simp [h] at hcheck
  | some p =>
      obtain ⟨ms, instW⟩ := p
      cases hi : Midfall.LoweringV2.instOfWords? (p := blsR) instW with
      | none => simp [h, hi] at hcheck
      | some inst => exact ⟨ms, instW, inst, rfl, hi⟩

/-- **`SoundSide` AT THE F1 RENDER, FROM THE FIXTURE.** The tracked decode's `prepareMsgs` does
    not panic; the universal follows because the decode is deterministic. -/
theorem f1PointRenderCCN_soundSide (n : Nat) :
    SoundSide (f1PointRenderCCN n) keccak256
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata := by
  intro ms instW inst hdec hinst
  have hcheck := f1FixtureSoundCheck_eq
  unfold f1FixtureSoundCheck at hcheck
  rw [← show Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
      (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = f1FixtureDecoded from rfl,
    hdec] at hcheck
  dsimp only at hcheck
  cases hi : Midfall.LoweringV2.instOfWords? (p := blsR) instW with
  | none => rw [hi] at hinst; cases hinst
  | some inst' =>
      have hinst' : inst' = inst := Option.some.inj (by rw [hi] at hinst; exact hinst)
      subst inst'
      simp only [hi] at hcheck
      change prepareMsgs (Gₜ := G₁z) Midfall.Instances.NativeReplay.envReal keccak256
        Features.solidity f1VkResourced inst ms ≠
        .error (Fault.panic "proofs/src/plonk/logup.rs:460")
      cases h : prepareMsgs (Gₜ := G₁z) Midfall.Instances.NativeReplay.envReal keccak256
          Features.solidity f1VkResourced inst ms with
      | ok u => simp
      | error e =>
          cases e with
          | error e => simp
          | panic msg => simp [h] at hcheck

/-- **`CompleteSide` AT THE F1 RENDER, FROM THE FIXTURE.** The fixture snapshot's two
    `ChallengesGood` fields hold; the universal follows by determinism of `snapshotOf`. -/
theorem f1PointRenderCCN_completeSide (n : Nat) :
    CompleteSide (f1PointRenderCCN n) keccak256
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata := by
  intro ms instW inst Snap hdec hinst hsnap
  have hcheck := f1FixtureCompleteCheck_eq
  unfold f1FixtureCompleteCheck at hcheck
  rw [← show Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
      (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = f1FixtureDecoded from rfl,
    hdec] at hcheck
  dsimp only at hcheck
  cases hi : Midfall.LoweringV2.instOfWords? (p := blsR) instW with
  | none => rw [hi] at hinst; cases hinst
  | some inst' =>
      have hinst' : inst' = inst := Option.some.inj (by rw [hi] at hinst; exact hinst)
      subst inst'
      simp only [hi] at hcheck
      have hsnap' : snapshotOf Midfall.Instances.NativeReplay.envReal keccak256 f1VkResourced
          inst ms none = Except.ok Snap := hsnap
      cases hs : snapshotOf Midfall.Instances.NativeReplay.envReal keccak256 f1VkResourced
          inst ms none with
      | error e => rw [hs] at hsnap'; cases hsnap'
      | ok S =>
          have hS : S = Snap := by
            rw [hs] at hsnap'
            exact Except.ok.inj hsnap'
          subst hS
          simp only [hs] at hcheck
          change ChallengesGood f1VkResourced S
          exact f1FixtureChallengesGood_of_b S hcheck

/-- **THE FIXTURE'S KEY IS NOT THE RENDER'S KEY.** The tracked proof is for
    `NativeReplay.vkF1`; `f1VkResourced` differs in the fixed commitments, the permutation
    commitments and the transcript representation. This is exactly where `LeanAccepts` stops. -/
theorem f1FixtureVkF1_isSome : Midfall.Instances.NativeReplay.vkF1.isSome = true := by
  native_decide

theorem f1FixtureVk_differs :
    f1VkResourced.fixedCommitments ≠
        (Midfall.Instances.NativeReplay.vkF1.getD f1VkResourced).fixedCommitments ∧
      f1VkResourced.permutation.commitments ≠
        (Midfall.Instances.NativeReplay.vkF1.getD f1VkResourced).permutation.commitments ∧
      f1VkResourced.transcriptRepr ≠
        (Midfall.Instances.NativeReplay.vkF1.getD f1VkResourced).transcriptRepr := by
  native_decide

/-- The F1 render's VK runtime bytes are the tracked `poseidonPlanV2` bytes (4,577 of them);
    this is the field `DeploymentV2.vkCode` reads. -/
theorem f1PointRenderCCN_vkRuntimeBytes (n : Nat) :
    (f1PointRenderCCN n).plan.vk.runtimeBytes = poseidonPlanV2.vk.runtimeBytes := by
  show genFilledOut.plan.vk.runtimeBytes = poseidonPlanV2.vk.runtimeBytes
  native_decide

/-- The F1 render's `TRANSCRIPT_MPTR` constant is the same `0x1000`; this is the field
    `EntryFrameV3.fmp` reads. -/
theorem f1PointRenderCCN_transcriptMptr (n : Nat) :
    (f1PointRenderCCN n).consts.lookup "TRANSCRIPT_MPTR" = some 4096 := by
  show (constTableOf genFilledOut.model).lookup "TRANSCRIPT_MPTR" = some 4096
  native_decide

/-- **`DeploymentV2` AT THE F1 RENDER.** The world is `VacuityWitnesses.f1W`; the VK runtime bytes
    at the render's plan are the same 4,577 bytes as `poseidonPlanV2` (computed), so the `vkCode`
    field transfers and the other fields are the world's. -/
theorem f1PointRenderCCN_deploymentV2 (n : Nat) :
    Midfall.LoweringV2.DeploymentV2 (f1PointRenderCCN n)
      Midfall.Instances.VacuityWitnesses.f1W keccak256
      Midfall.Instances.VacuityWitnesses.f1VkAddr := by
  have hrt := f1PointRenderCCN_vkRuntimeBytes n
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · refine ⟨?_, rfl⟩
    intro a
    simp only [Midfall.Instances.VacuityWitnesses.f1W, YulSemantics.EVM.projectedCodeHash]
    by_cases h : a = Midfall.Instances.VacuityWitnesses.f1VkAddr
    · subst h
      by_cases hc : Midfall.Instances.VacuityWitnesses.f1VkRuntime.length = 0 <;> simp [hc]
    · simp [h]
  · show Midfall.Instances.VacuityWitnesses.f1W.extCodeOf
        Midfall.Instances.VacuityWitnesses.f1VkAddr =
      (f1PointRenderCCN n).plan.vk.runtimeBytes.data.toList
    rw [hrt]
    simp [Midfall.Instances.VacuityWitnesses.f1W,
      Midfall.Instances.VacuityWitnesses.f1VkRuntime]
  · rw [hrt]; decide
  · decide

/-- **`EntryFrameV3` AT THE F1 RENDER** at the bare `verifyProof` selector, the same frame
    `VacuityWitnesses.f1_entryFrameV3` occupies at `poseidonRender`. -/
theorem f1PointRenderCCN_entryFrameV3 (n : Nat) :
    ∃ st, Midfall.LoweringV3.EntryFrameV3 (f1PointRenderCCN n)
      Midfall.Instances.VacuityWitnesses.f1W Midfall.Instances.VacuityWitnesses.f1Lyt
      keccak256 fnSigVerifyProof st := by
  apply Midfall.LoweringV3.entryFrame_inhabitedV3
  · rfl
  · rfl
  · exact ⟨4096, f1PointRenderCCN_transcriptMptr n, by decide⟩
  · decide

/-- **`EntryFrameV3` AT THE F1 RENDER AT THE TRACKED CALLDATA** - the frame the gate's `cd`
    actually uses. -/
theorem f1PointRenderCCN_entryFrameV3_fixture (n : Nat) :
    ∃ st, Midfall.LoweringV3.EntryFrameV3 (f1PointRenderCCN n)
      Midfall.Instances.VacuityWitnesses.f1W Midfall.Instances.VacuityWitnesses.f1Lyt
      keccak256 Midfall.Instances.GeneratorDone.poseidonFixtureCalldata st := by
  apply Midfall.LoweringV3.entryFrame_inhabitedV3
  · exact Midfall.Instances.GeneratorDone.poseidonFixtureCalldata_selector
  · rfl
  · exact ⟨4096, f1PointRenderCCN_transcriptMptr n, by decide⟩
  · have h := Midfall.Instances.GeneratorDone.poseidonFixtureCalldata_size
    omega

/-- **THE TRACKED CALLDATA DECODES AND SNAPSHOTS AT THE F1 RENDER.** This is the
    `decodeCalldata`/`instOfWords?`/`snapshotOf` part of `GateAtV3`'s final conjunct, with
    explicit witnesses. Only `LeanAccepts` (the `verifyMsgs` check) is not available. -/
theorem f1PointRenderCCN_decodes_snapshot (n : Nat) :
    ∃ (ms : List (Msg (Fr blsR) G₁z)) (instW : Array Word256)
      (inst : Array (Fr blsR)) (Snap : Snapshot blsR G₁z G2fold G₁z),
      Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
          (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
          Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = some (ms, instW) ∧
      Midfall.LoweringV2.instOfWords? (p := blsR) instW = some inst ∧
      snapshotOf (f1PointRenderCCN n).E keccak256 (f1PointRenderCCN n).vk inst ms none =
        Except.ok Snap := by
  have hcheck := f1FixtureSnapshotCheck_eq
  unfold f1FixtureSnapshotCheck at hcheck
  rw [← show Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
      (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata = f1FixtureDecoded from rfl] at hcheck
  cases h : Midfall.Lowering.decodeCalldata (p := blsR) (f1PointRenderCCN n).plan.proofLayout
      (f1PointRenderCCN n).cfg.numInstances (f1PointRenderCCN n).E.g1
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata with
  | none => simp [h] at hcheck
  | some p =>
      obtain ⟨ms, instW⟩ := p
      cases hi : Midfall.LoweringV2.instOfWords? (p := blsR) instW with
      | none => simp [h, hi] at hcheck
      | some inst =>
          simp only [h, hi] at hcheck
          cases hs : snapshotOf Midfall.Instances.NativeReplay.envReal keccak256 f1VkResourced
              inst ms none with
          | error e => simp [hs] at hcheck
          | ok S => exact ⟨ms, instW, inst, S, rfl, hi, hs⟩

/-- **THE GATE AT THE F1 RENDER FROM THE TRACKED FIXTURE, WITH THE TWO REMAINING INPUTS.**
    `DeploymentV2`, `EntryFrameV3`, the codec law, `SoundSide` and `CompleteSide` are proved;
    the final conjunct's decode/snapshot half is `f1PointRenderCCN_decodes_snapshot`. What is
    left is `Eip2537.Holds` and `LeanAccepts` - and the latter cannot be supplied by this
    fixture because its key is `NativeReplay.vkF1`, not `f1VkResourced` (`f1FixtureVk_differs`);
    at the test-SRS exponent the tracked calldata is in fact REJECTED at the render's key
    (`f1PointRenderCCN_not_leanAccepts_testExponent`). -/
theorem f1PointRenderCCN_gateAtV3_of_fixture
    (n : Nat) (product : PairingProduct)
    (hpc : Eip2537.Holds (f1PointRenderCCN n).E.g1 ⟨(f1PointRenderCCN n).encG2⟩ product)
    (hacc : LeanAccepts (f1PointRenderCCN n) keccak256
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata) :
    GateAtV3 (f1PointRenderCCN n) product
      Midfall.Instances.GeneratorDone.poseidonFixtureCalldata := by
  obtain ⟨st₀, hentry⟩ := f1PointRenderCCN_entryFrameV3_fixture n
  obtain ⟨ms, instW, inst, Snap, hdec, hinst, hsnap⟩ := f1PointRenderCCN_decodes_snapshot n
  exact f1PointRenderCCN_gateAtV3_of n product
    Midfall.Instances.GeneratorDone.poseidonFixtureCalldata
    Midfall.Instances.VacuityWitnesses.f1W Midfall.Instances.VacuityWitnesses.f1Lyt
    Midfall.Instances.VacuityWitnesses.f1VkAddr st₀
    (f1PointRenderCCN_deploymentV2 n) hentry hpc hacc
    (f1PointRenderCCN_soundSide n) (f1PointRenderCCN_completeSide n)
    ⟨ms, instW, inst, Snap, hdec, hinst, hsnap⟩

/-! ## 3. THE `Done` / `ArtifactEq` RESIDUAL AT THIS RENDER.

  `ValidV3` at `f1PointRenderCN n` is NOT `Done`, for three independent reasons, two of which are
  machine-checked here:

  * **The codec law fails.** `f1PointRenderCN n`'s G1 codec is `g1CodecZ` (`f1EnvC.g1`), whose
    compressed half is the constant `none`; `f1_codec_headline_false` refutes the four headline
    laws at it, and `G1CodecLawsV3` extends those laws. So `GateAtV3` - hence `Done.gate` - is
    FALSE at this render for every product and every calldata, independent of the data:
    `f1PointRenderCN_gate_false`.
  * **The render is not the artifact render, and `Done` is stated only at the artifact render.**
    `Done`'s five fields are all at `poseidonRender : Render blsR G₁z G2fold blsGT`, whereas
    `f1PointRenderCN n : Render blsR G₁z G2fold G₁z` - a DIFFERENT carrier for `Gₜ` and a
    re-sourced key/params/`sG2gen`. It cannot be substituted for `poseidonRender` even
    syntactically, and its model is the generator's (`genFilledOut.model`), not the artifact
    render's `poseidonM`.
  * **`TotalV3` is open.** `Done.total` is the TOT.1 obligation at every product; it is a named
    open leaf of the root, not a fact this render supplies.

  What remains for a positive `Done`, in order: (i) a codec with `G1CodecLawsV3` at the render
  (`g1CodecC_laws` proves the computable codec's laws from a width fact - the codec is a `Render`
  field, so this is a data choice, not a clause change); (ii) a `Done` STATEMENT at the re-sourced
  render or OBJ.8 step 3/4 executed on `poseidonRender` itself; (iii) TOT.1; (iv) an
  `ArtifactEq` measurement at whichever render `Done` names; (v) the `hpay` data witness from the
  tracked SRS. None of these is a weakening, and none is added as a hypothesis to `ValidV3`. -/

/-- **THE GATE CANNOT HOLD AT THIS RENDER.** Its `G1CodecLawsV3` conjunct is false at
    `g1CodecZ`. Machine-checked, so `Done` at this render is refuted independently of the data. -/
theorem f1PointRenderCN_codec_not_lawsV3 (n : Nat) :
    ¬ Midfall.LoweringV3.G1CodecLawsV3 (f1PointRenderCN n).E.g1 := by
  intro h
  exact Midfall.Instances.VacuityWitnesses.f1_codec_headline_false h.headline

/-- `GateAtV3` is uninhabited at `f1PointRenderCN n`: every product, every calldata. -/
theorem f1PointRenderCN_gate_false (n : Nat) (product : PairingProduct) (cd : Bytes) :
    ¬ GateAtV3 (f1PointRenderCN n) product cd := by
  rintro ⟨W, Lyt, vkAddr, st₀, _hdep, _hentry, _hpc, hcodec, _hacc, _hss, _hcs, _hdec⟩
  exact f1PointRenderCN_codec_not_lawsV3 n hcodec

end

end Midfall.Instances.ValidV3F1Real

/-! ## Axiom audit -/

#print axioms Midfall.Instances.ValidV3F1Real.f1ResRun_isOk
#print axioms Midfall.Instances.ValidV3F1Real.f1ResRun_eq_ok
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_generated
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_program
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_env
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_supported
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3ExceptPayload
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3_iff
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_codec_not_lawsV3
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_validV3ExceptPayload
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_validV3
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_decodes_snapshot
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_gateAtV3_of_fixture
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_decodes_fixture
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_soundSide
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_completeSide
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_deploymentV2
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_entryFrameV3
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_entryFrameV3_fixture
#print axioms Midfall.Instances.ValidV3F1Real.f1VkResourced_fixed_eq_production
#print axioms Midfall.Instances.ValidV3F1Real.f1VkResourced_perm_eq_production
#print axioms Midfall.Instances.ValidV3F1Real.f1VkResourced_transcript_eq_production
#print axioms Midfall.Instances.ValidV3F1Real.f1VkResourced_csDegree_eq_production
#print axioms Midfall.Instances.ValidV3F1Real.f1FixtureVk_csDegree_agrees
#print axioms Midfall.Instances.ValidV3F1Real.f1ParamsC_testExponent_eq
#print axioms Midfall.Instances.ValidV3F1Real.f1FixtureVerifyAtTestExponentCheck_eq_false
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_not_leanAccepts_testExponent
#print axioms Midfall.Instances.ValidV3F1Real.f1FixtureVk_differs
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCCN_gateAtV3_of
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_gate_false

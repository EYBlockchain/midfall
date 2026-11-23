/-
  Midfall.Generator.Certified  (CERT.0, rebased onto the current tree)

  THE CERTIFIED-GENERATOR STATEMENT: one theorem whose only hypotheses are on the generator's
  INPUT. For every input in a decidable supported class, if the generator returns an output, the
  render that output determines satisfies the CURRENT `Midfall.LoweringV3.ValidV3`, and therefore
  (through the real `lowering_correct`) the program in it is correct.

  REBASE. The scratch `docs/plans/V3-evidence/lean/object/GeneratorCertified.lean` imported the
  evidence-area `ObjectV3Full.lean`; ST.6/RECON.1 moved that vocabulary into the tree
  (`Midfall/LoweringV2/Statements.lean`, `Midfall/LoweringV2/Generated.lean`,
  `Midfall/Generator/PlanNew.lean`, `Midfall/Lowering/YulParse.lean`). This file imports the tree
  and changes only qualifiers:

  * `noShadow` -> `noShadowProg` (the tree's name for the identical every-binder scan);
  * the scratch's local object-text `Render.ValidV3` -> the ONE current
    `Midfall.LoweringV3.ValidV3`;
  * `SupportedInput.wfV3` is GONE: `SupportedV3`/`WellFormedV3` were deleted by RECON.1 step 4.
    The repaired permutation clause it carried is the OUTPUT obligation
    `permCommMatchRepaired`, one of the eight D-CERT1 additions below; nothing was weakened.

  D-CERT1 (signed 2026-11-22, `docs/design.md`). The current `programOk` bundle has fourteen
  decidable conjuncts plus three scans and `programFits`. The scratch's 33 lemmas cover nine of the
  fourteen (`codegenStruct`, `codegenAgrees`, `constsCoherent`, `callsResolved`, `noShadowProg`,
  `noShadowCore`, `mainClosed`, the transcript floor, `cdBoundB`), the three program clauses
  `ExitDiscipline`, `NoWriters` and the scope/env/payload clauses. The eight uncovered conjuncts
  are named CERT obligations here (`prog_hasMultiPointSet`, `prog_transcriptRegionOk`,
  `prog_g1IdentityFloor`, `prog_negLagrangesFloor`, `prog_permCommMatchRepaired`,
  `prog_gasCallOk`, `prog_gasFree`, `prog_programFits`), with D3/D4 owners. They are OUTPUT-side
  lemmas exactly like the 33, and they are NOT in the cone of `lowering_correct`: this file imports
  the root, the root does not import this file.

  Sections
   1. input (`GenInput`), the whole generator (`generate`), `renderOf`
   2. `SupportedInput`, input-only
   3. the 33 scratch lemma statements + the eight D-CERT1 obligations
   4. `generator_certified`, PROVED from section 3 against the current `ValidV3`
   5. `generator_correct` (hypothetical root) and `generator_correct_V3` (real root)
-/
import Midfall.LoweringV3.GeneratorTheorem
import Midfall.Generator.Vk
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldCompute
import Midfall.LoweringV2.Consts
import Midfall.Lowering.VkDigest
import Midfall.LoweringV3.LagrangeAlg
set_option autoImplicit false

namespace Midfall.Generator.Certified

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Generator.PlanNew
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientEvaluator

/-! ## 1. Input, generator, render -/

/-- EVERYTHING the certified generator reads. The first two fields are the Lean verifier's
    environment (the theorem compares the program against the Lean verifier run in it); the rest
    are what `SolidityGenerator` reads: the key, the prover SRS (`vk.rs` reads `g_lagrange`, `g2`,
    `s_g2`), the point encoders, the configuration, the render flags, and the two BUILD_ID /
    literal strings no key determines (`features`: `env!("SOLIDITY_VERIFIER_FEATURES")`, ART:125;
    `frDelta`: `fr_delta_literal()`, QVM:4131, a curve constant in Rust). -/
structure GenInput (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where
  E : VerifierEnv p G₁ G₂ Gₜ
  encG2 : G₂ → Bytes
  vk : VerifyingKey (Fr p) G₁
  srs : ParamsKZG G₁ G₂
  codecs : VkPointCodecs G₁ G₂
  cfg : GeneratorConfig
  flags : RenderFlags
  features : String
  frDelta : String

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
  [DecidableEq G₂]

/-- The four callbacks `generate_vk` reaches through `&self` (Vk.lean:405), filled with the
    PlanNew ports: `compact_quotient_program_for` is QRS:166-180 (plan, then
    `build_quotient_program_items` = the limb-op build at `DEFAULT_QUOTIENT_LIMB_VM_OPS`,
    QRS:2102-2111). -/
def vkBuildEnvOf (field : FieldCtx (Fr p)) (cs : ConstraintSystem (Fr p)) :
    VkBuildEnv QuotientProgramPlan :=
  { newVerifierMemoryLayout := VerifierMemoryLayout.new
    compactQuotientProgramFor := fun m d => do
      let pl ← quotientProgramPlan field cs m d
      let b ← buildQuotientProgramItemsWithLimbOps pl.items pl.selectorFold
        defaultQuotientLimbVmOps
      pure { bytes := b.bytes, consts := b.consts }
    quotientProgramPlan := fun m d => quotientProgramPlan field cs m d
    buildQuotientProgramItems := fun pl => do
      let b ← buildQuotientProgramItemsWithLimbOps pl.items pl.selectorFold
        defaultQuotientLimbVmOps
      pure { bytes := b.bytes, consts := b.consts } }

/-- `VerifierBuildInputs` (MOD:37-45) of one input, given the raw meta. -/
def buildInputsOf (gi : GenInput p G₁ G₂ Gₜ) (m0 : ConstraintSystemMeta) :
    VerifierBuildInputs p G₁ G₂ :=
  { params := gi.srs, vk := gi.vk, numInstances := gi.cfg.numInstances
    numCommittedInstances := gi.cfg.numCommittedInstances
    accEncoding := gi.cfg.accumulator, meta_ := m0 }

/-- The render-side build inputs: every field a function of the input and the SRS fingerprint. -/
def artifactInputsOf (gi : GenInput p G₁ G₂ Gₜ) (fp : Word256) : ArtifactBuildInputs :=
  { numInstances := gi.cfg.numInstances, k := gi.vk.domain.k
    accEncoding := gi.cfg.accumulator, srsFingerprint := fp, features := gi.features
    truncatedChallenges := Features.solidity.truncatedChallenges, frDelta := gi.frDelta }

/-- What one run returns: the SRS fingerprint (for BUILD_ID) and `generateAll`'s output. The
    payload is `out.plan.vk` (`plan_vk_of_generateAll`). -/
structure CertOut where
  fingerprint : Word256
  out : GenOut

/-- **THE WHOLE GENERATOR.** `generate_vk` (Vk.lean:1093) produces the payload from the key and
    the SRS; `generateAll` (Generated.lean) takes it from there. The payload is NOT an input:
    with the payload as input `PayloadAgrees` is false for some succeeding run. -/
def generate (gi : GenInput p G₁ G₂ Gₜ) : Except Fault CertOut := do
  let field := frFieldCtx gi.E.delta
  let m0 ← ConstraintSystemMeta.new Features.solidity gi.vk.cs gi.cfg.numCommittedInstances
  let payload ← generateVk Features.solidity (vkBuildEnvOf field gi.vk.cs) gi.codecs
    (buildInputsOf gi m0)
  let fp ← srsFingerprint gi.codecs (buildInputsOf gi m0)
  let out ← generateAll Features.solidity gi.E.delta gi.vk gi.cfg payload
    (artifactInputsOf gi fp) gi.flags
  pure { fingerprint := fp, out := out }

/-- "The generator succeeded on this input with this output." -/
def Generates (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) : Prop := generate gi = .ok o

/-- **THE RENDER A RUN DETERMINES.** No field is free once `gi` is fixed: `o` is determined by
    `gi` through `Generates`, the verifier parameters are `verifier_params` of the SRS
    (`ParamsVerifierKZG.ofParams`, params.rs:313-321), `sG2gen` is the SRS's `s_g2`. -/
def renderOf (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) : Render p G₁ G₂ Gₜ :=
  { E := gi.E, params := ParamsVerifierKZG.ofParams gi.srs.g2 gi.srs.sG2, vk := gi.vk
    sG2gen := gi.srs.sG2, encG2 := gi.encG2, cfg := gi.cfg
    inputs := artifactInputsOf gi o.fingerprint, flags := gi.flags
    plan := o.out.plan, qblocks := o.out.qblocks, model := o.out.model }

theorem cert_except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The do-block of `generate`, unfolded. PROVED. -/
theorem generate_spec {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut} (h : Generates gi o) :
    ∃ m0 payload,
      ConstraintSystemMeta.new Features.solidity gi.vk.cs gi.cfg.numCommittedInstances = .ok m0 ∧
      generateVk Features.solidity (vkBuildEnvOf (frFieldCtx gi.E.delta) gi.vk.cs) gi.codecs
        (buildInputsOf gi m0) = .ok payload ∧
      srsFingerprint gi.codecs (buildInputsOf gi m0) = .ok o.fingerprint ∧
      generateAll Features.solidity gi.E.delta gi.vk gi.cfg payload
        (artifactInputsOf gi o.fingerprint) gi.flags = .ok o.out := by
  unfold Generates generate at h
  obtain ⟨m0, h1, h⟩ := cert_except_bind_ok h
  obtain ⟨payload, h2, h⟩ := cert_except_bind_ok h
  obtain ⟨fp, h3, h⟩ := cert_except_bind_ok h
  obtain ⟨out, h4, h⟩ := cert_except_bind_ok h
  cases h
  exact ⟨m0, payload, h1, h2, h3, h4⟩

/-! ## 2. The supported class, input-only -/

/-- **THE SUPPORTED CLASS.** Every clause mentions only the input. Clauses 1-11 are
    `SupportedV2` (Statements.lean) verbatim with `R.` read as `gi.`, minus `layout`, which
    mentions the plan and follows from generation (`supported_layout`). The scratch's `wfV3`
    field is GONE because RECON.1 step 4 deleted `SupportedV3`/`WellFormedV3`; the repaired
    permutation clause it carried became the OUTPUT obligation `prog_permCommMatchRepaired`
    (D-CERT1). Then the input-only half of `EnvAgrees` (Inv.lean:533-579), the codec agreement
    between the generator's encoders and the Lean verifier's, and the delta literal. -/
structure SupportedInput (gi : GenInput p G₁ G₂ Gₜ) : Prop where
  advice : gi.vk.cs.numAdviceColumns ≠ 0
  instShape : gi.vk.cs.numInstanceColumns = 2 ∧ gi.cfg.numCommittedInstances = 1
  noRotInst : ∀ q ∈ gi.vk.cs.instanceQueries.toList, q.2.int = 0
  singlePhase : gi.vk.cs.numChallenges = 0
  hLimbs : gi.vk.domain.getQuotientPolyDegree = gi.vk.csDegree - 1
  vkPoints : ∀ C ∈ gi.vk.fixedCommitments.toList ++ gi.vk.permutation.commitments.toList,
    Midfall.LoweringV2.ptReadable (gi.E.g1.toEip C)
  production : gi.flags.trace = false ∧ gi.flags.gasCheckpoints = false
  wf : gi.vk.WellFormed Features.solidity
  noAcc : gi.cfg.accumulator = none
  embeddedQuotient : gi.flags.externalQuotient = false ∧ gi.flags.expectedQuotient = none
  separateVk : gi.flags.separate = true
  /-- `EnvAgrees.modulus`. -/
  modulus : p = frModulusConstant
  /-- `EnvAgrees.truncWidth`. -/
  truncWidth : Midfall.Halo2.divCeil (Midfall.Halo2.divCeil gi.E.field.numBits 8) 2 = 16
  /-- `EnvAgrees.domainN`, first half (the second is `env_k`). -/
  domainN : gi.vk.domain.n = 2 ^ gi.vk.domain.k
  baryWeight : gi.vk.domain.barycentricWeight = ((2 ^ gi.vk.domain.k : ℕ) : Fr p)⁻¹
  omegaInvMul : gi.vk.domain.omegaInv * gi.vk.domain.omega = 1
  omegaOrder : orderExactly gi.vk.domain.omega gi.vk.domain.n
  /-- CODEC LAW (G1): the generator's encoder (`g1ToU256s ∘ codecs.g1Repr`, ENC:835-859) and the
      Lean verifier's `E.g1.toEip` agree on every point. -/
  g1Codec : ∀ Q : G₁, ∃ ws : List Word256, g1ToU256s (gi.codecs.g1Repr Q) = .ok ws ∧
    ws.length = 4 ∧
    ws.foldl (init := Bytes.empty) (fun acc w => ByteArray.append acc (wordToBytesBE w)) =
      gi.E.g1.toEip Q
  /-- CODEC LAW (G2): likewise for `g2ToU256s ∘ codecs.g2Repr` (ENC:867-901) and `encG2`. -/
  g2Codec : ∀ Q : G₂, ∃ ws : List Word256, g2ToU256s (gi.codecs.g2Repr Q) = .ok ws ∧
    ws.length = 8 ∧
    ws.foldl (init := Bytes.empty) (fun acc w => ByteArray.append acc (wordToBytesBE w)) =
      gi.encG2 Q
  /-- `LoweringV3.PayloadAgrees.delta` (StatementsV3.lean:427): the literal string is the
      verifier's delta. Input-only (both sides are inputs). -/
  deltaLiteral : gi.E.delta.val = Inline.natOfLiteral gi.frDelta
  /-- SIZE BOUND: Rust computes these in `usize` (64 bits) and the header words as
      `U256::from(usize)` (vk.rs:110-111); the port computes in `Nat` and writes
      `BitVec.ofNat 256`, which wraps. Without it `payload_header`'s `numInstances` conjunct is
      false for `numInstances ≥ 2^256`. -/
  sizeBound : gi.cfg.numInstances < 2 ^ 64 ∧ gi.vk.domain.k < 64

/-! ## 3. One lemma per output-side clause. Every `sorry` below is the body of the named
    theorem. The first 33 are the scratch's; the last eight are D-CERT1's additions for the
    current `programOk` bundle. -/

section Clauses
variable {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}

/-! ### G: generated -/

/-- `newFromVk` stores the payload it is given (`LoweringPlan.mk vk …`), and `generateAll`
    returns that plan. -/
theorem plan_vk_of_generateAll {delta : Fr p} {vk : VerifyingKey (Fr p) G₁} {cfg : GeneratorConfig}
    {payload : Halo2VerifyingKey} {inputs : ArtifactBuildInputs} {flags : RenderFlags}
    {out : GenOut}
    (h : generateAll Features.solidity delta vk cfg payload inputs flags = .ok out) :
    out.plan.vk = payload := by
  simp only [generateAll, Bind.bind, Except.bind] at h
  obtain ⟨_rawMeta, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨plan, hpl, h2⟩ := cert_except_bind_ok h1
  obtain ⟨_blocks, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨_model, _, h4⟩ := cert_except_bind_ok h3
  cases h5 : (Halo2Verifier.validateLayout _model) with
  | error e => simp only [h5] at h4; cases h4
  | ok u =>
      simp only [h5] at h4
      have hA : { plan := plan, qblocks := _blocks, model := _model } = out :=
        Except.ok.inj (show Except.ok { plan := plan, qblocks := _blocks, model := _model } =
          Except.ok out from h4)
      have hp : plan = out.plan := congrArg GenOut.plan hA
      have hv : plan.vk = payload := by
        simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at hpl
        obtain ⟨q, _, hq1⟩ := cert_except_bind_ok hpl
        obtain ⟨_proofLayout, _, hq2⟩ := cert_except_bind_ok hq1
        obtain ⟨_qplan, _, hq3⟩ := cert_except_bind_ok hq2
        obtain ⟨_build, _, hq4⟩ := cert_except_bind_ok hq3
        obtain ⟨_nw, _, hq5⟩ := cert_except_bind_ok hq4
        obtain ⟨_pcs, _, hq6⟩ := cert_except_bind_ok hq5
        obtain ⟨_acc, _, hq7⟩ := cert_except_bind_ok hq6
        obtain ⟨_memory, _, hq8⟩ := cert_except_bind_ok hq7
        obtain ⟨_op, _, hq9⟩ := cert_except_bind_ok hq8
        obtain ⟨_trip, _, hq10⟩ := cert_except_bind_ok hq9
        split at hq10 <;> (try (split at hq10)) <;> (try (split at hq10)) <;>
          (try (split at hq10)) <;> (try (split at hq10)) <;> (try (split at hq10))
        all_goals (try (cases hq10))
        all_goals rfl
      rw [← hp]
      exact hv

/-- The generated-by clause, PROVED from `generate_spec` and `plan_vk_of_generateAll`. -/
theorem generated_of {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut} (hg : Generates gi o) :
    Midfall.LoweringV3.GeneratedBy (renderOf gi o) := by
  obtain ⟨_, payload, _, _, _, h4⟩ := generate_spec hg
  have hv : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  refine ⟨o.out, ?_, rfl, rfl, rfl⟩
  show generateAll Features.solidity gi.E.delta gi.vk gi.cfg o.out.plan.vk
    (artifactInputsOf gi o.fingerprint) gi.flags = .ok o.out
  rw [hv]; exact h4

/-! ### P: the program clause, `programOk` - the 33 scratch lemmas -/

theorem prog_codegenStruct (hg : Generates gi o) (hs : SupportedInput gi) :
    codegenStruct (mainAsmRaw (renderOf gi o).pv (renderOf gi o).model) (renderOf gi o).model
      = true := by
  sorry -- CERT.2

/-- A VM plan has `direct := none`. PROVED from the `newFromVk` peel. -/
theorem newFromVk_direct_none {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding)
    (payload : Halo2VerifyingKey) (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk feat field cs rawMeta numInstances accEncoding
        payload = .ok plan) : plan.direct = none := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨_q, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨_proofLayout, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨_qplan, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨_build, _, h4⟩ := cert_except_bind_ok h3
  obtain ⟨_nw, _, h5⟩ := cert_except_bind_ok h4
  obtain ⟨_pcs, _, h6⟩ := cert_except_bind_ok h5
  obtain ⟨_acc, _, h7⟩ := cert_except_bind_ok h6
  obtain ⟨_memory, _, h8⟩ := cert_except_bind_ok h7
  obtain ⟨_op, _, h9⟩ := cert_except_bind_ok h8
  obtain ⟨_trip, _, h10⟩ := cert_except_bind_ok h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals rfl

/-- The compact rendering arm's `intoTemplateParts` fourth component is `none`. PROVED. -/
theorem quotientRendering_direct_none {L : LoweringPlan Unit Unit} {trace : Bool}
    {compactBlocks : LoweringPlan Unit Unit → Bool →
      Midfall.Generator.QuotientFold.QuotientComputationBlocks}
    {rendering : Midfall.Generator.QuotientRendering}
    (h : LoweringPlan.quotientRendering compactBlocks L trace false = .ok rendering)
    (hd : L.direct = none) : (rendering.intoTemplateParts).2.2.2 = none := by
  unfold LoweringPlan.quotientRendering at h
  simp only [Bool.false_eq_true, if_false, hd] at h
  cases hv : L.vmQuotient with
  | error e => simp only [hv] at h; cases h
  | ok q => simp only [hv] at h; cases h; rfl

/-- `generateVerifierFromPlan` copies the rendering's `quotientDirect` (ART:320), so a VM plan
    with no direct quotient section renders none. PROVED. -/
theorem model_quotientDirect_none {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) (hext : R.flags.externalQuotient = false)
    (hd : R.plan.direct = none) : R.model.quotientDirect.isNone = true := by
  have hg := Midfall.LoweringV3.MemoryPairs.gvfp_of_generated h
  simp only [generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  · cases hg
  · cases hg
  · obtain ⟨_a1, _, h1⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp hg
    obtain ⟨rendering, hrend, h2⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h1
    obtain ⟨_a3, _, h3⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h2
    obtain ⟨_a4, _, h4⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h3
    obtain ⟨_a5, _, h5⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h4
    obtain ⟨_a6, _, h6⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h5
    obtain ⟨_a7, _, h7⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h6
    have hrec := Except.ok.inj h7
    rw [hext] at hrend
    have hlow : (rendering.intoTemplateParts).2.2.2 = none :=
      quotientRendering_direct_none hrend hd
    have hdir := congrArg (fun x => x.quotientDirect) hrec
    rw [← hdir, hlow]
    rfl

/-- P2a. A VM-lowered plan renders no Direct section. -/
theorem prog_noDirect (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).model.quotientDirect.isNone = true := by
  obtain ⟨_rawMeta, plan, _hraw, hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  have hdPlan : plan.direct = none :=
    newFromVk_direct_none Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs _rawMeta
      gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  have hd : (renderOf gi o).plan.direct = none := by rw [hp]; exact hdPlan
  exact model_quotientDirect_none (generated_of hg) hs.embeddedQuotient.1 hd

/-- P2b. Every `uint256 internal constant` line of `renderConstants` has a literal right side. -/
theorem prog_constLinesLiteral (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.constLinesLiteral (renderOf gi o).model = true := by
  sorry -- CERT.6 (disappears when Constants.sol is printed from the table, CERT.3)

/-- P2c. The table read back from the rendered text IS the data table of the plan view. -/
theorem prog_constTable (hg : Generates gi o) (hs : SupportedInput gi) :
    (Midfall.LoweringV2.constTableOf (renderOf gi o).model ==
      Midfall.LoweringV3.expectedConsts (renderOf gi o).pv (renderOf gi o).model) = true := by
  sorry -- CERT.6 (with CERT.3)

/-- The names of `expectedConsts`, independent of the option values. -/
def expectedConstsNames (vk quot acc : Bool) : List String :=
  (if vk then ["EXPECTED_VK_PAYLOAD_LENGTH",
      "EXPECTED_VK_LENGTH",
      "EXPECTED_VK_CODEHASH_WORD"] else []) ++
  (if quot then ["EXPECTED_QUOTIENT_LENGTH",
      "EXPECTED_QUOTIENT_CODEHASH_WORD"] else []) ++
  ["PROOF_LEN_CPTR",
      "PROOF_CPTR",
      "NUM_INSTANCE_CPTR",
      "INSTANCE_CPTR",
      "TRANSCRIPT_MPTR",
      "RETURN_MPTR",
      "VK_MPTR",
      "VK_DIGEST_MPTR",
      "NUM_INSTANCES_MPTR",
      "K_MPTR",
      "N_INV_MPTR",
      "OMEGA_MPTR",
      "OMEGA_INV_MPTR",
      "OMEGA_INV_TO_L_MPTR",
      "HAS_ACCUMULATOR_MPTR",
      "ACC_OFFSET_MPTR",
      "NUM_ACC_LIMBS_MPTR",
      "NUM_ACC_LIMB_BITS_MPTR",
      "G1_BASE_MPTR",
      "G2_BASE_MPTR",
      "NEG_S_G2_BASE_MPTR",
      "CHALLENGE_MPTR",
      "THETA_MPTR",
      "BETA_MPTR",
      "GAMMA_MPTR",
      "TRASH_CHALLENGE_MPTR",
      "Y_MPTR",
      "X_MPTR",
      "X1_MPTR",
      "X2_MPTR",
      "X3_MPTR",
      "X4_MPTR",
      "F_COM_MPTR",
      "PI_MPTR",
      "ACC_LHS_MPTR",
      "ACC_RHS_MPTR",
      "X_N_MPTR",
      "X_N_MINUS_1_INV_MPTR",
      "L_LAST_MPTR",
      "L_BLIND_MPTR",
      "L_0_MPTR",
      "INSTANCE_EVAL_MPTR",
      "QUOTIENT_EVAL_MPTR",
      "QUOTIENT_MPTR",
      "F_EVAL_MPTR",
      "V_MPTR",
      "FINAL_COM_MPTR",
      "PAIRING_LHS_MPTR",
      "PAIRING_RHS_MPTR",
      "ROT_POINTS_MPTR",
      "X1_POWERS_MPTR",
      "Q_COM_MPTR",
      "Q_EVAL_SET_MPTR",
      "Q_EVAL_CPTR_MPTR",
      "G1_IDENTITY_MPTR",
      "REVERSED_EVALS_MPTR",
      "SELECTOR_ACC_MPTR",
      "QUOTIENT_RETURN_MPTR",
      "BATCH_INV_SCRATCH_MPTR",
      "LAGRANGE_DENOMS_MPTR",
      "TRACE_U256_MPTR",
      "ADVICE_COMMS_MPTR_BASE",
      "LOOKUP_M_COMMS_MPTR_BASE",
      "PERM_Z_COMMS_MPTR_BASE",
      "LOOKUP_HELPER_COMMS_MPTR_BASE",
      "LOOKUP_Z_COMMS_MPTR_BASE",
      "TRASHCAN_COMMS_MPTR_BASE",
      "QUOTIENT_LIMB_COMMS_MPTR_BASE",
      "G1ADD_GAS",
      "G1MSM_GAS_1PAIR",
      "PAIRING_GAS_2PAIR",
      "MODEXP_GAS",
      "G1MSM_GAS_SMOKE"] ++
  (if acc then ["ACC_RHS_MSM_GAS"] else []) ++
  ["ERR_BAD_CALLDATA_SHAPE",
      "ERR_VK_MISMATCH",
      "ERR_NON_CANONICAL_SCALAR",
      "ERR_BAD_POINT_ENCODING",
      "ERR_PRECOMPILE_FAILED",
      "ERR_PROOF_REJECTED",
      "ERR_QUOTIENT_PROGRAM_INVALID",
      "ERR_MEMORY_LAYOUT_VIOLATED",
      "FR_MODULUS",
      "BLS_P_HI",
      "BLS_P_MINUS_ONE_LO",
      "BLS_P_MINUS_ONE_PACKED_0",
      "BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG",
      "BLS_P_MINUS_ONE_PACKED_1"]

/-- `expectedConsts`'s names are `expectedConstsNames` at the model's option flags. PROVED. -/
theorem expectedConsts_names_eq (pv : PlanView) (m : Model) :
    (Midfall.LoweringV3.expectedConsts pv m).map Prod.fst =
      expectedConstsNames m.expectedVkCodehash.isSome
        (m.quotientExternal.isSome && m.expectedQuotientCodehash.isSome)
        m.expectedHasAccumulator := by
  unfold Midfall.LoweringV3.expectedConsts expectedConstsNames
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;> rfl

/-- P2d. No constant name twice. -/
theorem prog_constNodup (hg : Generates gi o) (hs : SupportedInput gi) :
    decide (((Midfall.LoweringV3.expectedConsts (renderOf gi o).pv
      (renderOf gi o).model).map Prod.fst).Nodup) = true := by
  rw [expectedConsts_names_eq]
  cases h1 : (renderOf gi o).model.expectedVkCodehash <;>
    cases h2 : (renderOf gi o).model.quotientExternal <;>
    cases h3 : (renderOf gi o).model.expectedQuotientCodehash <;>
    cases h4 : (renderOf gi o).model.expectedHasAccumulator <;>
    simp only [Option.isSome_some, Option.isSome_none, Bool.and_true, Bool.and_false,
      Bool.true_and, Bool.false_and, if_true, if_false] <;>
    decide

/-- P2e. Every name the program reads is a declared constant (or a wrapper local). -/
theorem prog_constsDeclared (hg : Generates gi o) (hs : SupportedInput gi) :
    ((Midfall.LoweringV2.freeNames (abiGuardBlock (renderOf gi o).model ++
        mainAsmRaw (renderOf gi o).pv (renderOf gi o).model)).filter
        fun x => x != "vk" && x != "quotientEvaluator").all
      (fun x => ((Midfall.LoweringV3.expectedConsts (renderOf gi o).pv
        (renderOf gi o).model).map Prod.fst).contains x)
      = true := by
  sorry -- CERT.5

/-- P3. Every user call resolves to a top-level definition of the same arity. -/
theorem prog_callsResolved (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.callsResolved (mainAsmRaw (renderOf gi o).pv
      (renderOf gi o).model) = true := by
  sorry -- CERT.5

/-- P4. No binder is a constant name. -/
theorem prog_noShadow (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.noShadowProg (Midfall.LoweringV2.constTableOf (renderOf gi o).model)
      (abiGuardBlock (renderOf gi o).model ++ wrapperLocals (renderOf gi o).model 0 0 ++
        mainAsmRaw (renderOf gi o).pv (renderOf gi o).model) = true := by
  sorry -- CERT.5

/-- P5. After inlining only the two wrapper locals are free. -/
theorem prog_closed (hg : Generates gi o) (hs : SupportedInput gi) :
    (Midfall.LoweringV2.freeNames (Inline.inlineContractConstants
        (Midfall.LoweringV2.constTableOf (renderOf gi o).model)
        (abiGuardBlock (renderOf gi o).model ++
          mainAsmRaw (renderOf gi o).pv (renderOf gi o).model))).all
      (fun x => x == "vk" || x == "quotientEvaluator") = true := by
  sorry -- CERT.5

/-- P6. The transcript base is above Solidity's reserved words. -/
theorem prog_transcriptFloor (hg : Generates gi o) (hs : SupportedInput gi) :
    decide (0x80 ≤ (renderOf gi o).pv.memory.transcriptMptr) = true := by
  sorry -- CERT.4

/-! ### P: no writers -/

theorem prog_noWriters (hg : Generates gi o) (hs : SupportedInput gi) :
    NoWriters ((renderOf gi o).prog 0 0) := by
  sorry -- CERT.5

/-! ### K: environment (the plan-side half of `EnvAgrees`) -/

/-- `generateVerifierFromPlan` copies `inputs.k` into the model (ART:281). PROVED. -/
theorem model_k_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) : R.model.k = R.inputs.k := by
  have hg := Midfall.LoweringV3.MemoryPairs.gvfp_of_generated h
  simp only [generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  · cases hg
  · cases hg
  · obtain ⟨_a1, _, h1⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp hg
    obtain ⟨_a2, _, h2⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h1
    obtain ⟨_a3, _, h3⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h2
    obtain ⟨_a4, _, h4⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h3
    obtain ⟨_a5, _, h5⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h4
    obtain ⟨_a6, _, h6⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h5
    obtain ⟨_a7, _, h7⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h6
    have hrec := Except.ok.inj h7
    simpa using (congrArg (fun x => x.k) hrec).symm

theorem env_k (hg : Generates gi o) (hs : SupportedInput gi) :
    gi.vk.domain.k = (renderOf gi o).pv.k := by
  change gi.vk.domain.k = (renderOf gi o).model.k
  rw [model_k_of_generated (generated_of hg)]
  rfl

theorem env_negLagranges (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).pv.numNegLagranges = gi.vk.cs.blindingFactors.toOption.getD 0 + 1 := by
  sorry -- CERT.6

/-- The `vk.rs:180` check, from the small `generateBaseVkPrefix`. PROVED. -/
theorem generateBaseVkPrefix_g2 {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    (h : generateBaseVkPrefix inputs = .ok pre) :
    (inputs.params.g2 == P.g₂) = true := by
  simp only [generateBaseVkPrefix, Bind.bind, Except.bind] at h
  generalize h1 : feToU256 (bytesToNats (frToRepr inputs.vk.transcriptRepr)) = fe1 at h
  cases fe1 with
  | error e => cases h
  | ok v1 =>
    dsimp only at h
    generalize h2 : invert ((2 ^ inputs.vk.domain.k : ℕ) : Fr p) = o2 at h
    cases o2 with
    | none => cases h
    | some x2 =>
      dsimp only at h
      generalize h3 : feToU256 (bytesToNats (frToRepr x2)) = fe3 at h
      cases fe3 with
      | error e => cases h
      | ok v3 =>
        dsimp only at h
        generalize h4 : feToU256 (bytesToNats (frToRepr
          (EvaluationDomain.getOmega inputs.vk.domain))) = fe4 at h
        cases fe4 with
        | error e => cases h
        | ok v4 =>
          dsimp only at h
          generalize h5 : feToU256 (bytesToNats (frToRepr
            (EvaluationDomain.getOmegaInv inputs.vk.domain))) = fe5 at h
          cases fe5 with
          | error e => cases h
          | ok v5 =>
            dsimp only at h
            generalize h6 : feToU256 (bytesToNats (frToRepr
                (powVartime (EvaluationDomain.getOmegaInv inputs.vk.domain)
                  (Int.natAbs inputs.meta_.rotationLast)))) = fe6 at h
            cases fe6 with
            | error e => cases h
            | ok v6 =>
              dsimp only at h
              generalize hg1 : decideBool (P.decEqG₁
                (List.foldl (fun acc g => acc * g) 1 inputs.params.gLagrange) P.g₁) = b1 at h
              cases b1 with
              | false => cases h
              | true =>
                generalize hg2 : (inputs.params.g2 == P.g₂) = b2 at h
                cases b2 with
                | false => cases h
                | true => rfl

/-- `generateBaseVk` success gives the prefix success. PROVED. -/
theorem generateBaseVk_g2_check {codecs : VkPointCodecs G₁ G₂}
    {inputs : VerifierBuildInputs p G₁ G₂} {payload : Halo2VerifyingKey}
    (h : generateBaseVk codecs inputs = .ok payload) :
    (inputs.params.g2 == P.g₂) = true := by
  simp only [generateBaseVk, Bind.bind, Except.bind] at h
  generalize hp : generateBaseVkPrefix inputs = pre at h
  cases pre with
  | error e => cases h
  | ok p => exact generateBaseVkPrefix_g2 hp

theorem except_isOk_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β}
    (h : (x >>= f).isOk = true) : x.isOk = true := by
  cases x with
  | error e => change (Except.error e).isOk = true at h; cases h
  | ok a => rfl

def certGetOk {ε α : Type} : (e : Except ε α) → e.isOk = true → α
  | .ok a, _ => a
  | .error _, h => by change (Except.error _).isOk = true at h; cases h

theorem cert_eq_ok_getOk {ε α : Type} (e : Except ε α) (h : e.isOk = true) :
    e = .ok (certGetOk e h) := by
  cases e with
  | ok a => rfl
  | error _ => change (Except.error _).isOk = true at h; cases h

/-- `generateVk`'s first bind is `generateBaseVk`. PROVED. -/
theorem generateVk_base {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {codecs : VkPointCodecs G₁ G₂} {inputs : VerifierBuildInputs p G₁ G₂}
    {payload : Halo2VerifyingKey}
    (h : generateVk feat env codecs inputs = .ok payload) :
    ∃ vk0, generateBaseVk codecs inputs = .ok vk0 := by
  have his : (generateVk feat env codecs inputs).isOk = true := by rw [h]; rfl
  rw [generateVk] at his
  have hbase : (generateBaseVk codecs inputs).isOk = true := except_isOk_bind his
  exact ⟨certGetOk _ hbase, cert_eq_ok_getOk _ hbase⟩

theorem env_nG2 (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).params.nG2Prepared = P.g₂⁻¹ := by
  obtain ⟨_m0, _payload, _hraw, hgenvk, _hfp, _h4⟩ := generate_spec hg
  obtain ⟨_vk0, hbase⟩ := generateVk_base hgenvk
  have hg2c := generateBaseVk_g2_check hbase
  have hg2 : gi.srs.g2 = P.g₂ := beq_iff_eq.mp hg2c
  show gi.srs.g2⁻¹ = P.g₂⁻¹
  rw [hg2]

/-- D-CERT1 extension (D-GATE1's `PayloadAgrees.constantsLength`): the generated payload carries
    the eleven header constants the window reads. -/
theorem generateBaseVkHeader_length {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256}
    {constants : List (String × Word256)}
    (h : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants) :
    constants.length = 31 := by
  simp only [generateBaseVkHeader] at h
  obtain ⟨h1, hb1, h⟩ := cert_except_bind_ok h
  obtain ⟨h2, hb2, h⟩ := cert_except_bind_ok h
  obtain ⟨h3, hb3, h⟩ := cert_except_bind_ok h
  obtain ⟨h4, hb4, h⟩ := cert_except_bind_ok h
  obtain ⟨h5, hb5, h⟩ := cert_except_bind_ok h
  obtain ⟨h6, hb6, h⟩ := cert_except_bind_ok h
  obtain ⟨h7, hb7, h⟩ := cert_except_bind_ok h
  obtain ⟨h8, hb8, h⟩ := cert_except_bind_ok h
  obtain ⟨h9, hb9, h⟩ := cert_except_bind_ok h
  obtain ⟨h10, hb10, h⟩ := cert_except_bind_ok h
  obtain ⟨h11, hb11, h⟩ := cert_except_bind_ok h
  obtain ⟨h12, hb12, h⟩ := cert_except_bind_ok h
  obtain ⟨h13, hb13, h⟩ := cert_except_bind_ok h
  obtain ⟨h14, hb14, h⟩ := cert_except_bind_ok h
  have hconst : unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:264" h14.finish =
      .ok constants := h
  have l1 : h1.words.length = VkHeaderLayout.builder.words.length :=
    headerScalarInsert_length _ _ _ _ _ _ hb1
  have l2 : h2.words.length = h1.words.length := headerScalarInsert_length _ _ _ _ _ _ hb2
  have l3 : h3.words.length = h2.words.length := headerScalarInsert_length _ _ _ _ _ _ hb3
  have l4 : h4.words.length = h3.words.length := headerScalarInsert_length _ _ _ _ _ _ hb4
  have l5 : h5.words.length = h4.words.length := headerScalarInsert_length _ _ _ _ _ _ hb5
  have l6 : h6.words.length = h5.words.length := headerScalarInsert_length _ _ _ _ _ _ hb6
  have l7 : h7.words.length = h6.words.length := headerScalarInsert_length _ _ _ _ _ _ hb7
  have l8 : h8.words.length = h7.words.length := headerScalarInsert_length _ _ _ _ _ _ hb8
  have l9 : h9.words.length = h8.words.length := headerScalarInsert_length _ _ _ _ _ _ hb9
  have l10 : h10.words.length = h9.words.length := headerScalarInsert_length _ _ _ _ _ _ hb10
  have l11 : h11.words.length = h10.words.length := headerScalarInsert_length _ _ _ _ _ _ hb11
  have l12 : h12.words.length = h11.words.length := headerG1Insert_length _ _ _ _ _ _ hb12
  have l13 : h13.words.length = h12.words.length := headerG2Insert_length _ _ _ _ _ _ hb13
  have l14 : h14.words.length = h13.words.length := headerG2Insert_length _ _ _ _ _ _ hb14
  have hlen14 : h14.words.length = 31 := by
    rw [l14, l13, l12, l11, l10, l9, l8, l7, l6, l5, l4, l3, l2, l1]
    decide
  have := VkHeaderBuilder.finish_length h14 constants (unwrapAt_ok hconst)
  exact this.trans hlen14

theorem generateBaseVkBody_constants_length {codecs : VkPointCodecs G₁ G₂}
    {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {payload : Halo2VerifyingKey}
    (h : generateBaseVkBody codecs inputs pre = .ok payload) :
    11 ≤ payload.constants.length := by
  simp only [generateBaseVkBody] at h
  obtain ⟨_trip, _, h⟩ := cert_except_bind_ok h
  obtain ⟨constants, hconst, h⟩ := cert_except_bind_ok h
  obtain ⟨_fixed, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_perm, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_u, _, h⟩ := cert_except_bind_ok h
  have hrec := Except.ok.inj (ε := Fault) (by simpa using h)
  have hcp : constants = payload.constants := congrArg (fun x => x.constants) hrec
  have hlen := generateBaseVkHeader_length hconst
  rw [← hcp]
  omega

theorem generateBaseVk_constants_length {codecs : VkPointCodecs G₁ G₂}
    {inputs : VerifierBuildInputs p G₁ G₂} {payload : Halo2VerifyingKey}
    (h : generateBaseVk codecs inputs = .ok payload) : 11 ≤ payload.constants.length := by
  simp only [generateBaseVk] at h
  obtain ⟨pre, _, h⟩ := cert_except_bind_ok h
  exact generateBaseVkBody_constants_length h

theorem generateVkFillAndFinal_ge {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {inputs : VerifierBuildInputs p G₁ G₂} {st : VkReservationState}
    {lc : VkLayoutChecked} {payload : Halo2VerifyingKey}
    (h : generateVkFillAndFinal feat env inputs st lc = .ok payload) :
    st.vk.constants.length ≤ payload.constants.length := by
  simp only [generateVkFillAndFinal] at h
  obtain ⟨vkFilled, hfill1, h⟩ := cert_except_bind_ok h
  obtain ⟨vkFilled2, hfill2, h⟩ := cert_except_bind_ok h
  obtain ⟨_fm, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_fp, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_fb, _, h⟩ := cert_except_bind_ok h
  split at h
  · split at h
    · obtain ⟨_u, _, h⟩ := cert_except_bind_ok h
      have h1 : st.vk.constants.length ≤ vkFilled.constants.length :=
        foldlM_fillConst_ge _ _ _ _ _ hfill1 (le_refl _)
      have h2 : vkFilled.constants.length ≤ vkFilled2.constants.length :=
        foldlM_fillProgram_ge _ _ _ _ _ hfill2 (le_refl _)
      have hrec := Except.ok.inj (ε := Fault) (by simpa using h)
      have hcp : vkFilled2.constants = payload.constants := by
        simpa using congrArg (fun x => x.constants) hrec
      rw [← hcp]
      omega
    · cases h
  · cases h

theorem generateVkFinalize_ge {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {inputs : VerifierBuildInputs p G₁ G₂} {headerWords : Nat} {st : VkReservationState}
    {payload : Halo2VerifyingKey}
    (h : generateVkFinalize feat env inputs headerWords st = .ok payload) :
    st.vk.constants.length ≤ payload.constants.length := by
  simp only [generateVkFinalize] at h
  obtain ⟨lc, _, h⟩ := cert_except_bind_ok h
  exact generateVkFillAndFinal_ge h

theorem generateVk_constants_length {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {codecs : VkPointCodecs G₁ G₂} {inputs : VerifierBuildInputs p G₁ G₂}
    {payload : Halo2VerifyingKey}
    (h : generateVk feat env codecs inputs = .ok payload) : 11 ≤ payload.constants.length := by
  simp only [generateVk] at h
  obtain ⟨vk0, hbase, h⟩ := cert_except_bind_ok h
  have h0 : 11 ≤ vk0.constants.length := generateBaseVk_constants_length hbase
  obtain ⟨st, hfold, h⟩ := cert_except_bind_ok h
  have hst : vk0.constants.length ≤ st.vk.constants.length :=
    foldlM_reserve_ge _ _ _ _ _ _ _ hfold (le_refl _)
  have hfin := generateVkFinalize_ge h
  omega

/-- Slots 0–10 of the generated base VK header. PROVED. -/
theorem generateBaseVkHeader_slots {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256}
    {constants : List (String × Word256)}
    (h : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants) :
    constants.getD 0 ("", 0) = ("vk_digest", pre.1) ∧
    constants.getD 1 ("", 0) = ("num_instances", (BitVec.ofNat 256 inputs.numInstances)) ∧
    constants.getD 2 ("", 0) = ("k", (BitVec.ofNat 256 inputs.vk.domain.k)) ∧
    constants.getD 3 ("", 0) = ("n_inv", pre.2.1) ∧
    constants.getD 4 ("", 0) = ("omega", pre.2.2.1) ∧
    constants.getD 5 ("", 0) = ("omega_inv", pre.2.2.2.1) ∧
    constants.getD 6 ("", 0) = ("omega_inv_to_l", pre.2.2.2.2) ∧
    constants.getD 7 ("", 0) = ("has_accumulator", (BitVec.ofNat 256 (if inputs.accEncoding.isSome then 1 else 0))) ∧
    constants.getD 8 ("", 0) = ("acc_offset", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.offset | none => 0)) ∧
    constants.getD 9 ("", 0) = ("num_acc_limbs", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.numLimbs | none => 0)) ∧
    constants.getD 10 ("", 0) = ("num_acc_limb_bits", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.numLimbBits | none => 0)) := by
  simp only [generateBaseVkHeader] at h
  obtain ⟨h1, hb1, h⟩ := cert_except_bind_ok h
  obtain ⟨h2, hb2, h⟩ := cert_except_bind_ok h
  obtain ⟨h3, hb3, h⟩ := cert_except_bind_ok h
  obtain ⟨h4, hb4, h⟩ := cert_except_bind_ok h
  obtain ⟨h5, hb5, h⟩ := cert_except_bind_ok h
  obtain ⟨h6, hb6, h⟩ := cert_except_bind_ok h
  obtain ⟨h7, hb7, h⟩ := cert_except_bind_ok h
  obtain ⟨h8, hb8, h⟩ := cert_except_bind_ok h
  obtain ⟨h9, hb9, h⟩ := cert_except_bind_ok h
  obtain ⟨h10, hb10, h⟩ := cert_except_bind_ok h
  obtain ⟨h11, hb11, h⟩ := cert_except_bind_ok h
  obtain ⟨h12, hb12, h⟩ := cert_except_bind_ok h
  obtain ⟨h13, hb13, h⟩ := cert_except_bind_ok h
  obtain ⟨h14, hb14, h⟩ := cert_except_bind_ok h
  have l1 : h1.words.length = VkHeaderLayout.builder.words.length :=
    headerScalarInsert_length _ _ _ _ _ _ hb1
  have l2 : h2.words.length = h1.words.length := headerScalarInsert_length _ _ _ _ _ _ hb2
  have l3 : h3.words.length = h2.words.length := headerScalarInsert_length _ _ _ _ _ _ hb3
  have l4 : h4.words.length = h3.words.length := headerScalarInsert_length _ _ _ _ _ _ hb4
  have l5 : h5.words.length = h4.words.length := headerScalarInsert_length _ _ _ _ _ _ hb5
  have l6 : h6.words.length = h5.words.length := headerScalarInsert_length _ _ _ _ _ _ hb6
  have l7 : h7.words.length = h6.words.length := headerScalarInsert_length _ _ _ _ _ _ hb7
  have l8 : h8.words.length = h7.words.length := headerScalarInsert_length _ _ _ _ _ _ hb8
  have l9 : h9.words.length = h8.words.length := headerScalarInsert_length _ _ _ _ _ _ hb9
  have l10 : h10.words.length = h9.words.length := headerScalarInsert_length _ _ _ _ _ _ hb10
  have l11 : h11.words.length = h10.words.length := headerScalarInsert_length _ _ _ _ _ _ hb11
  have l12 : h12.words.length = h11.words.length := headerG1Insert_length _ _ _ _ _ _ hb12
  have l13 : h13.words.length = h12.words.length := headerG2Insert_length _ _ _ _ _ _ hb13
  have l14 : h14.words.length = h13.words.length := headerG2Insert_length _ _ _ _ _ _ hb14
  have hlen14 : h14.words.length = 31 := by
    rw [l14, l13, l12, l11, l10, l9, l8, l7, l6, l5, l4, l3, l2, l1]
    decide
  have hconst : unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:264" h14.finish =
      .ok constants := h

  have s0 : constants.getD 0 ("", 0) = ("vk_digest", pre.1) := by
    have hw : h14.words[0]? = some (some ("vk_digest", pre.1)) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 0 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 0 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 0 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb7 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb6 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb5 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb4 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb3 0 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb2 0 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb1
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 0 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s1 : constants.getD 1 ("", 0) = ("num_instances", (BitVec.ofNat 256 inputs.numInstances)) := by
    have hw : h14.words[1]? = some (some ("num_instances", (BitVec.ofNat 256 inputs.numInstances))) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 1 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 1 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 1 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb7 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb6 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb5 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb4 1 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb3 1 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb2
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 1 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s2 : constants.getD 2 ("", 0) = ("k", (BitVec.ofNat 256 inputs.vk.domain.k)) := by
    have hw : h14.words[2]? = some (some ("k", (BitVec.ofNat 256 inputs.vk.domain.k))) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 2 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 2 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 2 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb7 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb6 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb5 2 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb4 2 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb3
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 2 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s3 : constants.getD 3 ("", 0) = ("n_inv", pre.2.1) := by
    have hw : h14.words[3]? = some (some ("n_inv", pre.2.1)) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 3 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 3 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 3 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 3 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 3 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 3 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 3 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb7 3 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb6 3 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb5 3 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb4
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 3 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s4 : constants.getD 4 ("", 0) = ("omega", pre.2.2.1) := by
    have hw : h14.words[4]? = some (some ("omega", pre.2.2.1)) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 4 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 4 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 4 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 4 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 4 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 4 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 4 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb7 4 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb6 4 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb5
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 4 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s5 : constants.getD 5 ("", 0) = ("omega_inv", pre.2.2.2.1) := by
    have hw : h14.words[5]? = some (some ("omega_inv", pre.2.2.2.1)) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 5 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 5 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 5 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 5 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 5 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 5 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 5 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb7 5 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb6
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 5 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s6 : constants.getD 6 ("", 0) = ("omega_inv_to_l", pre.2.2.2.2) := by
    have hw : h14.words[6]? = some (some ("omega_inv_to_l", pre.2.2.2.2)) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 6 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 6 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 6 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 6 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 6 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 6 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb8 6 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb7
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 6 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s7 : constants.getD 7 ("", 0) = ("has_accumulator", (BitVec.ofNat 256 (if inputs.accEncoding.isSome then 1 else 0))) := by
    have hw : h14.words[7]? = some (some ("has_accumulator", (BitVec.ofNat 256 (if inputs.accEncoding.isSome then 1 else 0)))) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 7 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 7 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 7 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 7 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 7 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb9 7 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb8
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 7 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s8 : constants.getD 8 ("", 0) = ("acc_offset", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.offset | none => 0)) := by
    have hw : h14.words[8]? = some (some ("acc_offset", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.offset | none => 0))) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 8 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 8 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 8 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 8 (by decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb10 8 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb9
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 8 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s9 : constants.getD 9 ("", 0) = ("num_acc_limbs", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.numLimbs | none => 0)) := by
    have hw : h14.words[9]? = some (some ("num_acc_limbs", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.numLimbs | none => 0))) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 9 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 9 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 9 (by left; decide)]
      rw [headerScalarInsert_frame _ _ _ _ _ _ hb11 9 (by decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb10
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 9 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have s10 : constants.getD 10 ("", 0) = ("num_acc_limb_bits", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.numLimbBits | none => 0)) := by
    have hw : h14.words[10]? = some (some ("num_acc_limb_bits", (match inputs.accEncoding with | some e => BitVec.ofNat 256 e.numLimbBits | none => 0))) := by
      rw [headerG2Insert_frame _ _ _ _ _ _ hb14 10 (by left; decide)]
      rw [headerG2Insert_frame _ _ _ _ _ _ hb13 10 (by left; decide)]
      rw [headerG1Insert_frame _ _ _ _ _ _ hb12 10 (by left; decide)]
      exact headerScalarInsert_get _ _ _ _ _ _ hb11
    have hget := VkHeaderBuilder.finish_get? h14 constants (Midfall.Generator.unwrapAt_ok hconst) 10 (by omega) hw
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  exact ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩

theorem payload_constantsLength (hg : Generates gi o) (hs : SupportedInput gi) :
    11 ≤ (renderOf gi o).pv.vk.constants.length := by
  obtain ⟨_m0, payload, _hraw, hgenvk, _hfp, h4⟩ := generate_spec hg
  have hv : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  have hlen := generateVk_constants_length hgenvk
  change 11 ≤ o.out.plan.vk.constants.length
  rw [hv]
  exact hlen

/-! ## CERT.6/7 helpers: the payload layout, the header prefix, and the codec words -/

/-- The section list `forVk` reserves, in order. PROVED. -/
theorem forVk_sections (headerWords quotientConstWords quotientProgramWords
    fixedCommitments permutationCommitments : Nat) (l : VkPayloadLayout)
    (h : VkPayloadLayout.forVk headerWords quotientConstWords quotientProgramWords
      fixedCommitments permutationCommitments = .ok l) :
    l.sections = [
      { kind := PayloadSectionKind.header, wordOffset := 0, wordLen := headerWords },
      { kind := PayloadSectionKind.quotientConstants, wordOffset := headerWords,
        wordLen := quotientConstWords },
      { kind := PayloadSectionKind.quotientProgram, wordOffset := headerWords + quotientConstWords,
        wordLen := quotientProgramWords },
      { kind := PayloadSectionKind.fixedCommitments,
        wordOffset := headerWords + quotientConstWords + quotientProgramWords,
        wordLen := fixedCommitments * 4 },
      { kind := PayloadSectionKind.permutationCommitments,
        wordOffset := headerWords + quotientConstWords + quotientProgramWords + fixedCommitments * 4,
        wordLen := permutationCommitments * 4 }] := by
  unfold VkPayloadLayout.forVk at h
  simp only [VkPayloadLayout.new, vkPayloadLayoutDefault,
    VkPayloadLayout.reserve, VkPayloadLayout.reserveG1, Bind.bind, Except.bind] at h
  simp (config := { decide := true }) at h
  split at h
  · cases h
  · injection h with hl
    subst hl
    rfl

/-- The constant table starts at the header section's end. PROVED. -/
theorem forVk_constOffset (headerWords quotientConstWords quotientProgramWords
    fixedCommitments permutationCommitments : Nat) (l : VkPayloadLayout)
    (h : VkPayloadLayout.forVk headerWords quotientConstWords quotientProgramWords
      fixedCommitments permutationCommitments = .ok l) :
    l.wordOffset PayloadSectionKind.quotientConstants = .ok headerWords := by
  unfold VkPayloadLayout.wordOffset VkPayloadLayout.requireSection VkPayloadLayout.section
  rw [forVk_sections headerWords quotientConstWords quotientProgramWords
    fixedCommitments permutationCommitments l h]
  rfl

/-- The program section starts past the header section. PROVED. -/
theorem forVk_programOffset (headerWords quotientConstWords quotientProgramWords
    fixedCommitments permutationCommitments : Nat) (l : VkPayloadLayout)
    (h : VkPayloadLayout.forVk headerWords quotientConstWords quotientProgramWords
      fixedCommitments permutationCommitments = .ok l) :
    l.wordOffset PayloadSectionKind.quotientProgram = .ok (headerWords + quotientConstWords) := by
  unfold VkPayloadLayout.wordOffset VkPayloadLayout.requireSection VkPayloadLayout.section
  rw [forVk_sections headerWords quotientConstWords quotientProgramWords
    fixedCommitments permutationCommitments l h]
  rfl

/-- The two quotient section offsets are at or past the header word count, because
    `forVk` reserves the header first. PROVED. -/
theorem generateVkLayoutChecks_offsets {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {inputs : VerifierBuildInputs p G₁ G₂} {headerWords : Nat} {st : VkReservationState}
    {lc : VkLayoutChecked}
    (h : generateVkLayoutChecks feat env inputs headerWords st = .ok lc) :
    headerWords ≤ lc.constOffset ∧ headerWords ≤ lc.programOffset := by
  simp only [generateVkLayoutChecks] at h
  cases hb : st.build with
  | none =>
      simp only [hb] at h
      cases h
  | some b =>
      simp only [hb, Bind.bind, Except.bind] at h
      obtain ⟨pl, hpl, h⟩ := cert_except_bind_ok h
      obtain ⟨co, hco, h⟩ := cert_except_bind_ok h
      obtain ⟨po, hpo, h⟩ := cert_except_bind_ok h
      obtain ⟨qcLen, _hqcLen, h⟩ := cert_except_bind_ok h
      have hco' : pl.wordOffset PayloadSectionKind.quotientConstants = .ok co :=
        Midfall.Generator.unwrapAt_ok hco
      have hpo' : pl.wordOffset PayloadSectionKind.quotientProgram = .ok po :=
        Midfall.Generator.unwrapAt_ok hpo
      have hcoE : co = headerWords := by
        rw [forVk_constOffset _ _ _ _ _ pl (Midfall.Generator.unwrapAt_ok hpl)] at hco'
        exact (Except.ok.inj hco').symm
      have hpoE : po = headerWords + st.quotientConstWords := by
        rw [forVk_programOffset _ _ _ _ _ pl (Midfall.Generator.unwrapAt_ok hpl)] at hpo'
        exact (Except.ok.inj hpo').symm
      split at h
      · obtain ⟨_qpLen, _hqpLen, h⟩ := cert_except_bind_ok h
        split at h
        · split at h
          · split at h
            · split at h
              · injection h with hlc
                cases hlc
                simp only
                omega
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h

/-- **THE HEADER PREFIX OF `generateVk`.** Slots below the base VK's constant count survive
    the reservation loop (`foldlM_reserve_getD`) and the two write-back loops
    (`foldlM_fillConst_getD`, `foldlM_fillProgram_getD`), whose offsets are at or above that
    count by `generateVkLayoutChecks_offsets`. PROVED. -/
theorem generateVk_getD_lt {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {codecs : VkPointCodecs G₁ G₂} {inputs : VerifierBuildInputs p G₁ G₂}
    {payload : Halo2VerifyingKey}
    (h : generateVk feat env codecs inputs = .ok payload)
    (vk0 : Halo2VerifyingKey) (hbase : generateBaseVk codecs inputs = .ok vk0)
    (k : Nat) (hk : k < vk0.constants.length) (d : String × Word256) :
    payload.constants.getD k d = vk0.constants.getD k d := by
  simp only [generateVk] at h
  obtain ⟨vk0', hbase', h⟩ := cert_except_bind_ok h
  have hvk : vk0' = vk0 := Except.ok.inj (hbase'.symm.trans hbase)
  subst hvk
  obtain ⟨st, hfold, hfin⟩ := cert_except_bind_ok h
  have h1 : st.vk.constants.getD k d = vk0'.constants.getD k d :=
    foldlM_reserve_getD (List.range 8) feat env inputs vk0'.constants.length
      { vk := vk0', quotientConstWords := 0, quotientProgramWords := 0, build := none } st
      hfold k hk (le_refl _) d
  simp only [generateVkFinalize] at hfin
  obtain ⟨lc, hlc, hfill⟩ := cert_except_bind_ok hfin
  have hlcg := generateVkLayoutChecks_offsets hlc
  simp only [generateVkFillAndFinal] at hfill
  obtain ⟨vkFilled, hfill1, h⟩ := cert_except_bind_ok hfill
  obtain ⟨vkFilled2, hfill2, h⟩ := cert_except_bind_ok h
  obtain ⟨_fm, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_fp, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_fb, _, h⟩ := cert_except_bind_ok h
  split at h
  · split at h
    · obtain ⟨_u, _, h⟩ := cert_except_bind_ok h
      cases h
      have h2 : vkFilled.constants.getD k d = st.vk.constants.getD k d :=
        foldlM_fillConst_getD lc.qbuild.consts.zipIdx lc.constOffset st.vk vkFilled hfill1 k
          (by omega) d
      have h3 : vkFilled2.constants.getD k d = vkFilled.constants.getD k d :=
        foldlM_fillProgram_getD lc.chunks.zipIdx lc.programOffset vkFilled vkFilled2 hfill2 k
          (by omega) d
      change vkFilled2.constants.getD k d = vk0'.constants.getD k d
      rw [h3, h2, h1]
    · cases h
  · cases h

/-- An eight-element list is eight named elements. PROVED. -/
private theorem cert_length_eq_eight {α : Type} {l : List α} :
    l.length = 8 ↔ ∃ a b c d e f g h, l = [a,b,c,d,e,f,g,h] := by
  constructor
  · intro hl
    match l, hl with
    | [a,b,c,d,e,f,g,h], _ => exact ⟨a,b,c,d,e,f,g,h,rfl⟩
  · rintro ⟨a,b,c,d,e,f,g,h,rfl⟩
    rfl

/-- The G1 base slot's header names, in `vkHeaderFields` order. -/
def vkG1BaseNames : List String := ["g1_x_hi", "g1_x_lo", "g1_y_hi", "g1_y_lo"]

/-- The G2 base slot's header names, in `vkHeaderFields` order. -/
def vkG2BaseNames : List String := ["g2_x_c0_hi", "g2_x_c0_lo", "g2_x_c1_hi", "g2_x_c1_lo",
  "g2_y_c0_hi", "g2_y_c0_lo", "g2_y_c1_hi", "g2_y_c1_lo"]

/-- The `neg_s_g2` base slot's header names, in `vkHeaderFields` order. -/
def vkNegSG2BaseNames : List String := ["neg_s_g2_x_c0_hi", "neg_s_g2_x_c0_lo",
  "neg_s_g2_x_c1_hi", "neg_s_g2_x_c1_lo", "neg_s_g2_y_c0_hi", "neg_s_g2_y_c0_lo",
  "neg_s_g2_y_c1_hi", "neg_s_g2_y_c1_lo"]

private theorem g1Base_word : VkHeaderSlot.word .g1Base = 11 := by decide
private theorem g2Base_word : VkHeaderSlot.word .g2Base = 15 := by decide
private theorem negSG2Base_word : VkHeaderSlot.word .negSG2Base = 23 := by decide

/-- `generateBaseVkHeader` supplies its three point-insert builders and the final header. PROVED. -/
theorem generateBaseVkHeader_parts {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256}
    {constants : List (String × Word256)}
    (h : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants) :
    ∃ (h11 h12 h13 h14 : Midfall.Generator.VkHeaderBuilder),
      Midfall.Generator.headerG1Insert h11 "proofs/solidity-verifier/src/lowering/vk.rs:225"
          .g1Base vkG1BaseNames g1Words = .ok h12 ∧
      Midfall.Generator.headerG2Insert h12 "proofs/solidity-verifier/src/lowering/vk.rs:231"
          .g2Base vkG2BaseNames g2Words = .ok h13 ∧
      Midfall.Generator.headerG2Insert h13 "proofs/solidity-verifier/src/lowering/vk.rs:247"
          .negSG2Base vkNegSG2BaseNames negSG2Words = .ok h14 ∧
      h14.words.length = 31 ∧
      Midfall.Generator.unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:264"
        h14.finish = .ok constants := by
  simp only [Midfall.Generator.generateBaseVkHeader] at h
  obtain ⟨h1, hb1, h⟩ := cert_except_bind_ok h
  obtain ⟨h2, hb2, h⟩ := cert_except_bind_ok h
  obtain ⟨h3, hb3, h⟩ := cert_except_bind_ok h
  obtain ⟨h4, hb4, h⟩ := cert_except_bind_ok h
  obtain ⟨h5, hb5, h⟩ := cert_except_bind_ok h
  obtain ⟨h6, hb6, h⟩ := cert_except_bind_ok h
  obtain ⟨h7, hb7, h⟩ := cert_except_bind_ok h
  obtain ⟨h8, hb8, h⟩ := cert_except_bind_ok h
  obtain ⟨h9, hb9, h⟩ := cert_except_bind_ok h
  obtain ⟨h10, hb10, h⟩ := cert_except_bind_ok h
  obtain ⟨h11, hb11, h⟩ := cert_except_bind_ok h
  obtain ⟨h12, hb12, h⟩ := cert_except_bind_ok h
  obtain ⟨h13, hb13, h⟩ := cert_except_bind_ok h
  obtain ⟨h14, hb14, h⟩ := cert_except_bind_ok h
  have hconst : Midfall.Generator.unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:264"
      h14.finish = .ok constants := h
  have l1 : h1.words.length = Midfall.Generator.VkHeaderLayout.builder.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb1
  have l2 : h2.words.length = h1.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb2
  have l3 : h3.words.length = h2.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb3
  have l4 : h4.words.length = h3.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb4
  have l5 : h5.words.length = h4.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb5
  have l6 : h6.words.length = h5.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb6
  have l7 : h7.words.length = h6.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb7
  have l8 : h8.words.length = h7.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb8
  have l9 : h9.words.length = h8.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb9
  have l10 : h10.words.length = h9.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb10
  have l11 : h11.words.length = h10.words.length :=
    Midfall.Generator.headerScalarInsert_length _ _ _ _ _ _ hb11
  have l12 : h12.words.length = h11.words.length :=
    Midfall.Generator.headerG1Insert_length _ _ _ _ _ _ hb12
  have l13 : h13.words.length = h12.words.length :=
    Midfall.Generator.headerG2Insert_length _ _ _ _ _ _ hb13
  have l14 : h14.words.length = h13.words.length :=
    Midfall.Generator.headerG2Insert_length _ _ _ _ _ _ hb14
  have hlen14 : h14.words.length = 31 := by
    rw [l14, l13, l12, l11, l10, l9, l8, l7, l6, l5, l4, l3, l2, l1]
    decide
  exact ⟨h11, h12, h13, h14, hb12, hb13, hb14, hlen14, hconst⟩

/-- Slots 11–14 of the base VK header: the G1 generator's four words. PROVED. -/
theorem generateBaseVkHeader_g1Base_get {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256}
    {constants : List (String × Word256)}
    (h : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants)
    (hg1 : g1Words.length = 4) :
    ∀ j, j < 4 → constants.getD (VkHeaderSlot.word .g1Base + j) ("", 0) =
      (vkG1BaseNames.getD j "", g1Words.getD j 0) := by
  obtain ⟨h11, h12, h13, h14, hb12, hb13, hb14, hlen14, hconst⟩ :=
    generateBaseVkHeader_parts h
  have hb13' := hb13
  have hb14' := hb14
  intro j hj
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hg1
  have hg : h12.words[VkHeaderSlot.word .g1Base + j]? =
      some (some (vkG1BaseNames.getD j "", [a, b, c, d].getD j 0)) := by
    apply Midfall.Generator.headerG1Insert_get h11 _ _ _ _ h12 hb12
    interval_cases j <;> rfl
  have hw14 : h14.words[VkHeaderSlot.word .g1Base + j]? =
      some (some (vkG1BaseNames.getD j "", [a, b, c, d].getD j 0)) := by
    rw [Midfall.Generator.headerG2Insert_frame _ _ _ _ _ _ hb14' _
      (by left; rw [negSG2Base_word, g1Base_word]; omega)]
    rw [Midfall.Generator.headerG2Insert_frame _ _ _ _ _ _ hb13' _
      (by left; rw [g2Base_word, g1Base_word]; omega)]
    exact hg
  change constants.getD (VkHeaderSlot.word .g1Base + j) ("", 0) =
    (vkG1BaseNames.getD j "", [a, b, c, d].getD j 0)
  rw [Midfall.Generator.VkHeaderBuilder.finish_getD h14 constants
    (Midfall.Generator.unwrapAt_ok hconst) _
    (by rw [hlen14, g1Base_word]; omega) hw14 ("", 0)]

/-- Slots 15–22 of the base VK header: the G2 generator's eight words. PROVED. -/
theorem generateBaseVkHeader_g2Base_get {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256}
    {constants : List (String × Word256)}
    (h : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants)
    (hg2 : g2Words.length = 8) :
    ∀ j, j < 8 → constants.getD (VkHeaderSlot.word .g2Base + j) ("", 0) =
      (vkG2BaseNames.getD j "", g2Words.getD j 0) := by
  obtain ⟨h11, h12, h13, h14, hb12, hb13, hb14, hlen14, hconst⟩ :=
    generateBaseVkHeader_parts h
  have hb14' := hb14
  intro j hj
  obtain ⟨a, b, c, d, e, f, g, k, rfl⟩ := cert_length_eq_eight.mp hg2
  have hg : h13.words[VkHeaderSlot.word .g2Base + j]? =
      some (some (vkG2BaseNames.getD j "", [a, b, c, d, e, f, g, k].getD j 0)) := by
    apply Midfall.Generator.headerG2Insert_get h12 _ _ _ _ h13 hb13
    interval_cases j <;> rfl
  have hw14 : h14.words[VkHeaderSlot.word .g2Base + j]? =
      some (some (vkG2BaseNames.getD j "", [a, b, c, d, e, f, g, k].getD j 0)) := by
    rw [Midfall.Generator.headerG2Insert_frame _ _ _ _ _ _ hb14' _
      (by left; rw [negSG2Base_word, g2Base_word]; omega)]
    exact hg
  change constants.getD (VkHeaderSlot.word .g2Base + j) ("", 0) =
    (vkG2BaseNames.getD j "", [a, b, c, d, e, f, g, k].getD j 0)
  rw [Midfall.Generator.VkHeaderBuilder.finish_getD h14 constants
    (Midfall.Generator.unwrapAt_ok hconst) _
    (by rw [hlen14, g2Base_word]; omega) hw14 ("", 0)]

/-- Slots 23–30 of the base VK header: the negated SRS `s_g2`'s eight words. PROVED. -/
theorem generateBaseVkHeader_negSG2_get {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256}
    {constants : List (String × Word256)}
    (h : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants)
    (hneg : negSG2Words.length = 8) :
    ∀ j, j < 8 → constants.getD (VkHeaderSlot.word .negSG2Base + j) ("", 0) =
      (vkNegSG2BaseNames.getD j "", negSG2Words.getD j 0) := by
  obtain ⟨h11, h12, h13, h14, hb12, hb13, hb14, hlen14, hconst⟩ :=
    generateBaseVkHeader_parts h
  intro j hj
  obtain ⟨a, b, c, d, e, f, g, k, rfl⟩ := cert_length_eq_eight.mp hneg
  have hw14 : h14.words[VkHeaderSlot.word .negSG2Base + j]? =
      some (some (vkNegSG2BaseNames.getD j "", [a, b, c, d, e, f, g, k].getD j 0)) := by
    apply Midfall.Generator.headerG2Insert_get h13 _ _ _ _ h14 hb14
    interval_cases j <;> rfl
  change constants.getD (VkHeaderSlot.word .negSG2Base + j) ("", 0) =
    (vkNegSG2BaseNames.getD j "", [a, b, c, d, e, f, g, k].getD j 0)
  rw [Midfall.Generator.VkHeaderBuilder.finish_getD h14 constants
    (Midfall.Generator.unwrapAt_ok hconst) _
    (by rw [hlen14, negSG2Base_word]; omega) hw14 ("", 0)]

/-- A fold of a word-byte append over pairs equals the same fold over the second components. -/
theorem foldl_wordBytes_eq_of_snd (a : Bytes) {l : List (String × Word256)} {ws : List Word256}
    (hlen : l.length = ws.length)
    (h : ∀ j, j < ws.length → (l[j]?).map Prod.snd = ws[j]?) :
    l.foldl (fun acc p => ByteArray.append acc (wordToBytesBE p.2)) a =
      ws.foldl (fun acc w => ByteArray.append acc (wordToBytesBE w)) a := by
  induction ws generalizing l a with
  | nil =>
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hl
      rfl
  | cons w ws ih =>
      cases l with
      | nil => simp at hlen
      | cons p ps =>
          obtain ⟨name, pw⟩ := p
          have h0 := h 0 (by simp)
          simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at h0
          have hlen' : ps.length = ws.length := by simpa using hlen
          have h' : ∀ j, j < ws.length → (ps[j]?).map Prod.snd = ws[j]? := by
            intro j hj
            have := h (j + 1) (by simp [hj])
            simpa using this
          simp only [List.foldl_cons, h0]
          exact ih _ hlen' h'

/-- **THE HEADER WORDS ARE THE LIST'S WORDS.** `vkHeaderBytes` reads `n` consecutive
    constant words starting at `i`; when their second components are `ws`, the bytes are the
    fold of `wordToBytesBE` over `ws`. PROVED. -/
theorem vkHeaderBytes_eq_words {PV : PlanView} {i n : Nat} {ws : List Word256}
    (hlen : i + n ≤ PV.vk.constants.length) (hws : ws.length = n)
    (hget : ∀ j, j < n → (PV.vk.constants.getD (i + j) ("", 0)).2 = ws.getD j 0) :
    Midfall.Lowering.vkHeaderBytes PV i n =
      ws.foldl (init := Bytes.empty)
        (fun acc w => ByteArray.append acc (wordToBytesBE w)) := by
  unfold Midfall.Lowering.vkHeaderBytes
  apply foldl_wordBytes_eq_of_snd Bytes.empty
  · rw [List.length_take, List.length_drop]
    omega
  · intro j hj
    rw [List.getElem?_take, if_pos (by omega)]
    rw [List.getElem?_drop]
    rw [List.getElem?_eq_getElem (by omega : i + j < PV.vk.constants.length)]
    rw [List.getElem?_eq_getElem (by omega : j < ws.length)]
    have h1 := hget j (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by omega : i + j < PV.vk.constants.length)] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by omega : j < ws.length)] at h1
    simp only [Option.getD_some] at h1
    simpa only [Option.map_some, Option.some.injEq] using h1

/-- `generateBaseVk` splits into the prefix and the body. PROVED. -/
theorem generateBaseVk_parts {codecs : VkPointCodecs G₁ G₂}
    {inputs : VerifierBuildInputs p G₁ G₂} {payload : Halo2VerifyingKey}
    (h : generateBaseVk codecs inputs = .ok payload) :
    ∃ pre, generateBaseVkPrefix inputs = .ok pre ∧
      generateBaseVkBody codecs inputs pre = .ok payload := by
  simp only [generateBaseVk] at h
  obtain ⟨pre, hpre, h⟩ := cert_except_bind_ok h
  exact ⟨pre, hpre, h⟩

/-- `generateBaseVkBody` exposes its encodings, header words and commitment mapMs. PROVED. -/
theorem generateBaseVkBody_parts {codecs : VkPointCodecs G₁ G₂}
    {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {payload : Halo2VerifyingKey} (h : generateBaseVkBody codecs inputs pre = .ok payload) :
    ∃ (g1Words g2Words negSG2Words : List Word256) (constants : List (String × Word256))
      (fixedComms permComms : List Midfall.Generator.G1Words),
      generateBaseVkEncodings codecs inputs = .ok (g1Words, g2Words, negSG2Words) ∧
      generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants ∧
      inputs.vk.fixedCommitments.toList.mapM
        (fun g => g1ToU256s (codecs.g1Repr g) >>= vkG1WordsOf) = .ok fixedComms ∧
      inputs.vk.permutation.commitments.toList.mapM
        (fun g => g1ToU256s (codecs.g1Repr g) >>= vkG1WordsOf) = .ok permComms ∧
      payload.constants = constants ∧ payload.fixedComms = fixedComms ∧
      payload.permutationComms = permComms := by
  simp only [generateBaseVkBody] at h
  obtain ⟨⟨g1Words, g2Words, negSG2Words⟩, henc, h⟩ := cert_except_bind_ok h
  obtain ⟨constants, hhdr, h⟩ := cert_except_bind_ok h
  obtain ⟨fixedComms, hfix, h⟩ := cert_except_bind_ok h
  obtain ⟨permComms, hperm, h⟩ := cert_except_bind_ok h
  obtain ⟨_u, _, h⟩ := cert_except_bind_ok h
  cases h
  exact ⟨g1Words, g2Words, negSG2Words, constants, fixedComms, permComms,
    henc, hhdr, hfix, hperm, rfl, rfl, rfl⟩

/-- `generateBaseVkPrefix` returns the five field elements its five `feToU256` calls built. PROVED. -/
theorem generateBaseVkPrefix_components {inputs : VerifierBuildInputs p G₁ G₂}
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    (h : generateBaseVkPrefix inputs = .ok pre) :
    feToU256 (bytesToNats (frToRepr inputs.vk.transcriptRepr)) = .ok pre.1 ∧
    (∃ nInvField, invert ((2 ^ inputs.vk.domain.k : ℕ) : Fr p) = some nInvField ∧
      feToU256 (bytesToNats (frToRepr nInvField)) = .ok pre.2.1) ∧
    feToU256 (bytesToNats (frToRepr (EvaluationDomain.getOmega inputs.vk.domain))) =
      .ok pre.2.2.1 ∧
    feToU256 (bytesToNats (frToRepr (EvaluationDomain.getOmegaInv inputs.vk.domain))) =
      .ok pre.2.2.2.1 ∧
    feToU256 (bytesToNats (frToRepr
      (powVartime (EvaluationDomain.getOmegaInv inputs.vk.domain)
        (Int.natAbs inputs.meta_.rotationLast)))) = .ok pre.2.2.2.2 := by
  simp only [generateBaseVkPrefix, Bind.bind, Except.bind] at h
  generalize h1 : feToU256 (bytesToNats (frToRepr inputs.vk.transcriptRepr)) = fe1 at h
  cases fe1 with
  | error e => cases h
  | ok v1 =>
    dsimp only at h
    generalize h2 : invert ((2 ^ inputs.vk.domain.k : ℕ) : Fr p) = o2 at h
    cases o2 with
    | none => cases h
    | some x2 =>
      dsimp only at h
      generalize h3 : feToU256 (bytesToNats (frToRepr x2)) = fe3 at h
      cases fe3 with
      | error e => cases h
      | ok v3 =>
        dsimp only at h
        generalize h4 : feToU256 (bytesToNats (frToRepr
          (EvaluationDomain.getOmega inputs.vk.domain))) = fe4 at h
        cases fe4 with
        | error e => cases h
        | ok v4 =>
          dsimp only at h
          generalize h5 : feToU256 (bytesToNats (frToRepr
            (EvaluationDomain.getOmegaInv inputs.vk.domain))) = fe5 at h
          cases fe5 with
          | error e => cases h
          | ok v5 =>
            dsimp only at h
            generalize h6 : feToU256 (bytesToNats (frToRepr
                (powVartime (EvaluationDomain.getOmegaInv inputs.vk.domain)
                  (Int.natAbs inputs.meta_.rotationLast)))) = fe6 at h
            cases fe6 with
            | error e => cases h
            | ok v6 =>
              dsimp only at h
              generalize hg1 : decideBool (P.decEqG₁
                (List.foldl (fun acc g => acc * g) 1 inputs.params.gLagrange) P.g₁) = b1 at h
              cases b1 with
              | false => cases h
              | true =>
                generalize hg2 : (inputs.params.g2 == P.g₂) = b2 at h
                cases b2 with
                | false => cases h
                | true =>
                  simp only [reduceIte] at h
                  cases h
                  dsimp only
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · rw [← h1]
                  · exact ⟨x2, rfl, h3⟩
                  · rw [← h4]
                  · rw [← h5]
                  · rw [← h6]

/-- `newFromVk`'s plan meta keeps the raw meta's rotation. PROVED. -/
theorem newFromVk_rotationLast {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding)
    (payload : Halo2VerifyingKey) (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk feat field cs rawMeta numInstances accEncoding
        payload = .ok plan) :
    plan.meta_.rotationLast = rawMeta.rotationLast := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, hq, h1⟩ := cert_except_bind_ok h
  obtain ⟨_proofLayout, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨_qplan, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨_build, _, h4⟩ := cert_except_bind_ok h3
  obtain ⟨_nw, _, h5⟩ := cert_except_bind_ok h4
  obtain ⟨_pcs, _, h6⟩ := cert_except_bind_ok h5
  obtain ⟨_acc, _, h7⟩ := cert_except_bind_ok h6
  obtain ⟨_memory, _, h8⟩ := cert_except_bind_ok h7
  obtain ⟨_op, _, h9⟩ := cert_except_bind_ok h8
  obtain ⟨_trip, _, h10⟩ := cert_except_bind_ok h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals
    change q.2.1.rotationLast = rawMeta.rotationLast
    exact Midfall.Generator.metaDataForStableStaticLayout_rotationLast hq


theorem payload_header (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.vkDigest = frWord gi.vk.transcriptRepr ∧
    (Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.numInstances).toNat = gi.cfg.numInstances ∧
    (Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.k).toNat = gi.vk.domain.k ∧
    Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.nInv =
      frWord (((2 ^ gi.vk.domain.k : ℕ) : Fr p)⁻¹) ∧
    Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.omega = frWord gi.vk.domain.omega ∧
    Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.omegaInv = frWord gi.vk.domain.omegaInv ∧
    Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.omegaInvToL =
      frWord (gi.vk.domain.omegaInv ^ (renderOf gi o).plan.meta_.rotationLast.natAbs) ∧
    ((Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (Midfall.LoweringV3.payloadWord (renderOf gi o).pv Midfall.Generator.vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
      accWordsOfEncoding gi.cfg.accumulator := by
  obtain ⟨m0, payload, hraw, hgenvk, _hfp, h4⟩ := generate_spec hg
  have hvk : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  obtain ⟨vk0, hbase⟩ := generateVk_base hgenvk
  obtain ⟨pre, hpre, hbody⟩ := generateBaseVk_parts hbase
  obtain ⟨g1W, g2W, negW, consts, fixedC, permC, henc, hhdr, hfix, hperm, hconst,
    _hfixEq, _hpermEq⟩ := generateBaseVkBody_parts hbody
  have hlen31 : vk0.constants.length = 31 := by
    rw [hconst]
    exact generateBaseVkHeader_length hhdr
  obtain ⟨hd, ⟨nInvField, hinv, hnInv⟩, homega, homegaInv, homegaInvToL⟩ :=
    generateBaseVkPrefix_components hpre
  have hdigest : pre.1 = frWord gi.vk.transcriptRepr :=
    Except.ok.inj (hd.symm.trans (Midfall.Lowering.feToU256_frToRepr gi.vk.transcriptRepr))
  have hinvEq : nInvField = (((2 ^ gi.vk.domain.k : ℕ) : Fr p))⁻¹ := by
    change invert (((2 ^ gi.vk.domain.k : ℕ) : Fr p)) = some nInvField at hinv
    unfold invert at hinv
    by_cases hzero : (((2 ^ gi.vk.domain.k : ℕ) : Fr p)) = 0
    · rw [if_pos hzero] at hinv
      cases hinv
    · rw [if_neg hzero] at hinv
      exact (Option.some.inj hinv).symm
  have hnInv' : pre.2.1 = frWord (((2 ^ gi.vk.domain.k : ℕ) : Fr p)⁻¹) := by
    have h := Except.ok.inj (hnInv.symm.trans (Midfall.Lowering.feToU256_frToRepr nInvField))
    rw [hinvEq] at h
    exact h
  have homega' : pre.2.2.1 = frWord gi.vk.domain.omega := by
    have h := Except.ok.inj (homega.symm.trans
      (Midfall.Lowering.feToU256_frToRepr (EvaluationDomain.getOmega (buildInputsOf gi m0).vk.domain)))
    simp only [EvaluationDomain.getOmega] at h
    change pre.2.2.1 = frWord (gi.vk.domain.omega) at h
    exact h
  have homegaInv' : pre.2.2.2.1 = frWord gi.vk.domain.omegaInv := by
    have h := Except.ok.inj (homegaInv.symm.trans
      (Midfall.Lowering.feToU256_frToRepr (EvaluationDomain.getOmegaInv (buildInputsOf gi m0).vk.domain)))
    simp only [EvaluationDomain.getOmegaInv] at h
    change pre.2.2.2.1 = frWord (gi.vk.domain.omegaInv) at h
    exact h
  obtain ⟨rawMeta, plan, hraw', hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  have hrawEq : rawMeta = m0 := Except.ok.inj (hraw'.symm.trans hraw)
  have hmeta : (renderOf gi o).plan.meta_.rotationLast = m0.rotationLast := by
    rw [hp]
    rw [newFromVk_rotationLast Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs rawMeta
      gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl, hrawEq]
  have homegaInvToL' : pre.2.2.2.2 =
      frWord (gi.vk.domain.omegaInv ^ (renderOf gi o).plan.meta_.rotationLast.natAbs) := by
    have h := Except.ok.inj (homegaInvToL.symm.trans (Midfall.Lowering.feToU256_frToRepr
      (powVartime (EvaluationDomain.getOmegaInv (buildInputsOf gi m0).vk.domain)
        (Int.natAbs (buildInputsOf gi m0).meta_.rotationLast))))
    rw [Midfall.LoweringV3.LagrangeAlg.powVartime_eq_pow] at h
    simp only [EvaluationDomain.getOmegaInv] at h
    change pre.2.2.2.2 =
      frWord (gi.vk.domain.omegaInv ^ m0.rotationLast.natAbs) at h
    rw [hmeta]
    exact h
  have hval : ∀ (i : Nat), i < vk0.constants.length →
      Midfall.LoweringV3.payloadWord (renderOf gi o).pv i =
        (vk0.constants.getD i ("", 0)).2 := by
    intro i hi
    unfold Midfall.LoweringV3.payloadWord
    change ((o.out.plan.vk).constants.getD i ("", 0)).2 =
      (vk0.constants.getD i ("", 0)).2
    rw [hvk]
    exact congrArg Prod.snd (generateVk_getD_lt hgenvk vk0 hbase i hi ("", 0))
  have slot (i : Nat) (hi : i < vk0.constants.length) :
      Midfall.LoweringV3.payloadWord (renderOf gi o).pv i =
        (vk0.constants.getD i ("", 0)).2 := hval i hi
  have h0 : vk0.constants.getD 0 ("", 0) = ("vk_digest", pre.1) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).1
  have h1 : vk0.constants.getD 1 ("", 0) =
      ("num_instances", (BitVec.ofNat 256 (buildInputsOf gi m0).numInstances)) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.1
  have h2 : vk0.constants.getD 2 ("", 0) =
      ("k", (BitVec.ofNat 256 (buildInputsOf gi m0).vk.domain.k)) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.1
  have h3 : vk0.constants.getD 3 ("", 0) = ("n_inv", pre.2.1) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.1
  have h4s : vk0.constants.getD 4 ("", 0) = ("omega", pre.2.2.1) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.1
  have h5s : vk0.constants.getD 5 ("", 0) = ("omega_inv", pre.2.2.2.1) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.2.1
  have h6s : vk0.constants.getD 6 ("", 0) = ("omega_inv_to_l", pre.2.2.2.2) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.2.2.1
  have h7s : vk0.constants.getD 7 ("", 0) =
      ("has_accumulator", (BitVec.ofNat 256 (if (buildInputsOf gi m0).accEncoding.isSome then 1 else 0))) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.2.2.2.1
  have h8s : vk0.constants.getD 8 ("", 0) =
      ("acc_offset", (match (buildInputsOf gi m0).accEncoding with
        | some e => BitVec.ofNat 256 e.offset | none => 0)) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.2.2.2.2.1
  have h9s : vk0.constants.getD 9 ("", 0) =
      ("num_acc_limbs", (match (buildInputsOf gi m0).accEncoding with
        | some e => BitVec.ofNat 256 e.numLimbs | none => 0)) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.2.2.2.2.2.1
  have h10s : vk0.constants.getD 10 ("", 0) =
      ("num_acc_limb_bits", (match (buildInputsOf gi m0).accEncoding with
        | some e => BitVec.ofNat 256 e.numLimbBits | none => 0)) := by
    rw [hconst]; exact (generateBaseVkHeader_slots hhdr).2.2.2.2.2.2.2.2.2.2
  have hnumBound : gi.cfg.numInstances < 2 ^ 256 := by
    have h1 := hs.sizeBound.1
    have h2 : (2 : Nat) ^ 64 ≤ 2 ^ 256 := by norm_num
    omega
  have hkBound : gi.vk.domain.k < 2 ^ 256 := by
    have h1 := hs.sizeBound.2
    have h2 : (2 : Nat) ^ 64 ≤ 2 ^ 256 := by norm_num
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Midfall.LoweringV3.payloadWord (renderOf gi o).pv 0 = frWord gi.vk.transcriptRepr
    exact (slot 0 (by omega)).trans ((congrArg Prod.snd h0).trans hdigest)
  · change (Midfall.LoweringV3.payloadWord (renderOf gi o).pv 1).toNat = gi.cfg.numInstances
    rw [slot 1 (by omega), congrArg Prod.snd h1, BitVec.toNat_ofNat]
    change gi.cfg.numInstances % 2 ^ 256 = gi.cfg.numInstances
    exact Nat.mod_eq_of_lt hnumBound
  · change (Midfall.LoweringV3.payloadWord (renderOf gi o).pv 2).toNat = gi.vk.domain.k
    rw [slot 2 (by omega), congrArg Prod.snd h2, BitVec.toNat_ofNat]
    change gi.vk.domain.k % 2 ^ 256 = gi.vk.domain.k
    exact Nat.mod_eq_of_lt hkBound
  · change Midfall.LoweringV3.payloadWord (renderOf gi o).pv 3 =
      frWord (((2 ^ gi.vk.domain.k : ℕ) : Fr p)⁻¹)
    exact (slot 3 (by omega)).trans ((congrArg Prod.snd h3).trans hnInv')
  · change Midfall.LoweringV3.payloadWord (renderOf gi o).pv 4 = frWord gi.vk.domain.omega
    exact (slot 4 (by omega)).trans ((congrArg Prod.snd h4s).trans homega')
  · change Midfall.LoweringV3.payloadWord (renderOf gi o).pv 5 = frWord gi.vk.domain.omegaInv
    exact (slot 5 (by omega)).trans ((congrArg Prod.snd h5s).trans homegaInv')
  · change Midfall.LoweringV3.payloadWord (renderOf gi o).pv 6 =
      frWord (gi.vk.domain.omegaInv ^ (renderOf gi o).plan.meta_.rotationLast.natAbs)
    exact (slot 6 (by omega)).trans ((congrArg Prod.snd h6s).trans homegaInvToL')
  · change ((Midfall.LoweringV3.payloadWord (renderOf gi o).pv 7).toNat,
      (Midfall.LoweringV3.payloadWord (renderOf gi o).pv 8).toNat,
      (Midfall.LoweringV3.payloadWord (renderOf gi o).pv 9).toNat,
      (Midfall.LoweringV3.payloadWord (renderOf gi o).pv 10).toNat) =
      accWordsOfEncoding gi.cfg.accumulator
    change vk0.constants.getD 7 ("", 0) =
      ("has_accumulator", (BitVec.ofNat 256 (if gi.cfg.accumulator.isSome then 1 else 0))) at h7s
    change vk0.constants.getD 8 ("", 0) =
      ("acc_offset", (match gi.cfg.accumulator with
        | some e => BitVec.ofNat 256 e.offset | none => 0)) at h8s
    change vk0.constants.getD 9 ("", 0) =
      ("num_acc_limbs", (match gi.cfg.accumulator with
        | some e => BitVec.ofNat 256 e.numLimbs | none => 0)) at h9s
    change vk0.constants.getD 10 ("", 0) =
      ("num_acc_limb_bits", (match gi.cfg.accumulator with
        | some e => BitVec.ofNat 256 e.numLimbBits | none => 0)) at h10s
    rw [slot 7 (by omega), slot 8 (by omega), slot 9 (by omega), slot 10 (by omega)]
    rw [congrArg Prod.snd h7s, congrArg Prod.snd h8s, congrArg Prod.snd h9s,
      congrArg Prod.snd h10s]
    rw [hs.noAcc]
    simp [accWordsOfEncoding]

theorem env_vkDigest (hg : Generates gi o) (hs : SupportedInput gi) :
    ((renderOf gi o).pv.vk.constants.getD 0 ("", 0)).2 = frWord gi.vk.transcriptRepr := by
  show Midfall.LoweringV3.payloadWord (renderOf gi o).pv
    Midfall.Generator.vkHeaderTemplateSlotsDefault.vkDigest = frWord gi.vk.transcriptRepr
  exact (payload_header hg hs).1

/-! ### K: payload (`PayloadAgrees`), five groups -/

theorem payload_g1Base (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.Lowering.vkG1Words (renderOf gi o).pv Midfall.Lowering.vkG1BaseSlot =
      gi.E.g1.toEip (AdmissiblePairing.g₁ (G₂ := G₂) (Gₜ := Gₜ)) := by
  sorry -- CERT.7

theorem payload_g2Base (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.Lowering.vkG2Words (renderOf gi o).pv Midfall.Lowering.vkG2BaseSlot =
      gi.encG2 (AdmissiblePairing.g₂ (G₁ := G₁) (Gₜ := Gₜ)) := by
  sorry -- CERT.7

theorem payload_negSG2 (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.Lowering.vkG2Words (renderOf gi o).pv Midfall.Lowering.vkNegSG2BaseSlot =
      gi.encG2 (renderOf gi o).sG2gen⁻¹ := by
  sorry -- CERT.7

theorem payload_comms (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.vk.fixedComms.map Midfall.LoweringV2.g1WordsBytes =
      gi.vk.fixedCommitments.toList.map gi.E.g1.toEip ∧
    (renderOf gi o).plan.vk.permutationComms.map Midfall.LoweringV2.g1WordsBytes =
      gi.vk.permutation.commitments.toList.map gi.E.g1.toEip := by
  sorry -- CERT.7

/-! ### S: the one scope clause that mentions the plan -/

theorem supported_layout (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.memory.map.WellFormed ∧
      (renderOf gi o).plan.memory.validate.isOk = true := by
  sorry -- CERT.4

/-! ### The 18-clause text lemmas (scratch section 5) -/

theorem v3_planMeta (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.PlanMeta (renderOf gi o) := by
  sorry -- CERT.1 (suspect: final vs intermediate memory layout)

/-- `newFromVk`'s plan carries the meta and proof layout its own second bind produced. PROVED. -/
theorem newFromVk_plan_meta_proofLayout {F : Type} [BEq F] (feat : Features)
    (field : FieldCtx F) (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta)
    (numInstances : Nat) (accEncoding : Option Midfall.Generator.AccumulatorEncoding)
    (payload : Halo2VerifyingKey) (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk feat field cs rawMeta numInstances accEncoding
        payload = .ok plan) :
    ∃ (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout),
      plan.meta_ = meta_ ∧ plan.proofLayout = L ∧
      ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr meta_.numEvals
        meta_.numPointSets = .ok L := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨proofLayout, hpl, h2⟩ := cert_except_bind_ok h1
  obtain ⟨_qplan, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨_build, _, h4⟩ := cert_except_bind_ok h3
  obtain ⟨_nw, _, h5⟩ := cert_except_bind_ok h4
  obtain ⟨_pcs, _, h6⟩ := cert_except_bind_ok h5
  obtain ⟨_acc, _, h7⟩ := cert_except_bind_ok h6
  obtain ⟨_memory, _, h8⟩ := cert_except_bind_ok h7
  obtain ⟨_op, _, h9⟩ := cert_except_bind_ok h8
  obtain ⟨_trip, _, h10⟩ := cert_except_bind_ok h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals (exact ⟨q.2.1, proofLayout, rfl, rfl, hpl⟩)

theorem v3_layout (hg : Generates gi o) (hs : SupportedInput gi) :
    ProofCalldataLayout.fromProtocol (renderOf gi o).plan.meta_.protocol abiVerifyProofProofCptr
      (renderOf gi o).plan.meta_.numEvals (renderOf gi o).plan.meta_.numPointSets =
      .ok (renderOf gi o).plan.proofLayout := by
  obtain ⟨rawMeta, plan, _hraw, hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  obtain ⟨meta_, L, hmeta, hplL, hL⟩ :=
    newFromVk_plan_meta_proofLayout Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs
      rawMeta gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  rw [hp, hmeta, hplL]
  exact hL

/-- Invert a `validateGeneratorInvariants` success out of a three-arm match. PROVED. -/
theorem except_ok_ok_of_match {α : Type} {e : Except Fault (Except String Unit)}
    {rest : Unit → Except Fault α} {errMsg : String → Fault} {a : α}
    (h : (match e with
      | .ok (.ok u) => rest u
      | .ok (.error err) => .error (errMsg err)
      | .error fault => .error fault) = .ok a) : e = .ok (.ok ()) := by
  cases e with
  | error fault => cases h
  | ok inner =>
      cases inner with
      | error err => cases h
      | ok u =>
          cases u
          rfl

/-- `newFromVk` returns only after `validateGeneratorInvariants` has accepted. PROVED. -/
theorem newFromVk_validate {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding)
    (payload : Halo2VerifyingKey) (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk feat field cs rawMeta numInstances accEncoding
        payload = .ok plan) :
    plan.validateGeneratorInvariants = .ok (.ok ()) := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨_q, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨_proofLayout, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨_qplan, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨_build, _, h4⟩ := cert_except_bind_ok h3
  obtain ⟨_nw, _, h5⟩ := cert_except_bind_ok h4
  obtain ⟨_pcs, _, h6⟩ := cert_except_bind_ok h5
  obtain ⟨_acc, _, h7⟩ := cert_except_bind_ok h6
  obtain ⟨_memory, _, h8⟩ := cert_except_bind_ok h7
  obtain ⟨_op, _, h9⟩ := cert_except_bind_ok h8
  obtain ⟨_trip, _, h10⟩ := cert_except_bind_ok h9
  split at h10
  · split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;>
      (try (split at h10)) <;> (try (split at h10))
    all_goals (try (cases h10))
    all_goals (try assumption)
    all_goals (try (simp_all))
  · cases h10
  · cases h10

theorem v3_invariants (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.validateGeneratorInvariants = .ok (.ok ()) := by
  obtain ⟨_m0, _payload, _, _, _, h4⟩ := generate_spec hg
  simp only [generateAll, Bind.bind, Except.bind] at h4
  obtain ⟨_rawMeta, _, h1⟩ := cert_except_bind_ok h4
  obtain ⟨plan, hpl, h2⟩ := cert_except_bind_ok h1
  obtain ⟨_blocks, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨_model, _, h4'⟩ := cert_except_bind_ok h3
  cases hv : (Halo2Verifier.validateLayout _model) with
  | error e => simp only [hv] at h4'; cases h4'
  | ok u =>
      simp only [hv] at h4'
      have hA : { plan := plan, qblocks := _blocks, model := _model } = o.out :=
        Except.ok.inj (show Except.ok { plan := plan, qblocks := _blocks, model := _model } =
          Except.ok o.out from h4')
      have hp : plan = o.out.plan := congrArg GenOut.plan hA
      change o.out.plan.validateGeneratorInvariants = .ok (.ok ())
      rw [← hp]
      exact newFromVk_validate Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs
        _rawMeta gi.cfg.numInstances gi.cfg.accumulator _payload plan hpl

theorem v3_model (hg : Generates gi o) (hs : SupportedInput gi) :
    generateVerifierFromPlan (fun _ _ => (renderOf gi o).qblocks) (renderOf gi o).inputs
      (renderOf gi o).flags (renderOf gi o).plan = .ok (renderOf gi o).model := by
  obtain ⟨_m0, _payload, _, _, _, h4⟩ := generate_spec hg
  simp only [generateAll, Bind.bind, Except.bind] at h4
  obtain ⟨_rawMeta, _, h1⟩ := cert_except_bind_ok h4
  obtain ⟨plan, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨blocks, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨model, hgen, h4'⟩ := cert_except_bind_ok h3
  cases hv : (Halo2Verifier.validateLayout model) with
  | error e => simp only [hv] at h4'; cases h4'
  | ok u =>
      simp only [hv] at h4'
      have hA : { plan := plan, qblocks := blocks, model := model } = o.out :=
        Except.ok.inj (show Except.ok { plan := plan, qblocks := blocks, model := model } =
          Except.ok o.out from h4')
      change generateVerifierFromPlan (fun _ _ => o.out.qblocks)
        (artifactInputsOf gi o.fingerprint) gi.flags o.out.plan = .ok o.out.model
      rw [← hA]
      exact hgen

theorem v3_codegen (hg : Generates gi o) (hs : SupportedInput gi) :
    CodegenAgrees (renderOf gi o).pv (renderOf gi o).model := by
  sorry -- CERT.2

theorem v3_closed (hg : Generates gi o) (hs : SupportedInput gi) :
    mainClosed (renderOf gi o).pv (renderOf gi o).model = true := by
  sorry -- CERT.5

theorem v3_exitDiscipline (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.ExitDiscipline ((renderOf gi o).prog 0 0) := by
  sorry -- CERT.5

theorem v3_noShadow (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.noShadowB (renderOf gi o) = true := by
  sorry -- CERT.5

theorem v3_cdBound (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.proofLayout.proofEnd + 32 + 32 * gi.cfg.numInstances < 2 ^ 256 := by
  sorry -- CERT.1 (suspect: no generator check bounds proofEnd)

theorem v3_payload (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.PayloadAgrees (renderOf gi o) :=
  let h := payload_header hg hs
  { digest := h.1
    numInstances := by
      apply BitVec.eq_of_toNat_eq
      change (Midfall.LoweringV3.payloadWord (renderOf gi o).pv
        Midfall.Generator.vkHeaderTemplateSlotsDefault.numInstances).toNat =
          (BitVec.ofNat 256 gi.cfg.numInstances).toNat
      rw [h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.sizeBound.1; omega)]
    k := by
      apply BitVec.eq_of_toNat_eq
      change (Midfall.LoweringV3.payloadWord (renderOf gi o).pv
        Midfall.Generator.vkHeaderTemplateSlotsDefault.k).toNat =
          (BitVec.ofNat 256 gi.vk.domain.k).toNat
      rw [h.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.sizeBound.2; omega)]
    nInv := h.2.2.2.1
    omega := h.2.2.2.2.1
    omegaInv := h.2.2.2.2.2.1
    omegaInvToL := h.2.2.2.2.2.2.1
    accWords := h.2.2.2.2.2.2.2
    constantsLength := payload_constantsLength hg hs
    g1Base := payload_g1Base hg hs
    g2Base := payload_g2Base hg hs
    negSG2 := payload_negSG2 hg hs
    fixedComms := (payload_comms hg hs).1
    permutationComms := (payload_comms hg hs).2 }

theorem v3_pins_of_valid {R : Render p G₁ G₂ Gₜ} (h : Midfall.LoweringV3.ValidV3 R) :
    (∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t) ∧
      Midfall.LoweringV2.vkPins R ∧ Midfall.LoweringV2.vkProgressPins R := by
  sorry -- CERT.6 (corollary of the one text, not of generation)

/-! ### D-CERT1: the eight currently-uncovered `programOk` conjuncts -/

/-- D-CERT1 / CERT.6: `intermediateSets` has a point set of size at least two. -/
theorem prog_hasMultiPointSet (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.hasMultiPointSet (renderOf gi o).pv = true := by
  sorry -- CERT.6 (D4)

/-- D-CERT1 / CERT.6: the transcript window holds the longest absorb run and meets no walk
    window (the PG-TPBUF clause is a program obligation, not a consequence of `WellFormed`). -/
theorem prog_transcriptRegionOk (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.transcriptRegionOk (renderOf gi o).pv gi.cfg.numInstances = true := by
  sorry -- CERT.6 (D4)

/-- D-CERT1 / CERT.6: the `g1_identity` window lies above the zero floor (PG-G1ID). -/
theorem prog_g1IdentityFloor (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.g1IdentityFloor (renderOf gi o).pv = true := by
  sorry -- CERT.6 (D4)

/-- D-CERT1 / CERT.6: at least two Lagrange denominators (PG-NEGLAG). -/
theorem prog_negLagrangesFloor (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.negLagrangesFloor (renderOf gi o).pv = true := by
  sorry -- CERT.6 (D4)

/-- D-CERT1 / CERT.6: one sigma commitment per permutation column (D-P59's repair). -/
theorem prog_permCommMatchRepaired (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.permCommMatchRepaired (renderOf gi o).vk = true := by
  sorry -- CERT.6 (D4)

/-- D-CERT1 / CERT.5: `gas()` occurs only as a call's gas argument (D-P71 addition 1). -/
theorem prog_gasCallOk (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.GasCallOk ((renderOf gi o).prog 0 0) := by
  sorry -- CERT.5 (D3)

/-- D-CERT1 / CERT.5: the whole program executes no `gas()` at all (D-GATE1). -/
theorem prog_gasFree (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.GasFree ((renderOf gi o).prog 0 0) := by
  sorry -- CERT.5 (D3)

/-- D-CERT1 / CERT.6: the address-fit invariant (D-QVM1), VK window and quotient interpreter. -/
theorem prog_programFits (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.programFits (renderOf gi o).pv (renderOf gi o).model := by
  sorry -- CERT.6 (D4)

end Clauses

/-! ## 4. THE CERTIFIED GENERATOR (the current `ValidV3`) -/

theorem band {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp [ha, hb]

/-- The `constsCoherent` conjunct, assembled from the five scratch lemmas. PROVED. -/
theorem constsCoherent_of_parts {pv : PlanView} {m : Model}
    (h1 : m.quotientDirect.isNone = true)
    (h2 : Midfall.LoweringV3.constLinesLiteral m = true)
    (h3 : (Midfall.LoweringV2.constTableOf m ==
      Midfall.LoweringV3.expectedConsts pv m) = true)
    (h4 : decide (((Midfall.LoweringV3.expectedConsts pv m).map Prod.fst).Nodup) = true)
    (h5 : ((Midfall.LoweringV2.freeNames (abiGuardBlock m ++ mainAsmRaw pv m)).filter
        fun x => x != "vk" && x != "quotientEvaluator").all
      (fun x => ((Midfall.LoweringV3.expectedConsts pv m).map Prod.fst).contains x) = true) :
    Midfall.LoweringV3.constsCoherent pv m = true := by
  unfold Midfall.LoweringV3.constsCoherent Midfall.LoweringV3.progConstNames
  simp only [h1, h2, h3, h4, h5, Bool.and_self]

/-- The fourteen-conjunct `programOkB` bundle, assembled from its parts. PROVED. -/
theorem programOkB_of_parts {R : Render p G₁ G₂ Gₜ}
    (h1 : codegenStruct (mainAsmRaw R.pv R.model) R.model = true)
    (h2 : codegenAgrees R.pv R.model = true)
    (h3 : Midfall.LoweringV3.constsCoherent R.pv R.model = true)
    (h4 : Midfall.LoweringV3.callsResolved (mainAsmRaw R.pv R.model) = true)
    (h5 : Midfall.LoweringV3.noShadowProg (Midfall.LoweringV2.constTableOf R.model)
      (abiGuardBlock R.model ++ wrapperLocals R.model 0 0 ++ mainAsmRaw R.pv R.model) = true)
    (h6 : Midfall.LoweringV3.noShadowCore R.pv R.model = true)
    (h7 : mainClosed R.pv R.model = true)
    (h8 : decide (0x80 ≤ R.pv.memory.transcriptMptr) = true)
    (h9 : Midfall.LoweringV3.cdBoundB R.pv R.cfg.numInstances = true)
    (h10 : Midfall.LoweringV3.hasMultiPointSet R.pv = true)
    (h11 : Midfall.LoweringV3.transcriptRegionOk R.pv R.cfg.numInstances = true)
    (h12 : Midfall.LoweringV3.g1IdentityFloor R.pv = true)
    (h13 : Midfall.LoweringV3.negLagrangesFloor R.pv = true)
    (h14 : Midfall.LoweringV3.permCommMatchRepaired R.vk = true) :
    Midfall.LoweringV3.programOkB R = true := by
  unfold Midfall.LoweringV3.programOkB Midfall.LoweringV3.programOkCore
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.and_self]

/-- `Nat` below `2^256` read back from `BitVec.ofNat 256`. PROVED. -/
theorem bitvec_ofNat_toNat {n : Nat} (h : n < 2 ^ 256) :
    (BitVec.ofNat 256 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- **`generator_certified`.** Generation succeeded on a supported input ⇒ the render it
    determines satisfies the CURRENT `Midfall.LoweringV3.ValidV3`. PROVED from section 3 (no
    `sorry` of its own). -/
theorem generator_certified (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o)
    (hs : SupportedInput gi) : Midfall.LoweringV3.ValidV3 (renderOf gi o) where
  generated := generated_of hg
  inputs := ⟨rfl, rfl, rfl, rfl⟩
  program :=
    let hb := programOkB_of_parts
      (prog_codegenStruct hg hs)
      (v3_codegen hg hs)
      (constsCoherent_of_parts (prog_noDirect hg hs) (prog_constLinesLiteral hg hs)
        (prog_constTable hg hs) (prog_constNodup hg hs) (prog_constsDeclared hg hs))
      (prog_callsResolved hg hs)
      (prog_noShadow hg hs)
      (v3_noShadow hg hs)
      (v3_closed hg hs)
      (prog_transcriptFloor hg hs)
      (by
        show decide (Midfall.LoweringV3.cdBoundB (renderOf gi o).pv
          (renderOf gi o).cfg.numInstances) = true
        unfold Midfall.LoweringV3.cdBoundB
        change decide ((renderOf gi o).plan.proofLayout.proofEnd + 32 +
          32 * gi.cfg.numInstances < 2 ^ 256) = true
        exact decide_eq_true (v3_cdBound hg hs))
      (prog_hasMultiPointSet hg hs)
      (prog_transcriptRegionOk hg hs)
      (prog_g1IdentityFloor hg hs)
      (prog_negLagrangesFloor hg hs)
      (prog_permCommMatchRepaired hg hs)
    ⟨hb, prog_gasCallOk hg hs, prog_gasFree hg hs, v3_exitDiscipline hg hs,
      prog_programFits hg hs⟩
  noWriters := prog_noWriters hg hs
  env :=
    { modulus := hs.modulus, truncWidth := hs.truncWidth
      domainN := ⟨hs.domainN, env_k hg hs⟩, baryWeight := hs.baryWeight
      omegaInvMul := hs.omegaInvMul, omegaOrder := hs.omegaOrder
      negLagranges := env_negLagranges hg hs, nG2 := env_nG2 hg hs, sG2 := rfl
      vkDigestWord := env_vkDigest hg hs }
  payload := v3_payload hg hs
  supported :=
    { advice := hs.advice, instShape := hs.instShape, noRotInst := hs.noRotInst
      singlePhase := hs.singlePhase, hLimbs := hs.hLimbs, vkPoints := hs.vkPoints
      layout := supported_layout hg hs, production := hs.production, wf := hs.wf
      noAcc := hs.noAcc, embeddedQuotient := hs.embeddedQuotient, separateVk := hs.separateVk }

/-! ## 5. THE HEADLINE -/

/-- **`generator_correct`, hypothetical-root form.** `lowering_correct` over the current
    `ValidV3` is a hypothesis; this is the statement `CERT.H` turns into the real root. -/
theorem generator_correct
    (lowering_correct : ∀ (R : Render p G₁ G₂ Gₜ) (product : PairingProduct),
      Midfall.LoweringV3.ValidV3 R → Midfall.LoweringV3.LoweringEquivalenceV3 R product)
    (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o) (hs : SupportedInput gi)
    (product : PairingProduct) :
    Midfall.LoweringV3.LoweringEquivalenceV3 (renderOf gi o) product :=
  lowering_correct _ product (generator_certified gi o hg hs)

/-- **`generator_correct_V3`.** The same with the REAL `lowering_correct` of
    `GeneratorTheorem.lean`. No hypothesis mentions the plan, the model or the program. -/
theorem generator_correct_V3 (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o)
    (hs : SupportedInput gi) (product : PairingProduct) :
    Midfall.LoweringV3.LoweringEquivalenceV3 (renderOf gi o) product :=
  Midfall.LoweringV3.lowering_correct _ product (generator_certified gi o hg hs)

end Midfall.Generator.Certified

#check @Midfall.Generator.Certified.generator_certified
#check @Midfall.Generator.Certified.generator_correct_V3
#print axioms Midfall.Generator.Certified.generate_spec
#print axioms Midfall.Generator.Certified.generator_certified
#print axioms Midfall.Generator.Certified.generator_correct_V3
#cone_sorries Midfall.Generator.Certified.generator_certified
#cone_report Midfall.Generator.Certified.generator_certified under []

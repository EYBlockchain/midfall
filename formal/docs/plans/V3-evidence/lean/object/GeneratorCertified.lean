/-
  GeneratorCertified.lean  (SCRATCH - certifying the code generator)

  THE CERTIFIED-GENERATOR STATEMENT: one theorem whose only hypotheses are on the generator's
  INPUT. For every input in a decidable supported class, if the generator returns an output, the
  render that output determines satisfies `Render.ValidV3` (ObjectV3Full.lean:762), and therefore
  (given the headline `lowering_correct`) the program in it is correct.

  Compiled like a file of `lean/object/` that comes after `ObjectV3Full`, with the statements
  area on the path as well (for `LoweringEquivalenceV3`, the 18-clause `LoweringV3.ValidV3` and
  `LoweringV3.lowering_correct` of `GeneratorTheorem.lean`):

      LEAN_PATH="$BASE_LP:$OUT/object:$OUT/statements" lake env lean GeneratorCertified.lean

  Sections
   1. The generator's input (`GenInput`), the whole generator (`generate` = `generate_vk` then
      `generateAll`), and `renderOf`.
   2. `SupportedInput`: the scope, input-only.
   3. One lemma statement per output-side clause of `Render.ValidV3` (and per sub-clause of
      `programOk`); each `sorry` is the body of a named theorem.
   4. `generator_certified`, PROVED from section 3.
   5. The 18-clause text (`LoweringV3.ValidV3`): the extra clauses, and `generator_certified_V3`.
   6. `generator_correct`, the headline with input-only hypotheses.
-/
import ObjectV3Full
import GeneratorTheorem
set_option autoImplicit false

namespace Midfall.LoweringV2.Certified

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
    the SRS; `generateAll` (ObjectV3Full.lean:585) takes it from there. The payload is NOT an
    input: ObjectV3Full 7.7 measured that `generateAll` accepts a payload whose omega word is
    flipped, so with the payload as input `PayloadAgrees` is false for some succeeding run. -/
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

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
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
  obtain ⟨m0, h1, h⟩ := except_bind_ok h
  obtain ⟨payload, h2, h⟩ := except_bind_ok h
  obtain ⟨fp, h3, h⟩ := except_bind_ok h
  obtain ⟨out, h4, h⟩ := except_bind_ok h
  cases h
  exact ⟨m0, payload, h1, h2, h3, h4⟩

/-! ## 2. The supported class, input-only -/

/-- **THE SUPPORTED CLASS.** Every clause mentions only the input. Clauses 1-11 are
    `SupportedV2` (Statements.lean:118-134) verbatim with `R.` read as `gi.`, minus `layout`,
    which mentions the plan and follows from generation (`supported_layout`). `wfV3` is
    `SupportedV3.wf` (StatementsV3.lean:602); the reconciliation keeps one of `wf` / `wfV3`.
    Then the input-only half of `EnvAgrees` (Inv.lean:533-579), the codec agreement between the
    generator's encoders and the Lean verifier's, and the delta literal. -/
structure SupportedInput (gi : GenInput p G₁ G₂ Gₜ) : Prop where
  advice : gi.vk.cs.numAdviceColumns ≠ 0
  instShape : gi.vk.cs.numInstanceColumns = 2 ∧ gi.cfg.numCommittedInstances = 1
  noRotInst : ∀ q ∈ gi.vk.cs.instanceQueries.toList, q.2.int = 0
  singlePhase : gi.vk.cs.numChallenges = 0
  hLimbs : gi.vk.domain.getQuotientPolyDegree = gi.vk.csDegree - 1
  vkPoints : ∀ C ∈ gi.vk.fixedCommitments.toList ++ gi.vk.permutation.commitments.toList,
    ptReadable (gi.E.g1.toEip C)
  production : gi.flags.trace = false ∧ gi.flags.gasCheckpoints = false
  wf : gi.vk.WellFormed Features.solidity
  wfV3 : Midfall.LoweringV3.WellFormedV3 gi.vk Features.solidity
  noAcc : gi.cfg.accumulator = none
  embeddedQuotient : gi.flags.externalQuotient = false ∧ gi.flags.expectedQuotient = none
  separateVk : gi.flags.separate = true
  /-- `EnvAgrees.modulus`. -/
  modulus : p = frModulusConstant
  /-- `EnvAgrees.truncWidth`. -/
  truncWidth : Midfall.Halo2.divCeil (Midfall.Halo2.divCeil gi.E.field.numBits 8) 2 = 16
  /-- `EnvAgrees.domainN`, first half (the second is a builder fact, `env_k`). -/
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
  /-- SIZE BOUND (new; no existing clause). Rust computes these in `usize` (64 bits) and the
      header words as `U256::from(usize)` (vk.rs:110-111); the port computes in `Nat` and writes
      `BitVec.ofNat 256`, which wraps. Without it `payload_header`'s `numInstances` conjunct is
      false for `numInstances ≥ 2^256`. It does NOT give `v3_cdBound` (that also needs a bound on
      the proof length, i.e. on the circuit's commitment and evaluation counts). -/
  sizeBound : gi.cfg.numInstances < 2 ^ 64 ∧ gi.vk.domain.k < 64

/-! ## 3. One lemma per output-side clause. Every `sorry` below is the body of the named
    theorem; the tag after it is the T2 class (cert.md §2). -/

section Clauses
variable {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}

/-! ### G: generated -/

/-- `newFromVk` stores the payload it is given (`LoweringPlan.mk vk …`, ObjectV3Full.lean:538),
    and `generateAll` returns that plan. -/
theorem plan_vk_of_generateAll {delta : Fr p} {vk : VerifyingKey (Fr p) G₁} {cfg : GeneratorConfig}
    {payload : Halo2VerifyingKey} {inputs : ArtifactBuildInputs} {flags : RenderFlags}
    {out : GenOut}
    (h : generateAll Features.solidity delta vk cfg payload inputs flags = .ok out) :
    out.plan.vk = payload := by
  sorry -- (c) S: unfold generateAll / newFromVk, nine binds

/-! ### P: the program clause, `programOk` = six conjuncts, the second one of five -/

/-- P1. FALSE TODAY for every input (measured at the fixture: first statement difference at
    index 9, the accumulator helpers). Provable once `mainAsmRaw` is the WP-G1 emitter. -/
theorem prog_codegenStruct (hg : Generates gi o) (hs : SupportedInput gi) :
    codegenStruct (mainAsmRaw (renderOf gi o).pv) (renderOf gi o).model = true := by
  sorry -- (e) today / G1 route B or C after WP-G1

/-- P2a. A VM-lowered plan renders no Direct section. -/
theorem prog_noDirect (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).model.quotientDirect.isNone = true := by
  sorry -- (c) S: newFromVk sets `direct := none`; ART builder copies it

/-- P2b. Every `uint256 internal constant` line of `renderConstants` has a literal right side. -/
theorem prog_constLinesLiteral (hg : Generates gi o) (hs : SupportedInput gi) :
    constLinesLiteral (renderOf gi o).model = true := by
  sorry -- (b) S-M: induction over the Constants.sol renderer's interpolations (hexFilter/toString)

/-- P2c. The table read back from the rendered text IS the data table of the plan view. -/
theorem prog_constTable (hg : Generates gi o) (hs : SupportedInput gi) :
    (constTableOf (renderOf gi o).model ==
      expectedConsts (renderOf gi o).pv (renderOf gi o).model) = true := by
  sorry -- (c)+(d) M: renderConstants vs expectedConsts, and solConstantLine? ∘ hexFilter = id

/-- P2d. No constant name twice. -/
theorem prog_constNodup (hg : Generates gi o) (hs : SupportedInput gi) :
    decide (((expectedConsts (renderOf gi o).pv (renderOf gi o).model).map Prod.fst).Nodup)
      = true := by
  sorry -- (c) S: the names are literals of `expectedConsts`; two optional arms, a case split

/-- P2e. Every name the program reads is a declared constant (or a wrapper local). -/
theorem prog_constsDeclared (hg : Generates gi o) (hs : SupportedInput gi) :
    ((freeNames (abiGuardBlock (renderOf gi o).model ++ mainAsmRaw (renderOf gi o).pv)).filter
        fun x => x != "vk" && x != "quotientEvaluator").all
      (fun x => ((expectedConsts (renderOf gi o).pv (renderOf gi o).model).map Prod.fst).contains x)
      = true := by
  sorry -- (b) M: free-name lemma per emitter, against the fixed name list

/-- P3. Every user call resolves to a top-level definition of the same arity. -/
theorem prog_callsResolved (hg : Generates gi o) (hs : SupportedInput gi) :
    callsResolved (mainAsmRaw (renderOf gi o).pv) = true := by
  sorry -- (b) M: call-site lemma per emitter + the helper signature table

/-- P4. No binder is a constant name. -/
theorem prog_noShadow (hg : Generates gi o) (hs : SupportedInput gi) :
    noShadow (constTableOf (renderOf gi o).model)
      (abiGuardBlock (renderOf gi o).model ++ wrapperLocals (renderOf gi o).model 0 0 ++
        mainAsmRaw (renderOf gi o).pv) = true := by
  sorry -- (b) S-M: binder lemma per emitter (binders are emitter literals or `q_*`/`t*` names)

/-- P5. After inlining only the two wrapper locals are free. -/
theorem prog_closed (hg : Generates gi o) (hs : SupportedInput gi) :
    (freeNames (Inline.inlineContractConstants (constTableOf (renderOf gi o).model)
        (abiGuardBlock (renderOf gi o).model ++ mainAsmRaw (renderOf gi o).pv))).all
      (fun x => x == "vk" || x == "quotientEvaluator") = true := by
  sorry -- (b) S: from P2e + P2c + an `inlineContractConstants` free-name lemma

/-- P6. The transcript base is above Solidity's reserved words. -/
theorem prog_transcriptFloor (hg : Generates gi o) (hs : SupportedInput gi) :
    decide (0x80 ≤ (renderOf gi o).pv.memory.transcriptMptr) = true := by
  sorry -- (a) S: `memory.validate` (Layout.lean:1031) pins transcript_mptr = TRANSCRIPT_BUFFER_START

/-! ### P: no writers -/

theorem prog_noWriters (hg : Generates gi o) (hs : SupportedInput gi) :
    NoWriters ((renderOf gi o).prog 0 0) := by
  sorry -- (b) M: scan lemma per emitter; inlining substitutes literals only

/-! ### K: environment (the plan-side half of `EnvAgrees`) -/

theorem env_k (hg : Generates gi o) (hs : SupportedInput gi) :
    gi.vk.domain.k = (renderOf gi o).pv.k := by
  sorry -- (c) S: pv.k = model.k = inputs.k (ART:281) = vk.domain.k (artifactInputsOf)

theorem env_negLagranges (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).pv.numNegLagranges = gi.vk.cs.blindingFactors.toOption.getD 0 + 1 := by
  sorry -- (c) S: ART builder (mod.rs:509-515) from the plan meta; meta = ConstraintSystemMeta.new

theorem env_nG2 (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).params.nG2Prepared = P.g₂⁻¹ := by
  sorry -- (a) S: generate_base_vk checks `g2 == G2Affine::generator()` (vk.rs:180, Vk.lean:806)

theorem env_vkDigest (hg : Generates gi o) (hs : SupportedInput gi) :
    ((renderOf gi o).pv.vk.constants.getD 0 ("", 0)).2 = frWord gi.vk.transcriptRepr := by
  sorry -- (c)+(d) S: header slot 0 survives generate_vk's reservation loop; feToU256 ∘ frToRepr = frWord

/-! ### K: payload (`PayloadAgrees`, ObjectV3Full.lean:687), five groups -/

theorem payload_header (hg : Generates gi o) (hs : SupportedInput gi) :
    payloadWord (renderOf gi o).plan.vk 0 = frWord gi.vk.transcriptRepr ∧
    (payloadWord (renderOf gi o).plan.vk 1).toNat = gi.cfg.numInstances ∧
    (payloadWord (renderOf gi o).plan.vk 2).toNat = gi.vk.domain.k ∧
    payloadWord (renderOf gi o).plan.vk 3 = frWord (((2 ^ gi.vk.domain.k : ℕ) : Fr p)⁻¹) ∧
    payloadWord (renderOf gi o).plan.vk 4 = frWord gi.vk.domain.omega ∧
    payloadWord (renderOf gi o).plan.vk 5 = frWord gi.vk.domain.omegaInv ∧
    payloadWord (renderOf gi o).plan.vk 6 =
      frWord (gi.vk.domain.omegaInv ^ (renderOf gi o).plan.meta_.rotationLast.natAbs) ∧
    ((payloadWord (renderOf gi o).plan.vk 7).toNat, (payloadWord (renderOf gi o).plan.vk 8).toNat,
      (payloadWord (renderOf gi o).plan.vk 9).toNat,
      (payloadWord (renderOf gi o).plan.vk 10).toNat) = accWordsOfEncoding gi.cfg.accumulator := by
  sorry -- (c)+(d) M: VkHeaderBuilder slots (vk.rs:211-222); feToU256 ∘ frToRepr = frWord; < 2^256
        --   for numInstances/k by `sizeBound`; rotationLast kept by the two meta setters

theorem payload_g1Base (hg : Generates gi o) (hs : SupportedInput gi) :
    vkG1Words (renderOf gi o).pv vkG1BaseSlot =
      gi.E.g1.toEip (AdmissiblePairing.g₁ (G₂ := G₂) (Gₜ := Gₜ)) := by
  sorry -- (c)+(d) S: slot 11 written from `P.g₁` (Vk.lean:802) + `g1Codec`

theorem payload_g2Base (hg : Generates gi o) (hs : SupportedInput gi) :
    vkG2Words (renderOf gi o).pv vkG2BaseSlot =
      gi.encG2 (AdmissiblePairing.g₂ (G₁ := G₁) (Gₜ := Gₜ)) := by
  sorry -- (a)+(d) S: vk.rs:180 (`g2 == generator`) + `g2Codec`

theorem payload_negSG2 (hg : Generates gi o) (hs : SupportedInput gi) :
    vkG2Words (renderOf gi o).pv vkNegSG2BaseSlot = gi.encG2 (renderOf gi o).sG2gen⁻¹ := by
  sorry -- (c)+(d) S: slot 23 written from `s_g2⁻¹` (Vk.lean:804), sG2gen := srs.sG2, `g2Codec`

theorem payload_comms (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.vk.fixedComms.map LoweringV2.g1WordsBytes =
      gi.vk.fixedCommitments.toList.map gi.E.g1.toEip ∧
    (renderOf gi o).plan.vk.permutationComms.map LoweringV2.g1WordsBytes =
      gi.vk.permutation.commitments.toList.map gi.E.g1.toEip := by
  sorry -- (c)+(d) S-M: generate_base_vk mapM (Vk.lean:855-858), untouched by the reservation
        --   loop and the write-back (which index `constants` only), + `g1Codec`

/-! ### S: the one scope clause that mentions the plan -/

theorem supported_layout (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.memory.map.WellFormed ∧
      (renderOf gi o).plan.memory.validate.isOk = true := by
  sorry -- (a) S: validateGeneratorInvariants (LoweringPlan.lean:538) runs memory.validate, which
        --   ends in MemoryMap.validate (Layout.lean:1076); validate ⇒ wellFormedBool (Layout.lean:1112)

end Clauses

/-! ## 4. THE CERTIFIED GENERATOR (object text, seven clauses) -/

theorem band {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp [ha, hb]

/-- The generated-by clause. PROVED from `generate_spec` and `plan_vk_of_generateAll`. -/
theorem generated_of {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut} (hg : Generates gi o) :
    (renderOf gi o).GeneratedBy := by
  obtain ⟨_, payload, _, _, _, h4⟩ := generate_spec hg
  have hv : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  refine ⟨o.out, ?_, rfl, rfl, rfl⟩
  show generateAll Features.solidity gi.E.delta gi.vk gi.cfg o.out.plan.vk
    (artifactInputsOf gi o.fingerprint) gi.flags = .ok o.out
  rw [hv]; exact h4

/-- **`generator_certified`.** Generation succeeded on a supported input ⇒ the render it
    determines is valid. PROVED from the section-3 lemmas (no `sorry` of its own). -/
theorem generator_certified (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o)
    (hs : SupportedInput gi) : (renderOf gi o).ValidV3 where
  generated := generated_of hg
  inputs := ⟨rfl, rfl, rfl, rfl⟩
  program := by
    unfold programOk programOkWith constsCoherentWith
    exact band (band (band (band (band (prog_codegenStruct hg hs)
      (band (band (band (band (prog_noDirect hg hs) (prog_constLinesLiteral hg hs))
        (prog_constTable hg hs)) (prog_constNodup hg hs)) (prog_constsDeclared hg hs)))
      (prog_callsResolved hg hs)) (prog_noShadow hg hs)) (prog_closed hg hs))
      (prog_transcriptFloor hg hs)
  noWriters := prog_noWriters hg hs
  env :=
    { modulus := hs.modulus, truncWidth := hs.truncWidth
      domainN := ⟨hs.domainN, env_k hg hs⟩, baryWeight := hs.baryWeight
      omegaInvMul := hs.omegaInvMul, omegaOrder := hs.omegaOrder
      negLagranges := env_negLagranges hg hs, nG2 := env_nG2 hg hs, sG2 := rfl
      vkDigestWord := env_vkDigest hg hs }
  payload :=
    have h := payload_header hg hs
    { digest := h.1, numInstances := h.2.1, k := h.2.2.1, nInv := h.2.2.2.1
      omega := h.2.2.2.2.1, omegaInv := h.2.2.2.2.2.1, omegaInvToL := h.2.2.2.2.2.2.1
      accWords := h.2.2.2.2.2.2.2
      g1Base := payload_g1Base hg hs, g2Base := payload_g2Base hg hs
      negSG2 := payload_negSG2 hg hs
      fixed := (payload_comms hg hs).1, perm := (payload_comms hg hs).2 }
  supported :=
    { advice := hs.advice, instShape := hs.instShape, noRotInst := hs.noRotInst
      singlePhase := hs.singlePhase, hLimbs := hs.hLimbs, vkPoints := hs.vkPoints
      layout := supported_layout hg hs, production := hs.production, wf := hs.wf
      noAcc := hs.noAcc, embeddedQuotient := hs.embeddedQuotient, separateVk := hs.separateVk }

/-! ## 5. The 18-clause text (`LoweringV3.ValidV3`, StatementsV3.lean:613) -/

section V3
variable {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}

theorem v3_planMeta (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.PlanMeta (renderOf gi o) := by
  sorry -- (e)-suspect: Data.new is given the FINAL memory, Rust the intermediate default-config
        --   layout (StatementsV3.lean:313-318); equal at F1 only. Restate as an equation with newFromVk.

theorem v3_layout (hg : Generates gi o) (hs : SupportedInput gi) :
    ProofCalldataLayout.fromProtocol (renderOf gi o).plan.meta_.protocol abiVerifyProofProofCptr
      (renderOf gi o).plan.meta_.numEvals (renderOf gi o).plan.meta_.numPointSets =
      .ok (renderOf gi o).plan.proofLayout := by
  sorry -- (c) S: newFromVk computes proofLayout exactly so (ObjectV3Full.lean:521)

theorem v3_invariants (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.validateGeneratorInvariants = .ok (.ok ()) := by
  sorry -- (a) S: plan.rs:307-308, checked in newFromVk (ObjectV3Full.lean:542)

theorem v3_model (hg : Generates gi o) (hs : SupportedInput gi) :
    generateVerifierFromPlan (fun _ _ => (renderOf gi o).qblocks) (renderOf gi o).inputs
      (renderOf gi o).flags (renderOf gi o).plan = .ok (renderOf gi o).model := by
  sorry -- (c) S: generateAll's third bind (ObjectV3Full.lean:597)

/-- FALSE TODAY (measured, `codegenAgrees = false`, first token difference 1333). -/
theorem v3_codegen (hg : Generates gi o) (hs : SupportedInput gi) :
    CodegenAgrees (renderOf gi o).pv (renderOf gi o).model := by
  sorry -- (e) today; after WP-G1: from P1 + `yulTokens (print (parse ts)) = ts` (route C lemma)

theorem v3_closed (hg : Generates gi o) (hs : SupportedInput gi) :
    mainClosed (renderOf gi o).pv (renderOf gi o).model = true := by
  sorry -- (b) S: P5 restricted to the main block

theorem v3_exitDiscipline (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.ExitDiscipline ((renderOf gi o).prog 0 0) := by
  sorry -- (b) M: exit-scan lemma per emitter (only `fail`/`revert` and the final `return`)

theorem v3_noShadow (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.noShadowB (renderOf gi o) = true := by
  sorry -- (b) S: as P4, top-level binders only

theorem v3_cdBound (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.proofLayout.proofEnd + 32 + 32 * gi.cfg.numInstances < 2 ^ 256 := by
  sorry -- (e)-suspect: no generator check bounds proofEnd or numInstances (validate, validateLayout
        --   read); needs an input size bound

theorem v3_payload (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.PayloadAgrees (renderOf gi o) := by
  sorry -- (c)+(d): the same five groups as section 3 at the V3 slot names, plus `delta` = hs.deltaLiteral

/-- The three pin clauses are consequences of the object text, not new obligations. -/
theorem v3_pins_of_valid {R : Render p G₁ G₂ Gₜ} (h : R.ValidV3) :
    (∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t) ∧ vkPins R ∧
      vkProgressPins R := by
  sorry -- (c) S: the six-line script of `ValidV3.vkMptr_const` per name; `disjoint` from the
        --   memory map (a); `vkLen` needs runtimeBytes.size = len + 1 (Models builder)

end V3

theorem generator_certified_V3 (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o)
    (hs : SupportedInput gi) : Midfall.LoweringV3.ValidV3 (renderOf gi o) :=
  have hV := generator_certified gi o hg hs
  have hp := v3_pins_of_valid hV
  { circuitMeta := v3_planMeta hg hs, layout := v3_layout hg hs
    invariants := v3_invariants hg hs, model := v3_model hg hs, inputs := hV.inputs
    codegen := v3_codegen hg hs, closed := v3_closed hg hs, slots := hV.env
    payload := v3_payload hg hs
    supported :=
      { advice := hs.advice, instShape := hs.instShape, noRotInst := hs.noRotInst
        singlePhase := hs.singlePhase, hLimbs := hs.hLimbs, vkPoints := hs.vkPoints
        layout := supported_layout hg hs, production := hs.production, wf := hs.wfV3
        noAcc := hs.noAcc, embeddedQuotient := hs.embeddedQuotient, separateVk := hs.separateVk }
    noWriters := hV.noWriters, exitDiscipline := v3_exitDiscipline hg hs
    noShadow := v3_noShadow hg hs, cdBound := v3_cdBound hg hs
    transcriptMptr := hp.1, vkPins := hp.2.1, vkProgressPins := hp.2.2 }

/-! ## 6. THE HEADLINE WITH INPUT-ONLY HYPOTHESES -/

/-- **`generator_correct`, object text.** `lowering_correct` over the seven-clause `ValidV3` is a
    hypothesis: that theorem lives in the statements area and is stated today over the
    18-clause text (reconciliation card). -/
theorem generator_correct
    (lowering_correct : ∀ (R : Render p G₁ G₂ Gₜ) (product : PairingProduct),
      R.ValidV3 → Midfall.LoweringV3.LoweringEquivalenceV3 R product)
    (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o) (hs : SupportedInput gi)
    (product : PairingProduct) :
    Midfall.LoweringV3.LoweringEquivalenceV3 (renderOf gi o) product :=
  lowering_correct _ product (generator_certified gi o hg hs)

/-- **`generator_correct_V3`.** The same with the REAL `lowering_correct` of
    `GeneratorTheorem.lean:67` (18-clause text). No hypothesis mentions the plan, the model or
    the program. -/
theorem generator_correct_V3 (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut) (hg : Generates gi o)
    (hs : SupportedInput gi) (product : PairingProduct) :
    Midfall.LoweringV3.LoweringEquivalenceV3 (renderOf gi o) product :=
  Midfall.LoweringV3.lowering_correct _ product (generator_certified_V3 gi o hg hs)

end Midfall.LoweringV2.Certified

#check @Midfall.LoweringV2.Certified.generator_certified
#check @Midfall.LoweringV2.Certified.generator_correct_V3
#print axioms Midfall.LoweringV2.Certified.generate_spec
#print axioms Midfall.LoweringV2.Certified.generator_certified
#print axioms Midfall.LoweringV2.Certified.generator_correct_V3

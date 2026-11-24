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
import Midfall.LoweringV3.ParseGas
import Midfall.Generator.Vk
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldCompute
import Midfall.LoweringV2.Consts
import Midfall.Lowering.VkDigest
import Midfall.LoweringV3.LagrangeAlg
import Midfall.LoweringV3.KzgQueryMap
import Midfall.LoweringV3.EndToEndAlgebra
set_option autoImplicit false

namespace Midfall.Generator.Certified

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Generator.PlanNew
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientEvaluator
open Midfall.LoweringV3.TranscriptRows

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

/-! ### D-GATE11: the count budget

`prog_programFits` and `v3_cdBound` are NOT derivable from the pre-D-GATE11 `SupportedInput`: the
constraint system's counts are unbounded `Nat`s, and the layout arithmetic multiplies them by
`G1_BYTES`/`WORD_BYTES`. The clause below bounds every count the two obligations consume, as a
COMPUTATION on the input (`countBoundB`), so a concrete render witnesses it by `native_decide`.
The bound `2 ^ 32` is far above any real circuit (a circuit with 2^32 advice columns would not fit
in a transaction) and far below the `2 ^ 256` the address arithmetic needs; `2 ^ 200` leaves the VK
payload below every `2 ^ 256 - (2 ^ 200 + ...)` balance in the fit. The point-set count is not a
meta field, so it is bounded indirectly: `pcsQueries.length < 2 ^ 32` and
`numPointSets ≤ pcsQueries.length` (`numPointSets_le_pcsQueries`), the number of PCS point sets
never exceeding the number of PCS queries. No row, `ValidV3`, or root hypothesis is touched: this
is an input predicate. -/

/-- The `ConstraintSystemMeta` the generator builds from the input's constraint system, if the
    build succeeds. The D-GATE11 clause reads its counts; `generate_spec` identifies it with the
    `m0` of every successful run. -/
def rawMetaOf (gi : GenInput p G₁ G₂ Gₜ) : Option ConstraintSystemMeta :=
  match ConstraintSystemMeta.new Features.solidity gi.vk.cs gi.cfg.numCommittedInstances with
  | .ok m => some m
  | .error _ => none

/-- D-GATE11's per-count budget on the raw meta. `2 ^ 32` per count (including every list entry),
    which is the smallest round bound that keeps every product in the layout below `2 ^ 256`.
    `pcsQueries` is included because the point-set count is bounded through it, and
    `rotationLast.natAbs` because `batchInvertInputWords` adds it. -/
structure MetaCountsBound (m : ConstraintSystemMeta) : Prop where
  lookups : m.protocol.numLookups < 2 ^ 32
  permutationZs : m.protocol.numPermutationZs < 2 ^ 32
  trashcans : m.protocol.numTrashcans < 2 ^ 32
  quotients : m.protocol.numQuotients < 2 ^ 32
  simpleSelectors : m.numSimpleSelectors < 2 ^ 32
  evals : m.numEvals < 2 ^ 32
  challengeIndices : m.challengeIndices.length < 2 ^ 32
  userAdvicesLen : m.protocol.numUserAdvices.length < 2 ^ 32
  userAdvicesEach : ∀ n ∈ m.protocol.numUserAdvices, n < 2 ^ 32
  lookupChunksLen : m.protocol.lookupChunks.length < 2 ^ 32
  lookupChunksEach : ∀ n ∈ m.protocol.lookupChunks, n < 2 ^ 32
  pcsQueries : m.protocol.pcsQueries.length < 2 ^ 32
  rotationLast : m.rotationLast.natAbs < 2 ^ 32

/-- The `Bool` face of `MetaCountsBound`, for the concrete-count witness (`native_decide`). -/
def metaCountsBoundB (m : ConstraintSystemMeta) : Bool :=
  decide (m.protocol.numLookups < 2 ^ 32) &&
  decide (m.protocol.numPermutationZs < 2 ^ 32) &&
  decide (m.protocol.numTrashcans < 2 ^ 32) &&
  decide (m.protocol.numQuotients < 2 ^ 32) &&
  decide (m.numSimpleSelectors < 2 ^ 32) &&
  decide (m.numEvals < 2 ^ 32) &&
  decide (m.challengeIndices.length < 2 ^ 32) &&
  decide (m.protocol.numUserAdvices.length < 2 ^ 32) &&
  m.protocol.numUserAdvices.all (fun n => decide (n < 2 ^ 32)) &&
  decide (m.protocol.lookupChunks.length < 2 ^ 32) &&
  m.protocol.lookupChunks.all (fun n => decide (n < 2 ^ 32)) &&
  decide (m.protocol.pcsQueries.length < 2 ^ 32) &&
  decide (m.rotationLast.natAbs < 2 ^ 32)

theorem metaCountsBound_of_b {m : ConstraintSystemMeta}
    (h : metaCountsBoundB m = true) : MetaCountsBound m := by
  unfold metaCountsBoundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine { lookups := ?_, permutationZs := ?_, trashcans := ?_, quotients := ?_, simpleSelectors := ?_, evals := ?_, challengeIndices := ?_, userAdvicesLen := ?_, userAdvicesEach := ?_, lookupChunksLen := ?_, lookupChunksEach := ?_, pcsQueries := ?_, rotationLast := ?_ } <;>
    simp_all

/-- `ConstraintSystemMeta.new` copies every count from the protocol plan, so the direct fields the
    memory layout reads agree with the protocol fields the proof layout reads. This is the bridge
    the residual `staticWorkingSetFits` needs (D-GATE11 records it rather than adding a second set
    of duplicated bounds to the clause). PROVED. -/
theorem new_meta_counts_eq {F : Type} (feat : Features) (cs : ConstraintSystem F)
    (nbCommittedInstances : Nat) {m : ConstraintSystemMeta}
    (h : ConstraintSystemMeta.new feat cs nbCommittedInstances = .ok m) :
    m.numLookups = m.protocol.numLookups ∧
      m.numPermutationZs = m.protocol.numPermutationZs ∧
      m.numTrashcans = m.protocol.numTrashcans ∧
      m.numQuotients = m.protocol.numQuotients ∧
      m.numSimpleSelectors = m.protocol.numSimpleSelectors ∧
      m.numUserAdvices = m.protocol.numUserAdvices ∧
      m.lookupChunks = m.protocol.lookupChunks ∧
      m.challengeIndices = m.protocol.challengeIndices ∧
      m.numEvals = m.protocol.numMainEvals := by
  unfold ConstraintSystemMeta.new at h
  simp only [Bind.bind] at h
  obtain ⟨protocol, _, hok⟩ := cert_except_bind_ok h
  cases hok
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The VK payload a run produces, as a computation on the input. `generate`'s first two binds;
    `generate_spec` identifies it with the payload every successful run uses. The D-GATE11 payload
    length bound is stated on this, so it remains an input-only predicate even though the payload
    is generated (there is no payload field in `GenInput`). -/
def payloadOf (gi : GenInput p G₁ G₂ Gₜ) : Option Halo2VerifyingKey :=
  match ConstraintSystemMeta.new Features.solidity gi.vk.cs gi.cfg.numCommittedInstances with
  | .error _ => none
  | .ok m0 =>
    match generateVk Features.solidity (vkBuildEnvOf (frFieldCtx gi.E.delta) gi.vk.cs)
        gi.codecs (buildInputsOf gi m0) with
    | .ok p => some p
    | .error _ => none

/-- The quotient-builder output a plan carries, if it is a VM plan. -/
def quotientBuildOf (L : LoweringPlan Unit Unit) : Option QuotientProgramBuild :=
  L.quotient.map (fun q => q.build)

/-- The D-GATE11 input clause: the generated VK payload and every count the layout arithmetic
    consumes. `payloadOf` is a computation on `gi`, so this is still an input predicate. -/
structure CountBound (gi : GenInput p G₁ G₂ Gₜ) : Prop where
  payload : ∀ p, payloadOf gi = some p → p.len < 2 ^ 200
  instances : gi.cfg.numInstances < 2 ^ 32
  metaCounts : ∀ m, rawMetaOf gi = some m → MetaCountsBound m

/-- The `Bool` face of `CountBound`; the concrete-count witness at F1 is `native_decide` on this. -/
def countBoundB (gi : GenInput p G₁ G₂ Gₜ) : Bool :=
  decide (gi.cfg.numInstances < 2 ^ 32) &&
  (match payloadOf gi with | some p => decide (p.len < 2 ^ 200) | none => true) &&
  (match rawMetaOf gi with | some m => metaCountsBoundB m | none => true)

theorem countBound_of_b {gi : GenInput p G₁ G₂ Gₜ} (h : countBoundB gi = true) :
    CountBound gi := by
  unfold countBoundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine { payload := ?_, instances := ?_, metaCounts := ?_ }
  · intro q hq
    rw [hq] at h
    simpa using h.1.2
  · exact h.1.1
  · intro m hm
    rw [hm] at h
    exact metaCountsBound_of_b h.2

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
  /-- D-GATE11 (signed 2026-11-23): the count budget the layout arithmetic consumes. Every CS,
      lookup, commitment and point-set count is `< 2 ^ 32`; the VK payload is `< 2 ^ 200`. This
      is an INPUT predicate (a computation on `gi`), not a `ValidV3` hook. -/
  countBound : CountBound gi
  /-- D-GATE16 (signed 2026-11-23): the generated-build stack bound. The QVM:1217-1222
      validator is not ported (`finishValidatorLeg`), and `finish` records `maxStack` from the
      pre-compaction stream while `build.bytes` is compacted, so this inequality is not a
      builder-state invariant. It is an input predicate over the generator's own outputs:
      every successful run's quotient build has `maxStack ≤ bytes.size`. The F1 render witnesses
      the concrete content by `native_decide` (`CertMeasure.f1StackOk_true`). -/
  stackBound : ∀ (o : CertOut), Generates gi o →
    ∀ b, quotientBuildOf o.out.plan = some b → b.maxStack ≤ b.bytes.size

/-! ## 2b. D-GATE11: the point-set count is bounded by the PCS-query count

`numPointSets` is not a field of `ConstraintSystemMeta.new`: it is computed from the data by
`intermediateSets`, which partitions the protocol's PCS queries by rotation set. The number of
point sets therefore never exceeds the number of PCS queries, and `MetaCountsBound.pcsQueries`
bounds that by `2 ^ 32`. The lemmas below are the length walk; none of them mentions a render. -/

theorem span_length_eq {α : Type} (m : List α) (p : α → Bool) :
    (m.span p).1.length + (m.span p).2.length = m.length := by
  rw [List.span_eq_takeWhile_dropWhile]
  have h := congrArg List.length (List.takeWhile_append_dropWhile (p := p) (l := m))
  simp only [List.length_append] at h
  omega

theorem btreeMapEntryOrInsert_length_le (m : List (List Nat × Nat)) (key : List Nat) :
    (btreeMapEntryOrInsert m key).length ≤ m.length + 1 := by
  unfold btreeMapEntryOrInsert
  split
  · omega
  · have hs := span_length_eq m (fun x => natListCmp x.1 key == Ordering.lt)
    simp only [List.length_append, List.length_cons]
    omega

theorem btreeFold_length_le (l : List (EcPoint × List Nat × List Word))
    (init : List (List Nat × Nat)) :
    (l.foldl (fun m e => btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) init).length
      ≤ init.length + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
      simp only [List.foldl_cons, List.length_cons]
      have h1 := btreeMapEntryOrInsert_length_le init (btreeSetFromList natCmp a.2.1)
      have h2 := ih (btreeMapEntryOrInsert init (btreeSetFromList natCmp a.2.1))
      omega

theorem step1Pass_length_le
    (st : List (EcPoint × List Nat × List Word) × List Int) (q : Query)
    (st' : List (EcPoint × List Nat × List Word) × List Int)
    (h : constructIntermediateSetsImpl.step1Pass st q = .ok st') :
    st'.1.length ≤ st.1.length + 1 := by
  obtain ⟨cm, pi⟩ := st
  obtain ⟨rot, comm, ev⟩ := q
  simp only [constructIntermediateSetsImpl.step1Pass, Bind.bind, Except.bind] at h
  split at h
  · simp only [pure, Except.pure] at h
    cases h
    simp
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · split at h
          · simp only [pure, Except.pure] at h
            cases h
            simp
          · split at h
            · cases h
            · simp only [pure, Except.pure] at h
              cases h
              simp
      · split at h
        · cases h
        · rename_i hset
          simp only [pure, Except.pure] at h
          cases h
          rw [Midfall.LoweringV3.listSetMut_length _ _ _ _ _ hset]
          simp

theorem step1Fold_length_le (qs : List Query) :
    ∀ (st st' : List (EcPoint × List Nat × List Word) × List Int),
      Midfall.LoweringV3.step1Fold qs st = .ok st' →
      st'.1.length ≤ st.1.length + qs.length := by
  induction qs with
  | nil =>
      intro st st' h
      simp only [Midfall.LoweringV3.step1Fold] at h
      cases h
      simp
  | cons q rest ih =>
      intro st st' h
      simp only [Midfall.LoweringV3.step1Fold, Bind.bind, Except.bind] at h
      obtain ⟨st1, hstep, hrest⟩ := cert_except_bind_ok h
      have h1 := step1Pass_length_le st q st1 hstep
      have h2 := ih st1 st' hrest
      simp only [List.length_cons]
      omega

theorem queries_length {meta_ : ConstraintSystemMeta} {dat : Data} {qs : List Query}
    (h : queries meta_ dat = .ok qs) : qs.length = meta_.protocol.pcsQueries.length := by
  unfold queries at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨qs0, hq, hrest⟩ := cert_except_bind_ok h
  split at hrest
  · cases hrest
  · split at hrest
    · cases hrest
    · cases hrest
      exact Midfall.LoweringV3.list_mapM_length meta_.protocol.pcsQueries qs hq

theorem constructIntermediateSetsImpl_pointSets_length_le
    (queries : List Query) (sets : IntermediateSets)
    (h : constructIntermediateSetsImpl queries = .ok sets) :
    sets.pointSets.length ≤ queries.length := by
  unfold constructIntermediateSetsImpl at h
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  obtain ⟨step1, hstep, hrest⟩ := cert_except_bind_ok h
  have hformula := Midfall.LoweringV3.constructIntermediateSetsImpl_pointSets_length
    queries sets step1 hstep (by
      unfold constructIntermediateSetsImpl
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [hstep]
      exact hrest)
  have hmap : (step1.1.foldl (fun m e => btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) []).length
      ≤ step1.1.length := by
    have h := btreeFold_length_le step1.1 []
    simpa using h
  have hstepLen : step1.1.length ≤ queries.length := by
    have hstep' : Midfall.LoweringV3.step1Fold queries ([], []) = .ok step1 := by
      rw [← Midfall.LoweringV3.foldlM_step1Fold]
      exact hstep
    have h := step1Fold_length_le queries ([], []) step1 hstep'
    simpa using h
  omega

/-- **D-GATE11: THE POINT-SET COUNT IS BOUNDED BY THE PCS-QUERY COUNT.** `numPointSets` partitions
    the PCS queries by rotation set, so its result is at most the number of queries. PROVED. -/
theorem numPointSets_le_pcsQueries (meta_ : ConstraintSystemMeta) (dat : Data)
    (hdummy : dat.dummyEvalWords = []) {n : Nat}
    (h : numPointSets meta_ dat = .ok n) :
    n ≤ meta_.protocol.pcsQueries.length := by
  obtain ⟨out, hout, hlen⟩ := Midfall.LoweringV3.numPointSets_parts meta_ dat n h
  obtain ⟨qs, sets, hq, hci, hs⟩ :=
    Midfall.LoweringV3.intermediateSets_parts meta_ dat out hdummy hout
  have hsets := Midfall.LoweringV3.sortSets_pointSets_length sets out hs
  have hciLe := constructIntermediateSetsImpl_pointSets_length_le qs sets hci
  have hqsLen := queries_length hq
  omega

/-- Left fold of addition with a seed; the count bound `v3_cdBound` needs. -/
theorem foldl_add_le (l : List Nat) (B init : Nat) (h : ∀ x ∈ l, x ≤ B) :
    l.foldl (fun a b => a + b) init ≤ init + l.length * B := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
      simp only [List.foldl_cons, List.length_cons]
      have ha : a ≤ B := h a (by simp)
      have hih := ih (init + a) (fun x hx => h x (by simp [hx]))
      rw [Nat.succ_mul]
      omega

/-- A list of counts each at most `B` sums to at most `length * B`. -/
theorem sumNat_le_length_mul {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x ≤ B) :
    sumNat l ≤ l.length * B := by
  have hh := foldl_add_le l B 0 h
  simpa [sumNat] using hh

/-- **D-GATE11: `metaDataForVk`'s point-set count is bounded by the input's PCS queries.**
    Under `Features.solidity` the dummy-eval pass is off, so the data `Data.new` builds has an
    empty dummy vector; the number written by `setNumPointSets` is exactly the `numPointSets`
    result on that data, and `numPointSets_le_pcsQueries` bounds it. PROVED. -/
theorem metaDataForVk_numPointSets_le {Plan : Type} (feat : Features) (env : VkBuildEnv Plan)
    (hfew : feat.outerFewerPointSets = false)
    (m : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    {meta' : ConstraintSystemMeta} {dat : Data} {mem : VerifierMemoryLayout}
    (h : metaDataForVk feat env m numInstances vk vkMptr = .ok (meta', dat, mem)) :
    meta'.numPointSets ≤ m.protocol.pcsQueries.length := by
  unfold metaDataForVk at h
  rw [hfew] at h
  simp only [Bind.bind, Except.bind, Bool.false_eq_true, ite_false] at h
  obtain ⟨x1, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨x2, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨x3, hx3, h3⟩ := cert_except_bind_ok h2
  obtain ⟨x4, hx4, h4⟩ := cert_except_bind_ok h3
  obtain ⟨x5, hx5, h5⟩ := cert_except_bind_ok h4
  obtain ⟨x6, hx6, h6⟩ := cert_except_bind_ok h5
  cases h6
  have hx5' : numPointSets (m.setNumDummyEvals 0) x4 = .ok x5 := by simpa using hx5
  have hdummy := Midfall.LoweringV3.Data.new_dummyEvalWords
    (m.setNumDummyEvals 0) vk x3 x4 hx4
  have hle := numPointSets_le_pcsQueries (m.setNumDummyEvals 0) x4 hdummy hx5'
  simpa [ConstraintSystemMeta.setNumDummyEvals, ConstraintSystemMeta.setNumPointSets] using hle

/-- **D-GATE11: THE PLAN META'S POINT-SET COUNT IS BOUNDED BY THE INPUT'S PCS QUERIES.** The
    reservation loop only ever stores a `metaDataForVk` result, so the invariant is the previous
    lemma at every step; `metaDataForStableStaticLayout` is the `List.range 3` fold. PROVED. -/
theorem metaDataForStableStaticLayout_numPointSets_le {Plan : Type} (feat : Features)
    (hfew : feat.outerFewerPointSets = false) (env : VkBuildEnv Plan)
    (m : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    {vkMptr : Ptr} {meta' : ConstraintSystemMeta} {dat : Data} {mem : VerifierMemoryLayout}
    (h : metaDataForStableStaticLayout feat env m numInstances vk
      = .ok (vkMptr, meta', dat, mem)) :
    meta'.numPointSets ≤ m.protocol.pcsQueries.length := by
  unfold metaDataForStableStaticLayout at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨start, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨res, hres, hout⟩ := cert_except_bind_ok h1
  have key : ∀ (l : List Nat)
      (st : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr),
      (∀ r, st.1 = some r → r.2.1.numPointSets ≤ m.protocol.pcsQueries.length) →
      ∀ (res' : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr),
        l.foldlM (fun (st : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr)
            (_ : Nat) => do
          if st.1.isSome then Except.ok st else do
            let vkMptr := st.2
            let (metaOut, dat, memory) ← metaDataForVk feat env m numInstances vk vkMptr
            let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
            let cur ← Value.asUsize vkMptr.value
            if planned == cur then
              Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
            else
              Except.ok (none, ptrMemory (valueFromNat planned))) st = .ok res' →
        (∀ r, res'.1 = some r → r.2.1.numPointSets ≤ m.protocol.pcsQueries.length) := by
    intro l
    induction l with
    | nil =>
        intro st hinv res' hf
        cases hf
        exact hinv
    | cons a as ih =>
        intro st hinv res' hf
        rw [List.foldlM_cons] at hf
        obtain ⟨st1, hstep, hrest⟩ := cert_except_bind_ok hf
        apply ih _ ?_ res' hrest
        intro r hr
        split at hstep
        · rename_i hsome
          cases hstep
          exact hinv r hr
        · rename_i hnone
          obtain ⟨q, hq, hstep2⟩ := cert_except_bind_ok hstep
          obtain ⟨q2, hq2, hstep3⟩ := cert_except_bind_ok hstep2
          obtain ⟨q3, hq3, hstep4⟩ := cert_except_bind_ok hstep3
          split at hstep4
          · cases hstep4
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
            exact metaDataForVk_numPointSets_le feat env hfew m numInstances vk st.2 hq
          · cases hstep4
            cases hr
  obtain ⟨resO, resPtr⟩ := res
  cases resO with
  | none => cases hout
  | some r =>
      have hkey := key (List.range 3) (none, ptrMemory (valueFromNat start))
        (by intro r hr; cases hr) (some r, resPtr) hres
      have hval : r = (vkMptr, meta', dat, mem) := Except.ok.inj hout
      exact hkey (vkMptr, meta', dat, mem) (by rw [← hval])

/-- **D-GATE11: `newFromVk`'s plan meta has at most as many point sets as the input's PCS
    queries.** Six bind peels and the reservation lemma. PROVED. -/
theorem newFromVk_numPointSets_le {F : Type} [BEq F]
    (field : Midfall.Generator.QuotientEvaluator.FieldCtx F) (cs : ConstraintSystem F)
    (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Halo2VerifyingKey)
    (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk Features.solidity field cs rawMeta numInstances
        accEncoding payload = .ok plan) :
    plan.meta_.numPointSets ≤ rawMeta.protocol.pcsQueries.length := by
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
    exact metaDataForStableStaticLayout_numPointSets_le Features.solidity rfl _
      rawMeta numInstances payload hq

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

/-- The D-GATE11 computations agree with a successful run: `rawMetaOf` is the run's raw meta and
    `payloadOf` is the payload the run uses. PROVED. -/
theorem payloadOf_of_generates {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}
    (hg : Generates gi o) :
    ∃ (p : Halo2VerifyingKey) (m0 : ConstraintSystemMeta),
      rawMetaOf gi = some m0 ∧ payloadOf gi = some p ∧ (renderOf gi o).plan.vk = p := by
  obtain ⟨m0, payload, hraw, hgenvk, _, h4⟩ := generate_spec hg
  refine ⟨payload, m0, ?_, ?_, plan_vk_of_generateAll h4⟩
  · unfold rawMetaOf
    rw [hraw]
  · unfold payloadOf
    rw [hraw]
    simp only
    rw [hgenvk]

/-- **D-GATE11's payload clause, read off a run.** The render's VK payload is the `payloadOf`
    computation and is below `2 ^ 200`. PROVED from the clause; no `ValidV3` projection. -/
theorem payload_len_of_generates {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}
    (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.vk.len < 2 ^ 200 := by
  obtain ⟨q, _m0, _hraw, hpay, hvk⟩ := payloadOf_of_generates hg
  rw [hvk]
  exact hs.countBound.payload q hpay

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
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, hvk, hsize⟩ :=
    Midfall.LoweringV3.plan_size_of_generated (generated_of hg)
  rw [hmem, Midfall.LoweringV3.MemoryPairs.new_transcriptMptr_eq]
  decide

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

/-- The base VK's constants survive `generateVk` in number as well as in value. PROVED. -/
theorem generateVk_prefix_length {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {codecs : VkPointCodecs G₁ G₂} {inputs : VerifierBuildInputs p G₁ G₂}
    {payload : Halo2VerifyingKey}
    (h : generateVk feat env codecs inputs = .ok payload)
    (vk0 : Halo2VerifyingKey) (hbase : generateBaseVk codecs inputs = .ok vk0) :
    vk0.constants.length ≤ payload.constants.length := by
  simp only [generateVk] at h
  obtain ⟨vk0', hbase', h⟩ := cert_except_bind_ok h
  have hvk : vk0' = vk0 := Except.ok.inj (hbase'.symm.trans hbase)
  subst hvk
  obtain ⟨st, hfold, hfin⟩ := cert_except_bind_ok h
  have hst : vk0'.constants.length ≤ st.vk.constants.length :=
    foldlM_reserve_ge (List.range 8) feat env inputs vk0'.constants.length
      { vk := vk0', quotientConstWords := 0, quotientProgramWords := 0, build := none } st
      hfold (le_refl _)
  have hfin' := generateVkFinalize_ge hfin
  omega

/-- A header slot below 31 reads the same from the payload as from the header constants. PROVED. -/
theorem generateVk_payload_getD {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {codecs : VkPointCodecs G₁ G₂} {inputs : VerifierBuildInputs p G₁ G₂}
    {payload : Halo2VerifyingKey}
    (hgenvk : generateVk feat env codecs inputs = .ok payload)
    (vk0 : Halo2VerifyingKey) (hbase : generateBaseVk codecs inputs = .ok vk0)
    {pre : Word256 × Word256 × Word256 × Word256 × Word256}
    {g1Words g2Words negSG2Words : List Word256} {constants : List (String × Word256)}
    (hconst : vk0.constants = constants)
    (hhdr : generateBaseVkHeader inputs pre g1Words g2Words negSG2Words = .ok constants)
    (i : Nat) (hi : i < 31) (d : String × Word256) :
    payload.constants.getD i d = constants.getD i d := by
  have hlen : vk0.constants.length = 31 := by
    rw [hconst]
    exact generateBaseVkHeader_length hhdr
  rw [← hconst]
  exact generateVk_getD_lt hgenvk vk0 hbase i (by omega) d

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

/-- `generateBaseVkEncodings` exposes the three encoder calls. PROVED. -/
theorem generateBaseVkEncodings_parts {codecs : VkPointCodecs G₁ G₂}
    {inputs : VerifierBuildInputs p G₁ G₂}
    {g1Words g2Words negSG2Words : List Word256}
    (h : generateBaseVkEncodings codecs inputs = .ok (g1Words, g2Words, negSG2Words)) :
    g1ToU256s (codecs.g1Repr (P.g₁)) = .ok g1Words ∧
    g2ToU256s (codecs.g2Repr inputs.params.g2) = .ok g2Words ∧
    g2ToU256s (codecs.g2Repr inputs.params.sG2⁻¹) = .ok negSG2Words := by
  simp only [generateBaseVkEncodings] at h
  split at h
  · obtain ⟨g1', h1, h⟩ := cert_except_bind_ok h
    obtain ⟨g2', h2, h⟩ := cert_except_bind_ok h
    obtain ⟨neg', h3, h⟩ := cert_except_bind_ok h
    cases h
    exact ⟨h1, h2, h3⟩
  · cases h

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

/-- `ConstraintSystem.blindingFactors` is at least six: `f4 = f3 + 3` and `f1 = max 3 _`. PROVED. -/
theorem blindingFactors_ge_six {F : Type} {cs : ConstraintSystem F} {bf : Nat}
    (h : cs.blindingFactors = .ok bf) : 6 ≤ bf := by
  unfold ConstraintSystem.blindingFactors at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨_deg, _hdeg, h⟩ := cert_except_bind_ok h
  obtain ⟨_cc, _hcc, h⟩ := cert_except_bind_ok h
  split at h
  · cases h
  · cases h
    omega

/-- `fromConstraintSystem` writes `rotationLast = -(blindingFactors + 1)`. PROVED. -/
theorem fromConstraintSystem_rotationLast {F : Type} {feat : Features} {cs : ConstraintSystem F}
    {nb : Nat} {plan : ProtocolPlan}
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok plan) :
    ∃ bf, cs.blindingFactors = .ok bf ∧ plan.rotationLast = -((bf : Int) + 1) := by
  unfold ProtocolPlan.fromConstraintSystem at h
  simp only [Bind.bind] at h
  obtain ⟨_dg, _hdg, h⟩ := cert_except_bind_ok h
  obtain ⟨_lc, _hlc, h⟩ := cert_except_bind_ok h
  obtain ⟨_nu, _hnu, h⟩ := cert_except_bind_ok h
  obtain ⟨_nc, _hnc, h⟩ := cert_except_bind_ok h
  obtain ⟨bf, hbf, h⟩ := cert_except_bind_ok h
  split at h
  · rename_i _hfix
    split at h
    · cases h
      exact ⟨bf, hbf, rfl⟩
    · cases h
  · cases h

/-- `ConstraintSystemMeta.new` carries `-(blindingFactors + 1)` and the factor is at least six.
    PROVED. -/
theorem constraintSystemMeta_new_rotationLast {F : Type} {feat : Features}
    {cs : ConstraintSystem F} {nb : Nat} {metaOut : ConstraintSystemMeta}
    (h : ConstraintSystemMeta.new feat cs nb = .ok metaOut) :
    ∃ bf, cs.blindingFactors = .ok bf ∧ metaOut.rotationLast = -((bf : Int) + 1) ∧ 6 ≤ bf := by
  unfold ConstraintSystemMeta.new at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨protocol, hproto, h⟩ := cert_except_bind_ok h
  cases h
  obtain ⟨bf, hbf, hrot⟩ := fromConstraintSystem_rotationLast hproto
  exact ⟨bf, hbf, hrot, blindingFactors_ge_six hbf⟩

/-- Every generated render's model reads `numNegLagranges` off the plan meta. PROVED. -/
theorem model_numNegLagranges_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    R.model.numNegLagranges = R.plan.meta_.rotationLast.natAbs := by
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
    simpa [numNegLagrangesOf] using (congrArg (fun x => x.numNegLagranges) hrec).symm

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


theorem env_negLagranges (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).pv.numNegLagranges = gi.vk.cs.blindingFactors.toOption.getD 0 + 1 := by
  have hmodel : (renderOf gi o).model.numNegLagranges =
      (renderOf gi o).plan.meta_.rotationLast.natAbs :=
    model_numNegLagranges_of_generated (generated_of hg)
  have hpv : (renderOf gi o).pv.numNegLagranges = (renderOf gi o).model.numNegLagranges := rfl
  rw [hpv, hmodel]
  obtain ⟨m0, _payload, hraw, _hgenvk, _hfp, _h4⟩ := generate_spec hg
  obtain ⟨rawMeta, plan, hraw', hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  have hrawEq : rawMeta = m0 := Except.ok.inj (hraw'.symm.trans hraw)
  have hmeta : (renderOf gi o).plan.meta_.rotationLast = m0.rotationLast := by
    rw [hp]
    rw [newFromVk_rotationLast Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs rawMeta
      gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl, hrawEq]
  obtain ⟨bf, hbf, hrot, _hbfge⟩ := constraintSystemMeta_new_rotationLast hraw
  have hrot' : (renderOf gi o).plan.meta_.rotationLast.natAbs = bf + 1 := by
    rw [hmeta, hrot, Int.natAbs_neg]
    rw [show (↑bf + 1 : Int) = ↑(bf + 1) from by norm_num, Int.natAbs_natCast]
  rw [hrot', hbf]
  rfl

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
  obtain ⟨_m0, payload, _hraw, hgenvk, _hfp, h4⟩ := generate_spec hg
  have hvk : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  obtain ⟨vk0, hbase⟩ := generateVk_base hgenvk
  obtain ⟨pre, _hpre, hbody⟩ := generateBaseVk_parts hbase
  obtain ⟨g1W, g2W, negW, consts, _fixedC, _permC, henc, hhdr, _hfix, _hperm, hconst,
    _hfixEq, _hpermEq⟩ := generateBaseVkBody_parts hbody
  obtain ⟨henc1, _henc2, _henc3⟩ := generateBaseVkEncodings_parts henc
  obtain ⟨ws, hws, hwsLen, hwsFold⟩ := hs.g1Codec (P.g₁)
  have hg1eq : g1W = ws := Except.ok.inj (henc1.symm.trans hws)
  have hpv : (renderOf gi o).pv.vk = payload := by
    change o.out.plan.vk = payload
    exact hvk
  have hlen : 11 + 4 ≤ (renderOf gi o).pv.vk.constants.length := by
    have hlen31 : vk0.constants.length = 31 := by
      rw [hconst]; exact generateBaseVkHeader_length hhdr
    have hpreLen : vk0.constants.length ≤ payload.constants.length :=
      generateVk_prefix_length hgenvk vk0 hbase
    rw [hpv]
    omega
  have hget : ∀ j, j < 4 → (payload.constants.getD (11 + j) ("", 0)).2 = ws.getD j 0 := by
    intro j hj
    have hpay := generateVk_payload_getD hgenvk vk0 hbase hconst hhdr (11 + j)
      (by omega) ("", 0)
    have hh := generateBaseVkHeader_g1Base_get hhdr (by rw [hg1eq]; exact hwsLen) j hj
    have hh2 : (consts.getD (11 + j) ("", 0)).2 = g1W.getD j 0 := by
      have := congrArg Prod.snd hh
      rwa [g1Base_word] at this
    rw [hpay, hh2, hg1eq]
  have hbytes := vkHeaderBytes_eq_words (PV := (renderOf gi o).pv) (i := 11) (n := 4)
    (ws := ws) hlen hwsLen (by
      intro j hj
      rw [hpv]
      exact hget j hj)
  change Midfall.Lowering.vkHeaderBytes (renderOf gi o).pv 11 4 =
    gi.E.g1.toEip (AdmissiblePairing.g₁ (G₂ := G₂) (Gₜ := Gₜ))
  rw [hbytes]
  exact hwsFold

theorem payload_g2Base (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.Lowering.vkG2Words (renderOf gi o).pv Midfall.Lowering.vkG2BaseSlot =
      gi.encG2 (AdmissiblePairing.g₂ (G₁ := G₁) (Gₜ := Gₜ)) := by
  obtain ⟨m0, payload, _hraw, hgenvk, _hfp, h4⟩ := generate_spec hg
  have hvk : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  obtain ⟨vk0, hbase⟩ := generateVk_base hgenvk
  obtain ⟨pre, _hpre, hbody⟩ := generateBaseVk_parts hbase
  obtain ⟨g1W, g2W, negW, consts, _fixedC, _permC, henc, hhdr, _hfix, _hperm, hconst,
    _hfixEq, _hpermEq⟩ := generateBaseVkBody_parts hbody
  obtain ⟨_henc1, henc2, _henc3⟩ := generateBaseVkEncodings_parts henc
  have hg2 : (buildInputsOf gi m0).params.g2 = P.g₂ :=
    beq_iff_eq.mp (generateBaseVk_g2_check hbase)
  have henc2' : g2ToU256s (gi.codecs.g2Repr (P.g₂)) = .ok g2W := by
    rw [← hg2]
    exact henc2
  obtain ⟨ws, hws, hwsLen, hwsFold⟩ := hs.g2Codec (P.g₂)
  have hg2eq : g2W = ws := Except.ok.inj (henc2'.symm.trans hws)
  have hpv : (renderOf gi o).pv.vk = payload := by
    change o.out.plan.vk = payload
    exact hvk
  have hlen : 15 + 8 ≤ (renderOf gi o).pv.vk.constants.length := by
    have hlen31 : vk0.constants.length = 31 := by
      rw [hconst]; exact generateBaseVkHeader_length hhdr
    have hpreLen : vk0.constants.length ≤ payload.constants.length :=
      generateVk_prefix_length hgenvk vk0 hbase
    rw [hpv]
    omega
  have hget : ∀ j, j < 8 → (payload.constants.getD (15 + j) ("", 0)).2 = ws.getD j 0 := by
    intro j hj
    have hpay := generateVk_payload_getD hgenvk vk0 hbase hconst hhdr (15 + j)
      (by omega) ("", 0)
    have hh := generateBaseVkHeader_g2Base_get hhdr (by rw [hg2eq]; exact hwsLen) j hj
    have hh2 : (consts.getD (15 + j) ("", 0)).2 = g2W.getD j 0 := by
      have := congrArg Prod.snd hh
      rwa [g2Base_word] at this
    rw [hpay, hh2, hg2eq]
  have hbytes := vkHeaderBytes_eq_words (PV := (renderOf gi o).pv) (i := 15) (n := 8)
    (ws := ws) hlen hwsLen (by
      intro j hj
      rw [hpv]
      exact hget j hj)
  change Midfall.Lowering.vkHeaderBytes (renderOf gi o).pv 15 8 =
    gi.encG2 (AdmissiblePairing.g₂ (G₁ := G₁) (Gₜ := Gₜ))
  rw [hbytes]
  exact hwsFold

theorem payload_negSG2 (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.Lowering.vkG2Words (renderOf gi o).pv Midfall.Lowering.vkNegSG2BaseSlot =
      gi.encG2 (renderOf gi o).sG2gen⁻¹ := by
  obtain ⟨m0, payload, _hraw, hgenvk, _hfp, h4⟩ := generate_spec hg
  have hvk : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  obtain ⟨vk0, hbase⟩ := generateVk_base hgenvk
  obtain ⟨pre, _hpre, hbody⟩ := generateBaseVk_parts hbase
  obtain ⟨g1W, g2W, negW, consts, _fixedC, _permC, henc, hhdr, _hfix, _hperm, hconst,
    _hfixEq, _hpermEq⟩ := generateBaseVkBody_parts hbody
  obtain ⟨_henc1, _henc2, henc3⟩ := generateBaseVkEncodings_parts henc
  obtain ⟨ws, hws, hwsLen, hwsFold⟩ := hs.g2Codec (gi.srs.sG2⁻¹)
  have hnegeq : negW = ws := Except.ok.inj (henc3.symm.trans hws)
  have hpv : (renderOf gi o).pv.vk = payload := by
    change o.out.plan.vk = payload
    exact hvk
  have hlen : 23 + 8 ≤ (renderOf gi o).pv.vk.constants.length := by
    have hlen31 : vk0.constants.length = 31 := by
      rw [hconst]; exact generateBaseVkHeader_length hhdr
    have hpreLen : vk0.constants.length ≤ payload.constants.length :=
      generateVk_prefix_length hgenvk vk0 hbase
    rw [hpv]
    omega
  have hget : ∀ j, j < 8 → (payload.constants.getD (23 + j) ("", 0)).2 = ws.getD j 0 := by
    intro j hj
    have hpay := generateVk_payload_getD hgenvk vk0 hbase hconst hhdr (23 + j)
      (by omega) ("", 0)
    have hh := generateBaseVkHeader_negSG2_get hhdr (by rw [hnegeq]; exact hwsLen) j hj
    have hh2 : (consts.getD (23 + j) ("", 0)).2 = negW.getD j 0 := by
      have := congrArg Prod.snd hh
      rwa [negSG2Base_word] at this
    rw [hpay, hh2, hnegeq]
  have hbytes := vkHeaderBytes_eq_words (PV := (renderOf gi o).pv) (i := 23) (n := 8)
    (ws := ws) hlen hwsLen (by
      intro j hj
      rw [hpv]
      exact hget j hj)
  change Midfall.Lowering.vkHeaderBytes (renderOf gi o).pv 23 8 =
    gi.encG2 (gi.srs.sG2⁻¹)
  rw [hbytes]
  exact hwsFold

/-- The reservation step touches only the constants and the quotient reservations. PROVED. -/
theorem reserveStep_comms {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {inputs : VerifierBuildInputs p G₁ G₂} {headerWords : Nat}
    {st st' : VkReservationState} {x : Nat}
    (h : reserveStep feat env inputs headerWords st x = .ok st') :
    st'.vk.fixedComms = st.vk.fixedComms ∧
      st'.vk.permutationComms = st.vk.permutationComms := by
  unfold reserveStep at h
  by_cases hb : st.build.isSome
  · simp only [hb, if_true] at h
    cases h
    exact ⟨rfl, rfl⟩
  · simp only [hb, if_false, Bool.false_eq_true] at h
    obtain ⟨_m, _, h⟩ := cert_except_bind_ok h
    obtain ⟨_c, _, h⟩ := cert_except_bind_ok h
    split at h <;> cases h <;> exact ⟨rfl, rfl⟩

theorem foldlM_reserve_comms (l : List Nat) {feat : Features}
    {env : VkBuildEnv QuotientProgramPlan} {inputs : VerifierBuildInputs p G₁ G₂}
    {headerWords : Nat} (init st : VkReservationState)
    (h : l.foldlM (reserveStep feat env inputs headerWords) init = .ok st) :
    st.vk.fixedComms = init.vk.fixedComms ∧
      st.vk.permutationComms = init.vk.permutationComms := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      cases h
      exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : reserveStep feat env inputs headerWords init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          obtain ⟨ihf, ihp⟩ := ih s1 h
          obtain ⟨hsf, hsp⟩ := reserveStep_comms hs
          exact ⟨ihf.trans hsf, ihp.trans hsp⟩

/-- A constant write-back step leaves both commitment vectors alone. PROVED. -/
theorem fillConstStep_comms (offset : Nat) (vk vk' : Halo2VerifyingKey)
    (pair : Word256 × Nat) (h : fillConstStep offset vk pair = .ok vk') :
    vk'.fixedComms = vk.fixedComms ∧
      vk'.permutationComms = vk.permutationComms := by
  unfold fillConstStep at h
  obtain ⟨value, i⟩ := pair
  obtain ⟨cs, _hcs, h⟩ := cert_except_bind_ok h
  cases h
  exact ⟨rfl, rfl⟩

/-- A program write-back step leaves both commitment vectors alone. PROVED. -/
theorem fillProgramStep_comms (offset : Nat) (vk vk' : Halo2VerifyingKey)
    (pair : Word256 × Nat) (h : fillProgramStep offset vk pair = .ok vk') :
    vk'.fixedComms = vk.fixedComms ∧
      vk'.permutationComms = vk.permutationComms := by
  unfold fillProgramStep at h
  obtain ⟨value, i⟩ := pair
  obtain ⟨cs, _hcs, h⟩ := cert_except_bind_ok h
  cases h
  exact ⟨rfl, rfl⟩

theorem foldlM_fillConst_comms (l : List (Word256 × Nat)) {offset : Nat}
    (init st : Halo2VerifyingKey)
    (h : l.foldlM (fillConstStep offset) init = .ok st) :
    st.fixedComms = init.fixedComms ∧
      st.permutationComms = init.permutationComms := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      cases h
      exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : fillConstStep offset init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          obtain ⟨ihf, ihp⟩ := ih s1 h
          obtain ⟨hsf, hsp⟩ := fillConstStep_comms offset init s1 x hs
          exact ⟨ihf.trans hsf, ihp.trans hsp⟩

theorem foldlM_fillProgram_comms (l : List (Word256 × Nat)) {offset : Nat}
    (init st : Halo2VerifyingKey)
    (h : l.foldlM (fillProgramStep offset) init = .ok st) :
    st.fixedComms = init.fixedComms ∧
      st.permutationComms = init.permutationComms := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      cases h
      exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : fillProgramStep offset init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          obtain ⟨ihf, ihp⟩ := ih s1 h
          obtain ⟨hsf, hsp⟩ := fillProgramStep_comms offset init s1 x hs
          exact ⟨ihf.trans hsf, ihp.trans hsp⟩

/-- `generateVk` leaves the base VK's two commitment vectors unchanged. PROVED. -/
theorem generateVk_comms {feat : Features} {env : VkBuildEnv QuotientProgramPlan}
    {codecs : VkPointCodecs G₁ G₂} {inputs : VerifierBuildInputs p G₁ G₂}
    {payload : Halo2VerifyingKey}
    (h : generateVk feat env codecs inputs = .ok payload)
    (vk0 : Halo2VerifyingKey) (hbase : generateBaseVk codecs inputs = .ok vk0) :
    payload.fixedComms = vk0.fixedComms ∧
      payload.permutationComms = vk0.permutationComms := by
  simp only [generateVk] at h
  obtain ⟨vk0', hbase', h⟩ := cert_except_bind_ok h
  have hvk : vk0' = vk0 := Except.ok.inj (hbase'.symm.trans hbase)
  subst hvk
  obtain ⟨st, hfold, hfin⟩ := cert_except_bind_ok h
  obtain ⟨hsf, hsp⟩ := foldlM_reserve_comms (List.range 8)
    { vk := vk0', quotientConstWords := 0, quotientProgramWords := 0, build := none } st hfold
  simp only [generateVkFinalize] at hfin
  obtain ⟨lc, _hlc, hfill⟩ := cert_except_bind_ok hfin
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
      obtain ⟨h1f, h1p⟩ := foldlM_fillConst_comms lc.qbuild.consts.zipIdx st.vk vkFilled hfill1
      obtain ⟨h2f, h2p⟩ := foldlM_fillProgram_comms lc.chunks.zipIdx vkFilled vkFilled2 hfill2
      exact ⟨h2f.trans (h1f.trans hsf), h2p.trans (h1p.trans hsp)⟩
    · cases h
  · cases h

/-- `Bytes.empty` is `ByteArray.mk #[]`, so the core left-identity lemma applies under
    that spelling. PROVED. -/
private theorem cert_bytes_empty_append (x : Bytes) : (ByteArray.mk #[] : Bytes) ++ x = x := by
  change ByteArray.empty ++ x = x
  exact ByteArray.empty_append

/-- A four-word EIP G1 image is the left fold of its words. PROVED. -/
theorem g1WordsBytes_eq_fold (a b c d : Word256) :
    Midfall.LoweringV2.g1WordsBytes { xHi := a, xLo := b, yHi := c, yLo := d } =
      [a, b, c, d].foldl (init := Bytes.empty)
        (fun acc w => ByteArray.append acc (wordToBytesBE w)) := by
  simp [Midfall.LoweringV2.g1WordsBytes, Bytes.empty, List.foldl, cert_bytes_empty_append]

/-- The generator's G1 commitment mapM produces the EIP images of its inputs, by the codec
    law. PROVED. -/
theorem mapM_g1WordsBytes {E : VerifierEnv p G₁ G₂ Gₜ} {codecs : VkPointCodecs G₁ G₂}
    {l : List G₁} {ws : List Midfall.Generator.G1Words}
    (h : l.mapM (fun g => g1ToU256s (codecs.g1Repr g) >>= vkG1WordsOf) = .ok ws)
    (hcodec : ∀ Q : G₁, ∃ w : List Word256,
      g1ToU256s (codecs.g1Repr Q) = .ok w ∧ w.length = 4 ∧
      w.foldl (init := Bytes.empty) (fun acc w => ByteArray.append acc (wordToBytesBE w)) =
        E.g1.toEip Q) :
    ws.map Midfall.LoweringV2.g1WordsBytes = l.map E.g1.toEip := by
  induction l generalizing ws with
  | nil =>
      simp only [List.mapM_nil] at h
      cases h
      rfl
  | cons g gs ih =>
      rw [List.mapM_cons] at h
      obtain ⟨w0, h0, h⟩ := cert_except_bind_ok h
      obtain ⟨w, hw, hw1⟩ := cert_except_bind_ok h0
      obtain ⟨ws', hrest, h⟩ := cert_except_bind_ok h
      cases h
      obtain ⟨wc, hwc, hwclen, hwcfold⟩ := hcodec g
      have hweq : w = wc := Except.ok.inj (hw.symm.trans hwc)
      subst hweq
      obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hwclen
      simp only [vkG1WordsOf] at hw1
      have hw0 : w0 = { xHi := a, xLo := b, yHi := c, yLo := d } :=
        (Except.ok.inj hw1).symm
      subst hw0
      rw [List.map_cons, List.map_cons, g1WordsBytes_eq_fold, hwcfold, ih hrest]

theorem payload_comms (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.vk.fixedComms.map Midfall.LoweringV2.g1WordsBytes =
      gi.vk.fixedCommitments.toList.map gi.E.g1.toEip ∧
    (renderOf gi o).plan.vk.permutationComms.map Midfall.LoweringV2.g1WordsBytes =
      gi.vk.permutation.commitments.toList.map gi.E.g1.toEip := by
  obtain ⟨m0, payload, _hraw, hgenvk, _hfp, h4⟩ := generate_spec hg
  have hvk : o.out.plan.vk = payload := plan_vk_of_generateAll h4
  obtain ⟨vk0, hbase⟩ := generateVk_base hgenvk
  obtain ⟨pre, _hpre, hbody⟩ := generateBaseVk_parts hbase
  obtain ⟨g1W, g2W, negW, consts, fixedC, permC, henc, hhdr, hfix, hperm, hconst,
    hfixEq, hpermEq⟩ := generateBaseVkBody_parts hbody
  obtain ⟨hvkf, hvkp⟩ := generateVk_comms hgenvk vk0 hbase
  have hpv : (renderOf gi o).plan.vk.fixedComms = payload.fixedComms :=
    congrArg Halo2VerifyingKey.fixedComms hvk
  have hpvp : (renderOf gi o).plan.vk.permutationComms = payload.permutationComms :=
    congrArg Halo2VerifyingKey.permutationComms hvk
  constructor
  · rw [hpv, hvkf, hfixEq]
    exact mapM_g1WordsBytes hfix hs.g1Codec
  · rw [hpvp, hvkp, hpermEq]
    exact mapM_g1WordsBytes hperm hs.g1Codec

/-! ### S: the one scope clause that mentions the plan -/

/-- A successful `MemoryMap::validate` gives the `WellFormed` Bool: the reserved loop yields
    alignment and the spill-window floor, and the pair loop yields disjointness. PROVED. -/
theorem memoryMapValidateReserved_all {rs : List MemoryRegion}
    (h : memoryMapValidateReserved rs = .ok ()) :
    rs.all (fun r => r.len == 0 || r.start % wordBytes == 0) = true ∧
      rs.all (fun r => r.len == 0 || solidityReservedMemoryBytes <= r.start) = true := by
  induction rs with
  | nil => simp [memoryMapValidateReserved]
  | cons r rest ih =>
    unfold memoryMapValidateReserved at h
    by_cases h1 : r.len != 0 && r.start < solidityReservedMemoryBytes
    · simp [h1] at h
    · by_cases h2 : r.start % wordBytes != 0
      · simp [h1, h2] at h
      · by_cases h3 : r.len % wordBytes != 0
        · simp [h1, h2, h3] at h
        · simp [h1, h2, h3] at h
          obtain ⟨ih1, ih2⟩ := ih h
          constructor
          · rw [List.all_cons, Bool.and_eq_true]
            constructor
            · have hz : r.len = 0 ∨ r.start % wordBytes = 0 := by
                by_cases hlen : r.len = 0
                · exact Or.inl hlen
                · right
                  have hne : (r.start % wordBytes != 0) = false := by simpa using h2
                  simpa using hne
              simpa [Bool.or_eq_true, beq_iff_eq] using hz
            · exact ih1
          · rw [List.all_cons, Bool.and_eq_true]
            constructor
            · have hz : r.len = 0 ∨ solidityReservedMemoryBytes <= r.start := by
                by_cases hlen : r.len = 0
                · exact Or.inl hlen
                · right
                  have hnot : ¬ (r.start < solidityReservedMemoryBytes) := by
                    intro hlt
                    have : (r.len != 0 && r.start < solidityReservedMemoryBytes) = true := by
                      simp [hlen, hlt]
                    simp [h1] at this
                  exact Nat.le_of_not_lt hnot
              simpa [Bool.or_eq_true, beq_iff_eq] using hz
            · exact ih2

theorem memoryMapValidateAgainst_all {lhs : MemoryRegion} {rest : List MemoryRegion}
    (h : memoryMapValidateAgainst lhs rest = .ok ()) :
    rest.all (fun rhs => ! (lhs.overlaps rhs && memoryLifetimeIntersects lhs.lifetime rhs.lifetime)) = true := by
  induction rest with
  | nil => simp
  | cons rhs tl ih =>
    unfold memoryMapValidateAgainst at h
    cases hb : lhs.overlaps rhs <;>
      cases hl : memoryLifetimeIntersects lhs.lifetime rhs.lifetime <;>
      simp [hb, hl, List.all_cons] at h ⊢
    all_goals simpa [List.all_eq_true] using ih h

theorem memoryMapValidatePairs_all {rs : List MemoryRegion}
    (h : memoryMapValidatePairs rs = .ok ()) : memoryRegionsPairwiseDisjoint rs = true := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    unfold memoryMapValidatePairs at h
    simp only [Bind.bind, Except.bind] at h
    cases hb : memoryMapValidateAgainst r rest with
    | error e => simp [hb] at h
    | ok u =>
      cases hp : memoryMapValidatePairs rest with
      | error e => simp [hb, hp] at h
      | ok u2 =>
        simp [hb, hp] at h
        unfold memoryRegionsPairwiseDisjoint
        rw [Bool.and_eq_true]
        exact ⟨memoryMapValidateAgainst_all hb, ih hp⟩

theorem memoryMap_validate_wellFormed {map : MemoryMap} (h : map.validate = .ok ()) :
    map.WellFormed := by
  unfold MemoryMap.validate at h
  simp only [Bind.bind, Except.bind] at h
  cases hres : memoryMapValidateReserved map.regions with
  | error e => simp [hres] at h
  | ok u =>
    cases hpairs : memoryMapValidatePairs map.regions with
    | error e => simp [hres, hpairs] at h
    | ok u2 =>
      simp [hres, hpairs] at h
      obtain ⟨h1, h2⟩ := memoryMapValidateReserved_all hres
      have h3 := memoryMapValidatePairs_all hpairs
      unfold MemoryMap.WellFormed MemoryMap.wellFormedBool
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨h1, h2⟩, h3⟩

theorem invThen_ok_ok {x : Except String Unit}
    {k : Unit → Except Midfall.Halo2.Fault (Except String Unit)} {u : Unit}
    (h : Midfall.Generator.invThen x k = .ok (.ok u)) :
    ∃ v, x = .ok v ∧ k v = .ok (.ok u) := by
  unfold Midfall.Generator.invThen at h
  cases x with
  | error e => simp at h
  | ok v => exact ⟨v, rfl, h⟩

theorem memory_validate_of_validateGeneratorInvariants
    (L : Midfall.Generator.LoweringPlan Unit Unit)
    (h : L.validateGeneratorInvariants = .ok (.ok ())) :
    L.memory.validate = .ok () := by
  unfold Midfall.Generator.LoweringPlan.validateGeneratorInvariants at h
  obtain ⟨_, _, h2⟩ := invThen_ok_ok h
  obtain ⟨v, hv, _⟩ := invThen_ok_ok h2
  cases hL : L.memory.validate with
  | error e =>
      rw [hL] at hv
      cases hv
  | ok u =>
      cases u
      rfl

theorem verifierMemoryLayout_validate_map {self : VerifierMemoryLayout}
    (h : self.validate = .ok ()) : self.map.validate = .ok () := by
  unfold VerifierMemoryLayout.validate at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨_, _, h⟩ := cert_except_bind_ok h
  obtain ⟨_, _, h⟩ := cert_except_bind_ok h
  split at h
  · simp at h
  · by_cases h1 : self.pcs.rotPointsWords > self.thetaWindows.rotPointsCapWords
    · simp [h1] at h
    · simp only [h1, ite_false] at h
      by_cases h2 : self.pcs.x1PowersWords > self.thetaWindows.x1PowersCapWords
      · simp [h2] at h
      · simp only [h2, ite_false] at h
        by_cases h3 : self.pcs.qComWords > self.thetaWindows.qComCapWords
        · simp [h3] at h
        · simp only [h3, ite_false] at h
          by_cases h4 : self.pcs.qEvalSetWords > self.thetaWindows.qEvalSetCapWords
          · simp [h4] at h
          · simp only [h4, ite_false] at h
            exact h

/-! ### The 18-clause text lemmas (scratch section 5) -/

/-- **CERT.1: THE PLAN META, CLOSED.** `PlanMeta` asks for
    `Data.new meta1 vk R.plan.memory = .ok R.plan.data`, and the two sides come from DIFFERENT
    layouts: the constructor's `Data` is built on `meta_data_for_vk`'s intermediate default-config
    layout (VK:512-514, meta before `set_num_point_sets`), while `R.plan.memory` is the plan's
    final layout (PL:259-270, PCS/quotient config, meta after it). The exact stability fact is
    `LayoutMemory.new_dataBases_setNumPointSets`: `VerifierMemoryLayout::new` computes the ten
    bases `Data.new` reads from `(vk_mptr, vk.len, challenge_indices.length, num_evals, the
    commitment census)` only, none of which the point-set count changes, and the PCS overrides
    only move regions allocated after the commitment run; `Data.new_congr` then transfers the
    equation. `MemoryPairs.planMeta_of_generated` assembles the three-pass decomposition
    (`metaDataForVk_parts`) and the stability step. The `SupportedInput` hypotheses are not needed:
    the clause follows from generation alone. PROVED. -/
theorem v3_planMeta (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.PlanMeta (renderOf gi o) :=
  Midfall.LoweringV3.MemoryPairs.planMeta_of_generated (generated_of hg)

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

theorem supported_layout (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.memory.map.WellFormed ∧
      (renderOf gi o).plan.memory.validate.isOk = true := by
  obtain ⟨rawMeta, plan, _hraw, hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  have hval : plan.validateGeneratorInvariants = .ok (.ok ()) :=
    newFromVk_validate Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs rawMeta
      gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  have hmem : plan.memory.validate = .ok () :=
    memory_validate_of_validateGeneratorInvariants plan hval
  have hmap : plan.memory.map.WellFormed :=
    memoryMap_validate_wellFormed (verifierMemoryLayout_validate_map hmem)
  rw [hp]
  constructor
  · exact hmap
  · rw [hmem]
    rfl

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
  -- the raw meta and the plan's own meta / proof layout
  obtain ⟨m0, _payload, hraw, _hgenvk, _hfp, _h4⟩ := generate_spec hg
  obtain ⟨rawMeta, plan, hraw', hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  simp only [renderOf] at hraw' hpl
  rw [hraw] at hraw'
  cases hraw'
  obtain ⟨meta_, L, hmeta, hLplan, hL⟩ :=
    newFromVk_plan_meta_proofLayout Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs
      m0 gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  have hLR : (renderOf gi o).plan.proofLayout = L := by rw [hp]; exact hLplan
  -- the D-GATE11 count clause, instantiated at the run's own raw meta
  have hr : rawMetaOf gi = some m0 := by
    unfold rawMetaOf
    rw [hraw]
  have hM : MetaCountsBound m0 := hs.countBound.metaCounts m0 hr
  have hmetaFacts := Midfall.LoweringV3.newFromVk_meta_numEvals (frFieldCtx gi.E.delta)
    gi.vk.cs m0 gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  rw [hmeta] at hmetaFacts
  have hEval : meta_.numEvals < 2 ^ 32 := by
    rw [hmetaFacts.1]; exact hM.evals
  have hProtocol : meta_.protocol = m0.protocol := hmetaFacts.2
  have hPointLe : meta_.numPointSets ≤ m0.protocol.pcsQueries.length := by
    have h := newFromVk_numPointSets_le (frFieldCtx gi.E.delta) gi.vk.cs m0 gi.cfg.numInstances
      gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
    rwa [hmeta] at h
  have hPoint : meta_.numPointSets < 2 ^ 32 := lt_of_le_of_lt hPointLe hM.pcsQueries
  -- the proof-length equation and the commitment census
  have hfacts := Midfall.LoweringV3.TranscriptRows.tp_fromProtocol hL
  have hpen := proofLen_eq_repackedLen meta_.protocol meta_.numEvals meta_.numPointSets L hL
  have hcptr := Midfall.LoweringV2.fromProtocol_proofCptr meta_.protocol meta_.numEvals
    meta_.numPointSets L hL
  have hCG : L.commitmentG1Count = sumNat meta_.protocol.numUserAdvices
      + meta_.protocol.numLookups + meta_.protocol.numPermutationZs
      + sumNat (((List.range meta_.protocol.lookupChunks.length).zip
          meta_.protocol.lookupChunks).map (fun q => q.2 + 1))
      + meta_.protocol.numTrashcans + meta_.protocol.numQuotients := by
    rw [show L.commitmentG1Count =
        sumNat (L.advicePhases.map (fun s => s.itemCount))
        + L.lookupMultiplicities.itemCount + L.permutationProducts.itemCount
        + sumNat (L.lookups.map (fun lk => lk.helpers.itemCount + lk.accumulator.itemCount))
        + L.trash.itemCount + L.quotientLimbs.itemCount from rfl]
    rw [hfacts.adviceSum, hfacts.lookupM, hfacts.permZ, hfacts.lookupSum,
      hfacts.trash, hfacts.quotient]
  have hAdvSum : sumNat meta_.protocol.numUserAdvices ≤ 2 ^ 32 * 2 ^ 32 := by
    have h1 : sumNat meta_.protocol.numUserAdvices
        ≤ meta_.protocol.numUserAdvices.length * 2 ^ 32 := by
      rw [hProtocol]
      exact sumNat_le_length_mul (fun x hx => Nat.le_of_lt (hM.userAdvicesEach x hx))
    have h2 : meta_.protocol.numUserAdvices.length < 2 ^ 32 := by
      rw [hProtocol]; exact hM.userAdvicesLen
    nlinarith
  have hLkSum : sumNat (((List.range meta_.protocol.lookupChunks.length).zip
      meta_.protocol.lookupChunks).map (fun q => q.2 + 1)) ≤ 2 ^ 32 * 2 ^ 32 := by
    have hmap : ((List.range meta_.protocol.lookupChunks.length).zip
        meta_.protocol.lookupChunks).map (fun q => q.2 + 1)
        = meta_.protocol.lookupChunks.map (fun n => n + 1) := by
      let l := (List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks
      have hm : List.map (fun q => q.2 + 1) l = List.map (fun n => n + 1) (l.map Prod.snd) := by
        rw [List.map_map]
        rfl
      rw [hm, Midfall.LoweringV3.TranscriptRows.zip_range_snd]
    rw [hmap]
    have h1 : sumNat (meta_.protocol.lookupChunks.map (fun n => n + 1))
        ≤ meta_.protocol.lookupChunks.length * 2 ^ 32 := by
      have h := sumNat_le_length_mul
        (l := meta_.protocol.lookupChunks.map (fun n => n + 1)) (B := 2 ^ 32) (by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨n, hn, rfl⟩ := hx
          rw [hProtocol] at hn
          have := hM.lookupChunksEach n hn
          omega)
      simpa using h
    have h2 : meta_.protocol.lookupChunks.length < 2 ^ 32 := by
      rw [hProtocol]; exact hM.lookupChunksLen
    nlinarith
  have hCCount : L.commitmentG1Count < 2 ^ 66 := by
    rw [hCG]
    have hLk : meta_.protocol.numLookups < 2 ^ 32 := by rw [hProtocol]; exact hM.lookups
    have hPs : meta_.protocol.numPermutationZs < 2 ^ 32 := by rw [hProtocol]; exact hM.permutationZs
    have hTr : meta_.protocol.numTrashcans < 2 ^ 32 := by rw [hProtocol]; exact hM.trashcans
    have hQ : meta_.protocol.numQuotients < 2 ^ 32 := by rw [hProtocol]; exact hM.quotients
    nlinarith
  have hRep : L.proofLen = 128 * L.commitmentG1Count + 32 * meta_.numEvals
      + 128 + 32 * meta_.numPointSets + 128 := by
    rw [hpen.1]
    change (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count * Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numEvals * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numPointSets * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes = _
    rw [sum_commitmentReadGroups]
    change L.commitmentG1Count * Midfall.Generator.g1Bytes
        + L.evals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
        + L.qEvals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes = _
    rw [hfacts.evals, hfacts.qEvals]
    have hg1 : Midfall.Generator.g1Bytes = 128 := rfl
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hg1, hw]
    ring
  have hPE : L.proofEnd = 100 + L.proofLen := by
    rw [hpen.2, hcptr]
    rfl
  have hEnd : L.proofEnd < 2 ^ 80 := by
    rw [hPE, hRep]
    nlinarith [hCCount, hEval, hPoint, Nat.zero_le L.commitmentG1Count]
  rw [hLR]
  have hNI : gi.cfg.numInstances < 2 ^ 64 := hs.sizeBound.1
  have hsmall : L.proofEnd + 32 + 32 * gi.cfg.numInstances < 2 ^ 128 := by
    nlinarith [hEnd, hNI]
  exact lt_trans hsmall (by norm_num)

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
  have hcode : Midfall.LoweringV2.vkCodehashArm R.model :=
    Midfall.LoweringV3.MemoryPairs.vkCodehashArm_of_generated h.generated h.supported.separateVk
  refine ⟨Midfall.LoweringV3.transcriptMptr_of_valid h, ?_, ?_⟩
  · refine
      { vkMptr := ?_
        payloadLen := ?_
        numInst := ?_
        disjoint := ?_ }
    · refine ⟨ptrAddr R.pv.memory.vkMptr, ?_, rfl⟩
      exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 h "VK_MPTR"
        (cAddr R.pv.memory.vkMptr) (Midfall.LoweringV2.expectedConsts_lookup_VK_MPTR _ _)
    · refine ⟨R.pv.vk.len, ?_, rfl⟩
      exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 h "EXPECTED_VK_PAYLOAD_LENGTH"
        R.pv.vk.len (Midfall.LoweringV2.expectedConsts_lookup_EXPECTED_VK_PAYLOAD_LENGTH _ _ hcode)
    · exact Midfall.LoweringV3.MemoryPairs.vkPins_numInst_of_generated h.generated h.inputs.1
    · exact Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_generated h.generated
  · refine { vkLen := ?_, vkHash := ?_ }
    · refine ⟨R.plan.vk.runtimeBytes.size, ?_, rfl⟩
      exact Midfall.LoweringV3.VkClean.consts_lookup_EXPECTED_VK_LENGTH_V3 h hcode
    · refine ⟨(keccak256 R.plan.vk.runtimeBytes).toNat, ?_, rfl⟩
      exact Midfall.LoweringV3.VkClean.consts_lookup_EXPECTED_VK_CODEHASH_WORD_V3 h hcode

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
  obtain ⟨meta_, vkMptr, config, _vkBase, hmem, hvk, hsize⟩ :=
    Midfall.LoweringV3.plan_size_of_generated (generated_of hg)
  have hvkfloor : 0x1560 ≤ ptrAddr (renderOf gi o).pv.memory.vkMptr := by
    rw [hmem, Midfall.LoweringV3.MemoryPairs.new_vkMptr, hvk,
      Midfall.LoweringV3.MemoryPairs.ptrAddr_valueFromNat]
    exact Midfall.LoweringV3.staticWorkingMemorySizeForMeta_floor meta_ _ hsize
  have htheta : ptrAddr (renderOf gi o).pv.memory.vkMptr ≤
      ptrAddr (renderOf gi o).pv.memory.thetaMptr := by
    rw [hmem, Midfall.LoweringV3.MemoryPairs.new_vkMptr]
    exact Midfall.LoweringV3.new_theta_ge_vk meta_ _ vkMptr config
  have hg1 : ptrAddr (renderOf gi o).pv.memory.thetaMptr ≤
      ptrAddr (renderOf gi o).pv.memory.g1IdentityMptr := by
    rw [hmem]
    rw [show ptrAddr (VerifierMemoryLayout.new meta_ (renderOf gi o).pv.vk vkMptr config).g1IdentityMptr =
      ptrAddr (VerifierMemoryLayout.new meta_ (renderOf gi o).pv.vk vkMptr config).thetaMptr
        + 209 * wordBytes from rfl]
    omega
  unfold Midfall.LoweringV3.g1IdentityFloor
  rw [decide_eq_true_eq]
  omega

/-- D-CERT1 / CERT.6: at least two Lagrange denominators (PG-NEGLAG). -/
theorem prog_negLagrangesFloor (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.negLagrangesFloor (renderOf gi o).pv = true := by
  unfold Midfall.LoweringV3.negLagrangesFloor
  rw [decide_eq_true_eq]
  have hneg := env_negLagranges hg hs
  obtain ⟨_m0, _payload, hraw, _hgenvk, _hfp, _h4⟩ := generate_spec hg
  obtain ⟨bf, hbf, _hrot, hbfge⟩ := constraintSystemMeta_new_rotationLast hraw
  rw [hneg, hbf]
  simp only [Except.toOption, Option.getD_some]
  omega

/-- D-CERT1 / CERT.6: one sigma commitment per permutation column (D-P59's repair). -/
theorem prog_permCommMatchRepaired (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.permCommMatchRepaired (renderOf gi o).vk = true := by
  show (gi.vk.permutation.commitments.size == gi.vk.cs.permutation.columns.size) = true
  exact beq_iff_eq.mpr hs.wf.permutationCommitmentsMatch

/-- D-CERT1 / CERT.5: `gas()` occurs only as a call's gas argument (D-P71 addition 1). -/
theorem prog_gasCallOk (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.GasCallOk ((renderOf gi o).prog 0 0) := by
  sorry -- CERT.5 (D3)

/-- D-CERT1 / CERT.5: the whole program executes no `gas()` at all (D-GATE1). -/
theorem prog_gasFree (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.GasFree ((renderOf gi o).prog 0 0) := by
  sorry -- CERT.5 (D3)

set_option maxHeartbeats 10000000 in
/-- `new`'s selector-accumulator base, in the arena's own arithmetic (`rfl`: a structure field is
    a thunk; the twenty-nine other allocations are not evaluated). `batchInvertScratchMptr` IS
    `selectorAccMptr`, so D-GATE11's batch floor reads this equation. -/
theorem new_selectorAccMptr_eq (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).selectorAccMptr =
      alignUp (alignUp (alignUp (alignUp (ptrAddr vkMptr + vk.len) wordBytes
          + meta_.challengeIndices.length * wordBytes) wordBytes
          + ThetaWindowLayout.compatibility.reversedEvalsWord * wordBytes
          + meta_.numEvals * wordBytes) wordBytes
          + commitmentG1Count meta_ * g1Bytes) wordBytes := rfl

theorem alignUp_step_le (x y : Nat) : x ≤ alignUp (x + y) wordBytes :=
  Nat.le_trans (Nat.le_add_right x y)
    (Midfall.LoweringV3.MemoryPairs.alignUp_le _ _ Midfall.LoweringV3.MemoryPairs.wordBytes_pos)

theorem alignUp_step2_le (x y z : Nat) : x ≤ alignUp (x + y + z) wordBytes :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_right x y) (Nat.le_add_right (x + y) z))
    (Midfall.LoweringV3.MemoryPairs.alignUp_le _ _ Midfall.LoweringV3.MemoryPairs.wordBytes_pos)

set_option maxHeartbeats 10000000 in
/-- **D-GATE11: `selectorAccMptr` is above the payload window.** Four monotone `alignUp` steps:
    the selector base is the fourth arena step after `vkMptr + vk.len`. This is the standalone
    form of `Totality`'s local `hp_selector` bound (there it is an inline `have`, not exported). -/
theorem new_selectorAccMptr_ge (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    ptrAddr vkMptr + vk.len ≤
      (VerifierMemoryLayout.new meta_ vk vkMptr config).selectorAccMptr := by
  let A := ptrAddr vkMptr + vk.len
  let C := meta_.challengeIndices.length * wordBytes
  let D := ThetaWindowLayout.compatibility.reversedEvalsWord * wordBytes
  let E := meta_.numEvals * wordBytes
  let F := commitmentG1Count meta_ * g1Bytes
  have h0 : A ≤ alignUp A wordBytes :=
    Midfall.LoweringV3.MemoryPairs.alignUp_le _ _ Midfall.LoweringV3.MemoryPairs.wordBytes_pos
  have h02 : alignUp A wordBytes ≤ alignUp (alignUp A wordBytes + C) wordBytes :=
    alignUp_step_le _ C
  have h2 : alignUp (alignUp A wordBytes + C) wordBytes ≤
      alignUp (alignUp (alignUp A wordBytes + C) wordBytes + D + E) wordBytes :=
    alignUp_step2_le _ D E
  have h3 : alignUp (alignUp (alignUp A wordBytes + C) wordBytes + D + E) wordBytes ≤
      alignUp (alignUp (alignUp (alignUp A wordBytes + C) wordBytes + D + E) wordBytes + F) wordBytes :=
    alignUp_step_le _ F
  have hexp : A ≤
      alignUp (alignUp (alignUp (alignUp A wordBytes + C) wordBytes + D + E) wordBytes + F) wordBytes :=
    Nat.le_trans h0 (Nat.le_trans h02 (Nat.le_trans h2 h3))
  have heq := new_selectorAccMptr_eq meta_ vk vkMptr config
  change A ≤ (VerifierMemoryLayout.new meta_ vk vkMptr config).selectorAccMptr
  rw [heq]
  simpa only [A, C, D, E, F] using hexp

/-- `packedPackWords` emits exactly the word count it is given. -/
theorem packedPackWords_length (bs : List Nat) (n : Nat) :
    (packedPackWords bs n).length = n := by
  induction n generalizing bs with
  | zero => simp [packedPackWords]
  | succ n ih => simp [packedPackWords, ih]

/-- `PackedProgramCodec.encodeWords` has exactly `wordLenForBytes` words. -/
theorem encodeWords_length (b : Bytes) :
    (PackedProgramCodec.encodeWords b).length =
      PackedProgramCodec.wordLenForBytes (bytesToList b).length := by
  unfold PackedProgramCodec.encodeWords
  exact packedPackWords_length _ _

/-- A byte length fits in the rounded-up word count. -/
theorem wordLenForBytes_le_mul (n : Nat) :
    n ≤ 32 * PackedProgramCodec.wordLenForBytes n := by
  unfold PackedProgramCodec.wordLenForBytes
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  rw [hw]
  have hmod := Nat.mod_lt (n + 31) (by norm_num : 0 < 32)
  have hdiv := Nat.div_add_mod (n + 31) 32
  have h : n ≤ (n + 31) / 32 * 32 := by omega
  simpa [Nat.mul_comm] using h

theorem proofLen_eq_repackedLen_at (protocol : Midfall.Generator.ProtocolPlan)
    (cptr numEvals numPointSets : Nat) (L : ProofCalldataLayout)
    (h : ProofCalldataLayout.fromProtocol protocol cptr numEvals numPointSets = .ok L) :
    L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen ∧
      L.proofEnd = L.proofCptr + L.proofLen := by
  rw [ProofCalldataLayout.fromProtocol] at h
  simp only [Bind.bind] at h
  obtain ⟨x1, hx1, h1⟩ := except_bind_ok _ _ h
  obtain ⟨x2, hx2, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨x3, hx3, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨x4, hx4, h4⟩ := except_bind_ok _ _ h3
  obtain ⟨x5, hx5, h5⟩ := except_bind_ok _ _ h4
  obtain ⟨x6, hx6, h6⟩ := except_bind_ok _ _ h5
  by_cases hc : (x6.2.1 != protocol.proof.commitments.length) = true
  · rw [ite_eq_left hc] at h6
    obtain ⟨r, hr, _⟩ := except_bind_ok _ _ h6
    cases hr
  · rw [ite_eq_right (by simpa using hc)] at h6
    let ws6 := ProofCalldataLayout.wordSection x6.2.2 numEvals
    let fc := Midfall.Generator.ProofSection.new ws6.2 1 Midfall.Generator.g1Bytes
    let ws8 := ProofCalldataLayout.wordSection fc.end numPointSets
    let piS := Midfall.Generator.ProofSection.new ws8.2 1 Midfall.Generator.g1Bytes
    have hcptrE : L.proofCptr = cptr := by cases h6; rfl
    have hadvE : L.advicePhases = x1.1 := by cases h6; rfl
    have hlmE : L.lookupMultiplicities = x2.1 := by cases h6; rfl
    have hppE : L.permutationProducts = x3.1 := by cases h6; rfl
    have hlksE : L.lookups = x4.1 := by cases h6; rfl
    have htrE : L.trash = x5.1 := by cases h6; rfl
    have hqlE : L.quotientLimbs = x6.1 := by cases h6; rfl
    have hevE : L.evals = ws6.1 := by cases h6; rfl
    have hfE : L.fCom = fc := by cases h6; rfl
    have hqE : L.qEvals = ws8.1 := by cases h6; rfl
    have hpeE : L.proofEnd = piS.end := by cases h6; rfl
    have hplE : L.proofLen = piS.end - cptr := by cases h6; rfl
    let lks := (List.range protocol.lookupChunks.length).zip protocol.lookupChunks
    have h1' := foldlM_take_ok protocol Midfall.Generator.CommitmentRead.advice "advice phase"
      protocol.numUserAdvices ([], 0, cptr) x1 hx1 (by intro s hs; simp at hs)
    have h2' := takeCommitmentSection_ok protocol x1.2.1 x1.2.2 protocol.numLookups
      Midfall.Generator.CommitmentRead.lookupMultiplicity "lookup multiplicity" x2.1 x2.2.1 x2.2.2 hx2
    have h3' := takeCommitmentSection_ok protocol x2.2.1 x2.2.2 protocol.numPermutationZs
      Midfall.Generator.CommitmentRead.permutationProduct "permutation product" x3.1 x3.2.1 x3.2.2 hx3
    have h4' := foldlM_lookups_ok protocol lks ([], x3.2.1, x3.2.2) x4 hx4
      (by intro r hr; simp at hr)
    have h5' := takeCommitmentSection_ok protocol x4.2.1 x4.2.2 protocol.numTrashcans
      Midfall.Generator.CommitmentRead.trash "trash" x5.1 x5.2.1 x5.2.2 hx5
    have h6' := takeCommitmentSection_ok protocol x5.2.1 x5.2.2 protocol.numQuotients
      Midfall.Generator.CommitmentRead.quotient "quotient limb" x6.1 x6.2.1 x6.2.2 hx6
    have e2 : x2.1.itemCount = protocol.numLookups := by rw [h2'.1]; rfl
    have e3 : x3.1.itemCount = protocol.numPermutationZs := by rw [h3'.1]; rfl
    have e5 : x5.1.itemCount = protocol.numTrashcans := by rw [h5'.1]; rfl
    have e6 : x6.1.itemCount = protocol.numQuotients := by rw [h6'.1]; rfl
    have hg : Midfall.Generator.g1Bytes = 128 := rfl
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    have hCG : L.commitmentG1Count = sumNat protocol.numUserAdvices + protocol.numLookups
        + protocol.numPermutationZs + sumNat (lks.map (fun p => p.2 + 1))
        + protocol.numTrashcans + protocol.numQuotients := by
      simp only [ProofCalldataLayout.commitmentG1Count, ProofCalldataLayout.nonQuotientG1Count,
        hadvE, hlmE, hppE, hlksE, htrE, hqlE]
      show sumNat (x1.1.map (fun s => s.itemCount)) + x2.1.itemCount + x3.1.itemCount
          + sumNat (x4.1.map (fun r => r.helpers.itemCount + r.accumulator.itemCount))
          + x5.1.itemCount + x6.1.itemCount = _
      rw [h1'.2.2, h4'.2.2, e2, e3, e5, e6]
      simp only [List.map_nil, sumNat_nil, Nat.zero_add]
    have hc6 : x6.2.2 = cptr + Midfall.Generator.g1Bytes * L.commitmentG1Count := by
      rw [h6'.2, h5'.2, h4'.1, h3'.2, h2'.2, h1'.1, sumNat_map_mul, hCG, hg]
      ring
    have hws6 : ws6.2 = x6.2.2 + numEvals * Midfall.Generator.wordBytes := rfl
    have hfc : fc.end = ws6.2 + 1 * Midfall.Generator.g1Bytes := rfl
    have hws8 : ws8.2 = fc.end + numPointSets * Midfall.Generator.wordBytes := rfl
    have hpi : piS.end = ws8.2 + 1 * Midfall.Generator.g1Bytes := rfl
    have hpe2 : piS.end = cptr + (Midfall.Generator.g1Bytes * L.commitmentG1Count + numEvals * Midfall.Generator.wordBytes
        + numPointSets * Midfall.Generator.wordBytes + 2 * Midfall.Generator.g1Bytes) := by
      rw [hpi, hws8, hfc, hws6, hc6]
      ring
    have hge : piS.end ≥ cptr := by rw [hpe2]; omega
    refine ⟨?_, ?_⟩
    · rw [hplE, hpe2, Nat.add_sub_cancel_left]
      have hrep : (RepackedProofLayoutPlan.fromProofLayout L).repackedLen
          = L.commitmentG1Count * Midfall.Generator.g1Bytes + L.evals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
            + L.qEvals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes := by
        show (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count * Midfall.Generator.g1Bytes
            + (RepackedProofLayoutPlan.fromProofLayout L).numEvals * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
            + (RepackedProofLayoutPlan.fromProofLayout L).numPointSets * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes = _
        rw [sum_commitmentReadGroups L]
        rfl
      rw [hrep, hevE, hqE]
      have f1 : ws6.1.itemCount = numEvals := rfl
      have f2 : ws8.1.itemCount = numPointSets := rfl
      rw [f1, f2, hCG, hg, hw]
      ring
    · rw [hplE, hcptrE, hpeE, hpe2, Nat.add_sub_cancel_left]

theorem tp_fromProtocol_at {meta_ : ConstraintSystemMeta} {L : ProofCalldataLayout}
    (cptr : Nat)
    (hL : ProofCalldataLayout.fromProtocol meta_.protocol cptr
      meta_.numEvals meta_.numPointSets = .ok L) :
    Midfall.LoweringV3.TranscriptRows.TpLayoutFacts meta_ L := by
  unfold ProofCalldataLayout.fromProtocol at hL
  simp only [Bind.bind, Except.bind] at hL
  obtain ⟨adv, hAdv, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lm, hLM, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨pp, hPP, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lks, hLksFold, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨tr, hTr, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨ql, hQl, hL⟩ := except_bind_ok _ _ hL
  split at hL
  · cases hL
  cases hL
  have hadv := foldlM_take_ok meta_.protocol CommitmentRead.advice "advice phase"
    meta_.protocol.numUserAdvices ([], 0, cptr) adv hAdv (by simp)
  have hadvLen := foldlM_take_length meta_.protocol CommitmentRead.advice "advice phase"
    meta_.protocol.numUserAdvices ([], 0, cptr) adv hAdv
  have hlm := takeCommitmentSection_shape meta_.protocol adv.2.1 adv.2.2
    CommitmentRead.lookupMultiplicity meta_.protocol.numLookups "lookup multiplicity" hLM
  have hpp := takeCommitmentSection_shape meta_.protocol lm.2.1 lm.2.2
    CommitmentRead.permutationProduct meta_.protocol.numPermutationZs "permutation product" hPP
  have hLks := foldlM_lookups_ok meta_.protocol
    ((List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold (by simp)
  have hLksLen := foldlM_lookups_length meta_.protocol
    ((List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold
  have hLksAcc := foldlM_lookups_accOne meta_.protocol
    ((List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold (by simp)
  have htr := takeCommitmentSection_shape meta_.protocol lks.2.1 lks.2.2
    CommitmentRead.trash meta_.protocol.numTrashcans "trash" hTr
  have hql := takeCommitmentSection_shape meta_.protocol tr.2.1 tr.2.2
    CommitmentRead.quotient meta_.protocol.numQuotients "quotient limb" hQl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hadv.2.1 s hs).1
  · intro s hs
    exact (hadv.2.1 s hs).2
  · rw [hadvLen]
    simp
  · simpa [sumNat_nil] using hadv.2.2
  · exact hlm.1
  · exact hlm.2.2
  · exact hpp.1
  · exact hpp.2.2
  · rw [hLksLen, List.length_zip, List.length_range]
    simp
  · intro lk hlk
    obtain ⟨hg, ha⟩ := hLks.2.1 lk hlk
    have ha2 := ha.2
    rw [hLksAcc lk hlk] at ha2
    exact ⟨hg.1, hg.2, ha.1, by simpa using ha2⟩
  · exact hLksAcc
  · simpa [sumNat_nil] using hLks.2.2
  · exact htr.1
  · exact htr.2.2
  · exact hql.1
  · exact hql.2.2
  · rfl
  · rfl
  · rfl
  · rfl


/-- **D-GATE11: `fromProtocol`'s proof payload length is below `2 ^ 80`.** The same
    `tp_fromProtocol` + `proofLen_eq_repackedLen` arithmetic as `v3_cdBound`, factored out for
    the transcript-buffer bound. Counts come from `MetaCountsBound`; no render is mentioned. -/
theorem proofLen_lt_of_fromProtocol {meta_ m0 : ConstraintSystemMeta} {L : ProofCalldataLayout}
    (cptr : Nat) (hM : MetaCountsBound m0) (hProtocol : meta_.protocol = m0.protocol)
    (hEval : meta_.numEvals < 2 ^ 32) (hPoint : meta_.numPointSets < 2 ^ 32)
    (hL : ProofCalldataLayout.fromProtocol meta_.protocol cptr
      meta_.numEvals meta_.numPointSets = .ok L) :
    L.proofLen < 2 ^ 80 := by
  have hfacts := tp_fromProtocol_at cptr hL
  have hpen := proofLen_eq_repackedLen_at meta_.protocol cptr meta_.numEvals meta_.numPointSets L hL
  have hCG : L.commitmentG1Count = sumNat meta_.protocol.numUserAdvices
      + meta_.protocol.numLookups + meta_.protocol.numPermutationZs
      + sumNat (((List.range meta_.protocol.lookupChunks.length).zip
          meta_.protocol.lookupChunks).map (fun q => q.2 + 1))
      + meta_.protocol.numTrashcans + meta_.protocol.numQuotients := by
    rw [show L.commitmentG1Count =
        sumNat (L.advicePhases.map (fun s => s.itemCount))
        + L.lookupMultiplicities.itemCount + L.permutationProducts.itemCount
        + sumNat (L.lookups.map (fun lk => lk.helpers.itemCount + lk.accumulator.itemCount))
        + L.trash.itemCount + L.quotientLimbs.itemCount from rfl]
    rw [hfacts.adviceSum, hfacts.lookupM, hfacts.permZ, hfacts.lookupSum,
      hfacts.trash, hfacts.quotient]
  have hAdvSum : sumNat meta_.protocol.numUserAdvices ≤ 2 ^ 32 * 2 ^ 32 := by
    have h1 : sumNat meta_.protocol.numUserAdvices
        ≤ meta_.protocol.numUserAdvices.length * 2 ^ 32 := by
      rw [hProtocol]
      exact sumNat_le_length_mul (fun x hx => Nat.le_of_lt (hM.userAdvicesEach x hx))
    have h2 : meta_.protocol.numUserAdvices.length < 2 ^ 32 := by
      rw [hProtocol]; exact hM.userAdvicesLen
    nlinarith
  have hLkSum : sumNat (((List.range meta_.protocol.lookupChunks.length).zip
      meta_.protocol.lookupChunks).map (fun q => q.2 + 1)) ≤ 2 ^ 32 * 2 ^ 32 := by
    have hmap : ((List.range meta_.protocol.lookupChunks.length).zip
        meta_.protocol.lookupChunks).map (fun q => q.2 + 1)
        = meta_.protocol.lookupChunks.map (fun n => n + 1) := by
      let l := (List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks
      have hm : List.map (fun q => q.2 + 1) l = List.map (fun n => n + 1) (l.map Prod.snd) := by
        rw [List.map_map]
        rfl
      rw [hm, Midfall.LoweringV3.TranscriptRows.zip_range_snd]
    rw [hmap]
    have h1 : sumNat (meta_.protocol.lookupChunks.map (fun n => n + 1))
        ≤ meta_.protocol.lookupChunks.length * 2 ^ 32 := by
      have h := sumNat_le_length_mul
        (l := meta_.protocol.lookupChunks.map (fun n => n + 1)) (B := 2 ^ 32) (by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨n, hn, rfl⟩ := hx
          rw [hProtocol] at hn
          have := hM.lookupChunksEach n hn
          omega)
      simpa using h
    have h2 : meta_.protocol.lookupChunks.length < 2 ^ 32 := by
      rw [hProtocol]; exact hM.lookupChunksLen
    nlinarith
  have hCCount : L.commitmentG1Count < 2 ^ 66 := by
    rw [hCG]
    have hLk : meta_.protocol.numLookups < 2 ^ 32 := by rw [hProtocol]; exact hM.lookups
    have hPs : meta_.protocol.numPermutationZs < 2 ^ 32 := by rw [hProtocol]; exact hM.permutationZs
    have hTr : meta_.protocol.numTrashcans < 2 ^ 32 := by rw [hProtocol]; exact hM.trashcans
    have hQ : meta_.protocol.numQuotients < 2 ^ 32 := by rw [hProtocol]; exact hM.quotients
    nlinarith
  have hRep : L.proofLen = 128 * L.commitmentG1Count + 32 * meta_.numEvals
      + 128 + 32 * meta_.numPointSets + 128 := by
    rw [hpen.1]
    change (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count * Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numEvals * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numPointSets * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes = _
    rw [sum_commitmentReadGroups]
    change L.commitmentG1Count * Midfall.Generator.g1Bytes
        + L.evals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
        + L.qEvals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes = _
    rw [hfacts.evals, hfacts.qEvals]
    have hg1 : Midfall.Generator.g1Bytes = 128 := rfl
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hg1, hw]
    ring
  rw [hRep]
  nlinarith [hCCount, hEval, hPoint, Nat.zero_le L.commitmentG1Count]

/-- The stop-flag fold used by `TranscriptBufferLayout.fromProofLayout`. -/
def preSqueezeStep (phase : List Nat) (st : Nat × Bool) (pair : Nat × ProofSection) : Nat × Bool :=
  let (p, sect) := pair
  if st.2 then st else (st.1 + sect.itemCount, (phase[p]?.getD 0) > 0)

/-- Prefix sums of advice sections never exceed the total advice item count. -/
theorem preSqueezeFold_le (l : List (Nat × ProofSection)) (phase : List Nat) (acc : Nat)
    (stop : Bool) :
    (l.foldl (preSqueezeStep phase) (acc, stop)).1
      ≤ acc + sumNat (l.map (fun p => p.2.itemCount)) := by
  induction l generalizing acc stop with
  | nil => simp [preSqueezeStep]
  | cons a as ih =>
      simp only [List.foldl_cons, List.map_cons, sumNat_cons]
      by_cases hstop : stop
      · simp [preSqueezeStep, hstop]
        have h := ih acc true
        omega
      · simp [preSqueezeStep, hstop]
        have h := ih (acc + a.2.itemCount) (0 < phase[a.1]?.getD 0)
        omega

/-- The `preSqueezeAdvices` component of `fromProofLayout` is at most the advice item sum. -/
theorem preSqueeze_le_adviceSum (proof : ProofCalldataLayout) (phase : List Nat) :
    (((List.range proof.advicePhases.length).zip proof.advicePhases).foldl
      (fun st pair =>
        let (p, sect) := pair
        if st.snd then st else (st.fst + sect.itemCount, (phase.getD p 0) > 0))
      (0, false)).1
      ≤ sumNat (proof.advicePhases.map (fun s => s.itemCount)) := by
  have h := preSqueezeFold_le
    ((List.range proof.advicePhases.length).zip proof.advicePhases) phase 0 false
  have hz : ((List.range proof.advicePhases.length).zip proof.advicePhases).map
      (fun p => p.2) = proof.advicePhases := by
    induction proof.advicePhases with
    | nil => simp
    | cons a as ih =>
        rw [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons]
        rw [List.zip_map_left, List.map_map]
        simp only [Function.comp_def, Prod.map, id_eq]
        rw [ih]
  have hmap : (((List.range proof.advicePhases.length).zip proof.advicePhases).map
      (fun p => p.2.itemCount)) =
      proof.advicePhases.map (fun s => s.itemCount) := by
    change List.map ((fun s => s.itemCount) ∘ Prod.snd)
      ((List.range proof.advicePhases.length).zip proof.advicePhases) = _
    rw [← List.map_map, hz]
  change (List.foldl (preSqueezeStep phase) (0, false)
    ((List.range proof.advicePhases.length).zip proof.advicePhases)).1 ≤
    sumNat (proof.advicePhases.map (fun s => s.itemCount))
  simpa [hmap] using h

/-- `fromProtocol`'s `fCom` section is one G1 item. -/
theorem fromProtocol_fCom_itemCount {protocol : ProtocolPlan} {cptr numEvals numPointSets : Nat}
    {L : ProofCalldataLayout}
    (h : ProofCalldataLayout.fromProtocol protocol cptr numEvals numPointSets = .ok L) :
    L.fCom.itemCount = 1 := by
  unfold ProofCalldataLayout.fromProtocol at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨x1, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨x2, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨x3, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨x4, _, h4⟩ := cert_except_bind_ok h3
  obtain ⟨x5, _, h5⟩ := cert_except_bind_ok h4
  obtain ⟨x6, _, h6⟩ := cert_except_bind_ok h5
  split at h6
  · cases h6
  · cases h6
    rfl

/-- `fromProtocol`'s `pi` section is one G1 item. -/
theorem fromProtocol_pi_itemCount {protocol : ProtocolPlan} {cptr numEvals numPointSets : Nat}
    {L : ProofCalldataLayout}
    (h : ProofCalldataLayout.fromProtocol protocol cptr numEvals numPointSets = .ok L) :
    L.pi.itemCount = 1 := by
  unfold ProofCalldataLayout.fromProtocol at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨x1, _, h1⟩ := cert_except_bind_ok h
  obtain ⟨x2, _, h2⟩ := cert_except_bind_ok h1
  obtain ⟨x3, _, h3⟩ := cert_except_bind_ok h2
  obtain ⟨x4, _, h4⟩ := cert_except_bind_ok h3
  obtain ⟨x5, _, h5⟩ := cert_except_bind_ok h4
  obtain ⟨x6, _, h6⟩ := cert_except_bind_ok h5
  split at h6
  · cases h6
  · cases h6
    rfl

/-- `divCeil a 32 ≤ a + 1`. -/
theorem divCeil32_le_succ (a : Nat) : Midfall.Generator.QuotientFoldCompute.divCeil a 32 ≤ a + 1 := by
  unfold Midfall.Generator.QuotientFoldCompute.divCeil
  have h32 : (32 == 0) = false := rfl
  rw [h32]
  simp only [Bool.false_eq_true, ite_false]
  have h : a + 31 ≤ 32 * (a + 1) := by nlinarith
  exact Nat.div_le_of_le_mul h

set_option maxHeartbeats 2000000 in
/-- The G1 census fits the proof payload: `totalG1Count * 128 ≤ proofLen`. -/
theorem fromProtocol_totalG1Count_le_proofLen {meta_ : ConstraintSystemMeta}
    {cptr : Nat} {L : ProofCalldataLayout}
    (hL : ProofCalldataLayout.fromProtocol meta_.protocol cptr meta_.numEvals
      meta_.numPointSets = .ok L) :
    L.totalG1Count * 128 ≤ L.proofLen := by
  have hf := fromProtocol_fCom_itemCount hL
  have hp := fromProtocol_pi_itemCount hL
  have hpen := proofLen_eq_repackedLen_at meta_.protocol cptr meta_.numEvals
    meta_.numPointSets L hL
  have hfacts := tp_fromProtocol_at cptr hL
  have htotal : L.totalG1Count = L.commitmentG1Count + 2 := by
    simp only [ProofCalldataLayout.totalG1Count, hf, hp]
  have hrep : L.proofLen = 128 * L.commitmentG1Count + 32 * meta_.numEvals
      + 128 + 32 * meta_.numPointSets + 128 := by
    rw [hpen.1]
    change (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count * Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numEvals * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numPointSets * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes = _
    rw [sum_commitmentReadGroups]
    change L.commitmentG1Count * Midfall.Generator.g1Bytes
        + L.evals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
        + L.qEvals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes = _
    rw [hfacts.evals, hfacts.qEvals]
    have hg1 : Midfall.Generator.g1Bytes = 128 := rfl
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hg1, hw]
    ring
  rw [htotal, hrep]
  omega

set_option maxHeartbeats 2000000 in
/-- The quotient/evals/qEvals byte lengths fit the proof length. -/
theorem fromProtocol_byteLens_le_proofLen {meta_ : ConstraintSystemMeta}
    {cptr : Nat} {L : ProofCalldataLayout}
    (hL : ProofCalldataLayout.fromProtocol meta_.protocol cptr meta_.numEvals
      meta_.numPointSets = .ok L) :
    L.quotientLimbs.byteLen + L.evals.byteLen + L.qEvals.byteLen ≤ L.proofLen := by
  have hpen := proofLen_eq_repackedLen_at meta_.protocol cptr meta_.numEvals
    meta_.numPointSets L hL
  have hfacts := tp_fromProtocol_at cptr hL
  have hrep : L.proofLen = 128 * L.commitmentG1Count + 32 * meta_.numEvals
      + 128 + 32 * meta_.numPointSets + 128 := by
    rw [hpen.1]
    change (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count * Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numEvals * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes
        + (RepackedProofLayoutPlan.fromProofLayout L).numPointSets * Midfall.Generator.wordBytes
        + Midfall.Generator.g1Bytes = _
    rw [sum_commitmentReadGroups]
    change L.commitmentG1Count * Midfall.Generator.g1Bytes
        + L.evals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
        + L.qEvals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes = _
    rw [hfacts.evals, hfacts.qEvals]
    have hg1 : Midfall.Generator.g1Bytes = 128 := rfl
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    rw [hg1, hw]
    ring
  have hq : L.quotientLimbs.byteLen ≤ 128 * L.commitmentG1Count := by
    rw [hfacts.quotientByte, ← hfacts.quotient]
    have hle : L.quotientLimbs.itemCount ≤ L.commitmentG1Count := by
      simp only [ProofCalldataLayout.commitmentG1Count, ProofCalldataLayout.nonQuotientG1Count]
      omega
    calc L.quotientLimbs.itemCount * 128 ≤ L.commitmentG1Count * 128 :=
          Nat.mul_le_mul_right 128 hle
      _ = 128 * L.commitmentG1Count := Nat.mul_comm _ _
  have he : L.evals.byteLen = 32 * meta_.numEvals := by
    rw [hfacts.evalsByte, show Midfall.Generator.wordBytes = 32 from rfl, Nat.mul_comm]
  have hq2 : L.qEvals.byteLen = 32 * meta_.numPointSets := by
    rw [hfacts.qEvalsByte, show Midfall.Generator.wordBytes = 32 from rfl, Nat.mul_comm]
  rw [hrep, hq2, he]
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- A `fromProofLayout` transcript has fewer than `2 ^ 90` words once the advice prefix, G1
    census and scalar byte lengths fit `proofLen`. -/
theorem fromProofLayout_words_lt (proof : ProofCalldataLayout) (numInstances : Nat)
    (phase : List Nat)
    (hpre : (((List.range proof.advicePhases.length).zip proof.advicePhases).foldl
      (fun st pair =>
        let (p, sect) := pair
        if st.snd then st else (st.fst + sect.itemCount, (phase.getD p 0) > 0))
      (0, false)).1 ≤ 2 ^ 64)
    (hPL : proof.proofLen < 2 ^ 80)
    (htot : proof.totalG1Count * 128 ≤ proof.proofLen)
    (hbytes : proof.quotientLimbs.byteLen + proof.evals.byteLen + proof.qEvals.byteLen
      ≤ proof.proofLen)
    (hNI : numInstances < 2 ^ 64) :
    (TranscriptBufferLayout.fromProofLayout proof numInstances phase).words < 2 ^ 83 := by
  unfold TranscriptBufferLayout.fromProofLayout
  set pre := (((List.range proof.advicePhases.length).zip proof.advicePhases).foldl
    (fun st pair =>
      let (p, sect) := pair
      if st.snd then st else (st.fst + sect.itemCount, (phase.getD p 0) > 0))
    (0, false)).1 with hpredef
  set initial := 32 + 128 + 32 + numInstances * 32 + pre * 128 + 1024 with hinit
  set evalR := proof.quotientLimbs.byteLen + proof.evals.byteLen + proof.qEvals.byteLen
    + 1024 with heval
  set totalR := 32 + proof.totalG1Count * 128
    + (proof.evals.byteLen + proof.qEvals.byteLen) + 1024 + 1024 with htotal
  have hpre' : pre ≤ 2 ^ 64 := by simpa [hpredef] using hpre
  have hinit' : initial < 2 ^ 72 := by rw [hinit]; nlinarith
  have heval' : evalR < 2 ^ 81 := by rw [heval]; nlinarith
  have htotal' : totalR < 2 ^ 82 := by rw [htotal]; nlinarith
  have hmax : max (max initial evalR) totalR < 2 ^ 82 := by
    exact max_lt (max_lt (by omega) (by omega)) (by omega)
  have hwords : Midfall.Generator.QuotientFoldCompute.divCeil
      (max (max initial evalR) totalR) 32 ≤ max (max initial evalR) totalR + 1 :=
    divCeil32_le_succ _
  change Midfall.Generator.QuotientFoldCompute.divCeil
    (max (max initial evalR) totalR) 32 < 2 ^ 83
  omega

theorem foldl_max_le (l : List Nat) (a B : Nat) (ha : a ≤ B)
    (h : ∀ x ∈ l, x ≤ B) : l.foldl (fun a b => max a b) a ≤ B := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (max a x) (max_le ha (h x (by simp))) (fun y hy => h y (by simp [hy]))

theorem natMaximum_le_of_forall_le {l : List Nat} {v B : Nat}
    (hv : natMaximum l = some v) (h : ∀ x ∈ l, x ≤ B) : v ≤ B := by
  cases l with
  | nil => simp [natMaximum] at hv
  | cons x xs =>
      simp only [natMaximum, Option.some.injEq] at hv
      subst hv
      exact foldl_max_le xs x B (h x (by simp)) (fun y hy => h y (by simp [hy]))

/-- The render's proof layout length bound, from the count clause. -/
theorem plan_proofLen_lt {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}
    (hg : Generates gi o) (hs : SupportedInput gi) :
    (renderOf gi o).plan.proofLayout.proofLen < 2 ^ 80 := by
  obtain ⟨m0, _payload, hraw, _hgenvk, _hfp, _h4⟩ := generate_spec hg
  obtain ⟨rawMeta, plan, hraw', hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  simp only [renderOf] at hraw' hpl
  rw [hraw] at hraw'
  cases hraw'
  obtain ⟨meta_, L, hmeta, hLplan, hL⟩ :=
    newFromVk_plan_meta_proofLayout Features.solidity (frFieldCtx gi.E.delta) gi.vk.cs
      m0 gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  have hr : rawMetaOf gi = some m0 := by
    unfold rawMetaOf
    rw [hraw]
  have hM : MetaCountsBound m0 := hs.countBound.metaCounts m0 hr
  have hmetaFacts := Midfall.LoweringV3.newFromVk_meta_numEvals (frFieldCtx gi.E.delta)
    gi.vk.cs m0 gi.cfg.numInstances gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
  rw [hmeta] at hmetaFacts
  have hEval : meta_.numEvals < 2 ^ 32 := by
    rw [hmetaFacts.1]; exact hM.evals
  have hPointLe : meta_.numPointSets ≤ m0.protocol.pcsQueries.length := by
    have h := newFromVk_numPointSets_le (frFieldCtx gi.E.delta) gi.vk.cs m0 gi.cfg.numInstances
      gi.cfg.accumulator (renderOf gi o).plan.vk plan hpl
    rwa [hmeta] at h
  have hPoint : meta_.numPointSets < 2 ^ 32 := lt_of_le_of_lt hPointLe hM.pcsQueries
  have hlen := proofLen_lt_of_fromProtocol _ hM hmetaFacts.2 hEval hPoint hL
  rw [hp]
  rw [hLplan]
  exact hlen


/-- **D-GATE11: the quotient program's byte size from `vkCarriesBuild`.** The encoded program is
    the VK reservation's `quotientProgramWords`, and the raw bytes are at most the word count
    times the 32-byte word stride. This is the first builder-size bound the static layout needs;
    it does not use `maxStack`. PROVED. -/
theorem build_bytes_size_le (vk : Halo2VerifyingKey) (build : QuotientProgramBuild)
    (h : Midfall.Generator.PlanNew.vkCarriesBuild vk build = true) :
    build.bytes.size ≤ 32 * vk.quotientProgramWords := by
  have hprog : (PackedProgramCodec.encodeWords build.bytes).length ≤
      vk.quotientProgramWords := by
    unfold Midfall.Generator.PlanNew.vkCarriesBuild at h
    split at h
    · rename_i qc qp hqc hqp
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨_, hprog⟩ := h
      change List.take vk.quotientProgramWords
          (List.drop qp (List.map (fun x => x.2) vk.constants)) =
        PackedProgramCodec.encodeWords build.bytes ++
          List.replicate (vk.quotientProgramWords -
            (PackedProgramCodec.encodeWords build.bytes).length) 0 at hprog
      have hlen := congrArg List.length hprog
      have htake : (List.take vk.quotientProgramWords
          (List.drop qp (List.map (fun x => x.2) vk.constants))).length ≤
          vk.quotientProgramWords := by
        rw [List.length_take]
        omega
      simp only [List.length_append, List.length_replicate] at hlen
      omega
    · cases h
  have hsize : build.bytes.size ≤
      32 * (PackedProgramCodec.encodeWords build.bytes).length := by
    rw [encodeWords_length]
    have hb : (bytesToList build.bytes).length = build.bytes.size := by simp [bytesToList]
    rw [hb]
    exact wordLenForBytes_le_mul _
  omega

/-- **D-GATE11: the batch-invert scratch floor, from `generated`.** `batchInvertScratchMptr` is
    `selectorAccMptr` (`rfl`), which is above the payload window; the payload floor is
    `0x1560` (`staticWorkingMemorySizeForMeta_floor`), so the `32` the batch-inversion walk
    subtracts never reaches the EVM scratch. PROVED. -/
theorem batchInvertScratchFits_of_generated {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}
    (hg : Generates gi o) :
    Midfall.LoweringV3.batchInvertScratchFits (renderOf gi o).pv := by
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, hvk, hsize⟩ :=
    Midfall.LoweringV3.plan_size_of_generated (generated_of hg)
  unfold Midfall.LoweringV3.batchInvertScratchFits
  rw [hmem]
  have hfloorSize : 0x1560 ≤ vkBase :=
    Midfall.LoweringV3.staticWorkingMemorySizeForMeta_floor meta_
      (renderOf gi o).cfg.numInstances hsize
  have hfloor : 0x1560 ≤ ptrAddr vkMptr + (renderOf gi o).pv.vk.len := by
    rw [hvk, Midfall.LoweringV3.MemoryPairs.ptrAddr_valueFromNat]
    omega
  have hsel := new_selectorAccMptr_ge meta_ (renderOf gi o).pv.vk vkMptr config
  have hbatch :
      (VerifierMemoryLayout.new meta_ (renderOf gi o).pv.vk vkMptr config).batchInvertScratchMptr =
        (VerifierMemoryLayout.new meta_ (renderOf gi o).pv.vk vkMptr config).selectorAccMptr := rfl
  rw [hbatch]
  omega

/-- **D-GATE16 corollary: the generated build's stack fits the payload reservation.** The
    generated-build stack clause (`SupportedInput.stackBound`) and `build_bytes_size_le` together
    give `build.maxStack ≤ 32 * vk.quotientProgramWords`, the bound `quotientStackWordsForBuild`
    consumes. PROVED. -/
theorem generated_build_stack_words_le {gi : GenInput p G₁ G₂ Gₜ} {o : CertOut}
    (hg : Generates gi o) (hs : SupportedInput gi) :
    ∀ b, quotientBuildOf (renderOf gi o).plan = some b →
      b.maxStack ≤ 32 * (renderOf gi o).plan.vk.quotientProgramWords := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_of_generated (generated_of hg)
  obtain ⟨q, _memory, _vkMptr, _constOff, _progOff, _meta2, _config,
    hq, _hmem, _hnew, _hco, _hpo, _hfit, hvg, _hcm, _hsm, _hguards⟩ :=
    Midfall.LoweringV3.MemoryPairs.newFromVk_windows Features.solidity
      (frFieldCtx gi.E.delta) gi.vk.cs rawMeta gi.cfg.numInstances gi.cfg.accumulator
      (renderOf gi o).plan.vk plan hpl
  intro b hb
  have hp' : o.out.plan = plan := by simpa [renderOf] using hp
  have hbq : b = q.build := by
    have hb' : Option.map (fun q => q.build) plan.quotient = some b := by
      simp only [renderOf] at hb
      rw [hp'] at hb
      exact hb
    rw [hq] at hb'
    exact (Option.some.inj (by simpa using hb')).symm
  subst hbq
  have hstack := hs.stackBound o hg q.build (by
    change quotientBuildOf (renderOf gi o).plan = some q.build
    simpa [quotientBuildOf, renderOf, hp'] using (show quotientBuildOf plan = some q.build by
      unfold quotientBuildOf
      rw [hq]
      rfl))
  have hbytes := build_bytes_size_le plan.vk q.build (by
    simpa [← hp] using hvg)
  simpa [renderOf, hp'] using Nat.le_trans hstack hbytes

/-- D-CERT1 / CERT.6: the address-fit invariant (D-QVM1), VK window and quotient interpreter.

    D-GATE11 reduced the `v3_cdBound` half, the point-set census, and `batchInvertScratchFits`
    (`batchInvertScratchFits_of_generated` via the exported `new_selectorAccMptr_ge`) to the input
    count budget (`CountBound`). The quotient program's byte size is proved from `vkCarriesBuild`
    (`build_bytes_size_le`: `build.bytes.size ≤ 32 * vk.quotientProgramWords`) and D-GATE16's
    `SupportedInput.stackBound` supplies the generated-build stack inequality
    (`build.maxStack ≤ build.bytes.size`) that the unported QVM:1217-1222 validator would otherwise
    have to prove. The residual is now the LAYOUT ARITHMETIC: bound `staticWorkingMemorySizeForMeta`
    (the transcript-word count), the six `VerifierMemoryLayoutConfig` overrides
    (`quotientStateWords`, `quotientStackWords`, `accMsmTerms`, the PCS requirements), and then the
    twenty-three `traceU256Bound` candidates; `quotientProgramFits` needs the same config/selector
    (`selectorFold.maxPower`) bounds. No `ValidV3`, row or root hypothesis is involved;
    `SupportedInput` was strengthened, not weakened. -/
theorem prog_programFits (hg : Generates gi o) (hs : SupportedInput gi) :
    Midfall.LoweringV3.programFits (renderOf gi o).pv (renderOf gi o).model := by
  sorry -- CERT.6 (D4), residual documented above (quotient-build sizing)

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
#print axioms Midfall.Generator.Certified.v3_planMeta
#assert_axioms Midfall.Generator.Certified.v3_planMeta
  [propext, Classical.choice, Quot.sound] native []
#cone_sorries Midfall.Generator.Certified.v3_planMeta
#print axioms Midfall.Generator.Certified.generator_certified
#print axioms Midfall.Generator.Certified.generator_correct_V3
#cone_sorries Midfall.Generator.Certified.generator_certified
#cone_report Midfall.Generator.Certified.generator_certified under []

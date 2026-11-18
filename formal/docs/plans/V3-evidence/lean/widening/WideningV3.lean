/-
  WideningV3 - PROPOSED WIDENING of the supported class of the generic theorem (D-P71:
  `lowering_correct (R) (product) (hR : R.ValidV3) : LoweringEquivalenceV3 R product`) so that it
  covers renders in ACCUMULATOR MODE with an EXTERNAL, PINNED quotient evaluator - the class the
  IVC decider verifier is in. Every statement is for EVERY render `R`; no fixture occurs.
  (The file keeps its first name; it began as the design of a second fixture.)

  SPECIFICATION, NOT LANDED CODE. Typechecked against the built tree. RECON.1b REBASE: this file now
  imports the LANDED single text `Midfall/LoweringV3/Statements.lean` and no longer the
  eighteen-clause draft of `StatementsV3.lean`, which stays in the evidence directory as the D-P67
  fallback. `ValidCore` is no longer a copy of a second validity text: it is the six non-scope
  clauses OF THE SINGLE TEXT, and `validV3_iff_core` ties it back to `ValidV3` in both directions.
  `SupportedV3` is gone from the tree (RECON.1 step 4), so the scope vocabulary here is the frozen
  `SupportedV2` that the single text's `supported` clause carries. Nothing here is imported by the
  build. Design memo: ../../statements.md.

  Sections
    §A  scope            SupportedCore, AccShape, ExternalPinned, SupportedW
    §B  reference        accFinalCheck, LeanAcceptsAcc, RustAcceptsBoth, AlphaCollision
    §C  evaluator        EvalObject, EvalEntry, evalModel, QPinned, EvaluatorTrust
    §D  world            WorldW, callsW
    §E  headline         LoweringEquivalenceW and its four obligations; composition PROVED;
                         the no-accumulator / embedded instance IS the V3 text (PROVED)
    §F  tests            HypothesesInhabitedW, AccNontrivial, PairingInputsAgree
    §G  validity         ValidCore, ValidW; PROVED: `ValidW` leaves the evaluator's body free
                         (`ValidW.emptyBody`), and an empty body answers with no return data
                         (`evalModel_emptyBody`). THE TARGET `lowering_correctW` and
                         `lowering_correct_of_W` are in `WideningStages.lean` §7: the target must
                         carry the evaluator's contract (`EvalContracts`), which is defined there.

  Every `sorry` below is a STATED OBLIGATION (listed in the memo §10); every definition and every
  theorem statement elaborates.
-/
import Midfall.LoweringV3.Statements
import Midfall.Lowering.Accumulator

namespace Midfall.LoweringW

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §A. Scope -/

/-- The ten clauses of `SupportedV2` (`Midfall/LoweringV2/Statements.lean:202`) — the scope clause
    the single `ValidV3` carries — that do NOT mention the accumulator or the quotient mode.
    Verbatim; shared by F1 and F2. RECON.1 step 4 deleted `SupportedV3`/`WellFormedV3` from the
    staging module, so `wf` is the frozen `WellFormed` here too: the repaired permutation clause
    lives in `programOk` as `permCommMatchRepaired`, i.e. inside `ValidCore.program`. -/
structure SupportedCore (R : Render p G₁ G₂ Gₜ) : Prop where
  advice : R.vk.cs.numAdviceColumns ≠ 0
  instShape : R.vk.cs.numInstanceColumns = 2 ∧ R.cfg.numCommittedInstances = 1
  noRotInst : ∀ q ∈ R.vk.cs.instanceQueries.toList, q.2.int = 0
  singlePhase : R.vk.cs.numChallenges = 0
  hLimbs : R.vk.domain.getQuotientPolyDegree = R.vk.csDegree - 1
  vkPoints : ∀ C ∈ R.vk.fixedCommitments.toList ++ R.vk.permutation.commitments.toList,
    LoweringV2.ptReadable (R.E.g1.toEip C)
  layout : R.plan.memory.map.WellFormed ∧ R.plan.memory.validate.isOk = true
  production : R.flags.trace = false ∧ R.flags.gasCheckpoints = false
  wf : R.vk.WellFormed Features.solidity
  separateVk : R.flags.separate = true

/-- `SupportedV2` is the core plus its two first-headline restrictions. PROVED. -/
theorem supportedV2_iff_core (R : Render p G₁ G₂ Gₜ) :
    SupportedV2 R ↔ SupportedCore R ∧ R.cfg.accumulator = none ∧
      (R.flags.externalQuotient = false ∧ R.flags.expectedQuotient = none) :=
  ⟨fun h => ⟨⟨h.advice, h.instShape, h.noRotInst, h.singlePhase, h.hLimbs, h.vkPoints, h.layout,
      h.production, h.wf, h.separateVk⟩, h.noAcc, h.embeddedQuotient⟩,
   fun ⟨c, ha, hq⟩ => ⟨c.advice, c.instShape, c.noRotInst, c.singlePhase, c.hLimbs, c.vkPoints,
      c.layout, c.production, c.wf, ha, hq, c.separateVk⟩⟩

/-- **THE ACCUMULATOR SHAPES COVERED**: every encoding the generator accepts whose fixed-base
    tail is EMPTY. Each clause is a computation on the render.

    * The generator accepts ONE limb shape, 7 limbs of 56 bits (`api.rs:147-148`,
      `AccumulatorEncoding.limbShapeOk`), so the limb shape is not a restriction of this class:
      `noTail` implies it (`fixedScalarCount` is `none` on any other shape).
    * `noTail` - the accumulator fills the instance array to its end. Both kinds are admitted:
      point-and-scalar (12 words; the IVC decider, `offset + 12 = 16`) and point-pair (10 words).
      EXCLUDED: a point-and-scalar encoding followed by fixed-base scalars. That arm needs the
      fixed-base table as a function of the render, and the only table in the tree,
      `Midfall.Halo2.fixedBases`, has the identity for `-G` (R-52).
    * `noFixed` - the model agrees: no fixed-base tail entry is rendered. -/
structure AccShape (R : Render p G₁ G₂ Gₜ) (enc : Midfall.Generator.AccumulatorEncoding) :
    Prop where
  cfg : R.cfg.accumulator = some enc
  noTail : (Midfall.Lowering.toExec enc).fixedScalarCount R.cfg.numInstances = some 0
  noFixed : R.model.accFixedBases = []

/-- The external, PINNED evaluator profile (`RenderQuotient::ExternalPinned`). The pinned pair is
    an INPUT of the render: it is solc's output on the evaluator source and the Lean generator
    cannot compute it. An external evaluator WITHOUT a pin is not in the class (the contract then
    calls whatever code is at the address). -/
def ExternalPinned (R : Render p G₁ G₂ Gₜ) : Prop :=
  R.flags.externalQuotient = true ∧ ∃ len hash, R.flags.expectedQuotient = some (len, hash)

/-- **THE WIDENED SUPPORTED CLASS.** `SupportedV2` — the single text's `supported` clause — with
    `noAcc` replaced by `acc` and `embeddedQuotient` replaced by `quotient`. Four corners; V3's class is (none, embedded) and
    the IVC decider verifier is (collapsed, external pinned).

    `accKind` is the RECOMMENDED first cut (decision W-2 of the memo): only the point-and-scalar
    kind has a circuit, an artifact and an end-to-end test in the repository, so only it can
    meet rule W12. Striking the clause admits the point-pair kind at no cost to any statement
    below (`decodeAcc` and `accFinalCheck` already treat both). -/
structure SupportedW (R : Render p G₁ G₂ Gₜ) : Prop where
  core : SupportedCore R
  acc : R.cfg.accumulator = none ∨ ∃ enc, AccShape R enc
  accKind : ∀ enc, R.cfg.accumulator = some enc →
    enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar
  quotient : (R.flags.externalQuotient = false ∧ R.flags.expectedQuotient = none) ∨
    ExternalPinned R

/-- V3's class is inside the widened one. PROVED. -/
theorem SupportedW.ofV3 {R : Render p G₁ G₂ Gₜ} (h : SupportedV2 R) : SupportedW R :=
  let ⟨c, ha, hq⟩ := (supportedV2_iff_core R).mp h
  ⟨c, Or.inl ha, fun enc he => (by rw [ha] at he; cases he), Or.inl hq⟩

/-- And it is exactly the corner (none, embedded). PROVED. -/
theorem supportedV2_iff_W (R : Render p G₁ G₂ Gₜ) :
    SupportedV2 R ↔ SupportedW R ∧ R.cfg.accumulator = none ∧
      (R.flags.externalQuotient = false ∧ R.flags.expectedQuotient = none) :=
  ⟨fun h => ⟨SupportedW.ofV3 h, h.noAcc, h.embeddedQuotient⟩,
   fun ⟨hW, ha, hq⟩ => (supportedV2_iff_core R).mpr ⟨hW.core, ha, hq⟩⟩

/-- FALSIFIER of "the IVC class is already supported": a render in accumulator mode is outside
    the single text's scope clause `SupportedV2`. PROVED. -/
theorem acc_not_supportedV2 (R : Render p G₁ G₂ Gₜ)
    (enc : Midfall.Generator.AccumulatorEncoding) (h : R.cfg.accumulator = some enc) :
    ¬ SupportedV2 R := by
  intro h3
  rw [h3.noAcc] at h
  cases h

/-! ## §B. The reference in accumulator mode -/

/-- The fixed-base table of the covered shapes: empty (`AccShape.noTail`). -/
def accTable : Array (AccFixedBase G₁) := #[]

/-- The (name, base) view `KzgAcc.eval` wants; empty as well. -/
def accBases : Array (String × G₁) := #[]

/-- The verifying-key digest word the contract hashes into `alpha` (`mload(VK_DIGEST_MPTR)`,
    sol:2521), as the LEAN key's own digest. `EnvAgrees.vkDigestWord` ties the payload word to it. -/
def vkDigestWordOf (R : Render p G₁ G₂ Gₜ) : Word256 := frWord R.vk.transcriptRepr

/-- **THE CONTRACT'S FINAL CHECK**, on the KZG pair the PLONK part prepared and the RAW instance
    words. No accumulator: the plain pairing check. Accumulator: decode the two carried points
    from the words, scale each by its carried scalar, batch with the keccak `alpha`, ONE pairing
    check. A decode failure is a rejection. -/
def accFinalCheck (R : Render p G₁ G₂ Gₜ) (H : Hash) (instW : Array Word256)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) : Bool :=
  match R.cfg.accumulator with
  | none => DualMSM.check d R.params
  | some enc =>
    match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
        accTable instW with
    | none => false
    | some a =>
      batchedCheck R.params
        (alphaOf (p := p) H (vkDigestWordOf R) R.E.g1 d.left.eval d.right.eval
          (a.fullyCollapse accBases).1 (a.fullyCollapse accBases).2)
        d a accBases

/-- **THE LEAN REFERENCE OF THE CONTRACT'S OWN CHECK.** The calldata decodes at the render's
    layout, every instance word is canonical, the Rust-faithful `prepare` succeeds, and the
    contract's final check passes on the prepared pair and the raw words. -/
def LeanAcceptsAcc (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW inst,
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
    LoweringV2.instOfWords? (p := p) instW = some inst ∧
    ∃ d, prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms = .ok d ∧
      accFinalCheck R H instW d = true

/-- `verifyMsgs` is `prepareMsgs` followed by the pairing check. PROVED. -/
theorem verifyMsgs_ok_iff (R : Render p G₁ G₂ Gₜ) (H : Hash) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    verifyMsgs (Gₜ := Gₜ) R.E H Features.solidity R.params R.vk inst ms = .ok () ↔
      ∃ d, prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms = .ok d ∧
        DualMSM.check d R.params = true := by
  unfold verifyMsgs
  cases hp : prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms with
  | error e => simp [bind, Except.bind]
  | ok d =>
      by_cases hc : DualMSM.check d R.params = true
      · simp [bind, Except.bind, hc, pure, Except.pure]
      · simp [bind, Except.bind, hc, throw, throwThe, MonadExceptOf.throw]

/-- **V3 IS THE INSTANCE `accumulator = none`**: there the reference is the frozen `LeanAccepts`.
    PROVED. -/
theorem leanAcceptsAcc_iff_noAcc (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (H : Hash) (cd : Bytes) : LeanAcceptsAcc R H cd ↔ LeanAccepts R H cd := by
  unfold LeanAcceptsAcc LeanAccepts
  constructor
  · rintro ⟨ms, instW, inst, hdec, hinst, d, hd, hchk⟩
    refine ⟨ms, instW, inst, hdec, hinst, (verifyMsgs_ok_iff R H inst ms).mpr ⟨d, hd, ?_⟩⟩
    simpa [accFinalCheck, hacc] using hchk
  · rintro ⟨ms, instW, inst, hdec, hinst, hv⟩
    obtain ⟨d, hd, hchk⟩ := (verifyMsgs_ok_iff R H inst ms).mp hv
    exact ⟨ms, instW, inst, hdec, hinst, d, hd, by simpa [accFinalCheck, hacc] using hchk⟩

/-- `SoundSide` is implied by acceptance, as in V3 (`soundSide_of_leanAccepts`). PROVED. -/
theorem soundSide_of_leanAcceptsAcc (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : LeanAcceptsAcc R H cd) : SoundSide R H cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, d, hd, _⟩ := h
  intro ms' instW' inst' hdec' hinst' hpanic
  rw [hdec] at hdec'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hdec')
  rw [hinst] at hinst'
  obtain rfl := Option.some.inj hinst'
  rw [hpanic] at hd
  cases hd

/-- **WHAT THE RUST SIDE OF THE E2E TEST CHECKS** (`ivc_keccak_solidity.rs:1021-1024`, `:1085-1092`):
    two SEPARATE facts. (1) the Rust PLONK verifier accepts the decider proof (`verifyMsgs`, which
    runs its own pairing check); (2) the carried accumulator, read back from the instance words,
    satisfies ITS OWN pairing invariant (`Accumulator::check`).

    Not one Rust function: `IvcVerifier::verify_final` is NOT called by the test and is a third,
    different check (it folds with a Poseidon-derived `r`; see the memo §3). Stated under ONE
    `R.params` for both checks: the test uses two SRS files (k = 19 for the accumulator, k = 20
    for the proof), which agree on `[τ]₂` only because they are truncations of one ceremony. -/
def RustAcceptsBoth (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW inst enc a,
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
    LoweringV2.instOfWords? (p := p) instW = some inst ∧
    verifyMsgs (Gₜ := Gₜ) R.E H Features.solidity R.params R.vk inst ms = .ok () ∧
    R.cfg.accumulator = some enc ∧
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
      accTable instW = some a ∧
    KzgAcc.check a R.params accBases = true

/-- The lockstep lengths `batched_complete` / `batched_atMostOneRoot` need from the prepared pair.
    An owed lemma about `prepareMsgs` (v1 took it as a hypothesis too, `Accumulator.lean:1511`). -/
def PrepWf (R : Render p G₁ G₂ Gₜ) (H : Hash) : Prop :=
  ∀ (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (d : DualMSM (Fr p) G₁ G₂ Gₜ),
    prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms = .ok d →
    d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size

/-- **THE EXACT DIRECTION.** Rust PLONK accept, plus the accumulator's own pairing check, implies
    the contract reference accepts - for EVERY hash, so in particular whatever `alpha` is.
    PROVED from v1's `batched_complete` (bilinearity). -/
theorem leanAcceptsAcc_of_rust (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (hWf : PrepWf R H) (h : RustAcceptsBoth R H cd) : LeanAcceptsAcc R H cd := by
  obtain ⟨ms, instW, inst, enc, a, hdec, hinst, hv, henc, ha, hchk⟩ := h
  obtain ⟨d, hd, hdchk⟩ := (verifyMsgs_ok_iff R H inst ms).mp hv
  refine ⟨ms, instW, inst, hdec, hinst, d, hd, ?_⟩
  unfold accFinalCheck
  simp only [henc, ha]
  apply Midfall.Lowering.batched_complete
  · exact hWf inst ms d hd
  · exact hdchk
  · exact hchk

/-- **THE EVENT THE CONVERSE EXCLUDES.** The contract reference accepts although one of the two
    equations fails: the keccak-derived `alpha` is a root of the batched equation at four points
    for which the batched equation is not identically satisfied. -/
def AlphaCollision (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW inst enc a d,
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
    LoweringV2.instOfWords? (p := p) instW = some inst ∧
    prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms = .ok d ∧
    R.cfg.accumulator = some enc ∧
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
      accTable instW = some a ∧
    (DualMSM.check d R.params = false ∨ KzgAcc.check a R.params accBases = false) ∧
    batchedCheck R.params
      (alphaOf (p := p) H (vkDigestWordOf R) R.E.g1 d.left.eval d.right.eval
        (a.fullyCollapse accBases).1 (a.fullyCollapse accBases).2) d a accBases = true

/-- **THE CONVERSE, AS FAR AS IT GOES.** In accumulator mode: the contract reference accepts only
    if Rust accepts both, or `alpha` collided. PROVED (a case split; the content is the next
    theorem). NOT an iff with `RustAcceptsBoth`. -/
theorem rust_or_collision_of_leanAcceptsAcc (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (enc : Midfall.Generator.AccumulatorEncoding) (henc : R.cfg.accumulator = some enc)
    (h : LeanAcceptsAcc R H cd) : RustAcceptsBoth R H cd ∨ AlphaCollision R H cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, d, hd, hchk⟩ := h
  unfold accFinalCheck at hchk
  simp only [henc] at hchk
  cases ha : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
      accTable instW with
  | none => simp [ha] at hchk
  | some a =>
      simp only [ha] at hchk
      by_cases h1 : DualMSM.check d R.params = true
      · by_cases h2 : KzgAcc.check a R.params accBases = true
        · exact Or.inl ⟨ms, instW, inst, enc, a, hdec, hinst,
            (verifyMsgs_ok_iff R H inst ms).mpr ⟨d, hd, h1⟩, henc, ha, h2⟩
        · exact Or.inr ⟨ms, instW, inst, enc, a, d, hdec, hinst, hd, henc, ha,
            Or.inr (by simpa using h2), hchk⟩
      · exact Or.inr ⟨ms, instW, inst, enc, a, d, hdec, hinst, hd, henc, ha,
          Or.inl (by simpa using h1), hchk⟩

/-- **AT MOST ONE BAD `alpha`.** For a fixed prepared pair and a fixed accumulator, if one of the
    two equations fails, the batched check passes for at most one scalar. This is the
    Schwartz-Zippel-style statement the contract's soundness in accumulator mode rests on; it is
    a statement about ALL scalars, not about the hash. PROVED: it is v1's `batched_atMostOneRoot`
    at the empty table. -/
theorem alpha_atMostOne (R : Render p G₁ G₂ Gₜ) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hbad : DualMSM.check d R.params = false ∨ KzgAcc.check a R.params accBases = false)
    (α β : Fr p) (hα : batchedCheck R.params α d a accBases = true)
    (hβ : batchedCheck R.params β d a accBases = true) : α = β :=
  Midfall.Lowering.batched_atMostOneRoot R.params d a accBases hWf hbad α β hα hβ

/-! ## §C. The evaluator call -/

/-- **THE OBJECT OF THE CLAIM FOR THE EVALUATOR**: the assembly block of the fallback of
    `Halo2QuotientEvaluator.sol` as the Lean generator emits it, constants inlined. `outMptr` is
    `QUOTIENT_OUTPUT_MPTR`, the lowest address the generated layout writes.

    SUPPLIED BY THE OBJECT PASS. The frozen `Render` has no evaluator program; until
    `evalBodyOf : PlanView → Model → YulBlock` exists and is tied to the printed text the way
    `CodegenAgrees` ties `asmOf`, this is a parameter checked by `ValidF2`. -/
structure EvalObject where
  body : YulBlock
  outMptr : Nat

/-- **TRUSTED: the state in which the evaluator's fallback body starts**, for a STATICCALL that
    solc's dispatcher routed to `fallback()`. The frame is `Evaluator.calleeState` (the callee's
    own account view, `static`, zero call value, the request's input as calldata, the caller's
    hash oracle) EXCEPT memory: solc's prologue has written the free-memory pointer, so memory is
    some `mem₀` that is zero from `0x80` and whose free-memory pointer does not exceed the
    generated layout. Measured on the tracked artifact: the runtime opens with
    `PUSH2 0x08c0 PUSH1 0x40 MSTORE`, and `QUOTIENT_OUTPUT_MPTR = 0x1000`. The evaluator has NO
    on-chain guard for this bound (the verifier has MF-2; the evaluator fallback does not). -/
structure EvalEntry (Q : EvalObject) (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256)
    (st : EvmState) (req : YulSemantics.EVM.CallRequest) (stC : EvmState) : Prop where
  shape : ∃ (mem₀ : Nat → UInt8) (aw : U256),
    stC = { Evaluator.calleeState W Lyt qAddr st req with memory := mem₀, activeWords := aw }
  zeroAbove : LoweringV2.ZeroAbove stC.memory
  fmp : (loadWord stC.memory 0x40).toNat ≤ Q.outMptr

/-- **THE MODELLED ANSWER OF THE EVALUATOR**: some run of the generated body, in the CLOSED
    dialect, from some entry frame; the response is the frame-boundary view of that run, with the
    caller's world unchanged (`Evaluator.responseOf`). -/
def evalModel (Q : EvalObject) (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256) :
    YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop :=
  fun req st resp => ∃ stC V' st' o,
    EvalEntry Q W Lyt qAddr st req stC ∧
    YulSemantics.Run EVM.evm Q.body stC V' st' o ∧
    resp = Evaluator.responseOf st (committedState stC st')

/-- The modelled answer never reports a world change. PROVED (replaces the false world-locality
    lemma for the one property the composition needs: an honest response is a permissive one). -/
theorem evalModel_quiet (Q : EvalObject) (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256)
    (req : YulSemantics.EVM.CallRequest) (st : EvmState) (resp : CallResponse)
    (h : evalModel Q W Lyt qAddr req st resp) : resp.world = CallWorld.ofState st := by
  obtain ⟨stC, V', st', o, _, _, rfl⟩ := h
  unfold Evaluator.responseOf
  split <;> rfl

/-- v1's slot (`Evaluator.rel`, all-zero entry memory) is contained in the model. PROVED: the
    model is inhabited wherever v1's relation is. -/
theorem evalModel_of_rel (Q : EvalObject) (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256)
    (req : YulSemantics.EVM.CallRequest) (st : EvmState) (resp : CallResponse)
    (h : Evaluator.rel W Lyt qAddr Q.body req st resp) : evalModel Q W Lyt qAddr req st resp := by
  obtain ⟨V', st', o, hrun, rfl⟩ := h
  refine ⟨Evaluator.calleeState W Lyt qAddr st req, V', st', o, ⟨⟨_, _, rfl⟩, ?_, ?_⟩, hrun, rfl⟩
  · exact fun a _ => rfl
  · have h0 : (loadWord (Evaluator.calleeState W Lyt qAddr st req).memory 0x40).toNat = 0 := by
      show (loadWord (fun _ : Nat => (0 : UInt8)) 0x40).toNat = 0
      decide
    rw [h0]; exact Nat.zero_le _

/-- **THE PIN, AS THE CONTRACT TESTS IT** (sol:1808-1811): the code at `qAddr` has the pinned
    length and the pinned code hash, both compared as words, in the CURRENT state. The guard
    establishes exactly this immediately before the call, so no deployment fact is needed to
    discharge it on the soundness side. -/
def QPinnedEnv (R : Render p G₁ G₂ Gₜ) (env : ExecEnv) (qAddr : U256) : Prop :=
  ∃ len hash, R.flags.expectedQuotient = some (len, hash) ∧
    BitVec.ofNat 256 (env.extCodeOf qAddr).length = BitVec.ofNat 256 len ∧
    projectedCodeHash env env.balanceOf qAddr = hash

def QPinned (R : Render p G₁ G₂ Gₜ) (st : EvmState) (qAddr : U256) : Prop :=
  QPinnedEnv R st.env qAddr

/-- **TRUSTED: solc, for the evaluator.** The analogue of `EntryFrame` for the second contract.
    `evalRel` is what the chain answers to a call at the evaluator address. The assumption:

    * `spec`  - whenever the code at `qAddr` passes the verifier's pin, the chain's answers to a
                STATICCALL there are exactly the modelled ones: runs of the generated fallback
                body from an evaluator entry frame. This is "solc compiles the generated source
                to the runtime with the pinned hash, that runtime implements the Yul body, and no
                other code has that hash", in one clause. It says nothing when the pin fails.
    * `quiet` - a call at the evaluator address never reports a world change (it is a STATICCALL).

    NOT validated against any compiler output inside Lean. What IS checked outside Lean: the
    pinned pair is solc 0.8.30's output on the tracked source (measured, memo §5.4). -/
structure EvaluatorTrust (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (W : ExecEnv)
    (Lyt : EVM.Layout) (qAddr : U256)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) : Prop where
  spec : ∀ req st resp, req.kind = YulSemantics.EVM.CallKind.staticcall → QPinned R st qAddr →
    (evalRel req st resp ↔ evalModel Q W Lyt qAddr req st resp)
  quiet : ∀ req st resp, evalRel req st resp → resp.world = CallWorld.ofState st

/-- WITNESS: the trust assumption is satisfiable, by the model itself. PROVED. -/
theorem evaluatorTrust_model (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (W : ExecEnv)
    (Lyt : EVM.Layout) (qAddr : U256) :
    EvaluatorTrust R Q W Lyt qAddr (evalModel Q W Lyt qAddr) :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun req st resp h => evalModel_quiet Q W Lyt qAddr req st resp h⟩

/-- FALSIFIER of dropping `quiet`: a relation that agrees with the model on pinned states and
    reports another world elsewhere satisfies `spec` and is NOT below `permissive`. Stated as
    the property `quiet` buys; PROVED. -/
theorem evaluatorTrust_le_permissive (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (W : ExecEnv)
    (Lyt : EVM.Layout) (qAddr : U256)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop)
    (product : PairingProduct) (ht : EvaluatorTrust R Q W Lyt qAddr evalRel) :
    ∀ req st r, (honestCalls product qAddr evalRel).Call req st r →
      (permissive (honestCalls product qAddr evalRel)).Call req st r := by
  refine honest_le_permissive (honestCalls product qAddr evalRel) ?_
  intro req st r h
  rcases h with h | ⟨_, hE⟩
  · simp only [honestOf, Option.map_eq_some_iff] at h
    obtain ⟨rel, _, hr⟩ := h
    rw [← hr]
    split <;> rfl
  · exact ht.quiet req st r hE

/-- The modelled answer does not read the forwarded gas word (`gas()` at
    `QuotientAndLinearization.yul:35` is the program's only use of the oracle). PROVED. With
    `Externals.lean:799` (the precompile relations do not test `gas` either) this is what the
    gas-insensitivity lemma of the totality proof rests on. -/
theorem evalModel_gas_irrel (Q : EvalObject) (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256)
    (req : YulSemantics.EVM.CallRequest) (gas' : U256) (st : EvmState) (resp : CallResponse) :
    evalModel Q W Lyt qAddr req st resp ↔
      evalModel Q W Lyt qAddr { req with gas := gas' } st resp := by
  have hc : Evaluator.calleeState W Lyt qAddr st { req with gas := gas' } =
      Evaluator.calleeState W Lyt qAddr st req := rfl
  constructor
  · rintro ⟨stC, V', st', o, ⟨hs, hz, hf⟩, hrun, hresp⟩
    exact ⟨stC, V', st', o, ⟨by rw [hc]; exact hs, hz, hf⟩, hrun, hresp⟩
  · rintro ⟨stC, V', st', o, ⟨hs, hz, hf⟩, hrun, hresp⟩
    exact ⟨stC, V', st', o, ⟨by rw [hc] at hs; exact hs, hz, hf⟩, hrun, hresp⟩

/-! ## §D. The world a render runs in -/

/-- Does this render call an evaluator? Read off the MODEL, because that is what decides whether
    the program binds `quotientEvaluator` (`Program.lean:107`). -/
def isExternal (R : Render p G₁ G₂ Gₜ) : Prop := R.model.quotientExternal.isSome = true

instance (R : Render p G₁ G₂ Gₜ) : Decidable (isExternal R) := by
  unfold isExternal; infer_instance

/-- The honest relation of a render in either mode: the four precompiles, and - only when the
    render calls one - the evaluator slot at `qAddr`. -/
def callsW (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (qAddr : U256)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) : ExternalCalls :=
  if isExternal R then honestCalls product qAddr evalRel else callsOf product

theorem callsW_embedded (R : Render p G₁ G₂ Gₜ) (hq : R.model.quotientExternal = none)
    (product : PairingProduct) (qAddr : U256)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) :
    callsW R product qAddr evalRel = callsOf product := by
  simp [callsW, isExternal, hq]

/-- **THE HYPOTHESES OF THE WIDENED HEADLINE**, bundled. The first four are V3's, verbatim. The
    last two are vacuous for a render with an embedded quotient and no accumulator.

    * `evaluator` - only for a render that calls one: the pinned code is deployed at `qAddr`,
      `qAddr` is not a precompile address, and the chain answers there as `EvaluatorTrust` says.
    * `idLaw` - only in accumulator mode: the codec decodes its own identity encoding. The
      accumulator decoder turns an identity-flagged point into 128 zero bytes and asks the codec
      for the group element (`decodeAcc`, `Exec/Accumulator.lean:1033`); the contract sends the
      same bytes through G1MSM, which accepts them. `G1CodecHeadlineLaws` has the decoder-first
      law only, so without `idLaw` a codec may reject the zero encoding, and the reference then
      rejects every identity-flagged accumulator the contract accepts. -/
structure WorldW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) : Prop where
  dep : DeploymentV2 R W H vkAddr
  entry : EntryFrameV3 R W Lyt H cd st₀
  pc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product
  codec : Midfall.LoweringV3.G1CodecHeadlineLaws R.E.g1
  evaluator : isExternal R → QPinnedEnv R W qAddr ∧
    accountKey qAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
    EvaluatorTrust R Q W Lyt qAddr evalRel
  idLaw : R.cfg.accumulator.isSome = true → R.E.g1.ofEip? (R.E.g1.toEip 1) = some 1

/-- An honest response is a permissive one, in either mode. PROVED. -/
theorem callsW_le_permissive (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (W : ExecEnv)
    (Lyt : EVM.Layout) (qAddr : U256)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop)
    (product : PairingProduct) (ht : isExternal R → EvaluatorTrust R Q W Lyt qAddr evalRel) :
    ∀ req st r, (callsW R product qAddr evalRel).Call req st r →
      (permissive (callsW R product qAddr evalRel)).Call req st r := by
  by_cases he : isExternal R
  · have hc : callsW R product qAddr evalRel = honestCalls product qAddr evalRel := by
      simp [callsW, he]
    rw [hc]
    exact evaluatorTrust_le_permissive R Q W Lyt qAddr evalRel product (ht he)
  · have hc : callsW R product qAddr evalRel = callsOf product := by simp [callsW, he]
    rw [hc]
    exact callsOf_le_permissive product

/-! ## §E. The headline, for every render -/

/-- TWO OUTCOMES, for EVERY evaluator address (V3's `TwoOutcomes` fixes it to 0). -/
def TwoOutcomesW (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∀ (vkAddr qAddr : U256) (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (obs : Obs),
    RunBody R vkAddr qAddr c g st₀ obs →
    obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)

/-- `TwoOutcomesW` from the SAME two decidable scans as V3, by the same two obligations
    (`twoOutcomes_of_exitDiscipline`, `scans_prog_addr_indep`, both already stated for every
    `qAddr`). PROVED from them: no evaluator fact and no accumulator fact enters conjunct 3,
    whatever the evaluator answers. -/
theorem twoOutcomesW_of_scans (R : Render p G₁ G₂ Gₜ)
    (hw : NoWriters (R.prog 0 0)) (hx : Midfall.LoweringV3.ExitDiscipline (R.prog 0 0)) :
    TwoOutcomesW R := by
  intro vkAddr qAddr c g st₀ obs hobs
  obtain ⟨V', hrun⟩ := hobs
  obtain ⟨hw', hx'⟩ := scans_prog_addr_indep R vkAddr qAddr hw hx
  exact twoOutcomes_of_exitDiscipline (R.prog vkAddr qAddr) hw' hx' c g st₀ V' obs.state
    obs.outcome hrun

theorem TwoOutcomesW.toV3 {R : Render p G₁ G₂ Gₜ} (h : TwoOutcomesW R) : TwoOutcomes R :=
  fun vkAddr c g st₀ obs hobs => h vkAddr 0 c g st₀ obs hobs

/-- **LOWERING EQUIVALENCE, WIDENED.** V3's text (`Midfall/LoweringV3/Statements.lean:1378`) with four substitutions:
    the evaluator address is a variable `qAddr`; `callsW` for `callsOf`; `LeanAcceptsAcc` for
    `LeanAccepts`; `WorldW` for the four V3 hypotheses (it adds two that are vacuous at V3's
    class). `SoundSide`, `CompleteSide`, `EntryFrameV3`, `RunBody`, `GasTotal`, `returnView` are
    V3's, unchanged. Conjunct 2 keeps V3's zero gas oracle so that V3's class gives back the V3
    text; `CompleteAnyGasW` below is the stronger form a render that executes `gas()` deserves.

    1. soundness   - a run that returns returns ABI `true`, and `LeanAcceptsAcc` holds;
    2. completeness - if `LeanAcceptsAcc` holds, an honest run exists and every honest run returns
                     ABI `true`, world unchanged;
    3. two outcomes - every run returns ABI `true` or is a non-committing halt, world unchanged;
    4. totality    - under the honest relation and any total gas oracle, a run exists. -/
def LoweringEquivalenceW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) :
    Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel →
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr qAddr (permissive (callsW R product qAddr evalRel)) g st₀ obs →
        obs.isReturn → SoundSide R H cd → obs.returnData = abiTrue ∧ LeanAcceptsAcc R H cd) ∧
    (LeanAcceptsAcc R H cd → CompleteSide R H cd →
        (∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel)
            (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel)
            (ExternalGas.ofFun fun _ => 0) st₀ obs → obs.view = returnView st₀) ∧
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr qAddr (permissive (callsW R product qAddr evalRel)) g st₀ obs →
        obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)) ∧
    (∀ g : ExternalGas, Midfall.LoweringV3.GasTotal g →
        ∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel) g st₀ obs)

/-- PROGRAM-LEVEL REJECTION, widened (`RejectsV3`). -/
def RejectsW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop)
    (g : ExternalGas) (obs : Obs),
    WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel →
    SoundSide R H cd → ¬ LeanAcceptsAcc R H cd →
    RunBody R vkAddr qAddr (permissive (callsW R product qAddr evalRel)) g st₀ obs → ¬ obs.isReturn

/-- Conjunct 2, named (`CompleteV3`). -/
def CompleteW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel →
    LeanAcceptsAcc R H cd → CompleteSide R H cd →
      (∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel)
          (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
      ∀ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel)
          (ExternalGas.ofFun fun _ => 0) st₀ obs → obs.view = returnView st₀

/-- Conjunct 4, named (`TotalV3`). -/
def TotalW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel →
    ∀ g : ExternalGas, Midfall.LoweringV3.GasTotal g →
      ∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel) g st₀ obs

/-- OPTIONAL STRENGTHENING of conjunct 2 (decision W-5): completeness under EVERY total gas
    oracle. At V3's class it follows from conjunct 2 and "the program executes no `gas()`"; at
    an external render the program executes `gas()` once, and the zero oracle of conjunct 2
    means "the model forwards a gas word of 0 and the evaluator slot ignores it". -/
def CompleteAnyGasW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel →
    LeanAcceptsAcc R H cd → CompleteSide R H cd → ∀ g : ExternalGas, Midfall.LoweringV3.GasTotal g →
      (∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel) g st₀ obs) ∧
      ∀ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel) g st₀ obs →
        obs.view = returnView st₀

theorem CompleteAnyGasW.toComplete {R : Render p G₁ G₂ Gₜ} {Q : EvalObject}
    {product : PairingProduct} (h : CompleteAnyGasW R Q product) : CompleteW R Q product :=
  fun W Lyt H vkAddr qAddr cd st₀ evalRel hw hacc hside =>
    h W Lyt H vkAddr qAddr cd st₀ evalRel hw hacc hside _ (gasTotal_ofFun _)

/-- **COMPOSITION, widened.** The headline is four independent obligations. PROVED, no `sorry`:
    the proof is `lowering_equivalenceV3_of`'s, word for word. -/
theorem lowering_equivalenceW_of (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (h2 : TwoOutcomesW R) (hrej : RejectsW R Q product)
    (hcomp : CompleteW R Q product) (htot : TotalW R Q product) :
    LoweringEquivalenceW R Q product := by
  intro W Lyt H vkAddr qAddr cd st₀ evalRel hw
  refine ⟨?_, hcomp W Lyt H vkAddr qAddr cd st₀ evalRel hw,
    fun g obs hobs => h2 vkAddr qAddr _ g st₀ obs hobs,
    htot W Lyt H vkAddr qAddr cd st₀ evalRel hw⟩
  intro g obs hobs hret hside
  constructor
  · rcases h2 vkAddr qAddr _ g st₀ obs hobs with hview | ⟨hrh, _⟩
    · have hh : obs.state.halted = some (.ret, abiTrue) := congrArg ObsView.halted hview
      simp only [Obs.returnData, hh]
    · exact absurd hrh (not_isRevertOrHalt_of_isReturn hret)
  · by_contra hna
    exact hrej W Lyt H vkAddr qAddr cd st₀ evalRel g obs hw hside hna hobs hret

/-- An embedded-quotient program does not mention the evaluator address. PROVED by unfolding
    `asmOf` (`Program.lean:114`). -/
theorem prog_qAddr_irrel (R : Render p G₁ G₂ Gₜ) (hq : R.model.quotientExternal = none)
    (vkAddr qAddr : U256) : R.prog vkAddr qAddr = R.prog vkAddr 0 := by
  simp [Render.prog, asmOf, wrapperLocals, hq]

theorem runBody_qAddr_irrel (R : Render p G₁ G₂ Gₜ) (hq : R.model.quotientExternal = none)
    (vkAddr qAddr : U256) (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (obs : Obs) :
    RunBody R vkAddr qAddr c g st₀ obs = RunBody R vkAddr 0 c g st₀ obs := by
  unfold RunBody
  rw [prog_qAddr_irrel R hq]

/-- **THE NO-ACCUMULATOR, EMBEDDED INSTANCE IS THE V3 TEXT.** For such a render,
    `LoweringEquivalenceW` and `LoweringEquivalenceV3` are equivalent. PROVED: the two extra
    hypotheses are vacuous, the evaluator address does not occur in the program, `callsW` is
    `callsOf`, and `LeanAcceptsAcc` is `LeanAccepts`. -/
theorem equivalenceW_iff_V3 (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct)
    (hacc : R.cfg.accumulator = none) (hq : R.model.quotientExternal = none) :
    LoweringEquivalenceW R Q product ↔ LoweringEquivalenceV3 R product := by
  have hext : ¬ isExternal R := by simp [isExternal, hq]
  constructor
  · intro hG W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec
    have h := hG W Lyt H vkAddr 0 cd st₀ (fun _ _ _ => False)
      ⟨hdep, hentry, hpc, hcodec, fun he => absurd he hext, fun ha => by simp [hacc] at ha⟩
    simp only [callsW_embedded R hq, leanAcceptsAcc_iff_noAcc R hacc] at h
    exact h
  · intro h3 W Lyt H vkAddr qAddr cd st₀ evalRel hw
    have h := h3 W Lyt H vkAddr cd st₀ hw.dep hw.entry hw.pc hw.codec
    simp only [callsW_embedded R hq, leanAcceptsAcc_iff_noAcc R hacc,
      runBody_qAddr_irrel R hq vkAddr qAddr]
    exact h

/-! ### What the headline says about Rust (corollaries; no new obligation) -/

/-- COROLLARY 1 (the exact direction). If Rust accepts the proof and the carried accumulator
    passes its own check, an honest run exists and every honest run returns `true`. PROVED from
    the headline and `leanAcceptsAcc_of_rust`. -/
theorem returns_of_rustAcceptsBoth (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hEq : LoweringEquivalenceW R Q product)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop)
    (hw : WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel) (hWf : PrepWf R H)
    (hrust : RustAcceptsBoth R H cd) (hside : CompleteSide R H cd) :
    (∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel)
        (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
      ∀ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel)
        (ExternalGas.ofFun fun _ => 0) st₀ obs → obs.view = returnView st₀ :=
  (hEq W Lyt H vkAddr qAddr cd st₀ evalRel hw).2.1 (leanAcceptsAcc_of_rust R H cd hWf hrust) hside

/-- COROLLARY 2 (soundness side, NOT an iff). In accumulator mode: if the contract returns, then
    Rust accepts both, or `alpha` collided. PROVED from the headline and
    `rust_or_collision_of_leanAcceptsAcc`. -/
theorem rust_or_collision_of_returns (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hEq : LoweringEquivalenceW R Q product)
    (enc : Midfall.Generator.AccumulatorEncoding) (henc : R.cfg.accumulator = some enc)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop)
    (hw : WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel)
    (g : ExternalGas) (obs : Obs)
    (hrun : RunBody R vkAddr qAddr (permissive (callsW R product qAddr evalRel)) g st₀ obs)
    (hret : obs.isReturn) (hside : SoundSide R H cd) :
    RustAcceptsBoth R H cd ∨ AlphaCollision R H cd :=
  rust_or_collision_of_leanAcceptsAcc R H cd enc henc
    ((hEq W Lyt H vkAddr qAddr cd st₀ evalRel hw).1 g obs hrun hret hside).2

/-! ## §F. Tests: what a circuit must exhibit (non-vacuity; NOT proof obligations of the theorem) -/

/-- The accepted accumulator is not the neutral one: both carried points are non-identity. The
    neutral accumulator (both flags set) passes its own check trivially and exercises none of
    the limb decoder; the e2e test asserts the same (`ivc_keccak_solidity.rs:1457-1461`). -/
def AccNontrivial (R : Render p G₁ G₂ Gₜ) (cd : Bytes) : Prop :=
  ∃ ms instW enc a,
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
    R.cfg.accumulator = some enc ∧
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
      accTable instW = some a ∧
    (a.fullyCollapse accBases).1 ≠ 1 ∧ (a.fullyCollapse accBases).2 ≠ 1

/-- **NON-VACUITY, widened** (`HypothesesInhabitedV3`). Every hypothesis of the headline holds at
    once, AT KECCAK, at a calldata the reference ACCEPTS. To be exhibited at one real circuit of
    each corner of the class that is claimed; needs the SRS trapdoor (memo §7). -/
def HypothesesInhabitedW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) :
    Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr qAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    WorldW R Q product W Lyt keccak256 vkAddr qAddr cd st₀ evalRel ∧
      LeanAcceptsAcc R keccak256 cd ∧ SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd

/-- What the gate buys, PROVED: headline plus gate give an honest run that returns ABI `true`. -/
theorem returns_of_inhabitedW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hEq : LoweringEquivalenceW R Q product)
    (hI : HypothesesInhabitedW R Q product) :
    ∃ (vkAddr qAddr : U256) (st₀ : EvmState)
      (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) (obs : Obs),
      RunBody R vkAddr qAddr (callsW R product qAddr evalRel) (ExternalGas.ofFun fun _ => 0) st₀
          obs ∧ obs.view = returnView st₀ := by
  obtain ⟨W, Lyt, vkAddr, qAddr, cd, st₀, evalRel, hw, hacc, _, hcomp⟩ := hI
  obtain ⟨_, h2, _, _⟩ := hEq W Lyt keccak256 vkAddr qAddr cd st₀ evalRel hw
  obtain ⟨⟨obs, hobs⟩, hall⟩ := h2 hacc hcomp
  exact ⟨vkAddr, qAddr, st₀, evalRel, obs, hobs, hall obs hobs⟩

/-- The two G1 inputs of the contract's one pairing call, as the reference computes them:
    `(kzg_lhs + α·acc_lhs, kzg_rhs + α·acc_rhs)`. -/
def batchedInputs (R : Render p G₁ G₂ Gₜ) (H : Hash) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : G₁ × G₁ :=
  let accL := (a.fullyCollapse accBases).1
  let accR := (a.fullyCollapse accBases).2
  let α := alphaOf (p := p) H (vkDigestWordOf R) R.E.g1 d.left.eval d.right.eval accL accR
  (d.left.eval * gsmul (p := p) α accL, d.right.eval * gsmul (p := p) α accR)

/-- **THE WEAK TEST, for an SRS whose trapdoor is unknown.** Instead of acceptance: the reference
    reaches the final check, and the two pairing inputs it computes are, byte for byte, the two
    G1 slots of the `0x0f` call the EVM made on the same calldata (`lhsBytes`, `rhsBytes`, exported
    by the test's precompile tracer). The pairing's verdict is then the EVM's, not Lean's. -/
def PairingInputsAgree (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (lhsBytes rhsBytes : Bytes) : Prop :=
  ∃ ms instW inst enc a d,
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
    LoweringV2.instOfWords? (p := p) instW = some inst ∧
    prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms = .ok d ∧
    R.cfg.accumulator = some enc ∧
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
      accTable instW = some a ∧
    R.E.g1.toEip (batchedInputs R H d a).1 = lhsBytes ∧
    R.E.g1.toEip (batchedInputs R H d a).2 = rhsBytes

/-! ## §G. Validity, and the target -/

/-- The `model` clause of the old eighteen-clause text is NOT a clause of the single text: it is
    inside `generated`. This is the projection that replaces it, PROVED by inverting the four binds
    of `generateAll`. Nothing was restated to make it go through: the equation is verbatim the one
    the old `model` clause carried. -/
theorem ok_bind_iff {α β γ : Type} (x : Except α β) (f : β → Except α γ) {η : γ} :
    (x >>= f) = .ok η ↔ ∃ y, x = .ok y ∧ f y = .ok η := by
  constructor
  · cases x with
    | error e => intro h; cases h
    | ok y => intro h; exact ⟨y, rfl, h⟩
  · rintro ⟨y, rfl, hy⟩; exact hy

theorem model_of_generated {R : Render p G₁ G₂ Gₜ} (h : Midfall.LoweringV3.GeneratedBy R) :
    generateVerifierFromPlan (fun _ _ => R.qblocks) R.inputs R.flags R.plan = .ok R.model := by
  obtain ⟨out, hg, hplan, hq, hm⟩ := h
  rw [Midfall.LoweringV3.generated] at hg
  simp only [generateAll, Bind.bind] at hg
  obtain ⟨rawMeta, _, h1⟩ := (ok_bind_iff _ _).mp hg
  obtain ⟨plan, _, h2⟩ := (ok_bind_iff _ _).mp h1
  obtain ⟨blocks, _, h3⟩ := (ok_bind_iff _ _).mp h2
  obtain ⟨model, hgen, h4⟩ := (ok_bind_iff _ _).mp h3
  cases h5 : model.validateLayout with
  | error e => simp only [h5] at h4; cases h4
  | ok u =>
    simp only [h5] at h4
    have hA : { plan := plan, qblocks := blocks, model := model } = out :=
      Except.ok.inj (show Except.ok { plan := plan, qblocks := blocks, model := model } =
        Except.ok out from h4)
    have hp : plan = R.plan := (congrArg GenOut.plan hA).trans hplan
    have hb : blocks = R.qblocks := (congrArg GenOut.qblocks hA).trans hq
    have hm' : model = R.model := (congrArg GenOut.model hA).trans hm
    subst hp; subst hb; subst hm'
    exact hgen

/-- **THE SIX NON-SCOPE CLAUSES OF THE SINGLE `ValidV3`.** Not a second text: every field type is a
    clause type of `Midfall.LoweringV3.ValidV3` (`Statements.lean:1116`) — `generated`, `inputs`,
    `program`, `noWriters`, `env`, `payload` — and `validV3_iff_core` below is the only way in or
    out. The widening replaces ONE clause of the single text, the scope clause `supported :
    SupportedV2 R`, by `SupportedW`; everything else is that text unchanged. The old copy of the
    eighteen-clause text that stood here is deleted (RECON.1b Do step 1): its `circuitMeta`,
    `layout`, `invariants` and `model` are now inside `generated` (projection
    `model_of_generated`), its `codegen`, `closed`, `noShadow`, `cdBound`, `transcriptMptr` are
    conjuncts of `programOk` (projections `cdBound_of_valid`, `transcriptMptr_of_valid`,
    `noShadow_of_programOk`), and its `vkPins` / `vkProgressPins` are NOT clauses of the single
    text at all — see the obligation recorded at `object/GeneratorCertified.lean` §5. -/
structure ValidCore (R : Render p G₁ G₂ Gₜ) : Prop where
  generated : Midfall.LoweringV3.GeneratedBy R
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  program : Midfall.LoweringV3.programOk R
  noWriters : NoWriters (R.prog 0 0)
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  payload : Midfall.LoweringV3.PayloadAgrees R

/-- `ValidV3` is the core plus the single text's scope clause. PROVED, both directions, by
    re-associating seven clauses. -/
theorem validV3_iff_core (R : Render p G₁ G₂ Gₜ) : ValidV3 R ↔ ValidCore R ∧ SupportedV2 R :=
  ⟨fun h => ⟨⟨h.generated, h.inputs, h.program, h.noWriters, h.env, h.payload⟩, h.supported⟩,
   fun ⟨c, s⟩ => ⟨c.generated, c.inputs, c.program, c.noWriters, c.env, c.payload, s⟩⟩

/-- The pins an external render adds; each is a lookup in the render's own constant table or a
    computation on the evaluator object. -/
structure EvalPins (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) : Prop where
  /-- The verifier's two pin constants are the render flags' pair, and the length is not zero
      (so `extcodehash` is the hash of the code, never the empty-account 0). -/
  pin : ∃ len hash, R.flags.expectedQuotient = some (len, hash) ∧
    R.consts.lookup "EXPECTED_QUOTIENT_LENGTH" = some len ∧
    R.consts.lookup "EXPECTED_QUOTIENT_CODEHASH_WORD" = some hash.toNat ∧
    0 < len ∧ len < 2 ^ 256
  /-- The evaluator's output window is the verifier's return window, and the frame the verifier
      sends is the frame the evaluator expects (one `QuotientExternal` record for both). -/
  frame : ∃ qe, R.model.quotientExternal = some qe ∧ Q.outMptr = R.pv.memory.quotientReturnMptr
  /-- The evaluator body is closed (no free name: otherwise it is stuck, and totality fails). -/
  evalClosed : (freeNames Q.body).isEmpty = true

/-- **VALIDITY, WIDENED.** `ValidV3` with `SupportedW` for the single text's `supported` clause, plus the evaluator pins
    for a render that calls one. Checked per circuit by computation, as `ValidV3` is (D-P71.3). -/
structure ValidW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) : Prop where
  core : ValidCore R
  supported : SupportedW R
  evaluator : isExternal R → EvalPins R Q

/-- OBLIGATION (generator fact; `Artifacts.lean:534-537`): the model externalises the quotient
    exactly when the flag says so. Needed to read the program's mode off the frozen scope
    clause, which is about the FLAG. W12: a KAT at one embedded and one external render. -/
theorem model_quotientMode (R : Render p G₁ G₂ Gₜ)
    (hm : generateVerifierFromPlan (fun _ _ => R.qblocks) R.inputs R.flags R.plan = .ok R.model) :
    R.model.quotientExternal.isSome = R.flags.externalQuotient := by
  sorry

/-- A V3-valid render is W-valid, with any evaluator object (it has no evaluator). PROVED from
    `model_quotientMode`. -/
theorem ValidW.ofV3 {R : Render p G₁ G₂ Gₜ} (Q : EvalObject) (h : ValidV3 R) : ValidW R Q := by
  obtain ⟨hc, hs⟩ := (validV3_iff_core R).mp h
  refine ⟨hc, SupportedW.ofV3 hs, fun he => ?_⟩
  have hm := model_quotientMode R (model_of_generated hc.generated)
  rw [hs.embeddedQuotient.1] at hm
  unfold isExternal at he
  rw [he] at hm
  cases hm

/-- A V3-valid render does not call an evaluator. PROVED from `model_quotientMode`. -/
theorem quotientExternal_none_of_V3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.model.quotientExternal = none := by
  obtain ⟨hc, hs⟩ := (validV3_iff_core R).mp hR
  have hm := model_quotientMode R (model_of_generated hc.generated)
  rw [hs.embeddedQuotient.1] at hm
  cases hqe : R.model.quotientExternal with
  | none => rfl
  | some qe => rw [hqe] at hm; cases hm

/-! ### `ValidW` does not constrain the evaluator's body

  `EvalPins` fixes the pin constants, the output pointer and CLOSEDNESS of `Q.body`; nothing
  else. So `(hR : ValidW R Q) : LoweringEquivalenceW R Q product` - the target as first stated
  here - is FALSE at an external render: the two lemmas below are the machine-checked half of the
  counterexample, and `WideningStages.lean` §7 states the target with the evaluator's contract as
  an explicit hypothesis (`lowering_correctW`) and derives what the old statement would have
  implied (`lowering_correctW_needs_evalContracts`). -/

/-- The empty block has no free name. PROVED (`freeNames` is defined by well-founded recursion and
    does not reduce by `rfl`; its equations do). -/
theorem freeNames_nil : (freeNames ([] : YulBlock)).isEmpty = true := by
  simp [freeNames, refSs, boundSs]

/-- **`ValidW` LEAVES THE EVALUATOR BODY FREE. PROVED.** Whatever body `Q` has, the same render is
    `ValidW` with the EMPTY body at the same output pointer. -/
theorem ValidW.emptyBody {R : Render p G₁ G₂ Gₜ} {Q : EvalObject} (h : ValidW R Q) :
    ValidW R ⟨[], Q.outMptr⟩ :=
  ⟨h.core, h.supported, fun he => ⟨(h.evaluator he).pin, (h.evaluator he).frame, freeNames_nil⟩⟩

/-- **THE EMPTY BODY ANSWERS `success` WITH NO RETURN DATA. PROVED.** Every modelled answer of an
    evaluator whose body is `[]` is a successful call returning zero bytes. Under
    `EvaluatorTrust.spec` these are ALL the chain's answers at a pinned state, so the verifier's
    return-size check after the call (`returndatasize() = outputLen`, `outputLen ≠ 0`) fails on
    every run, the contract reverts, and conjunct 2 of `LoweringEquivalenceW` (an honest run
    returns `true` on an accepted calldata) is false. -/
theorem evalModel_emptyBody (outMptr : Nat) (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256)
    (req : YulSemantics.EVM.CallRequest) (st : EvmState) (resp : CallResponse)
    (h : evalModel ⟨[], outMptr⟩ W Lyt qAddr req st resp) :
    resp.success = true ∧ resp.returndata = [] := by
  obtain ⟨stC, V', st', o, hentry, hrun, rfl⟩ := h
  have hst : st' = stC := by
    unfold YulSemantics.Run at hrun
    cases hrun with
    | block hb => cases hb; rfl
  subst hst
  obtain ⟨mem₀, aw, hs⟩ := hentry.shape
  have hh : st'.halted = none := by rw [hs]; rfl
  simp [Evaluator.responseOf, committedState, hh]

/-! ## Axiom audit -/

#print axioms supportedV2_iff_W
#print axioms acc_not_supportedV2
#print axioms verifyMsgs_ok_iff
#print axioms leanAcceptsAcc_iff_noAcc
#print axioms soundSide_of_leanAcceptsAcc
#print axioms leanAcceptsAcc_of_rust
#print axioms rust_or_collision_of_leanAcceptsAcc
#print axioms alpha_atMostOne
#print axioms evalModel_quiet
#print axioms evalModel_of_rel
#print axioms evaluatorTrust_model
#print axioms evalModel_gas_irrel
#print axioms callsW_le_permissive
#print axioms twoOutcomesW_of_scans           -- sorryAx: V3's two scan obligations
#print axioms lowering_equivalenceW_of
#print axioms prog_qAddr_irrel
#print axioms equivalenceW_iff_V3
#print axioms returns_of_rustAcceptsBoth
#print axioms rust_or_collision_of_returns
#print axioms returns_of_inhabitedW
#print axioms validV3_iff_core
#print axioms ValidW.ofV3                     -- sorryAx: model_quotientMode
#print axioms quotientExternal_none_of_V3     -- sorryAx: model_quotientMode
#print axioms freeNames_nil
#print axioms ValidW.emptyBody
#print axioms evalModel_emptyBody

end Midfall.LoweringW

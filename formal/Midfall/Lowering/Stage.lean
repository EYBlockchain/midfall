/-
  Stage.lean - the Lean verifier staged in the CONTRACT's order (SIM.1).

  Ported VERBATIM from section 1 of the design-evidence scratch file
  docs/plans/V3-evidence/lean/soundness/SoundnessV3.lean (HEAD b086937, lines 63-466), which
  RECON.1b-i rebased onto the tree and which elaborates in this tree: verified by 'lake env lean'
  at this commit. Nothing in section 1 moved in that rebase - its three adaptations
  (run_split/run_join's hhoist.symm scope, the BodyTotal conjunct, the G1CodecHeadlineLaws codec
  premise) are all in sections 2-5 - so the text below is the text the card cites.

  WHAT IS HERE (the card's Goal, in the scratch's order)
    abiHeadOk, envelopeOk, RawMsg, rawSlots, rawDecode, liftRaw,
    decodeSlots_eq_raw, decodeCalldata_eq_raw, decodeCalldata_isSome_iff, Decoded,
    PcsReads, pcsReads, SnapXcript, snapshotXcriptRun, Render.nSets, padSnap,
    LinFull, linearizeFull, linearize_eq_full, leanStage, LeanRaw, LeanFinal,
    leanStage_prefix (THE registered sorry), leanStage_pairing_ok, leanStage_pairing_of,
    leanAccepts_of_final.

  SEVEN PROVED LEMMAS, ONE SIM.1 LEAF. 'decodeSlots_eq_raw', 'decodeCalldata_eq_raw',
  'decodeCalldata_isSome_iff', 'linearize_eq_full', 'leanStage_pairing_ok', 'leanStage_pairing_of'
  and 'leanAccepts_of_final' are PROVED; the last one reaches the tree through the PROVED replay
  fact 'Midfall.Lowering.snapshotOf_prepareMsgs_ok' (D-GATE1 item 3 retired the old
  'snapshotOf_prepareMsgs' row and its only completeness-direction consumer,
  'leanFinal_of_accepts', which no root cone used).
  'leanStage_prefix' is the leaf SIM.1 was told to register: ALG, Lean-only, and NOT used by the
  glue (the scratch header records the same), so it sits outside the headline cone. SIM.9 removes it.

  TWO NAME ADAPTATIONS AND NOTHING ELSE (no statement was restated; both were checked by printing
  the ELABORATED declaration in the scratch and in this file and diffing them - identical):
    * the scratch lived in namespace 'Midfall.LoweringV2.V3', where the enclosing namespace made
      'instOfWords?' and 'LeanAccepts' resolve to 'Midfall.LoweringV2.*'. This file is
      'Midfall.Lowering.Stage', so those two names are written with that qualification - and they
      MUST name the LoweringV2 constants, because the frozen 'LeanAccepts'
      (LoweringV2/Statements.lean:1160) is stated over 'Midfall.LoweringV2.instOfWords?' and the
      linking lemmas compare the two conjuncts field for field. ('Midfall.Lowering.instOfWords?'
      is a copy of it in Accumulator.lean:1407, and 'Midfall.Lowering.LeanAccepts' is the v1
      Surface predicate at Surface.lean:883: both would be a different statement.)
    * the additions to 'Render' keep the scratch's '_root_.Midfall.LoweringV2.Render.*' spelling,
      so 'R.nSets' extends the same type the frozen statements are stated over.

  IMPORTS. 'Midfall.LoweringV2.Blocks' is the first edge from Midfall/Lowering/ into LoweringV2/;
  the card allows it ("the Render type can be replaced by its fields if Stage.lean must not import
  LoweringV2"). No cycle: Blocks imports Lowering.Snapshot and Lowering.Calldata, never this file.
  No Exec edit: 'linearizeFull' is a NEW def beside 'linearize', which is untouched.
  No 'native_decide' here (D-P17): the KATs live in Midfall/Instances/StageKats.lean.
-/
import Midfall.Lowering.Calldata
import Midfall.Lowering.Snapshot
import Midfall.LoweringV2.Blocks
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.Stage

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. The Lean verifier, staged in the contract's order

  The contract checks in the order: envelope (ABI guard + VkLoading), raw parse (parser:
  canonical scalars, in-range G1 words, cursor), x^n ≠ 1 (Lagrange), nothing (quotient),
  point validity + the two `scalar_inv` zero checks (PCS), pairing (FinalPairing).
  Lean checks in the order: decode (ALL of the above byte checks AND point validity at once),
  parseTrace, readAlgebra, lagrangeTriple, linearize, phaseA, phaseB, phaseC, assertEmpty, check.
  The two orders differ in exactly one structural way: the contract learns that a proof point is
  a group element LAST (G1MSM in the PCS block), Lean needs it FIRST. So the staged Lean state
  is split into
    * a RAW part, a predicate on the calldata bytes alone, and
    * a DECODE-RELATIVE part: for every decoding `ms` of the calldata, the Lean prefix at this
      checkpoint exists. -/

/-- Guards 1-4 of `decodeCalldata` (Calldata.lean:334-338): the selector (solc's dispatcher, via
    `EntryFrame.selector`), two static layout facts, and the two ABI head words the FIRST assembly
    block checks (Halo2Verifier.sol:148; `Program.abiGuardBlock`). Established by the PREFIX. -/
def abiHeadOk (L : ProofCalldataLayout) (cd : Bytes) : Bool :=
  (bytesTake cd 0 4 == some Midfall.Generator.fnSigVerifyProof) &&
  (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr) &&
  (L.proofEnd == L.proofCptr + L.proofLen) &&
  ((cdWord cd 4).toNat == 0x40 && (cdWord cd 0x24).toNat == L.proofEnd - 4)

/-- Guards 1-7 of `decodeCalldata` (Calldata.lean:334-341): the ABI head plus what
    VkLoading.yul:101-112 checks (proof length word, instance count word, calldatasize). -/
def envelopeOk (L : ProofCalldataLayout) (numInstances : Nat) (cd : Bytes) : Bool :=
  abiHeadOk L cd &&
  ((cdWord cd 0x44).toNat == L.proofLen) &&
  ((cdWord cd L.proofEnd).toNat == numInstances) &&
  (cd.size == L.proofEnd + 32 + 32 * numInstances)

/-- One slot of the repacked proof BEFORE point decoding: a 128-byte frame or a canonical scalar. -/
inductive RawMsg (p : ℕ) where
  | g1 (frame : Bytes)
  | fr (s : Fr p)

/-- `decodeSlots` (Calldata.lean:304) with the `ofEip?` call removed: exactly what the parser
    block checks (AssemblyHelpers.yul:94-104, TranscriptProofParser.yul:319, :382). -/
def rawSlots (cd : Bytes) : List WireSlot → Nat → Option (List (RawMsg p) × Nat)
  | [], cur => some ([], cur)
  | .g1 :: rest, cur =>
      if g1WordsOk cd cur then
        match bytesTake cd cur g1EipWidth with
        | none => none
        | some b =>
          match rawSlots cd rest (cur + g1EipWidth) with
          | none => none
          | some (ms, cur') => some (RawMsg.g1 b :: ms, cur')
      else none
  | .fr :: rest, cur =>
      if (cdWord cd cur).toNat < p then
        match rawSlots cd rest (cur + 32) with
        | none => none
        | some (ms, cur') => some (RawMsg.fr (Nat.cast (cdWord cd cur).toNat) :: ms, cur')
      else none

/-- `decodeCalldata` without point decoding. -/
def rawDecode (L : ProofCalldataLayout) (numInstances : Nat) (cd : Bytes) :
    Option (List (RawMsg p) × Array Word256) :=
  if envelopeOk L numInstances cd then
    match rawSlots (p := p) cd (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr with
    | none => none
    | some (ms, cur) =>
      let inst := (List.range numInstances).map (fun i => cdWord cd (L.proofEnd + 32 + 32 * i))
      if cur == L.proofEnd && inst.all (fun w => w.toNat < p) then some (ms, inst.toArray) else none
  else none

/-- The point-validity step the contract performs LAST (EIP-2537 G1MSM inside the PCS block). -/
def liftRaw (c : G1Codec G₁) : RawMsg p → Option (Msg (Fr p) G₁)
  | .g1 b => (c.ofEip? b).map Msg.g1
  | .fr s => some (Msg.fr s)

set_option linter.unusedSimpArgs false in
/-- The slot walk IS the raw walk followed by point decoding (PROVED). -/
theorem decodeSlots_eq_raw {G : Type} (c : G1Codec G) (cd : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat),
      decodeSlots (p := p) c cd slots cur =
        (rawSlots (p := p) cd slots cur).bind fun r =>
          (r.1.mapM (liftRaw c)).map fun ms => (ms, r.2) := by
  intro slots
  induction slots with
  | nil => intro cur; simp [decodeSlots, rawSlots]
  | cons sl rest ih =>
      intro cur
      cases sl with
      | g1 =>
          simp only [decodeSlots, rawSlots, ih]
          by_cases hg : g1WordsOk cd cur = true
          · cases hb : bytesTake cd cur g1EipWidth with
            | none => simp [hg, hb, guard]
            | some b =>
                cases hr : rawSlots (p := p) cd rest (cur + g1EipWidth) with
                | none => simp [hg, hb, hr, guard]
                | some r =>
                    obtain ⟨raw, cur'⟩ := r
                    cases hq : c.ofEip? b with
                    | none => simp [hg, hb, hr, hq, guard, liftRaw]
                    | some Q =>
                        cases hm : raw.mapM (liftRaw (p := p) c) with
                        | none => simp [hg, hb, hr, hq, hm, guard, liftRaw]
                        | some ms => simp [hg, hb, hr, hq, hm, guard, liftRaw]
          · simp [hg, guard]
      | fr =>
          simp only [decodeSlots, rawSlots, ih]
          by_cases hg : (cdWord cd cur).toNat < p
          · cases hr : rawSlots (p := p) cd rest (cur + 32) with
            | none => simp [hg, hr, guard]
            | some r =>
                obtain ⟨raw, cur'⟩ := r
                cases hm : raw.mapM (liftRaw (p := p) c) with
                | none => simp [hg, hr, hm, guard, liftRaw]
                | some ms => simp [hg, hr, hm, guard, liftRaw]
          · simp [hg, guard]

set_option linter.unusedSimpArgs false in
/-- **`decodeCalldata` IS the raw walk followed by point decoding (PROVED, Lean-only).** This is
    the lemma that splits the one Lean decode into what the parser checks (`rawDecode`) and what
    the PCS block's G1MSM checks (`liftRaw`, i.e. `ofEip?`). -/
theorem decodeCalldata_eq_raw {G : Type} (L : ProofCalldataLayout) (n : Nat) (c : G1Codec G)
    (cd : Bytes) :
    decodeCalldata (p := p) L n c cd =
      (rawDecode (p := p) L n cd).bind fun r =>
        (r.1.mapM (liftRaw c)).map fun ms => (ms, r.2) := by
  unfold decodeCalldata rawDecode envelopeOk abiHeadOk
  simp only [decodeSlots_eq_raw]
  by_cases h1 : (bytesTake cd 0 4 == some Midfall.Generator.fnSigVerifyProof) = true
  <;> by_cases h2 : (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr) = true
  <;> by_cases h3 : (L.proofEnd == L.proofCptr + L.proofLen) = true
  <;> by_cases h4 : ((cdWord cd 4).toNat == 0x40 && (cdWord cd 0x24).toNat == L.proofEnd - 4) = true
  <;> by_cases h5 : ((cdWord cd 0x44).toNat == L.proofLen) = true
  <;> by_cases h6 : ((cdWord cd L.proofEnd).toNat == n) = true
  <;> by_cases h7 : (cd.size == L.proofEnd + 32 + 32 * n) = true
  <;> simp [h1, h2, h3, h4, h5, h6, h7, guard]
  cases hr : rawSlots (p := p) cd (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr with
  | none => simp
  | some r =>
      obtain ⟨raw, cur⟩ := r
      cases hm : raw.mapM (liftRaw (p := p) c) with
      | none => simp [hm]; split_ifs <;> simp_all
      | some ms =>
          simp [hm]; split_ifs <;> simp_all
          rename_i hex hall
          obtain ⟨x, hx, hle⟩ := hex
          exact absurd (hall.2 x hx) (Nat.not_lt.mpr hle)

/-- COROLLARY (PROVED): a decoding exists exactly when the raw walk succeeds and every frame is
    a group element. The first conjunct is the parser's job, the second the PCS block's. -/
theorem decodeCalldata_isSome_iff {G : Type} (L : ProofCalldataLayout) (n : Nat) (c : G1Codec G)
    (cd : Bytes) :
    (decodeCalldata (p := p) L n c cd).isSome = true ↔
      ∃ raw instW, rawDecode (p := p) L n cd = some (raw, instW) ∧
        (raw.mapM (liftRaw c)).isSome = true := by
  rw [decodeCalldata_eq_raw]
  cases hr : rawDecode (p := p) L n cd with
  | none => simp
  | some r =>
      obtain ⟨raw, instW⟩ := r
      cases hm : raw.mapM (liftRaw (p := p) c) <;> simp [hm]

/-- The calldata decodes: the hypothesis pair every Lean prefix is relative to. -/
def Decoded (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
    (instW : Array Word256) (inst : Array (Fr p)) : Prop :=
  decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
    Midfall.LoweringV2.instOfWords? (p := p) instW = some inst  -- see header: the frozen LeanAccepts conjunct

/-! ### 1.1 The transcript-only prefix (the record digest D-3 asks for)

  The parser block writes x1..x4, fCom and pi. In Lean those are produced INSIDE phaseA/B/C,
  after `linearize` (logup panic) and interleaved with `fEval` (kzg/mod.rs:479 panic). A stage
  aligned with the parser must not run that algebra. `pcsReads` is the transcript half of the
  three phases (MultiOpen.lean:254-255, :278-283, :300, :306) with the algebra cut out; the only
  datum that flowed from the algebra into the schedule is the NUMBER of point sets, which is the
  layout's static `qEvals.itemCount`. -/

structure PcsReads (F G : Type) where
  x1 : F
  x2 : F
  fCom : G
  x3raw : F
  x3 : F
  qEvalsOnX3 : List F
  x4 : F
  pi : G

/-- The transcript operations of `multiPrepare`, in order, with no algebra. -/
def pcsReads {G : Type} (g1 : G1Codec G) (fc : FieldConsts (Fr p)) (feat : Features) (nSets : Nat) :
    TranscriptM (PcsReads (Fr p) G) := do
  let x1 ← tmSqueezeChallenge
  let x2 ← tmSqueezeChallenge
  let fCom ← tmRead (hashableG1 g1)
  let x3raw ← tmSqueezeChallenge
  let x3 := if feat.truncatedChallenges then truncate fc.numBits x3raw else x3raw
  let qEvalsOnX3 ← (List.range nSets).mapM (fun _ => tmRead (hashableFr (p := p)))
  let x4 ← tmSqueezeChallenge
  let pi ← tmRead (hashableG1 g1)
  pure { x1 := x1, x2 := x2, fCom := fCom, x3raw := x3raw, x3 := x3,
         qEvalsOnX3 := qEvalsOnX3, x4 := x4, pi := pi }

/-- Boundary `.transcript`: everything the parser block reads or squeezes, and nothing computed. -/
structure SnapXcript (p : ℕ) [Fact (Nat.Prime p)] (G₁ : Type) extends SnapAlgebra p G₁ where
  r : PcsReads (Fr p) G₁

/-- The transcript-only run: parseTrace, readAlgebra (existing runner), then the PCS reads, then
    the trailing-bytes check. No `linearize`, no `fEval`: it cannot panic at logup.rs:460 or
    kzg/mod.rs:479, and it cannot fail at `Error.opening`. -/
def snapshotXcriptRun (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (nSets : Nat) :
    Except Fault (SnapXcript p G₁) := do
  let (s2, t2) ← snapshotAlgebraRun E H vk inst ms
  let (r, t5) ← (pcsReads E.g1 E.field Features.solidity nSets).run t2
  t5.assertEmpty
  pure { toSnapAlgebra := s2, r := r }

/-- The layout's static number of point sets (one q_eval word per set). -/
def _root_.Midfall.LoweringV2.Render.nSets (R : Render p G₁ G₂ Gₜ) : Nat :=
  R.plan.proofLayout.qEvals.itemCount

/-- A Lean prefix presented as a `Snapshot` whose not-yet-computed fields hold inert defaults.
    This is the TRANSITIONAL carrier that lets `Inv` (which takes a full `Snapshot`) be reused
    verbatim at checkpoints before `.pcs`; `InvAt k` reads only prefix-`k` fields. -/
def padSnap (x : SnapXcript p G₁) (lag : LagrangeTriple (Fr p)) (ie : Option (Fr p))
    (queries : Array (VerifierQuery (Fr p) G₁)) : Snapshot p G₁ G₂ Gₜ :=
  { trace := x.trace, alg := x.alg, lagrange := lag, instanceEval := ie,
    queries := queries, lin := none,
    a := { x1 := x.r.x1, x2 := x.r.x2, qComs := #[], qEvalSets := #[], pointSets := #[] },
    b := { fCom := x.r.fCom, x3raw := x.r.x3raw, x3 := x.r.x3,
           qEvalsOnX3 := x.r.qEvalsOnX3, fEval := 0 },
    c := { x4 := x.r.x4, finalCom := ⟨#[], #[], #[]⟩, v := 0, pi := x.r.pi,
           dual := ⟨⟨#[], #[], #[]⟩, ⟨#[], #[], #[]⟩⟩ },
    acc := none }

/-- `linearize` (Verifier.lean:944) returning ALL THREE values it computes instead of one. This is
    the widening `Snapshot.lean` names as D6 limit 1 and never made; it is what turns the two
    inert `Inv .quotient` clauses (QUOTIENT_EVAL_MPTR, SELECTOR_ACC_MPTR) into live ones. -/
structure LinFull (F G : Type) where
  expressions : Array (Option Nat × F)
  linCom : VerifierQuery F G
  queries : Array (VerifierQuery F G)

def linearizeFull {G : Type} (delta : Fr p) (vk : VerifyingKey (Fr p) G)
    (adviceCommitments committedInstances : Array (Array G))
    (y beta gamma theta trashChallenge : Fr p) (challenges : Array (Fr p))
    (alg : Verifier.AlgebraRead (Fr p) G) : Except Fault (LinFull (Fr p) G) := do
  let expressions ← (partiallyEvaluateIdentities (p := p) (delta := delta)
    (vk := vk) (fixedEvals := alg.fixedEvals) (instanceEvals := alg.instanceEvals)
    (adviceEvals := alg.adviceEvals)
    (permutationEvals := alg.permutationsEvaluated.map (fun e => e.sets))
    (lookupEvals := alg.lookupsEvaluated.map (fun row => row.map (fun e => e.evaluated)))
    (trashcanEvals := alg.trashcansEvaluated.map (fun row => row.map (fun e => e.evaluated)))
    (permutationsCommon := alg.permutationsCommon) (x := alg.x) (xn := alg.xn) (beta := beta)
    (gamma := gamma) (theta := theta) (trashChallenge := trashChallenge)
    (challenges := challenges))
  let linCom ← (computeLinearizationCommitment (F := Fr p) (G₁ := G)
    expressions vk alg.x y alg.xn alg.splittingFactor alg.quotientLimbComs)
  let queries ← (Verifier.collectQueries (p := p) alg.nbCommitted vk alg.x
    (committedInstances := committedInstances) (adviceCommitments := adviceCommitments)
    (instanceEvals := alg.instanceEvals) (adviceEvals := alg.adviceEvals)
    (permutationsEvaluated := alg.permutationsEvaluated)
    (lookupsEvaluated := alg.lookupsEvaluated) (trashcansEvaluated := alg.trashcansEvaluated)
    (fixedEvals := alg.fixedEvals) (permutationsCommon := alg.permutationsCommon)
    (linCom := linCom))
  pure { expressions := expressions, linCom := linCom, queries := queries }

/-- The widening is a CUT, not a second computation: `linearize` is its `queries` projection. -/
theorem linearize_eq_full {G : Type} (delta : Fr p) (vk : VerifyingKey (Fr p) G)
    (adviceCommitments committedInstances : Array (Array G))
    (y beta gamma theta trashChallenge : Fr p) (challenges : Array (Fr p))
    (alg : Verifier.AlgebraRead (Fr p) G) :
    Verifier.linearize (p := p) delta vk adviceCommitments committedInstances
        y beta gamma theta trashChallenge challenges alg =
      (fun r => r.queries) <$> linearizeFull delta vk adviceCommitments committedInstances
        y beta gamma theta trashChallenge challenges alg := by
  simp only [Verifier.linearize, linearizeFull, map_bind, map_pure, bind_pure]

/-- **THE STAGE INDEX.** The Lean partial state at checkpoint `k`, for one decoding `ms`.
    Aligned with the seven partials: partial `q` takes `leanStage q.pre` to `leanStage q.post`.

      .start, .vk   no Lean computation (the envelope is a `LeanRaw` fact)
      .transcript   `snapshotXcriptRun`            faults: transcript read errors, invalidInstances,
                                                   static panics (verifier.rs:118/134/348/366/370/410)
      .lagrange     + `snapshotLagrangeStep`       faults: static only (circuit.rs blindingFactors, mod.rs:511)
      .quotient     + `linearizeFull`              faults: logup.rs:460 (DYNAMIC, no contract check),
                                                   static panics of the expression evaluators
      .pcs          `snapshotOf` (adds phaseA/B/C) faults: DuplicatedQuery (x = 0), kzg/mod.rs:479,
                                                   static panics (:391, arithmetic.rs)
      .pairing      + `DualMSM.check`              fault: Error.opening -/
def leanStage (R : Render p G₁ G₂ Gₜ) (H : Hash) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Checkpoint → Except Fault (Snapshot p G₁ G₂ Gₜ)
  | .start => .ok witnessSnapshot
  | .vk => .ok witnessSnapshot
  | .transcript => do
      let x ← snapshotXcriptRun R.E H R.vk inst ms R.nSets
      pure (padSnap x ⟨0, 0, 0⟩ none #[])
  | .lagrange => do
      let x ← snapshotXcriptRun R.E H R.vk inst ms R.nSets
      let l ← snapshotLagrangeStep (G₁ := G₁) R.vk x.toSnapAlgebra
      pure (padSnap x l.lagrange l.instanceEval #[])
  | .quotient => do
      let x ← snapshotXcriptRun R.E H R.vk inst ms R.nSets
      let l ← snapshotLagrangeStep (G₁ := G₁) R.vk x.toSnapAlgebra
      let q ← linearizeFull R.E.delta R.vk x.trace.adviceCommitments (committedShape (G₁ := G₁))
        x.trace.y x.trace.beta x.trace.gamma x.trace.theta x.trace.trashChallenge
        x.trace.challenges x.alg
      pure { padSnap x l.lagrange l.instanceEval q.queries with
             lin := some { expressions := q.expressions, linCom := q.linCom } }
  | .pcs => snapshotOf R.E H R.vk inst ms none
  | .pairing => do
      let S ← snapshotOf R.E H R.vk inst ms none
      if DualMSM.check S.c.dual R.params then pure S else throw (Fault.error Error.opening)

/-- The RAW half of the staged Lean state: facts about the calldata bytes alone. From `.pcs` on
    the calldata DECODES (every proof point passed a G1MSM). -/
def LeanRaw (R : Render p G₁ G₂ Gₜ) (cd : Bytes) : Checkpoint → Prop
  | .start => abiHeadOk R.plan.proofLayout cd = true
  | .vk => envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true
  | .transcript | .lagrange | .quotient =>
      (rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd).isSome = true
  | .pcs | .pairing => ∃ ms instW inst, Decoded R cd ms instW inst

/-- The last stage, closed: the calldata decodes, the snapshot exists, the pairing check holds. -/
def LeanFinal (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW inst, Decoded R cd ms instW inst ∧
    ∃ S, leanStage R H inst ms .pairing = .ok S

/-- LEAF (ALG, Lean-only; the chain IS a chain): a later stage existing implies the earlier one
    does. The steps `.transcript → .lagrange → .quotient` are immediate; `.quotient → .pcs` is the
    agreement of `snapshotXcriptRun` with `snapshotOf` (phaseA/B/C perform exactly `pcsReads`). -/
theorem leanStage_prefix (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (H : Hash) (cd : Bytes)
    (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (hdec : Decoded R cd ms instW inst) (k : Checkpoint) (S' : Snapshot p G₁ G₂ Gₜ)
    (h : leanStage R H inst ms k.next = .ok S') : ∃ S, leanStage R H inst ms k = .ok S := by
  sorry

/-! ### 1.2 The linking lemma: the last stage IS `LeanAccepts` (PROVED, both directions) -/

theorem leanStage_pairing_ok {R : Render p G₁ G₂ Gₜ} {H : Hash} {inst : Array (Fr p)}
    {ms : List (Msg (Fr p) G₁)} {S : Snapshot p G₁ G₂ Gₜ}
    (h : leanStage R H inst ms .pairing = .ok S) :
    snapshotOf R.E H R.vk inst ms none = .ok S ∧ DualMSM.check S.c.dual R.params = true := by
  unfold leanStage at h
  cases hs : snapshotOf R.E H R.vk inst ms none with
  | error e => rw [hs] at h; cases h
  | ok S0 =>
      rw [hs] at h
      by_cases hc : DualMSM.check S0.c.dual R.params = true
      · simp only [bind, Except.bind, hc, ite_true, pure, Except.pure] at h
        cases h
        exact ⟨rfl, hc⟩
      · simp only [bind, Except.bind, hc] at h
        cases h

theorem leanStage_pairing_of {R : Render p G₁ G₂ Gₜ} {H : Hash} {inst : Array (Fr p)}
    {ms : List (Msg (Fr p) G₁)} {S : Snapshot p G₁ G₂ Gₜ}
    (hs : snapshotOf R.E H R.vk inst ms none = .ok S)
    (hc : DualMSM.check S.c.dual R.params = true) :
    leanStage R H inst ms .pairing = .ok S := by
  unfold leanStage
  rw [hs]
  simp only [bind, Except.bind, hc, ite_true, pure, Except.pure]

/-- **LINK, soundness direction.** No Yul, no program. -/
theorem leanAccepts_of_final {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes}
    (h : LeanFinal R H cd) : Midfall.LoweringV2.LeanAccepts R H cd := by
  obtain ⟨ms, instW, inst, ⟨hdec, hinst⟩, S, hS⟩ := h
  obtain ⟨hsnap, hcheck⟩ := leanStage_pairing_ok hS
  refine ⟨ms, instW, inst, hdec, hinst, ?_⟩
  have hprep := snapshotOf_prepareMsgs_ok (Gₜ := Gₜ) R.E H R.vk inst ms none S hsnap
  unfold verifyMsgs
  rw [hprep]
  simp only [bind, Except.bind, hcheck]
  rfl

end Midfall.Lowering.Stage

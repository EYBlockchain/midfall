/-
  SoundnessV3.lean  (SCRATCH - design evidence for PLAN-V3, area "soundness architecture")

  Typechecked against the built tree with:   cd formal && lake env lean <this file>

  WHAT IS HERE
    §1  The Lean verifier staged in the CONTRACT's order (real definitions over existing functions).
    §2  The staged invariant `StageInv` and the per-block simulation contract `BlockSim`.
    §3  Composition: seven `BlockSim`s + a snapshot-free prefix contract  ==>  conjunct 1
        (returns => ABI true and LeanAccepts), with NO case split on LeanAccepts and NO `Rejects`.
    §4  Conjunct 3 (two outcomes) WITHOUT any snapshot: exit-shape scan + NoWriters.
    §5  Completeness with the SAME invariant family (`BlockProgS`), both halves composed, and
        the frozen `LoweringEquivalence` derived from the staged rows.
    §6  Migration: the TraceReturn row re-proved against `BlockSim` from the existing lemmas, and
        the generic lift that carries `fp_blockSound` over.
    §7  Evidence: two executable falsifiers and the leaf register (`#cone_sorries`).

  RULE FOLLOWED: definitions are real; leaf obligations (one per block / one per Lean-only fact) are
  `sorry`; every composition lemma is PROVED.

  THE SIX `sorry`s OF THIS FILE (all leaves; `decodeCalldata_eq_raw` is PROVED):
    leanStage_prefix        ALG  the staged Lean chain is a chain             (not used by the glue)
    xcript_total            ALG  the transcript-only prefix always exists     (not used by the glue)
    lean_fault_table        ALG  the fault table as a theorem; FALSE AT HEAD  (not used by the glue)
    prefix_sim              SEM  the six prefix statements, forall-runs form
    prefix_prog             SEM  the same statements, total form
    quiet_init              SEM-INFRA  exit discipline of scanned code
  The fourteen block rows (`Render.SimContracts`, `Render.ProgContracts`) are HYPOTHESES of the
  composition theorems, exactly as `BlockContractsAt` was.
-/
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.LoweringV2.V3

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
    instOfWords? (p := p) instW = some inst

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
    (h : LeanFinal R H cd) : LeanAccepts R H cd := by
  obtain ⟨ms, instW, inst, ⟨hdec, hinst⟩, S, hS⟩ := h
  obtain ⟨hsnap, hcheck⟩ := leanStage_pairing_ok hS
  refine ⟨ms, instW, inst, hdec, hinst, ?_⟩
  have hprep := (snapshotOf_prepareMsgs (Gₜ := Gₜ) R.E H R.vk inst ms none).1 S hsnap
  unfold verifyMsgs
  rw [hprep]
  simp only [bind, Except.bind, hcheck]
  rfl

/-- **LINK, completeness direction.** -/
theorem leanFinal_of_accepts {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes}
    (h : LeanAccepts R H cd) : LeanFinal R H cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, hv⟩ := h
  have hboth := snapshotOf_prepareMsgs (Gₜ := Gₜ) R.E H R.vk inst ms none
  cases hp : prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms with
  | error e =>
      unfold verifyMsgs at hv
      rw [hp] at hv
      cases hv
  | ok g =>
      have hok : (snapshotOf R.E H R.vk inst ms none).isOk = true := by
        rw [hboth.2, hp]; rfl
      cases hs : snapshotOf R.E H R.vk inst ms none with
      | error e => rw [hs] at hok; cases hok
      | ok S =>
          have hg : g = S.c.dual := by
            have h1 := hboth.1 S hs
            rw [hp] at h1
            exact Except.ok.inj h1
          have hcheck : DualMSM.check S.c.dual R.params = true := by
            unfold verifyMsgs at hv
            rw [hp] at hv
            by_cases hc : DualMSM.check g R.params = true
            · rw [← hg]; exact hc
            · simp only [bind, Except.bind, hc] at hv
              cases hv
          exact ⟨ms, instW, inst, ⟨hdec, hinst⟩, S, leanStage_pairing_of hs hcheck⟩


/-! ## 2. The staged invariant and the per-block simulation contract

  `StageInv k` has NO snapshot argument. It is five things:
    * `Frame` and `success = 1`                      (as `Clean` today)
    * `BaseInv k`    the snapshot-free clauses of `Inv` (halt record, locals, g1_identity window,
                     and from `.vk` on the payload image and the calldata length), UNCONDITIONAL
    * `LeanRaw k`    what the contract has established about the calldata bytes so far
    * `Mirror k`     memory regions that are verbatim copies of calldata sections, UNCONDITIONAL
                     (this is where the D-5 clauses live: they need no Lean value at all)
    * `Agree k`      for EVERY decoding of the calldata, the Lean prefix at `k` exists and `Inv k`
                     holds for it (the computed values: challenges, Lagrange, PCS scalars, pairing
                     inputs). Vacuous while the points are not known to be group elements, and
                     that is correct: until then the unconditional parts carry the proof. -/

/-- The checkpoint whose `Inv` clauses mention no snapshot field. -/
def baseCk : Checkpoint → Checkpoint
  | .start => .start
  | _ => .vk

/-- The snapshot-free clauses of `Inv`, at any boundary (`InvAt .start` / `InvAt .vk` read the
    snapshot only through `S.acc.isSome`, guarded by `hasAccumulator`). -/
def BaseInv (R : Render p G₁ G₂ Gₜ) (k : Checkpoint) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  match k with
  | .pcs | .pairing => True      -- the calldata decodes from here on, so `Agree` carries `Inv`
  | _ => Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params (baseCk k) R.pv
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) V st

/-- `n` bytes of calldata at offset `a` (no zero padding: a short slice is shorter). -/
def cdSlice (cd : Bytes) (a n : Nat) : Bytes :=
  ByteArray.mk ((cd.data.toList.drop a).take n).toArray

/-- A memory window is the verbatim copy of one calldata section (what `calldatacopy` /
    `mstore(eval_buf, calldataload(..))` leave behind in the parser). -/
def mirrorsSection (st : EvmState) (maddr : Nat) (cd : Bytes) (s : ProofSection) : Prop :=
  bytesAt st maddr s.byteLen = cdSlice cd s.start s.byteLen

/-- Lookup helpers and lookup accumulators interleave in calldata and are split in memory
    (TranscriptProofParser.yul:202-229): helper walk advances by the helper section, z walk by
    one G1 per lookup. -/
def lookupMirror (st : EvmState) (cd : Bytes) (hBase zBase : Nat) :
    List ProofLookupCommitmentsLayout → Nat → Nat → Prop
  | [], _, _ => True
  | l :: rest, hOff, i =>
      mirrorsSection st (hBase + hOff) cd l.helpers ∧
        mirrorsSection st (zBase + 128 * i) cd l.accumulator ∧
        lookupMirror st cd hBase zBase rest (hOff + l.helpers.byteLen) (i + 1)

/-- **THE CLAUSES DIGEST D-5 SAYS ARE MISSING FOR THE QUOTIENT-TO-PCS BOUNDARY**, stated against
    CALLDATA rather than against a snapshot: the five commitment regions `Inv` never pinned
    (lookup-m, perm-z, lookup-helper, lookup-z, trashcan), the REVERSED_EVALS window, plus the
    four regions `Inv .transcript` pins through the snapshot today. No `EvalRead → Fr` bridge is
    needed in the invariant: the window is the evals section word for word, and relating that
    section to Lean's six arrays is an ALG lemma about `decodeCalldata` and `readAlgebra`. -/
structure MirrorAt (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (st : EvmState) : Prop where
  advice : bytesAt st (ptrAddr R.pv.memory.adviceCommsMptrBase)
      (R.pv.proofLayout.advicePhases.foldl (fun a s => a + s.byteLen) 0) =
    cdSlice cd R.pv.proofLayout.proofCptr
      (R.pv.proofLayout.advicePhases.foldl (fun a s => a + s.byteLen) 0)
  lookupM : mirrorsSection st (ptrAddr R.pv.memory.lookupMCommsMptrBase) cd
      R.pv.proofLayout.lookupMultiplicities
  permZ : mirrorsSection st (ptrAddr R.pv.memory.permZCommsMptrBase) cd
      R.pv.proofLayout.permutationProducts
  lookups : lookupMirror st cd (ptrAddr R.pv.memory.lookupHelperCommsMptrBase)
      (ptrAddr R.pv.memory.lookupZCommsMptrBase) R.pv.proofLayout.lookups 0 0
  trash : mirrorsSection st (ptrAddr R.pv.memory.trashcanCommsMptrBase) cd R.pv.proofLayout.trash
  quotientLimbs : mirrorsSection st (ptrAddr R.pv.memory.quotientLimbCommsMptrBase) cd
      R.pv.proofLayout.quotientLimbs
  evals : mirrorsSection st (ptrAddr R.pv.memory.reversedEvalsMptr) cd R.pv.proofLayout.evals
  fCom : mirrorsSection st (ptrAddr R.pv.memory.fComMptr) cd R.pv.proofLayout.fCom
  pi : mirrorsSection st (ptrAddr R.pv.memory.piMptr) cd R.pv.proofLayout.pi
  qEvalCptr : wordAt st (ptrAddr R.pv.memory.qEvalCptrMptr) =
    BitVec.ofNat 256 R.pv.proofLayout.qEvalCptr

/-- The mirror is asserted between the parser and the PCS block, which is where it is read. -/
def Mirror (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (st : EvmState) : Checkpoint → Prop
  | .transcript | .lagrange | .quotient => MirrorAt R cd st
  | _ => True

/-- The decode-relative half: for every decoding, the Lean prefix exists and `Inv` holds for it. -/
def Agree (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  ∀ ms instW inst, Decoded R cd ms instW inst →
    ∃ S, leanStage R H inst ms k = .ok S ∧
      Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st

/-- **THE STAGED INVARIANT.** One family, used by soundness AND completeness. -/
def StageInv (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ BaseInv R k V st ∧
    LeanRaw R cd k ∧ Mirror R cd st k ∧ Agree R H cd k V st

/-- How block `q` finishes when nothing failed: at the next staged boundary, except TraceReturn,
    which returns ABI `true` AND carries the closed Lean stage out of the program. -/
def exitSim (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd
  | _ => o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st'

/-- **THE PER-BLOCK SIMULATION CONTRACT.** No snapshot is presupposed. From a staged boundary every
    run of the CLOSED slice, in scope, reverts; or exits normally with `success = 1`, the Lean
    stage at the next checkpoint reached (`LeanRaw` and, per decoding, `leanStage = .ok`) and the
    next invariant; or exits poisoned. From a poisoned boundary a run reverts or stays poisoned.
    The four §6 properties are kept: (i) closed slices in `R.scope`, (iii) the poisoned arm,
    (iv) facts via `Frame`; (ii) totality is `BlockProgS` in §5, over the same `StageInv`. -/
def BlockSim (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => StageInv R H vkAddr cd q.pre V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitSim R q H vkAddr cd V' st' o ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))

/-- THE NEW DIVERGENCE THIS DESIGN FOUND (fault table, row "x = 0"). Lean - and Rust - deduplicate
    the opening points by VALUE (Kzg/Utils.lean:137; kzg/utils.rs:46-52), so at `x = 0` every
    rotated point is 0: a commitment opened at two rotations is `DuplicatedQuery`, and otherwise
    the point sets merge and the read schedule shrinks. The contract's layout is static. It
    reverts at `x = 0` only through `scalar_inv` of a product that contains `pt_j - pt_k`, i.e.
    only if SOME static point set has two points. That is decidable on the plan, and it is TRUE
    at the deployment (measured: the sets are [[0],[0,1],[0,1,-9]]). -/
def hasMultiPointSet (R : Render p G₁ G₂ Gₜ) : Bool :=
  match Midfall.Generator.intermediateSets R.plan.meta_ R.plan.data with
  | .ok s => s.pointSets.any (fun ps => decide (2 ≤ ps.length))
  | .error _ => false

/-- The fallback if a render has several point sets and none with two points: a dynamic side
    condition, which would have to join `SoundSide` (frozen surface). Not needed at the deployment. -/
def XNonzero (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst S, Decoded R cd ms instW inst →
    snapshotOfAlgebra R.E H R.vk inst ms = .ok S → S.alg.x ≠ 0

/-- Static facts the simulation rows need and frozen `Valid` does not carry (D-10, A-4). Each is
    a computation or a codec theorem at a deployment; none is a semantic hypothesis. -/
structure SimPins (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- encoder-first compressed law: `verifyMsgs` re-reads every decoded point through it. -/
  compressedEnc : ∀ Q : G₁, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q
  /-- decoder-first EIP law: `Inv` compares memory (raw calldata bytes) with `toEip` of the
      decoded point. Frozen conjunct 1 carries no codec hypothesis (D-10). -/
  eipRt : R.E.g1.eipRoundtrip
  /-- the committed instance is absorbed as 128 zero bytes (TranscriptProofParser.yul:41-45). -/
  toEipOne : R.E.g1.toEip 1 = Midfall.natToBytesBE 0 128
  /-- the `x = 0` row of the fault table is discharged by a revert in the PCS block. -/
  multiPoint : hasMultiPointSet R = true

/-- **WHERE `SoundSide` ENTERS.** The seven simulation rows of a render, under the precompile
    assumption and the SOUNDNESS side conditions. Only the `.quotientLin` row reads `SoundSide`
    (it is the row whose Lean stage is `linearize`). -/
def _root_.Midfall.LoweringV2.Render.SimContracts (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  R.Valid → SimPins R → Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product →
  ∀ (H : Hash) (vkAddr : U256) (cd : Bytes), SoundSide R H cd →
    ∀ (q : Partial) (g : ExternalGas),
      BlockSim R q H vkAddr (permissive (callsOf product)) g cd

/-! ## 3. Composition (all PROVED) -/

section Seq

variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- A postcondition that says "continue at `mid`, or stop with `fin` already established". -/
def splitPost (mid : VEnv D → D.State → Prop) (fin : VEnv D → D.State → Outcome → Prop) :
    VEnv D → D.State → VEnv D → D.State → Outcome → Prop :=
  fun _ _ V' st' o => (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ fin V' st' o)

/-- Two split contracts compose to a split contract. -/
theorem seq_split {funs : FunEnv D} {a b : Block D.Op}
    {pre mid mid' : VEnv D → D.State → Prop} {fin : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsContractAll funs a pre (splitPost mid fin))
    (hb : StmtsContractAll funs b mid (splitPost mid' fin)) :
    StmtsContractAll funs (a ++ b) pre (splitPost mid' fin) := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases ha V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact hb V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne'
  · rcases ha V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hfin⟩
    · exact absurd heq hne
    · exact Or.inr ⟨hne, hfin⟩

/-- A split contract followed by a closing contract. -/
theorem seq_final {funs : FunEnv D} {a b : Block D.Op}
    {pre mid : VEnv D → D.State → Prop} {fin : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsContractAll funs a pre (splitPost mid fin))
    (hb : StmtsContractAll funs b mid (fun _ _ V' st' o => fin V' st' o)) :
    StmtsContractAll funs (a ++ b) pre (fun _ _ V' st' o => fin V' st' o) := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases ha V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact hb V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne'
  · rcases ha V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hfin⟩
    · exact absurd heq hne
    · exact hfin

/-- Seven blocks: six split contracts along a chain of mids, then a closing one. -/
theorem seq7 {funs : FunEnv D} {s1 s2 s3 s4 s5 s6 s7 : Block D.Op}
    {m0 m1 m2 m3 m4 m5 m6 : VEnv D → D.State → Prop}
    {fin : VEnv D → D.State → Outcome → Prop}
    (h1 : StmtsContractAll funs s1 m0 (splitPost m1 fin))
    (h2 : StmtsContractAll funs s2 m1 (splitPost m2 fin))
    (h3 : StmtsContractAll funs s3 m2 (splitPost m3 fin))
    (h4 : StmtsContractAll funs s4 m3 (splitPost m4 fin))
    (h5 : StmtsContractAll funs s5 m4 (splitPost m5 fin))
    (h6 : StmtsContractAll funs s6 m5 (splitPost m6 fin))
    (h7 : StmtsContractAll funs s7 m6 (fun _ _ V' st' o => fin V' st' o)) :
    StmtsContractAll funs (s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7) m0
      (fun _ _ V' st' o => fin V' st' o) :=
  seq_final (seq_split (seq_split (seq_split (seq_split (seq_split h1 h2) h3) h4) h5) h6) h7

end Seq

/-- The boundary predicate the chain runs on: staged-clean or poisoned. -/
def Mid (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  StageInv R H vkAddr cd k V st ∨ Poisoned R H vkAddr cd V st

/-- What the whole slice list may end in: a revert, or ABI `true` together with the closed Lean
    stage. THE LEAN FACT LEAVES THE PROGRAM HERE, which is what `slices_seq_sound` dropped. -/
def FinSim (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (_V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  (o = .halt ∧ Reverted st') ∨ (o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd)

/-- One non-terminal `BlockSim`, in the split form the chain consumes. -/
theorem blockSim_split {R : Render p G₁ G₂ Gₜ} {q : Partial} {H : Hash} {vkAddr : U256}
    {c : ExternalCalls} {g : ExternalGas} {cd : Bytes} (hq : q ≠ .traceReturn)
    (h : BlockSim R q H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Mid R H vkAddr cd q.pre V st)
      (splitPost (fun V st => Mid R H vkAddr cd q.pre.next V st)
        (fun V' st' o => FinSim R H cd V' st' o)) := by
  intro V st hpre V' st' o hrun
  have hhalt : (Outcome.halt : Outcome) ≠ Outcome.normal := by decide
  rcases hpre with hclean | hpois
  · rcases h.1 V st hclean V' st' o hrun with ⟨ho, hrev⟩ | hexit | ⟨_, ho, hp⟩
    · exact Or.inr ⟨ho ▸ hhalt, Or.inl ⟨ho, hrev⟩⟩
    · have hexit' : o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st' := by
        cases q <;> first | exact absurd rfl hq | exact hexit
      exact Or.inl ⟨hexit'.1, Or.inl hexit'.2⟩
    · exact Or.inl ⟨ho, Or.inr hp⟩
  · rcases h.2 V st hpois V' st' o hrun with ⟨ho, hrev⟩ | ⟨_, ho, hp⟩
    · exact Or.inr ⟨ho ▸ hhalt, Or.inl ⟨ho, hrev⟩⟩
    · exact Or.inl ⟨ho, Or.inr hp⟩

/-- The terminal `BlockSim`, in closing form. -/
theorem blockSim_final {R : Render p G₁ G₂ Gₜ} {H : Hash} {vkAddr : U256}
    {c : ExternalCalls} {g : ExternalGas} {cd : Bytes}
    (h : BlockSim R .traceReturn H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice .traceReturn)
      (fun V st => Mid R H vkAddr cd .pairing V st)
      (fun _ _ V' st' o => FinSim R H cd V' st' o) := by
  intro V st hpre V' st' o hrun
  rcases hpre with hclean | hpois
  · rcases h.1 V st hclean V' st' o hrun with hrev | hexit | ⟨hne, _⟩
    · exact Or.inl hrev
    · exact Or.inr hexit
    · exact absurd rfl hne
  · rcases h.2 V st hpois V' st' o hrun with hrev | ⟨hne, _⟩
    · exact Or.inl hrev
    · exact absurd rfl hne

/-- **SEQUENCING (replaces `slices_seq_sound`), PROVED.** Seven `BlockSim`s compose to one contract
    for `R.slices`: from a staged boundary at `.start`, every run reverts or returns ABI `true`
    WITH `LeanFinal`. Six applications of `seq_split` and one of `seq_final`. -/
theorem slices_seq_sim (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (h7 : ∀ q : Partial, BlockSim R q H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) R.slices
      (fun V st => Mid R H vkAddr cd .start V st)
      (fun _ _ V' st' o => FinSim R H cd V' st' o) :=
  seq7 (blockSim_split (q := .vkLoading) (by decide) (h7 .vkLoading))
    (blockSim_split (q := .transcriptParser) (by decide) (h7 .transcriptParser))
    (blockSim_split (q := .lagrange) (by decide) (h7 .lagrange))
    (blockSim_split (q := .quotientLin) (by decide) (h7 .quotientLin))
    (blockSim_split (q := .pcs) (by decide) (h7 .pcs))
    (blockSim_split (q := .finalPairing) (by decide) (h7 .finalPairing))
    (blockSim_final (h7 .traceReturn))

/-- Everything the closed program runs before the first slice (`funDef` statements included:
    each is a no-op step). -/
def _root_.Midfall.LoweringV2.Render.preBlock (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) : YulBlock :=
  R.preSlice vkAddr 0 ++ R.helpers ++ R.mainLocalsInlined

/-- **RUN DECOMPOSITION, PROVED from `prog_slices_decomp`** (the existential form digest C-3
    asks for: no prefix endpoint is fixed, so no determinism is needed). A committed run of the
    program IS a run of `preBlock ++ slices` in the block scope. -/
theorem run_split (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas)
    (st₀ : EvmState) (obs : Obs) (hobs : RunBody R vkAddr 0 c g st₀ obs) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome),
      obs = ⟨committedState st₀ st', o⟩ ∧
        ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
          (R.preBlock vkAddr ++ R.slices) V' st' o := by
  obtain ⟨V', st', hrun, heq⟩ := hobs
  obtain ⟨hprog, hhoist⟩ := prog_slices_decomp R vkAddr 0 c g
  have hrun' : ExecStmt (Bridge.Dialect c g) [] [] st₀ (.block (R.prog vkAddr 0)) V' st'
      obs.outcome := hrun
  cases hrun' with
  | block hstmts =>
      rename_i Vb
      refine ⟨Vb, st', obs.outcome, ?_, ?_⟩
      · cases obs
        simp only at heq ⊢
        rw [heq]
      · have hscope : R.scope c g = [hoist (Bridge.Dialect c g) (R.prog vkAddr 0)] := by
          show [hoist (Bridge.Dialect c g) R.helpers] = _
          rw [hhoist]
        rw [hscope]
        have hbody : R.preBlock vkAddr ++ R.slices = R.prog vkAddr 0 := by
          rw [hprog]; rfl
        rw [hbody]
        exact hstmts

/-- LEAF (SEM, one card: the six prefix statements). SNAPSHOT-FREE replacement of
    `prefix_run_clean`: from an entry frame every run of the prefix reverts (ABI guard, memory
    guard) or ends at a staged boundary at `.start`. No `LeanAccepts`, no snapshot in the
    statement: `StageInv .start` is `Frame`, `success = 1` and the three `Inv .start` clauses. -/
theorem prefix_sim (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (W : ExecEnv) (Lyt : EVM.Layout)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (splitPost (fun V st => Mid R H vkAddr cd .start V st)
        (fun V' st' o => FinSim R H cd V' st' o)) := by
  sorry

/-- **CONJUNCT 1 OF THE HEADLINE, PROVED from the seven rows and the prefix row.**
    A returning run returns ABI `true` and the Lean verifier accepts. There is NO case split on
    `LeanAccepts` and NO `Render.Rejects`: the Lean fact is carried forward by the invariant and
    read off at the return. `SoundSide` is consumed by `hsim` (the quotient row). -/
theorem soundness_of_sims (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hsim : R.SimContracts product)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (g : ExternalGas) (obs : Obs)
    (hobs : RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs)
    (hret : obs.isReturn) (hside : SoundSide R H cd) :
    obs.returnData = abiTrue ∧ LeanAccepts R H cd := by
  obtain ⟨V', st', o, heq, hrun⟩ := run_split R vkAddr (permissive (callsOf product)) g st₀ obs hobs
  have hall := seq_final
    (prefix_sim R hR W Lyt H vkAddr cd st₀ hdep hentry (permissive (callsOf product)) g)
    (slices_seq_sim R H vkAddr cd (permissive (callsOf product)) g
      (fun q => hsim hR hpins hpc H vkAddr cd hside q g))
  have hfin := hall [] st₀ ⟨rfl, rfl⟩ V' st' o hrun
  rw [heq] at hret ⊢
  rcases hfin with ⟨rfl, hrev⟩ | ⟨rfl, hh, hlean⟩
  · exact absurd (isRevertOrHalt_of_Reverted st₀ st' hrev) (not_isRevertOrHalt_of_isReturn hret)
  · exact ⟨returnData_of_committed_ret st₀ st' hh, leanAccepts_of_final hlean⟩

/-- **WHAT IS LEFT OF `Render.Rejects`: A COROLLARY.** Derived, not assumed. -/
theorem rejects_of_sims (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hsim : R.SimContracts product)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hside : SoundSide R H cd) (hna : ¬ LeanAccepts R H cd)
    (g : ExternalGas) (obs : Obs)
    (hobs : RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs) :
    ¬ obs.isReturn := fun hret =>
  hna (soundness_of_sims R product hR hpins hsim W Lyt H vkAddr cd st₀ hdep hentry hpc g obs
    hobs hret hside).2


/-! ## 4. Conjunct 3 (two outcomes) and world preservation WITHOUT any snapshot

  The argument is syntactic plus one local fact:
    (a) no `return`, `stop` or `selfdestruct` occurs anywhere before the TraceReturn slice, and
        `break`/`continue`/`leave` occur only inside a loop / a function  (decidable scan);
    (b) the TraceReturn slice halts on every run: with a revert, or with `return` of the word 1;
    (c) `NoWriters` (already a `Valid` clause) gives the world.
  Nothing here mentions `LeanAccepts`, `SoundSide` or a snapshot, so it holds on the logup-panic
  set, where `rejects_of_not_accepts` was false. -/

/-- The built-ins that end the frame with a COMMITTING halt (`HaltKind.commits`). -/
def isCommitHalt : EVM.Op → Bool
  | .ret | .stop | .selfdestruct => true
  | _ => false

/-- **THE DECIDABLE EXIT SCAN.** Fuel-bounded, structural in the fuel (so `decide` reduces it,
    like `Bridge.noWritersScan`). `lp` = inside a `for` body or post block, `fn` = inside a
    function body. Exhausted fuel answers `false`. -/
def exitScan : Nat → Bool → Bool → Scan → Bool
  | 0, _, _, _ => false
  | n + 1, lp, fn, sc =>
    match sc with
    | .e (.lit _) => true
    | .e (.var _) => true
    | .e (.builtin op args) => !isCommitHalt op && exitScan n lp fn (.es args)
    | .e (.call _ args) => exitScan n lp fn (.es args)
    | .es [] => true
    | .es (e :: rest) => exitScan n lp fn (.e e) && exitScan n lp fn (.es rest)
    | .s (.block body) => exitScan n lp fn (.b body)
    | .s (.funDef _ _ _ body) => exitScan n false true (.b body)
    | .s (.letDecl _ none) => true
    | .s (.letDecl _ (some e)) => exitScan n lp fn (.e e)
    | .s (.assign _ e) => exitScan n lp fn (.e e)
    | .s (.cond c body) => exitScan n lp fn (.e c) && exitScan n lp fn (.b body)
    | .s (.switch c cases dflt) =>
        exitScan n lp fn (.e c) && exitScan n lp fn (.cs cases) &&
          (match dflt with | none => true | some d => exitScan n lp fn (.b d))
    | .s (.forLoop init c post body) =>
        exitScan n lp fn (.b init) && exitScan n lp fn (.e c) &&
          exitScan n true fn (.b post) && exitScan n true fn (.b body)
    | .s (.exprStmt e) => exitScan n lp fn (.e e)
    | .s .break => lp
    | .s .continue => lp
    | .s .leave => fn
    | .b [] => true
    | .b (s :: ss) => exitScan n lp fn (.s s) && exitScan n lp fn (.b ss)
    | .cs [] => true
    | .cs ((_, b) :: rest) => exitScan n lp fn (.b b) && exitScan n lp fn (.cs rest)

/-- A block has the exit shape if the scan succeeds with some fuel. -/
def ExitShape (b : Block EVM.Op) : Prop := ∃ n, exitScan n false false (.b b) = true

/-- The scan is not vacuous: it rejects a `return`, a top-level `leave`, and accepts a revert. -/
example : exitScan 20 false false
    (.b [Stmt.exprStmt (Expr.builtin Op.ret [Expr.lit (.number 0), Expr.lit (.number 32)])]) =
    false := by decide
example : exitScan 20 false false (.b [Stmt.leave]) = false := by decide
example : exitScan 20 false false
    (.b [Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 4)])]) =
    true := by decide

/-- How a run that cannot commit may end: normally and not halted, or with a non-committing halt. -/
def QuietExit (st' : EvmState) (o : Outcome) : Prop :=
  (o = .normal ∧ st'.halted = none) ∨
    (o = .halt ∧ ∃ k d, st'.halted = some (k, d) ∧ k.commits = false)

/-- The first six slices. -/
def _root_.Midfall.LoweringV2.Render.slices6 (R : Render p G₁ G₂ Gₜ) : YulBlock :=
  R.slice .vkLoading ++ R.slice .transcriptParser ++ R.slice .lagrange ++
    R.slice .quotientLin ++ R.slice .pcs ++ R.slice .finalPairing

theorem slices_eq (R : Render p G₁ G₂ Gₜ) : R.slices = R.slices6 ++ R.slice .traceReturn := rfl

/-- The per-render exit clause: decided by computation at a deployment (address-independent:
    the wrapper addresses are literals). A candidate fourteenth clause of `Valid`. -/
def _root_.Midfall.LoweringV2.Render.ExitOk (R : Render p G₁ G₂ Gₜ) : Prop :=
  ExitShape (R.preBlock 0 ++ R.slices6)

/-- LEAF (SEM-INFRA, generic in content): the exit discipline of scanned code. The proof is the
    `Step` induction `Bridge.Run_worldEq_of_noWriters` also needs: a built-in other than
    `ret`/`stop`/`selfdestruct` never records a committing halt, a `staticcall` never records a
    halt of the calling frame, and a scanned function body ends `normal` or `leave`-caught. -/
theorem quiet_init (R : Render p G₁ G₂ Gₜ) (hx : R.ExitOk) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr ++ R.slices6)
      (fun _ st => st.halted = none) (fun _ _ _ st' o => QuietExit st' o) := by
  sorry

section TrExit

variable {c : ExternalCalls} {g : ExternalGas}

open Midfall.LoweringV2.Blocks.TraceReturn

/-- The guard expression `iszero(success)` yields one word and leaves the state alone, whatever
    `success` holds. (T.1's `tr_iszero_val` with the value hypothesis removed.) -/
theorem iszero_success_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {r : EResult (Bridge.Dialect c g)}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var "success"]) r) : ∃ w, r = .vals [w] st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var hget =>
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w] at hbi
                  obtain ⟨h1, h2⟩ := hbi
                  subst h2
                  subst h1
                  exact ⟨_, rfl⟩
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var hget => simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h => cases h

/-- The terminal guard, for ANY value of `success`: it reverts or is skipped. -/
theorem tr_guard_any {R : Render p G₁ G₂ Gₜ} {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
          [Stmt.exprStmt (Expr.call "fail" [trErrExpr R.consts])]) V' st' o) :
    (o = .halt ∧ Reverted st') ∨ (V' = V ∧ st' = st ∧ o = .normal) := by
  cases h with
  | ifTrue hc hnz hbody =>
      obtain ⟨w, hw⟩ := iszero_success_inv hc
      cases hw
      refine Or.inl ?_
      cases hbody with
      | block hstmts =>
          have hl : lookupFun
              (hoist (Bridge.Dialect c g)
                [Stmt.exprStmt (Expr.call "fail" [trErrExpr R.consts])] :: funs) "fail" =
              some (failFDecl, funs') := by
            show lookupFun funs "fail" = some (failFDecl, funs')
            exact hlookup
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hstmts with
              ⟨V₁, st₁, h₁, hnil⟩ | ⟨h₁, hne⟩
          · exact absurd (tr_fail_reverts hl h₁).1
              (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
          · exact tr_fail_reverts hl h₁
  | ifFalse hc hz =>
      obtain ⟨w, hw⟩ := iszero_success_inv hc
      cases hw
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | ifHalt hc =>
      obtain ⟨w, hw⟩ := iszero_success_inv hc
      cases hw

/-- **THE TRACERETURN EXIT, SNAPSHOT-FREE AND STATE-FREE (PROVED).** From ANY state, every run of
    the slice halts: with a revert, or with a `return` whose payload is `abiTrue`. This is the
    only committing halt of the program. Re-uses T.1's step lemmas verbatim. -/
theorem tr_exit_any (R : Render p G₁ G₂ Gₜ) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice .traceReturn)
      (fun _ _ => True)
      (fun _ _ _ st' o => o = .halt ∧ (Reverted st' ∨ st'.halted = some (.ret, abiTrue))) := by
  intro V st _ V' st' o hrun
  rw [tr_slice R] at hrun
  have hl : lookupFun (R.scope c g) "fail" = some (failFDecl, R.scope c g) := fail_lookup R
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · rcases tr_guard_any hl h₁ with ⟨habs, _⟩ | ⟨rfl, rfl, _⟩
    · cases habs
    · rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest with
          ⟨V₂, st₂, h₂, hlast⟩ | ⟨h₂, hne₂⟩
      · obtain ⟨a, haddr, rfl, hst₂⟩ := tr_mstore_step h₂
        rw [hst₂] at hlast
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hlast with
            ⟨V₃, st₃, h₃, hnil⟩ | ⟨h₃, hne₃⟩
        · have h0 := tr_ret_o h₃
          cases h0
        · have ho : o = Outcome.halt := tr_ret_o h₃
          subst ho
          obtain ⟨rfl, hrec⟩ := tr_ret_step haddr h₃
          have hpay : some (HaltKind.ret, readBytes (storeWord st₁.memory (BitVec.toNat a) 1)
              (BitVec.toNat a) 32) = some (HaltKind.ret, abiTrue) :=
            congrArg (fun x => some (HaltKind.ret, x)) (readBytes_storeWord_one _ _)
          exact ⟨rfl, Or.inr (hrec.trans hpay)⟩
      · exact absurd (tr_mstore_o h₂) hne₂
  · rcases tr_guard_any hl h₁ with hrev | ⟨_, _, ho⟩
    · exact ⟨hrev.1, Or.inl hrev.2⟩
    · exact absurd ho hne

end TrExit

/-- An entry frame is not halted (PROVED: `initState` starts from `EvmState.init`). -/
theorem entry_not_halted {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st₀ : EvmState} (h : EntryFrame R W Lyt H cd st₀) : st₀.halted = none := by
  obtain ⟨mem₀, aw, rfl⟩ := h.shape
  rfl

/-- **CONJUNCT 3 OF THE HEADLINE, PROVED** from the scan leaf, the TraceReturn exit and
    `NoWriters`. No snapshot, no `LeanAccepts`, no `SoundSide`, no precompile assumption, ANY call
    relation and ANY gas oracle. Replaces `rejects_of_not_accepts`. -/
theorem two_outcomes_of_exitShape (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (hx : R.ExitOk)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hentry : EntryFrame R W Lyt H cd st₀) (c : ExternalCalls) (g : ExternalGas) (obs : Obs)
    (hobs : RunBody R vkAddr 0 c g st₀ obs) :
    obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀) := by
  have hw : WorldEq st₀ obs.state := worldEq_of_runBody R hR vkAddr c g st₀ obs hobs
  obtain ⟨V', st', o, heq, hrun⟩ := run_split R vkAddr c g st₀ obs hobs
  have h0 : st₀.halted = none := entry_not_halted hentry
  have hrun' : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
      ((R.preBlock vkAddr ++ R.slices6) ++ R.slice .traceReturn) V' st' o := by
    rw [List.append_assoc, ← slices_eq]
    exact hrun
  rw [heq] at hw ⊢
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun' with
      ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · obtain ⟨ho, hfin⟩ := tr_exit_any R V₁ st₁ trivial V' st' o h₂
    subst ho
    rcases hfin with hrev | hret
    · exact Or.inr ⟨isRevertOrHalt_of_Reverted st₀ st' hrev, hw⟩
    · exact Or.inl (view_eq_returnView_of_committed st₀ st' hw hret)
  · rcases quiet_init R hx vkAddr c g [] st₀ h0 V' st' o h₁ with ⟨ho, _⟩ | ⟨ho, k, d, hk, hc⟩
    · exact absurd ho hne
    · refine Or.inr ⟨⟨k, d, ?_, hc⟩, hw⟩
      show (committedState st₀ st').halted = some (k, d)
      rw [halted_committedState, hk]

/-! ## 5. Completeness over the SAME invariant

  One invariant family serves both directions. What differs is not the boundary predicate but
  (a) the call relation (honest instead of permissive), (b) the hypotheses on the calldata
  (`LeanAccepts` and `CompleteSide` instead of `SoundSide`), and (c) the shape of the claim
  (a run exists and every run takes the clean exit; no revert arm, no poisoned arm). -/

/-- The clean exit of block `q`, without the Lean fact (under `LeanAccepts` it is a hypothesis). -/
def exitProg (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue)
  | _ => o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st'

/-- **THE TOTAL PROGRESS CONTRACT**, over `StageInv`. -/
def BlockProgS (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes) : Prop :=
  StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (R.scope _ _) (R.slice q)
    (fun V st => StageInv R H vkAddr cd q.pre V st)
    (fun _ _ V' st' o => exitProg R q H vkAddr cd V' st' o)

/-- **WHERE `CompleteSide` ENTERS.** Only the `.lagrange` row reads it (x^n ≠ 1). -/
def _root_.Midfall.LoweringV2.Render.ProgContracts (R : Render p G₁ G₂ Gₜ)
    (product : PairingProduct) : Prop :=
  R.Valid → SimPins R → Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecLaws R.E.g1 →
  ∀ (H : Hash) (vkAddr : U256) (cd : Bytes), LeanAccepts R H cd → CompleteSide R H cd →
    ∀ q : Partial, BlockProgS R q H vkAddr product cd

section SeqEx

variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- Runs concatenate (the converse of `Step.stmts_append_inv`, normal-head case). -/
theorem stmts_append_run {funs : FunEnv D} {a b : Block D.Op} :
    ∀ {V : VEnv D} {st : D.State} {V₁ : VEnv D} {st₁ : D.State} {V' : VEnv D} {st' : D.State}
      {o : Outcome},
      ExecStmts D funs V st a V₁ st₁ .normal → ExecStmts D funs V₁ st₁ b V' st' o →
        ExecStmts D funs V st (a ++ b) V' st' o := by
  induction a with
  | nil =>
      intro V st V₁ st₁ V' st' o h₁ h₂
      cases h₁
      exact h₂
  | cons s rest ih =>
      intro V st V₁ st₁ V' st' o h₁ h₂
      cases h₁ with
      | seqCons hs hrest => exact Step.seqCons hs (ih hrest h₂)
      | seqStop hs hne => exact absurd rfl hne

/-- Existence composes: a block that ends normally at `mid`, then a block from `mid`. -/
theorem ex_append {funs : FunEnv D} {a b : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsContract funs a pre (fun _ _ V' st' o => o = .normal ∧ mid V' st'))
    (hb : StmtsContract funs b mid (fun _ _ V' st' o => post V' st' o)) :
    StmtsContract funs (a ++ b) pre (fun _ _ V' st' o => post V' st' o) := by
  intro V st hpre
  obtain ⟨V₁, st₁, o₁, h₁, ho, hmid⟩ := ha V st hpre
  subst ho
  obtain ⟨V', st', o, h₂, hpost⟩ := hb V₁ st₁ hmid
  exact ⟨V', st', o, stmts_append_run h₁ h₂, hpost⟩

/-- Total contracts compose (both halves). -/
theorem total_append {funs : FunEnv D} {a b : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsTotal funs a pre (fun _ _ V' st' o => o = .normal ∧ mid V' st'))
    (hb : StmtsTotal funs b mid (fun _ _ V' st' o => post V' st' o)) :
    StmtsTotal funs (a ++ b) pre (fun _ _ V' st' o => post V' st' o) := by
  refine ⟨ex_append ha.1 hb.1, ?_⟩
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · exact hb.2 V₁ st₁ (ha.2 V st hpre V₁ st₁ .normal h₁).2 V' st' o h₂
  · exact absurd (ha.2 V st hpre V' st' o h₁).1 hne

end SeqEx

/-- One non-terminal progress row in chain form. -/
theorem blockProg_step {R : Render p G₁ G₂ Gₜ} {q : Partial} {H : Hash} {vkAddr : U256}
    {product : PairingProduct} {cd : Bytes} (hq : q ≠ .traceReturn)
    (h : BlockProgS R q H vkAddr product cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.slice q)
      (fun V st => StageInv R H vkAddr cd q.pre V st)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st') := by
  have hconv : ∀ (V' : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)))
      (st' : EvmState) (o : Outcome), exitProg R q H vkAddr cd V' st' o →
      o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st' := by
    intro V' st' o hexit
    cases q <;> first | exact absurd rfl hq | exact hexit
  refine ⟨?_, ?_⟩
  · intro V st hpre
    obtain ⟨V', st', o, hrun, hexit⟩ := h.1 V st hpre
    exact ⟨V', st', o, hrun, hconv V' st' o hexit⟩
  · intro V st hpre V' st' o hrun
    exact hconv V' st' o (h.2 V st hpre V' st' o hrun)

/-- **SEQUENCING, PROGRESS (replaces `slices_seq_progress`), PROVED - BOTH HALVES.** -/
theorem slices_seq_prog (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (h7 : ∀ q : Partial, BlockProgS R q H vkAddr product cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) R.slices
      (fun V st => StageInv R H vkAddr cd .start V st)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) :=
  total_append
    (total_append
      (total_append
        (total_append
          (total_append
            (total_append (blockProg_step (q := .vkLoading) (by decide) (h7 .vkLoading))
              (blockProg_step (q := .transcriptParser) (by decide) (h7 .transcriptParser)))
            (blockProg_step (q := .lagrange) (by decide) (h7 .lagrange)))
          (blockProg_step (q := .quotientLin) (by decide) (h7 .quotientLin)))
        (blockProg_step (q := .pcs) (by decide) (h7 .pcs)))
      (blockProg_step (q := .finalPairing) (by decide) (h7 .finalPairing)))
    (h7 .traceReturn)

/-- LEAF (SEM, same card as `prefix_sim`): under the honest calls and a decodable calldata the
    prefix run EXISTS and every prefix run ends at the staged boundary `.start`. -/
theorem prefix_prog (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hacc : LeanAccepts R H cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd .start V' st') := by
  sorry

/-- The converse of `run_split` (PROVED from `prog_slices_decomp`): a run of `preBlock ++ slices`
    in the block scope is a committed run of the program. -/
theorem run_join (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas)
    (st₀ : EvmState) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
      (R.preBlock vkAddr ++ R.slices) V' st' o) :
    RunBody R vkAddr 0 c g st₀ ⟨committedState st₀ st', o⟩ := by
  obtain ⟨hprog, hhoist⟩ := prog_slices_decomp R vkAddr 0 c g
  have hscope : R.scope c g = [hoist (Bridge.Dialect c g) (R.prog vkAddr 0)] := by
    show [hoist (Bridge.Dialect c g) R.helpers] = _
    rw [hhoist]
  have hbody : R.preBlock vkAddr ++ R.slices = R.prog vkAddr 0 := by
    rw [hprog]; rfl
  rw [hscope, hbody] at hrun
  exact ⟨restore [] V', st', Step.block hrun, rfl⟩

/-- **CONJUNCT 2 OF THE HEADLINE, PROVED** from the seven progress rows and the prefix row. -/
theorem completeness_of_progs (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hprog : R.ProgContracts product)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) (hcodec : G1CodecLaws R.E.g1) :
    (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
      ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
        obs.view = returnView st₀ := by
  have htot := total_append
    (prefix_prog R product hR W Lyt H vkAddr cd st₀ hdep hentry hacc)
    (slices_seq_prog R product H vkAddr cd
      (fun q => hprog hR hpins hpc hcodec H vkAddr cd hacc hcomp q))
  refine ⟨?_, ?_⟩
  · obtain ⟨V', st', o, hrun, _⟩ := htot.1 [] st₀ ⟨rfl, rfl⟩
    exact ⟨_, run_join R vkAddr _ _ st₀ V' st' o hrun⟩
  · intro obs hobs
    have hw : WorldEq st₀ obs.state := worldEq_of_runBody R hR vkAddr _ _ st₀ obs hobs
    obtain ⟨V', st', o, heq, hrun⟩ := run_split R vkAddr _ _ st₀ obs hobs
    obtain ⟨ho, hh⟩ := htot.2 [] st₀ ⟨rfl, rfl⟩ V' st' o hrun
    subst ho
    rw [heq] at hw ⊢
    exact view_eq_returnView_of_committed st₀ st' hw hh

/-- **THE HEADLINE FROM THE STAGED CONTRACTS (PROVED).** `Render.Rejects`, `BlockSound`,
    `BlockProgress`, `prefix_run_clean`, `runBody_iff_slices`, `slices_seq_sound`,
    `slices_seq_progress` and `rejects_of_not_accepts` do not occur, and NO hypothesis beyond the
    frozen headline's own is used: the side conditions are exactly `SoundSide` (conjunct 1) and
    `CompleteSide` (conjunct 2), each consumed by one row. -/
theorem lowering_equivalence_of_stages (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hpins : SimPins R) (hexit : R.ExitOk)
    (hsim : R.SimContracts product) (hprog : R.ProgContracts product) :
    LoweringEquivalence R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc
  refine ⟨?_, ?_, ?_⟩
  · intro g obs hobs hret hside
    exact soundness_of_sims R product hR hpins hsim W Lyt H vkAddr cd st₀ hdep hentry hpc
      g obs hobs hret hside
  · intro hacc hcomp hcodec
    exact completeness_of_progs R product hR hpins hprog W Lyt H vkAddr cd st₀ hdep hentry hpc
      hacc hcomp hcodec
  · intro g obs hobs
    exact two_outcomes_of_exitShape R hR hexit W Lyt H vkAddr cd st₀ hentry _ g obs hobs

/-! ## 6. Migration: existing proved rows against the new contract (PROVED) -/

/-- `Decoded` is functional in the calldata. -/
theorem decoded_unique {R : Render p G₁ G₂ Gₜ} {cd : Bytes}
    {ms ms' : List (Msg (Fr p) G₁)} {instW instW' : Array Word256} {inst inst' : Array (Fr p)}
    (h : Decoded R cd ms instW inst) (h' : Decoded R cd ms' instW' inst') :
    ms = ms' ∧ instW = instW' ∧ inst = inst' := by
  obtain ⟨hd, hi⟩ := h
  obtain ⟨hd', hi'⟩ := h'
  rw [hd] at hd'
  have hpair : (ms, instW) = (ms', instW') := Option.some.inj hd'
  have h1 : ms = ms' := congrArg Prod.fst hpair
  have h2 : instW = instW' := congrArg Prod.snd hpair
  subst h1 h2
  rw [hi] at hi'
  exact ⟨rfl, rfl, Option.some.inj hi'⟩

/-- One decoding's prefix and invariant give `Agree` (for all decodings: there is only one). -/
theorem agree_of_one {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes} {k : Checkpoint}
    {c : ExternalCalls} {g : ExternalGas} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    {S : Snapshot p G₁ G₂ Gₜ} (hdec : Decoded R cd ms instW inst)
    (hS : leanStage R H inst ms k = .ok S)
    (hinv : Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st) :
    Agree R H cd k V st := by
  intro ms' instW' inst' hdec'
  obtain ⟨rfl, rfl, rfl⟩ := decoded_unique hdec hdec'
  exact ⟨S, hS, hinv⟩

/-- **THE TRACERETURN ROW MIGRATES UNCHANGED (PROVED, no new semantics, no pin).** T.1's and
    T.2's walks give `BlockSim R .traceReturn`: the closed Lean stage is read off the boundary
    (`LeanRaw .pairing` + `Agree .pairing`) and handed out with the return. -/
theorem tr_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash) (vkAddr : U256)
    (g : ExternalGas) (cd : Bytes) :
    BlockSim R .traceReturn H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    have hclean : Clean R Checkpoint.pairing S H vkAddr cd V st := ⟨hinv, hframe, hsucc⟩
    rcases Blocks.TraceReturn.tr_sound_clean_noarm R product S H vkAddr cd g hclean hrun with
        hrev | hok
    · exact Or.inl hrev
    · obtain ⟨ho, hh⟩ := exitOk_traceReturn_apply hok
      exact Or.inr (Or.inl ⟨ho, hh, ms, instW, inst, hdec, S, hS⟩)
  · intro V st hpre V' st' o hrun
    exact Or.inl (Blocks.TraceReturn.tr_poison_walk_noarm R H vkAddr cd hpre hrun)

/-- **THE TRACERETURN PROGRESS ROW MIGRATES TOO (PROVED)**, with T.2's pin `trRetMptr`. -/
theorem tr_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hpin : Blocks.TraceReturn.trRetMptr R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockProgS R .traceReturn H vkAddr product cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    obtain ⟨V', st', o, hrun, hexit⟩ :=
      (Blocks.TraceReturn.tr_blockProgress R product hpin S H vkAddr cd).1 V st
        ⟨hinv, hframe, hsucc⟩
    exact ⟨V', st', o, hrun, exitOk_traceReturn_apply hexit⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    exact exitOk_traceReturn_apply
      ((Blocks.TraceReturn.tr_blockProgress R product hpin S H vkAddr cd).2 V st
        ⟨hinv, hframe, hsucc⟩ V' st' o hrun)

/-- **THE GENERIC LIFT FOR A BLOCK THAT STARTS AFTER THE DECODE IS KNOWN** (PROVED). At `.pcs` the
    calldata decodes and the snapshot exists, so a snapshot-relative `BlockSound` for that one
    snapshot IS the simulation row. This is how `fp_blockSound` migrates. -/
theorem fp_blockSim_of_blockSound (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (H : Hash)
    (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas) (cd : Bytes)
    (hsound : ∀ ms instW inst Snap, Decoded R cd ms instW inst →
      snapshotOf R.E H R.vk inst ms none = .ok Snap →
      BlockSound R .finalPairing Snap H vkAddr c g cd)
    (hpoison : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice .finalPairing)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (Partial.finalPairing ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))) :
    BlockSim R .finalPairing H vkAddr c g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    obtain ⟨hframe, hsucc, _, hraw, _, hagree⟩ := hpre
    obtain ⟨ms, instW, inst, hdec⟩ := hraw
    obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
    have hsnap : snapshotOf R.E H R.vk inst ms none = .ok S := hS
    have hclean : Clean R Checkpoint.pcs S H vkAddr cd V st := ⟨hinv, hframe, hsucc⟩
    rcases (hsound ms instW inst S hdec hsnap).1 V st hclean V' st' o hrun with
        hrev | hok | hpois
    · exact Or.inl hrev
    · obtain ⟨ho, hinv', hframe', hsucc'⟩ :
          o = .normal ∧ Clean R Checkpoint.pairing S H vkAddr cd V' st' := hok
      have hcheck : DualMSM.check S.c.dual R.params = true := by
        rcases Inv.pairing_dualMsm_or hinv' with hacc | hc
        · rw [Blocks.VkLoading.pv_hasAcc_false R hR] at hacc
          cases hacc
        · exact hc
      refine Or.inr (Or.inl ⟨ho, hframe', hsucc', trivial, ⟨ms, instW, inst, hdec⟩, trivial, ?_⟩)
      exact agree_of_one hdec (leanStage_pairing_of hsnap hcheck) hinv'
    · exact Or.inr (Or.inr hpois)
  · exact hpoison


/-! ## 6.1 The Lean-only leaves the block rows consume (STATEMENTS; ALG layer)

  These are what make the fault table a THEOREM instead of a document. Neither mentions Yul. -/

/-- LEAF (ALG): on a decodable calldata of a valid render the TRANSCRIPT-ONLY prefix always
    exists. Its only possible faults are static (shape of the key against the layout) or codec
    laws (`SimPins.compressedEnc`, the scalar round trip). This is the parser row's Lean half. -/
theorem xcript_total (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (hpins : SimPins R) (H : Hash)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (hdec : Decoded R cd ms instW inst) :
    ∃ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x := by
  sorry

/-- **THE FAULT TABLE AS A THEOREM (LEAF, ALG).** On a decodable calldata of a valid render,
    outside the logup-panic set, the Lean pipeline has exactly TWO ways not to produce a snapshot:
    `x = 0` (the opening points coincide: `DuplicatedQuery` or a collapsed schedule) and `x3` in
    a point set (kzg/mod.rs:479). Every other fault site of the table is unreachable.

    THIS IS FALSE AT HEAD and is the acceptance test of the reference repairs: with value-equality
    grouping (`kzgCommitBeq`) two equal one-piece commitments give `Error.opening`, and with
    structural `Rotation` equality an imported key panics in the permutation identity. -/
theorem lean_fault_table (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (hpins : SimPins R) (H : Hash)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (hdec : Decoded R cd ms instW inst) (hside : SoundSide R H cd) :
    (∃ S, snapshotOf R.E H R.vk inst ms none = .ok S) ∨
      (∃ S2, snapshotOfAlgebra R.E H R.vk inst ms = .ok S2 ∧ S2.alg.x = 0) ∨
      prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms =
        .error (Fault.panic "proofs/src/poly/kzg/mod.rs:479") := by
  sorry

/-! ## 7. Evidence: falsifiers and the leaf register -/

section Evidence

open Midfall.Lowering.CdKats

local instance fact17ev : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The right-hand side of `decodeCalldata_eq_raw`, as a comparable code. -/
def rawThenLift (L : ProofCalldataLayout) (n : Nat) (cd : Bytes) :
    Option (List (Nat × Nat) × List Nat) :=
  (rawDecode (p := 17) L n cd).bind fun r =>
    (r.1.mapM (liftRaw toyCodec)).map fun ms => (ms.map msgCode, r.2.toList.map (·.toNat))

def decodeCode (L : ProofCalldataLayout) (n : Nat) (cd : Bytes) :
    Option (List (Nat × Nat) × List Nat) :=
  (decodeCalldata (p := 17) L n toyCodec cd).map fun r =>
    (r.1.map msgCode, r.2.toList.map (·.toNat))

/-- FALSIFIER FOR THE LEAF `decodeCalldata_eq_raw`: the two sides agree on the tree's own
    calldata fixture and on every perturbation `decodeCalldataGuards_ok` uses, PLUS the case the
    split exists for: a frame that passes the parser's range check and is not a group element
    (raw walk succeeds, lift fails, decode fails). -/
def rawDecodeAgreesKats_ok : Bool :=
  let cd := Midfall.Lowering.calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 7]
  let nats := Midfall.Generator.bytesToNats cd
  let replace (pos : Nat) (v : List Nat) : Bytes :=
    Midfall.Generator.bytesFromNats
      ((List.take pos nats) ++ v ++ (List.drop (pos + v.length) nats))
  let cases : List (ProofCalldataLayout × Nat × Bytes) :=
    [ (katLayout, 1, cd),
      (katLayout, 1, cd ++ Midfall.natToBytesBE 0 32),
      (katLayout, 1, replace 0 [0xde, 0xad, 0xbe, 0xef]),
      (katLayout, 1, replace 0x44 (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 415 32))),
      (katLayout, 2, cd),
      (katLayout, 1, Midfall.Lowering.calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 17]),
      (katLayout, 1, replace (100 + 128)
        (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 17 32))),
      ({ katLayout with proofCptr := 0x84 }, 1, cd),
      -- an in-range frame that is not a point of the toy group: byte 100+127 (low y byte)
      (katLayout, 1, replace (100 + 127) [9]) ]
  cases.all (fun t => rawThenLift t.1 t.2.1 t.2.2 == decodeCode t.1 t.2.1 t.2.2) &&
  -- the good case really decodes, and the last case is raw-ok / decode-none
  (decodeCode katLayout 1 cd).isSome &&
  (rawDecode (p := 17) katLayout 1 (replace (100 + 127) [9])).isSome &&
  (decodeCode katLayout 1 (replace (100 + 127) [9])).isNone

#eval rawDecodeAgreesKats_ok   -- expect true

/-- EVIDENCE FOR THE NEW DIVERGENCE (fault table, row "x = 0"). `constructIntermediateSets`
    deduplicates opening points BY VALUE (Kzg/Utils.lean:137; Rust: a HashMap keyed on the point,
    kzg/utils.rs:46-52). With rotations {0, 1} and omega = 2 over Fr 17:
      * x = 3, a commitment opened at both rotations plus two single openings: THREE point sets;
      * x = 0, the same shape: `Error.opening` (DuplicatedQuery);
      * x = 3, only single openings at the two rotations: TWO point sets;
      * x = 0, the same shape: ONE point set - the read schedule shrinks by one q_eval. -/
def xZeroCollapseKats_ok : Bool :=
  let run (x : Fr 17) (multi : Bool) :=
    let p0 := x
    let p1 := x * 2
    constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRef
      ((if multi then #[vq17 p0 5 1, vq17 p1 5 2] else #[]) ++ #[vq17 p0 7 3, vq17 p1 9 4])
  (match run 3 true with | .ok (_, ps) => ps.size == 3 | .error _ => false) &&
  (match run 0 true with | .error (Fault.error Error.opening) => true | _ => false) &&
  (match run 3 false with | .ok (_, ps) => ps.size == 2 | .error _ => false) &&
  (match run 0 false with | .ok (_, ps) => ps.size == 1 | .error _ => false)

#eval xZeroCollapseKats_ok   -- expect true

end Evidence

/-! ### The leaf register of this file (what the glue rests on) -/

#cone_sorries Midfall.LoweringV2.V3.decodeCalldata_eq_raw
#cone_sorries Midfall.LoweringV2.V3.decodeCalldata_isSome_iff
#cone_sorries Midfall.LoweringV2.V3.linearize_eq_full
#cone_sorries Midfall.LoweringV2.V3.leanAccepts_of_final
#cone_sorries Midfall.LoweringV2.V3.slices_seq_sim
#cone_sorries Midfall.LoweringV2.V3.slices_seq_prog
#cone_sorries Midfall.LoweringV2.V3.tr_exit_any
#cone_sorries Midfall.LoweringV2.V3.tr_blockSim
#cone_sorries Midfall.LoweringV2.V3.tr_blockProgS
#cone_sorries Midfall.LoweringV2.V3.fp_blockSim_of_blockSound
#cone_sorries Midfall.LoweringV2.V3.soundness_of_sims
#cone_sorries Midfall.LoweringV2.V3.two_outcomes_of_exitShape
#cone_sorries Midfall.LoweringV2.V3.completeness_of_progs
#cone_sorries Midfall.LoweringV2.V3.lowering_equivalence_of_stages
#cone_sorries Midfall.LoweringV2.lowering_equivalence_of_blocks


/-- NON-VACUITY OF THE COMPOSED CONTRACT (falsifier for `slices_seq_sim`): the empty program
    cannot satisfy it. A program that falls off the end is refuted, because `FinSim` demands a
    halt. (The v1 defect this guards against: a contract a stuck or empty program satisfies.) -/
theorem finSim_refutes_empty (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (funs : FunEnv (Bridge.Dialect c g)) :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) funs []
        (fun _ _ => True) (fun _ _ V' st' o => FinSim R H cd V' st' o) := by
  intro h
  have hfin := h [] EVM.EvmState.init trivial [] _ .normal Step.seqNil
  rcases hfin with ⟨ho, _⟩ | ⟨ho, _⟩ <;> cases ho

#cone_sorries Midfall.LoweringV2.V3.finSim_refutes_empty
#print axioms Midfall.LoweringV2.V3.slices_seq_sim
#print axioms Midfall.LoweringV2.V3.tr_exit_any
#print axioms Midfall.LoweringV2.V3.tr_blockSim

end Midfall.LoweringV2.V3

-- |
-- Midfall.Halo2.Exec.Kzg.MultiOpen
--
-- The KZG multi-opening verifier (rust: proofs/src/poly/kzg/mod.rs:321-574,
-- KZGCommitmentScheme::multi_prepare). Reads the proof stream, squeezes x1..x4,
-- builds the q_i combinations and their evaluation vector, and returns the
-- DualMSM whose pairing check is the whole of KZG verification.
--
-- This is the function the S3 binding theorem is about, so the order of reads
-- and squeezes is not an implementation detail: it is the Fiat-Shamir schedule.
--
-- Errors: the Rust returns poly::Error (SamplingError on a failed read,
-- VerificationError elsewhere) and the only caller collapses all of it to
-- plonk Error::Opening (plonk/verifier.rs:651). The port keeps the richer
-- Fault from the transcript instead of flattening it here, because Exec does not
-- own poly::Error; the collapse happens where the Rust does it.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Common.Codec
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Transcript
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Kzg.Utils

namespace Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- The commitment comparison the port uses where the Rust uses pointer
    equality (docs/REVIEW.md R-7): value equality, with the labels ignored
    exactly as the Rust PartialEq does. Lengths are compared explicitly because
    Vec equality in Rust is length-plus-elements, while List.zip truncates. -/
def kzgCommitBeq : CommitmentReference (Fr p) G₁ → CommitmentReference (Fr p) G₁ → Bool
  | .onePiece x, .onePiece y => decideBool (P.decEqG₁ x y)
  | .linear p1 s1 _, .linear p2 s2 _ =>
      p1.size == p2.size && s1.size == s2.size &&
      (List.zip p1.toList p2.toList).all (fun (x, y) => decideBool (P.decEqG₁ x y)) &&
      (List.zip s1.toList s2.toList).all (fun (x, y) => x == y)
  | _, _ => false

/-- The rayon thread count eval_polynomial would see. The two branches of
    evalPolynomial are provably equal (Exec/Arith pins that with a KAT), so the
    value is unobservable; 1 keeps the chunked branch trivial. -/
def numThreads : Nat := 1


namespace MultiPrepare

/-- rust: kzg/mod.rs:336-355 (the dummy-query pass). The eval is read BEFORE
    queries[idx] is indexed, exactly as in the Rust, because the read advances
    the transcript and any divergence in that order would shift every later
    challenge. -/
def addDummies {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (queries : Array (VerifierQuery (Fr p) G₁)) :
    TranscriptM (Array (VerifierQuery (Fr p) G₁)) := do
  let pairs := queries.toList.map (fun q => (q.commitment, q.point))
  let eqC := kzgCommitBeq (G₂ := G₂) (Gₜ := Gₜ)
  let dummies ← StateT.lift (computeDummyQueries (P := Fr p) eqC pairs)
  dummies.foldlM (init := queries) fun qs (idx, point) => do
    let eval ← tmRead hashableFr
    match qs[idx]? with
    | none => throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349")
    | some o =>
      let q : VerifierQuery (Fr p) G₁ :=
        { point := point, commitmentLabel := o.commitmentLabel,
          commitment := o.commitment, eval := eval }
      pure (qs.push q)

/-- Ascending insertion sort of indices by a Nat × Nat key: the Rust
    order.sort_by_key(|&i| (point_sets[i].len(), i)). The key is a total order
    because i is distinct, so Rust's stable sort and this agree. -/
def sortById (key : Nat → Nat × Nat) : List Nat → List Nat
  | [] => []
  | i :: rest => insert i (sortById key rest)
where
  insert : Nat → List Nat → List Nat
    | i, [] => [i]
    | i, j :: rest => if key i ≤ key j then i :: j :: rest else j :: insert i rest

/-- rust: kzg/mod.rs:373-424. Returns the reordered (q_coms, q_eval_sets,
    point_sets). The assert at :391 is a real panic site. -/
def buildQ {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (feat : Features) (fc : FieldConsts (Fr p)) (x1 : Fr p)
    (commitmentMap : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p))) :
    Except Fault (Array (MSMKZG (Fr p) G₁) ×
      Array (Array (Fr p)) × Array (Array (Fr p))) := do
  let step (st : Array (Array (MSMKZG (Fr p) G₁)) ×
        Array (Array (Array (Fr p))))
      (cd : CD (Fr p) G₁) :
      Except Fault (Array (Array (MSMKZG (Fr p) G₁)) × Array (Array (Array (Fr p)))) := do
    let terms ← cd.commitment.asTerms
    -- kzg/mod.rs:379-382: a Linear commitment carries its own per-term labels;
    -- anything else repeats the query label once per term. The zip at :383 then
    -- truncates to the shorter of terms and labels (rule R3), so a Linear
    -- commitment whose label vector is shorter than its point vector silently
    -- loses trailing terms - and asTerms only checks points against scalars.
    let termLabels := match cd.commitment with
      | .linear _ _ labels => labels
      | _ => arrayReplicate terms.size cd.commitmentLabel
    let msm := (List.zip terms.toList termLabels.toList).foldl
      (init := MSMKZG.init) fun m (t, l) => MSMKZG.appendTerm m t.1 t.2 l
    let qComs := arraySetD st.1 cd.setIndex ((st.1.getD cd.setIndex #[]).push msm)
    let qEvalSets :=
      arraySetD st.2 cd.setIndex ((st.2.getD cd.setIndex #[]).push cd.evals)
    pure (qComs, qEvalSets)
  let (qComs, qEvalSets) ← commitmentMap.toList.foldlM
    (init := (arrayReplicate pointSets.size (#[] : Array (MSMKZG (Fr p) G₁)),
               arrayReplicate pointSets.size (#[] : Array (Array (Fr p)))))
    step
  let nbX1Powers := (qComs.toList.map (fun v => v.size)).foldl (init := 0) max
  unless nbX1Powers ≥ (qEvalSets.toList.map (fun v => v.size)).foldl (init := 0) max do
    throw (Fault.panic "proofs/src/poly/kzg/mod.rs:391")
  -- kzg/mod.rs:393-397, rule R8
  let ps := if feat.truncatedChallenges then truncatedPowers fc.numBits x1 nbX1Powers
            else powers x1 nbX1Powers
  let powersX1 := ps.toArray
  let qComs' := qComs.map (fun msms => msmInnerProduct msms powersX1)
  let qEvalSets' ← qEvalSets.toList.mapM (fun evs => evalsInnerProduct evs ps)
  -- kzg/mod.rs:409-424: sort the point sets by ascending cardinality so the
  -- first set is the one opened only at x. Not needed by the proving system,
  -- but the in-circuit verifier relies on it, so the order is load-bearing.
  let order := sortById (fun i => ((pointSets.getD i #[]).size, i))
    (List.range pointSets.size)
  let perm {α : Type} (xs : Array α) : Array α :=
    (order.filterMap (fun i => xs[i]?)).toArray
  pure (perm qComs', perm qEvalSets'.toArray, perm pointSets)

/-- rust: kzg/mod.rs:471-482. Note den.invert().unwrap() at :479: if x3
    coincides with any point of a set the reference verifier PANICS, i.e. the
    process aborts rather than rejecting the proof. x3 is squeezed from the
    transcript so a prover cannot choose it, but this is a real availability
    hazard and the port keeps it as Fault.panic rather than papering over it. -/
def fEval {p : ℕ} [Fact (Nat.Prime p)]
    (pointSets : Array (Array (Fr p))) (qEvalSets : Array (Array (Fr p)))
    (qEvalsOnX3 : List (Fr p)) (x2 x3 : Fr p) : Except Fault (Fr p) :=
  (((pointSets.toList.zip qEvalSets.toList).zip qEvalsOnX3).reverse.foldlM
    (init := 0) fun acc ((points, evals), proofEval) => do
      let rPoly ← lagrangeInterpolate points evals
      let rEval ← evalPolynomial numThreads rPoly x3
      let den := points.foldl (init := 1) fun a p => a * (x3 - p)
      match invert den with
      | none => throw (Fault.panic "proofs/src/poly/kzg/mod.rs:479")
      | some denInv => pure (acc * x2 + (proofEval - rEval) * denInv))

def collapseSkip1 {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] :
    List (MSMKZG (Fr p) G₁) → List (MSMKZG (Fr p) G₁)
  | [] => []
  | x :: xs => x :: xs.map MSMKZG.collapse

/-- rust: kzg/mod.rs:488-508. The collapse of every MSM but the first is gated
    on truncated-challenges (rule R8), and BASELINE.md records that feature as
    ON in production, so the collapse IS applied for the deployed verifier.
    Skipping the first is because its x4 power is 1. -/
def finalCom {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (feat : Features) (fc : FieldConsts (Fr p))
    (qComs : Array (MSMKZG (Fr p) G₁)) (fCom : G₁) (x4 : Fr p) :
    Except Fault (MSMKZG (Fr p) G₁) := do
  let size := qComs.size + 1
  let fComAsMsm := MSMKZG.appendTerm MSMKZG.init 1 fCom .noLabel
  let coms := (if feat.truncatedChallenges then collapseSkip1 qComs.toList
               else qComs.toList) ++ [fComAsMsm]
  let ps := if feat.truncatedChallenges then truncatedPowers fc.numBits x4 size
            else powers x4 size
  pure (msmInnerProduct coms.toArray ps.toArray)

/-- rust: kzg/mod.rs:510-516. A FRESH x4 power stream, not the one final_com
    consumed, and the length is q_evals_on_x3.len() + 1 rather than size. -/
def vCalc {p : ℕ} [Fact (Nat.Prime p)]
    (feat : Features) (fc : FieldConsts (Fr p)) (qEvalsOnX3 : List (Fr p))
    (fEval : Fr p) (x4 : Fr p) : Except Fault (Fr p) := do
  let evals := (qEvalsOnX3 ++ [fEval]).toArray
  let ps := if feat.truncatedChallenges then truncatedPowers fc.numBits x4 evals.size
            else powers x4 evals.size
  innerProduct evals ps

end MultiPrepare

/-- rust: proofs/src/poly/kzg/mod.rs:321-574 (multi_prepare). The whole
    multi-open verification: read the proof stream, squeeze x1..x4 in exactly
    this order, build the q_i combinations, and return the DualMSM whose
    pairing check IS the KZG check. -/
def multiPrepare (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) := do
  -- kzg/mod.rs:331-359. Rule R8: the cargo feature gates whether the code
  -- exists, and fewer_point_sets_enabled() is a runtime thread-local switch
  -- inside it, so both are parameters here. BASELINE.md records the production
  -- features as evm,truncated-challenges,in-circuit-fewer-point-sets - plain
  -- fewer-point-sets is NOT among them, so feat.outerFewerPointSets is false
  -- for the deployed profile and this whole branch is dead there.
  let queries ←
    if feat.outerFewerPointSets && fewerPointSetsRuntime then
      MultiPrepare.addDummies (G₂ := G₂) (Gₜ := Gₜ) g1 queries
    else pure queries
  -- kzg/mod.rs:363-364
  let x1 ← tmSqueezeChallenge
  let x2 ← tmSqueezeChallenge
  -- kzg/mod.rs:371
  let (commitmentMap, pointSets) ← StateT.lift
    (constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (G₂ := G₂) (Gₜ := Gₜ)) queries)
  -- kzg/mod.rs:373-424
  let (qComs, qEvalSets, pointSets) ← StateT.lift
    (MultiPrepare.buildQ (G₂ := G₂) (Gₜ := Gₜ) feat fc x1 commitmentMap pointSets)
  -- kzg/mod.rs:447
  let fCom ← tmRead (hashableG1 g1)
  -- kzg/mod.rs:455-457
  let x3raw ← tmSqueezeChallenge
  let x3 := if feat.truncatedChallenges then truncate fc.numBits x3raw else x3raw
  -- kzg/mod.rs:461-467
  let qEvalsOnX3 ← (List.range qEvalSets.size).mapM (fun _ => tmRead hashableFr)
  -- kzg/mod.rs:471-482
  let fEval ← StateT.lift (MultiPrepare.fEval pointSets qEvalSets qEvalsOnX3 x2 x3)
  -- kzg/mod.rs:484
  let x4 ← tmSqueezeChallenge
  -- kzg/mod.rs:488-508
  let finalCom ← StateT.lift (MultiPrepare.finalCom feat fc qComs fCom x4)
  -- kzg/mod.rs:510-516
  let v ← StateT.lift (MultiPrepare.vCalc feat fc qEvalsOnX3 fEval x4)
  -- kzg/mod.rs:527-533
  let pi ← tmRead (hashableG1 g1)
  let piMsm := MSMKZG.appendTerm MSMKZG.init 1 pi (.custom "π")
  -- kzg/mod.rs:544-551: scalars [x3, v] over bases [pi, -generator]. The
  -- generator is AdmissiblePairing.g₁ (D-P1); the Rust writes -E::G1::generator().
  let scaledPi : MSMKZG (Fr p) G₁ :=
    { scalars := #[x3, v], bases := #[pi, P.g₁⁻¹],
      labels := #[.custom "π", .custom "-G"] }
  -- kzg/mod.rs:553-558: (π, C − vG + zπ). The Rust calls add_msm on
  -- msm_accumulator.right, which mutates in place and returns nothing; a port
  -- that computed addMsm and discarded the result would silently drop the whole
  -- scaled_pi term and accept every proof. The value is threaded here.
  let acc : DualMSM (Fr p) G₁ G₂ Gₜ := { left := piMsm, right := finalCom }
  pure { acc with right := acc.right.addMsm scaledPi }

end Midfall.Halo2

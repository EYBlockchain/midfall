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

/-- rust: kzg/mod.rs:331-424, the output of the FIRST phase of multi_prepare: the two
    x-challenges and the q_i combinations they determine. It is a record so that P-SE
    can name x1 and x2 from OUTSIDE the do-block (decision D6); until this split they
    were `let` binders with no external name at all. -/
structure PhaseA (F G : Type) where
  x1 : F
  x2 : F
  qComs : Array (MSMKZG F G)
  qEvalSets : Array (Array F)
  pointSets : Array (Array F)

/-- rust: kzg/mod.rs:447-482, the SECOND phase's output: the `f_com` read, the raw
    and the truncated x3, the `q_evals_on_x3` block and `f_eval`. Both x3raw and x3 are
    kept: the truncation is a feature branch INSIDE the squeeze sequence (hazard 2 of
    the D6 brief, and R-22/D-P14 make it the deployed profile), and a snapshot that
    recorded only the truncated value could not express that the branch ran at all. -/
structure PhaseB (F G : Type) where
  fCom : G
  x3raw : F
  x3 : F
  qEvalsOnX3 : List F
  fEval : F

/-- rust: kzg/mod.rs:484-558, the THIRD phase: x4, the final commitment, v, the `pi`
    read, and the DualMSM they build. `dual` is exactly what multi_prepare returns, so
    the composition is a projection and not a recomputation. -/
structure PhaseC (F G₁ G₂ Gₜ : Type) where
  x4 : F
  finalCom : MSMKZG F G₁
  v : F
  pi : G₁
  dual : DualMSM F G₁ G₂ Gₜ

end MultiPrepare

/-- rust: kzg/mod.rs:331-424. The first phase: the optional dummy-query pass, the x1
    and x2 squeezes, the intermediate sets and the q_i combinations. The body is the
    first third of the original monolithic multiPrepare, moved VERBATIM; the only
    textual change is that its results leave in a record instead of staying `let`
    binders inside the block. -/
def phaseA {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    TranscriptM (MultiPrepare.PhaseA (Fr p) G₁) := do
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
  pure { x1 := x1, x2 := x2, qComs := qComs, qEvalSets := qEvalSets, pointSets := pointSets }

/-- rust: kzg/mod.rs:447-482. The second phase: the `f_com` read, the x3 squeeze with
    its truncation branch, the `q_evals_on_x3` block and `f_eval`. The truncation stays
    exactly where the Rust puts it - after the `f_com` read, before the
    `q_evals_on_x3` reads - because that is what the digest chain sees.

    Note what this function does NOT need: no Group, no module, no pairing. Every
    value it produces is an `Fr p` or a codec read, which is what lets Exec pin the
    x2/x3 consumption with a pairing-free KAT. -/
def phaseB {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) :
    TranscriptM (MultiPrepare.PhaseB (Fr p) G₁) := do
  -- kzg/mod.rs:447
  let fCom ← tmRead (hashableG1 g1)
  -- kzg/mod.rs:455-457
  let x3raw ← tmSqueezeChallenge
  let x3 := if feat.truncatedChallenges then truncate fc.numBits x3raw else x3raw
  -- kzg/mod.rs:461-467
  let qEvalsOnX3 ← (List.range a.qEvalSets.size).mapM (fun _ => tmRead hashableFr)
  -- kzg/mod.rs:471-482
  let fEval ← StateT.lift (MultiPrepare.fEval a.pointSets a.qEvalSets qEvalsOnX3 a.x2 x3)
  pure { fCom := fCom, x3raw := x3raw, x3 := x3, qEvalsOnX3 := qEvalsOnX3, fEval := fEval }

/-- rust: kzg/mod.rs:484-558. The third phase: the x4 squeeze, the final commitment,
    v, the `pi` read and the DualMSM they build. -/
def phaseC {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁)
    (b : MultiPrepare.PhaseB (Fr p) G₁) :
    TranscriptM (MultiPrepare.PhaseC (Fr p) G₁ G₂ Gₜ) := do
  -- kzg/mod.rs:484
  let x4 ← tmSqueezeChallenge
  -- kzg/mod.rs:488-508
  let finalCom ← StateT.lift (MultiPrepare.finalCom feat fc a.qComs b.fCom x4)
  -- kzg/mod.rs:510-516
  let v ← StateT.lift (MultiPrepare.vCalc feat fc b.qEvalsOnX3 b.fEval x4)
  -- kzg/mod.rs:527-533
  let pi ← tmRead (hashableG1 g1)
  let piMsm := MSMKZG.appendTerm MSMKZG.init 1 pi (.custom "π")
  -- kzg/mod.rs:544-551: scalars [x3, v] over bases [pi, -generator]. The
  -- generator is AdmissiblePairing.g₁ (D-P1); the Rust writes -E::G1::generator().
  let scaledPi : MSMKZG (Fr p) G₁ :=
    { scalars := #[b.x3, v], bases := #[pi, P.g₁⁻¹],
      labels := #[.custom "π", .custom "-G"] }
  -- kzg/mod.rs:553-558: (π, C − vG + zπ). The Rust calls add_msm on
  -- msm_accumulator.right, which mutates in place and returns nothing; a port
  -- that computed addMsm and discarded the result would silently drop the whole
  -- scaled_pi term and accept every proof. The value is threaded here.
  let acc : DualMSM (Fr p) G₁ G₂ Gₜ := { left := piMsm, right := finalCom }
  pure { x4 := x4, finalCom := finalCom, v := v, pi := pi, dual := { acc with right := acc.right.addMsm scaledPi } }

/-- rust: proofs/src/poly/kzg/mod.rs:321-574 (multi_prepare). The whole
    multi-open verification: read the proof stream, squeeze x1..x4 in exactly
    this order, build the q_i combinations, and return the DualMSM whose
    pairing check IS the KZG check.

    This is now the composition of the three phases above - phaseA, phaseB, phaseC -
    and nothing else. That is the whole point of the split: the statement sequence is
    the original one, cut at the kzg/mod.rs:447 and :484 boundaries, so the old
    function and this one are the same term rather than two terms that must be proved
    equal (D6, hazard 1). -/
def multiPrepare (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) := do
  -- The composition IS the old body: phaseA, then phaseB, then phaseC, with the
  -- DualMSM projected out of the last record. Nothing is recomputed and nothing is
  -- reordered; the three bodies above are the original statement sequence cut at the
  -- kzg/mod.rs:447 and kzg/mod.rs:484 boundaries.
  let a ← phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries
  let b ← phaseB g1 fc feat a
  let c ← phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b
  pure c.dual
/-! ## Known-answer checks

    Executable booleans in the style of Exec/Arith and Exec/Domain, over Fr 17 and
    Fr 1009 with no curve needed: every check below runs a PAIRING-FREE part of this
    module. They exist because the D6 safety gate ("every existing
    '#eval ... -- expect' token in Verifier.lean, MultiOpen.lean and Native.lean stays
    identical") had nothing to bite on here - this file had zero tokens - while the
    refactor moves four transcript squeezes through it.

    WHAT IS PINNED HERE, AND WHAT IS NOT. The squeeze ORDER cannot be pinned from
    inside this file: an executable order gate has to instantiate multiPrepare at a
    concrete AdmissiblePairing, the only one in the tree is
    Midfall/Instances/ExponentModel.lean (R-28), and that file imports Exec.Pcs, which
    imports this one - so the dependency can only run Instances -> Exec, never back
    (D-P17, and the "Instances/ import confinement" gate in scripts/checks.sh). The
    order gate is therefore Midfall/Instances/ChallengeStream.lean. What follows is
    the half that is visible without a curve: how x2 and x3 are consumed, the invert
    panic the doc comment above names, the point-set permutation, and the
    truncatedChallenges feature branch on the x4 power streams. -/

section MultiOpenKats

local instance fact17mo : Fact (Nat.Prime 17) := by decide

/-- Fr 1009's field constants, for the truncation gate only. The prime is deliberately
    larger than 256. truncate keeps divCeil (divCeil numBits 8) 2 bytes, which at
    numBits = 10 is ONE byte, so over Fr 17 - where every value is below 256 -
    truncation is the IDENTITY and the whole truncatedChallenges branch is
    unobservable. That is a finding in its own right: a truncation gate written at
    Fr 17 cannot fail, which is why moVCalcTrunc_ok runs at 1009 and why the Fr 17
    clause of it is pinned as an EQUALITY (the branch is a no-op there) rather than as
    a difference.

    P-ENV REPAIRED THE THREE DEAD FIELDS HERE, and `numBits` with them. Nothing in this
    module reads `s`, `rootOfUnity` or `zeta` - the only `fc.` projections in the file are
    `fc.numBits` at :131, :181, :191 and :281 - which is precisely why they were free to
    stay wrong: a field nothing reads cannot fail. But a `FieldConsts` that declares
    `s := 4` while its root has order 168 and its zeta has order 504 is a FALSE CLAIM
    about a field, and P-4a2 proved it (`TwoAdicity.fc1009Placeholder_root_fails`,
    `..._zeta_fails`). The values are now the ones `Midfall/Assumptions/TwoAdicity.lean`
    exhibits and proves well formed IN THE KERNEL (`fc1009Real_isWellFormed`): 62 has
    order exactly 16 = 2^4 in Fr 1009 and 374 has order exactly 3. `numBits` moves from
    the placeholder 5 to 10, the true bit width of 1009, and that changes nothing here:
    divCeil (divCeil 5 8) 2 = 1 = divCeil (divCeil 10 8) 2, so the truncation width is
    the same one byte and every pinned value in this section is UNCHANGED - the
    non-circularity evidence is that arithmetic plus the fact that no gate value moved,
    not a re-pinned expectation. `moFc1009WellFormed_ok` re-checks the five literal
    conditions as a computation, and reddens on the placeholder values. -/
def fc1009 : FieldConsts (Fr 1009) :=
  { numBits := 10, s := 4, rootOfUnity := 62, zeta := 374 }

set_option maxRecDepth 100000 in
local instance fact1009mo : Fact (Nat.Prime 1009) := by decide

/-- THE CONSTANTS ARE WELL FORMED, as a computation rather than as a paragraph: `62` has
    order exactly 2^4 (16th power 1, 8th power NOT 1), `374` has order exactly 3 (cube 1,
    not itself 1), and `s < numBits`. Those are the five checks `FieldConsts.IsWellFormed`
    is made of, and they are the same five `TwoAdicity.fc1009Real_isWellFormed` discharges
    by `decide` - so this is the VM twin of a kernel proof, not a second assertion of it.
    The last two lines are the falsification half: the PLACEHOLDER values this replaced
    (root 3, zeta 2) fail both halves, and the truncation width the gates above depend on
    is the same one byte at numBits 5 and at numBits 10. -/
def moFc1009WellFormed_ok : Bool :=
  ((62 : Fr 1009) ^ 2 ^ 4 == 1) && ((62 : Fr 1009) ^ 2 ^ 3 != 1) &&
    ((374 : Fr 1009) ^ 3 == 1) && ((374 : Fr 1009) != 1) &&
    (fc1009.s < fc1009.numBits) && (fc1009.s == 4) && (fc1009.numBits == 10) &&
    (fc1009.rootOfUnity == 62) && (fc1009.zeta == 374) &&
    (divCeil (divCeil fc1009.numBits 8) 2 == 1) &&
    (divCeil (divCeil 5 8) 2 == divCeil (divCeil 10 8) 2) &&
    ((3 : Fr 1009) ^ 2 ^ 4 != 1) && ((2 : Fr 1009) ^ 3 != 1)

#eval moFc1009WellFormed_ok             -- expect true

/-- The ascending-cardinality permutation buildQ applies to the point sets
    (kzg/mod.rs:409-424), which the doc comment there calls load-bearing for the
    in-circuit verifier. Keys (3,0) (1,1) (2,2) (1,3) sort to 1 3 2 0: ties on the
    first component break on the index, which is the only reason the key carries i. -/
def moSortById_ok : Bool :=
  MultiPrepare.sortById (fun i => (#[3, 1, 2, 1][i]!, i)) [0, 1, 2, 3]
    == [1, 3, 2, 0]

/-- fEval at ONE point set, hand-computed in Fr 17 (kzg/mod.rs:471-482). rPoly is the
    constant 3 through the single point 2, so rEval = 3; den = x3 - 2 = 5 and the
    inverse of 5 in Fr 17 is 7; the fold starts at 0, so the result is
    0 * x2 + (4 - 3) * 7 = 7. Note that x2 does not reach the answer here: with one
    set the single fold step multiplies the ZERO accumulator. That is what makes the
    two-set check below the one that pins x2's position. -/
def moFEvalOne_ok : Bool :=
  match MultiPrepare.fEval (p := 17) (#[#[2]] : Array (Array (Fr 17)))
      (#[#[3]] : Array (Array (Fr 17))) [4] 5 7 with
  | .ok v => ZMod.val v == 7
  | .error _ => false

/-- fEval at TWO point sets: the only shape in which x2 is observable, because the
    second fold step multiplies what the first left behind. The fold runs over the
    REVERSED zip (kzg/mod.rs:472), so set 1 = (points [3], evals [5]) goes first with
    proofEval 7: den = 11 - 3 = 8, its inverse is 15, giving 0 * 5 + (7 - 5) * 15 =
    30 = 13. Then set 0 = (points [2], evals [4]) with proofEval 6: den = 9, its
    inverse is 2, giving 13 * 5 + (6 - 4) * 2 = 69 = 1. Changing x2 from 5 to 6 moves
    the answer to 14, so x2 is load-bearing at exactly the position the Rust puts it. -/
def moFEvalTwo_ok : Bool :=
  (match MultiPrepare.fEval (p := 17) (#[#[2], #[3]] : Array (Array (Fr 17)))
      (#[#[4], #[5]] : Array (Array (Fr 17))) [6, 7] 5 11 with
   | .ok v => ZMod.val v == 1
   | .error _ => false) &&
  (match MultiPrepare.fEval (p := 17) (#[#[2], #[3]] : Array (Array (Fr 17)))
      (#[#[4], #[5]] : Array (Array (Fr 17))) [6, 7] 6 11 with
   | .ok v => ZMod.val v == 14
   | .error _ => false)

/-- The .rev() on the fold input (kzg/mod.rs:472) is a real order, not a stylistic
    choice: feeding the two q_evals_on_x3 values in the other order gives 13, not 1.
    Pinned next to moFEvalTwo_ok so a mover who dropped the .rev() sees which gate
    broke. -/
def moFEvalReverse_ok : Bool :=
  match MultiPrepare.fEval (p := 17) (#[#[2], #[3]] : Array (Array (Fr 17)))
      (#[#[4], #[5]] : Array (Array (Fr 17))) [7, 6] 5 11 with
  | .ok v => ZMod.val v == 13
  | .error _ => false

/-- The invert().unwrap() panic the doc comment at fEval names (kzg/mod.rs:479): when
    x3 coincides with a point of a set, den is zero and the reference verifier ABORTS
    rather than rejecting. Kept as Fault.panic, and gated, so that a refactor which
    turned it into a silent skip or a different error class is caught. -/
def moFEvalPanic_ok : Bool :=
  match MultiPrepare.fEval (p := 17) (#[#[2]] : Array (Array (Fr 17)))
      (#[#[3]] : Array (Array (Fr 17))) [4] 5 2 with
  | .error (Fault.panic "proofs/src/poly/kzg/mod.rs:479") => true
  | _ => false

/-- The truncatedChallenges branch on the x4 power stream in vCalc (kzg/mod.rs:521).
    At Fr 1009 with numBits = 5 the truncated stream is [1, 232, 92] (744 mod 256 =
    232) and the plain stream is [1, 744, 604], so the two branches give 265 and 988
    for the same inputs: the branch is load-bearing and a refactor that dropped it
    would move the pinned value. The Fr 17 clause records the opposite fact - there
    the two agree at 5, because truncation is the identity below 256 - which is exactly
    why a truncation gate at Fr 17 alone would be a gate that cannot fail. -/
def moVCalcTrunc_ok : Bool :=
  (match MultiPrepare.vCalc (p := 1009) Features.solidity fc1009 [300] 500 744 with
   | .ok v => ZMod.val v == 265
   | .error _ => false) &&
  (match MultiPrepare.vCalc (p := 1009)
      { Features.solidity with truncatedChallenges := false } fc1009 [300] 500 744 with
   | .ok v => ZMod.val v == 988
   | .error _ => false) &&
  (match MultiPrepare.vCalc (p := 17) Features.solidity
      { numBits := 5, s := 4, rootOfUnity := 3, zeta := 2 } [4] 5 7 with
   | .ok v => ZMod.val v == 5
   | .error _ => false)

/-- The power streams themselves, pinned elementwise: truncatedPowers is powers
    mapped through truncate, and at Fr 1009 the two differ in every position after the
    first. -/
def moTruncatedPowers_ok : Bool :=
  (truncatedPowers (p := 1009) 5 744 3).map ZMod.val == [1, 232, 92] &&
  (powers (744 : Fr 1009) 3).map ZMod.val == [1, 744, 604]

end MultiOpenKats

#eval Midfall.Halo2.moSortById_ok          -- expect true
#eval Midfall.Halo2.moFEvalOne_ok          -- expect true
#eval Midfall.Halo2.moFEvalTwo_ok          -- expect true
#eval Midfall.Halo2.moFEvalReverse_ok      -- expect true
#eval Midfall.Halo2.moFEvalPanic_ok        -- expect true
#eval Midfall.Halo2.moVCalcTrunc_ok        -- expect true
#eval Midfall.Halo2.moTruncatedPowers_ok   -- expect true

end Midfall.Halo2

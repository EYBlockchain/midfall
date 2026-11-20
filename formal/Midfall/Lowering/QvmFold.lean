-- |
-- Midfall.Lowering.QvmFold
--
-- P-SE stage 5, file 2 of 2 (docs/plans/P-SE-stage5.md; plan index section P,
-- P-SE-semantic-equivalence.md:2078-2162; design1.md M6-4 and M6-5).
--
-- WHAT THIS FILE IS FOR. The quotient VM evaluates ONE identity at a time; the thing
-- the contract actually produces is a y-batch fold over the whole identity stream,
-- whose result is the linearization commitment the PCS then opens. D-P20 (amended at
-- 514c808) says the fold is portable in three senses - structurally (folds.rs::check,
-- P-10a), as emitted text (P-10b), and as arithmetic (the reference's own test
-- oracles, expected_linearization_artifacts_for_test at T:4288 and the whole-stream
-- executor at T:4325, both ported into FoldCompute.lean). What did NOT exist was a
-- Lean definition of the fold as one function from a plan and a value list to the
-- pair the verifier needs. That is what this file adds, plus the statement that ties
-- it to computeLinearizationCommitment.
--
-- THE FINDING THAT CHANGED WHAT IS DISCHARGEABLE HERE. P-11 reported that
-- IdentityCorrespondence cannot be DISCHARGED for a real plan because
-- quotient_expr_from_expression (QVM:2870) was unported, and section P line 2138
-- still says so. That claim is now FALSE: P-10c ported the whole chain -
-- quotientExprFromExpression (QuotientBlocks.lean:308), DataQuotientExpressionEnv
-- (:340), wordToQuotientExpr / ptrToQuotientMem, quotientExprFromPlonkExpr (:381) -
-- and P-10c also ported quotientIdentityParts (:976), which is the PRODUCER that
-- applies the bridge to every gate polynomial and stamps each identity's target as
-- QuotientTarget.selector (positionOf sortedSimple col) at :998-1000. So the
-- correspondence is no longer an assumption that has to be postulated from nothing:
--   * the BUCKET-TAG half is derivable today, and positionOf_nth? below PROVES the
--     fact the producer needs (sortedSimple[positionOf sortedSimple col]? = some col
--     for col in sortedSimple), i.e. the plan's selector index and the verifier's
--     fixed-column index are inverse readings of the same list;
--   * the VALUE half needs one more thing, and it is not a missing port: it needs the
--     frame valuation, i.e. that the QVM memory ρ_frame reads at each literal pointer
--     is the value partiallyEvaluateIdentities used for that column eval. That is the
--     QuotientReadModel / QuotientNumeratorBlock.yul window layer (P-13, M6-5), and
--     identityCorrespondence_of_bridge_fixed (LoweringV3/QuotientRows.lean) states the
--     derivation with exactly that one named obligation added, and it is PROVED.
-- So: IdentityCorrespondence is now DERIVABLE-MODULO-ONE-LAYER, not unportable. The
-- fold theorem keeps hcorr as a binder (the plan says so and it is right for today),
-- but the hole is no longer "the bridge does not exist".
--
-- D-P20's TWO CLAIMS, and which is statable here.
--   * Claim 2 (per-identity compile correctness over evalQuotientIdentity) is stated
--     in Qvm.lean as qvm_compile_correct_identity.
--   * Claim 1 (per-stream fold agreement over evalQuotientProgramArtifacts vs
--     expectedLinearizationArtifacts) is stated here as qvm_compile_correct_stream,
--     modulo L.qprog. It is statable ONLY under an explicit exclusion: the fold
--     executor walks bytecode, and native markers, the inline prefix and the
--     structured tail contribute no bytecode, so the two artifact records disagree on
--     any plan that has them. The exclusion is a HYPOTHESIS of the theorem
--     (streamIsInterpretedOnly), not a fixture - the gap D-P20 names is recorded, not
--     papered. The second named gap, the segment-evaluator seam, is also stated rather
--     than hidden: the reference's whole-stream executor takes a segment-value closure
--     (FoldCompute's DEVIATION note), and the two candidate closures - the test
--     module's HashMap memory and P-09b's PRNG memory - agree only on literal-only
--     expressions whose pointers the PRNG and the map were made to match.
--     foldClaim1_agreementOnInterpretedStream_ok is that computation, run through
--     P-09b's interpreter rather than the test module's third one.
--
-- HAZARD 1, ANSWERED. The brief asks what this file uses for structural equality of
-- Yul, since D-P13's YulSemantics.SyntaxEq.stmtsBeq does not exist (no declaration
-- anywhere; stage 4 confirmed by grep). Nothing here needs it: the fold is a function
-- of the plan's identity RECORDS and their QVMFr values, and the identity stream is
-- compared through QuotientIdentity.meta_.globalIndex and .target, both of which carry
-- BEq (VmTypes.lean:618, :600). Where a statement needs two Yul texts to agree it
-- quotes the emitter's own output (FoldCompute's directQuotientBlock), never a
-- structural-equality predicate. stmtsBeq is NOT cited.
--
-- SKETCH NAMES FROM SECTION P THAT DO NOT RESOLVE (reported, not invented):
--   * plan.sortedSimple.Sorted (· < ·) - List.Sorted does not resolve in this build
--     surface (Mathlib order theory is not imported by any Midfall module). Stage 2 hit
--     the same wall in Lowering/Accumulator.lean:183-191 and defined a local
--     namesAscending; natsAscending below is the same device at Nat.
--   * st.buckets.modify (fun b => ...) s - List.modify in Lean 4.35 is
--     List.modify : List α → Nat → (α → α) → List α, i.e. index BEFORE function, the
--     opposite of the sketch. foldStep uses the real order.
--   * IdentityCorrespondence's sketch body indexes with (exprs[i]'(by omega)) inside a
--     CONJUNCTION: the two length equalities are conjuncts, not hypotheses in scope, so
--     omega cannot bridge i < ids.length to i < exprs.size and the sketch does not
--     elaborate (measured). The def below keeps the two length conjuncts and uses
--     Option indexing, which is equivalent under them and elaborates.
--   * limbScalars (sketched as a comment, undefined) is defined below from
--     Linearization.lean:80-85.
--   * The sketch's vals[i]'(by omega) in the same body: same fix.
--
-- ORDER (Lean is order-sensitive, plans README standing note 2): qvmFrPow is declared
-- here even though FoldCompute.lean:771 already defines a function of that name in
-- Midfall.Generator.QuotientFoldCompute. The plan asks for it in this file; the two
-- agree, and foldQvmFrPow_agreesWithFoldCompute_ok is the gate that says so rather
-- than a silent duplicate.
--
-- NO Midfall/Instances/ IMPORT (D-P17).

import Midfall.Lowering.Qvm
import Midfall.Lowering.QvmFoldLin
import Midfall.Halo2.Exec.Linearization
import Midfall.Halo2.Exec.VerifyingKey
import Midfall.Generator.Quotient.FoldCompute
import Midfall.Generator.Quotient.QuotientBlocks
namespace Midfall.Lowering

open Midfall Midfall.Generator Midfall.Generator.QuotientBuilder
  Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientBlocks
open Midfall.Generator (QuotientIdentity QuotientProgramItem QuotientProgramPlan
  SelectorFoldPlan QVMFr qvmFrAdd qvmFrMul qvmFrNeg qvmFrModulus)

/-- Strictly ascending Nats, with no duplicates. The local stand-in for the sketch's
    List.Sorted (· < ·), which does not resolve in this build surface (Mathlib order
    theory is imported by no Midfall module). The precedent is
    Lowering/Accumulator.lean:188 namesAscending, defined for the same reason. -/
def natsAscending : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ natsAscending (b :: rest)

/-- The global y-order: inline prefix, items with native markers expanded to the
    identity ranges they stand for, structured tail (QuotientNumeratorBlock.
    yul:198, :1205-1279, :1368; R-16/R-19). The three SKETCH field names in section P
    (nativePermutationIdentities, nativeLookupIdentities, nativeIdentities) all resolve
    against VmTypes.lean:875-886, so this is exactly the sketch. -/
def expandItem (plan : QuotientProgramPlan) : QuotientProgramItem → List QuotientIdentity
  | .identity id => [id]
  | .nativePermutation => plan.nativePermutationIdentities
  | .nativeLookup => plan.nativeLookupIdentities
  | .nativeIdentity i => ((plan.nativeIdentities.drop i).head?).toList

/-- Every identity the y-batch covers, in global order. -/
def globalIdentities (plan : QuotientProgramPlan) : List QuotientIdentity :=
  plan.inlineIdentities ++ plan.items.flatMap (expandItem plan)
    ++ plan.structuredTailIdentities

/-- y^n by repeated multiplication, the fold's own helper (the sketch's qvmFrPow).
    1 % qvmFrModulus rather than 1 so the exponent-0 case is canonical whatever the
    modulus. foldQvmFrPow_agreesWithFoldCompute_ok ties it to the reference's ported
    fq_pow (T:4283-4285, FoldCompute.lean:771), which is the OTHER qvmFrPow in the tree. -/
def qvmFrPow (y : QVMFr) : Nat → QVMFr
  | 0 => 1 % qvmFrModulus
  | n + 1 => qvmFrMul (qvmFrPow y n) y

/-- The fold's state: the main numerator accumulator and one bucket per simple selector,
    indexed by POSITION in plan.sortedSimple (not by fixed-column index - that gap is
    exactly what IdentityCorrespondence carries). -/
structure FoldState where
  qn : QVMFr
  buckets : List QVMFr

/-- FOLD_MAIN (yul:1284-1299): qn := qn·y + v. FOLD_SELECTOR (yul:1303-1341): qn := qn·y
    and bucket[s] := bucket[s]·y^gap (only when gap ≠ 0) + v. The main accumulator is
    advanced on BOTH arms - dropping it on the selector arm is the error the Yul comment
    at :1312-1315 exists to prevent, and foldStep_mainAdvanceIsLoadBearing_ok is the
    gate. NOTE the sketch's argument order for List.modify is wrong for Lean 4.35: the
    real signature is List α → Nat → (α → α) → List α, index before function. -/
def foldStep (y : QVMFr) (sf : SelectorFoldPlan) (st : FoldState)
    (id : QuotientIdentity) (v : QVMFr) : FoldState :=
  match id.target with
  | .main => { st with qn := qvmFrAdd (qvmFrMul st.qn y) v }
  | .selector s =>
      let gap := (sf.gapFor id).getD 0
      { qn := qvmFrMul st.qn y,
        buckets := st.buckets.modify s (fun b =>
          qvmFrAdd (if gap = 0 then b else qvmFrMul b (qvmFrPow y gap)) v) }

/-- The whole-stream fold (the NEW definition D-P20's addendum asks for): per-identity
    values in global order give (QUOTIENT_EVAL = -qn, selector buckets after their
    tails) - the negation is what the Yul stores at QUOTIENT_EVAL_MPTR
    (QuotientNumeratorBlock.yul:1393) and the tails are :1382-1394. -/
def quotientFold (plan : QuotientProgramPlan) (y : QVMFr) (vals : List QVMFr) :
    QVMFr × List QVMFr :=
  let init : FoldState :=
    { qn := 0, buckets := List.replicate plan.sortedSimple.length 0 }
  let st := (List.zip (globalIdentities plan) vals).foldl
    (fun st iv => foldStep y plan.selectorFold st iv.1 iv.2) init
  (qvmFrNeg st.qn,
    List.zipWith (fun b t => qvmFrMul b (qvmFrPow y t)) st.buckets
      plan.selectorFold.tailExponents)

/-- What quotient_program_plan / selector_fold_plan (Q:356, Q:426; the Lean producer is
    FoldCompute.lean:487 selectorFoldPlan) guarantee about gaps and tails. Five facts:
    sortedSimple is strictly ascending; globalIndex is dense in the global order; a
    selector identity's gap is the distance to the PREVIOUS identity in the same bucket;
    there is one tail exponent per bucket; and a bucket's tail exponent is the distance
    from its LAST identity to the end of the stream. Those are exactly what makes the
    sparse gap form equal the naive global-power form - the reference's own exhaustive
    proof of that equality is T:1289-1340, ported as
    sparseFoldMatchesNaiveGlobalPowers_ok. Written with Option indexing where the
    sketch's (ids[k]'hk) subtype form needs a bound that is not in scope there (the same
    defect as IdentityCorrespondence's by omega). -/
def SelectorFoldConsistent (plan : QuotientProgramPlan) : Prop :=
  let ids := globalIdentities plan
  natsAscending plan.sortedSimple ∧
    (∀ i (h : i < ids.length), (ids[i]'h).meta_.globalIndex = i) ∧
    (∀ i (h : i < ids.length) s, (ids[i]'h).target = .selector s →
      s < plan.sortedSimple.length ∧
      (∀ j (hj : j < i),
        (∀ k (hk : k < ids.length), j < k → k < i →
          (ids[k]'hk).target ≠ .selector s) →
          (ids[j]'(Nat.lt_trans hj h)).target ≠ .selector s ∨
            plan.selectorFold.gapFor (ids[i]'h) = some (i - j))) ∧
    plan.selectorFold.tailExponents.length = plan.sortedSimple.length ∧
    (∀ s (_hs : s < plan.sortedSimple.length),
      (∃ x ∈ ids, x.target = .selector s) ∧
      (∀ i (h : i < ids.length), (ids[i]'h).target = .selector s →
        (∀ k (hk : k < ids.length), i < k →
          (ids[k]'hk).target ≠ .selector s) →
          plan.selectorFold.tailExponents[s]? = some (ids.length - 1 - i)))

/-- The bridge between the QVM identity list and the Lean verifier's tagged expression
    array (partiallyEvaluateIdentities' output): same length, same values, and bucket s
    of the fold is the fixed column plan.sortedSimple[s].
    THE SKETCH'S BODY DOES NOT ELABORATE (measured, and reported): the two length
    equalities are conjuncts of the same conjunction, so omega cannot see them when
    discharging i < exprs.size from i < ids.length. Option indexing is used instead,
    which is equivalent under those two conjuncts and does elaborate.
    The sketch's doc comment names quotient_expr_from_expression as the reason this can
    only be assumed. That is stale - the bridge is ported (QuotientBlocks.lean:308) and
    so is the producer that applies it (:976). What is still owed is the frame
    valuation, which identityCorrespondence_of_bridge_fixed turns into four named
    hypotheses with named owners instead of a hypothesis bundle. -/
def IdentityCorrespondence (plan : QuotientProgramPlan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) : Prop :=
  let ids := globalIdentities plan
  exprs.size = ids.length ∧ vals.length = ids.length ∧
    ∀ i (h : i < ids.length),
      (exprs[i]?.map Prod.snd = some (qvmToFr (vals[i]?.getD 0))) ∧
      (match (ids[i]'h).target with
       | .main => exprs[i]?.map Prod.fst = some none
       | .selector s => exprs[i]?.map Prod.fst = some plan.sortedSimple[s]?)

/-- The decidable twin of IdentityCorrespondence, so the correspondence can be DISCHARGED
    on a concrete plan by computation rather than only postulated. The gate
    identityCorrespondence_dischargedOnFixture_ok runs it on a plan whose selector
    indices name real fixed columns and whose values come from the QVM evaluator. -/
def identityCorrespondenceBool (plan : QuotientProgramPlan)
    (exprs : List (Option Nat × FrR)) (vals : List QVMFr) : Bool :=
  let ids := globalIdentities plan
  (exprs.length == ids.length && vals.length == ids.length) &&
    (List.range ids.length).all fun i =>
      match ids[i]?, exprs[i]?, vals[i]? with
      | some id, some e, some v =>
          e.2 == qvmToFr v &&
            (match id.target with
             | .main => e.1 == none
             | .selector s => e.1 == plan.sortedSimple[s]?)
      | _, _, _ => false

/-- The producer's bucket-key function, restated so it can be reasoned about.
    QuotientBlocks.lean:936 positionOf is the port of the Rust's slice::position; it is
    written with a where-go, which computes fine but is awkward to induct on, so this is
    the same function in the equation form the induction needs.
    bucketPositionOf_agreesWithPositionOf_ok gates that the two agree elementwise. -/
def bucketPositionOf : List Nat → Nat → Option Nat
  | [], _ => none
  | y :: rest, a => if y == a then some 0 else (bucketPositionOf rest a).map Nat.succ

/-- The position the bucket-key function names is in range and holds the column. -/
theorem bucketPositionOf_some : ∀ (xs : List Nat) (a : Nat), a ∈ xs →
    ∃ n, bucketPositionOf xs a = some n ∧ n < xs.length ∧ xs[n]? = some a
  | [], _, h => absurd h (by simp)
  | x :: rest, a, h => by
      rcases List.mem_cons.mp h with hx | hrest
      · subst hx
        exact ⟨0, by simp [bucketPositionOf], by simp, rfl⟩
      · by_cases hc : (x == a) = true
        · have hxa : x = a := Iff.mp beq_iff_eq hc
          subst hxa
          exact ⟨0, by simp [bucketPositionOf], by simp, rfl⟩
        · have hpos : bucketPositionOf (x :: rest) a =
              (bucketPositionOf rest a).map Nat.succ := by
            show (if x == a then some 0 else _) = _
            rw [if_neg hc]
          obtain ⟨n, hn, hlt, hget⟩ := bucketPositionOf_some rest a hrest
          have hshift : (x :: rest)[n + 1]? = rest[n]? := by
            cases n <;> cases rest <;> rfl
          exact ⟨n + 1, by rw [hpos, hn]; rfl, by simp [hlt], by rw [hshift]; exact hget⟩

/-- THE PRODUCER'S BUCKET-KEY FACT, PROVED. quotientIdentityParts stamps a gate
    identity's target as QuotientTarget.selector (positionOf sortedSimple col)
    (QuotientBlocks.lean:998-1000, Q:844-850), so the plan's selector index is the
    POSITION of the fixed column in sortedSimple. This says the two readings invert each
    other, which is the third conjunct of IdentityCorrespondence for every identity the
    producer builds. It is the concrete answer to the question this stage was set: the
    TAG half of the correspondence is dischargeable today, by induction, now that the
    bridge and its producer are ported. -/
theorem nth?_bucketPositionOf (xs : List Nat) (a : Nat) (h : a ∈ xs) :
    xs[(bucketPositionOf xs a).getD 0]? = some a := by
  obtain ⟨n, hn, _hlt, hget⟩ := bucketPositionOf_some xs a h
  rw [hn]
  exact hget

-- RETIRED BY ROW.Q (PLAN-V3 card ROW.Q step 1), W13: THE REFUTED STATEMENT IS DELETED, NOT
--    REPAIRED IN PLACE. What used to sit here was
--
--        theorem identityCorrespondence_of_bridge (plan) (exprs) (vals) (rho)
--          (horder) (hvals) (htags) : IdentityCorrespondence plan exprs vals
--
--    and it is FALSE as stated: this file exhibits, at bridgeCounterexamplePlan /
--    bridgeCounterexampleExprs / bridgeCounterexampleVals, an environment in which all three
--    hypotheses hold (718, 'bridgeCounterexample_hypotheses_hold') and the conclusion fails (749,
--    'bridgeCounterexample_conclusion_fails'). The gap is that no hypothesis mentions 'Prod.snd' of
--    'exprs', so the value half of the conclusion is not derivable - the finding recorded in the
--    deleted statement's own docstring, and the reason the repair is a STATEMENT change and not a
--    proof.
--
--    THE CORRECTED STATEMENT, WITH ITS PROOF, IS
--    'Midfall.LoweringV3.QuotientRows.identityCorrespondence_of_bridge_fixed': the same three
--    hypotheses plus 'hsnd', the value-agreement hypothesis
--    'exprs[i]?.map Prod.snd = some (qvmToFr (vals[i]?.getD 0))'. It is PROVED (no sorry), on
--    [propext, Classical.choice, Quot.sound], and it is ported verbatim from the evidence file
--    (GeneratorRows.lean:913), which had already written the repair.
--
--    WHAT THE DELETION DOES NOT CHANGE: the frame-valuation obligation stays. 'hsnd' is exactly the
--    hypothesis the old docstring named as needing 'the Yul window layer - QuotientReadModel's four
--    windows and nine token bases (LoweringPlan.lean:392-420) tied to the verifier's evaluation
--    environment'. Moving a named obligation from the conclusion into a hypothesis is what the
--    repair does; discharging it is ROW.Q.4's card, and 'hvals' above still says who owns it.
--

/-- The verifier-side scalars the linearization MSM opens the quotient limbs with:
    (1 - xn)·sf^i for i < n, the list computeLinearizationCommitment builds at
    Linearization.lean:80-85 (rust: linearization/verifier.rs:63-70). The plan sketches
    this as a comment ('limbScalars n xn sf := the n scalars'); it is defined here so the
    statement below is closed. -/
def limbScalars {F : Type} [Field F] (n : Nat) (xn sf : F) : List F :=
  ((List.range n).foldl (fun (acc : List F × F) _ => (acc.1 ++ [acc.2], acc.2 * sf))
    ([], 1 - xn)).1

/-! ## QLIN: instantiating QFOLD's generic arithmetic at a plan

    QFOLD's header named four remaining steps and said the row was wiring, not ideas. This
    section lands steps (a) and (b) as named lemmas: the abstract stream at a plan, and the
    per-step / whole-fold transport from `foldStep` (QVMFr arithmetic) to `fstep`
    (`FrR` field arithmetic). Everything generic they need is in
    `Midfall.Lowering.QvmFoldLin`, which this file now imports. The row itself is still open:
    steps (c) and (d) - `WellSpaced` on the projected stream at a plan, and the reading of
    `computeLinearizationCommitment`'s success - are not yet wired here. -/

theorem qvmToFr_val (y : FrR) : qvmToFr y.val = y := by
  unfold qvmToFr
  exact (ZMod.natCast_val (R := FrR) y).trans (by rw [ZMod.cast_id])

/-- The fold's own power, read in the field. -/
theorem qvmToFr_pow_of (yv : QVMFr) (y : FrR) (hy : qvmToFr yv = y) :
    ∀ (n : Nat), qvmToFr (qvmFrPow yv n) = y ^ n := by
  intro n
  induction n with
  | zero => show qvmToFr (1 % qvmFrModulus) = y ^ 0; rfl
  | succ n ih =>
      show qvmToFr (qvmFrMul (qvmFrPow yv n) yv) = y ^ (n + 1)
      rw [qvmToFr_mul, ih, hy, pow_succ]

theorem qvmToFr_pow (y : FrR) (n : Nat) : qvmToFr (qvmFrPow y.val n) = y ^ n :=
  qvmToFr_pow_of y.val y (qvmToFr_val y) n

theorem getD_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  induction l with
  | nil => rfl
  | cons a as ih => cases i <;> simp [ih]

theorem sum_mul {E : Type} [Field E] (l : List E) (b : E) :
    l.sum * b = (l.map fun x => x * b).sum := by
  induction l with
  | nil => simp
  | cons a as ih => rw [List.sum_cons, add_mul, ih, List.map_cons, List.sum_cons]

/-- The stream's bucket key at an identity: its own target. -/
def streamKey (id : QuotientIdentity) : Option Nat :=
  match id.target with | .main => (none : Option Nat) | .selector s => some s

/-- The entry the abstract stream carries at a position of the global y-batch. -/
def streamEntry (sf : SelectorFoldPlan) (a : (QuotientIdentity × QVMFr) × Nat) :
    Option Nat × BEntry FrR :=
  (streamKey a.1.1, ⟨a.2, (sf.gapFor a.1.1).getD 0, qvmToFr a.1.2⟩)

/-- (a) The abstract stream at a plan: one entry per position of `globalIdentities`. The bucket
    key is the identity's own target, so `fstep`'s `modify` lands on the same bucket as
    `foldStep`'s; the index is the position (`SelectorFoldConsistent`'s second conjunct
    makes that exact); the gap is the plan's own `gapFor`; and the value is the QVM's value read
    in the field - the half `IdentityCorrespondence` ties to the verifier's tagged array. -/
def linStream (plan : QuotientProgramPlan) (vals : List QVMFr) :
    List (Option Nat × BEntry FrR) :=
  let ids := globalIdentities plan
  List.map (streamEntry plan.selectorFold)
    (List.zip (List.zip ids vals) (List.range' 0 ids.length))

/-- The `val` component of the stream: the tagged list the verifier's grouped walk consumes. -/
def streamPairs (xs : List (Option Nat × BEntry FrR)) : List (Option Nat × FrR) :=
  xs.map fun p => (p.1, p.2.val)

theorem length_linStream (plan : QuotientProgramPlan) (vals : List QVMFr)
    (h : (globalIdentities plan).length ≤ vals.length) :
    (linStream plan vals).length = (globalIdentities plan).length := by
  show List.length (List.map (streamEntry plan.selectorFold)
      (List.zip (List.zip (globalIdentities plan) vals)
        (List.range' 0 (globalIdentities plan).length)))
      = (globalIdentities plan).length
  have h2 : (List.range' 0 (globalIdentities plan).length).length
      = (globalIdentities plan).length := by simp
  have h3 : (List.zip (globalIdentities plan) vals).length
      = (globalIdentities plan).length := by
    rw [List.length_zip, Nat.min_eq_left h]
  simp only [List.length_map, List.length_zip, h2, h3, Nat.min_self]

/-- (b) The QVM fold's state read in the field. -/
def ffState (st : FoldState) : FFold FrR := ⟨qvmToFr st.qn, st.buckets.map qvmToFr⟩

theorem map_modify {α β : Type} (f : α → β) (g : α → α) (h : β → β)
    (c : ∀ a, f (g a) = h (f a)) :
    ∀ (l : List α) (i : Nat), (l.modify i g).map f = (l.map f).modify i h := by
  intro l
  induction l with
  | nil => intro i; simp [List.modify_nil]
  | cons a as ih =>
      intro i
      cases i with
      | zero =>
          show f (g a) :: as.map f = h (f a) :: as.map f
          rw [c]
      | succ u =>
          have h1 : ((a :: as).modify (u + 1) g) = a :: as.modify u g := rfl
          have h2 : ((f a :: as.map f).modify (u + 1) h) = f a :: (as.map f).modify u h := rfl
          simp only [h1, h2, List.map_cons, ih]

/-- (b) The per-step transport: `foldStep` read in the field is `fstep`. This is where
    `qvmToFr_add`, `qvmToFr_mul`, `qvmToFr_pow` and `qvmToFr_val` do their work,
    and it needs no canonicity hypothesis: `foldStep`'s `if gap = 0` arm is `fstep`'s
    `y ^ 0` arm. -/
theorem ffState_foldStep (yv : QVMFr) (sf : SelectorFoldPlan) (st : FoldState)
    (id : QuotientIdentity) (v : QVMFr) (idx gap : Nat)
    (hgap : gap = (sf.gapFor id).getD 0) :
    ffState (foldStep yv sf st id v)
      = fstep (qvmToFr yv) (ffState st) (streamEntry sf ((id, v), idx)) := by
  obtain ⟨m1, m2, m3, target, m4⟩ := id
  dsimp only [streamEntry, streamKey]
  cases target with
  | main =>
      rw [foldStep]
      dsimp only
      simp only [ffState, fstep_none]
      rw [qvmToFr_add, qvmToFr_mul]
  | selector s =>
      rw [foldStep]
      dsimp only
      simp only [ffState, fstep_some, ← hgap]
      have hb : (st.buckets.modify s fun b =>
              qvmFrAdd (if gap = 0 then b else qvmFrMul b (qvmFrPow yv gap)) v).map qvmToFr
            = (st.buckets.map qvmToFr).modify s fun x => x * qvmToFr yv ^ gap + qvmToFr v := by
        refine map_modify qvmToFr
          (fun b => qvmFrAdd (if gap = 0 then b else qvmFrMul b (qvmFrPow yv gap)) v)
          (fun x => x * qvmToFr yv ^ gap + qvmToFr v) ?_ st.buckets s
        intro b
        by_cases hg : gap = 0
        · rw [if_pos hg, qvmToFr_add, hg, pow_zero, mul_one]
        · rw [if_neg hg, qvmToFr_add, qvmToFr_mul, qvmToFr_pow_of yv (qvmToFr yv) rfl]
      rw [hb]
      rw [qvmToFr_mul]

/-- (b), the whole fold: the QVM fold's state read in the field is the field fold over the same
    abstract stream, starting the positions at `o`. -/
theorem ffState_foldl (yv : QVMFr) (sf : SelectorFoldPlan) :
    ∀ (src : List (QuotientIdentity × QVMFr)) (o : Nat) (st : FoldState),
      ffState (List.foldl (fun st a => foldStep yv sf st a.1 a.2) st src)
        = List.foldl (fstep (qvmToFr yv)) (ffState st)
            (List.map (streamEntry sf) (List.zip src (List.range' o src.length))) := by
  intro src
  induction src with
  | nil => intro o st; rfl
  | cons a rest ih =>
      intro o st
      show ffState (List.foldl (fun st x => foldStep yv sf st x.1 x.2)
            (foldStep yv sf st a.1 a.2) rest) = _
      have h1 : ffState (foldStep yv sf st a.1 a.2)
          = fstep (qvmToFr yv) (ffState st) (streamEntry sf ((a, o))) :=
        ffState_foldStep yv sf st a.1 a.2 o ((sf.gapFor a.1).getD 0) rfl
      have h2 := ih (o + 1) (foldStep yv sf st a.1 a.2)
      rw [h1] at h2
      have hzip : List.zip (a :: rest) (List.range' o (rest.length + 1))
          = (a, o) :: List.zip rest (List.range' (o + 1) rest.length) := rfl
      rw [List.length_cons] at *
      rw [hzip, List.map_cons, List.foldl_cons]
      exact h2






/-! ## QLIN2: the position bridge for the abstract stream

    QFOLD's header named four remaining steps; QLIN landed (a) and (b) and named (c) and (d).
    The generic halves of all five are now in QvmFoldLin (stream-indexed linBucket, WellSpaced
    for a projection, the scalar-order pieces, newLinear_ok and the reading of
    computeLinearizationCommitment). What the instantiation still needs, and what this section
    supplies, is the bridge from the stream's getD/nth? to the plan's own identity list: the
    list-index API this toolchain lacks (no List.get?_map, get?_zip or get_range') is proved
    locally here, and nth?_linStream names the entry the stream carries at a position. -/

theorem get?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    (xs.map f)[i]? = (xs[i]?).map f := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases i <;> simp [ih]

theorem get?_zip {α β : Type} (xs : List α) (ys : List β) (i : Nat) (hi : i < xs.length)
    (hj : i < ys.length) : (xs.zip ys)[i]? = some (xs[i]'hi, ys[i]'hj) := by
  induction xs generalizing ys i with
  | nil => exact absurd hi (by simp)
  | cons a as ih =>
      cases ys with
      | nil => exact absurd hj (by simp)
      | cons b bs =>
          cases i with
          | zero => rfl
          | succ u => exact ih bs u (by simpa using hi) (by simpa using hj)

theorem getD_eq_of_get? {α : Type} : ∀ (xs : List α) (i : Nat) (d a : α),
    xs[i]? = some a → xs.getD i d = a := by
  intro xs
  induction xs with
  | nil => intro i d a h; exact absurd h (by simp)
  | cons x rest ih =>
      intro i d a h
      cases i with
      | zero => simpa using h
      | succ u => exact ih u d a (by simpa using h)

theorem get?_range : ∀ (n : Nat), ∀ (o i : Nat), i < n →
    (List.range' o n)[i]? = some (o + i) := by
  intro n
  induction n with
  | zero => intro o i hi; exact absurd hi (by simp)
  | succ n ih =>
      intro o i hi
      cases i with
      | zero => rw [range'_succ]; simp
      | succ u =>
          rw [range'_succ]
          exact (ih (o + 1) u (by omega)).trans (congrArg some (by omega))

/-- The entry the abstract stream carries at a position of the global y-batch: the identity,
    its value, and the position itself. -/
theorem nth?_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    (linStream plan vals)[i]? =
      some (streamEntry plan.selectorFold
        (Prod.mk (Prod.mk ((globalIdentities plan)[i]'hi) ((vals[i]'hi2))) i)) := by
  have hz : i < (List.zip (globalIdentities plan) vals).length := by
    rw [List.length_zip]
    omega
  have hr : i < (List.range' 0 (globalIdentities plan).length).length := by
    simp
    omega
  have h5 : (List.zip (globalIdentities plan) vals)[i]'hz
      = Prod.mk ((globalIdentities plan)[i]'hi) ((vals[i]'hi2)) := by
    simpa using get?_zip (globalIdentities plan) vals i hi hi2
  have h4 : (List.range' 0 (globalIdentities plan).length)[i]'hr = i := by
    have h := get?_range (globalIdentities plan).length 0 i (by simpa using hr)
    simpa using h
  have huf : linStream plan vals = List.map (streamEntry plan.selectorFold)
      (List.zip (List.zip (globalIdentities plan) vals)
        (List.range' 0 (globalIdentities plan).length)) := rfl
  rw [huf, get?_map]
  rw [get?_zip (List.zip (globalIdentities plan) vals)
    (List.range' 0 (globalIdentities plan).length) i hz hr]
  rw [h5, h4]
  rfl



/-! ## QLIN3: the row closes by instantiation

    Everything below is the wiring QLIN2 named: the stream's own position/key/gap facts, the
    two readings of SelectorFoldConsistent's third and fifth conjuncts, the scalar-ORDER fact,
    and the assembly. No new idea and no new hypothesis: the row's own statement is unchanged. -/

/-- The stream entry at a position, as a getD (the getD form is what idxAt/gapAt/hasKey read). -/
theorem getD_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    (linStream plan vals).getD i noPair
      = streamEntry plan.selectorFold
          (Prod.mk (Prod.mk ((globalIdentities plan)[i]'hi) (vals[i]'hi2)) i) :=
  getD_eq_of_get? (linStream plan vals) i noPair _ (nth?_linStream plan vals i hi hi2)

theorem streamKey_eq_some (id : QuotientIdentity) (s : Nat) :
    streamKey id = some s ↔ id.target = QuotientTarget.selector s := by
  obtain ⟨m1, m2, m3, target, m4⟩ := id
  cases target with
  | main =>
      constructor
      · intro h; exact absurd h (by simp [streamKey])
      · intro h; exact absurd h (by simp)
  | selector t =>
      constructor
      · intro h
        have : t = s := Option.some.inj h
        subst this
        rfl
      · intro h
        have : t = s := QuotientTarget.selector.inj h
        subst this
        rfl

/-- (1) The stream carries its own position as its index. -/
theorem idxAt_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    idxAt (linStream plan vals) i = i := by
  show ((linStream plan vals).getD i noPair).2.idx = i
  rw [getD_linStream plan vals i hi hi2]
  rfl

/-- (1) The stream carries the plan's own gap at that position. -/
theorem gapAt_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    gapAt (linStream plan vals) i =
      (plan.selectorFold.gapFor ((globalIdentities plan)[i]'hi)).getD 0 := by
  show ((linStream plan vals).getD i noPair).2.gap = _
  rw [getD_linStream plan vals i hi hi2]
  rfl

/-- (1) The stream carries the QVM's value at that position, read in the field. -/
theorem val_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    ((linStream plan vals).getD i noPair).2.val = qvmToFr (vals[i]'hi2) := by
  show ((linStream plan vals).getD i noPair).2.val = _
  rw [getD_linStream plan vals i hi hi2]
  rfl

/-- (1) The stream's bucket key at a position is the identity's own target. -/
theorem hasKey_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (s i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    hasKey s (linStream plan vals) i ↔
      ((globalIdentities plan)[i]'hi).target = QuotientTarget.selector s := by
  dsimp only [hasKey]
  rw [getD_linStream plan vals i hi hi2]
  exact streamKey_eq_some ((globalIdentities plan)[i]'hi) s

theorem mainKey_linStream (plan : QuotientProgramPlan) (vals : List QVMFr) (i : Nat)
    (hi : i < (globalIdentities plan).length) (hi2 : i < vals.length) :
    ((linStream plan vals).getD i noPair).1 = none ↔
      ((globalIdentities plan)[i]'hi).target = QuotientTarget.main := by
  rw [getD_linStream plan vals i hi hi2]
  obtain ⟨m1, m2, m3, target, m4⟩ := (globalIdentities plan)[i]'hi
  cases target with
  | main => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | selector t =>
      constructor
      · intro h; nomatch h
      · intro h; nomatch h

theorem idLen_exprs (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR))
    (vals : List QVMFr) (hcorr : IdentityCorrespondence plan exprs vals)
    (i : Nat) (h : i < (globalIdentities plan).length) : i < exprs.toList.length := by
  have h1 : exprs.toList.length = (globalIdentities plan).length := by
    show exprs.size = _
    exact hcorr.1
  omega

theorem valsLen (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR))
    (vals : List QVMFr) (hcorr : IdentityCorrespondence plan exprs vals) :
    vals.length = (globalIdentities plan).length := hcorr.2.1

/-- The verifier's tagged array, read at a position: its value half. -/
theorem exprs_getD_snd (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR))
    (vals : List QVMFr) (hcorr : IdentityCorrespondence plan exprs vals)
    (i : Nat) (h : i < (globalIdentities plan).length) :
    (exprs.toList.getD i (none, 0)).2 = qvmToFr (vals.getD i 0) := by
  have hlenE := idLen_exprs plan exprs vals hcorr i h
  have hget : vals[i]? = some (vals.getD i 0) :=
    get?_getD vals i 0 (by rw [valsLen plan exprs vals hcorr]; exact h)
  have h4 := (hcorr.2.2 i h).1
  have h5 : exprs.toList[i]?.map Prod.snd = some (qvmToFr (vals.getD i 0)) := by
    have := h4
    rw [← Array.getElem?_toList] at this
    rw [this, hget]
    simp
  have h6 : exprs.toList[i]? =
      some ((exprs.toList.getD i (none, 0)).1, (exprs.toList.getD i (none, 0)).2) :=
    get?_getD exprs.toList i (none, 0) hlenE
  rw [h6] at h5
  exact Option.some.inj (by simpa using h5)

/-- The verifier's tagged array, read at a position: its tag half, split by target. -/
theorem exprs_getD_fst_main (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR))
    (vals : List QVMFr) (hcorr : IdentityCorrespondence plan exprs vals)
    (i : Nat) (h : i < (globalIdentities plan).length)
    (ht : ((globalIdentities plan)[i]'h).target = QuotientTarget.main)
    (d : Option Nat × FrR) :
    (exprs.toList.getD i d).1 = none := by
  have hlenE := idLen_exprs plan exprs vals hcorr i h
  have h6 : exprs.toList[i]? =
      some ((exprs.toList.getD i d).1, (exprs.toList.getD i d).2) :=
    get?_getD exprs.toList i d hlenE
  have h4 := (hcorr.2.2 i h).2
  rw [ht] at h4
  have h5 : exprs.toList[i]?.map Prod.fst = some (none : Option Nat) := by
    rw [Array.getElem?_toList]
    exact h4
  rw [h6] at h5
  simpa using h5

theorem exprs_getD_fst_sel (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR))
    (vals : List QVMFr) (hcorr : IdentityCorrespondence plan exprs vals)
    (i : Nat) (h : i < (globalIdentities plan).length) (s : Nat)
    (ht : ((globalIdentities plan)[i]'h).target = QuotientTarget.selector s)
    (d : Option Nat × FrR) :
    (exprs.toList.getD i d).1 = plan.sortedSimple[s]? := by
  have hlenE := idLen_exprs plan exprs vals hcorr i h
  have h6 : exprs.toList[i]? =
      some ((exprs.toList.getD i d).1, (exprs.toList.getD i d).2) :=
    get?_getD exprs.toList i d hlenE
  have h4 := (hcorr.2.2 i h).2
  rw [ht] at h4
  have h5 : exprs.toList[i]?.map Prod.fst = some plan.sortedSimple[s]? := by
    rw [Array.getElem?_toList]
    exact h4
  rw [h6] at h5
  simpa using h5


/-- Strict ascendingness bounds every entry below the head. -/
theorem natAsc_head_le : ∀ (xs : List Nat) (h : natsAscending xs) (x : Nat), x ∈ xs →
    xs.getD 0 0 ≤ x := by
  intro xs
  induction xs with
  | nil => intro _ x hx; exact absurd hx (by simp)
  | cons a as ih =>
      intro h x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_refl x
      · have h1 : a ≤ as.getD 0 0 := by
          cases as with
          | nil => exact absurd hx (by simp)
          | cons b rest => exact Nat.le_of_lt h.1
        have has : natsAscending as := by
          cases as with
          | nil => exact absurd hx (by simp)
          | cons b rest => exact h.2
        exact Nat.le_trans h1 (ih has x hx)

theorem getD_eq_getD {α : Type} : ∀ (xs : List α) (i : Nat) (d d' : α), i < xs.length →
    xs.getD i d = xs.getD i d' := by
  intro xs
  induction xs with
  | nil => intro i d d' h; exact absurd h (by simp)
  | cons a as ih =>
      intro i d d' hi
      cases i with
      | zero => rfl
      | succ u => exact ih u d d' (by simpa using hi)

theorem natAsc_nodup : ∀ (xs : List Nat), natsAscending xs → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; exact List.nodup_nil
  | cons a as ih =>
      intro h
      refine List.Nodup.cons ?_ ?_
      · cases as with
        | nil => intro hx; exact absurd hx (by simp)
        | cons b rest =>
            intro hx
            have hle : b ≤ a := natAsc_head_le (b :: rest) h.2 a hx
            have h1 : a < b := h.1
            omega
      · cases as with
        | nil => exact List.nodup_nil
        | cons b rest => exact ih h.2

/-- Duplicate-freeness makes getD injective on in-range positions. -/
theorem nodup_getD_ne : ∀ (xs : List Nat) (i j : Nat), i < j → j < xs.length →
    xs.getD i 0 = xs.getD j 0 → ¬ xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro i j _ hj _; exact absurd hj (by simp)
  | cons a as ih =>
      intro i j hij hj heq hnod
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ v =>
              have hv : v < as.length := by simpa using hj
              have hin : as.getD v 0 ∈ as :=
                (mem_iff_get? _ _).mpr ⟨v, hv, get?_getD _ _ _ hv⟩
              have heq' : a = as.getD v 0 := heq
              cases hnod with
              | cons hp _ => exact hp (as.getD v 0) hin heq'
      | succ u =>
          cases j with
          | zero => omega
          | succ v =>
              cases hnod with
              | cons _ htail =>
                  exact ih u v (by omega) (by simpa using hj) (by simpa using heq) htail

theorem nodup_getD_inj {xs : List Nat} (h : xs.Nodup) : ∀ i j, i < xs.length → j < xs.length →
    xs.getD i 0 = xs.getD j 0 → i = j := by
  intro i j hi hj heq
  by_contra hne
  have hlt : i < j ∨ j < i := by omega
  rcases hlt with hlt | hlt
  · exact (nodup_getD_ne xs i j hlt hj heq) h
  · exact (nodup_getD_ne xs j i hlt hi heq.symm) h

/-- Key-ascendingness of a list lifted into some: SelectorFoldConsistent's first conjunct is
    exactly what makes plan.sortedSimple.map some ascending in the grouped walk's order. -/
theorem keyAsc_map_some (xs : List Nat) (h : natsAscending xs) : KeyAsc (xs.map some) := by
  induction xs with
  | nil => exact trivial
  | cons a as ih =>
      refine ⟨?_, ih ?_⟩
      · intro y hy
        obtain ⟨c, hc, hyc⟩ := List.mem_map.mp hy
        subst hyc
        have h1 : a < as.getD 0 0 := by
          cases as with
          | nil => exact absurd hc (by simp)
          | cons b rest => exact h.1
        have has : natsAscending as := by
          cases as with
          | nil => exact absurd hc (by simp)
          | cons b rest => exact h.2
        have hle : as.getD 0 0 ≤ c := natAsc_head_le as has c hc
        have hlt : a < c := Nat.lt_of_lt_of_le h1 hle
        show Midfall.Halo2.optionNatLt (some a) (some c) = true
        simp only [Midfall.Halo2.optionNatLt]
        simpa using hlt
      · cases as with
        | nil => exact trivial
        | cons b rest => exact h.2


theorem foldState_buckets_len (yv : QVMFr) (sf : SelectorFoldPlan) :
    ∀ (src : List (QuotientIdentity × QVMFr)) (st : FoldState),
      (List.foldl (fun st a => foldStep yv sf st a.1 a.2) st src).buckets.length =
        st.buckets.length := by
  intro src
  induction src with
  | nil => intro st; rfl
  | cons a as ih =>
      intro st
      show (List.foldl (fun st x => foldStep yv sf st x.1 x.2)
          (foldStep yv sf st a.1 a.2) as).buckets.length = st.buckets.length
      rw [ih]
      cases a with
      | mk id v =>
          cases id with
          | mk m1 m2 m3 target m4 =>
              cases target with
              | main => rfl
              | selector s => exact List.length_modify _ _ _

/-- (iii) Canonicity is TRIVIAL: qvmFrAdd and qvmFrMul are both '(% qvmFrModulus)', so every
    foldStep's qn is already below the modulus and qvmToFr_neg applies directly. No new
    hypothesis is needed and none was added. -/
theorem qvmFrAdd_lt (a b : QVMFr) : qvmFrAdd a b < qvmFrModulus := by
  show (a + b) % qvmFrModulus < qvmFrModulus
  exact Nat.mod_lt _ (by decide)

theorem qvmFrMul_lt (a b : QVMFr) : qvmFrMul a b < qvmFrModulus := by
  show (a * b) % qvmFrModulus < qvmFrModulus
  exact Nat.mod_lt _ (by decide)

theorem foldStep_qn_lt (yv : QVMFr) (sf : SelectorFoldPlan) (st : FoldState)
    (id : QuotientIdentity) (v : QVMFr) (h : st.qn < qvmFrModulus) :
    (foldStep yv sf st id v).qn < qvmFrModulus := by
  cases id with
  | mk m1 m2 m3 target m4 =>
      cases target with
      | main =>
          show qvmFrAdd (qvmFrMul st.qn yv) v < qvmFrModulus
          exact qvmFrAdd_lt _ _
      | selector s =>
          show qvmFrMul st.qn yv < qvmFrModulus
          exact qvmFrMul_lt _ _

theorem foldl_foldStep_qn_lt (yv : QVMFr) (sf : SelectorFoldPlan) :
    ∀ (src : List (QuotientIdentity × QVMFr)) (st : FoldState),
      st.qn < qvmFrModulus →
        (List.foldl (fun st a => foldStep yv sf st a.1 a.2) st src).qn < qvmFrModulus := by
  intro src
  induction src with
  | nil => intro st h; exact h
  | cons a as ih =>
      intro st h
      exact ih (foldStep yv sf st a.1 a.2) (foldStep_qn_lt yv sf st a.1 a.2 h)


/-- THE HEADLINE FOLD STATEMENT. The whole-stream fold over the plan's identity values
    equals what computeLinearizationCommitment computes from the verifier's partially
    evaluated identities: the query's expected evaluation is -qn (the None bucket,
    subtracted in at Linearization.lean:105), and the selector buckets appear as the
    linear-combination scalars after the quotient-limb scalars, in ascending column
    order - ascending bucket index because sortedSimple is ascending
    (SelectorFoldConsistent's first conjunct).
    PROOF HOLE (M6-4, design1 estimates 3 days): the argument is horner_reverse +
    bucket_horner_with_gaps + groupedAdd_as_sum, i.e. that the sparse gap/tail scheme
    reproduces Σ vᵢ·y^(m-1-i) per bucket and that groupedAdd's key order is the
    ascending column order. hcorr stays a binder because the frame layer above is not
    discharged yet - identityCorrespondence_of_bridge_fixed (LoweringV3/QuotientRows.lean) says
    exactly what would remove it.
    The statement is FALSE without hcons (a gap off by one moves a bucket by a factor y,
    foldGapOffByOneFlipsBucket_ok) and without hvals (non-canonical representatives break
    qvmToFr's homomorphism, Qvm.lean's qvmToFr_needsCanonicity_ok). -/
theorem quotientFold_matches_linearization {G₁ : Type} (plan : QuotientProgramPlan)
    (hcons : SelectorFoldConsistent plan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr)
    (hvals : ∀ v ∈ vals, v < qvmFrModulus)
    (hcorr : IdentityCorrespondence plan exprs vals)
    (vk : Midfall.Halo2.VerifyingKey FrR G₁) (x y xn sf : FrR) (limbs : Array G₁)
    (q : Midfall.Halo2.VerifierQuery FrR G₁)
    (hq : Midfall.Halo2.computeLinearizationCommitment exprs vk x y xn sf limbs = .ok q) :
    let r := quotientFold plan y.val vals
    q.eval = qvmToFr r.1 ∧
      ∃ pts labs, q.commitment = Midfall.Halo2.CommitmentReference.linear pts
        ((limbScalars limbs.size xn sf ++ r.2.map qvmToFr).toArray) labs := by
  intro r
  -- sizes: the two length conjuncts of the correspondence make every index transferable.
  have hvl : vals.length = (globalIdentities plan).length := hcorr.2.1
  have hlen : (linStream plan vals).length = (globalIdentities plan).length :=
    length_linStream plan vals (by omega)
  have hlenE : exprs.toList.length = (globalIdentities plan).length := by
    show exprs.size = _
    exact hcorr.1
  have hlenS : (streamVals (linStream plan vals)).length = (globalIdentities plan).length := by
    show (List.map (fun p => (p.1, p.2.val)) (linStream plan vals)).length = _
    rw [List.length_map]
    exact hlen
  -- (1) streamFacts
  have hidx : ∀ i < (linStream plan vals).length,
      idxAt (linStream plan vals) i = i := by
    intro i hi
    exact idxAt_linStream plan vals i (by omega) (by omega)
  have hkeyNone : ∀ i < exprs.toList.length,
      (exprs.toList.getD i (none, 0)).1 = none ↔
        ((streamVals (linStream plan vals)).getD i (none, 0)).1 = none := by
    intro i hi
    have hn : i < (globalIdentities plan).length := by omega
    have hs : ((streamVals (linStream plan vals)).getD i (none, 0)).1 =
        ((linStream plan vals).getD i noPair).1 := by
      dsimp only [streamVals]
      rw [getD_map_of_lt (fun p => (p.1, p.2.val)) (linStream plan vals) i (none, 0) noPair
        (by rw [hlen]; omega)]
    rw [hs, mainKey_linStream plan vals i hn (by omega)]
    cases h : ((globalIdentities plan)[i]'hn).target with
    | main =>
        rw [exprs_getD_fst_main plan exprs vals hcorr i hn h]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
    | selector s =>
        have hslt : s < plan.sortedSimple.length := (hcons.2.2.1 i hn s h).1
        rw [exprs_getD_fst_sel plan exprs vals hcorr i hn s h,
          get?_getD plan.sortedSimple s 0 hslt]
        exact ⟨fun hh => absurd hh (by simp), fun hh => absurd hh (by simp)⟩
  have hvalNone : ∀ i < exprs.toList.length,
      (exprs.toList.getD i (none, 0)).2 =
        ((streamVals (linStream plan vals)).getD i (none, 0)).2 := by
    intro i hi
    have hn : i < (globalIdentities plan).length := by omega
    have h1 : (exprs.toList.getD i (none, 0)).2 = qvmToFr (vals.getD i 0) :=
      exprs_getD_snd plan exprs vals hcorr i hn
    have h2 : ((streamVals (linStream plan vals)).getD i (none, 0)).2 =
        ((linStream plan vals).getD i noPair).2.val := by
      dsimp only [streamVals]
      rw [getD_map_of_lt (fun p => (p.1, p.2.val)) (linStream plan vals) i (none, 0) noPair
        (by rw [hlen]; omega)]
    rw [h1, h2, val_linStream plan vals i hn (by omega)]
    exact congrArg qvmToFr ((get_eq_getD vals i 0 (by omega)).symm)
  -- (2) SelectorFoldConsistent's third conjunct, read at consecutive bucket positions.
  have hgapc : ∀ s i j, i < j → j < (linStream plan vals).length →
      hasKey s (linStream plan vals) i → hasKey s (linStream plan vals) j →
        (∀ k, i < k → k < j → ¬ hasKey s (linStream plan vals) k) →
        gapAt (linStream plan vals) j = j - i := by
    intro s i j hij hj hki hkj hmid
    have hn : j < (globalIdentities plan).length := by omega
    have hn' : i < (globalIdentities plan).length := by omega
    have hkj' : ((globalIdentities plan)[j]'hn).target = QuotientTarget.selector s :=
      (hasKey_linStream plan vals s j hn (by omega)).mp hkj
    have hki' : ((globalIdentities plan)[i]'hn').target = QuotientTarget.selector s :=
      (hasKey_linStream plan vals s i hn' (by omega)).mp hki
    have h4 := (hcons.2.2.1 j hn s hkj').2 i (by omega) (fun k hk hk1 hk2 =>
      fun hh => hmid k hk1 hk2
        ((hasKey_linStream plan vals s k hk (by omega)).mpr hh))
    rcases h4 with hnot | hg
    · exact absurd hki' hnot
    · rw [gapAt_linStream plan vals j hn (by omega), hg]
      simp
  -- (3) SelectorFoldConsistent's fifth conjunct gives endIdx and the tail exponent.
  have htailL : plan.selectorFold.tailExponents.length = plan.sortedSimple.length :=
    hcons.2.2.2.1
  have htail (t : Nat) (ht : t < plan.sortedSimple.length) :
      plan.selectorFold.tailExponents.getD t 0 =
        (globalIdentities plan).length - 1 - endIdx (proj t (linStream plan vals)) := by
    have hex : ∃ x ∈ globalIdentities plan, x.target = QuotientTarget.selector t :=
      (hcons.2.2.2.2 t ht).1
    obtain ⟨x, hx, hxt⟩ := hex
    obtain ⟨i, hi, hget⟩ := (mem_iff_get? (globalIdentities plan) x).mp hx
    have hx' : ((globalIdentities plan)[i]'(by omega)) = x := by
      have hg2 := get?_getD (globalIdentities plan) i x (by omega)
      rw [hget] at hg2
      exact ((get_eq_getD (globalIdentities plan) i x (by omega)).trans
        (Option.some.inj hg2).symm)
    have htarget : ((globalIdentities plan)[i]'(by omega)).target = QuotientTarget.selector t := by
      rw [hx']
      exact hxt
    have hkey : ∃ m < (linStream plan vals).length, hasKey t (linStream plan vals) m :=
      ⟨i, by omega, (hasKey_linStream plan vals t i (by omega) (by omega)).mpr htarget⟩
    obtain ⟨j, hj, hkj, hlast⟩ := exists_last_hasKey (linStream plan vals) hkey
    have hjn : j < (globalIdentities plan).length := by omega
    have hkj' : ((globalIdentities plan)[j]'hjn).target = QuotientTarget.selector t :=
      (hasKey_linStream plan vals t j hjn (by omega)).mp hkj
    have h5 := (hcons.2.2.2.2 t ht).2 j hjn hkj' (fun k hk hk2 =>
      fun hh => hlast k (by omega) (by omega)
        ((hasKey_linStream plan vals t k hk (by omega)).mpr hh))
    have hgt : endIdx (proj t (linStream plan vals)) = j := by
      have := endIdx_proj (linStream plan vals) j hj hkj hlast
      rwa [idxAt_linStream plan vals j hjn (by omega)] at this
    have hgt2 : plan.selectorFold.tailExponents.getD t 0 =
        (globalIdentities plan).length - 1 - j := by
      have h : t < plan.selectorFold.tailExponents.length := by rw [htailL]; exact ht
      have := get?_getD plan.selectorFold.tailExponents t 0 h
      rw [h5] at this
      exact (Option.some.inj this).symm
    have hjle : j ≤ (globalIdentities plan).length - 1 := by omega
    omega
  -- the fold state, and its transport into the field
  let init : FoldState :=
    { qn := 0, buckets := List.replicate plan.sortedSimple.length 0 }
  let st : FoldState := (List.zip (globalIdentities plan) vals).foldl
      (fun st iv => foldStep y.val plan.selectorFold st iv.1 iv.2) init
  have hr : r = (qvmFrNeg st.qn,
      List.zipWith (fun b t => qvmFrMul b (qvmFrPow y.val t)) st.buckets
        plan.selectorFold.tailExponents) := rfl
  have hqnlt : st.qn < qvmFrModulus :=
    foldl_foldStep_qn_lt y.val plan.selectorFold (List.zip (globalIdentities plan) vals) init
      (by show 0 < qvmFrModulus; decide)
  have hff : ffState st = List.foldl (fstep y) (ffState init) (linStream plan vals) := by
    have h1 := ffState_foldl y.val plan.selectorFold
      (List.zip (globalIdentities plan) vals) 0 init
    have hz : (List.zip (globalIdentities plan) vals).length = (globalIdentities plan).length := by
      rw [List.length_zip, Nat.min_eq_left]
      omega
    rw [hz] at h1
    rw [qvmToFr_val] at h1
    exact h1
  have hbs : st.buckets.length = plan.sortedSimple.length := by
    rw [foldState_buckets_len]
    show (List.replicate plan.sortedSimple.length 0).length = plan.sortedSimple.length
    exact List.length_replicate
  -- (A) the expected evaluation
  have hqn : qvmToFr st.qn = ((mainEntries (linStream plan vals)).map
      fun e => e.val * y ^ ((globalIdentities plan).length - 1 - e.idx)).sum := by
    calc qvmToFr st.qn = (ffState st).qn := rfl
      _ = (List.foldl (fstep y) (ffState init) (linStream plan vals)).qn := by rw [hff]
      _ = bfold y (mainEntries (linStream plan vals)) (ffState init).qn :=
          ffold_qn y (linStream plan vals) (ffState init)
      _ = bfold y (mainEntries (linStream plan vals)) 0 := by
          refine congrArg (fun z => bfold y (mainEntries (linStream plan vals)) z) ?_
          show (ffState init).qn = 0
          rfl
      _ = bfoldTarget y (mainEntries (linStream plan vals)) := bfold_zero y _
      _ = ((mainEntries (linStream plan vals)).map fun e =>
            e.val * y ^ (endIdx (mainEntries (linStream plan vals)) - e.idx)).sum :=
          bfoldTarget_naive y (mainEntries (linStream plan vals))
            (wellSpaced_mainEntries (linStream plan vals) hidx)
      _ = ((mainEntries (linStream plan vals)).map fun e =>
            e.val * y ^ ((globalIdentities plan).length - 1 - e.idx)).sum := by
          rw [endIdx_mainEntries (linStream plan vals) hidx, hlen]
  -- (4) the grouped walk, its keys, and its scalar list
  obtain ⟨grouped, pts, labs, hgrp, heval, hcomm⟩ :=
    computeLinearizationCommitment_ok exprs vk x y xn sf limbs q hq
  have hgg : grouped = gfoldGo y exprs.toList.reverse 1 [] := by
    rw [hgrp]
    exact congrArg Prod.fst (gfoldGo_foldl y exprs.toList.reverse ([] : List (Option Nat × FrR)) 1)
  have hksorted : KeySorted grouped := by
    rw [hgg]
    exact gfoldGo_keySorted y exprs.toList.reverse 1 [] keySorted_nil
  have hlv (q' : Option Nat) : linValAt q' grouped =
      linBucket y (globalIdentities plan).length exprs.toList q' := by
    rw [hgg, groupedWalk_linValAt, hlenE]
  have hnoneS : (noneSnds grouped).sum = linValAt none grouped := (linValAt_none grouped).symm
  have hbridge_none : linBucket y (globalIdentities plan).length exprs.toList none =
      linBucket y (globalIdentities plan).length
        (streamVals (linStream plan vals)) none := by
    have hc := linBucket_congr y exprs.toList (streamVals (linStream plan vals)) none none
      (by rw [hlenE, hlenS]) hkeyNone hvalNone
    rw [hlenE] at hc
    rw [hlenS] at hc
    exact hc
  have hA : q.eval = qvmToFr r.1 := by
    rw [hr]
    show q.eval = qvmToFr (qvmFrNeg st.qn)
    rw [qvmToFr_neg st.qn hqnlt, heval, hnoneS, hlv, hbridge_none]
    have h2 : linBucket y (globalIdentities plan).length
        (streamVals (linStream plan vals)) none
        = ((mainEntries (linStream plan vals)).map fun e =>
            e.val * y ^ ((globalIdentities plan).length - 1 - e.idx)).sum := by
      have h := linBucket_stream_none y (linStream plan vals) hidx
      rw [hlen] at h
      exact h
    rw [h2, hqn, zero_sub]
  -- (4b) the scalar ORDER: the some-keys of the grouped walk are exactly sortedSimple
  have hfilter : ((grouped.map Prod.fst).filter
      (fun q => match q with | some _ => true | none => false))
      = plan.sortedSimple.map some := by
    refine keys_eq_of_sorted (keyAsc_filter _ _ (keySorted_keyAsc grouped hksorted))
      (keyAsc_map_some _ hcons.1) (fun q => ?_)
    rw [List.mem_filter, hgg, gfoldGo_mem_keys_reverse, List.mem_map]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      cases q with
      | none => exact absurd h2 (by simp)
      | some c =>
          obtain ⟨e, he, hqe⟩ := h1
          obtain ⟨i, hi, hie⟩ := (mem_iff_get? exprs.toList e).mp he
          have hn : i < (globalIdentities plan).length := by omega
          have hgi : exprs.toList[i]? = some (exprs.toList.getD i (none, 0)) :=
            get?_getD exprs.toList i (none, 0) hi
          rw [hie] at hgi
          have he2 : exprs.toList.getD i (none, 0) = e := (Option.some.inj hgi).symm
          have hqe' : (exprs.toList.getD i (none, 0)).1 = some c := by rw [he2]; exact hqe
          cases h : ((globalIdentities plan)[i]'hn).target with
          | main =>
              rw [exprs_getD_fst_main plan exprs vals hcorr i hn h (none, 0)] at hqe'
              exact absurd hqe' (by simp)
          | selector s =>
              rw [exprs_getD_fst_sel plan exprs vals hcorr i hn s h (none, 0)] at hqe'
              have hslt : s < plan.sortedSimple.length := (hcons.2.2.1 i hn s h).1
              refine ⟨c, ?_, rfl⟩
              exact (mem_iff_get? plan.sortedSimple c).mpr ⟨s, hslt, hqe'⟩
    · intro h
      obtain ⟨c, hc, rfl⟩ := h
      obtain ⟨s, hs, hget⟩ := (mem_iff_get? plan.sortedSimple c).mp hc
      have hex : ∃ x ∈ globalIdentities plan, x.target = QuotientTarget.selector s :=
        (hcons.2.2.2.2 s hs).1
      obtain ⟨x, hx, hxt⟩ := hex
      obtain ⟨k, hk, hkg⟩ := (mem_iff_get? (globalIdentities plan) x).mp hx
      have hkg2 : (globalIdentities plan)[k]? = some ((globalIdentities plan).getD k x) :=
        get?_getD (globalIdentities plan) k x hk
      rw [hkg] at hkg2
      have hx' : ((globalIdentities plan)[k]'hk) = x :=
        (get_eq_getD (globalIdentities plan) k x hk).trans (Option.some.inj hkg2).symm
      have hsel : ((globalIdentities plan)[k]'hk).target = QuotientTarget.selector s := by
        rw [hx']
        exact hxt
      have hfst : (exprs.toList.getD k (none, 0)).1 = plan.sortedSimple[s]? :=
        exprs_getD_fst_sel plan exprs vals hcorr k hk s hsel (none, 0)
      have hcs : plan.sortedSimple[s]? = some c := hget
      have hmemk : exprs.toList.getD k (none, 0) ∈ exprs.toList :=
        (mem_iff_get? exprs.toList _).mpr ⟨k, by omega, get?_getD exprs.toList k (none, 0)
          (by omega)⟩
      have hP : (exprs.toList.getD k (none, 0)).1 = some c := by rw [hfst, hcs]
      exact ⟨⟨exprs.toList.getD k (none, 0), hmemk, hP⟩, by simp⟩
  have hr2 : r.2 = List.zipWith (fun b t => qvmFrMul b (qvmFrPow y.val t)) st.buckets
      plan.selectorFold.tailExponents := by
    rw [hr]
  have hrl : r.2.length = plan.sortedSimple.length := by
    rw [hr2, List.length_zipWith, hbs, htailL, Nat.min_self]
  have hrep : ∀ (n i : Nat), i < n → (List.replicate n (0 : QVMFr)).getD i 0 = 0 := by
    intro n
    induction n with
    | zero => intro i h; exact absurd h (by simp)
    | succ m ih =>
        intro i hi
        cases i with
        | zero => rw [List.replicate_succ]; rfl
        | succ u =>
            rw [List.replicate_succ]
            exact ih u (by simpa using hi)
  have hfi_len : (ffState init).buckets.length = plan.sortedSimple.length := by
    dsimp only [ffState, init]
    rw [List.length_map, List.length_replicate]
  have hkeyBridge (t : Nat) (ht : t < plan.sortedSimple.length) :
      ∀ i < (streamVals (linStream plan vals)).length,
        ((streamVals (linStream plan vals)).getD i (some t, 0)).1 = some t ↔
          (exprs.toList.getD i (some (plan.sortedSimple.getD t 0), 0)).1 =
            some (plan.sortedSimple.getD t 0) := by
    intro i hi
    have hn : i < (globalIdentities plan).length := by
      rw [hlenS] at hi
      exact hi
    have hs : ((streamVals (linStream plan vals)).getD i (some t, 0)).1 =
        ((linStream plan vals).getD i noPair).1 := by
      dsimp only [streamVals]
      rw [getD_map_of_lt (fun p => (p.1, p.2.val)) (linStream plan vals) i (some t, 0) noPair
        (by rw [hlen]; omega)]
    rw [hs]
    show hasKey t (linStream plan vals) i ↔
      (exprs.toList.getD i (some (plan.sortedSimple.getD t 0), 0)).1 =
        some (plan.sortedSimple.getD t 0)
    rw [hasKey_linStream plan vals t i hn (by omega)]
    constructor
    · intro hsel
      rw [exprs_getD_fst_sel plan exprs vals hcorr i hn t hsel
            (some (plan.sortedSimple.getD t 0), 0)]
      exact get?_getD plan.sortedSimple t 0 ht
    · intro h
      cases h2 : ((globalIdentities plan)[i]'hn).target with
      | main =>
          rw [exprs_getD_fst_main plan exprs vals hcorr i hn h2
            (some (plan.sortedSimple.getD t 0), 0)] at h
          exact absurd h (by simp)
      | selector s =>
          rw [exprs_getD_fst_sel plan exprs vals hcorr i hn s h2
                (some (plan.sortedSimple.getD t 0), 0)] at h
          have hslt : s < plan.sortedSimple.length := (hcons.2.2.1 i hn s h2).1
          have hgs : plan.sortedSimple[s]? = some (plan.sortedSimple.getD s 0) :=
            get?_getD plan.sortedSimple s 0 hslt
          rw [hgs] at h
          have hst : s = t :=
            nodup_getD_inj (natAsc_nodup plan.sortedSimple hcons.1) s t hslt ht
              (Option.some.inj h)
          exact congrArg QuotientTarget.selector hst
  have hbkt (t : Nat) (ht : t < plan.sortedSimple.length) :
      (r.2.map qvmToFr).getD t 0 =
        linBucket y (globalIdentities plan).length exprs.toList
          (some (plan.sortedSimple.getD t 0)) := by
    have h1 : (r.2.map qvmToFr).getD t 0 = qvmToFr (r.2.getD t 0) :=
      getD_map_of_lt qvmToFr r.2 t 0 0 (by rw [hrl]; exact ht)
    have h2 : r.2.getD t 0 = qvmFrMul (st.buckets.getD t 0)
        (qvmFrPow y.val (plan.selectorFold.tailExponents.getD t 0)) :=
      getD_zipWith (fun b t => qvmFrMul b (qvmFrPow y.val t)) st.buckets
        plan.selectorFold.tailExponents t 0 0 0 (by rw [hbs]; exact ht) (by rw [htailL]; exact ht)
    have h3 : qvmToFr (r.2.getD t 0) = qvmToFr (st.buckets.getD t 0)
        * y ^ (plan.selectorFold.tailExponents.getD t 0) := by
      rw [h2, qvmToFr_mul, qvmToFr_pow]
    have h4 : qvmToFr (st.buckets.getD t 0) = (ffState st).buckets.getD t 0 := by
      rw [show (ffState st).buckets = st.buckets.map qvmToFr from rfl,
        getD_map_of_lt qvmToFr st.buckets t 0 0 (by rw [hbs]; exact ht)]
    have h5 : (ffState st).buckets.getD t 0
        = (List.foldl (fstep y) (ffState init) (linStream plan vals)).buckets.getD t 0 := by
      rw [hff]
    have h6 : (List.foldl (fstep y) (ffState init) (linStream plan vals)).buckets.getD t 0
        = bfold y (proj t (linStream plan vals)) ((ffState init).buckets.getD t 0) :=
      ffold_buckets y (linStream plan vals) t (ffState init)
        (by rw [hfi_len]; exact ht)
    have h7 : (ffState init).buckets.getD t 0 = 0 := by
      rw [show (ffState init).buckets =
            (List.replicate plan.sortedSimple.length 0).map qvmToFr from rfl,
        getD_map_of_lt qvmToFr (List.replicate plan.sortedSimple.length 0) t 0 0
          (by rw [List.length_replicate]; exact ht)]
      show qvmToFr ((List.replicate plan.sortedSimple.length 0).getD t 0) = 0
      rw [hrep plan.sortedSimple.length t ht]
      rfl
    have hidx0 : ∀ i < (linStream plan vals).length,
        idxAt (linStream plan vals) i = 0 + i := by
      intro i hi
      rw [hidx i hi]
      omega
    have hw : WellSpaced (proj t (linStream plan vals)) :=
      wellSpaced_proj (linStream plan vals) 0 hidx0 (hgapc t)
    have hle : ∀ e ∈ proj t (linStream plan vals),
        e.idx ≤ (globalIdentities plan).length - 1 := by
      intro e he
      obtain ⟨i, hi, hki, hre⟩ := exists_of_mem_proj (linStream plan vals) e he
      have hn : i < (globalIdentities plan).length := by rw [← hlen]; exact hi
      have hei : ((linStream plan vals).getD i noPair).2.idx = i :=
        idxAt_linStream plan vals i hn (by omega)
      rw [← hre, hei]
      omega
    have h9 : bfoldTarget y (proj t (linStream plan vals))
        * y ^ ((globalIdentities plan).length - 1 - endIdx (proj t (linStream plan vals)))
        = ((proj t (linStream plan vals)).map fun e =>
            e.val * y ^ ((globalIdentities plan).length - 1 - e.idx)).sum :=
      bfoldTarget_at y (proj t (linStream plan vals))
        ((globalIdentities plan).length - 1) hw hle
    have h10 : ((proj t (linStream plan vals)).map fun e =>
          e.val * y ^ ((globalIdentities plan).length - 1 - e.idx)).sum
        = linBucket y (globalIdentities plan).length
            (streamVals (linStream plan vals)) (some t) := by
      have := linBucket_stream y t (linStream plan vals) hidx
      rw [hlen] at this
      exact this.symm
    have h11 : linBucket y (globalIdentities plan).length
          (streamVals (linStream plan vals)) (some t)
        = linBucket y (globalIdentities plan).length exprs.toList
            (some (plan.sortedSimple.getD t 0)) := by
      have hvalB : ∀ i < (streamVals (linStream plan vals)).length,
          ((streamVals (linStream plan vals)).getD i (some t, 0)).2 =
            (exprs.toList.getD i (some (plan.sortedSimple.getD t 0), 0)).2 := by
        intro i hi
        have hn : i < (globalIdentities plan).length := by
          rw [hlenS] at hi
          exact hi
        have hs : ((streamVals (linStream plan vals)).getD i (some t, 0)).2 =
            ((linStream plan vals).getD i noPair).2.val := by
          dsimp only [streamVals]
          rw [getD_map_of_lt (fun p => (p.1, p.2.val)) (linStream plan vals) i (some t, 0) noPair
            (by rw [hlen]; omega)]
        have he : (exprs.toList.getD i (some (plan.sortedSimple.getD t 0), 0)).2 =
            (exprs.toList.getD i (none, 0)).2 :=
          (getD_eq_getD exprs.toList i (some (plan.sortedSimple.getD t 0), 0) (none, 0)
            (by rw [hlenE]; exact hn)).symm ▸ rfl
        rw [hs, he, val_linStream plan vals i hn (by omega),
          exprs_getD_snd plan exprs vals hcorr i hn]
        show qvmToFr (vals[i]'(by omega)) = qvmToFr (vals.getD i 0)
        exact congrArg qvmToFr (get_eq_getD vals i 0 (by omega))
      have hc := linBucket_congr y (streamVals (linStream plan vals)) exprs.toList
        (some t) (some (plan.sortedSimple.getD t 0))
        (by rw [hlenS, hlenE]) (hkeyBridge t ht) hvalB
      rw [hlenS] at hc
      rw [hlenE] at hc
      exact hc
    calc (r.2.map qvmToFr).getD t 0 = qvmToFr (r.2.getD t 0) := h1
      _ = qvmToFr (st.buckets.getD t 0) * y ^ (plan.selectorFold.tailExponents.getD t 0) := h3
      _ = (ffState st).buckets.getD t 0 * y ^ (plan.selectorFold.tailExponents.getD t 0) := by rw [h4]
      _ = (List.foldl (fstep y) (ffState init) (linStream plan vals)).buckets.getD t 0
            * y ^ (plan.selectorFold.tailExponents.getD t 0) := by rw [h5]
      _ = bfold y (proj t (linStream plan vals)) ((ffState init).buckets.getD t 0)
            * y ^ (plan.selectorFold.tailExponents.getD t 0) := by rw [h6]
      _ = bfold y (proj t (linStream plan vals)) 0
            * y ^ (plan.selectorFold.tailExponents.getD t 0) := by rw [h7]
      _ = bfoldTarget y (proj t (linStream plan vals))
            * y ^ (plan.selectorFold.tailExponents.getD t 0) := by rw [bfold_zero y _]
      _ = bfoldTarget y (proj t (linStream plan vals))
            * y ^ ((globalIdentities plan).length - 1 - endIdx (proj t (linStream plan vals))) := by
            rw [htail t ht]
      _ = ((proj t (linStream plan vals)).map fun e =>
            e.val * y ^ ((globalIdentities plan).length - 1 - e.idx)).sum := h9
      _ = linBucket y (globalIdentities plan).length
            (streamVals (linStream plan vals)) (some t) := h10
      _ = linBucket y (globalIdentities plan).length exprs.toList
            (some (plan.sortedSimple.getD t 0)) := h11
  have hsg0 : someSnds grouped
      = (plan.sortedSimple.map some).map (fun q => linValAt q grouped) :=
    (someSnds_keySorted grouped hksorted).trans
      (congrArg (fun K => List.map (fun q => linValAt q grouped) K) hfilter)
  have hcomp : ∀ (xs : List Nat),
      (xs.map some).map (fun q => linValAt q grouped)
        = xs.map (fun s => linValAt (some s) grouped) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons c rest ih =>
        rw [List.map_cons, List.map_cons, List.map_cons, ih]
  have hsg1 : someSnds grouped
      = plan.sortedSimple.map (fun s => linValAt (some s) grouped) :=
    hsg0.trans (hcomp plan.sortedSimple)
  have hsome : someSnds grouped = r.2.map qvmToFr := by
    refine list_eq_of_getD (someSnds grouped) (r.2.map qvmToFr) 0 ?_ ?_
    · simp only [hsg1, List.length_map, hrl]
    · intro t ht
      have hlt : t < plan.sortedSimple.length := by
        simp only [hsg1, List.length_map] at ht
        exact ht
      have h1 : (someSnds grouped).getD t 0
          = (plan.sortedSimple.map (fun s => linValAt (some s) grouped)).getD t 0 :=
        congrArg (fun l => l.getD t 0) hsg1
      have h2 : (plan.sortedSimple.map (fun s => linValAt (some s) grouped)).getD t 0
          = linValAt (some (plan.sortedSimple.getD t 0)) grouped := by
        rw [getD_map_of_lt (fun s => linValAt (some s) grouped) plan.sortedSimple t 0 0 hlt]
      have h3 : linValAt (some (plan.sortedSimple.getD t 0)) grouped
          = linBucket y (globalIdentities plan).length exprs.toList
              (some (plan.sortedSimple.getD t 0)) := hlv _
      have h4 : (r.2.map qvmToFr).getD t 0 =
          linBucket y (globalIdentities plan).length exprs.toList
            (some (plan.sortedSimple.getD t 0)) := hbkt t hlt
      rw [h1, h2, h3, ← h4]
  have hB : ∃ pts labs, q.commitment = Midfall.Halo2.CommitmentReference.linear pts
      ((limbScalars limbs.size xn sf ++ r.2.map qvmToFr).toArray) labs := by
    refine ⟨pts.toArray, labs.toArray, ?_⟩
    refine hcomm.trans ?_
    rw [hsome]
    show Midfall.Halo2.CommitmentReference.linear pts.toArray
        ((limbScalars limbs.size xn sf ++ r.2.map qvmToFr).toArray) labs.toArray =
      Midfall.Halo2.CommitmentReference.linear pts.toArray
        ((limbScalars limbs.size xn sf ++ r.2.map qvmToFr).toArray) labs.toArray
    rfl
  exact ⟨hA, hB⟩

/-- The exclusion D-P20's gap names, spelled as a hypothesis rather than implied by a
    fixture: the plan's stream is interpreted-only, i.e. no inline prefix, no structured
    tail and no native marker. Only then do the two artifact records even have the same
    number of identities: the whole-stream executor walks bytecode and folds once per
    fold opcode, while expectedLinearizationArtifacts folds once per identity in the
    stream, and the certifier pushes ZERO for every native item (VmCertify.lean:607, and
    the survey's warning not to use identityValues as y-position values). -/
def streamIsInterpretedOnly (plan : QuotientProgramPlan) : Prop :=
  plan.inlineIdentities = [] ∧ plan.structuredTailIdentities = [] ∧
    plan.nativePermutationIdentities = [] ∧ plan.nativeLookupIdentities = [] ∧
    plan.nativeIdentities = [] ∧
    (∀ it ∈ plan.items, ∃ id, it = QuotientProgramItem.identity id)

/-- D-P20 CLAIM 1, statable today modulo L.plan.qprog - and stated with the named
    exclusion rather than papered over. The whole-stream fold executor over the finalized
    bytecode (T:4325-4391, FoldCompute.lean:907) produces the same artifacts as the
    reference's naive global-power oracle (T:4288-4321) evaluated on the plan's identity
    stream, PROVIDED the stream is interpreted-only.
    THE SEGMENT-EVALUATOR SEAM IS hseg, and it is a real mismatch, not plumbing: the test
    module's third interpreter reads a HashMap memory (TestMem) while P-09b's reference
    interpreter reads the Keccak PRNG (QuotientRefMemory); the two agree only where the
    two memories were made to agree, which is what hseg says per pointer on the literal
    domain. foldClaim1_agreementOnInterpretedStream_ok below runs the theorem's content
    through P-09b's interpreter rather than the test module's, on a fixture where the
    memories do agree - so the hypothesis is not vacuous and the exclusion is not
    decorative.
    PROOF HOLE (M6-4): the fold-walk induction over evalQuotientProgramArtifacts.go
    against List.foldl over the identity stream, plus qvm_compile_correct_identity at
    each segment. -/
theorem qvm_compile_correct_stream {Program Layout : Type}
    (r : QuotientShapeRecognizers) (hr : RecognizersSound r)
    (L : Midfall.Generator.LoweringPlan Program Layout)
    (q : Midfall.Generator.PlannedQuotient) (hq : L.quotient = some q)
    (hbuild : buildPlan r q.plan (withLimbVmOps true) = .ok q.build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ q.plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ q.build.consts, c.toNat < qvmFrModulus)
    (hstream : streamIsInterpretedOnly q.plan)
    (bytes : List Nat) (hqprog : L.qprog = .ok bytes)
    (y : QVMFr) (hy : y < qvmFrModulus)
    (mem : QuotientRefMemory) (memT : TestMem)
    (hseg : ∀ (start end' : Nat), start ≤ end' → end' ≤ bytes.length →
        ((Midfall.Generator.evalQuotientIdentity
              ((bytes.drop start).take (end' - start)) q.build.consts mem).toOption.map
            Prod.fst).getD 0 ==
          foldTestSegmentEval ((bytes.drop start).take (end' - start)) q.build.consts memT)
    (hvals : ∀ id ∈ globalIdentities q.plan,
                (evalExprρ (fun _ a => testMemGet memT a) id.expr).isOk) :
    let segEval : Nat → Nat → QVMFr := fun start end' =>
      ((Midfall.Generator.evalQuotientIdentity
          ((bytes.drop start).take (end' - start)) q.build.consts mem).toOption.map
        Prod.fst).getD 0
    (expectedLinearizationArtifacts (globalIdentities q.plan) memT y
        q.plan.sortedSimple.length).mainNumerator ==
      (match evalQuotientProgramArtifacts bytes y q.plan.selectorFold.tailExponents segEval with
       | .ok arts => arts.mainNumerator
       | .error _ => 999) := by
  sorry

end Midfall.Lowering


/-! ====================================================================
    ## Known-answer tests
    ====================================================================

    R-41: every gate below was RUN; the failures to redden are reported in the package
    report with their causes. R-30 rule (the sketch's own KAT requirement): the fixture
    has at least 2 main AND at least 2 selector identities in INTERLEAVED order - it is
    FoldCompute's tIdentities, T:837-861 verbatim: Main, Selector(0), Selector(1), Main,
    Selector(0). A one-identity circuit cannot see an off-by-one gap.
    HAZARD 2: everything runs at the real modulus through QVMFr arithmetic. -/

namespace Midfall.Lowering.QvmFoldKats

open Midfall Midfall.Generator Midfall.Generator.QuotientBuilder
  Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientFoldComputeKats
  Midfall.Generator.QuotientBlocks Midfall.Lowering
open Midfall.Generator (QuotientIdentity QuotientProgramItem QuotientProgramPlan
  QuotientTarget QVMFr qvmFrAdd qvmFrMul qvmFrNeg qvmFrModulus)

/-- The five-identity stream as an interpreted-only plan: no inline prefix, no structured
    tail, no native marker, and the fold schedule the ported producer computes. -/
def foldPlan : QuotientProgramPlan :=
  { inlineIdentities := []
    items := tIdentities.map QuotientProgramItem.identity
    nativeIdentities := []
    nativePermutationIdentities := []
    nativeLookupIdentities := []
    structuredTailIdentities := []
    sortedSimple := [3, 7]
    hasNativePermutation := false
    hasNativeLookup := false
    selectorFold := tFold }

/-- The per-identity values the reference's own test oracle computes for that stream. -/
def foldVals : List QVMFr := tIdentities.map (fun id => evalQuotientExprForTest id.expr tMem)

/-- GATE 1 (the fold against BOTH reference oracles). quotientFold equals the naive
    global-power oracle (T:4288-4321) and the sparse gap/tail oracle (T:1314-1335) on the
    interleaved five-identity stream. This is the arithmetic D-P20 item 1 said was
    modelled nowhere; the oracles are the reference's own, so the agreement is not a
    self-consistency check. -/
def foldAgreesWithReferenceOracles_ok : Bool :=
  let y : QVMFr := 31
  let r := quotientFold foldPlan y foldVals
  let naive := expectedLinearizationArtifacts tIdentities tMem y 2
  let sparse := sparseFoldArtifacts tIdentities tMem y tFold 2
  globalIdentities foldPlan == tIdentities &&
    r.1 == naive.quotientExpectedEval && r.2 == naive.selectorBuckets &&
    r.1 == sparse.quotientExpectedEval && r.2 == sparse.selectorBuckets &&
    naive.selectorBuckets.length == 2 &&
    (naive.selectorBuckets.all fun b => b != 0)
#eval foldAgreesWithReferenceOracles_ok -- expect true

/-- GATE 2 (non-vacuity of hcons). Moving one selector gap by one changes that bucket and
    leaves the main numerator alone - the R-16 off-by-one class. If the fold could not see
    the gap this gate would stay true. -/
def foldGapOffByOneFlipsBucket_ok : Bool :=
  let y : QVMFr := 31
  let brokenFold : SelectorFoldPlan :=
    { tFold with gapsByIdentity := tFold.gapsByIdentity.modify 4 (fun g => g.map (fun n => n + 1)) }
  let broken := quotientFold { foldPlan with selectorFold := brokenFold } y foldVals
  let good := quotientFold foldPlan y foldVals
  broken.1 == good.1 && broken.2.getD 0 0 != good.2.getD 0 0 && broken.2 != good.2
#eval foldGapOffByOneFlipsBucket_ok -- expect true

/-- GATE 3 (non-vacuity of the main-advance on the selector arm). A foldStep that forgets
    qn := qn·y on the selector arm disagrees with the real one on the interleaved stream
    - which is why the Yul comment at :1312-1315 exists. -/
def foldStep_mainAdvanceIsLoadBearing_ok : Bool :=
  let y : QVMFr := 31
  let stepNoAdvance (st : FoldState) (id : QuotientIdentity) (v : QVMFr) : FoldState :=
    match id.target with
    | .main => { st with qn := qvmFrAdd (qvmFrMul st.qn y) v }
    | .selector s =>
        let gap := (tFold.gapFor id).getD 0
        { qn := st.qn,
          buckets := st.buckets.modify s (fun b =>
            qvmFrAdd (if gap = 0 then b else qvmFrMul b (qvmFrPow y gap)) v) }
  let run (f : FoldState → QuotientIdentity → QVMFr → FoldState) : QVMFr :=
    (List.zip tIdentities foldVals).foldl (fun st iv => f st iv.1 iv.2)
      { qn := 0, buckets := [0, 0] } |>.qn
  run stepNoAdvance != qvmFrNeg (quotientFold foldPlan y foldVals).1 &&
    run (fun st id v => foldStep y tFold st id v) ==
      qvmFrNeg (quotientFold foldPlan y foldVals).1
#eval foldStep_mainAdvanceIsLoadBearing_ok -- expect true

/-- GATE 4 (the duplicate qvmFrPow). This file's qvmFrPow and FoldCompute's port of the
    reference's fq_pow agree, so the duplicate is pinned rather than a silent divergence. -/
def foldQvmFrPow_agreesWithFoldCompute_ok : Bool :=
  ([0, 1, 2, 3, 7, 16] : List Nat).all fun n =>
    (Midfall.Lowering.qvmFrPow 31 n == Midfall.Generator.QuotientFoldCompute.qvmFrPow 31 n) &&
      (Midfall.Lowering.qvmFrPow 0 n == (if n == 0 then 1 % qvmFrModulus else 0)) &&
      (Midfall.Lowering.qvmFrPow 1 n == 1 % qvmFrModulus)
#eval foldQvmFrPow_agreesWithFoldCompute_ok -- expect true

/-- The decidable twin of SelectorFoldConsistent, so the producer's schedule can be GATED
    rather than only asserted: the same five conditions over bounded indices. -/
def selectorFoldConsistentBool (plan : QuotientProgramPlan) : Bool :=
  let ids := globalIdentities plan
  let asc := match plan.sortedSimple with
    | [] => true
    | [_] => true
    | _ :: _ => (List.zip plan.sortedSimple plan.sortedSimple.tail).all fun (a, b) => a < b
  let dense := (List.zipIdx ids).all fun pair => (pair.1).meta_.globalIndex == pair.2
  let gaps := (List.zipIdx ids).all fun pair =>
    match (pair.1).target with
    | QuotientTarget.selector s =>
        s < plan.sortedSimple.length &&
          (List.range pair.2).all fun j =>
            let prev := ids.getD j pair.1
            (prev.target != QuotientTarget.selector s) ||
              (((List.range (pair.2 - j - 1)).all fun k =>
                    (ids.getD (j + 1 + k) pair.1).target != QuotientTarget.selector s) →
                plan.selectorFold.gapFor pair.1 == some (pair.2 - j))
    | QuotientTarget.main => true
  let tails := plan.selectorFold.tailExponents.length == plan.sortedSimple.length
  let covered := (List.zipIdx plan.sortedSimple).all fun pair =>
    let s := pair.2
    (ids.any fun id => id.target == QuotientTarget.selector s) &&
      (List.zipIdx ids).all fun ip =>
        ((ip.1).target == QuotientTarget.selector s) →
          (((List.range (ids.length - ip.2 - 1)).all fun k =>
                (ids.getD (ip.2 + 1 + k) ip.1).target != QuotientTarget.selector s) →
            plan.selectorFold.tailExponents.getD s 999 == ids.length - 1 - ip.2)
  asc && dense && gaps && tails && covered

/-- GATE 5 (the producer satisfies the hypothesis). The fold schedule comes from the
    ported producer selectorFoldPlan (Q:356-425) and the decidable twin of
    SelectorFoldConsistent holds of it - so hcons is a fact about real plans, not an
    assumption nobody can discharge. Two perturbations fail it, so the gate is not
    vacuous. -/
def selectorFoldConsistent_onProducedPlan_ok : Bool :=
  selectorFoldConsistentBool foldPlan &&
    !selectorFoldConsistentBool
      { foldPlan with selectorFold := { tFold with tailExponents := [0, 0] } } &&
    !selectorFoldConsistentBool { foldPlan with sortedSimple := [7, 3] }
#eval selectorFoldConsistent_onProducedPlan_ok -- expect true

/-- GATE 6 (IdentityCorrespondence DISCHARGED, not assumed). For the produced plan, take
    the verifier-side array to be the tags the producer writes (fixed column at position
    s, none for Main) and the values to be the QVM's own evaluations: the correspondence
    holds by computation. The negative controls - a wrong tag and a dropped value - fail,
    so the gate checks the correspondence rather than a tautology. -/
def fixtureExprs : List (Option Nat × FrR) :=
  (List.zip tIdentities foldVals).map fun pair =>
    ((match (pair.1).target with
      | .main => (none : Option Nat)
      | .selector s => foldPlan.sortedSimple[s]?),
     qvmToFr pair.2)

/-- NOTE ON A GATE THAT COULD NOT BE WRITTEN. The natural gate for the Prop above (as
    opposed to the decidable twin below) is a by-decide discharge on this fixture. It
    does not close: the third conjunct quantifies over a Nat-bounded index whose element
    access carries a subtype proof (ids[i]'h), and decide cannot reduce that at the
    255-bit ZMod; the tactic that would (Mathlib's interval_cases / fin_cases) needs a
    Mathlib.Tactic import this package does not add, because it would rebuild the tree.
    Consequence, recorded rather than hidden: the perturbation that changes the Prop's
    selector arm from plan.sortedSimple[s]? to s reddens NO gate. The decidable twin
    below is what is actually gated, and it is the same condition. -/

def identityCorrespondence_dischargedOnFixture_ok : Bool :=
  let vals : List QVMFr := foldVals
  let exprs : List (Option Nat × FrR) := fixtureExprs
  identityCorrespondenceBool foldPlan exprs vals &&
    !identityCorrespondenceBool foldPlan
      (((none : Option Nat), (exprs.getD 1 (none, 0)).2) :: (exprs.drop 2)) vals &&
    !identityCorrespondenceBool foldPlan exprs (vals.drop 1) &&
    exprs.length == (globalIdentities foldPlan).length
#eval identityCorrespondence_dischargedOnFixture_ok -- expect true

/-- GATE 7 (the producer's bucket key inverts). The proved lemma's content on a real
    selector list, plus the agreement between this file's bucketPositionOf and the
    producer's own positionOf - the lemma is about the function the producer calls, not a
    lookalike. -/
def bucketPositionOf_agreesWithPositionOf_ok : Bool :=
  let cols : List Nat := [3, 7, 11, 200]
  cols.all fun c =>
    bucketPositionOf cols c == positionOf cols c &&
      (cols[(bucketPositionOf cols c).getD 0]? == some c) &&
    cols[(positionOf cols 99).getD 0]? != some 99
#eval bucketPositionOf_agreesWithPositionOf_ok -- expect true

/-- GATE 8 (D-P20 claim 1, run through P-09b's interpreter). The whole-stream fold
    executor over a REAL builder artifact, with the segment value taken from the
    reference interpreter run on a memory pre-populated from the SAME TestMem the naive
    oracle reads, agrees with the naive oracle on main numerator, buckets and negation.
    This is the segment-evaluator seam CLOSED for the literal-only fragment, and what
    makes it close is Qvm.lean's evalQuotientExpr_memOfρ - a proof, not a fixture. -/
def foldClaim1_agreementOnInterpretedStream_ok : Bool :=
  let y : QVMFr := 31
  let allKeys : List (Nat × Nat) :=
    (globalIdentities foldPlan).flatMap (fun id => leafKeys id.expr)
  let ρ : Valuation := fun _ a => testMemGet tMem a
  let mem := memOfρ ρ allKeys
  match buildPlan noShapeRecognizers foldPlan builderDefault with
  | .error _ => false
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      let segEval : Nat → Nat → QVMFr := fun start stop =>
        (Midfall.Generator.evalQuotientIdentity
            ((bytes.drop start).take (stop - start)) build.consts mem).toOption.map Prod.fst |>.getD 0
      match evalQuotientProgramArtifacts bytes y tFold.tailExponents segEval with
      | .error _ => false
      | .ok arts =>
          let naive := expectedLinearizationArtifacts (globalIdentities foldPlan) tMem y 2
          arts.mainNumerator == naive.mainNumerator &&
            arts.selectorBuckets == naive.selectorBuckets &&
            arts.quotientExpectedEval == naive.quotientExpectedEval &&
            arts.identityTrace.length == (globalIdentities foldPlan).length
#eval foldClaim1_agreementOnInterpretedStream_ok -- expect true

/-- GATE 9 (claim 1's exclusion is load-bearing). Add a native marker to the stream and
    the two records stop agreeing: the executor sees no fold for it while the identity
    stream has one. This is what streamIsInterpretedOnly records, and the gate is the
    evidence that the exclusion is not decorative. -/
def foldClaim1_exclusionIsLoadBearing_ok : Bool :=
  let y : QVMFr := 31
  let allKeys : List (Nat × Nat) :=
    (globalIdentities foldPlan).flatMap (fun id => leafKeys id.expr)
  let ρ : Valuation := fun _ a => testMemGet tMem a
  let mem := memOfρ ρ allKeys
  let withNative : QuotientProgramPlan :=
    { foldPlan with items := foldPlan.items ++ [QuotientProgramItem.nativeLookup] }
  match buildPlan noShapeRecognizers withNative builderDefault with
  | .error _ => true
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      let segEval : Nat → Nat → QVMFr := fun start stop =>
        (Midfall.Generator.evalQuotientIdentity
            ((bytes.drop start).take (stop - start)) build.consts mem).toOption.map Prod.fst |>.getD 0
      match evalQuotientProgramArtifacts bytes y withNative.selectorFold.tailExponents
          segEval with
      | .error _ => true
      | .ok arts => arts.identityTrace.length != (globalIdentities withNative).length
#eval foldClaim1_exclusionIsLoadBearing_ok -- expect true


/-! ### FINDING: `identityCorrespondence_of_bridge` is false as written

    Both D-P23 halves for the finding itself: `bridgeCounterexample_hypotheses_hold` is
    the satisfiability witness (all three hypotheses at once, on a real plan record), and
    `bridgeCounterexample_conclusion_fails` is the falsification (the conclusion is false
    at that same witness). Together they are the refutation of the theorem as registered.
    Per the measured falsification-deletion gap: deleting either leaves the build green and
    no gate catches it, so no persistence coverage is claimed here, only truth. -/

/-- One Main identity whose expression is the constant 0, so its value under every
    valuation is 0. Built with FoldCompute's own `cIdentity` fixture helper. -/
def bridgeCounterexampleId : QuotientIdentity :=
  Midfall.Generator.QuotientFoldComputeKats.cIdentity 0 QuotientTarget.main
    (Midfall.Generator.QuotientExpr.const 0)

/-- The one-identity plan. `sortedSimple` is empty because the single identity targets Main,
    so no bucket is named and the tag hypothesis reduces to `none`. -/
def bridgeCounterexamplePlan : QuotientProgramPlan :=
  { inlineIdentities := []
    items := [QuotientProgramItem.identity bridgeCounterexampleId]
    nativeIdentities := []
    nativePermutationIdentities := []
    nativeLookupIdentities := []
    structuredTailIdentities := []
    sortedSimple := []
    hasNativePermutation := false
    hasNativeLookup := false
    selectorFold := Midfall.Generator.selectorFoldPlanDefault }

/-- The verifier-side array: the RIGHT tag and a value of 1 where the QVM says 0. This is
    the degree of freedom the hypothesis bundle leaves open. -/
def bridgeCounterexampleExprs : Array (Option Nat × FrR) := #[(none, 1)]

/-- The QVM-side values: the identity's own value under `bridgeCounterexampleRho`. -/
def bridgeCounterexampleVals : List QVMFr := [0]

/-- The zero valuation. -/
def bridgeCounterexampleRho : Valuation := fun _ _ => 0

/-- SATISFIABILITY WITNESS (D-P23, first half): the three hypotheses of
    `identityCorrespondence_of_bridge` are simultaneously satisfiable, so the hole is not
    vacuous - it is missing a hypothesis. -/
theorem bridgeCounterexample_hypotheses_hold :
    bridgeCounterexampleExprs.size = (globalIdentities bridgeCounterexamplePlan).length ∧
      (bridgeCounterexampleVals =
        ((globalIdentities bridgeCounterexamplePlan).map
          fun id => (evalExprρ bridgeCounterexampleRho id.expr).toOption.getD 0)) ∧
      ∀ i (h : i < (globalIdentities bridgeCounterexamplePlan).length),
        (bridgeCounterexampleExprs[i]?.map Prod.fst) =
          some (match (globalIdentities bridgeCounterexamplePlan)[i]'h |>.target with
                | .main => (none : Option Nat)
                | .selector s => bridgeCounterexamplePlan.sortedSimple[s]?) := by
  refine ⟨by decide, ?_, ?_⟩
  · show [0] = [(evalExprρ bridgeCounterexampleRho bridgeCounterexampleId.expr).toOption.getD 0]
    unfold evalExprρ
    unfold Midfall.Generator.fqFromU256
    rfl
  · intro i h
    have hlen : (globalIdentities bridgeCounterexamplePlan).length = 1 := by decide
    rw [hlen] at h
    have : i = 0 := by omega
    subst this
    show (bridgeCounterexampleExprs[0]?.map Prod.fst) =
        some (match (globalIdentities bridgeCounterexamplePlan)[0]'(by decide) |>.target with
              | .main => (none : Option Nat)
              | .selector s => bridgeCounterexamplePlan.sortedSimple[s]?)
    dsimp only [bridgeCounterexampleExprs, globalIdentities, bridgeCounterexamplePlan,
      expandItem, bridgeCounterexampleId]
    rfl

/-- THE FALSIFICATION (D-P23, second half, and the finding): at that same witness the
    conclusion is FALSE. The value conjunct demands `1 = (0 : Fr r)` because `exprs` carries
    1 where the QVM's own value is 0, and no hypothesis forbids that. -/
theorem bridgeCounterexample_conclusion_fails :
    ¬ IdentityCorrespondence bridgeCounterexamplePlan bridgeCounterexampleExprs
        bridgeCounterexampleVals := by
  intro hc
  rcases hc with ⟨_, _, hval⟩
  have h0 := hval 0 (by decide)
  simp [bridgeCounterexampleExprs, bridgeCounterexampleVals, Midfall.Lowering.qvmToFr] at h0

end Midfall.Lowering.QvmFoldKats


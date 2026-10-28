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
--     identityCorrespondence_of_bridge below states the derivation with exactly that
--     one named hypothesis instead of a bundle.
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
    valuation, which identityCorrespondence_of_bridge below turns into three named
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

/-- THE DERIVATION, stated as a theorem with three named hypotheses instead of a
    postulated bundle. Each hypothesis has an owner, and none of them is the conclusion:
      horder - the two producers emit one entry per identity.
               partiallyEvaluateIdentities (Exec/Verifier.lean:253) returns an
               Array (Option Nat × Fr p) in gate/permutation/lookup/trash order;
               quotientIdentityParts (QuotientBlocks.lean:976) builds its stream from the
               same four families in the same order and asserts the counts against the
               protocol plan at Q:941-960. The agreement is a lemma about two ported
               functions.
      hvals  - vals are the QVM's own evaluations of the plan's expressions under the
               frame valuation ρ. This is the half the bridge exists for: a gate
               identity's expr field IS quotientExprFromPlonkExpr of the very Expression
               partiallyEvaluateIdentities evaluated, so what remains is
               evaluation-agreement across the bridge, per memory slot.
      htags  - the bucket-key translation: the plan's selector index s names position s
               of sortedSimple and the verifier's tag names the fixed column stored
               there. nth?_bucketPositionOf above is the proof-key, because the producer
               stamps the index as positionOf sortedSimple col
               (QuotientBlocks.lean:998-1000).
    PROOF HOLE (M6/M7): hvals is the one that still needs the Yul window layer -
    QuotientReadModel's four windows and nine token bases (LoweringPlan.lean:392-420)
    tied to the verifier's evaluation environment. That is ONE layer, not a bundle, and
    it is the honest answer to whether IdentityCorrespondence is dischargeable now: the
    blocker P-11 named (an unported function) is gone; what is left is a stated
    valuation-agreement obligation with a named owner. -/
theorem identityCorrespondence_of_bridge (plan : QuotientProgramPlan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) (ρ : Valuation)
    (horder : exprs.size = (globalIdentities plan).length)
    (hvals : vals = (globalIdentities plan).map
              fun id => (evalExprρ ρ id.expr).toOption.getD 0)
    (htags : ∀ i (h : i < (globalIdentities plan).length),
              (exprs[i]?.map Prod.fst) =
                some (match (globalIdentities plan)[i]'h |>.target with
                      | .main => (none : Option Nat)
                      | .selector s => plan.sortedSimple[s]?)) :
    IdentityCorrespondence plan exprs vals := by
  sorry

/-- The verifier-side scalars the linearization MSM opens the quotient limbs with:
    (1 - xn)·sf^i for i < n, the list computeLinearizationCommitment builds at
    Linearization.lean:80-85 (rust: linearization/verifier.rs:63-70). The plan sketches
    this as a comment ('limbScalars n xn sf := the n scalars'); it is defined here so the
    statement below is closed. -/
def limbScalars {F : Type} [Field F] (n : Nat) (xn sf : F) : List F :=
  ((List.range n).foldl (fun (acc : List F × F) _ => (acc.1 ++ [acc.2], acc.2 * sf))
    ([], 1 - xn)).1

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
    discharged yet - identityCorrespondence_of_bridge says exactly what would remove it.
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
  sorry

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

end Midfall.Lowering.QvmFoldKats


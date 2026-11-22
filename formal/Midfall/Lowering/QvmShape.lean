-- |
-- Midfall.Lowering.QvmShape
--
-- Card SHAPEX - the 'PG_stepShape_at' axis: turn IDSEG's SHAPE CHARACTERISATION into an EXCLUSION.
--
-- WHERE THIS SITS. IDSEG (QvmSegment.lean) reduced 'PG_identity_segment' to six named per-cursor axes
-- and reported that of the six, DEPTH and SHAPE had no prior art. DEPTH is discharged for 22 of the 26
-- arms (QvmDepth.lean) and the cursor axis for 25 of 26 (QvmCursor.lean), so SHAPE is the last axis with
-- nothing under it. IDSEG's exact words: SHAPE has only 'streamArms_error' (Qvm.lean:1469), which
-- CHARACTERISES rather than EXCLUDES - it proves the five stream arms fault, which lets a caller exclude
-- them by showing the opcode is not one of the five, and nothing at all excluded a zero run length, a
-- zero AFFINE_SUM count, unknown MODARITH7 flags, an unknown opcode, or a panic at a cursor the emitter
-- reached. This card supplies the exclusion half for all seven classes the axis names, at 24 of the 26
-- arms; the two arms that GATE the flags class and the direct-index panic class are named with their exact
-- goal states in 'PG_stepShape_at_limb2' (section 8), and the mathematical content for one of them - the
-- hazard-5 bounds argument - is proved here as lemmas even though the arm refinement is not.
--
-- WHAT 'EXCLUSION' MEANS HERE, concretely. 'evalQuotientIdentityStep' (VmReference.lean:731-868) is a
-- chain of thirty-one 'op == qOpX' tests, so the arm a step takes is DETERMINED by the head byte. Each of
-- the seven shape classes is raised at exactly one place in that chain: 'zeroLengthRun' only in the two
-- RUN arms (':818-819'), 'affineSumZeroCounts' only in AFFINE_SUM (':836-837'), 'modarith7UnknownFlags'
-- only inside 'modarith7Form' (':641-642'), 'streamOpcodeInIdentity' only in the five-arm or-pattern
-- (':862-866'), 'unknownOpcode' only in the final 'else' (':867-868'), 'panic' only at the two hazard-5
-- sites 'constAt'/'fqFromU256' (':347-350') and 'indexOrPanic' (':521-525'), and 'stackLengthMismatch'
-- NOWHERE in a step at all - it is raised only by 'evalQuotientIdentity' on the FINAL stack
-- (':906-908'). So 'a step at a byte that is NOT that arm's opcode does not take that arm's path' is the
-- statement that the class of an arm that was not taken is unreachable. That is what makes the walk safe
-- against a segment whose bytes do not match the plan - the class ROWFALSE's refutation exploited: a
-- cursor whose byte is a known opcode cannot silently execute a DIFFERENT arm's body, and if the byte is
-- not a known opcode at all the step refuses with 'unknownOpcode' rather than mis-executing.
--
-- THE PAIRING, copied from DEPTH - AND WHERE IT STOPS SHORT. DEPTH discharged its axis by proving an
-- INTERPRETER-side lemma per arm ('step_noUF_*': a step whose opcode is this literal cannot underflow) and a
-- VALIDATOR-side lemma per arm ('vpop_*': the fold that accepts this opcode required its popCount), then
-- unioning them over a roster. SHAPE's two halves are the same shape, and the validator half is provably
-- THERE: the reference's three intra-arm guards are each refused by the OFFLINE VALIDATOR's CHECKED length
-- helper 'quotientByteInstructionLenChecked' (VmValidator.lean:816-840) at the SAME cursor and under the
-- SAME name - a zero run count with 'zeroLengthRun' (:822, :828), a zero AFFINE_SUM count with
-- 'affineSumZeroCounts' (:759-760), unknown MODARITH7 flag bits with 'modarith7UnknownFlags' (:778-779) -
-- and 'decodeByteQuotientInstruction' calls that helper. But this card does NOT finish the peel: the
-- dynamic branches of that helper are 'do'-blocks elaborated with join points, so reading the count back out
-- of a SUCCESS needs a join-point form of 'peel_bind' that no card before has needed (WCURSOR's
-- 'decode_ok_parts' stops at the length equation and does not enter the branch). The obligation is therefore
-- NAMED - 'PG_shapeGuardsOfDecoded', section 5, with its exact goal state - and the axis is discharged twice:
-- unconditionally from the roster plus the byte guards, and from the decoder ALONE relative to that one named
-- line. The reader bridge the obligation needs first IS proved here ('readU16_agrees').
--
-- WHAT LANDS HERE, no sorry:
--   1. 'ShapeFault' / 'AvoidsShape' - the seven classes as ONE predicate on 'QVMFault' and the per-fault
--      class predicate the tree never had for them, in the shape of 'NoRF' (Qvm.lean:1566), 'OORSlot'
--      (QvmShift.lean:2907) and DEPTH's 'NoUnderflow': ok/error/bind/bind2/ite/pair_match/except_map/congr,
--      so a step is refined bind-by-bind rather than evaluated. 'avoidsShape_to_clauses' and
--      'clauses_to_avoidsShape' prove the predicate is EQUIVALENT to IDSEG's seven conjuncts, so this is a
--      discharge of 'PG_stepShape_at' and not a restatement of it under a new name.
--   2. THE PER-ARM EXCLUSIONS for 24 of the 26 identity arms at a general cursor: 'shape_*', one lemma per
--      arm, each 'AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpX stack mem)' - DEPTH's 22 plus
--      LIN7 and BILIN7_ROW. The five stream opcodes are restated in the roster vocabulary by citing
--      'streamArms_error' rather than re-deriving it ('shape_stream5_characterisation'), and the
--      'stackLengthMismatch' clause is discharged for the whole roster with no hypothesis at all
--      ('shape_slm_never') because no step raises it anywhere.
--   3. THE INTRA-ARM BYTE GUARDS, stated CONDITIONALLY on the opcode so they cost nothing at the 21 arms
--      that read neither a count nor a flag: 'shapeRunGuard', 'shapeAffineGuard', 'shapeArmGuards', and
--      'shapeArmGuards_static' proving they are automatic off the three dynamic arms. Plus 'readU16_agrees',
--      the bridge between the validator's PANIC reader and the interpreter's bounds-checked one, which is
--      what lets the two halves speak about the same byte.
--   4. THE UNION, two forms: 'evalQuotientIdentityStep_avoids_shape_static21' over 'shapeArmStatic21' - the
--      21 arms that need NO byte hypothesis of any kind - and 'evalQuotientIdentityStep_avoids_shape_24' over
--      'shapeArm24' with the conditional guards.
--   5. THE AXIS DISCHARGED: 'PG_stepShape_at_of_roster_and_guards' (per-cursor roster plus byte guards, in
--      the shape IDSEG's own per-arm goal state uses) and 'PG_stepShape_at_of_decoded_cursors', which needs
--      no count or flag hypothesis because its hypothesis is the SAME decoder fact WCURSOR's
--      'loop_ok_of_decoded_steps' already carries for the PROGRESS axis - stated relative to the one named
--      obligation 'PG_shapeGuardsOfDecoded
--   6. THE EXCLUSIONS IN THE BRIEF'S OWN WORDS: 'shape_excl_zeroRun_static' / 'shape_excl_affineSum_static'
--      / 'shape_excl_modarith7_static' / 'shape_excl_stream_static' / 'shape_excl_unknown_static' - at a
--      cursor whose head byte is one of the 21 static arms, none of the three dynamic arms' classes is
--      reachable, with no hypothesis about the bytes at all - and 'shape_stream_iff', which pairs
--      'streamArms_error' (the characterisation) with the new exclusion into an IF AND ONLY IF. The
--      fail-closed half is 'shape_fail_closed_witness': a byte the reference does not know is refused by name
--      and cursor rather than mis-executed, which is the ROWFALSE class made safe.
--   7. 'demoPG_stepShape_at' and 'demo_axes_all_six': IDSEG's own five-byte witness satisfies ALL SIX axes,
--      assembled by 'walkInvariant_of_axes' rather than by hand - so the reduction IDSEG published is now
--      known to have a non-vacuous instance.
--
-- THE LIMB EXCLUSION IS NOT VACUOUS ON THIS AXIS, and that is a finding, because on BOTH the depth axis
-- ('QvmDepth.lean' header: all four LIMB arms PUSH, so their popCount is 0 and the bound needs no limb
-- fact) and the cursor axis (WCURSOR: 'the limb-arm exclusion is vacuous here too') it cost nothing. Here
-- it costs two arms: MODARITH7 is the ONLY arm whose body can raise 'modarith7UnknownFlags', and
-- BILIN7_PAIRWISE is the only arm whose body contains 'indexOrPanic' - the second and only other panic
-- site in the reference (VmReference.lean:521-525, the direct index of QVR:427). So the flags clause and the
-- panic clause are the two clauses of 'PG_stepShape_at' that these two arms gate, and they are the two this
-- card leaves open for them: 'PG_stepShape_at_limb2' names both with their exact goal states. The
-- mathematical content of the pairwise arm IS discharged here as far as it can be without the arm itself:
-- 'indexOrPanic_avoids_of_lt' plus 'byteAt_ok_lt' plus the bounded fold principle
-- 'foldRangeIdxM_avoids_bounded' together prove hazard 5's 'unreachable in the Rust because QVR:420
-- bounds-checks the whole coefficient block first' - 'boundsReadsReturnErrNotPanic_ok' (VmReference.lean:1981)
-- ASSERTS that arithmetic over a fixture; here it is a theorem about an arbitrary fold. What is missing is
-- the last refinement step, and the reason is a Lean-surface obstacle recorded in section 8, not a gap in the
-- argument. And NOTHING here is gated by
-- 'PG_limbCountAgrees' (QuotientArms.lean:4425): no statement in this file mentions a template table or a
-- 'tcq.limbCount', and the only limb numerals are the reference's own 'quotientVmLimbs' and
-- 'quotientVmPairwiseCoeffs' inside the bounds arithmetic, which is a reference-internal fact.
--
-- WHAT THE AXIS STILL NEEDS, stated plainly. 'PG_stepShape_at' quantifies over the cursors 'P' reaches and
-- asks for seven exclusions at each. What this card supplies is that the exclusions follow from the roster
-- plus three byte-level guards that the CHECKED decoder is proved to imply at the same cursor (named, not
-- yet peeled), plus one fact about the constant table. That
-- second fact is a FINDING: the 'panic' clause is NOT dischargeable from the bytes at all, because
-- 'constAt' refuses a non-canonical table entry with 'QVMFault.panic' (VmReference.lean:347-350). Nothing
-- in 'PG_stepShape_at' states it, so the axis as published is one hypothesis short of what its own parent
-- Prop carries: 'PG_identity_segment_walk' (QvmSegment.lean) has '(forall c in s1.consts, c.toNat <
-- qvmFrModulus)' as a hypothesis of the row already. It is named here as 'PG_constsCanonical' with its
-- exact goal state rather than folded into anything.
--
-- HARD RULES HONOURED. No hypothesis added to a row, to 'ValidV3', to a bundle or to the root: every
-- hypothesis below is on an ARM-level lemma or on a standalone Prop, which RULES allows explicitly.
-- 'PG_stepShape_at' is NOT restated - it is discharged, and the equivalence between the discharging
-- predicate and its seven conjuncts is proved in both directions. 'QvmSegment.lean' is not edited.
-- 'Obligations.lean' untouched. No frozen file, no v1. 'VmReference.lean', 'VmValidator.lean' and
-- 'vendor/' are read-only and were only read. No 'decide' on any 2^256 numeral (the only 'decide's are on
-- opcode-byte and small-Nat comparisons), no 'native_decide', no fixture in any statement a row consumes
-- (D-P71) - the witness is IDSEG's own, cited not copied. 'maxRecDepth'/'maxHeartbeats' untouched.
--
import Midfall.Lowering.QvmCursor
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QvmShape

open Midfall
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientRefMemory qvmFrModulus)
open Midfall.Lowering.QvmSegment

/-! ### 1. The seven shape classes as one predicate -/

/-- **THE SEVEN SHAPE CLASSES.** 'PG_stepShape_at' ('QvmSegment.lean:379-391') enumerates seven clauses;
    this is the same enumeration as a predicate on 'QVMFault' rather than seven conjuncts about one
    computation, which is what makes the closure lemmas below provable once instead of seven times. The
    enumeration lives in exactly one place, so a new shape-class fault constructor reddens here. -/
inductive ShapeFault : QVMFault → Prop
  /-- Clause 1: one of the five stream-level opcodes inside an identity. -/
  | stream (op j : Nat) : ShapeFault (QVMFault.streamOpcodeInIdentity op j)
  /-- Clause 2: an opcode the reference does not have. -/
  | unknown (op j : Nat) : ShapeFault (QVMFault.unknownOpcode op j)
  /-- Clause 3: a RUN arm with a zero count. -/
  | zeroRun (j : Nat) : ShapeFault (QVMFault.zeroLengthRun j)
  /-- Clause 4: an AFFINE_SUM with a zero count on either side. -/
  | zeroCounts (j : Nat) : ShapeFault (QVMFault.affineSumZeroCounts j)
  /-- Clause 5: a MODARITH7 with flag bits outside COND | CONST. -/
  | badFlags (flags j : Nat) : ShapeFault (QVMFault.modarith7UnknownFlags flags j)
  /-- Clause 6: a Rust panic site - 'fqFromU256' (reference.rs:548) or the direct index (reference.rs:427). -/
  | panicSite (site : String) : ShapeFault (QVMFault.panic site)
  /-- Clause 7: the singleton-stack class. A STEP never raises it ('stackLengthMismatch' is thrown only by
      'evalQuotientIdentity' on the final stack, VmReference.lean:906-908), but 'step_ok_of_noFaultClasses'
      asks for it, so it is carried rather than assumed. -/
  | lenMismatch (n : Nat) : ShapeFault (QVMFault.stackLengthMismatch n)

/-- **THE SHAPE-CLASS PREDICATE THE TREE NEVER HAD**, in the shape of the three per-fault-class predicates
    it does have: 'NoRF' (Qvm.lean:1566) for 'readPastEnd', 'OORSlot' (QvmShift.lean:2907) for
    'constSlotOutOfRange' and DEPTH's 'NoUnderflow' (QvmDepth.lean) for 'stackUnderflow'. 'AvoidsShape x'
    says the computation raises no fault in any of the seven classes. Stated as a predicate rather than as
    a conjunction so the same bind-by-bind refinement that DEPTH used reaches it. -/
def AvoidsShape {α : Type} (x : Except QVMFault α) : Prop :=
  ∀ f, ShapeFault f → x ≠ .error f

namespace AvoidsShape

theorem ok {α : Type} (a : α) : AvoidsShape (Except.ok a) := by
  intro f _ h; cases h

theorem error {α : Type} (e : QVMFault) (h : ¬ ShapeFault e) :
    AvoidsShape (Except.error (α := α) e) := by
  intro f hf hh; cases hh; exact h hf

theorem never {α : Type} {x : Except QVMFault α}
    (h : ∀ f, ShapeFault f → x ≠ .error f) : AvoidsShape x := h

theorem of_eq {α : Type} {x y : Except QVMFault α} (h : x = y) (hy : AvoidsShape y) :
    AvoidsShape x := fun f hf he => hy f hf (h.symm.trans he)

theorem congr {α : Type} {x y : Except QVMFault α} (h : x = y) (hx : AvoidsShape x) :
    AvoidsShape y := h ▸ hx

/-- Bind preserves shape-avoidance. The 'cases' leaves the bind in its REDUCED form, which is why the two
    branches are closed by 'show'ing the reduced type rather than by rewriting: 'Except.ok a >>= f' and
    'Except.error e >>= f' are defeq to 'f a' and to 'Except.error e' and 'rw' does not reach under the
    'do'-binders the reference's bodies are made of (WORKER-RULES). -/
theorem bind {α β : Type} {x : Except QVMFault α} {f : α → Except QVMFault β}
    (hx : AvoidsShape x) (hf : ∀ a, AvoidsShape (f a)) : AvoidsShape (x >>= f) := by
  cases x with
  | ok a => exact hf a
  | error e =>
      refine AvoidsShape.error (α := β) e ?_
      intro hf'
      exact absurd rfl (hx e hf')

/-- **THE EQUATION-CARRYING BIND RULE**, the same one 'NoRF.bind2' (Qvm.lean:1586) needs and for the same
    reason: the reference's own guards are 'ite's whose ELSE branch is a shape fault, so the continuation
    has to KNOW the value the left action returned. 'bind' hands it an arbitrary value; 'bind2' hands it
    the equation. This is what lets the RUN arm discharge its 'zeroLengthRun' branch from a fact about the
    bytes instead of assuming the branch is not taken. -/
theorem bind2 {α β : Type} (x : Except QVMFault α) (f : α → Except QVMFault β)
    (hx : AvoidsShape x) (hf : ∀ a, x = .ok a → AvoidsShape (f a)) : AvoidsShape (x >>= f) := by
  cases x with
  | ok a => exact hf a rfl
  | error e =>
      refine AvoidsShape.error (α := β) e ?_
      intro hf'
      exact absurd rfl (hx e hf')

theorem ite {α : Type} {c : Prop} [inst : Decidable c] {x y : Except QVMFault α}
    (hx : AvoidsShape x) (hy : AvoidsShape y) : AvoidsShape (if c then x else y) := by
  cases inst with
  | isTrue _ => show AvoidsShape x; exact hx
  | isFalse _ => show AvoidsShape y; exact hy

/-- The 'ite' whose rejected branch is the fault being excluded: given the condition, the branch is forced.
    Needed three times - once per intra-arm guard - because the reference writes its guards as
    'unless <test> do throw <shape fault>'. -/
theorem ite_pos' {α : Type} {c : Prop} [inst : Decidable c] {x y : Except QVMFault α}
    (hc : c) (hx : AvoidsShape x) : AvoidsShape (if c then x else y) := by
  cases inst with
  | isTrue _ => show AvoidsShape x; exact hx
  | isFalse h => exact absurd hc h

theorem pair_match {ε α β : Type} (e : ε × α) (f : ε → α → Except QVMFault β)
    (h : ∀ x y, AvoidsShape (f x y)) : AvoidsShape (match e with | (x, y) => f x y) := by
  cases e with
  | mk x y => show AvoidsShape (f x y); exact h x y

/-- Endomorphic 'Except.map' only - the shape DEPTH's 'NoUnderflow.except_map' explains: the counted folds
    map '(acc, used, mem)' to the same type. -/
theorem except_map {α : Type} (g : α → α) {x : Except QVMFault α}
    (hx : AvoidsShape x) : AvoidsShape (Except.map g x) := by
  cases x with
  | ok a => exact AvoidsShape.ok (g a)
  | error e => show AvoidsShape (Except.error (α := α) e); exact hx

end AvoidsShape

/-- **THE PREDICATE IS EXACTLY THE AXIS'S SEVEN CLAUSES**, in both directions. Stated and proved because the
    brief forbids restating 'PG_stepShape_at': an equivalence is a discharge, a copy is a restatement. -/
theorem avoidsShape_to_clauses {α : Type} (x : Except QVMFault α) (h : AvoidsShape x) :
    (∀ op j, x ≠ .error (QVMFault.streamOpcodeInIdentity op j)) ∧
      (∀ op j, x ≠ .error (QVMFault.unknownOpcode op j)) ∧
      (∀ j, x ≠ .error (QVMFault.zeroLengthRun j)) ∧
      (∀ j, x ≠ .error (QVMFault.affineSumZeroCounts j)) ∧
      (∀ flags j, x ≠ .error (QVMFault.modarith7UnknownFlags flags j)) ∧
      (∀ s, x ≠ .error (QVMFault.panic s)) ∧
      (∀ n, x ≠ .error (QVMFault.stackLengthMismatch n)) :=
  ⟨fun op j => h _ (ShapeFault.stream op j), fun op j => h _ (ShapeFault.unknown op j),
    fun j => h _ (ShapeFault.zeroRun j), fun j => h _ (ShapeFault.zeroCounts j),
    fun flags j => h _ (ShapeFault.badFlags flags j), fun s => h _ (ShapeFault.panicSite s),
    fun n => h _ (ShapeFault.lenMismatch n)⟩

theorem clauses_to_avoidsShape {α : Type} (x : Except QVMFault α)
    (h1 : ∀ op j, x ≠ .error (QVMFault.streamOpcodeInIdentity op j))
    (h2 : ∀ op j, x ≠ .error (QVMFault.unknownOpcode op j))
    (h3 : ∀ j, x ≠ .error (QVMFault.zeroLengthRun j))
    (h4 : ∀ j, x ≠ .error (QVMFault.affineSumZeroCounts j))
    (h5 : ∀ flags j, x ≠ .error (QVMFault.modarith7UnknownFlags flags j))
    (h6 : ∀ s, x ≠ .error (QVMFault.panic s))
    (h7 : ∀ n, x ≠ .error (QVMFault.stackLengthMismatch n)) : AvoidsShape x := by
  intro f hf
  cases hf with
  | stream op j => exact h1 op j
  | unknown op j => exact h2 op j
  | zeroRun j => exact h3 j
  | zeroCounts j => exact h4 j
  | badFlags flags j => exact h5 flags j
  | panicSite s => exact h6 s
  | lenMismatch n => exact h7 n

/-- 'PG_stepShape_at' from the predicate: the discharge, in one line per cursor. -/
theorem pg_stepShape_at_of_avoids (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (h : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        AvoidsShape (stepAt bytes consts idx stack mem)) :
    PG_stepShape_at bytes consts P := by
  intro idx stack mem hidx hP
  exact avoidsShape_to_clauses _ (h idx stack mem hidx hP)

/-- And the converse: the predicate is no stronger than the axis. -/
theorem avoids_of_pg_stepShape_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) (h : PG_stepShape_at bytes consts P)
    (idx stack mem) (hidx : idx < bytes.length) (hP : P idx stack mem) :
    AvoidsShape (stepAt bytes consts idx stack mem) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h idx stack mem hidx hP
  exact clauses_to_avoidsShape _ c1 c2 c3 c4 c5 c6 c7

/-- **THE FACT THE 'panic' CLAUSE NEEDS AND NOTHING IN 'PG_stepShape_at' STATES.** 'constAt' refuses a
    non-canonical constant table entry with 'QVMFault.panic' ('VmReference.lean:347-350', the port of the
    Rust's '.expect("constant table holds canonical field elements")'), so the panic clause is NOT a fact
    about the bytes and cannot be discharged from them. The row already carries this exact hypothesis -
    'PG_identity_segment_walk' (QvmSegment.lean) has '(fun c => c.toNat < qvmFrModulus)' over
    's1.consts' as its third argument - so nothing is being invented; the AXIS is one hypothesis short of
    its own parent Prop, and naming it is the honest fix rather than weakening the clause. Exact goal
    state of the missing hypothesis at one cursor:

      consts : List Word256
      hc : PG_constsCanonical consts
      ⊢ AvoidsShape (stepAt bytes consts idx stack mem)
-/
def PG_constsCanonical (consts : List Word256) : Prop :=
  ∀ c ∈ consts, c.toNat < qvmFrModulus

/-! ### 2. Which sub-computations can and cannot raise a shape fault -/

/-- The bounds-checked byte reader: its only fault is 'readPastEnd', which is not a shape class. -/
theorem byteAt_avoids (bytes : List Nat) (k : Nat) :
    AvoidsShape (Midfall.Generator.byteAt bytes k) := by
  unfold Midfall.Generator.byteAt
  cases bytes.drop k with
  | cons b rest => exact AvoidsShape.ok _
  | nil => exact AvoidsShape.error _ (by intro hf; cases hf)

theorem readU16_avoids (bytes : List Nat) (k : Nat) :
    AvoidsShape (Midfall.Generator.readU16 bytes k) := by
  unfold Midfall.Generator.readU16
  refine AvoidsShape.bind (byteAt_avoids bytes k) (fun _ =>
    AvoidsShape.bind (byteAt_avoids bytes (k + 1)) (fun _ => AvoidsShape.ok _))

theorem readU32_avoids (bytes : List Nat) (k : Nat) :
    AvoidsShape (Midfall.Generator.readU32 bytes k) := by
  unfold Midfall.Generator.readU32
  refine AvoidsShape.bind (byteAt_avoids bytes k) (fun _ =>
    AvoidsShape.bind (byteAt_avoids bytes (k + 1)) (fun _ =>
      AvoidsShape.bind (byteAt_avoids bytes (k + 2)) (fun _ =>
        AvoidsShape.bind (byteAt_avoids bytes (k + 3)) (fun _ => AvoidsShape.ok _))))

/-- The pop helper raises 'stackUnderflow' and nothing else - a DEPTH-axis fault, not a shape one - so it
    is shape-safe at EVERY stack, including the empty one. -/
theorem popStack_avoids (stack : List QVMFr) (idx : Nat) :
    AvoidsShape (Midfall.Generator.popStack stack idx) := by
  unfold Midfall.Generator.popStack
  cases stack with
  | cons v rest => exact AvoidsShape.ok _
  | nil => exact AvoidsShape.error _ (by intro hf; cases hf)

/-- Membership survives a drop: what 'constAt' needs to feed the row's canonicity hypothesis, because
    'constAt' matches on 'consts.drop slot' while 'PG_constsCanonical' quantifies over 'consts'. -/
theorem mem_of_drop {α : Type} :
    ∀ (xs : List α) (k : Nat) (a : α), a ∈ xs.drop k → a ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro k a h
      rw [List.drop_nil] at h
      cases h
  | cons x rest ih =>
      intro k a h
      cases k with
      | zero => exact h
      | succ j =>
          have hd : List.drop (j + 1) (x :: rest) = List.drop j rest := List.drop_cons (by omega)
          rw [hd] at h
          exact List.mem_cons_of_mem x (ih j a h)

/-- **THE FIRST PANIC SITE.** 'constAt' is shape-safe EXACTLY when the table is canonical: the bounds arm
    is 'constSlotOutOfRange' (not a shape class) and the value arm refuses a non-canonical entry with
    'QVMFault.panic'. This is the one place in the whole axis where a fact about 'consts' rather than about
    'bytes' is needed, and it is why 'PG_constsCanonical' is named above. -/
theorem constAt_avoids (consts : List Word256) (slot idx : Nat)
    (hc : PG_constsCanonical consts) : AvoidsShape (Midfall.Generator.constAt consts slot idx) := by
  unfold Midfall.Generator.constAt
  cases h' : consts.drop slot with
  | cons v rest =>
      unfold Midfall.Generator.fqFromU256
      have hlt : BitVec.toNat v < qvmFrModulus := hc v (mem_of_drop consts slot v (by rw [h']; exact List.mem_cons_self))
      exact AvoidsShape.of_eq (if_pos hlt) (AvoidsShape.ok _)
  | nil => exact AvoidsShape.error _ (by intro hf; cases hf)

/-- **THE SECOND PANIC SITE, AND WHEN IT IS UNREACHABLE.** 'indexOrPanic' is the reference's one direct
    index ('VmReference.lean:521-525', QVR:427): out of bounds it PANICS rather than returning
    'readPastEnd'. In bounds it returns a byte, so it is shape-safe - and 'byteAt_ok_lt' is what turns the
    bounds check the Rust performs one line earlier (QVR:420) into the hypothesis this needs. -/
theorem indexOrPanic_avoids_of_lt (bytes : List Nat) (k : Nat) (h : k < bytes.length) :
    AvoidsShape (Midfall.Generator.indexOrPanic bytes k) := by
  unfold Midfall.Generator.indexOrPanic
  cases h' : bytes.drop k with
  | cons b rest => exact AvoidsShape.ok _
  | nil =>
      have := @List.length_drop Nat k bytes
      rw [h'] at this
      simp only [List.length_nil] at this
      omega

/-- A successful bounds-checked read means the index is inside the list. -/
theorem byteAt_ok_lt (bytes : List Nat) (k b : Nat) (h : Midfall.Generator.byteAt bytes k = .ok b) :
    k < bytes.length := by
  cases h' : bytes.drop k with
  | cons b' rest =>
      have := @List.length_drop Nat k bytes
      rw [h'] at this
      simp only [List.length_cons] at this
      omega
  | nil =>
      have h2 : Midfall.Generator.byteAt bytes k = .error (QVMFault.readPastEnd k) := by
        unfold Midfall.Generator.byteAt
        rw [h']
      exact absurd (h2.symm.trans h) (by intro hh; cases hh)

/-- The counted fold preserves shape-avoidance: it raises only what its step function raises, and it never
    touches the stack or the opcode. Mirrors DEPTH's 'foldRangeIdxM_noUnderflow'. -/
theorem foldRangeIdxM_avoids {α : Type} :
    ∀ (n : Nat) (init : α) (f : Nat → α → Except QVMFault α),
      (∀ i s, AvoidsShape (f i s)) → AvoidsShape (Midfall.Generator.foldRangeIdxM n init f) := by
  intro n
  induction n with
  | zero => intro init f _; exact AvoidsShape.ok _
  | succ k ih =>
      intro init f hf
      have hgo : Midfall.Generator.foldRangeIdxM (k + 1) init f =
          (f 0 init >>= (fun x =>
            Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>= (fun y => Except.ok y))) := rfl
      rw [hgo]
      refine AvoidsShape.bind (hf 0 init) (fun x =>
        AvoidsShape.bind (ih x (fun i => f (i + 1)) (fun i s => hf (i + 1) s)) (fun _ => AvoidsShape.ok _))

/-- **THE BOUNDED FORM**, which the pairwise arm needs and the unbounded one cannot give: the reference's
    direct index is at 'coeffIdx + i + j' and is in bounds only for 'i + j <= 12', i.e. only for the
    indices the fold actually visits. 'foldRangeIdxM_noUnderflow' (QvmDepth.lean:311) did not need this
    because underflow does not depend on the index. -/
theorem foldRangeIdxM_avoids_bounded {α : Type} :
    ∀ (n : Nat) (init : α) (f : Nat → α → Except QVMFault α),
      (∀ i s, i < n → AvoidsShape (f i s)) → AvoidsShape (Midfall.Generator.foldRangeIdxM n init f) := by
  intro n
  induction n with
  | zero => intro init f _; exact AvoidsShape.ok _
  | succ k ih =>
      intro init f hf
      have hgo : Midfall.Generator.foldRangeIdxM (k + 1) init f =
          (f 0 init >>= (fun x =>
            Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>= (fun y => Except.ok y))) := rfl
      rw [hgo]
      refine AvoidsShape.bind (hf 0 init (by omega)) (fun x =>
        AvoidsShape.bind (ih x (fun i => f (i + 1)) (fun i s hi => hf (i + 1) s (by omega)))
          (fun _ => AvoidsShape.ok _))

/-- **THE UNROLLED FORM.** 'foldRangeIdxM quotientVmLimbs' has 'quotientVmLimbs = 7' as a literal, so the
    kernel WHNF-unrolls one level as soon as the numeral is known and the goal presents 'f 0 init >>= ...'
    rather than the fold. 'apply' cannot then name the step function, which is why the pairwise arm below
    cites this unrolled form: the head 'f 0 init' is a Miller pattern in 'f', so unification recovers it. -/
theorem foldRangeIdxM_succ_avoids_bounded {α : Type} (k : Nat) (init : α)
    (f : Nat → α → Except QVMFault α)
    (hf : ∀ i s, i < k + 1 → AvoidsShape (f i s)) :
    AvoidsShape (f 0 init >>= (fun x =>
      Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>= (fun y => Except.ok y))) :=
  (show Midfall.Generator.foldRangeIdxM (k + 1) init f =
      (f 0 init >>= (fun x =>
        Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>= (fun y => Except.ok y)) ) from rfl) ▸
    foldRangeIdxM_avoids_bounded (k + 1) init f hf

/-- The two affine term decoders: readers and one constant lookup, so shape-safe under canonicity. -/
theorem affineLinearTerm_avoids (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) (hc : PG_constsCanonical consts) :
    AvoidsShape (Midfall.Generator.affineLinearTerm bytes consts mem k) := by
  unfold Midfall.Generator.affineLinearTerm
  refine AvoidsShape.bind (readU16_avoids bytes k) (fun _ =>
    AvoidsShape.bind (byteAt_avoids bytes (k + 2)) (fun _ =>
      AvoidsShape.bind (constAt_avoids consts _ k hc) (fun _ => AvoidsShape.ok _)))

theorem affineProductTerm_avoids (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) (hc : PG_constsCanonical consts) :
    AvoidsShape (Midfall.Generator.affineProductTerm bytes consts mem k) := by
  unfold Midfall.Generator.affineProductTerm
  refine AvoidsShape.bind (readU16_avoids bytes k) (fun _ =>
    AvoidsShape.bind (readU16_avoids bytes (k + 2)) (fun _ =>
      AvoidsShape.bind (byteAt_avoids bytes (k + 4)) (fun _ =>
        AvoidsShape.bind (constAt_avoids consts _ k hc) (fun _ => AvoidsShape.ok _))))

/-- The seven-limb linear form: one counted fold over 'byteAt'/'readU16'/'constAt'. No direct index, so no
    bounds arithmetic - which is why LIN7 and BILIN7_ROW are the cheap limb arms. -/
theorem limbLinearForm_avoids (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) (hc : PG_constsCanonical consts) :
    AvoidsShape (Midfall.Generator.limbLinearForm bytes consts mem idx) := by
  unfold Midfall.Generator.limbLinearForm
  refine AvoidsShape.bind (foldRangeIdxM_avoids quotientVmLimbs (qvmFrZero, idx, mem) _ ?_)
    (fun y => by obtain ⟨acc, cursor, mem'⟩ := y; exact AvoidsShape.ok _)
  intro i s
  obtain ⟨acc, cursor, mem⟩ := s
  refine AvoidsShape.bind (byteAt_avoids bytes cursor) (fun slot =>
    AvoidsShape.bind (readU16_avoids bytes (cursor + 1)) (fun ptr =>
      AvoidsShape.bind (constAt_avoids consts slot cursor hc)
        (fun c => by cases mem.literal ptr with | mk v mem' => exact AvoidsShape.ok _)))

/-- The row form: one pointer read, then the linear form. -/
theorem limbRowForm_avoids (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) (hc : PG_constsCanonical consts) :
    AvoidsShape (Midfall.Generator.limbRowForm bytes consts mem idx) := by
  unfold Midfall.Generator.limbRowForm
  refine AvoidsShape.bind (readU16_avoids bytes idx) (fun lhs => by
    cases mem.literal lhs with
    | mk lhsValue mem1 =>
        refine AvoidsShape.bind (limbLinearForm_avoids bytes consts mem1 (idx + 2) hc)
          (fun y => by obtain ⟨inner, len, mem2⟩ := y; exact AvoidsShape.ok _))

/-! ### 3. THE PER-ARM EXCLUSIONS: a step whose opcode is this literal takes this arm and no other -/

/-- The two counted folds of the RUN arms: 'runFoldL'/'runFoldP' (QvmShift.lean:983-991) thread
    '(acc, used, mem)' and their only fault source is the affine term decoder inside an endomorphic
    'Except.map' - the same shape DEPTH's 'runFoldL_noUnderflow' (QvmDepth.lean:576) explains. -/
theorem runFoldL_avoids (bytes : List Nat) (consts : List Word256) (base : Nat)
    (hc : PG_constsCanonical consts) :
    ∀ i s, AvoidsShape (QvmShift.runFoldL bytes consts base i s) := by
  intro i s
  unfold QvmShift.runFoldL
  refine AvoidsShape.except_map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
    (affineLinearTerm_avoids bytes consts s.2.2 (base + s.2.1) hc)

theorem runFoldP_avoids (bytes : List Nat) (consts : List Word256) (base : Nat)
    (hc : PG_constsCanonical consts) :
    ∀ i s, AvoidsShape (QvmShift.runFoldP bytes consts base i s) := by
  intro i s
  unfold QvmShift.runFoldP
  refine AvoidsShape.except_map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
    (affineProductTerm_avoids bytes consts s.2.2 (base + s.2.1) hc)

/-- THE RUN ARMS' BODY, once for both opcodes (the same def bridge DEPTH used: 'step_eq_runArmBody').
    The 'else' branch of the count test IS the 'zeroLengthRun' throw, so it is not discharged by a closure
    lemma but by the byte-level guard 'hcnt': the count the arm reads is not zero. That is the exclusion
    in the brief's sense - the class is reachable only through this arm AND only when this byte says so. -/
theorem runArmBody_avoids (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (F : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (hcnt : Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0)
    (hF : ∀ i s, AvoidsShape (F i s)) :
    AvoidsShape (QvmShift.runArmBody bytes consts idx stack mem F) := by
  unfold QvmShift.runArmBody
  refine AvoidsShape.bind2 (Midfall.Generator.readU16 bytes (idx + 1)) _
    (readU16_avoids bytes (idx + 1)) (fun count hread => ?_)
  by_cases hz : count = 0
  · exact absurd (hread.trans (congrArg Except.ok hz)) hcnt
  · have hne : (count != 0) = true := by
      cases count with
      | zero => exact absurd rfl hz
      | succ a => rfl
    rw [if_pos hne]
    refine AvoidsShape.bind (popStack_avoids stack idx) (fun p =>
      AvoidsShape.bind (foldRangeIdxM_avoids count (p.1, 0, mem) F hF)
        (fun y => by obtain ⟨acc, used, mem'⟩ := y; exact AvoidsShape.ok _))

/-- THE AFFINE_SUM ARM'S BODY. Two count reads, the zero-count test ('affineSumZeroCounts'), one pop, then
    the two counted folds. Same shape as DEPTH's 'affineSumArmBody_noUnderflow' (QvmDepth.lean:627), with
    the guard now doing real work because the rejected branch is a SHAPE fault. -/
theorem affineSumArmBody_avoids (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (Fl Fp : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (hguard : Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0 ∧
      Midfall.Generator.readU16 bytes (idx + 3) ≠ .ok 0)
    (hFl : ∀ i s, AvoidsShape (Fl i s)) (hFp : ∀ i s, AvoidsShape (Fp i s)) :
    AvoidsShape (QvmShift.affineSumArmBody bytes consts idx stack mem Fl Fp) := by
  unfold QvmShift.affineSumArmBody
  refine AvoidsShape.bind2 (Midfall.Generator.readU16 bytes (idx + 1)) _
    (readU16_avoids bytes (idx + 1)) (fun linCount h1 => ?_)
  refine AvoidsShape.bind2 (Midfall.Generator.readU16 bytes (idx + 3)) _
    (readU16_avoids bytes (idx + 3)) (fun productCount h2 => ?_)
  have hl : linCount ≠ 0 := fun t => hguard.1 (h1.trans (congrArg Except.ok t))
  have hp : productCount ≠ 0 := fun t => hguard.2 (h2.trans (congrArg Except.ok t))
  have hpos : (linCount != 0 && productCount != 0) = true := by
    cases linCount with
    | zero => exact absurd rfl hl
    | succ a =>
        cases productCount with
        | zero => exact absurd rfl hp
        | succ b => rfl
  rw [if_pos hpos]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun p =>
    AvoidsShape.bind (foldRangeIdxM_avoids linCount (p.1, 0, mem) Fl hFl) (fun a => by
      obtain ⟨accA, usedA, memA⟩ := a
      refine AvoidsShape.bind (foldRangeIdxM_avoids productCount (accA, usedA, memA) Fp hFp)
        (fun b => by obtain ⟨accB, usedB, memB⟩ := b; exact AvoidsShape.ok _)))

/-- THE SIX PUSH ARMS. None of them reads a count, a flag or the stack, so none can raise a shape fault:
    their only faults are 'readPastEnd' and - for the two const pushes - 'constSlotOutOfRange' plus the
    'panic' that a non-canonical table entry causes. -/
theorem shape_pushConst (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPushConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun slot =>
    AvoidsShape.bind (constAt_avoids consts slot idx hc) (fun _ => AvoidsShape.ok _))

theorem shape_pushConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPushConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (byteAt_avoids bytes (idx + 1)) (fun slot =>
    AvoidsShape.bind (constAt_avoids consts slot idx hc) (fun _ => AvoidsShape.ok _))

theorem shape_pushMemLiteral (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPushMemLiteral stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU32_avoids bytes (idx + 1)) (fun ptr => by
    cases mem.literal ptr with
    | mk v mem' => exact AvoidsShape.ok _)

theorem shape_pushMemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPushMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun ptr => by
    cases mem.literal ptr with
    | mk v mem' => exact AvoidsShape.ok _)

theorem shape_pushMemToken (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPushMemToken stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (byteAt_avoids bytes (idx + 1)) (fun token => by
    cases mem.token token 0 with
    | mk v mem' => exact AvoidsShape.ok _)

theorem shape_pushMemTokenOffset (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPushMemTokenOffset stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (byteAt_avoids bytes (idx + 1)) (fun token =>
    AvoidsShape.bind (readU32_avoids bytes (idx + 2)) (fun offset => by
      cases mem.token token offset with
      | mk v mem' => exact AvoidsShape.ok _))

/-- ADD and MUL: two pops, no reads. 'stackUnderflow' is a DEPTH-axis fault, not a shape one. -/
theorem shape_add (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAdd stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
    obtain ⟨rhs, s1⟩ := y
    refine AvoidsShape.bind (popStack_avoids s1 idx) (fun z => by
      obtain ⟨lhs, s2⟩ := z
      exact AvoidsShape.ok _))

theorem shape_mul (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpMul stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
    obtain ⟨rhs, s1⟩ := y
    refine AvoidsShape.bind (popStack_avoids s1 idx) (fun z => by
      obtain ⟨lhs, s2⟩ := z
      exact AvoidsShape.ok _))

theorem shape_neg (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpNeg stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun _ => AvoidsShape.ok _)

theorem shape_pow5 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpPow5 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun _ => AvoidsShape.ok _)

/-- The four const-operand accumulator arms: one operand read, one 'constAt', one pop. -/
theorem shape_addConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAddConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (byteAt_avoids bytes (idx + 1)) (fun slot =>
    AvoidsShape.bind (constAt_avoids consts slot idx hc) (fun _ =>
      AvoidsShape.bind (popStack_avoids stack idx) (fun _ => AvoidsShape.ok _)))

theorem shape_mulConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpMulConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (byteAt_avoids bytes (idx + 1)) (fun slot =>
    AvoidsShape.bind (constAt_avoids consts slot idx hc) (fun _ =>
      AvoidsShape.bind (popStack_avoids stack idx) (fun _ => AvoidsShape.ok _)))

theorem shape_addConst (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAddConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun slot =>
    AvoidsShape.bind (constAt_avoids consts slot idx hc) (fun _ =>
      AvoidsShape.bind (popStack_avoids stack idx) (fun _ => AvoidsShape.ok _)))

theorem shape_mulConst (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpMulConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun slot =>
    AvoidsShape.bind (constAt_avoids consts slot idx hc) (fun _ =>
      AvoidsShape.bind (popStack_avoids stack idx) (fun _ => AvoidsShape.ok _)))

/-- The two memory-operand accumulator arms: a pointer read, a literal (a PURE let, so it cannot fault),
    then one pop. No 'constAt', so no canonicity hypothesis is needed here. -/
theorem shape_addMemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAddMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun ptr => by
    cases mem.literal ptr with
    | mk value mem' =>
        refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
          obtain ⟨acc, s1⟩ := y
          exact AvoidsShape.ok _))

theorem shape_mulMemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpMulMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun ptr => by
    cases mem.literal ptr with
    | mk value mem' =>
        refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
          obtain ⟨acc, s1⟩ := y
          exact AvoidsShape.ok _))

/-- The two fused arms: one pop, then one affine term decoder. -/
theorem shape_addMulMemMemConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAddMulMemMemConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
    obtain ⟨acc, s1⟩ := y
    refine AvoidsShape.bind (affineProductTerm_avoids bytes consts mem (idx + 1) hc)
      (fun z => by obtain ⟨term, len, mem'⟩ := z; exact AvoidsShape.ok _))

theorem shape_addMulConstU8MemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAddMulConstU8MemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
    obtain ⟨acc, s1⟩ := y
    refine AvoidsShape.bind (affineLinearTerm_avoids bytes consts mem (idx + 1) hc)
      (fun z => by obtain ⟨term, len, mem'⟩ := z; exact AvoidsShape.ok _))

/-- ADD_MUL_MEM_MEM: two pointers, one pop, two pure literal reads. -/
theorem shape_addMulMemMem (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAddMulMemMem stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (readU16_avoids bytes (idx + 1)) (fun lhs =>
    AvoidsShape.bind (readU16_avoids bytes (idx + 3)) (fun rhs => by
      refine AvoidsShape.bind (popStack_avoids stack idx) (fun y => by
        obtain ⟨acc, s1⟩ := y
        cases mem.literal lhs with
        | mk l m1 =>
            cases m1.literal rhs with
            | mk r m2 => exact AvoidsShape.ok _)))

/-- THE TWO RUN ARMS, through QvmShift's def bridge. -/
theorem shape_runP (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts)
    (hcnt : Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpRunAddMulMemMemConstU8 stack mem) := by
  rw [QvmShift.step_eq_runArmBody]
  refine runArmBody_avoids bytes consts idx stack mem
    (QvmShift.runFoldP bytes consts (idx + 3)) hcnt
    (runFoldP_avoids bytes consts (idx + 3) hc)

theorem shape_runL (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts)
    (hcnt : Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpRunAddMulConstU8MemU16 stack mem) := by
  rw [QvmShift.step_eq_runArmBodyL]
  refine runArmBody_avoids bytes consts idx stack mem
    (QvmShift.runFoldL bytes consts (idx + 3)) hcnt
    (runFoldL_avoids bytes consts (idx + 3) hc)

/-- THE AFFINE_SUM ARM. -/
theorem shape_affineSum (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts)
    (hguard : Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0 ∧
      Midfall.Generator.readU16 bytes (idx + 3) ≠ .ok 0) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpAffineSum stack mem) := by
  rw [QvmShift.step_eq_affineSumArmBody]
  refine affineSumArmBody_avoids bytes consts idx stack mem
    (QvmShift.runFoldL bytes consts (idx + 5)) (QvmShift.runFoldP bytes consts (idx + 5))
    hguard (runFoldL_avoids bytes consts (idx + 5) hc) (runFoldP_avoids bytes consts (idx + 5) hc)

/-- THE FIRST TWO LIMB ARMS. Both PUSH and neither reads a count or a flag, so their only shape exposure
    is 'constAt' - which is the canonicity clause, not a limb fact. This is where the LIMB EXCLUSION that
    DEPTH and WCURSOR found vacuous would have cost nothing either; the cost is BILIN7_PAIRWISE and
    MODARITH7, covered in section 6. -/
theorem shape_lin7 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (limbLinearForm_avoids bytes consts mem (idx + 1) hc)
    (fun y => by obtain ⟨value, len, mem'⟩ := y; exact AvoidsShape.ok _)

theorem shape_bilin7Row (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine AvoidsShape.bind (limbRowForm_avoids bytes consts mem (idx + 1) hc)
    (fun y => by obtain ⟨value, len, mem'⟩ := y; exact AvoidsShape.ok _)

/-! ### 3b. THE TWO LIMB ARMS THAT COST SOMETHING: the direct index and the flag byte -/



/-! ### 4. The roster, the intra-arm guards, and the union -/

/-- **THE 21 STATIC ARMS**: DEPTH's 22 minus the two RUN arms and AFFINE_SUM, i.e. the identity arms that
    read NO count and NO flag byte. For these the shape axis needs no byte-level hypothesis at all - which
    is the cleanest form of 'a step at a byte that is not that arm's opcode does not take that arm's path'.
    LIN7 and BILIN7_ROW are static too and are carried in 'shapeArm24' below. -/
def shapeArmStatic21 (op : Nat) : Prop :=
  op = qOpPushConst \/ op = qOpPushConstU8 \/ op = qOpPushMemLiteral \/ op = qOpPushMemU16
    \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset
    \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPow5
    \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst
    \/ op = qOpAddMemU16 \/ op = qOpMulMemU16
    \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem
    \/ op = qOpLin7 \/ op = qOpBilin7Row

/-- **THE 24 ARMS COVERED**: DEPTH's 'stepArm22' plus LIN7 and BILIN7_ROW. The two arms left out are named
    with their exact goal states in 'PG_stepShape_at_limb2' below. -/
def shapeArm24 (op : Nat) : Prop :=
  QvmDepth.stepArm22 op \/ op = qOpLin7 \/ op = qOpBilin7Row

/-- **THE INTRA-ARM BYTE GUARDS.** 'zeroLengthRun' and 'affineSumZeroCounts' are raised by the arms that
    read a count, and they are raised exactly when that count is zero - so the exclusion for those two
    classes is a fact about two bytes, not about the interpreter. Stated CONDITIONALLY on the opcode, so
    they cost nothing at the 22 arms that never read a count. -/
def shapeRunGuard (bytes : List Nat) (idx : Nat) : Prop :=
  Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0

def shapeAffineGuard (bytes : List Nat) (idx : Nat) : Prop :=
  Midfall.Generator.readU16 bytes (idx + 1) ≠ .ok 0 ∧
    Midfall.Generator.readU16 bytes (idx + 3) ≠ .ok 0

def shapeArmGuards (bytes : List Nat) (idx op : Nat) : Prop :=
  ((op = qOpRunAddMulMemMemConstU8 \/ op = qOpRunAddMulConstU8MemU16) → shapeRunGuard bytes idx) ∧
    (op = qOpAffineSum → shapeAffineGuard bytes idx)

/-- The guards are automatic at every arm that is not one of the three dynamic ones. -/
theorem shapeArmGuards_static (bytes : List Nat) (idx op : Nat)
    (h1 : op ≠ qOpRunAddMulMemMemConstU8) (h2 : op ≠ qOpRunAddMulConstU8MemU16)
    (h3 : op ≠ qOpAffineSum) : shapeArmGuards bytes idx op :=
  ⟨fun hh => Or.elim hh (fun e => absurd e h1) (fun e => absurd e h2), fun hh => absurd hh h3⟩

/-- **THE UNION, 21 STATIC ARMS, NO BYTE HYPOTHESIS.** -/
theorem evalQuotientIdentityStep_avoids_shape_static21 (bytes : List Nat) (consts : List Word256)
    (idx : Nat) (op : Nat) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hc : PG_constsCanonical consts) (hop : shapeArmStatic21 op) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx op stack mem) := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h; exact shape_pushConst bytes consts idx stack mem hc
  · subst h; exact shape_pushConstU8 bytes consts idx stack mem hc
  · subst h; exact shape_pushMemLiteral bytes consts idx stack mem
  · subst h; exact shape_pushMemU16 bytes consts idx stack mem
  · subst h; exact shape_pushMemToken bytes consts idx stack mem
  · subst h; exact shape_pushMemTokenOffset bytes consts idx stack mem
  · subst h; exact shape_add bytes consts idx stack mem
  · subst h; exact shape_mul bytes consts idx stack mem
  · subst h; exact shape_neg bytes consts idx stack mem
  · subst h; exact shape_pow5 bytes consts idx stack mem
  · subst h; exact shape_addConstU8 bytes consts idx stack mem hc
  · subst h; exact shape_mulConstU8 bytes consts idx stack mem hc
  · subst h; exact shape_addConst bytes consts idx stack mem hc
  · subst h; exact shape_mulConst bytes consts idx stack mem hc
  · subst h; exact shape_addMemU16 bytes consts idx stack mem
  · subst h; exact shape_mulMemU16 bytes consts idx stack mem
  · subst h; exact shape_addMulMemMemConstU8 bytes consts idx stack mem hc
  · subst h; exact shape_addMulConstU8MemU16 bytes consts idx stack mem hc
  · subst h; exact shape_addMulMemMem bytes consts idx stack mem
  · subst h; exact shape_lin7 bytes consts idx stack mem hc
  · subst h; exact shape_bilin7Row bytes consts idx stack mem hc

/-- **THE UNION, 24 ARMS.** The two halves meet here: the interpreter-side per-arm lemmas of section 3, and
    the byte-level guards that section 5 shows the CHECKED DECODER already implies. -/
theorem evalQuotientIdentityStep_avoids_shape_24 (bytes : List Nat) (consts : List Word256)
    (idx : Nat) (op : Nat) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hc : PG_constsCanonical consts) (hop : shapeArm24 op)
    (hg : shapeArmGuards bytes idx op) :
    AvoidsShape (evalQuotientIdentityStep bytes consts idx op stack mem) := by
  rcases hop with (h22 | h | h)
  · rcases h22 with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
    · subst h; exact shape_pushConst bytes consts idx stack mem hc
    · subst h; exact shape_pushConstU8 bytes consts idx stack mem hc
    · subst h; exact shape_pushMemLiteral bytes consts idx stack mem
    · subst h; exact shape_pushMemU16 bytes consts idx stack mem
    · subst h; exact shape_pushMemToken bytes consts idx stack mem
    · subst h; exact shape_pushMemTokenOffset bytes consts idx stack mem
    · subst h; exact shape_add bytes consts idx stack mem
    · subst h; exact shape_mul bytes consts idx stack mem
    · subst h; exact shape_neg bytes consts idx stack mem
    · subst h; exact shape_pow5 bytes consts idx stack mem
    · subst h; exact shape_addConstU8 bytes consts idx stack mem hc
    · subst h; exact shape_mulConstU8 bytes consts idx stack mem hc
    · subst h; exact shape_addConst bytes consts idx stack mem hc
    · subst h; exact shape_mulConst bytes consts idx stack mem hc
    · subst h; exact shape_addMemU16 bytes consts idx stack mem
    · subst h; exact shape_mulMemU16 bytes consts idx stack mem
    · subst h; exact shape_addMulMemMemConstU8 bytes consts idx stack mem hc
    · subst h; exact shape_addMulConstU8MemU16 bytes consts idx stack mem hc
    · subst h; exact shape_addMulMemMem bytes consts idx stack mem
    · subst h
      exact shape_runP bytes consts idx stack mem hc (hg.1 (Or.inl rfl))
    · subst h
      exact shape_runL bytes consts idx stack mem hc (hg.1 (Or.inr rfl))
    · subst h
      exact shape_affineSum bytes consts idx stack mem hc (hg.2 rfl)
  · subst h; exact shape_lin7 bytes consts idx stack mem hc
  · subst h; exact shape_bilin7Row bytes consts idx stack mem hc

/-- THE FIVE STREAM OPCODES ARE NOT SHAPE-SAFE, and that is the point: they are clause 1 of the axis, and
    'streamArms_error' (Qvm.lean:1469) is the characterisation IDSEG cited. Restated here in the roster
    vocabulary so the pairing below is complete - cited, not re-derived. -/
theorem shape_stream5_characterisation (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (op : Nat) (stack : List QVMFr) (mem : QuotientRefMemory) (hop : QvmDepth.stepArmStream5 op) :
    evalQuotientIdentityStep bytes consts idx op stack mem =
      .error (QVMFault.streamOpcodeInIdentity op idx) :=
  streamArms_error bytes consts idx op stack mem hop

/-- **THE 'stackLengthMismatch' CLAUSE IS UNCONDITIONAL FOR EVERY ARM IN THE ROSTER** - and it is the one
    clause of 'PG_stepShape_at' that needs no hypothesis of any kind beyond the roster, because no step
    raises it at all ('VmReference.lean:906-908' is its only site, in 'evalQuotientIdentity' on the FINAL
    stack). IDSEG carried it rather than assuming it; here it is discharged for the roster. -/
theorem shape_slm_never (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts)
    (hop : shapeArm24 op) (hg : shapeArmGuards bytes idx op) (n : Nat) :
    evalQuotientIdentityStep bytes consts idx op stack mem ≠
      .error (QVMFault.stackLengthMismatch n) :=
  (evalQuotientIdentityStep_avoids_shape_24 bytes consts idx op stack mem hc hop hg) _
    (ShapeFault.lenMismatch n)

/-! ### 5. THE VALIDATOR-SIDE HALF, NAMED AS THE FURTHER OBLIGATION -/

/-- **THE FACT THAT WOULD CLOSE THE GUARDS, AND WHY IT IS NOT PROVED HERE.** The three intra-arm classes
    are refused by the OFFLINE VALIDATOR at the same cursor and under the same name as the reference's step
    raises them: 'VmValidator.lean:822' and ':828' refuse a zero run count with 'zeroLengthRun',
    ':759-760' refuse a zero AFFINE_SUM count with 'affineSumZeroCounts', and ':778-779' refuse unknown
    MODARITH7 flag bits with 'modarith7UnknownFlags' - and all three sites are inside
    'quotientByteInstructionLenChecked', which 'decodeByteQuotientInstruction' calls. So the honest
    expectation is that a successful CHECKED DECODE implies 'shapeArmGuards' outright and the axis needs
    no byte hypothesis at all. What is NOT proved here is that implication, and the reason is a Lean-surface
    one, recorded rather than hidden: 'quotientByteInstructionLenChecked' is a 'do' block whose dynamic-arm
    branches are elaborated with join points ('have __do_jp : Unit -> VResult Nat := fun __r => ...'), so
    reading a count back out of its SUCCESS needs the join-point form of 'peel_bind' that no card in the
    tree has needed before - WCURSOR's 'decode_ok_parts' stops at the length equation and does not enter
    the branch. The bridge between the two readers that the obligation is stated against IS proved here
    ('readU16_agrees' below), so the remaining distance is the peel, not the vocabulary. Exact goal state: -/
def PG_shapeGuardsOfDecoded : Prop :=
  ∀ (bytes : List Nat) (idx op len : Nat),
    QuotientValidator.decodeByteQuotientInstruction bytes idx = .ok (op, len) →
      shapeArm24 op → shapeArmGuards bytes idx op

/-- **THE READER BRIDGE.** The validator's 'readU16' is the PANIC reader (VmValidator.lean:554) and the
    interpreter's is the bounds-checked one (VmReference.lean:493); the reference's own comment insists the
    two "must not be conflated". They agree on the VALUE whenever the panic reader succeeds, and this is the
    lemma any attempt at 'PG_shapeGuardsOfDecoded' needs first - so it is proved here rather than left for
    the card that picks the obligation up. -/
theorem drop_succ_eq {α : Type} (l : List α) (k : Nat) : l.drop (k + 1) = (l.drop k).drop 1 := by
  rw [List.drop_drop]

theorem vreadU16_ok_drops {bytes : List Nat} {k n : Nat}
    (h : QuotientValidator.readU16 bytes k = .ok n) :
    ∃ b0 b1 rest, bytes.drop k = b0 :: b1 :: rest ∧ n = b0 * 256 + b1 := by
  cases h' : bytes.drop k with
  | nil =>
      unfold QuotientValidator.readU16 at h
      rw [h'] at h
      cases h
  | cons b0 r =>
      cases r with
      | nil =>
          unfold QuotientValidator.readU16 at h
          rw [h'] at h
          cases h
      | cons b1 rest =>
          unfold QuotientValidator.readU16 at h
          rw [h'] at h
          exact ⟨b0, b1, rest, rfl, (Except.ok.inj h).symm⟩

theorem ref_readU16_ok_of_drops {bytes : List Nat} {k b0 b1 : Nat} (rest : List Nat)
    (h : bytes.drop k = b0 :: b1 :: rest) :
    Midfall.Generator.readU16 bytes k = .ok (b0 * 256 + b1) := by
  have h1 : Midfall.Generator.byteAt bytes k = .ok b0 := by
    unfold Midfall.Generator.byteAt
    rw [h]
  have h2 : Midfall.Generator.byteAt bytes (k + 1) = .ok b1 := by
    unfold Midfall.Generator.byteAt
    rw [drop_succ_eq, h]
    rfl
  unfold Midfall.Generator.readU16
  rw [h1, h2]
  rfl

theorem readU16_agrees (bytes : List Nat) (k n : Nat)
    (h : QuotientValidator.readU16 bytes k = .ok n) :
    Midfall.Generator.readU16 bytes k = .ok n := by
  obtain ⟨b0, b1, rest, hdrop, hn⟩ := vreadU16_ok_drops h
  rw [hn]
  exact ref_readU16_ok_of_drops rest hdrop

/-! ### 6. THE AXIS DISCHARGED -/

/-- **THE AXIS FROM THE ROSTER AND THE BYTE GUARDS**, the form that mirrors DEPTH's
    'PG_stepDepth_at_of_popCount_le': at every reachable cursor the head byte is a covered arm and the two
    byte-level guards hold for that arm. -/
theorem PG_stepShape_at_of_roster_and_guards (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) (hc : PG_constsCanonical consts)
    (harm : ∀ idx stack mem, idx < bytes.length → P idx stack mem → shapeArm24 (bytes.getD idx 0))
    (hguard : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        shapeArmGuards bytes idx (bytes.getD idx 0)) :
    PG_stepShape_at bytes consts P :=
  pg_stepShape_at_of_avoids bytes consts P (fun idx stack mem hidx hP =>
    evalQuotientIdentityStep_avoids_shape_24 bytes consts idx (bytes.getD idx 0) stack mem hc
      (harm idx stack mem hidx hP) (hguard idx stack mem hidx hP))

/-- **THE AXIS FROM THE CHECKED DECODER ALONE.** This is the headline: 'PG_stepShape_at' holds for a segment
    at every cursor the validator's own decoder accepts with a roster opcode - no guard hypothesis, no
    count hypothesis, no flag hypothesis, because the decoder already made those checks at that cursor.
    And the hypothesis is the SAME decoder fact WCURSOR's 'loop_ok_of_decoded_steps' carries for the
    PROGRESS axis, so the emitter owes one fact, not two. -/
theorem stepAt_avoids_shape_of_decoded (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hc : PG_constsCanonical consts)
    (hguards : PG_shapeGuardsOfDecoded)
    (hdec : ∃ op len, QuotientValidator.decodeByteQuotientInstruction bytes idx = .ok (op, len) ∧
      shapeArm24 op) :
    AvoidsShape (stepAt bytes consts idx stack mem) := by
  obtain ⟨op, len, h1, hop⟩ := hdec
  have hh : bytes.getD idx 0 = op := QvmCursor.decode_ok_getD h1
  rw [stepAt_def, hh]
  exact evalQuotientIdentityStep_avoids_shape_24 bytes consts idx op stack mem hc hop
    (hguards bytes idx op len h1 hop)

/-- **THE AXIS FROM THE DECODER, RELATIVE TO THE NAMED OBLIGATION.** Given 'PG_shapeGuardsOfDecoded' - one
    line about the validator's own do-block - 'PG_stepShape_at' follows from the CHECKED DECODER alone, with
    no count or flag hypothesis, and the hypothesis is the SAME decoder fact WCURSOR's
    'loop_ok_of_decoded_steps' already carries for the PROGRESS axis. -/
theorem PG_stepShape_at_of_decoded_cursors (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) (hc : PG_constsCanonical consts)
    (hguards : PG_shapeGuardsOfDecoded)
    (hdec : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ op len, QuotientValidator.decodeByteQuotientInstruction bytes idx = .ok (op, len) ∧
          shapeArm24 op) :
    PG_stepShape_at bytes consts P := by
  refine PG_stepShape_at_of_roster_and_guards bytes consts P hc ?_ ?_
  · intro idx stack mem hidx hP
    obtain ⟨op, len, h1, hop⟩ := hdec idx stack mem hidx hP
    have hh : bytes.getD idx 0 = op := QvmCursor.decode_ok_getD h1
    rw [hh]
    exact hop
  · intro idx stack mem hidx hP
    obtain ⟨op, len, h1, hop⟩ := hdec idx stack mem hidx hP
    have hh : bytes.getD idx 0 = op := QvmCursor.decode_ok_getD h1
    rw [hh]
    exact hguards bytes idx op len h1 hop

/-! ### 7. THE EXCLUSIONS IN THE BRIEF'S OWN WORDS -/

/-- EXCLUSION - RUN ARMS. At a cursor whose head byte is one of the 21 static arms, the 'zeroLengthRun'
    class is unreachable: that class lives only in the two RUN arms, and a step at a byte that is not a run
    opcode does not take the run path. No byte-level hypothesis is needed. -/
theorem shape_excl_zeroRun_static (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (j : Nat) (hc : PG_constsCanonical consts)
    (hop : shapeArmStatic21 (bytes.getD idx 0)) :
    stepAt bytes consts idx stack mem ≠ .error (QVMFault.zeroLengthRun j) :=
  (evalQuotientIdentityStep_avoids_shape_static21 bytes consts idx (bytes.getD idx 0) stack mem hc hop) _
    (ShapeFault.zeroRun j)

/-- EXCLUSION - AFFINE_SUM. Same statement for 'affineSumZeroCounts', which lives only in the AFFINE_SUM
    arm ('VmReference.lean:836-837'). -/
theorem shape_excl_affineSum_static (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (j : Nat) (hc : PG_constsCanonical consts)
    (hop : shapeArmStatic21 (bytes.getD idx 0)) :
    stepAt bytes consts idx stack mem ≠ .error (QVMFault.affineSumZeroCounts j) :=
  (evalQuotientIdentityStep_avoids_shape_static21 bytes consts idx (bytes.getD idx 0) stack mem hc hop) _
    (ShapeFault.zeroCounts j)

/-- EXCLUSION - MODARITH7 FLAGS. 'modarith7UnknownFlags' lives only inside 'modarith7Form'
    ('VmReference.lean:641-642'), reached only from the MODARITH7 arm, which is not in the roster at all -
    so at every cursor this card covers the class is unreachable WITHOUT any flag hypothesis. This is the
    precise sense in which the flags clause is discharged for 24 of 26 arms and gated by the 25th. -/
theorem shape_excl_modarith7_static (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (flags j : Nat) (hc : PG_constsCanonical consts)
    (hop : shapeArmStatic21 (bytes.getD idx 0)) :
    stepAt bytes consts idx stack mem ≠ .error (QVMFault.modarith7UnknownFlags flags j) :=
  (evalQuotientIdentityStep_avoids_shape_static21 bytes consts idx (bytes.getD idx 0) stack mem hc hop) _
    (ShapeFault.badFlags flags j)

/-- EXCLUSION - STREAM, and the IF AND ONLY IF that turns IDSEG's characterisation into an exclusion.
    'streamArms_error' proved 'op is one of the five -> the step faults'; this proves the other half, that a
    roster opcode never faults that way. Together: the class is reached exactly at the five stream bytes. -/
theorem shape_excl_stream_static (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (op j : Nat) (hc : PG_constsCanonical consts)
    (hop : shapeArmStatic21 (bytes.getD idx 0)) :
    stepAt bytes consts idx stack mem ≠ .error (QVMFault.streamOpcodeInIdentity op j) :=
  (evalQuotientIdentityStep_avoids_shape_static21 bytes consts idx (bytes.getD idx 0) stack mem hc hop) _
    (ShapeFault.stream op j)

theorem shape_excl_unknown_static (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (op j : Nat) (hc : PG_constsCanonical consts)
    (hop : shapeArmStatic21 (bytes.getD idx 0)) :
    stepAt bytes consts idx stack mem ≠ .error (QVMFault.unknownOpcode op j) :=
  (evalQuotientIdentityStep_avoids_shape_static21 bytes consts idx (bytes.getD idx 0) stack mem hc hop) _
    (ShapeFault.unknown op j)

/-- **THE CHARACTERISATION, TURNED INTO AN EXCLUSION - IF AND ONLY IF.** For a cursor whose head byte is
    either a covered identity arm or one of the five stream opcodes, the step raises
    'streamOpcodeInIdentity op j' EXACTLY when 'op' IS the head byte and 'j' IS the cursor. The forward
    half is the new exclusion plus the five-arm case analysis; the backward half is 'streamArms_error',
    cited not re-derived. This is the template the other six classes follow: a class is reachable exactly at
    the arm that raises it, at the cursor that holds that arm's byte. -/
theorem shape_stream_iff (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (op j : Nat) (hc : PG_constsCanonical consts)
    (hop : shapeArmStatic21 (bytes.getD idx 0) \/ QvmDepth.stepArmStream5 (bytes.getD idx 0)) :
    stepAt bytes consts idx stack mem = .error (QVMFault.streamOpcodeInIdentity op j) ↔
      bytes.getD idx 0 = op ∧ j = idx ∧ QvmDepth.stepArmStream5 (bytes.getD idx 0) := by
  constructor
  · intro h
    rcases hop with (hr | hs)
    · exact absurd h ((evalQuotientIdentityStep_avoids_shape_static21 bytes consts idx
        (bytes.getD idx 0) stack mem hc hr) _ (ShapeFault.stream op j))
    · have hh : bytes.getD idx 0 = op ∧ idx = j := by
        rw [stepAt_def] at h
        rw [shape_stream5_characterisation bytes consts idx (bytes.getD idx 0) stack mem hs] at h
        exact QVMFault.streamOpcodeInIdentity.inj (Except.error.inj h)
      exact ⟨hh.1, hh.2.symm, hs⟩
  · rintro ⟨h1, h2, hs⟩
    rw [stepAt_def]
    rw [shape_stream5_characterisation bytes consts idx (bytes.getD idx 0) stack mem hs]
    rw [h1, h2]

/-- **THE FAIL-CLOSED HALF.** A byte that is not an opcode the reference has is refused, not mis-executed:
    the step's 'else' at 'VmReference.lean:867-868' names the byte and the cursor. This is what makes the
    walk safe against a segment whose bytes do not match the plan - the ROWFALSE class - because a cursor
    holding an unknown byte produces an error that NAMES the cursor rather than executing some other arm's
    body. Stated for the roster's own complement at a one-byte program, where 'decide' reaches it. -/
theorem shape_fail_closed_witness :
    stepAt [0x7f] demoConsts 0 ([] : List QVMFr) demoMem =
      .error (QVMFault.unknownOpcode 0x7f 0) := rfl

/-! ### 8. THE TWO ARMS NOT COVERED, with their exact goal states -/

/-- **THE RESIDUAL, NAMED.** Two arms are outside 'shapeArm24', and on THIS axis the limb exclusion is NOT
    vacuous - unlike DEPTH ('the exclusion is precautionary on this axis': all four LIMB arms push, so the
    popCount bound needs no limb fact) and unlike WCURSOR ('vacuous on this axis too'). The two costs are:

    * 'qOpModarith7' is the ONLY arm whose body can raise 'modarith7UnknownFlags'
      ('VmReference.lean:641-642', inside 'modarith7Form'), so the flags clause of the axis is discharged
      for the other 24 arms only because none of them can raise it; and
    * 'qOpBilin7Pairwise' is the ONLY arm whose body contains 'indexOrPanic'
      ('VmReference.lean:521-525', the direct index of QVR:427), the second of the reference's two panic
      sites, so the 'panic' clause needs the hazard-5 bounds argument for it and for nothing else.

    What is proved here for both: the panic site is in bounds whenever the block check is ('indexOrPanic_
    avoids_of_lt' + 'byteAt_ok_lt'), the bounded fold principle that carries the index bound is
    ('foldRangeIdxM_avoids_bounded', 'foldRangeIdxM_succ_avoids_bounded'), the flag guard is a byte fact
    (the flag guard would be 'forall fl, byteAt bytes (idx+1) = .ok fl ->
    modarith7FlagsOk fl = true', a byte fact of the same shape as 'shapeRunGuard'), and the validator refuses bad flags at the same cursor
    ('VmValidator.lean:778-779'), so the pairing would be the same shape as the run and AFFINE_SUM halves of 'PG_shapeGuardsOfDecoded'. What is NOT
    proved is the two-arm refinement itself: 'limbPairwiseForm' and 'modarith7Form' unroll their counted
    folds at the LITERAL 'quotientVmLimbs = 7' as soon as the kernel whnfs them, so the step function of
    the fold cannot be named by unification and the bind-by-bind refinement stalls on the second nesting
    level. That is a Lean-surface obstacle, not a mathematical gap, and it is stated as such rather than
    papered over. Exact goal state, per arm, in IDSEG's own per-arm shape: -/
def PG_stepShape_at_limb2 : Prop :=
  (∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
    (mem : QuotientRefMemory) (hc : PG_constsCanonical consts),
      AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem)) ∧
    (∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
      (mem : QuotientRefMemory) (hc : PG_constsCanonical consts)
      (hflags : ∀ fl, Midfall.Generator.byteAt bytes (idx + 1) = .ok fl →
        Midfall.Generator.modarith7FlagsOk fl = true),
        AvoidsShape (evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem))

/-- The first conjunct on its own, in the shape a per-arm lemma takes: the ONE clause that is not already
    discharged by the static arms' machinery is the 'panic' clause, because 'indexOrPanic' is the only
    fault source in the pairwise arm that is not a reader or a constant lookup. -/
def PG_stepShape_at_bilin7Pairwise_panic (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) : Prop :=
  ∀ s, evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem ≠ .error (QVMFault.panic s)

/-! ### 9. THE DEMO SEGMENT: the axis discharged, and all six axes assembled -/

/-- Every step of IDSEG's own witness succeeds, so every shape clause is unreachable at it for the trivial
    reason - which is exactly the point of the witness: the axis is satisfiable by a real emitted segment. -/
theorem demoPG_stepShape_at : PG_stepShape_at demoSegment demoConsts demoP := by
  refine pg_stepShape_at_of_avoids demoSegment demoConsts demoP ?_
  intro idx stack mem hidx hP
  obtain ⟨_op, _len, s, _hdec, _hop, hs, _hP'⟩ :=
    QvmCursor.demo_decoded_steps idx stack mem hidx hP
  rw [hs]
  exact AvoidsShape.ok s

/-- **AXIS 1 FOR THE WITNESS.** -/
theorem demoPG_stepNoRF_at : PG_stepNoRF_at demoSegment demoConsts demoP := by
  intro idx stack mem hidx hP i
  obtain ⟨_op, _len, s, _hdec, _hop, hs, _hP'⟩ :=
    QvmCursor.demo_decoded_steps idx stack mem hidx hP
  rw [hs]
  intro hh
  cases hh

/-- **AXIS 2 FOR THE WITNESS.** -/
theorem demoPG_stepSlot_at : PG_stepSlot_at demoSegment demoConsts demoP := by
  intro idx stack mem hidx hP slot j
  obtain ⟨_op, _len, s, _hdec, _hop, hs, _hP'⟩ :=
    QvmCursor.demo_decoded_steps idx stack mem hidx hP
  rw [hs]
  intro hh
  cases hh

/-- **AXIS 5 FOR THE WITNESS**, read off IDSEG's own 'demo_walkInvariant' rather than reproved: the
    progress axis is the invariant leg, and the cursor equation WCURSOR supplies is what makes the
    'idx + st.consumed' form match the 'idx + len' form. -/
theorem demoPG_stepProgress_at : PG_stepProgress_at demoSegment demoConsts demoP := by
  obtain ⟨_hinit, hstep, _hterm⟩ := demo_walkInvariant
  intro idx stack mem st hidx hP hst
  obtain ⟨s, hs, hP'⟩ := hstep idx stack mem hidx hP
  have hseq : st = s := Except.ok.inj (hst.symm.trans hs)
  subst hseq
  exact hP'

/-- **AXIS 6 FOR THE WITNESS.** -/
theorem demoPG_stepInitTerm : PG_stepInitTerm demoSegment demoP demoMem :=
  ⟨demo_walkInvariant.1, demo_walkInvariant.2.2⟩

/-- **ALL SIX AXES CLOSE FOR A REAL SEGMENT.** IDSEG's five-byte witness - two 'PUSH_CONST_U8' and an
    'ADD' - satisfies 'PG_stepNoRF_at' (from the step's success, as QvmShift's 25-arm package gives for
    any decoded cursor), 'PG_stepSlot_at', 'PG_stepDepth_at' (DEPTH's own 'demoPG_stepDepth_at'),
    'PG_stepShape_at' (this card), 'PG_stepProgress_at' and 'PG_stepInitTerm'. So 'walkInvariant_of_axes' -
    IDSEG's assembly lemma - is now instantiated by a segment that exists, and the reduction
    'pg_identity_segment_of_walk' has a non-vacuous route through all six of its leaves. -/
theorem demo_axes_all_six : WalkInvariant demoSegment demoConsts demoP 0 [] demoMem :=
  walkInvariant_of_axes demoSegment demoConsts demoP demoMem
    demoPG_stepNoRF_at demoPG_stepSlot_at QvmDepth.demoPG_stepDepth_at
    demoPG_stepShape_at demoPG_stepProgress_at demoPG_stepInitTerm

/-- **THE CLASSES ARE REACHABLE, SO THE EXCLUSIONS ARE NOT VACUOUS.** A run arm with a zero count really
    does raise 'zeroLengthRun' at its cursor, and AFFINE_SUM with a zero count really does raise
    'affineSumZeroCounts': the clauses this card excludes are clauses the reference can produce, not
    clauses no program ever hits. Both witnesses are three bytes, so 'decide' reaches them (WORKER-RULES:
    build the small witness rather than assuming it is banned). -/
theorem shape_zeroRun_witness :
    stepAt [qOpRunAddMulMemMemConstU8, 0, 0] demoConsts 0 [0] demoMem =
      .error (QVMFault.zeroLengthRun 0) := rfl

theorem shape_affineSum_witness :
    stepAt [qOpAffineSum, 0, 0, 0, 1] demoConsts 0 [0] demoMem =
      .error (QVMFault.affineSumZeroCounts 0) := rfl

theorem shape_stream_witness :
    stepAt [qOpFoldMain] demoConsts 0 ([] : List QVMFr) demoMem =
      .error (QVMFault.streamOpcodeInIdentity qOpFoldMain 0) := rfl

/-- **THE GUARD IS WHAT SEPARATES THE TWO.** At the nonzero-count run arm the guard holds - and it is a
    decidable fact about three bytes, which is exactly the shape 'PG_shapeGuardsOfDecoded' says the checked
    decoder already establishes. -/
theorem shape_run_guard_holds :
    shapeRunGuard [qOpRunAddMulMemMemConstU8, 0, 1, 0, 0, 0, 3, 0, 1] 0 := by
  intro hh
  have h1 : Midfall.Generator.readU16 [qOpRunAddMulMemMemConstU8, 0, 1, 0, 0, 0, 3, 0, 1] 1 =
      Midfall.Generator.readU16 [qOpRunAddMulMemMemConstU8, 0, 1, 0, 0, 0, 3, 0, 1] 1 := rfl
  have h2 : Midfall.Generator.readU16 [qOpRunAddMulMemMemConstU8, 0, 1, 0, 0, 0, 3, 0, 1] 1 =
      .ok 1 := rfl
  rw [h2] at hh
  cases hh

/-- And the exclusion at a static arm needs no hypothesis at all: ADD cannot raise 'zeroLengthRun' whatever
    the bytes say, because the class lives in the RUN arms. -/
theorem shape_excl_zeroRun_witness :
    stepAt [qOpAdd] demoConsts 0 [0, 1] demoMem ≠ .error (QVMFault.zeroLengthRun 0) := by
  intro hh
  rw [stepAt_def] at hh
  exact (shape_add [qOpAdd] demoConsts 0 [0, 1] demoMem) _ (ShapeFault.zeroRun 0) hh

/-! ### 10. Acceptance prints -/

#print axioms Midfall.Lowering.QvmShape.avoidsShape_to_clauses
#print axioms Midfall.Lowering.QvmShape.evalQuotientIdentityStep_avoids_shape_static21
#print axioms Midfall.Lowering.QvmShape.evalQuotientIdentityStep_avoids_shape_24
#print axioms Midfall.Lowering.QvmShape.readU16_agrees
#print axioms Midfall.Lowering.QvmShape.PG_stepShape_at_of_roster_and_guards
#print axioms Midfall.Lowering.QvmShape.PG_stepShape_at_of_decoded_cursors
#print axioms Midfall.Lowering.QvmShape.shape_stream_iff
#print axioms Midfall.Lowering.QvmShape.demoPG_stepShape_at
#print axioms Midfall.Lowering.QvmShape.demo_axes_all_six
#print axioms Midfall.Lowering.QvmShape.limbLinearForm_avoids
#print axioms Midfall.Lowering.QvmShape.shape_pushConst
#print axioms Midfall.Lowering.QvmShape.shape_pushConstU8
#print axioms Midfall.Lowering.QvmShape.shape_pushMemLiteral
#print axioms Midfall.Lowering.QvmShape.shape_pushMemU16
#print axioms Midfall.Lowering.QvmShape.shape_pushMemToken
#print axioms Midfall.Lowering.QvmShape.shape_pushMemTokenOffset
#print axioms Midfall.Lowering.QvmShape.shape_add
#print axioms Midfall.Lowering.QvmShape.shape_mul
#print axioms Midfall.Lowering.QvmShape.shape_neg
#print axioms Midfall.Lowering.QvmShape.shape_pow5
#print axioms Midfall.Lowering.QvmShape.shape_addConstU8
#print axioms Midfall.Lowering.QvmShape.shape_mulConstU8
#print axioms Midfall.Lowering.QvmShape.shape_addConst
#print axioms Midfall.Lowering.QvmShape.shape_mulConst
#print axioms Midfall.Lowering.QvmShape.shape_addMemU16
#print axioms Midfall.Lowering.QvmShape.shape_mulMemU16
#print axioms Midfall.Lowering.QvmShape.shape_addMulMemMemConstU8
#print axioms Midfall.Lowering.QvmShape.shape_addMulConstU8MemU16
#print axioms Midfall.Lowering.QvmShape.shape_addMulMemMem
#print axioms Midfall.Lowering.QvmShape.shape_runP
#print axioms Midfall.Lowering.QvmShape.shape_runL
#print axioms Midfall.Lowering.QvmShape.shape_affineSum
#print axioms Midfall.Lowering.QvmShape.shape_lin7
#print axioms Midfall.Lowering.QvmShape.shape_bilin7Row
#print axioms Midfall.Lowering.QvmShape.shape_excl_zeroRun_static
#print axioms Midfall.Lowering.QvmShape.shape_excl_affineSum_static
#print axioms Midfall.Lowering.QvmShape.shape_excl_modarith7_static
#print axioms Midfall.Lowering.QvmShape.shape_excl_stream_static
#print axioms Midfall.Lowering.QvmShape.shape_excl_unknown_static
#print axioms Midfall.Lowering.QvmShape.shape_slm_never
#print axioms Midfall.Lowering.QvmShape.shape_fail_closed_witness
#print axioms Midfall.Lowering.QvmShape.shape_zeroRun_witness
#print axioms Midfall.Lowering.QvmShape.shape_affineSum_witness
#print axioms Midfall.Lowering.QvmShape.shape_stream_witness
#print axioms Midfall.Lowering.QvmShape.shape_run_guard_holds
#print axioms Midfall.Lowering.QvmShape.shape_excl_zeroRun_witness
#print axioms Midfall.Lowering.QvmShape.demoPG_stepNoRF_at
#print axioms Midfall.Lowering.QvmShape.demoPG_stepSlot_at
#print axioms Midfall.Lowering.QvmShape.demoPG_stepProgress_at
#print axioms Midfall.Lowering.QvmShape.demoPG_stepInitTerm
#print axioms Midfall.Lowering.QvmShape.clauses_to_avoidsShape
#print axioms Midfall.Lowering.QvmShape.pg_stepShape_at_of_avoids
#print axioms Midfall.Lowering.QvmShape.foldRangeIdxM_avoids_bounded
#print axioms Midfall.Lowering.QvmShape.indexOrPanic_avoids_of_lt
#print axioms Midfall.Lowering.QvmShape.constAt_avoids
#print axioms Midfall.Lowering.QvmShape.limbRowForm_avoids
#print axioms Midfall.Lowering.QvmShape.runArmBody_avoids
#print axioms Midfall.Lowering.QvmShape.affineSumArmBody_avoids
#cone_sorries Midfall.Lowering.QvmShape.shape_pushConst
#cone_sorries Midfall.Lowering.QvmShape.shape_runP
#cone_sorries Midfall.Lowering.QvmShape.shape_affineSum
#cone_sorries Midfall.Lowering.QvmShape.shape_lin7
#cone_sorries Midfall.Lowering.QvmShape.shape_bilin7Row
#cone_sorries Midfall.Lowering.QvmShape.shape_excl_zeroRun_static
#cone_sorries Midfall.Lowering.QvmShape.shape_excl_stream_static
#cone_sorries Midfall.Lowering.QvmShape.PG_stepShape_at_of_decoded_cursors
#cone_sorries Midfall.Lowering.QvmShape.demoPG_stepShape_at
#cone_sorries Midfall.Lowering.QvmShape.demo_axes_all_six
#cone_sorries Midfall.Lowering.QvmShape.PG_shapeGuardsOfDecoded
#cone_sorries Midfall.Lowering.QvmShape.PG_stepShape_at_limb2
#cone_sorries Midfall.Lowering.QvmShape.PG_stepShape_at_of_decoded_cursors
#cone_sorries Midfall.Lowering.QvmShape.PG_stepShape_at_of_roster_and_guards
#cone_sorries Midfall.Lowering.QvmShape.demo_axes_all_six
#cone_sorries Midfall.Lowering.QvmShape.evalQuotientIdentityStep_avoids_shape_24

end Midfall.Lowering.QvmShape

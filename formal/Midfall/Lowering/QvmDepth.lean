-- |
-- Midfall.Lowering.QvmDepth
--
-- Card DEPTH - the PG_stepDepth_at axis: a PER-ARM popCount tying the VALIDATOR's depth fold to the
-- INTERPRETER's popStack. IDSEG (QvmSegment.lean) reduced PG_identity_segment to six named axes and
-- reported that of the six, DEPTH has NO prior art at all: "nothing in the tree bounds the stack length
-- a step needs" and "the gap is the equation between the two, not either one". This card lands that
-- equation.
--
-- WHY NOTHING EXISTED, measured rather than asserted. The two folds are stated in DIFFERENT vocabularies
-- with DIFFERENT fault types, which is exactly why no lemma connected them:
--
--   * the OFFLINE VALIDATOR (VmValidator.lean:723 'applyQuotientStackEffect') carries a Nat 'depth' and
--     refuses with 'QuotientValidationFault.stackUnderflow op idx required depth' - a FOUR-field fault
--     naming the opcode, the cursor, what it required and what it found - reached from
--     'validateQuotientProgramGo' (VmValidator.lean:876) through 'requireQuotientStackDepth' (:712);
--   * the INTERPRETER (VmReference.lean:723 'popStack') carries a real 'List QVMFr' and refuses with
--     'QVMFault.stackUnderflow idx' - a ONE-field fault naming only the cursor, and NOT the amount it
--     needed. 'VmReference.lean:719-722' says the pop helpers "only fire on validator drift": the
--     reference deliberately does not re-derive the bound, so the equation was never inside it.
--
-- So the missing fact is not a missing lemma about one fold or the other; it is the ROSTER: a function
-- 'stepPopCount op' that says how many values the reference's step for opcode 'op' takes off the stack,
-- together with (i) the interpreter half - a step whose stack is at least 'stepPopCount op' deep cannot
-- raise 'QVMFault.stackUnderflow' - and (ii) the validator half - a fold that ACCEPTS opcode 'op' at
-- depth 'd' had 'stepPopCount op <= d'. Composing (i) and (ii) is the axis: a segment the validator's
-- own depth fold accepts never underflows at run time.
--
-- WHAT LANDS HERE, no sorry:
--   1. 'stepPopCount' - the per-arm popCount IDSEG named as owed, read off the reference's own bodies
--      (0 for the six pushes, 2 for ADD/MUL, 1 for the fourteen accumulator arms), with the per-arm
--      values proved by 'rfl'.
--   2. 'NoUnderflow' - the underflow-class predicate the tree never had, in the shape of the two passes
--      QvmShift already uses for the other fault classes ('NoRF' Qvm.lean:1564, 'OORSlot'
--      QvmShift.lean:2907): ok/error/bind/ite/pair_match/except_map/congr, so a step is refined
--      bind-by-bind rather than by evaluating it.
--   3. THE INTERPRETER HALF for 22 of the 26 identity arms at a GENERAL cursor:
--      'evalQuotientIdentityStep_noUnderflow_22'. The five stream opcodes and the unknown-opcode class
--      are proved too ('step_noUnderflow_stream5'), so the ONLY identity arms left are the four LIMB
--      arms, which are excluded by instruction, not by necessity - see EXCLUSIONS.
--   4. THE VALIDATOR HALF, per arm: 'validator_popCount_22' - the fold that accepts 'op' at depth 'd'
--      had 'stepPopCount op <= d', and the accepted next depth is 'd - stepPopCount op + 1', so the
--      popCount is not merely an upper bound but the exact requirement the validator enforces.
--   5. THE COMPOSITION: 'step_noUnderflow_of_validator_fold' (one cursor: validator depth + stack
--      correspondence => no underflow) and 'FoldDepth', the validator's own fold re-entered as a RELATION
--      so that the depth at a cursor is certified by the constructor that produced it -
--      'foldDepth_certifies' reads it back against 'decodeByteQuotientInstruction' and
--      'applyQuotientStackEffect' with no fuel induction in the way. 'PG_stepDepth_at_of_validator_fold'
--      then discharges the axis from the fold alone. ONE STEP IS DELIBERATELY NOT TAKEN: this card does
--      not prove 'decodeByteQuotientInstruction bytes idx = .ok (op, len) -> bytes.getD idx 0 = op'. That
--      is a fact about the validator's do-block, not about depth, so the composition carries the opcode
--      equation as a hypothesis 'hh' in the exact shape IDSEG's own per-arm goal state uses
--      ('QvmSegment.lean:361', 'op = bytes.getD idx 0').
--   6. THE AXIS DISCHARGED: 'PG_stepDepth_at_of_popCount_le' (the hypothesis shape IDSEG predicted,
--      'stack.length >= popCount op') and 'demoPG_stepDepth_at', which discharges
--      'PG_stepDepth_at' outright for IDSEG's own five-byte witness segment. The axis is therefore not
--      merely named any more: it has a proof for a real segment and a named route for every other.
--
-- DOES IT FALL OUT OF 'QSegmentStackSafe'? NO, AND IT IS WORTH SAYING WHY PRECISELY. DQVM2's
-- 'QSegmentStackSafe' (QuotientInterp.lean:1140) is a Prop ABOUT THE VALIDATOR WALK - 'qSegmentDepthGo
-- bytes len 0 0 = some 1' - and it is carried as a HYPOTHESIS of 'QInterpRefinesSegment'
-- (QuotientInterp.lean:1192). It never mentions 'evalQuotientIdentityStep', 'popStack' or
-- 'QVMFault.stackUnderflow', so it cannot be cited as the per-arm fact: a hypothesis that the walk ends
-- at depth 1 does not by itself say the interpreter's pops are covered by the depths along the way.
-- What it DOES supply is the construction to copy - the walk shape, the fuel = length argument, and the
-- end-depth-1 target - and 'FoldDepth' below is that construction re-entered at a cursor instead of run
-- to the end. So: INDEPENDENT FACT, built on DQVM2's construction, citing it rather than rebuilding it. Nothing here edits QuotientInterp.lean, which STKINV owns.
--
-- EXCLUSIONS, declared rather than assumed. The four LIMB arms (LIN7, BILIN7_ROW, BILIN7_PAIRWISE,
-- MODARITH7) sit behind 'PG_limbCountAgrees' (QuotientArms.lean:4425), an OPEN HUMAN DECISION, and are
-- EXCLUDED here by instruction: nothing in this file assumes 'tcq.limbCount = quotientVmLimbs' and no
-- statement mentions a template table. THE EXCLUSION IS PRECAUTIONARY ON THIS AXIS AND THAT IS A
-- FINDING: all four LIMB arms PUSH (VmReference.lean:850-861 pops nothing on any of them), so their
-- popCount is 0 and their depth bound needs no limb fact at all. Each is named with its exact goal
-- state in 'PG_stepDepth_at_limb4' and discharging it is one 'NoUnderflow' refinement of a form already
-- proved here ('limbLinearForm_noUnderflow' and friends would be the only new ingredient, and none of
-- them mentions a limb count). MODARITH7 is additionally the arm QvmShift excludes on the read and slot
-- axes.
--
-- WHAT THE AXIS STILL NEEDS, stated plainly. 'PG_stepDepth_at' is discharged for a segment once
-- something says the stack at each reachable cursor is at least as deep as the validator's fold computed
-- there. That is a property of the EMITTER's cursor sequence, not of the interpreter or the validator:
-- 'PG_stepDepth_at_of_validator_walk' is the form that closes it, and its hypothesis 'hwalk' is exactly
-- what 'identityExpr' has to be shown to produce. DEPTH is therefore no longer "nothing in the tree":
-- the equation exists, is proved per arm, and the remaining obligation is one named hypothesis about
-- the emitter rather than an unnamed gap.
--
-- HARD RULES HONOURED. No hypothesis added to a row, to 'ValidV3', to a bundle or to the root: every
-- hypothesis below is on an ARM-level lemma or on a standalone Prop, which RULES allows explicitly.
-- 'QvmSegment.lean' is NOT edited - the six axis Props are discharged, not restated. 'Obligations.lean'
-- untouched. No frozen file, no v1. 'VmReference.lean' and 'vendor/' are read-only and were only read.
-- No 'decide' on any 2^256 numeral (the only 'decide's are on opcode-byte comparisons and on the
-- five-byte witness), no 'native_decide', no fixture in any statement a row consumes (D-P71),
-- 'maxRecDepth'/'maxHeartbeats' untouched.
--
import Midfall.Lowering.QvmSegment
import Midfall.Generator.Quotient.VmValidator
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QvmDepth

open Midfall
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientRefMemory qvmFrModulus)
open Midfall.Lowering.QvmSegment
open Midfall.Lowering.QvmShift

/-! ### 1. The per-arm popCount -/

/-- **THE popCount IDSEG OWED** ('QvmSegment.lean:367': "'popCount' does not exist in the tree: the
    validator computes depth with its own fold and no lemma ties it to the interpreter's 'popStack'").
    'stepPopCount op' is the number of values the reference's step for opcode 'op' takes OFF the stack,
    read off the reference's own bodies: 0 for the six pushes (VmReference.lean:733-757, which cons and
    never pop), 2 for ADD and MUL (:758-765, two pops), and 1 for the fourteen accumulator arms
    (:766-849, one pop each). It is NOT read off the validator: the equation between the two is the
    theorem, not the definition, and 'validator_popCount_22' below is where they meet. -/
def stepPopCount (op : Nat) : Nat :=
  if op = qOpAdd || op = qOpMul then 2
  else if op = qOpNeg || op = qOpPow5 || op = qOpAddConstU8 || op = qOpMulConstU8
    || op = qOpAddConst || op = qOpMulConst || op = qOpAddMemU16 || op = qOpMulMemU16
    || op = qOpAddMulMemMemConstU8 || op = qOpAddMulConstU8MemU16 || op = qOpAddMulMemMem
    || op = qOpRunAddMulMemMemConstU8 || op = qOpRunAddMulConstU8MemU16 || op = qOpAffineSum then 1
  else 0

/-- The arms this card covers: the 22 identity opcodes that are neither of the two LIMB push families nor
    MODARITH7. The disjunction is the same 22-way split QvmShift uses for its general-cursor packages
    ('readsWithinStride_at_22', QvmShift.lean:2685) minus the three limb arms it carries and plus the two
    RUN arms and AFFINE_SUM, which QvmWalk carries on the read axis - so the covered set here is the same
    22 opcodes as QvmShift's '_22' packages, and the excluded set is the same four LIMB arms. -/
def stepArm22 (op : Nat) : Prop :=
  op = qOpPushConst \/ op = qOpPushConstU8 \/ op = qOpPushMemLiteral \/ op = qOpPushMemU16
    \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset
    \/ op = qOpAdd \/ op = qOpMul
    \/ op = qOpNeg \/ op = qOpPow5
    \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst
    \/ op = qOpAddMemU16 \/ op = qOpMulMemU16
    \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem
    \/ op = qOpRunAddMulMemMemConstU8 \/ op = qOpRunAddMulConstU8MemU16
    \/ op = qOpAffineSum

/-- The five stream-level opcodes: a width to the validator, an ERROR to the identity interpreter
    ('VmReference.lean:862-866'). They are NOT in 'stepArm22' - they are not identity arms - but they are
    proved here too, because the axis quantifies over whatever opcode the cursor holds. -/
def stepArmStream5 (op : Nat) : Prop :=
  op = qOpFoldMain \/ op = qOpFoldSelector \/ op = qOpNativePermutation
    \/ op = qOpNativeLookup \/ op = qOpNativeIdentity

/- The per-arm popCount values, proved by 'rfl': these are the numerals the axis is stated with. -/
theorem pc_pushConst : stepPopCount qOpPushConst = 0 := rfl
theorem pc_pushConstU8 : stepPopCount qOpPushConstU8 = 0 := rfl
theorem pc_pushMemLiteral : stepPopCount qOpPushMemLiteral = 0 := rfl
theorem pc_pushMemU16 : stepPopCount qOpPushMemU16 = 0 := rfl
theorem pc_pushMemToken : stepPopCount qOpPushMemToken = 0 := rfl
theorem pc_pushMemTokenOffset : stepPopCount qOpPushMemTokenOffset = 0 := rfl
theorem pc_add : stepPopCount qOpAdd = 2 := rfl
theorem pc_mul : stepPopCount qOpMul = 2 := rfl
theorem pc_neg : stepPopCount qOpNeg = 1 := rfl
theorem pc_pow5 : stepPopCount qOpPow5 = 1 := rfl
theorem pc_addConstU8 : stepPopCount qOpAddConstU8 = 1 := rfl
theorem pc_mulConstU8 : stepPopCount qOpMulConstU8 = 1 := rfl
theorem pc_addConst : stepPopCount qOpAddConst = 1 := rfl
theorem pc_mulConst : stepPopCount qOpMulConst = 1 := rfl
theorem pc_addMemU16 : stepPopCount qOpAddMemU16 = 1 := rfl
theorem pc_mulMemU16 : stepPopCount qOpMulMemU16 = 1 := rfl
theorem pc_addMulMemMemConstU8 : stepPopCount qOpAddMulMemMemConstU8 = 1 := rfl
theorem pc_addMulConstU8MemU16 : stepPopCount qOpAddMulConstU8MemU16 = 1 := rfl
theorem pc_addMulMemMem : stepPopCount qOpAddMulMemMem = 1 := rfl
theorem pc_runP : stepPopCount qOpRunAddMulMemMemConstU8 = 1 := rfl
theorem pc_runL : stepPopCount qOpRunAddMulConstU8MemU16 = 1 := rfl
theorem pc_affineSum : stepPopCount qOpAffineSum = 1 := rfl
/-- The four excluded LIMB arms push, so their popCount is 0 and NO LIMB FACT IS NEEDED to say so. Stated
    here so the exclusion above is checkable rather than rhetorical. -/
theorem pc_lin7 : stepPopCount qOpLin7 = 0 := rfl
theorem pc_bilin7Row : stepPopCount qOpBilin7Row = 0 := rfl
theorem pc_bilin7Pairwise : stepPopCount qOpBilin7Pairwise = 0 := rfl
theorem pc_modarith7 : stepPopCount qOpModarith7 = 0 := rfl
theorem pc_stream5 : stepPopCount qOpFoldMain = 0 := rfl

/-- A stack at least one deep is a cons. Stated here because the axis hypothesis is a LENGTH bound and
    the reference's pops are STRUCTURAL, so the two only meet through a destructuring lemma. -/
theorem length_ge_one_cons {α : Type} (s : List α) (h : 1 ≤ s.length) : ∃ a r, s = a :: r := by
  cases s with
  | nil => exact absurd h (by simp)
  | cons a r => exact ⟨a, r, rfl⟩

theorem length_ge_two_cons {α : Type} (s : List α) (h : 2 ≤ s.length) : ∃ a b r, s = a :: b :: r := by
  cases s with
  | nil => exact absurd h (by simp)
  | cons a r =>
      cases r with
      | nil => exact absurd h (by simp)
      | cons b rr => exact ⟨a, b, rr, rfl⟩

/-! ### 2. The underflow-class predicate the tree never had -/

/-- **THE THIRD FAULT-CLASS PREDICATE.** QvmShift's two passes are per-fault-class predicates - 'NoRF'
    (Qvm.lean:1564) for 'readPastEnd' and 'OORSlot' (QvmShift.lean:2907) for 'constSlotOutOfRange' - and
    IDSEG reported that the underflow class has NO predicate at all, which is why nothing could state the
    depth bound per arm. 'NoUnderflow x' says the computation raises no 'QVMFault.stackUnderflow'. It is
    stated in the same shape as 'OORSlot' so the same bind-by-bind refinement reaches it, and for the
    same reason: the step is a chain of '>>=' over readers and pops, and evaluating it is not available
    at a general cursor. -/
def NoUnderflow {α : Type} (x : Except QVMFault α) : Prop :=
  ∀ j, x ≠ .error (QVMFault.stackUnderflow j)

namespace NoUnderflow

theorem ok {α : Type} (a : α) : NoUnderflow (Except.ok a) := by
  intro j h; cases h

theorem error {α : Type} (e : QVMFault) (h : ∀ j, e ≠ QVMFault.stackUnderflow j) :
    NoUnderflow (Except.error (α := α) e) := by
  intro j hh; exact h j (Except.error.inj hh)

theorem never {α : Type} {x : Except QVMFault α}
    (h : ∀ j, x ≠ .error (QVMFault.stackUnderflow j)) : NoUnderflow x := h

theorem bind {α β : Type} {x : Except QVMFault α} {f : α → Except QVMFault β}
    (hx : NoUnderflow x) (hf : ∀ a, NoUnderflow (f a)) : NoUnderflow (x >>= f) := by
  intro j h
  cases x with
  | ok a => exact hf a j h
  | error e => exact hx j (congrArg Except.error (Except.error.inj h))

theorem ite {α : Type} {c : Prop} [inst : Decidable c] {x y : Except QVMFault α}
    (hx : NoUnderflow x) (hy : NoUnderflow y) : NoUnderflow (if c then x else y) := by
  cases inst with
  | isTrue _ => exact hx
  | isFalse _ => exact hy

theorem pair_match {ε α β : Type} (e : ε × α) (f : ε → α → Except QVMFault β)
    (h : ∀ x y, NoUnderflow (f x y)) : NoUnderflow (match e with | (x, y) => f x y) := by
  cases e with
  | mk x y => exact h x y

/-- Endomorphic 'Except.map' only, and that is exactly what the two counted-fold bodies need:
    'runFoldL'/'runFoldP' (QvmShift.lean:983-991) map a term of type
    'QVMFr × Nat × QuotientRefMemory' to the SAME type. The general 'α → β' form needs a transport of
    'NoUnderflow' across the payload type, which is not what the axis asks for. -/
theorem except_map {α : Type} (g : α → α) {x : Except QVMFault α}
    (hx : NoUnderflow x) : NoUnderflow (Except.map g x) := by
  cases x with
  | ok a => exact NoUnderflow.ok _
  | error e =>
      refine NoUnderflow.error e ?_
      intro j hh
      exact hx j (congrArg Except.error hh)

theorem congr {α : Type} {x y : Except QVMFault α} (h : x = y) (hx : NoUnderflow x) :
    NoUnderflow y := h ▸ hx

end NoUnderflow

/-! ### 3. What can and cannot raise an underflow -/

/-- The bounds-checked byte reader never underflows: it does not touch the stack. -/
theorem byteAt_noUnderflow (bytes : List Nat) (k : Nat) :
    NoUnderflow (Midfall.Generator.byteAt bytes k) := by
  unfold Midfall.Generator.byteAt
  cases bytes.drop k with
  | cons b rest => exact NoUnderflow.ok _
  | nil => exact NoUnderflow.error _ (by intro j hh; cases hh)

theorem readU16_noUnderflow (bytes : List Nat) (k : Nat) :
    NoUnderflow (Midfall.Generator.readU16 bytes k) := by
  unfold Midfall.Generator.readU16
  refine NoUnderflow.bind (byteAt_noUnderflow bytes k) (fun _ =>
    NoUnderflow.bind (byteAt_noUnderflow bytes (k + 1)) (fun _ => NoUnderflow.ok _))

theorem readU32_noUnderflow (bytes : List Nat) (k : Nat) :
    NoUnderflow (Midfall.Generator.readU32 bytes k) := by
  unfold Midfall.Generator.readU32
  refine NoUnderflow.bind (byteAt_noUnderflow bytes k) (fun _ =>
    NoUnderflow.bind (byteAt_noUnderflow bytes (k + 1)) (fun _ =>
      NoUnderflow.bind (byteAt_noUnderflow bytes (k + 2)) (fun _ =>
        NoUnderflow.bind (byteAt_noUnderflow bytes (k + 3)) (fun _ => NoUnderflow.ok _))))

/-- The constant-table reader never underflows. Its 'fqFromU256' rejection is the 'panic' class the
    row's 'hconsts' is about - a DIFFERENT fault, which is why the SLOT axis and the DEPTH axis are
    independent obligations even though both are about 'constAt'. -/
theorem constAt_noUnderflow (consts : List Word256) (slot idx : Nat) :
    NoUnderflow (Midfall.Generator.constAt consts slot idx) := by
  unfold Midfall.Generator.constAt
  cases consts.drop slot with
  | cons v rest =>
      unfold Midfall.Generator.fqFromU256
      by_cases h : BitVec.toNat v < qvmFrModulus
      · simp [h]
        exact NoUnderflow.ok _
      · simp [h]
        exact NoUnderflow.error _ (by intro j hh; cases hh)
  | nil => exact NoUnderflow.error _ (by intro j hh; cases hh)

theorem indexOrPanic_noUnderflow (bytes : List Nat) (k : Nat) :
    NoUnderflow (Midfall.Generator.indexOrPanic bytes k) := by
  unfold Midfall.Generator.indexOrPanic
  cases bytes.drop k with
  | cons b rest => exact NoUnderflow.ok _
  | nil => exact NoUnderflow.error _ (by intro j hh; cases hh)

/-- THE ONLY THING IN THE STEP THAT UNDERFLOWS, and exactly when: 'popStack' raises
    'stackUnderflow idx' on the EMPTY stack and on nothing else. This single lemma is the reason the
    per-arm popCount is the whole story on this axis - every other fault the step can raise comes from a
    reader or an explicit throw, and those are the other axes' business. -/
theorem popStack_noUnderflow (v : QVMFr) (rest : List QVMFr) (idx : Nat) :
    NoUnderflow (Midfall.Generator.popStack (v :: rest) idx) := by
  unfold Midfall.Generator.popStack
  exact NoUnderflow.ok _

theorem popStack_underflows_only_nil (stack : List QVMFr) (idx j : Nat)
    (h : Midfall.Generator.popStack stack idx = .error (QVMFault.stackUnderflow j)) :
    stack = [] ∧ j = idx := by
  cases stack with
  | nil =>
      have h2 : Midfall.Generator.popStack ([] : List QVMFr) idx =
          .error (QVMFault.stackUnderflow idx) := rfl
      rw [h2] at h
      have h3 := Except.error.inj h
      cases h3
      exact ⟨rfl, rfl⟩
  | cons v rest =>
      have h2 : Midfall.Generator.popStack (v :: rest) idx = .ok (v, rest) := rfl
      rw [h2] at h
      exact absurd h (by intro hh; cases hh)

/-- The counted fold never underflows whatever its accumulator is: the stack is not part of the state it
    threads (RUN and AFFINE_SUM thread '(acc, used, mem)'), so a fold cannot pop. Mirrors
    'foldRangeIdxM_oorSlot' (QvmShift.lean:3008). -/
theorem foldRangeIdxM_noUnderflow {α : Type} :
    ∀ (n : Nat) (init : α) (f : Nat → α → Except QVMFault α),
      (∀ i s, NoUnderflow (f i s)) → NoUnderflow (Midfall.Generator.foldRangeIdxM n init f) := by
  intro n
  induction n with
  | zero => intro init f _; exact NoUnderflow.ok _
  | succ k ih =>
      intro init f hf
      have hgo : Midfall.Generator.foldRangeIdxM (k + 1) init f =
          (f 0 init >>= (fun x =>
            Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>= (fun y => Except.ok y))) := rfl
      rw [hgo]
      refine NoUnderflow.bind (hf 0 init) (fun x => ?_)
      show NoUnderflow (Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>=
        fun y => Except.ok y)
      exact NoUnderflow.bind (ih x (fun i => f (i + 1)) (fun i s => hf (i + 1) s))
        (fun _ => NoUnderflow.ok _)

theorem affineLinearTerm_noUnderflow {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    NoUnderflow (Midfall.Generator.affineLinearTerm bytes consts mem k) := by
  unfold Midfall.Generator.affineLinearTerm
  refine NoUnderflow.bind (readU16_noUnderflow bytes k) (fun _ =>
    NoUnderflow.bind (byteAt_noUnderflow bytes (k + 2)) (fun _ =>
      NoUnderflow.bind (constAt_noUnderflow consts _ k) (fun _ => NoUnderflow.ok _)))

theorem affineProductTerm_noUnderflow {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    NoUnderflow (Midfall.Generator.affineProductTerm bytes consts mem k) := by
  unfold Midfall.Generator.affineProductTerm
  refine NoUnderflow.bind (readU16_noUnderflow bytes k) (fun _ =>
    NoUnderflow.bind (readU16_noUnderflow bytes (k + 2)) (fun _ =>
      NoUnderflow.bind (byteAt_noUnderflow bytes (k + 4)) (fun _ =>
        NoUnderflow.bind (constAt_noUnderflow consts _ k) (fun _ => NoUnderflow.ok _))))


/-! ### 4. THE INTERPRETER HALF: a step whose stack is deep enough cannot underflow -/

/-- THE SIX PUSH ARMS: 'VmReference.lean:733-757'. None of them pops, so none can underflow, at ANY stack
    and ANY cursor - the bound 'stepPopCount = 0' is vacuous here and that is the point: the arms the
    validator's push group accepts at depth 0 are exactly the arms the interpreter runs at depth 0. -/
theorem step_noUF_pushConst (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (constAt_noUnderflow consts _ idx) (fun _ => NoUnderflow.ok _))

theorem step_noUF_pushConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (byteAt_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (constAt_noUnderflow consts _ idx) (fun _ => NoUnderflow.ok _))

theorem step_noUF_pushMemLiteral (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemLiteral stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU32_noUnderflow bytes (idx + 1)) (fun _ => NoUnderflow.ok _)

theorem step_noUF_pushMemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ => NoUnderflow.ok _)

theorem step_noUF_pushMemToken (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemToken stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (byteAt_noUnderflow bytes (idx + 1)) (fun _ => NoUnderflow.ok _)

theorem step_noUF_pushMemTokenOffset (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemTokenOffset stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (byteAt_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (readU32_noUnderflow bytes (idx + 2)) (fun _ => NoUnderflow.ok _))

/-- ADD and MUL: two pops, so two values are needed - and two are enough, whatever the cursor or the
    bytes, because neither arm reads a byte before it pops ('VmReference.lean:758-765'). This is the arm
    QvmShift.lean:759 'shift_bare_equation_is_false_no_bytes' uses to show a step DOES underflow on a
    short stack, so the bound here is tight, not merely sound. -/
theorem step_noUF_add (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 2 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAdd stack mem) := by
  obtain ⟨a, b, rest, rfl⟩ := length_ge_two_cons stack h
  -- Two cons cells let this arm be EVALUATED outright: neither ADD nor MUL reads a byte, so the two
  -- pops are its only fault sources and both succeed. The computed '.ok' is the shape 'demo_step2'
  -- (QvmSegment.lean:532) already uses, and an '.ok' step cannot underflow by construction.
  have hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAdd
      (a :: b :: rest) mem
      = .ok { stack := qvmFrAdd b a :: rest, consumed := 1, hConsumed := Nat.succ_pos 0, mem := mem } := by
    show (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAdd (a :: b :: rest) mem) = _
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rfl
  rw [hstep]
  exact NoUnderflow.ok _

theorem step_noUF_mul (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 2 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMul stack mem) := by
  obtain ⟨a, b, rest, rfl⟩ := length_ge_two_cons stack h
  -- Two cons cells let this arm be EVALUATED outright: neither ADD nor MUL reads a byte, so the two
  -- pops are its only fault sources and both succeed. The computed '.ok' is the shape 'demo_step2'
  -- (QvmSegment.lean:532) already uses, and an '.ok' step cannot underflow by construction.
  have hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMul
      (a :: b :: rest) mem
      = .ok { stack := qvmFrMul b a :: rest, consumed := 1, hConsumed := Nat.succ_pos 0, mem := mem } := by
    show (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMul (a :: b :: rest) mem) = _
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rfl
  rw [hstep]
  exact NoUnderflow.ok _

/-- NEG and POW5: one pop, no byte read ('VmReference.lean:766-775'). -/
theorem step_noUF_neg (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpNeg stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)

theorem step_noUF_pow5 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPow5 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)

/-- The four const-operand accumulator arms: the operand read comes FIRST, so a short stack can be
    shadowed by a read or slot fault - which is why the reference's own 'errorPrecedence_ok' pins the
    order and why the DEPTH axis is a one-sided bound, not a characterisation. One pop either way, so
    one value is enough. -/
theorem step_noUF_addConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddConstU8 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (byteAt_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (constAt_noUnderflow consts _ idx) (fun _ =>
      NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)))

theorem step_noUF_mulConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulConstU8 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (byteAt_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (constAt_noUnderflow consts _ idx) (fun _ =>
      NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)))

theorem step_noUF_addConst (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddConst stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (constAt_noUnderflow consts _ idx) (fun _ =>
      NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)))

theorem step_noUF_mulConst (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulConst stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (constAt_noUnderflow consts _ idx) (fun _ =>
      NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)))

/-- The two memory-operand accumulator arms: the reference reads the memory value BEFORE popping
    ('VmReference.lean:788-795', and the comment there says the Rust caches the address even on a
    truncated stack). Memory reads are not faults at all, so the pop count is still one. -/
theorem step_noUF_addMemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMemU16 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _))

theorem step_noUF_mulMemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulMemU16 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _))

/-- The three fused arms. 'ADD_MUL_MEM_MEM_CONST_U8' and 'ADD_MUL_CONST_U8_MEM_U16' pop FIRST and then
    decode a term ('VmReference.lean:796-805'); 'ADD_MUL_MEM_MEM' reads two pointers, pops, then reads
    two literals (:806-813). One value in every case. -/
theorem step_noUF_addMulMemMemConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAddMulMemMemConstU8 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ =>
    NoUnderflow.bind (affineProductTerm_noUnderflow (bytes := bytes) (mem := mem)
      (k := idx + 1)) (fun _ => NoUnderflow.ok _))

theorem step_noUF_addMulConstU8MemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAddMulConstU8MemU16 stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ =>
    NoUnderflow.bind (affineLinearTerm_noUnderflow (bytes := bytes) (mem := mem)
      (k := idx + 1)) (fun _ => NoUnderflow.ok _))

theorem step_noUF_addMulMemMem (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAddMulMemMem stack mem) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (readU16_noUnderflow bytes (idx + 3)) (fun _ =>
      NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun _ => NoUnderflow.ok _)))

/-- THE COUNTED FOLDS CANNOT UNDERFLOW: 'runFoldL'/'runFoldP' (QvmShift.lean:983-991) thread the state
    '(acc, used, mem)' - the stack is not in it - and their only fault source is the affine term decoder
    inside an endomorphic 'Except.map'. This is the lemma the RUN and AFFINE_SUM arms reduce to. -/
theorem runFoldL_noUnderflow (bytes : List Nat) (consts : List Word256) (base : Nat) :
    ∀ i s, NoUnderflow (runFoldL bytes consts base i s) := by
  intro i s
  unfold QvmShift.runFoldL
  refine NoUnderflow.except_map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
    (affineLinearTerm_noUnderflow (bytes := bytes) (mem := s.2.2) (k := base + s.2.1))

theorem runFoldP_noUnderflow (bytes : List Nat) (consts : List Word256) (base : Nat) :
    ∀ i s, NoUnderflow (runFoldP bytes consts base i s) := by
  intro i s
  unfold QvmShift.runFoldP
  refine NoUnderflow.except_map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
    (affineProductTerm_noUnderflow (bytes := bytes) (mem := s.2.2) (k := base + s.2.1))

/-- THE RUN ARMS, through QvmShift's def bridge: 'step_eq_runArmBody'/'_L' are 'rfl' bridges onto
    'runArmBody', so the arm is refined once for both opcodes instead of twice. The count test is an
    'ite' whose 'else' branch is the 'zeroLengthRun' throw - a DIFFERENT fault class, which is why the
    SHAPE axis and the DEPTH axis stay separate obligations even on the same arm. -/
theorem runArmBody_noUnderflow (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (F : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (h : 1 ≤ stack.length) (hF : ∀ i s, NoUnderflow (F i s)) :
    NoUnderflow (runArmBody bytes consts idx stack mem F) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold QvmShift.runArmBody
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun count =>
    NoUnderflow.ite
      (NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun p =>
        NoUnderflow.bind
          (foldRangeIdxM_noUnderflow count (p.1, 0, mem) F hF) (fun _ => NoUnderflow.ok _)))
      (NoUnderflow.error _ (by intro j hh; cases hh)))

theorem step_noUF_runP (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulMemMemConstU8 stack mem) := by
  rw [step_eq_runArmBody]
  refine runArmBody_noUnderflow bytes consts idx stack mem
    (runFoldP bytes consts (idx + 3)) h (runFoldP_noUnderflow bytes consts (idx + 3))

theorem step_noUF_runL (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulConstU8MemU16 stack mem) := by
  rw [step_eq_runArmBodyL]
  refine runArmBody_noUnderflow bytes consts idx stack mem
    (runFoldL bytes consts (idx + 3)) h (runFoldL_noUnderflow bytes consts (idx + 3))

/-- AFFINE_SUM: two count reads, the zero-count test, one pop, then the two counted folds
    ('VmReference.lean:831-849'). One value needed; the fold bodies cannot pop. -/
theorem affineSumArmBody_noUnderflow (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (Fl Fp : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (h : 1 ≤ stack.length) (hl : ∀ i s, NoUnderflow (Fl i s))
    (hp : ∀ i s, NoUnderflow (Fp i s)) :
    NoUnderflow (affineSumArmBody bytes consts idx stack mem Fl Fp) := by
  obtain ⟨a, rest, rfl⟩ := length_ge_one_cons stack h
  unfold QvmShift.affineSumArmBody
  refine NoUnderflow.bind (readU16_noUnderflow bytes (idx + 1)) (fun _ =>
    NoUnderflow.bind (readU16_noUnderflow bytes (idx + 3)) (fun _ =>
      NoUnderflow.ite
        (NoUnderflow.bind (popStack_noUnderflow a rest idx) (fun p =>
          NoUnderflow.bind (foldRangeIdxM_noUnderflow _ (p.1, 0, mem) Fl hl) (fun x =>
            NoUnderflow.bind (foldRangeIdxM_noUnderflow _ (x.1, x.2.1, x.2.2) Fp hp)
              (fun _ => NoUnderflow.ok _))))
        (NoUnderflow.error _ (by intro j hh; cases hh))))

theorem step_noUF_affineSum (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : 1 ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAffineSum stack mem) := by
  rw [step_eq_affineSumArmBody]
  refine affineSumArmBody_noUnderflow bytes consts idx stack mem
    (runFoldL bytes consts (idx + 5)) (runFoldP bytes consts (idx + 5)) h
    (runFoldL_noUnderflow bytes consts (idx + 5)) (runFoldP_noUnderflow bytes consts (idx + 5))

/-- **THE INTERPRETER HALF, 22 ARMS AT A GENERAL CURSOR.** The hypothesis is the popCount bound in the
    shape IDSEG predicted ('QvmSegment.lean:365': "discharged from a hypothesis of the shape
    'stack.length >= popCount op' for a per-arm 'popCount'"), and the conclusion is exactly the DEPTH
    axis's per-arm content. MODARITH7 and the other three LIMB arms are outside 'stepArm22' by
    instruction; the five stream opcodes are covered separately below. -/
theorem evalQuotientIdentityStep_noUnderflow_22
    (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : stepArm22 op) (h : stepPopCount op ≤ stack.length) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem) := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h; rw [pc_pushConst] at h; exact step_noUF_pushConst bytes consts idx stack mem
  · subst h; rw [pc_pushConstU8] at h; exact step_noUF_pushConstU8 bytes consts idx stack mem
  · subst h; rw [pc_pushMemLiteral] at h
    exact step_noUF_pushMemLiteral bytes consts idx stack mem
  · subst h; rw [pc_pushMemU16] at h; exact step_noUF_pushMemU16 bytes consts idx stack mem
  · subst h; rw [pc_pushMemToken] at h; exact step_noUF_pushMemToken bytes consts idx stack mem
  · subst h; rw [pc_pushMemTokenOffset] at h
    exact step_noUF_pushMemTokenOffset bytes consts idx stack mem
  · subst h; rw [pc_add] at h; exact step_noUF_add bytes consts idx stack mem h
  · subst h; rw [pc_mul] at h; exact step_noUF_mul bytes consts idx stack mem h
  · subst h; rw [pc_neg] at h; exact step_noUF_neg bytes consts idx stack mem h
  · subst h; rw [pc_pow5] at h; exact step_noUF_pow5 bytes consts idx stack mem h
  · subst h; rw [pc_addConstU8] at h; exact step_noUF_addConstU8 bytes consts idx stack mem h
  · subst h; rw [pc_mulConstU8] at h; exact step_noUF_mulConstU8 bytes consts idx stack mem h
  · subst h; rw [pc_addConst] at h; exact step_noUF_addConst bytes consts idx stack mem h
  · subst h; rw [pc_mulConst] at h; exact step_noUF_mulConst bytes consts idx stack mem h
  · subst h; rw [pc_addMemU16] at h; exact step_noUF_addMemU16 bytes consts idx stack mem h
  · subst h; rw [pc_mulMemU16] at h; exact step_noUF_mulMemU16 bytes consts idx stack mem h
  · subst h; rw [pc_addMulMemMemConstU8] at h
    exact step_noUF_addMulMemMemConstU8 bytes consts idx stack mem h
  · subst h; rw [pc_addMulConstU8MemU16] at h
    exact step_noUF_addMulConstU8MemU16 bytes consts idx stack mem h
  · subst h; rw [pc_addMulMemMem] at h; exact step_noUF_addMulMemMem bytes consts idx stack mem h
  · subst h; rw [pc_runP] at h; exact step_noUF_runP bytes consts idx stack mem h
  · subst h; rw [pc_runL] at h; exact step_noUF_runL bytes consts idx stack mem h
  · subst h; rw [pc_affineSum] at h; exact step_noUF_affineSum bytes consts idx stack mem h

/-- THE FIVE STREAM ARMS NEVER UNDERFLOW AT ALL, at any depth: 'VmReference.lean:862-866' refuses them
    with 'streamOpcodeInIdentity' before touching the stack. Recorded here because the DEPTH axis
    quantifies over whatever opcode the cursor holds, and because it is what makes the validator's
    'stackBoundary'/'nativeCallbackStack' requirements irrelevant to underflow: those two groups are the
    only ones whose requirement is an EXACT equality rather than a lower bound, and they cannot underflow
    in the reference even so. -/
theorem step_noUnderflow_stream5 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (op : Nat) (stack : List QVMFr) (mem : QuotientRefMemory) (hop : stepArmStream5 op) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem) := by
  rcases hop with (h|h|h|h|h) <;> subst h
  all_goals
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    exact NoUnderflow.error _ (by intro j hh; cases hh)

theorem vpop_pushConst {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushConst idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPushConst ≤ depth ∧ d' = depth - stepPopCount qOpPushConst + 1 := by
  rw [pc_pushConst]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushConst idx depth ms =
      .ok (depth + 1, Nat.max ms (depth + 1)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
    have hnot : ¬ (depth + 1 < depth) := by omega
    simp (config := {decide := true}) only [reduceIte, hnot]
  rw [key] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by omega, by omega⟩

theorem vpop_pushConstU8 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushConstU8 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPushConstU8 ≤ depth ∧ d' = depth - stepPopCount qOpPushConstU8 + 1 := by
  rw [pc_pushConstU8]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushConstU8 idx depth ms =
      .ok (depth + 1, Nat.max ms (depth + 1)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
    have hnot : ¬ (depth + 1 < depth) := by omega
    simp (config := {decide := true}) only [reduceIte, hnot]
  rw [key] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by omega, by omega⟩

theorem vpop_pushMemLiteral {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemLiteral idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPushMemLiteral ≤ depth ∧ d' = depth - stepPopCount qOpPushMemLiteral + 1 := by
  rw [pc_pushMemLiteral]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemLiteral idx depth ms =
      .ok (depth + 1, Nat.max ms (depth + 1)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
    have hnot : ¬ (depth + 1 < depth) := by omega
    simp (config := {decide := true}) only [reduceIte, hnot]
  rw [key] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by omega, by omega⟩

theorem vpop_pushMemU16 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemU16 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPushMemU16 ≤ depth ∧ d' = depth - stepPopCount qOpPushMemU16 + 1 := by
  rw [pc_pushMemU16]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemU16 idx depth ms =
      .ok (depth + 1, Nat.max ms (depth + 1)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
    have hnot : ¬ (depth + 1 < depth) := by omega
    simp (config := {decide := true}) only [reduceIte, hnot]
  rw [key] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by omega, by omega⟩

theorem vpop_pushMemToken {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemToken idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPushMemToken ≤ depth ∧ d' = depth - stepPopCount qOpPushMemToken + 1 := by
  rw [pc_pushMemToken]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemToken idx depth ms =
      .ok (depth + 1, Nat.max ms (depth + 1)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
    have hnot : ¬ (depth + 1 < depth) := by omega
    simp (config := {decide := true}) only [reduceIte, hnot]
  rw [key] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by omega, by omega⟩

theorem vpop_pushMemTokenOffset {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemTokenOffset idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPushMemTokenOffset ≤ depth ∧ d' = depth - stepPopCount qOpPushMemTokenOffset + 1 := by
  rw [pc_pushMemTokenOffset]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPushMemTokenOffset idx depth ms =
      .ok (depth + 1, Nat.max ms (depth + 1)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
    have hnot : ¬ (depth + 1 < depth) := by omega
    simp (config := {decide := true}) only [reduceIte, hnot]
  rw [key] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by omega, by omega⟩

theorem vpop_add {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAdd idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAdd ≤ depth ∧ d' = depth - stepPopCount qOpAdd + 1 := by
  rw [pc_add]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAdd idx depth ms =
      (if depth < 2
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAdd idx 2 depth)
        else .ok (depth - 1, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 2
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 2
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_mul {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMul idx depth ms = .ok (d', ms')) :
    stepPopCount qOpMul ≤ depth ∧ d' = depth - stepPopCount qOpMul + 1 := by
  rw [pc_mul]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMul idx depth ms =
      (if depth < 2
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpMul idx 2 depth)
        else .ok (depth - 1, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 2
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 2
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_neg {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpNeg idx depth ms = .ok (d', ms')) :
    stepPopCount qOpNeg ≤ depth ∧ d' = depth - stepPopCount qOpNeg + 1 := by
  rw [pc_neg]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpNeg idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpNeg idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_pow5 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPow5 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpPow5 ≤ depth ∧ d' = depth - stepPopCount qOpPow5 + 1 := by
  rw [pc_pow5]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPow5 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpPow5 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_addConstU8 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddConstU8 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAddConstU8 ≤ depth ∧ d' = depth - stepPopCount qOpAddConstU8 + 1 := by
  rw [pc_addConstU8]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddConstU8 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAddConstU8 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_mulConstU8 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMulConstU8 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpMulConstU8 ≤ depth ∧ d' = depth - stepPopCount qOpMulConstU8 + 1 := by
  rw [pc_mulConstU8]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMulConstU8 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpMulConstU8 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_addConst {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddConst idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAddConst ≤ depth ∧ d' = depth - stepPopCount qOpAddConst + 1 := by
  rw [pc_addConst]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddConst idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAddConst idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_mulConst {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMulConst idx depth ms = .ok (d', ms')) :
    stepPopCount qOpMulConst ≤ depth ∧ d' = depth - stepPopCount qOpMulConst + 1 := by
  rw [pc_mulConst]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMulConst idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpMulConst idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_addMemU16 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMemU16 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAddMemU16 ≤ depth ∧ d' = depth - stepPopCount qOpAddMemU16 + 1 := by
  rw [pc_addMemU16]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMemU16 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAddMemU16 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_mulMemU16 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMulMemU16 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpMulMemU16 ≤ depth ∧ d' = depth - stepPopCount qOpMulMemU16 + 1 := by
  rw [pc_mulMemU16]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMulMemU16 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpMulMemU16 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_addMulMemMemConstU8 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMulMemMemConstU8 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAddMulMemMemConstU8 ≤ depth ∧ d' = depth - stepPopCount qOpAddMulMemMemConstU8 + 1 := by
  rw [pc_addMulMemMemConstU8]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMulMemMemConstU8 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAddMulMemMemConstU8 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_addMulConstU8MemU16 {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMulConstU8MemU16 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAddMulConstU8MemU16 ≤ depth ∧ d' = depth - stepPopCount qOpAddMulConstU8MemU16 + 1 := by
  rw [pc_addMulConstU8MemU16]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMulConstU8MemU16 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAddMulConstU8MemU16 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_addMulMemMem {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMulMemMem idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAddMulMemMem ≤ depth ∧ d' = depth - stepPopCount qOpAddMulMemMem + 1 := by
  rw [pc_addMulMemMem]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAddMulMemMem idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAddMulMemMem idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_runP {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpRunAddMulMemMemConstU8 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpRunAddMulMemMemConstU8 ≤ depth ∧ d' = depth - stepPopCount qOpRunAddMulMemMemConstU8 + 1 := by
  rw [pc_runP]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpRunAddMulMemMemConstU8 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpRunAddMulMemMemConstU8 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_runL {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpRunAddMulConstU8MemU16 idx depth ms = .ok (d', ms')) :
    stepPopCount qOpRunAddMulConstU8MemU16 ≤ depth ∧ d' = depth - stepPopCount qOpRunAddMulConstU8MemU16 + 1 := by
  rw [pc_runL]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpRunAddMulConstU8MemU16 idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpRunAddMulConstU8MemU16 idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

theorem vpop_affineSum {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAffineSum idx depth ms = .ok (d', ms')) :
    stepPopCount qOpAffineSum ≤ depth ∧ d' = depth - stepPopCount qOpAffineSum + 1 := by
  rw [pc_affineSum]
  have key : Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAffineSum idx depth ms =
      (if depth < 1
        then .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAffineSum idx 1 depth)
        else .ok (depth, ms)) := by
    unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect Midfall.Generator.QuotientValidator.requireQuotientStackDepth
    simp (config := {decide := true}) only [reduceIte]
    by_cases hlt : depth < 1
    · simp [hlt]; rfl
    · simp [hlt]; rfl
  rw [key] at h
  by_cases hlt : depth < 1
  · simp [hlt] at h
  · simp [hlt] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega⟩

/-- **THE VALIDATOR HALF, 22 ARMS - THE EQUATION IDSEG NAMED AS OWED.** For every covered opcode: if the
    validator's own depth fold ACCEPTS it at depth 'depth' - i.e. 'applyQuotientStackEffect op idx depth
    maxStack' succeeds, which is the step 'validateQuotientProgramGo' (VmValidator.lean:886) performs at
    that cursor - then the fold required at least 'stepPopCount op', and the depth it computed for the
    next cursor is exactly 'depth - stepPopCount op + 1'. The second conjunct is why the popCount is not
    merely a safe over-estimate: it is the number the validator's own table subtracts, read off
    'applyQuotientStackEffect' (VmValidator.lean:731-741) rather than assumed. -/
theorem validator_popCount_22 (op : Nat) (hop : stepArm22 op) {idx depth ms d' ms' : Nat}
    (h : Midfall.Generator.QuotientValidator.applyQuotientStackEffect op idx depth ms = .ok (d', ms')) :
    stepPopCount op ≤ depth ∧ d' = depth - stepPopCount op + 1 := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h; exact vpop_pushConst h
  · subst h; exact vpop_pushConstU8 h
  · subst h; exact vpop_pushMemLiteral h
  · subst h; exact vpop_pushMemU16 h
  · subst h; exact vpop_pushMemToken h
  · subst h; exact vpop_pushMemTokenOffset h
  · subst h; exact vpop_add h
  · subst h; exact vpop_mul h
  · subst h; exact vpop_neg h
  · subst h; exact vpop_pow5 h
  · subst h; exact vpop_addConstU8 h
  · subst h; exact vpop_mulConstU8 h
  · subst h; exact vpop_addConst h
  · subst h; exact vpop_mulConst h
  · subst h; exact vpop_addMemU16 h
  · subst h; exact vpop_mulMemU16 h
  · subst h; exact vpop_addMulMemMemConstU8 h
  · subst h; exact vpop_addMulConstU8MemU16 h
  · subst h; exact vpop_addMulMemMem h
  · subst h; exact vpop_runP h
  · subst h; exact vpop_runL h
  · subst h; exact vpop_affineSum h

/-! ### 6. The composition, the fold re-entered at a cursor, and the axis discharged -/

/-- **THE GAP CLOSED AT ONE CURSOR.** This is the sentence the brief asked for: the reference step's stack
    requirement at cursor 'idx' is bounded by the depth the validator's own fold computed there. The
    hypotheses are the two halves and nothing else - 'hv' is the validator's fold accepting the opcode at
    depth 'd' (the step 'validateQuotientProgramGo' performs at that cursor), 'hle' is the stack
    correspondence at that cursor, 'hh' names the opcode the cursor holds in the shape IDSEG's own per-arm
    goal state uses ('QvmSegment.lean:361', 'op = bytes.getD idx 0'). No hypothesis was added to a row, to
    'ValidV3', to a bundle or to the root: this is a standalone Prop with hypotheses on an ARM-level fact,
    which RULES allows explicitly. -/
theorem step_noUnderflow_of_validator_fold {bytes consts idx op stack mem d d' ms'}
    (hop : stepArm22 op) (hh : bytes.getD idx 0 = op)
    (hv : Midfall.Generator.QuotientValidator.applyQuotientStackEffect op idx d 0 = .ok (d', ms'))
    (hle : d ≤ stack.length) :
    NoUnderflow (stepAt bytes consts idx stack mem) := by
  obtain ⟨hpc, _⟩ := validator_popCount_22 op hop hv
  rw [stepAt_def, hh]
  exact evalQuotientIdentityStep_noUnderflow_22 bytes consts idx op stack mem hop
    (Nat.le_trans hpc hle)

/-- **THE VALIDATOR'S DEPTH FOLD, RE-ENTERED AT A CURSOR.** The inductive form of the computation
    'validateQuotientProgramGo' (VmValidator.lean:876-887) performs, stopped at one cursor: the walk from
    'start' reaches 'target' and there the validator's own decoder names 'op' and its own stack-effect
    table accepts 'op' at depth 'd'. Stated as a relation rather than as a fuel-indexed function because
    then the certification IS the constructor - no fuel induction stands between the fold and the
    equation - and because DQVM2's 'qSegmentDepthGo' (QuotientInterp.lean:1120) already owns the
    functional form on the end-depth, which this card cites rather than rebuilds. -/
inductive FoldDepth : List Nat → Nat → Nat → Nat → Nat → Prop where
  /-- The walk is AT the target: the validator decodes 'op' there and its depth table accepts 'op' at
      depth 'd'. -/
  | here {bytes start target op len d d' ms'}
      (hstart : start ≤ target)
      (hdec : Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes target = .ok (op, len))
      (heff : Midfall.Generator.QuotientValidator.applyQuotientStackEffect op target d 0 = .ok (d', ms')) :
      FoldDepth bytes start target op d
  /-- The walk is one instruction short of the target: decode and accept at 'start', then continue from
      'start + len' at the depth the table computed. -/
  | next {bytes start target op len d d' ms' op'}
      (hdec : Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes start = .ok (op, len))
      (heff : Midfall.Generator.QuotientValidator.applyQuotientStackEffect op start d 0 = .ok (d', ms'))
      (hnext : FoldDepth bytes (start + len) target op' d') :
      FoldDepth bytes start target op' d'

/-- The fold's depth at the target, transported along the walk: at every cursor the relation names, the
    validator accepted the opcode there at the depth it carried. -/
theorem foldDepth_certifies {bytes start target op d}
    (h : FoldDepth bytes start target op d) :
    ∃ (len d' ms' : Nat),
      Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes target = .ok (op, len) ∧
        Midfall.Generator.QuotientValidator.applyQuotientStackEffect op target d 0 = .ok (d', ms') := by
  induction h with
  | here _ hdec heff => exact ⟨_, _, _, hdec, heff⟩
  | next _ _ _ hrec => exact hrec

/-- The fold's depth at the target, transported along the walk: at every cursor the relation names, the
    validator accepted the opcode there at the depth it carried, so the composition applies. -/
theorem noUnderflow_of_FoldDepth {bytes start target op d consts stack mem}
    (h : FoldDepth bytes start target op d) (hh : bytes.getD target 0 = op)
    (hop : stepArm22 op) (hle : d ≤ stack.length) :
    NoUnderflow (stepAt bytes consts target stack mem) := by
  obtain ⟨_len, _d', _ms', _hdec, heff⟩ := foldDepth_certifies h
  exact step_noUnderflow_of_validator_fold hop hh heff hle

/-- **THE AXIS DISCHARGED, PRIMARY FORM.** 'PG_stepDepth_at' from the hypothesis shape IDSEG predicted
    ('QvmSegment.lean:365'): at every reachable cursor the opcode is a covered arm and the stack is at
    least 'stepPopCount' deep. What this card supplies is the content of that hypothesis - the popCount,
    the interpreter half and the validator half - so the remaining obligation for the emitter card is one
    named line about its own cursor sequence, not an unnamed gap in the interpreter. -/
theorem PG_stepDepth_at_of_popCount_le (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (h : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        stepArm22 (bytes.getD idx 0) ∧ stepPopCount (bytes.getD idx 0) ≤ stack.length) :
    PG_stepDepth_at bytes consts P := by
  intro idx stack mem hidx hP j
  obtain ⟨hop, hle⟩ := h idx stack mem hidx hP
  rw [stepAt_def]
  exact evalQuotientIdentityStep_noUnderflow_22 bytes consts idx (bytes.getD idx 0) stack mem hop hle j

/-- **THE AXIS DISCHARGED FROM THE VALIDATOR'S OWN FOLD.** The same conclusion with the depth bound
    supplied by 'FoldDepth' instead of by hand: a segment whose validator walk reaches every cursor the
    walk-invariant predicate holds at, at a depth the interpreter's stack matches, satisfies the DEPTH
    axis. This is the form the emitter card can actually cite, because 'FoldDepth' talks about the bytes
    alone. -/
theorem PG_stepDepth_at_of_validator_fold (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hfold : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ op d, bytes.getD idx 0 = op ∧ stepArm22 op ∧ FoldDepth bytes 0 idx op d
          ∧ d ≤ stack.length) :
    PG_stepDepth_at bytes consts P := by
  intro idx stack mem hidx hP j
  obtain ⟨op, d, hh, hop, hf, hle⟩ := hfold idx stack mem hidx hP
  rw [stepAt]
  exact noUnderflow_of_FoldDepth hf hh hop hle j

/-- **THE AXIS HOLDS FOR A REAL SEGMENT.** IDSEG's own five-byte witness - two 'PUSH_CONST_U8' and an
    'ADD' - with its own 'demoP'. The DEPTH axis is therefore not a named hole any more: it has a proof
    for a concrete emitted-shape segment, discharged through the per-arm lemmas above rather than by
    evaluating the interpreter by hand. -/
theorem demoPG_stepDepth_at : PG_stepDepth_at demoSegment demoConsts demoP := by
  intro idx stack mem hidx hP j
  rw [demo_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, hl⟩)
  · subst hs
    rw [demo_step0 mem]
    exact NoUnderflow.ok _ j
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    rw [demo_step1 [a] mem]
    exact NoUnderflow.ok _ j
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    rw [demo_step2 a b mem]
    exact NoUnderflow.ok _ j
  · omega

/-- **THE BOUND IS NEEDED, NOT INVENTED.** 'ADD' on an empty stack really does raise
    'QVMFault.stackUnderflow', so the axis is not vacuously satisfiable by an interpreter that never
    underflows: the popCount bounds a fault the reference can actually produce. QvmShift's
    'shift_bare_equation_is_false_no_bytes' (QvmShift.lean:759) is the same fact used to refute a stronger
    claim; this is the witness inside this card's own vocabulary. -/
theorem depth_axis_not_vacuous :
    Midfall.Generator.evalQuotientIdentityStep [qOpAdd] ([] : List Word256) 0 qOpAdd
        ([] : List QVMFr) demoMem = .error (QVMFault.stackUnderflow 0) := rfl

/-- And the validator's fold refuses that program at depth 1 and accepts it at depth 2, which is the
    equation holding on a live pair of inputs rather than on an empty type. -/
theorem validator_fold_agrees_on_the_witness :
    Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAdd 0 2 0 = .ok (1, 0) ∧
      Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAdd 0 1 0 =
        .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.stackUnderflow qOpAdd 0 2 1) := by
  refine ⟨rfl, rfl⟩

/-- **THE FOUR EXCLUDED LIMB ARMS, NAMED WITH THEIR EXACT GOAL STATE.** Excluded by instruction, not by
    necessity, and the exclusion is worth recording precisely because on THIS axis it costs nothing: all
    four PUSH ('VmReference.lean:850-861' pops on none of them), so 'stepPopCount' is 0 for each
    ('pc_lin7', 'pc_bilin7Row', 'pc_bilin7Pairwise', 'pc_modarith7' above, all 'rfl') and the goal needs no
    limb fact, no template table and no depth hypothesis at all. Each is one 'NoUnderflow' refinement of a
    form already proved here, over 'limbLinearForm'/'limbRowForm'/'limbPairwiseForm'/'modarith7Form' -
    whose only fault sources are the readers, all proved 'NoUnderflow' above. MODARITH7 is additionally
    the arm QvmShift leaves open on the read and slot axes. -/
def PG_stepDepth_at_limb4 : Prop :=
  ∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
    (mem : QuotientRefMemory),
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem) ∧
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem) ∧
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpBilin7Pairwise stack mem) ∧
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem)

/-- The exact per-arm goal state, in the shape IDSEG stated the axis in
    ('QvmSegment.lean:360-363'), for one excluded arm; the other three are the same with their opcode. -/
def PG_stepDepth_at_lin7_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) : Prop :=
  ∀ (stack : List QVMFr) (mem : QuotientRefMemory) (idx : Nat),
    P idx stack mem → idx < bytes.length → qOpLin7 = bytes.getD idx 0 →
    ∀ j, Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem ≠
      .error (QVMFault.stackUnderflow j)

/-! ### 7. Acceptance prints -/

#print axioms Midfall.Lowering.QvmDepth.evalQuotientIdentityStep_noUnderflow_22
#print axioms Midfall.Lowering.QvmDepth.validator_popCount_22
#print axioms Midfall.Lowering.QvmDepth.step_noUnderflow_of_validator_fold
#print axioms Midfall.Lowering.QvmDepth.noUnderflow_of_FoldDepth
#print axioms Midfall.Lowering.QvmDepth.PG_stepDepth_at_of_popCount_le
#print axioms Midfall.Lowering.QvmDepth.PG_stepDepth_at_of_validator_fold
#print axioms Midfall.Lowering.QvmDepth.demoPG_stepDepth_at
#print axioms Midfall.Lowering.QvmDepth.step_noUnderflow_stream5
#print axioms Midfall.Lowering.QvmDepth.depth_axis_not_vacuous
#print axioms Midfall.Lowering.QvmDepth.validator_fold_agrees_on_the_witness
#cone_sorries Midfall.Lowering.QvmDepth.PG_stepDepth_at_of_popCount_le
#cone_sorries Midfall.Lowering.QvmDepth.PG_stepDepth_at_of_validator_fold
#cone_sorries Midfall.Lowering.QvmDepth.demoPG_stepDepth_at
#cone_sorries Midfall.Lowering.QvmDepth.evalQuotientIdentityStep_noUnderflow_22

end Midfall.Lowering.QvmDepth

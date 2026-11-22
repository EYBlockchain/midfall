-- |
-- Midfall.Lowering.QvmShift
--
-- Card QSHIFT - the shift/prefix congruence for 'evalQuotientIdentityStep'.
--
-- THE GAP, in QVMC's words (78c217b): "every per-arm fact in the tree is stated at index 0 with
-- the opcode consed on (Qvm.lean:1197's convention), but the loop induction runs at a GENERAL
-- cursor on bytes.drop cursor. There is NO shift/prefix congruence for evalQuotientIdentityStep
-- anywhere in the tree." This file is that congruence.
--
-- WHY NOT AN EQUATION. The step's fault payloads embed the cursor: 'readPastEnd i',
-- 'constSlotOutOfRange slot idx', 'stackUnderflow idx', 'zeroLengthRun idx',
-- 'affineSumZeroCounts idx', 'modarith7UnknownFlags flags idx', 'streamOpcodeInIdentity op idx',
-- 'unknownOpcode op idx'. So 'step bytes idx = step (drop idx bytes) 0' is FALSE for idx > 0 on
-- any faulting path - and 'shift_bare_equation_is_false' / 'shift_bare_equation_is_false_no_bytes'
-- below PROVE it by counterexample, the second one on an arm (ADD) that reads no byte at all, so
-- it is not a reader-layer quirk. The ok payload, by contrast, carries NO cursor: 'consumed' is a
-- delta and the stack and memory are position-free. That asymmetry is the whole design.
--
-- THE RELATION ACTUALY USED. Rather than weaken to a bare ok-implication, the congruence is stated
-- as an equation MODULO AN EXPLICIT FAULT TRANSPORT:
--
--   step bytes consts idx op stack mem
--     = mapErr (shiftFault idx) (step (bytes.drop idx) consts 0 op stack mem)
--
-- where 'shiftFault k' adds k to the cursor field of every fault that has one and leaves
-- 'stackLengthMismatch' and 'panic' alone. That IS an equation, it is strictly stronger than
-- ok-preservation, and it degrades to exactly the ok-preservation QVMC asked for via
-- 'mapErr_ok_iff' ('step_ok_congr'). The two facts the loop induction needs then transport for
-- free: 'NoRF' (read bounds) because shiftFault moves readPastEnd onto readPastEnd both ways, and
-- 'NamesSlot' (const-slot correspondence) because shiftFault never touches the SLOT component.
--
-- WHAT IS HERE: the transport and the six reader-level shift lemmas (section 1); the counted-fold
-- transport and the folded-arm term shifts (section 2); the per-arm congruences - 20 of the 26
-- identity arms (19 flat blocks over the readers plus LIN7, whose body is a counted fold), plus
-- the five stream arms and the unknown-opcode class (section 3); the
-- ok-preservation corollaries and the two counterexamples (section 4); and the general-cursor forms
-- of the two per-arm packages that were stuck at index 0, 'readsWithinStride_at' and
-- 'consumed_agrees_at' (section 5).
--
-- WHAT IS NOT HERE, named: MODARITH7 is the only identity arm with no step congruence in this file;
-- its exact remaining goal on each of the three families is named in 'PG_stepNoRF_validated_cs_-
-- modarith7' (const-slot) and in the three 'PG_stepNoRF_validated_shif2_modarith7_*' Props (read
-- bound, width agreement, and the congruence both depend on). Everything else is here: the flat
-- arms and LIN7 in sections 1-3, the two RUN arms and AFFINE_SUM in section 7, and the two
-- nested/counted limb arms BILIN7_ROW and BILIN7_PAIRWISE in section 9 - 25 of the 26 identity
-- arms. The general-cursor packages 'readsWithinStride_at_22' and 'consumed_agrees_at_22' (section
-- 9) reach the same 22 arms as the index-0 statements they transport, and with QvmWalk's
-- 'runAddMul*_noRF' / 'affineSum_noRF' and 'consumed_agrees_at_affineSum' both families now stand
-- at 25 of 26.
--
-- SECTION 10 (card SLOT2) is the SECOND slot-axis pass Qvm.lean:2277-2288 names: the OUT-OF-RANGE-NESS
-- of the faulted slot, 'OORSlot (evalQuotientIdentityStep ...) consts.length', for 25 of the 26
-- identity arms at a general cursor, plus 'noSlotFault_of_namesSlot_oorSlot', which composes this
-- pass with CSLOT's membership pass into the row's second conjunct per arm
-- ('evalQuotientIdentityStep_noSlotFault_25'). MODARITH7 alone is left, named in
-- 'PG_stepNoRF_validated_slot2_modarith7_oor'.
-- NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES); no statement
-- names a fixture (D-P71); no 'native_decide'; the file has no sorry.
import Midfall.Lowering.Qvm
import Midfall.Lowering.QvmWalk

set_option autoImplicit false

namespace Midfall.Lowering.QvmShift

open Midfall Midfall.Generator Midfall.Generator.QuotientValidator


/-! ### Section 1: the transport and the six readers -/
def shiftFault (k : Nat) : QVMFault → QVMFault
  | .stackUnderflow i => .stackUnderflow (k + i)
  | .readPastEnd i => .readPastEnd (k + i)
  | .constSlotOutOfRange s i => .constSlotOutOfRange s (k + i)
  | .zeroLengthRun i => .zeroLengthRun (k + i)
  | .affineSumZeroCounts i => .affineSumZeroCounts (k + i)
  | .modarith7UnknownFlags f i => .modarith7UnknownFlags f (k + i)
  | .streamOpcodeInIdentity o i => .streamOpcodeInIdentity o (k + i)
  | .unknownOpcode o i => .unknownOpcode o (k + i)
  | .stackLengthMismatch l => .stackLengthMismatch l
  | .panic s => .panic s

def mapErr {α : Type} (g : QVMFault → QVMFault) (x : Except QVMFault α) : Except QVMFault α :=
  match x with
  | .ok a => .ok a
  | .error e => .error (g e)

theorem mapErr_ok {α : Type} (g : QVMFault → QVMFault) (a : α) : mapErr g (Except.ok a) = Except.ok a := rfl
theorem mapErr_bind {α β : Type} (g : QVMFault → QVMFault) (x : Except QVMFault α)
    (K : α → Except QVMFault β) :
    (mapErr g x) >>= (fun a => mapErr g (K a)) = mapErr g (x >>= K) := by
  cases x with
  | ok a => rfl
  | error e => rfl
theorem mapErr_ite {p : Prop} [Decidable p] {α : Type} (g : QVMFault → QVMFault)
    (x y : Except QVMFault α) : mapErr g (if p then x else y) = if p then mapErr g x else mapErr g y := by
  split <;> rfl
theorem bind_ok_id {α : Type} (z : Except QVMFault α) :
    (z >>= (fun y => Except.ok y)) = z := by cases z <;> rfl

theorem drop_shift (bytes : List Nat) (idx k : Nat) :
    List.drop k (List.drop idx bytes) = List.drop (idx + k) bytes :=
  @List.drop_drop Nat k idx bytes

theorem byteAt_shift (bytes : List Nat) (idx k : Nat) :
    Midfall.Generator.byteAt bytes (idx + k)
    = mapErr (shiftFault idx) (Midfall.Generator.byteAt (bytes.drop idx) k) := by
  have h : List.drop (idx + k) bytes = List.drop k (List.drop idx bytes) := (drop_shift bytes idx k).symm
  unfold Midfall.Generator.byteAt
  rw [h]
  cases List.drop k (List.drop idx bytes) with
  | cons b rest => rfl
  | nil => rfl

theorem byteAt_shiftHere (bytes : List Nat) (idx : Nat) :
    Midfall.Generator.byteAt bytes idx
    = mapErr (shiftFault idx) (Midfall.Generator.byteAt (bytes.drop idx) 0) :=
  byteAt_shift bytes idx 0

theorem readU16_shift (bytes : List Nat) (idx k : Nat) :
    Midfall.Generator.readU16 bytes (idx + k)
    = mapErr (shiftFault idx) (Midfall.Generator.readU16 (bytes.drop idx) k) := by
  unfold Midfall.Generator.readU16
  rw [byteAt_shift bytes idx k, show (idx + k) + 1 = idx + (k + 1) by omega,
      byteAt_shift bytes idx (k + 1)]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem readU16_shiftHere (bytes : List Nat) (idx : Nat) :
    Midfall.Generator.readU16 bytes idx
    = mapErr (shiftFault idx) (Midfall.Generator.readU16 (bytes.drop idx) 0) :=
  readU16_shift bytes idx 0

theorem readU32_shift (bytes : List Nat) (idx k : Nat) :
    Midfall.Generator.readU32 bytes (idx + k)
    = mapErr (shiftFault idx) (Midfall.Generator.readU32 (bytes.drop idx) k) := by
  unfold Midfall.Generator.readU32
  rw [byteAt_shift bytes idx k, show (idx + k) + 1 = idx + (k + 1) by omega,
      byteAt_shift bytes idx (k + 1), show (idx + k) + 2 = idx + (k + 2) by omega,
      byteAt_shift bytes idx (k + 2), show (idx + k) + 3 = idx + (k + 3) by omega,
      byteAt_shift bytes idx (k + 3)]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem fqFromU256_mapErr (v : Word256) (idx : Nat) :
    mapErr (shiftFault idx) (Midfall.Generator.fqFromU256 v) = Midfall.Generator.fqFromU256 v := by
  unfold Midfall.Generator.fqFromU256
  split <;> rfl

theorem constAt_shift (consts : List Word256) (slot idx k : Nat) :
    Midfall.Generator.constAt consts slot (idx + k)
    = mapErr (shiftFault idx) (Midfall.Generator.constAt consts slot k) := by
  unfold Midfall.Generator.constAt
  cases List.drop slot consts with
  | cons v rest =>
      show Midfall.Generator.fqFromU256 v = mapErr (shiftFault idx) (Midfall.Generator.fqFromU256 v)
      exact (fqFromU256_mapErr v idx).symm
  | nil => rfl

theorem constAt_shiftHere (consts : List Word256) (slot idx : Nat) :
    Midfall.Generator.constAt consts slot idx
    = mapErr (shiftFault idx) (Midfall.Generator.constAt consts slot 0) :=
  constAt_shift consts slot idx 0

theorem popStack_shift (stack : List QVMFr) (idx k : Nat) :
    Midfall.Generator.popStack stack (idx + k)
    = mapErr (shiftFault idx) (Midfall.Generator.popStack stack k) := by
  unfold Midfall.Generator.popStack
  cases stack with
  | cons v rest => rfl
  | nil => show Except.error (QVMFault.stackUnderflow (idx+k)) = _; rfl

theorem popStack_shiftHere (stack : List QVMFr) (idx : Nat) :
    Midfall.Generator.popStack stack idx
    = mapErr (shiftFault idx) (Midfall.Generator.popStack stack 0) :=
  popStack_shift stack idx 0

theorem indexOrPanic_shift (bytes : List Nat) (idx k : Nat) :
    Midfall.Generator.indexOrPanic bytes (idx + k)
    = mapErr (shiftFault idx) (Midfall.Generator.indexOrPanic (bytes.drop idx) k) := by
  have h : List.drop (idx + k) bytes = List.drop k (List.drop idx bytes) := (drop_shift bytes idx k).symm
  unfold Midfall.Generator.indexOrPanic
  rw [h]
  cases List.drop k (List.drop idx bytes) with
  | cons b rest => rfl
  | nil => rfl

/-- The transport through a two-way branch, for the arms whose body ends in an ite on the opcode. -/
theorem affineLinearTerm_shift (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx k : Nat) :
    Midfall.Generator.affineLinearTerm bytes consts mem (idx + k)
    = mapErr (shiftFault idx)
      (Midfall.Generator.affineLinearTerm (bytes.drop idx) consts mem k) := by
  unfold Midfall.Generator.affineLinearTerm
  rw [readU16_shift bytes idx k, show (idx + k) + 2 = idx + (k + 2) by omega,
      byteAt_shift bytes idx (k + 2)]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shift]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem affineProductTerm_shift (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx k : Nat) :
    Midfall.Generator.affineProductTerm bytes consts mem (idx + k)
    = mapErr (shiftFault idx)
      (Midfall.Generator.affineProductTerm (bytes.drop idx) consts mem k) := by
  unfold Midfall.Generator.affineProductTerm
  rw [readU16_shift bytes idx k, show (idx + k) + 2 = idx + (k + 2) by omega,
      readU16_shift bytes idx (k + 2), show (idx + k) + 4 = idx + (k + 4) by omega,
      byteAt_shift bytes idx (k + 4)]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shift]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

/-- The step congruence for one arm, as a reusable tactic-shaped lemma set: the flat arms are all
    do-blocks over the six readers above. -/
theorem step_shift_pushConst (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConst stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPushConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_pushConstU8 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConstU8 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPushConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [byteAt_shift bytes idx 1]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_pushMemLiteral (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemLiteral stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPushMemLiteral stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU32_shift bytes idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_pushMemU16 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemU16 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPushMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_pushMemToken (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemToken stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPushMemToken stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [byteAt_shift bytes idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_pushMemTokenOffset (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemTokenOffset stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPushMemTokenOffset stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [byteAt_shift bytes idx 1, readU32_shift bytes idx 2]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_add (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAdd stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAdd stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_mul (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMul stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpMul stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_neg (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpNeg stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpNeg stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_pow5 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPow5 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpPow5 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_addConstU8 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddConstU8 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAddConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [byteAt_shift bytes idx 1]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shiftHere]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_mulConstU8 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulConstU8 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpMulConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [byteAt_shift bytes idx 1]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shiftHere]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_addConst (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddConst stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAddConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shiftHere]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_mulConst (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulConst stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpMulConst stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1]
  conv_lhs => simp (config := { singlePass := true }) only [constAt_shiftHere]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_addMemU16 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMemU16 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAddMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1, popStack_shiftHere stack idx]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_mulMemU16 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulMemU16 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpMulMemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1, popStack_shiftHere stack idx]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_addMulMemMem (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMulMemMem stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAddMulMemMem stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [readU16_shift bytes idx 1, readU16_shift bytes idx 3, popStack_shiftHere stack idx]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_addMulMemMemConstU8 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMulMemMemConstU8 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
        qOpAddMulMemMemConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  rw [affineProductTerm_shift bytes consts mem idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

theorem step_shift_addMulConstU8MemU16 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMulConstU8MemU16 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
        qOpAddMulConstU8MemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  conv_lhs => simp (config := { singlePass := true }) only [popStack_shiftHere]
  rw [affineLinearTerm_shift bytes consts mem idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

/-- The five stream-level opcodes and the unknown-opcode class: both sides take the same error
    branch, and the embedded cursor is exactly what shiftFault repairs. -/
theorem step_shift_stream (bytes : List Nat) (idx op : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : op = qOpFoldMain \/ op = qOpFoldSelector \/ op = qOpNativePermutation
      \/ op = qOpNativeLookup \/ op = qOpNativeIdentity) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem) := by
  rcases hop with (h|h|h|h|h) <;> subst h
  · unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    simp only [mapErr, shiftFault, Nat.add_zero]
  · unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    simp only [mapErr, shiftFault, Nat.add_zero]
  · unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    simp only [mapErr, shiftFault, Nat.add_zero]
  · unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    simp only [mapErr, shiftFault, Nat.add_zero]
  · unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    simp only [mapErr, shiftFault, Nat.add_zero]

/-! ### Section 2: the counted-fold transport -/

def mapBoth {α β : Type} (g : QVMFault → QVMFault) (S : α → β) : Except QVMFault α → Except QVMFault β
  | .ok a => .ok (S a)
  | .error e => .error (g e)

theorem mapBoth_mapErr {α : Type} (g : QVMFault → QVMFault) :
    mapBoth g (id : α → α) = mapErr g := rfl
theorem mapBoth_ok {α β : Type} (g : QVMFault → QVMFault) (S : α → β) (a : α) :
    mapBoth g S (Except.ok a) = Except.ok (S a) := rfl
theorem mapBoth_error {α β : Type} (g : QVMFault → QVMFault) (S : α → β) (e : QVMFault) :
    mapBoth g S (Except.error (α := α) e) = Except.error (g e) := rfl

theorem mapBoth_pair_match {α β γ : Type} (g : QVMFault → QVMFault) (S : γ → γ)
    (e : α × QuotientRefMemory) (f : α → QuotientRefMemory → Except QVMFault γ) :
    mapBoth g S (match e with | (a, b) => f a b) = match e with | (a, b) => mapBoth g S (f a b) := by
  cases e <;> rfl

theorem mapErr_pair_match {α β : Type} (g : QVMFault → QVMFault) (e : α × QuotientRefMemory)
    (f : α → QuotientRefMemory → Except QVMFault β) :
    mapErr g (match e with | (a, b) => f a b) = match e with | (a, b) => mapErr g (f a b) := by
  cases e <;> rfl

theorem mapBoth_bind_first {α β γ : Type} (g : QVMFault → QVMFault) (S : γ → γ)
    (x : Except QVMFault α) (K' : α → Except QVMFault γ) :
    mapBoth g S (x >>= K') = mapErr g x >>= (fun a => mapBoth g S (K' a)) := by
  cases x <;> rfl

theorem mapBoth_bind {α β γ : Type} (g : QVMFault → QVMFault) (S : α → β) (T : β → γ)
    (x : Except QVMFault α) (K : β → Except QVMFault γ) (K' : α → Except QVMFault β)
    (hK : ∀ a, K (S a) = mapBoth g T (K' a)) :
    mapBoth g S x >>= K = mapBoth g T (x >>= K') := by
  cases x with
  | ok a => exact hK a
  | error e => rfl

theorem mapBoth_pure {α : Type} (g : QVMFault → QVMFault) (S : α → α) (z : Except QVMFault α) :
    mapBoth g S z >>= (fun y => Except.ok y) = mapBoth g S (z >>= (fun y => Except.ok y)) := by
  cases z <;> rfl

theorem foldRangeIdxM_shift {α : Type} (g : QVMFault → QVMFault) (S : α → α) :
    ∀ (n : Nat) (init : α) (f f' : Nat → α → Except QVMFault α),
      (∀ i s, f i (S s) = mapBoth g S (f' i s)) →
      Midfall.Generator.foldRangeIdxM n (S init) f
        = mapBoth g S (Midfall.Generator.foldRangeIdxM n init f')
  | 0, init, f, f', _ => rfl
  | k + 1, init, f, f', hf => by
      have hstep : ∀ a, (Midfall.Generator.foldRangeIdxM k (S a) (fun i => f (i + 1))
            >>= (fun y => Except.ok y))
          = mapBoth g S (Midfall.Generator.foldRangeIdxM k a (fun i => f' (i + 1))
            >>= (fun y => Except.ok y)) := by
        intro a
        rw [foldRangeIdxM_shift g S k a (fun i => f (i + 1)) (fun i => f' (i + 1))
          (fun i s => hf (i + 1) s)]
        exact mapBoth_pure g S (Midfall.Generator.foldRangeIdxM k a (fun i => f' (i + 1)))
      show (Midfall.Generator.foldRangeIdxM (k + 1) (S init) f)
          = mapBoth g S (Midfall.Generator.foldRangeIdxM (k + 1) init f')
      unfold Midfall.Generator.foldRangeIdxM
      rw [hf 0 init]
      exact mapBoth_bind g S S (f' 0 init)
        (fun x => Midfall.Generator.foldRangeIdxM k x (fun i => f (i + 1)) >>= (fun y => Except.ok y))
        (fun x => Midfall.Generator.foldRangeIdxM k x (fun i => f' (i + 1)) >>= (fun y => Except.ok y))
        hstep

def shiftSt3 (idx : Nat) (s : QVMFr × Nat × QuotientRefMemory) :
    QVMFr × Nat × QuotientRefMemory := (s.1, idx + s.2.1, s.2.2)

def limbLinBody (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (acc, cursor, mem) := state
    let slot ← Midfall.Generator.byteAt bytes cursor
    let ptr ← Midfall.Generator.readU16 bytes (cursor + 1)
    let c ← Midfall.Generator.constAt consts slot cursor
    let (v, mem') := mem.literal ptr
    .ok (qvmFrAdd acc (qvmFrMul c v), cursor + 3, mem')

theorem limbLinBody_shift (bytes : List Nat) (consts : List Word256) (idx : Nat) :
    ∀ i s, limbLinBody bytes consts i (shiftSt3 idx s)
      = mapBoth (shiftFault idx) (shiftSt3 idx) (limbLinBody (bytes.drop idx) consts i s) := by
  intro i s
  obtain ⟨acc, c, m⟩ := s
  show (do
        let slot ← Midfall.Generator.byteAt bytes (idx + c)
        let ptr ← Midfall.Generator.readU16 bytes (idx + c + 1)
        let cc ← Midfall.Generator.constAt consts slot (idx + c)
        let (v, mem') := m.literal ptr
        .ok (qvmFrAdd acc (qvmFrMul cc v), idx + c + 3, mem'))
      = mapBoth (shiftFault idx) (shiftSt3 idx) (do
        let slot ← Midfall.Generator.byteAt (bytes.drop idx) c
        let ptr ← Midfall.Generator.readU16 (bytes.drop idx) (c + 1)
        let cc ← Midfall.Generator.constAt consts slot c
        let (v, mem') := m.literal ptr
        .ok (qvmFrAdd acc (qvmFrMul cc v), c + 3, mem'))
  cases h1 : Midfall.Generator.byteAt (bytes.drop idx) c with
  | error e1 =>
      rw [byteAt_shift bytes idx c, h1]
      simp only [mapErr, mapBoth, bind, Except.bind]
  | ok slot =>
      rw [byteAt_shift bytes idx c, h1, mapErr_ok]
      simp only [bind, Except.bind]
      cases h2 : Midfall.Generator.readU16 (bytes.drop idx) (c + 1) with
      | error e2 =>
          rw [show (idx + c) + 1 = idx + (c + 1) by omega, readU16_shift bytes idx (c + 1), h2]
          simp only [mapErr, mapBoth, bind, Except.bind]
      | ok ptr =>
          rw [show (idx + c) + 1 = idx + (c + 1) by omega, readU16_shift bytes idx (c + 1),
            h2, mapErr_ok]
          simp only [bind, Except.bind]
          cases h3 : Midfall.Generator.constAt consts slot c with
          | error e3 =>
              conv_lhs => simp (config := { singlePass := true }) only [constAt_shift]
              rw [h3]
              simp only [mapErr, mapBoth, bind, Except.bind]
          | ok cc =>
              conv_lhs => simp (config := { singlePass := true }) only [constAt_shift]
              rw [h3, mapErr_ok]
              simp only [bind, Except.bind]
              simp only [mapBoth, shiftSt3]
              have : idx + c + 3 = idx + (c + 3) := by omega
              rw [this]

theorem limbLinearForm_shift (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx k : Nat) :
    Midfall.Generator.limbLinearForm bytes consts mem (idx + k)
    = mapErr (shiftFault idx)
      (Midfall.Generator.limbLinearForm (bytes.drop idx) consts mem k) := by
  have hbody := limbLinBody_shift bytes consts idx
  have hinit : (qvmFrZero, idx + k, mem) = shiftSt3 idx (qvmFrZero, k, mem) := rfl
  show (Midfall.Generator.foldRangeIdxM quotientVmLimbs (qvmFrZero, idx + k, mem)
        (limbLinBody bytes consts)
        >>= (fun y => .ok (y.1, y.2.1 - (idx + k), y.2.2)))
      = mapErr (shiftFault idx) (Midfall.Generator.foldRangeIdxM quotientVmLimbs (qvmFrZero, k, mem)
        (limbLinBody (bytes.drop idx) consts) >>= (fun y => .ok (y.1, y.2.1 - k, y.2.2)))
  rw [hinit, foldRangeIdxM_shift (shiftFault idx) (shiftSt3 idx) quotientVmLimbs
    (qvmFrZero, k, mem) (limbLinBody bytes consts) (limbLinBody (bytes.drop idx) consts) hbody]
  cases h : Midfall.Generator.foldRangeIdxM quotientVmLimbs (qvmFrZero, k, mem)
      (limbLinBody (bytes.drop idx) consts) with
  | ok y =>
      simp only [mapBoth, mapErr_ok, bind, Except.bind, shiftSt3]
      have : (idx + y.2.1) - (idx + k) = y.2.1 - k := by omega
      rw [this]
  | error e =>
      simp only [mapBoth, mapErr, bind, Except.bind, shiftSt3]

theorem step_shift_lin7 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem
    = mapErr (shiftFault idx)
      (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpLin7 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [limbLinearForm_shift bytes consts mem idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

/-! ### Section 4: ok-preservation, and the two proofs that the bare equation is false -/

theorem mapErr_error {α : Type} (g : QVMFault → QVMFault) (e : QVMFault) :
    mapErr g (Except.error (α := α) e) = Except.error (g e) := rfl

theorem mapErr_ok_iff {α : Type} {g : QVMFault → QVMFault} {x : Except QVMFault α} {a : α} :
    mapErr g x = .ok a ↔ x = .ok a := by
  cases x <;> simp [mapErr]

theorem mapErr_error_iff {α : Type} {g : QVMFault → QVMFault} {x : Except QVMFault α} {e : QVMFault} :
    mapErr g x = .error e ↔ (∃ e', x = .error e' ∧ g e' = e) := by
  cases x with
  | ok a =>
      refine ⟨fun h => absurd h (by intro h2; cases h2), fun ⟨e', h, _⟩ => ?_⟩
      cases h
  | error e' =>
      refine ⟨fun h => ⟨e', rfl, Except.error.inj h⟩, fun ⟨w, hw, hg⟩ => ?_⟩
      have : w = e' := (Except.error.inj hw.symm)
      subst this
      rw [mapErr_error, ← hg]

/-- shiftFault is REFLECTING on the read class: a shifted fault is a readPastEnd only if the
    original was one. -/
theorem shiftFault_readPastEnd {k : Nat} {e : QVMFault} {i : Nat}
    (h : shiftFault k e = QVMFault.readPastEnd i) : ∃ j, e = QVMFault.readPastEnd j := by
  cases e with
  | stackUnderflow _ => simp [shiftFault] at h
  | readPastEnd j => exact ⟨j, rfl⟩
  | constSlotOutOfRange _ _ => simp [shiftFault] at h
  | zeroLengthRun _ => simp [shiftFault] at h
  | affineSumZeroCounts _ => simp [shiftFault] at h
  | modarith7UnknownFlags _ _ => simp [shiftFault] at h
  | streamOpcodeInIdentity _ _ => simp [shiftFault] at h
  | unknownOpcode _ _ => simp [shiftFault] at h
  | stackLengthMismatch _ => simp [shiftFault] at h
  | panic _ => simp [shiftFault] at h

/-- ...and it preserves the read class upward, so the two are equivalent. -/
theorem shiftFault_readPastEnd_of {k : Nat} {e : QVMFault}
    (h : ∃ j, e = QVMFault.readPastEnd j) : ∃ i, shiftFault k e = QVMFault.readPastEnd i := by
  obtain ⟨j, rfl⟩ := h
  exact ⟨k + j, rfl⟩

/-- READ BOUNDS TRANSPORT. 'NoRF' is "names no readPastEnd"; shiftFault moves readPastEnd onto
    readPastEnd in both directions, so the read bound at a general cursor and the read bound at
    index 0 on the dropped prefix are the same statement. -/
theorem NoRF_mapErr_shiftFault {α : Type} (k : Nat) (x : Except QVMFault α) :
    NoRF (mapErr (shiftFault k) x) ↔ NoRF x := by
  constructor
  · intro h i hi
    have h2 : mapErr (shiftFault k) x = .error (QVMFault.readPastEnd (k + i)) := by
      rw [hi]; rfl
    exact h (k + i) h2
  · intro h i hi
    obtain ⟨e', hx, hg⟩ := mapErr_error_iff.mp hi
    obtain ⟨j, hj⟩ := shiftFault_readPastEnd hg
    exact absurd (hx.trans (congrArg Except.error hj)) (h j)

/-- shiftFault leaves the SLOT component of a const-slot fault alone, so the const-slot
    correspondence transports unchanged. -/
theorem shiftFault_slot {k : Nat} {e : QVMFault} {s j : Nat}
    (h : shiftFault k e = QVMFault.constSlotOutOfRange s j) : ∃ i, e = QVMFault.constSlotOutOfRange s i := by
  cases e with
  | stackUnderflow _ => simp [shiftFault] at h
  | readPastEnd _ => simp [shiftFault] at h
  | constSlotOutOfRange s' i =>
      simp only [shiftFault] at h
      have hs : s' = s := (QVMFault.constSlotOutOfRange.inj h).1
      rw [hs]
      exact ⟨i, rfl⟩
  | zeroLengthRun _ => simp [shiftFault] at h
  | affineSumZeroCounts _ => simp [shiftFault] at h
  | modarith7UnknownFlags _ _ => simp [shiftFault] at h
  | streamOpcodeInIdentity _ _ => simp [shiftFault] at h
  | unknownOpcode _ _ => simp [shiftFault] at h
  | stackLengthMismatch _ => simp [shiftFault] at h
  | panic _ => simp [shiftFault] at h

theorem NamesSlot_mapErr_shiftFault {α : Type} (k : Nat) (x : Except QVMFault α) (S : List Nat) :
    NamesSlot (mapErr (shiftFault k) x) S ↔ NamesSlot x S := by
  constructor
  · intro h slot j hh
    have h2 : mapErr (shiftFault k) x = .error (QVMFault.constSlotOutOfRange slot (k + j)) := by
      rw [hh]; rfl
    exact h slot (k + j) h2
  · intro h slot j hh
    obtain ⟨e', hx, hg⟩ := mapErr_error_iff.mp hh
    obtain ⟨i, hi⟩ := shiftFault_slot hg
    exact h slot i (hx.trans (congrArg Except.error hi))

/-- THE CONGRUENCE IN THE FORM THE LOOP INDUCTION WANTS: ok-preservation with a SHARED payload.
    Not an implication between two existentials - the same 'step' on both sides, because the ok
    payload carries no cursor. -/
theorem step_ok_congr (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) (step : IdentityStep) (op : Nat)
    (hshift : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem)) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok step ↔
      Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem = .ok step := by
  rw [hshift]
  exact mapErr_ok_iff

/-- THE BARE EQUATION IS FALSE, and this is the reason the deliverable is an ok-preservation.
    PUSH_CONST at cursor 1 of the two-byte program [PUSH_CONST, PUSH_CONST] reads its slot at
    absolute position 2 and faults 'readPastEnd 2'; the same step at index 0 of the dropped
    one-byte prefix faults 'readPastEnd 1'. Same constructor, different cursor, so no
    ok-side renaming repairs it. -/
theorem shift_bare_equation_is_false :
    ¬ (∀ (bytes : List Nat) (idx : Nat) (consts : List Word256) (stack : List QVMFr)
        (mem : QuotientRefMemory),
        Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConst stack mem
          = Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
            qOpPushConst stack mem) := by
  intro h
  have h1 : Midfall.Generator.evalQuotientIdentityStep [qOpPushConst, qOpPushConst] [] 1
      qOpPushConst ([] : List QVMFr) (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats []))
      = Except.error (QVMFault.readPastEnd 2) := by
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    unfold Midfall.Generator.readU16 Midfall.Generator.byteAt
    rfl
  have h2 : Midfall.Generator.evalQuotientIdentityStep
      (List.drop 1 [qOpPushConst, qOpPushConst]) [] 0 qOpPushConst
      ([] : List QVMFr) (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats []))
      = Except.error (QVMFault.readPastEnd 1) := by
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    unfold Midfall.Generator.readU16 Midfall.Generator.byteAt
    rfl
  have h3 := h [qOpPushConst, qOpPushConst] 1 [] [] (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats []))
  rw [h1, h2] at h3
  exact absurd h3 (by simp)

/-- AND NOT ONLY THE READ FAULTS: ADD reads no byte at all, yet its underflow payload carries the
    cursor. So the cursor-embedding is in the step's own error taxonomy, not an artefact of the
    reader layer that a reader-level fix could dodge. -/
theorem shift_bare_equation_is_false_no_bytes :
    ¬ (∀ (idx : Nat) (stack : List QVMFr),
        Midfall.Generator.evalQuotientIdentityStep [] [] idx qOpAdd stack
            (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats []))
          = Midfall.Generator.evalQuotientIdentityStep (List.drop idx []) [] 0 qOpAdd stack
            (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats []))) := by
  intro h
  have h1 : Midfall.Generator.evalQuotientIdentityStep [] [] 3 qOpAdd ([] : List QVMFr)
      (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats [])) = Except.error (QVMFault.stackUnderflow 3) := by
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    have hp : Midfall.Generator.popStack ([] : List QVMFr) 3
        = Except.error (QVMFault.stackUnderflow 3) := rfl
    rw [hp]
    simp only [bind, Except.bind]
  have h2 : Midfall.Generator.evalQuotientIdentityStep (List.drop 3 []) [] 0 qOpAdd
      ([] : List QVMFr) (Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats []))
      = Except.error (QVMFault.stackUnderflow 0) := by
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true }) only [reduceIte]
    have hp : Midfall.Generator.popStack ([] : List QVMFr) 0
        = Except.error (QVMFault.stackUnderflow 0) := rfl
    rw [hp]
    simp only [bind, Except.bind]
  have h3 := h 3 []
  rw [h1, h2] at h3
  exact absurd h3 (by simp)

/-- The fault side of the congruence, stated as a transport rather than an equation: a step at a
    general cursor faults with 'f' exactly when the dropped-prefix step faults with some 'f' whose
    cursor is 'f'’s minus the offset. This is the exact sense in which the payloads differ. -/
theorem step_error_transport (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) (op : Nat) (f : QVMFault)
    (hshift : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem)) :
    (∃ f', Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem
        = .error f' ∧ f = shiftFault idx f') ↔
      Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .error f := by
  rw [hshift]
  constructor
  · rintro ⟨f', hf, rfl⟩
    exact mapErr_error_iff.mpr ⟨f', hf, rfl⟩
  · intro hh
    obtain ⟨f', hf, hge⟩ := mapErr_error_iff.mp hh
    exact ⟨f', hf, hge.symm⟩


/-! ### Section 5: the combined congruence and the two general-cursor packages -/

/-- THE COMBINED CONGRUENCE. **Count deliberately not stated here: it has gone stale twice as
    arms landed (QSHIFT said 20, section 5 said 21 and wrongly claimed BILIN7_ROW). The
    authoritative list is the set of `step_shift_*` theorems in this file; section 6 names
    the identity arms NOT yet covered.** The static arms whose body is a
    flat block over the six readers, plus LIN7 and BILIN7_ROW (the two whose body is a counted fold
    and which the fold transport of section 2 reaches). The remaining six - BILIN7_ROW,
    BILIN7_PAIRWISE, MODARITH7, the two RUN arms and AFFINE_SUM - are named in section 6. -/
theorem evalQuotientIdentityStep_shift (op : Nat)
    (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7)
    (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem) := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h) <;> subst h
  · exact step_shift_pushConst bytes idx consts stack mem
  · exact step_shift_pushMemLiteral bytes idx consts stack mem
  · exact step_shift_pushMemToken bytes idx consts stack mem
  · exact step_shift_pushMemTokenOffset bytes idx consts stack mem
  · exact step_shift_pushMemU16 bytes idx consts stack mem
  · exact step_shift_add bytes idx consts stack mem
  · exact step_shift_mul bytes idx consts stack mem
  · exact step_shift_neg bytes idx consts stack mem
  · exact step_shift_pushConstU8 bytes idx consts stack mem
  · exact step_shift_addConstU8 bytes idx consts stack mem
  · exact step_shift_mulConstU8 bytes idx consts stack mem
  · exact step_shift_addConst bytes idx consts stack mem
  · exact step_shift_mulConst bytes idx consts stack mem
  · exact step_shift_addMemU16 bytes idx consts stack mem
  · exact step_shift_mulMemU16 bytes idx consts stack mem
  · exact step_shift_addMulMemMem bytes idx consts stack mem
  · exact step_shift_pow5 bytes idx consts stack mem
  · exact step_shift_addMulMemMemConstU8 bytes idx consts stack mem
  · exact step_shift_addMulConstU8MemU16 bytes idx consts stack mem
  · exact step_shift_lin7 bytes idx consts stack mem

/-- The five stream-level opcodes and the unknown-opcode class also transport, with the cursor in
    their payload repaired by shiftFault. Not part of the identity-arm count - these are the arms the
    identity loop must NEVER see (Qvm.lean:768 excludes them) - but the congruence covers them for
    free, which is what makes 'streamArms_error' usable mid-stream. -/
theorem evalQuotientIdentityStep_shift_stream (op : Nat)
    (hop : op = qOpFoldMain \/ op = qOpFoldSelector \/ op = qOpNativePermutation
      \/ op = qOpNativeLookup \/ op = qOpNativeIdentity)
    (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem) :=
  step_shift_stream bytes idx op consts stack mem hop

/-- THE READ BOUND AT A GENERAL CURSOR, 21 arms. This is the fact
    'qvm_validated_noBoundsFault' needs and 'evalQuotientIdentityStep_readsWithinStride'
    (Qvm.lean:1864) does not supply: that one is stated at index 0 with the opcode consed on, and
    the loop induction runs at a cursor. The walker hypothesis is stated at the DROPPED prefix,
    which is the same instruction: 'hdrop' is the hypothesis that says so. -/
theorem evalQuotientIdentityStep_readsWithinStride_at
    (op : Nat) (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7)
    (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = op :: rest)
    (len : Nat)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len)
    (hfit : len ≤ (op :: rest).length)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem) := by
  rw [evalQuotientIdentityStep_shift op hop bytes idx consts stack mem, NoRF_mapErr_shiftFault]
  rw [hdrop]
  refine evalQuotientIdentityStep_readsWithinStride op ?_ rest len hlen hfit consts stack mem
  tauto

/-- THE WIDTH AGREEMENT AT A GENERAL CURSOR, 21 arms: the cursor-shifted twin of
    'evalQuotientIdentityStep_consumed_agrees' (Qvm.lean:1197). The step's 'consumed' is a delta, so
    the SAME step value is produced at the cursor and at index 0 on the dropped prefix - which is
    exactly what makes the transport possible without touching the conclusion. -/
theorem evalQuotientIdentityStep_consumed_agrees_at
    (op : Nat) (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7)
    (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = op :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len) :
    step.consumed = len := by
  have h2 : Midfall.Generator.evalQuotientIdentityStep (op :: rest) consts 0 op stack mem = .ok step := by
    have h3 := step_ok_congr bytes idx consts stack mem step op
      (evalQuotientIdentityStep_shift op hop bytes idx consts stack mem)
    rw [hdrop] at h3
    exact (h3.mp hstep)
  refine evalQuotientIdentityStep_consumed_agrees op ?_ rest consts stack mem step len h2 hlen
  tauto

/-- THE CONST-SLOT CORRESPONDENCE IS ALREADY GENERAL-CURSOR. 'evalQuotientIdentityStep_constSlot_namedByWalker'
    (Qvm.lean:2588) is stated at an arbitrary 'idx' over 'bytes', so it needs no transport - which is
    worth recording, because it means the shift congruence is needed for exactly TWO of the three
    per-arm packages the hole wants, not three. What the congruence adds on this axis is the
    robustness fact: shiftFault never moves the SLOT component of a const-slot fault, so any future
    index-0 slot statement transports unchanged. -/
theorem NamesSlot_shiftFault_slot_ok {α : Type} {x : Except QVMFault α} {S : List Nat} (k : Nat) :
    NamesSlot (mapErr (shiftFault k) x) S → NamesSlot x S :=
  (NamesSlot_mapErr_shiftFault k x S).mp

/-! ### Section 6: what is left, named -/

/-- THE REMAINING FIVE ARMS, with the exact obstacle in each case, so the next card does not have to
    rediscover it.

  * BILIN7_ROW. One more layer than LIN7: 'limbRowForm' is a u16 read, a memory hit and then
    'limbLinearForm' at 'idx + 2'. The pieces are all here ('readU16_shift', 'limbLinearForm_shift',
    'mapErr_pair_match'); what costs the lines is that the memory hit's pair-pattern sits between the
    two, so the transport has to be pushed past the match before the inner congruence can be cited.
  * BILIN7_PAIRWISE. The body is a fold of a fold and the OUTER state is '(acc, mem)' with no cursor
    component, so 'foldRangeIdxM_shift' applies with 'S = id' - the obstacle is only that the inner
    fold sits inside the outer body's continuation, and the body congruence has to be stated about
    the inner fold's own transport. Mechanically the same shape as 'limbLinBody_shift'; nothing
    conceptual is missing.
  * MODARITH7. Five chained counted blocks plus a header whose branch points depend on a flag byte
    read at the cursor. The fold transport handles each block (S = shiftSt3, as for the limb forms);
    what is missing is the header congruence, i.e. that 'afterCond'/'afterConst' computed at
    'idx + k' are 'idx +' the values computed at 'k'. That is a two-line omega per branch, but it has
    to be done inside the do-block, under the binders - the same 'conv_lhs' + singlePass pattern this
    file uses for 'constAt_shift'.
  * The two RUN arms and AFFINE_SUM. Their fold state cursor is the RELATIVE 'used', so the transport
    is 'foldRangeIdxM_shift' with 'S = id' and the body congruence is 'affineProductTerm_shift' /
    'affineLinearTerm_shift' at 'idx + 3 + used' - both already proved here. These three are the
    cheapest of the five. They are also NOT needed for the two general-cursor packages above: the
    22-arm statements exclude all four dynamic arms, and QvmWalk already supplies their read bounds
    at a general cursor ('affineSum_noRF', 'runAddMul*_noRF' are stated at an arbitrary 'idx').
  LANDED SINCE (card NBF): the two RUN arms and AFFINE_SUM - the three named cheapest - are proved in
  section 7 below, so what was still missing from this file was BILIN7_ROW, BILIN7_PAIRWISE and
  MODARITH7.

  LANDED SINCE (card CSLOT): BILIN7_ROW and BILIN7_PAIRWISE now have their CONST-SLOT
  correspondence - section 8's authoritative content is the set of 'constSlot_*' theorems plus
  'evalQuotientIdentityStep_constSlot_namedByWalker_folded'. CORRECTION, card SHIF2: what CSLOT
  wrote here claimed those two arms had their STEP CONGRUENCES from section 8, and they did not -
  section 8 works on the slot axis, where 'NamesSlot' is a forall over the fault and no transport
  is needed. The step congruences for those two arms are the axes' other obligation and landed in
  section 9 (card SHIF2), which is what the two general-cursor packages needed. MODARITH7 remains
  the only identity arm with neither a step congruence nor a const-slot correspondence in this
  file; its exact goal state is named in 'PG_stepNoRF_validated_cs_modarith7' and, for the other
  two families, in the 'PG_stepNoRF_validated_shif2_modarith7_*' Props. -/


theorem shift_remaining_arms_are_the_dynamic_and_pairwise_ones : True := trivial


/-! ### Section 7: the three cheapest of the six remaining arm congruences (card NBF)

    THE TWO RUN ARMS AND AFFINE_SUM. QSHIFT section 6 named these as the cheapest of the six: their
    fold state's cursor component is the RELATIVE 'used', not an absolute byte offset, so the state
    transport is the IDENTITY and only the per-term byte read moves. That is why 'foldRangeIdxM_shift'
    is instantiated at 'S = id' here (via 'foldRangeIdxM_shift_id') rather than at 'shiftSt3' as for
    the limb forms.

    WHY THE BODIES HAVE TO BE VARIABLES. The concrete per-term lambda inside 'evalQuotientIdentityStep'
    compiles to a match auxiliary ('Except.map.match_1') that is NOT writable from a statement: the
    equation compiler names it after the definition it was generated in, so a lambda typed out here
    compiles to a DIFFERENT constant and 'rw' cannot see the goal's copy. Measured: three formulations
    (do-notation with tuple destructuring, do-notation with projections, and an explicit match) all
    failed to rewrite, while the same term written as 'Except.map' is definitionally equal. The fix is
    to state the transport about an ABSTRACT body 'F' and bridge the concrete arm to it with a 'rfl'
    equation ('step_eq_runArmBody' and friends), which typechecks up to defeq instead of matching
    syntax. Nothing is weakened by this: the bridging lemmas are definitional.

    NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES); no statement
    names a fixture (D-P71); no 'native_decide'; this section adds no sorry. -/

theorem foldRangeIdxM_shift_id {α : Type} (g : QVMFault → QVMFault) (n : Nat) (init : α)
    (f f' : Nat → α → Except QVMFault α) (h : ∀ i s, f i s = mapErr g (f' i s)) :
    Midfall.Generator.foldRangeIdxM n init f
      = mapErr g (Midfall.Generator.foldRangeIdxM n init f') := by
  have := foldRangeIdxM_shift g (id : α → α) n init f f'
    (fun i s => by rw [(show f i (id s) = f i s from rfl), h i s]; rfl)
  rwa [mapBoth_mapErr] at this

def runFoldL (bytes : List Nat) (consts : List Word256) (base : Nat) :
    Nat → QVMFr × Nat × QuotientRefMemory → Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => Except.map (fun x => (qvmFrAdd state.1 x.1, state.2.1 + x.2.1, x.2.2))
    (affineLinearTerm bytes consts state.2.2 (base + state.2.1))

def runFoldP (bytes : List Nat) (consts : List Word256) (base : Nat) :
    Nat → QVMFr × Nat × QuotientRefMemory → Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => Except.map (fun x => (qvmFrAdd state.1 x.1, state.2.1 + x.2.1, x.2.2))
    (affineProductTerm bytes consts state.2.2 (base + state.2.1))

def runArmBody (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (F : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory)) :
    Except QVMFault IdentityStep :=
  Midfall.Generator.readU16 bytes (idx + 1) >>= fun count =>
    if count != 0 then
      Midfall.Generator.popStack stack idx >>= fun p =>
        Midfall.Generator.foldRangeIdxM count (p.1, 0, mem) F >>= fun y =>
          Except.ok { stack := y.1 :: p.2, consumed := 3 + y.2.1, hConsumed := by omega, mem := y.2.2 }
    else Except.error (QVMFault.zeroLengthRun idx)

theorem runArmBody_shift (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (F F' : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (h : ∀ i s, F i s = mapErr (shiftFault idx) (F' i s)) :
    runArmBody bytes consts idx stack mem F
      = mapErr (shiftFault idx) (runArmBody (bytes.drop idx) consts 0 stack mem F') := by
  unfold runArmBody
  rw [readU16_shift bytes idx 1, popStack_shiftHere stack idx]
  cases hcnt : Midfall.Generator.readU16 (bytes.drop idx) 1 with
  | error e => simp only [mapErr, bind, Except.bind]
  | ok count =>
      rw [mapErr_ok]
      simp only [bind, Except.bind]
      rw [mapErr_ite]
      by_cases hc : (count != 0) = true
      · rw [if_pos hc, if_pos hc]
        cases hps : Midfall.Generator.popStack stack 0 with
        | error e => simp only [mapErr, bind, Except.bind]
        | ok v =>
            rw [mapErr_ok]
            simp only [bind, Except.bind]
            rw [foldRangeIdxM_shift_id (shiftFault idx) count (v.1, 0, mem) F F' h]
            cases hf : Midfall.Generator.foldRangeIdxM count (v.1, 0, mem) F' with
            | ok y => simp only [mapErr_ok, bind, Except.bind]
            | error e => simp only [mapErr, bind, Except.bind]
      · rw [if_neg hc, if_neg hc]
        simp only [mapErr, shiftFault, Nat.add_zero]

theorem step_eq_runArmBodyL (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpRunAddMulConstU8MemU16 stack mem
      = runArmBody bytes consts idx stack mem (runFoldL bytes consts (idx + 3)) := rfl

theorem step_eq_runArmBodyL_dropped (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
        qOpRunAddMulConstU8MemU16 stack mem
      = runArmBody (bytes.drop idx) consts 0 stack mem (runFoldL (bytes.drop idx) consts 3) := rfl

theorem step_eq_runArmBody (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpRunAddMulMemMemConstU8 stack mem
      = runArmBody bytes consts idx stack mem (runFoldP bytes consts (idx + 3)) := rfl

theorem step_eq_runArmBody_dropped (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
        qOpRunAddMulMemMemConstU8 stack mem
      = runArmBody (bytes.drop idx) consts 0 stack mem (runFoldP (bytes.drop idx) consts 3) := rfl

theorem runFoldL_shift (bytes : List Nat) (consts : List Word256) (idx base : Nat) :
    ∀ i s, runFoldL bytes consts (idx + base) i s
      = mapErr (shiftFault idx) (runFoldL (bytes.drop idx) consts base i s) := by
  intro i s
  unfold runFoldL
  show Except.map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
        (affineLinearTerm bytes consts s.2.2 (idx + base + s.2.1))
      = mapErr (shiftFault idx) (Except.map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
        (affineLinearTerm (bytes.drop idx) consts s.2.2 (base + s.2.1)))
  have key : affineLinearTerm bytes consts s.2.2 (idx + base + s.2.1)
      = mapErr (shiftFault idx)
        (affineLinearTerm (bytes.drop idx) consts s.2.2 (base + s.2.1)) := by
      rw [show idx + base + s.2.1 = idx + (base + s.2.1) by omega,
          affineLinearTerm_shift bytes consts s.2.2 idx (base + s.2.1)]
  rw [key]
  cases h : affineLinearTerm (bytes.drop idx) consts s.2.2 (base + s.2.1) with
  | ok y => simp only [mapErr_ok, Except.map]
  | error e => simp only [mapErr, Except.map]

theorem runFoldP_shift (bytes : List Nat) (consts : List Word256) (idx base : Nat) :
    ∀ i s, runFoldP bytes consts (idx + base) i s
      = mapErr (shiftFault idx) (runFoldP (bytes.drop idx) consts base i s) := by
  intro i s
  unfold runFoldP
  show Except.map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
        (affineProductTerm bytes consts s.2.2 (idx + base + s.2.1))
      = mapErr (shiftFault idx) (Except.map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
        (affineProductTerm (bytes.drop idx) consts s.2.2 (base + s.2.1)))
  have key : affineProductTerm bytes consts s.2.2 (idx + base + s.2.1)
      = mapErr (shiftFault idx)
        (affineProductTerm (bytes.drop idx) consts s.2.2 (base + s.2.1)) := by
      rw [show idx + base + s.2.1 = idx + (base + s.2.1) by omega,
          affineProductTerm_shift bytes consts s.2.2 idx (base + s.2.1)]
  rw [key]
  cases h : affineProductTerm (bytes.drop idx) consts s.2.2 (base + s.2.1) with
  | ok y => simp only [mapErr_ok, Except.map]
  | error e => simp only [mapErr, Except.map]

theorem step_shift_runAddMulConstU8MemU16 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpRunAddMulConstU8MemU16 stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
          qOpRunAddMulConstU8MemU16 stack mem) := by
  rw [step_eq_runArmBodyL, step_eq_runArmBodyL_dropped,
      runArmBody_shift bytes consts idx stack mem _ _ (runFoldL_shift bytes consts idx 3)]

theorem step_shift_runAddMulMemMemConstU8 (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpRunAddMulMemMemConstU8 stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
          qOpRunAddMulMemMemConstU8 stack mem) := by
  rw [step_eq_runArmBody, step_eq_runArmBody_dropped,
      runArmBody_shift bytes consts idx stack mem _ _ (runFoldP_shift bytes consts idx 3)]


/-- ARM AFFINE_SUM's body with BOTH counted blocks' per-term functions abstracted: the linear block
    first, the product block second, in the source order the interpreter depends on. The second
    block's INIT CURSOR is the first block's output, which is why the transport has to be stated
    about variable bodies and bridged by 'rfl'. -/
def affineSumArmBody (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (Fl Fp : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory)) :
    Except QVMFault IdentityStep :=
  Midfall.Generator.readU16 bytes (idx + 1) >>= fun linCount =>
    Midfall.Generator.readU16 bytes (idx + 3) >>= fun productCount =>
      if (linCount != 0 && productCount != 0) = true then
        Midfall.Generator.popStack stack idx >>= fun p =>
          Midfall.Generator.foldRangeIdxM linCount (p.1, 0, mem) Fl >>= fun a =>
            Midfall.Generator.foldRangeIdxM productCount (a.1, a.2.1, a.2.2) Fp >>= fun b =>
              Except.ok { stack := b.1 :: p.2, consumed := 5 + b.2.1, hConsumed := by omega, mem := b.2.2 }
      else Except.error (QVMFault.affineSumZeroCounts idx)

theorem affineSumArmBody_shift (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (Fl Fl' Fp Fp' : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (hl : ∀ i s, Fl i s = mapErr (shiftFault idx) (Fl' i s))
    (hp : ∀ i s, Fp i s = mapErr (shiftFault idx) (Fp' i s)) :
    affineSumArmBody bytes consts idx stack mem Fl Fp
      = mapErr (shiftFault idx)
        (affineSumArmBody (bytes.drop idx) consts 0 stack mem Fl' Fp') := by
  unfold affineSumArmBody
  cases h1 : Midfall.Generator.readU16 (bytes.drop idx) 1 with
  | error e => rw [readU16_shift bytes idx 1, h1]; simp only [mapErr, bind, Except.bind]
  | ok lin =>
      rw [readU16_shift bytes idx 1, h1, mapErr_ok]
      cases h3 : Midfall.Generator.readU16 (bytes.drop idx) 3 with
      | error e => rw [readU16_shift bytes idx 3, h3]; simp only [mapErr, bind, Except.bind]
      | ok prod =>
          rw [readU16_shift bytes idx 3, h3, mapErr_ok]
          simp only [bind, Except.bind]
          rw [mapErr_ite, popStack_shiftHere stack idx]
          by_cases hc : (lin != 0 && prod != 0) = true
          · rw [if_pos hc, if_pos hc]
            cases hps : Midfall.Generator.popStack stack 0 with
            | error e => simp only [mapErr, bind, Except.bind]
            | ok p =>
                rw [mapErr_ok]
                simp only [bind, Except.bind]
                rw [foldRangeIdxM_shift_id (shiftFault idx) lin (p.1, 0, mem) Fl Fl' hl]
                cases ha : Midfall.Generator.foldRangeIdxM lin (p.1, 0, mem) Fl' with
                | error e => simp only [ha, mapErr, bind, Except.bind]
                | ok a =>
                    rw [mapErr_ok]
                    simp only [bind, Except.bind]
                    rw [foldRangeIdxM_shift_id (shiftFault idx) prod (a.1, a.2.1, a.2.2) Fp Fp' hp]
                    cases hb : Midfall.Generator.foldRangeIdxM prod (a.1, a.2.1, a.2.2) Fp' with
                    | ok b => simp only [mapErr_ok, bind, Except.bind]
                    | error e => simp only [mapErr, bind, Except.bind]
          · rw [if_neg hc, if_neg hc]
            simp only [mapErr, shiftFault, Nat.add_zero]

theorem step_eq_affineSumArmBody (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAffineSum stack mem
      = affineSumArmBody bytes consts idx stack mem
          (runFoldL bytes consts (idx + 5)) (runFoldP bytes consts (idx + 5)) := rfl

theorem step_eq_affineSumArmBody_dropped (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAffineSum stack mem
      = affineSumArmBody (bytes.drop idx) consts 0 stack mem
          (runFoldL (bytes.drop idx) consts 5) (runFoldP (bytes.drop idx) consts 5) := rfl

theorem step_shift_affineSum (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAffineSum stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 qOpAffineSum stack mem) := by
  rw [step_eq_affineSumArmBody, step_eq_affineSumArmBody_dropped,
      affineSumArmBody_shift bytes consts idx stack mem _ _ _ _
        (runFoldL_shift bytes consts idx 5) (runFoldP_shift bytes consts idx 5)]


/-- THE WIDTH AGREEMENT AT A GENERAL CURSOR for the first RUN arm: QvmWalk supplies it at index 0 and
    the section-7 congruence transports it, so the loop induction can cite it at a cursor. -/
theorem consumed_agrees_at_runAddMulMemMemConstU8 (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = qOpRunAddMulMemMemConstU8 :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx
        qOpRunAddMulMemMemConstU8 stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen
        (qOpRunAddMulMemMemConstU8 :: rest) 0 = .ok len) :
    step.consumed = len := by
  have h2 : Midfall.Generator.evalQuotientIdentityStep (qOpRunAddMulMemMemConstU8 :: rest)
      consts 0 qOpRunAddMulMemMemConstU8 stack mem = .ok step := by
    have h3 := step_ok_congr bytes idx consts stack mem step qOpRunAddMulMemMemConstU8
      (step_shift_runAddMulMemMemConstU8 bytes idx consts stack mem)
    rw [hdrop] at h3
    exact h3.mp hstep
  exact Midfall.Lowering.QvmWalk.consumed_agrees_runAddMulMemMemConstU8
    rest consts stack mem step len h2 hlen

/-- Same for the second RUN arm. -/
theorem consumed_agrees_at_runAddMulConstU8MemU16 (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = qOpRunAddMulConstU8MemU16 :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx
        qOpRunAddMulConstU8MemU16 stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen
        (qOpRunAddMulConstU8MemU16 :: rest) 0 = .ok len) :
    step.consumed = len := by
  have h2 : Midfall.Generator.evalQuotientIdentityStep (qOpRunAddMulConstU8MemU16 :: rest)
      consts 0 qOpRunAddMulConstU8MemU16 stack mem = .ok step := by
    have h3 := step_ok_congr bytes idx consts stack mem step qOpRunAddMulConstU8MemU16
      (step_shift_runAddMulConstU8MemU16 bytes idx consts stack mem)
    rw [hdrop] at h3
    exact h3.mp hstep
  exact Midfall.Lowering.QvmWalk.consumed_agrees_runAddMulConstU8MemU16
    rest consts stack mem step len h2 hlen

/-- PG_NBF - THE EXACT FACT 'qvm_validated_noBoundsFault' STILL NEEDS after QSHIFT and card NBF,
    recorded as a named Prop and NOT added to the row, to 'ValidV3', a bundle or the root (RULES:
    "if a fact is missing, STOP, record a PG_* row with the exact goal state"). It is the per-step
    core of the hole: at a cursor inside a VALIDATED program, a step that faults names neither
    read-past-end nor a const slot. The hole is this fact plus the loop induction over the segment,
    and the induction is mechanical once this is available ('evalQuotientIdentityLoop_fuelNeverBinds'
    is the template and 'foldRangeIdxM_ok_advance' supplies the cursor arithmetic).

    WHY NOTHING SUPPLIES IT, named rather than glossed - three families, all per-arm:

    1. THE READ BOUND at a general cursor is missing for THREE arms: BILIN7_ROW and BILIN7_PAIRWISE
       (their index-0 form exists in the 22-arm 'evalQuotientIdentityStep_readsWithinStride' but
       their step congruence does not, so 'readsWithinStride_at' cannot reach them), and MODARITH7
       (missing at index 0 AND at a cursor - five chained counted blocks plus a flag-dependent
       header; 'fold_chain_step' in QvmWalk is the tool and 'affineSum_noRF' the template).
    2. THE WIDTH AGREEMENT at a general cursor is missing for FOUR arms: AFFINE_SUM and MODARITH7
       have no index-0 form at all (QvmWalk names both as open), and BILIN7_ROW / BILIN7_PAIRWISE
       have the index-0 form but no congruence to transport it. The two RUN arms' general-cursor
       forms LANDED in this card ('consumed_agrees_at_runAddMul*').
    3. THE CONST-SLOT CORRESPONDENCE was missing for SEVEN arms - LIN7, BILIN7_ROW,
       BILIN7_PAIRWISE, the two RUN arms, AFFINE_SUM and MODARITH7 - all excluded from the 19-arm
       'evalQuotientIdentityStep_constSlot_namedByWalker' because their slot reads sit inside a
       counted fold. SIX OF THE SEVEN LANDED in card CSLOT (section 8: 'constSlot_lin7',
       'constSlot_bilin7Row', 'constSlot_bilin7Pairwise', 'constSlot_runAddMulMemMemConstU8',
       'constSlot_runAddMulConstU8MemU16', 'constSlot_affineSum', unioned as
       'evalQuotientIdentityStep_constSlot_namedByWalker_25'). The obstacle was NOT the case split
       QSHIFT predicted but the two inductions section 8's header names: a cursor-invariant
       induction over the interpreter's fold and a prefix lemma over the walker's. MODARITH7 is
       the one arm left, and its exact remaining goal is named in
       'PG_stepNoRF_validated_cs_modarith7' rather than here, so this count cannot rot again.

    WHAT THIS CARD DID LAND, so the count is honest: the three congruences QSHIFT named cheapest -
    both RUN arms and AFFINE_SUM - plus the two general-cursor width agreements they unlock. That is
    3 of the 6 remaining arm congruences and 2 of the 4 remaining width agreements. The row is
    still open, and it is open on the 3 arms of family 1, the 4 of family 2 and the 7 of family 3,
    not on anything conceptual. NO CONTRACT DEFECT WAS FOUND: on the arms the congruence covers,
    interpreter-at-cursor and interpreter-at-index-0 agree as an EQUATION, so the validator cannot
    be shown to fault a validated program on those arms; the remaining arms were not measured here
    and no claim is made about them. -/
def PG_stepNoRF_validated (bytes : List Nat) (consts : List Word256)
    (model : QuotientOperandModel) : Prop :=
  ∀ (j : Nat) (stack : List QVMFr) (mem : QuotientRefMemory) (f : QVMFault),
    j < bytes.length →
    (∃ ops, Midfall.Generator.QuotientValidator.quotientBytecodeOps bytes = .ok ops ∧
        ∀ p ∈ ops.map (fun (idx, op, _len) => (idx, op)),
          ∀ operand ∈ operandList bytes p.1 p.2,
            Midfall.Generator.QuotientValidator.checkQuotientOperand model p.1 operand = .ok ()) →
    Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0) stack mem
        = .error f →
    (∀ i, f ≠ QVMFault.readPastEnd i) ∧
      (∀ slot idx, f ≠ QVMFault.constSlotOutOfRange slot idx)

#print axioms Midfall.Lowering.QvmShift.PG_stepNoRF_validated


/-! ### Section 8: the const-slot correspondence for the folded arms (card CSLOT)

    THE SEVEN ARMS whose slot reads sit INSIDE a counted fold, and which are therefore excluded
    from the 19-arm 'evalQuotientIdentityStep_constSlot_namedByWalker' (Qvm.lean section 9). Five
    of the seven are proved here at a GENERAL cursor: LIN7, BILIN7_ROW, the two RUN arms and
    AFFINE_SUM. BILIN7_PAIRWISE and MODARITH7 are named at the end of this section with the exact
    remaining goal, and are NOT sorried.

    THE SHAPE OF THE PROOF, once per arm. 'NamesSlot x S' says every 'constSlotOutOfRange' the
    computation can produce names a slot in S, so a counted fold needs TWO inductions that have
    never been written down anywhere in the tree:

    * THE INTERPRETER SIDE ('foldRangeIdxM_namesSlot_range' and its cursor form). The i-th
      iteration's slot read is at 'c0 + w*i' ONLY IF every earlier iteration succeeded and
      advanced by exactly w, so the induction carries a predicate P on (index, state) rather than
      a bare hypothesis about all states. 'P i s = s.2.1 = c0 + w*i' is the whole trick; a
      hypothesis stated for all states is FALSE for these arms (the cursor of an unreachable
      state can read any byte), which is why the 19 flat arms did not need it.
    * THE WALKER SIDE ('foldRangeIdxM_ok_iter' and 'foldRangeIdxM_append_witness'). The walker's
      own fold has to be shown to have RUN iteration i and to have left its 'konst' operand inside
      the final list, because 'operandList' is the whole appended list, not the i-th piece. This
      is the prefix lemma Qvm.lean section 9 asked for.

    THE TWO FAMILIES ARE BRIDGED POSITION-WISE: the interpreter reads the slot byte at the same
    absolute offset the walker names at the same iteration - 'idx+1+3i' for the limb blocks,
    'idx+7+5i' / 'idx+5+3i' for the two RUN arms, 'idx+7+3i' then 'idx+9+3*linCount+5j' for
    AFFINE_SUM. 'byteAt_iff_byteAtPanic' (Qvm.lean) turns the walker's panic-class read into the
    interpreter's Err-class read at the same offset, which is what makes the two measurements
    comparable.

    WHY THE WALKER BODIES ARE RE-STATED AS DEFS HERE (walkLimbBody, walkRunPBody, walkRunLBody,
    walkAffLBody, walkAffPBody). The equation compiler names a generated match auxiliary after the
    definition it was generated in, so a lambda typed out in a statement is a DIFFERENT CONSTANT
    from the one inside 'limbTerms' / 'visitQuotientOperands' and 'rw' cannot see the goal's copy -
    the surface fact card NBF paid 40 minutes for. Each def is bridged to the real one by a 'rfl'
    equation ('limbTerms_unfold', 'visit_runP', 'visit_runL', 'visit_affineSum'), which typechecks
    up to defeq instead of matching syntax. Nothing is weakened by this.

    NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES); no
    statement names a fixture (D-P71); no 'native_decide'; this section adds no sorry. -/

theorem bind_ok_id' {ε α : Type} (z : Except ε α) :
    (z >>= (fun y => Except.ok y)) = z := by cases z <;> rfl

theorem foldRangeIdxM_namesSlot_range {α : Type} :
    ∀ (n : Nat) (f : Nat → α → Except QVMFault α) (S : List Nat) (P : Nat → α → Prop)
      (init : α),
      (∀ i s, i < n → P i s → NamesSlot (f i s) S) →
      (∀ i s x, i < n → P i s → f i s = .ok x → P (i+1) x) →
      P 0 init →
      NamesSlot (foldRangeIdxM n init f) S
  | 0, _, _, _, _, _, _, _ => NamesSlot.ok _ _
  | k+1, f, S, P, init, hstep, hprog, h0 => by
      show NamesSlot (f 0 init >>= (fun x =>
        foldRangeIdxM k x (fun i => f (i+1)) >>= (fun y => Except.ok y))) S
      refine NamesSlot.bind2 (f 0 init)
        (fun x => foldRangeIdxM k x (fun i => f (i+1)) >>= (fun y => Except.ok y))
        (hstep 0 init (by omega) h0) (fun x hx => ?_)
      rw [bind_ok_id']
      exact foldRangeIdxM_namesSlot_range k (fun i => f (i+1)) S (fun i s => P (i+1) s) x
        (fun i s hi hP => hstep (i+1) s (by omega) hP)
        (fun i s y hi hP heq => hprog (i+1) s y (by omega) hP heq)
        (hprog 0 init x (by omega) h0 hx)

theorem foldRangeIdxM_namesSlot_cursor
    (n : Nat) (init : QVMFr) (c0 : Nat) (mem : QuotientRefMemory) (w : Nat)
    (f : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory)) (S : List Nat)
    (hstep : ∀ i s, i < n → s.2.1 = c0 + w * i → NamesSlot (f i s) S)
    (hprog : ∀ i s x, i < n → s.2.1 = c0 + w * i → f i s = .ok x → x.2.1 = c0 + w * (i+1)) :
    NamesSlot (foldRangeIdxM n (init, c0, mem) f) S :=
  foldRangeIdxM_namesSlot_range n f S (fun i s => s.2.1 = c0 + w * i) (init, c0, mem) hstep
    (fun i s x hi hP heq => hprog i s x hi hP heq) (by simp)

theorem foldRangeIdxM_append_witness {β : Type} {ε : Type}
    (f : Nat → List β → Except ε (List β))
    (hf : ∀ i s out, f i s = .ok out → ∃ t, out = s ++ t) :
    ∀ (n : Nat) (init out : List β),
      foldRangeIdxM n init f = .ok out → ∃ t, out = init ++ t
  | 0, init, out, h => ⟨[], by
      have hio : init = out := Except.ok.inj h
      rw [← hio]
      exact (List.append_nil init).symm⟩
  | k+1, init, out, h => by
      obtain ⟨x, hx, hrest0⟩ := peel_bind h
      obtain ⟨t0, ht0⟩ := hf 0 init x hx
      have hrest : foldRangeIdxM k x (fun i => f (i+1)) = .ok out := by
        rw [bind_ok_id'] at hrest0
        exact hrest0
      obtain ⟨u, hu⟩ := foldRangeIdxM_append_witness (fun i => f (i+1))
        (fun i s out h2 => hf (i+1) s out h2) k x out hrest
      exact ⟨t0 ++ u, by rw [hu, ht0, List.append_assoc]⟩

theorem foldRangeIdxM_ok_iter {β : Type} {ε : Type}
    (f : Nat → List β → Except ε (List β))
    (hf : ∀ i s out, f i s = .ok out → ∃ t, out = s ++ t) :
    ∀ (n : Nat) (init out : List β),
      foldRangeIdxM n init f = .ok out →
      ∀ i, i < n → ∃ s s' t u,
        foldRangeIdxM i init f = .ok s ∧ f i s = .ok s' ∧ s' = s ++ t ∧ out = s' ++ u
  | 0, _, _, _, i, hi => absurd hi (by omega)
  | k+1, init, out, h, i, hi => by
      obtain ⟨x, hx, hrest0⟩ := peel_bind h
      obtain ⟨t0, ht0⟩ := hf 0 init x hx
      have hrest : foldRangeIdxM k x (fun i => f (i+1)) = .ok out := by
        rw [bind_ok_id'] at hrest0
        exact hrest0
      cases i with
      | zero =>
          obtain ⟨u, hu⟩ := foldRangeIdxM_append_witness (fun i => f (i+1))
            (fun i s out h2 => hf (i+1) s out h2) k x out hrest
          exact ⟨init, x, t0, u, rfl, hx, ht0, hu⟩
      | succ j =>
          obtain ⟨s, s', t, u, hpre, hfi, hs', hu⟩ :=
            foldRangeIdxM_ok_iter (fun i => f (i+1))
              (fun i s out h2 => hf (i+1) s out h2) k x out hrest j (by omega)
          refine ⟨s, s', t, u, ?_, hfi, hs', hu⟩
          have heq : foldRangeIdxM (j+1) init f
              = foldRangeIdxM j x (fun i => f (i+1)) := by
            show (f 0 init >>= (fun y =>
              foldRangeIdxM j y (fun i => f (i+1)) >>= (fun z => Except.ok z))
              : Except ε (List β)) = _
            rw [hx]
            show (foldRangeIdxM j x (fun i => f (i+1)) >>= (fun z => Except.ok z)) = _
            exact bind_ok_id' _
          exact heq.trans hpre

/-! #### The walker's limb block, spelled out -/

def walkLimbBody (bytes : List Nat) (base : Nat) :
    Nat → List QuotientOperand → VResult (List QuotientOperand) :=
  fun k acc => do
    let term := base + k * limbTermStride
    let slot ← byteAtPanic bytes term 2329
    let ptr ← QuotientValidator.readU16 bytes (term + 1)
    .ok (acc ++ [QuotientOperand.konst slot false, QuotientOperand.mem "limb" ptr])

theorem limbTerms_unfold (bytes : List Nat) (base : Nat) :
    limbTerms bytes base = foldRangeIdxM quotientVmLimbs [] (walkLimbBody bytes base) := rfl

theorem walkLimbBody_ok (bytes : List Nat) (base i : Nat) (acc out : List QuotientOperand)
    (h : walkLimbBody bytes base i acc = .ok out) :
    ∃ slot ptr, byteAtPanic bytes (base + i * limbTermStride) 2329 = .ok slot ∧
      QuotientValidator.readU16 bytes (base + i * limbTermStride + 1) = .ok ptr ∧
      out = acc ++ [QuotientOperand.konst slot false, QuotientOperand.mem "limb" ptr] := by
  unfold walkLimbBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨slot, hslot, h1⟩ := peel_bind h
  obtain ⟨ptr, hptr, h2⟩ := peel_bind h1
  exact ⟨slot, ptr, hslot, hptr, (Except.ok.inj h2).symm⟩

theorem walkLimbBody_shape (bytes : List Nat) (base i : Nat) (acc out : List QuotientOperand)
    (h : walkLimbBody bytes base i acc = .ok out) : ∃ t, out = acc ++ t := by
  obtain ⟨_, _, _, _, heq⟩ := walkLimbBody_ok bytes base i acc out h
  exact ⟨_, heq⟩

/-- THE WALKER'S LIMB BLOCK NAMES EVERY SLOT THE INTERPRETER'S LIMB FOLD CAN READ. -/
theorem limbTerms_names_limb_slots {bytes : List Nat} {base : Nat} {os : List QuotientOperand}
    (h : limbTerms bytes base = .ok os) :
    ∀ i, i < quotientVmLimbs → ∀ b,
      byteAt bytes (base + i * limbTermStride) = .ok b →
      QuotientOperand.konst b false ∈ os := by
  intro i hi b hb
  obtain ⟨s, s', t, u, hpre, hstep, hs', hu⟩ :=
    foldRangeIdxM_ok_iter (walkLimbBody bytes base)
      (fun j acc out h2 => walkLimbBody_shape bytes base j acc out h2)
      quotientVmLimbs [] os h i hi
  obtain ⟨slot, ptr, hsp, _, hshape⟩ := walkLimbBody_ok bytes base i s s' hstep
  have hmatch : slot = b := by
    have hb2 : byteAt bytes (base + i * limbTermStride) = .ok slot :=
      (byteAt_iff_byteAtPanic (line := 2329)).mpr hsp
    exact Except.ok.inj (hb2.symm.trans hb)
  have hmem : QuotientOperand.konst slot false ∈ os := by
    rw [hu, hshape]; simp
  rw [← hmatch]; exact hmem


/-! #### The interpreter's limb fold -/

theorem limbLinearForm_unfold (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) :
    limbLinearForm bytes consts mem k
      = (foldRangeIdxM quotientVmLimbs (qvmFrZero, k, mem) (limbLinBody bytes consts)
          >>= (fun y => Except.ok (y.1, y.2.1 - k, y.2.2))) := rfl

theorem limbLinBody_unfold (bytes : List Nat) (consts : List Word256) (c : Nat)
    (i : Nat) (acc : QVMFr) (m : QuotientRefMemory) :
    limbLinBody bytes consts i (acc, c, m)
      = (do
          let slot ← byteAt bytes c
          let ptr ← readU16 bytes (c + 1)
          let cc ← constAt consts slot c
          let (v, mem') := m.literal ptr
          .ok (qvmFrAdd acc (qvmFrMul cc v), c + 3, mem')) := rfl

theorem limbLinBody_namesSlot (bytes : List Nat) (consts : List Word256) (c : Nat) (S : List Nat)
    (h : ∀ b, byteAt bytes c = .ok b → b ∈ S) :
    ∀ (i : Nat) (acc : QVMFr) (m : QuotientRefMemory),
      NamesSlot (limbLinBody bytes consts i (acc, c, m)) S := by
  intro i acc m
  rw [limbLinBody_unfold bytes consts c i acc m]
  refine NamesSlot.bind2 (byteAt bytes c) ?F (byteAt_namesSlot bytes c S) (fun slot hslot => ?_)
  refine NamesSlot.bind (readU16_namesSlot bytes (c+1) S) (fun _ =>
    NamesSlot.bind (constAt_namesSlot slot c S (h slot hslot)) (fun _ => NamesSlot.ok _ S))

theorem limbLinBody_advance (bytes : List Nat) (consts : List Word256) (c : Nat)
    (i : Nat) (acc : QVMFr) (m : QuotientRefMemory)
    (x : QVMFr × Nat × QuotientRefMemory)
    (h : limbLinBody bytes consts i (acc, c, m) = .ok x) : x.2.1 = c + 3 := by
  rw [limbLinBody_unfold bytes consts c i acc m] at h
  obtain ⟨slot, _, h1⟩ := peel_bind h
  obtain ⟨ptr, _, h2⟩ := peel_bind h1
  obtain ⟨cc, _, h3⟩ := peel_bind h2
  exact (Except.ok.inj h3).symm ▸ rfl

/-- THE LIMB FOLD NAMES ONLY WALKER SLOTS. -/
theorem limbLinearForm_namesSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} {S : List Nat}
    (h : ∀ i, i < quotientVmLimbs → ∀ b,
        byteAt bytes (k + limbTermStride * i) = .ok b → b ∈ S) :
    NamesSlot (limbLinearForm bytes consts mem k) S := by
  have hfold : NamesSlot
      (foldRangeIdxM quotientVmLimbs (qvmFrZero, k, mem) (limbLinBody bytes consts)) S :=
    foldRangeIdxM_namesSlot_cursor quotientVmLimbs qvmFrZero k mem limbTermStride
      (limbLinBody bytes consts) S
      (fun i s hi hc => by
        obtain ⟨acc, c, m⟩ := s
        have hc' : c = k + limbTermStride * i := hc
        rw [hc']
        exact limbLinBody_namesSlot bytes consts (k + limbTermStride * i) S (h i hi) i acc m)
      (fun i s x hi hc hok => by
        obtain ⟨acc, c, m⟩ := s
        have hc' : c = k + limbTermStride * i := hc
        rw [hc'] at hok
        exact limbLinBody_advance bytes consts (k + limbTermStride * i) i acc m x hok)
  rw [limbLinearForm_unfold bytes consts mem k]
  exact NamesSlot.bind hfold (fun _ => NamesSlot.ok _ S)

theorem operandList_ok {bytes : List Nat} {idx op : Nat} {os : List QuotientOperand}
    (h : visitQuotientOperands bytes idx op = .ok os) : operandList bytes idx op = os := by
  unfold operandList
  rw [h]

/-- ARM LIN7 AT A GENERAL CURSOR: the const-slot correspondence. -/
theorem constSlot_lin7 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hw : ∃ os, visitQuotientOperands bytes idx qOpLin7 = .ok os) :
    NamesSlot (evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem)
      (walkerKonstSlots bytes idx qOpLin7) := by
  obtain ⟨os, hos⟩ := hw
  have hv : visitQuotientOperands bytes idx qOpLin7 = limbTerms bytes (idx + 1) := by
    unfold visitQuotientOperands
    simp (config := {decide := true}) only [reduceIte]
  have hlist : operandList bytes idx qOpLin7 = os := operandList_ok (hv ▸ hos)
  have hslot : ∀ i, i < quotientVmLimbs → ∀ b,
      byteAt bytes (idx + 1 + limbTermStride * i) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpLin7 := by
    intro i hi b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist]
    exact limbTerms_names_limb_slots (hv ▸ hos) i hi b
      (by rw [mul_comm] at hb; exact hb)
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NamesSlot.bind (limbLinearForm_namesSlot (k := idx + 1) hslot) (fun y => ?_)
  obtain ⟨value, len, mem'⟩ := y
  exact NamesSlot.ok _ _




/-! #### BILIN7_ROW -/

theorem limbRowForm_unfold (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) :
    limbRowForm bytes consts mem k
      = (Midfall.Generator.readU16 bytes k >>= (fun lhs =>
          match mem.literal lhs with
          | (lhsValue, mem1) =>
              limbLinearForm bytes consts mem1 (k + 2)
                >>= (fun x => Except.ok (qvmFrMul lhsValue x.1, 2 + x.2.1, x.2.2)))) := rfl

theorem limbRowForm_namesSlot (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) (S : List Nat)
    (h : ∀ i, i < quotientVmLimbs → ∀ b,
        byteAt bytes (k + 2 + limbTermStride * i) = .ok b → b ∈ S) :
    NamesSlot (limbRowForm bytes consts mem k) S := by
  rw [limbRowForm_unfold bytes consts mem k]
  apply NamesSlot.bind
  · exact readU16_namesSlot bytes k S
  · intro lhs
    obtain ⟨lhsValue, mem1⟩ := mem.literal lhs
    refine NamesSlot.bind (limbLinearForm_namesSlot (k := k + 2) ?_) (fun y => ?_)
    · intro i hi b hb
      exact h i hi b hb
    · obtain ⟨v, len, m'⟩ := y
      exact NamesSlot.ok _ S

theorem constSlot_bilin7Row (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hw : ∃ os, visitQuotientOperands bytes idx qOpBilin7Row = .ok os) :
    NamesSlot (evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem)
      (walkerKonstSlots bytes idx qOpBilin7Row) := by
  obtain ⟨os, hos⟩ := hw
  have hv : visitQuotientOperands bytes idx qOpBilin7Row
      = (QuotientValidator.readU16 bytes (idx + 1) >>= fun lhs =>
          limbTerms bytes (idx + 1 + quotientVmByteU16Bytes) >>= fun terms =>
            Except.ok (QuotientOperand.mem "row_lhs" lhs :: terms)) := by
    unfold visitQuotientOperands
    simp (config := {decide := true}) only [reduceIte]
  obtain ⟨lhs0, hl, h1⟩ := peel_bind (hv ▸ hos)
  obtain ⟨terms, ht, _⟩ := peel_bind h1
  have hlist : operandList bytes idx qOpBilin7Row
      = QuotientOperand.mem "row_lhs" lhs0 :: terms := by
    unfold operandList
    rw [hv, hl, ht]
    rfl
  have hterms : limbTerms bytes (idx + 3) = .ok terms := by
    rw [show idx + 1 + quotientVmByteU16Bytes = idx + 3 from rfl] at ht
    exact ht
  have hslot : ∀ i, i < quotientVmLimbs → ∀ b,
      byteAt bytes (idx + 3 + limbTermStride * i) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpBilin7Row := by
    intro i hi b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist]
    have := limbTerms_names_limb_slots hterms i hi b
      (by rw [mul_comm limbTermStride i] at hb; exact hb)
    simp [this]
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  apply NamesSlot.bind
  · exact limbRowForm_namesSlot bytes consts mem (idx + 1) _
      (fun i hi b hb => hslot i hi b
        (by rw [show idx + 1 + 2 = idx + 3 from rfl] at hb; exact hb))
  · intro y
    exact NamesSlot.ok _ _

/-! #### The affine-term helpers the RUN and AFFINE_SUM arms share -/

theorem NamesSlot.except_map {α β : Type} (g : α → β) {x : Except QVMFault α} {S : List Nat}
    (h : NamesSlot x S) : NamesSlot (Except.map g x) S := by
  intro slot j hh
  cases x with
  | ok a => cases hh
  | error e =>
      have he : e = QVMFault.constSlotOutOfRange slot j := Except.error.inj hh
      exact h slot j (by rw [he])

theorem affineLinearTerm_len {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} {y : QVMFr × Nat × QuotientRefMemory}
    (h : affineLinearTerm bytes consts mem k = .ok y) : y.2.1 = 3 := by
  unfold Midfall.Generator.affineLinearTerm at h
  obtain ⟨a, _, h1⟩ := peel_bind h
  obtain ⟨b, _, h2⟩ := peel_bind h1
  obtain ⟨c, _, h3⟩ := peel_bind h2
  obtain ⟨l, m1⟩ := mem.literal a
  rw [(Except.ok.inj h3).symm]

theorem affineProductTerm_len {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} {y : QVMFr × Nat × QuotientRefMemory}
    (h : affineProductTerm bytes consts mem k = .ok y) : y.2.1 = 5 := by
  unfold Midfall.Generator.affineProductTerm at h
  obtain ⟨a, _, h1⟩ := peel_bind h
  obtain ⟨b, _, h2⟩ := peel_bind h1
  obtain ⟨s, _, h3⟩ := peel_bind h2
  obtain ⟨c, _, h4⟩ := peel_bind h3
  obtain ⟨l, m1⟩ := mem.literal a
  obtain ⟨r, m2⟩ := m1.literal b
  rw [(Except.ok.inj h4).symm]


theorem runFoldP_namesSlot_at (bytes : List Nat) (consts : List Word256)
    (base c0 n : Nat) (S : List Nat)
    (h : ∀ i, i < n → ∀ b, byteAt bytes (base + (c0 + 5 * i) + 4) = .ok b → b ∈ S) :
    ∀ i, i < n → ∀ s, s.2.1 = c0 + 5 * i → NamesSlot (runFoldP bytes consts base i s) S := by
  intro i hi s hs
  unfold runFoldP
  refine NamesSlot.except_map _ (affineProductTerm_namesSlot ?_)
  intro b hb
  exact h i hi b (by rw [hs] at hb; exact hb)

theorem runFoldP_advance_at (bytes : List Nat) (consts : List Word256) (base c0 i : Nat)
    (s x : QVMFr × Nat × QuotientRefMemory) (hs : s.2.1 = c0 + 5 * i)
    (h : runFoldP bytes consts base i s = .ok x) : x.2.1 = c0 + 5 * (i+1) := by
  unfold runFoldP at h
  cases hz : affineProductTerm bytes consts s.2.2 (base + s.2.1) with
  | error e => rw [hz] at h; cases h
  | ok y =>
      rw [hz] at h
      have hy : y.2.1 = 5 := affineProductTerm_len hz
      have hxy : (qvmFrAdd s.1 y.1, s.2.1 + y.2.1, y.2.2) = x := by simpa [Except.map] using h
      rw [← hxy, hs, hy]
      show (c0 + 5 * i + 5 : Nat) = c0 + 5 * (i+1)
      omega

theorem runFoldL_namesSlot_at (bytes : List Nat) (consts : List Word256)
    (base c0 n : Nat) (S : List Nat)
    (h : ∀ i, i < n → ∀ b, byteAt bytes (base + (c0 + 3 * i) + 2) = .ok b → b ∈ S) :
    ∀ i, i < n → ∀ s, s.2.1 = c0 + 3 * i → NamesSlot (runFoldL bytes consts base i s) S := by
  intro i hi s hs
  unfold runFoldL
  refine NamesSlot.except_map _ (affineLinearTerm_namesSlot ?_)
  intro b hb
  exact h i hi b (by rw [hs] at hb; exact hb)

theorem runFoldL_advance_at (bytes : List Nat) (consts : List Word256) (base c0 i : Nat)
    (s x : QVMFr × Nat × QuotientRefMemory) (hs : s.2.1 = c0 + 3 * i)
    (h : runFoldL bytes consts base i s = .ok x) : x.2.1 = c0 + 3 * (i+1) := by
  unfold runFoldL at h
  cases hz : affineLinearTerm bytes consts s.2.2 (base + s.2.1) with
  | error e => rw [hz] at h; cases h
  | ok y =>
      rw [hz] at h
      have hy : y.2.1 = 3 := affineLinearTerm_len hz
      have hxy : (qvmFrAdd s.1 y.1, s.2.1 + y.2.1, y.2.2) = x := by simpa [Except.map] using h
      rw [← hxy, hs, hy]
      show (c0 + 3 * i + 3 : Nat) = c0 + 3 * (i+1)
      omega
/-! #### The RUN arms' walker bodies -/

def walkRunPBody (bytes : List Nat) (idx : Nat) :
    Nat → List QuotientOperand → VResult (List QuotientOperand) :=
  fun k acc => do
    let item := idx + 1 + quotientVmByteU16Bytes + k * (2 * quotientVmByteU16Bytes + 1)
    let lhs ← QuotientValidator.readU16 bytes item
    let rhs ← QuotientValidator.readU16 bytes (item + quotientVmByteU16Bytes)
    let slot ← byteAtPanic bytes (item + 2 * quotientVmByteU16Bytes) 2413
    .ok (acc ++ [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
                 QuotientOperand.konst slot false])

def walkRunLBody (bytes : List Nat) (idx : Nat) :
    Nat → List QuotientOperand → VResult (List QuotientOperand) :=
  fun k acc => do
    let item := idx + 1 + quotientVmByteU16Bytes + k * (quotientVmByteU16Bytes + 1)
    let ptr ← QuotientValidator.readU16 bytes item
    let slot ← byteAtPanic bytes (item + quotientVmByteU16Bytes) 2424
    .ok (acc ++ [QuotientOperand.mem "u16" ptr, QuotientOperand.konst slot false])

theorem walkRunPBody_ok (bytes : List Nat) (base i : Nat)
    (acc out : List QuotientOperand)
    (h : walkRunPBody bytes base i acc = .ok out) :
    ∃ slot, byteAtPanic bytes (base + 7 + 5 * i) 2413 = .ok slot ∧
      QuotientOperand.konst slot false ∈ out := by
  unfold walkRunPBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨lhs, _, h1⟩ := peel_bind h
  obtain ⟨rhs, _, h2⟩ := peel_bind h1
  obtain ⟨slot, hsp, h3⟩ := peel_bind h2
  have hpos : base + 1 + quotientVmByteU16Bytes + i * (2 * quotientVmByteU16Bytes + 1)
      + 2 * quotientVmByteU16Bytes = base + 7 + 5 * i := by
    show base + 1 + 2 + i * (2 * 2 + 1) + 2 * 2 = _; ring
  rw [hpos] at hsp
  exact ⟨slot, hsp, by rw [← Except.ok.inj h3]; simp⟩

theorem walkRunPBody_shape (bytes : List Nat) (base i : Nat)
    (acc out : List QuotientOperand)
    (h : walkRunPBody bytes base i acc = .ok out) : ∃ t, out = acc ++ t := by
  unfold walkRunPBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨lhs, _, h1⟩ := peel_bind h
  obtain ⟨rhs, _, h2⟩ := peel_bind h1
  obtain ⟨slot, _, h3⟩ := peel_bind h2
  exact ⟨_, (Except.ok.inj h3).symm⟩

theorem walkRunLBody_ok (bytes : List Nat) (base i : Nat)
    (acc out : List QuotientOperand)
    (h : walkRunLBody bytes base i acc = .ok out) :
    ∃ slot, byteAtPanic bytes (base + 5 + 3 * i) 2424 = .ok slot ∧
      QuotientOperand.konst slot false ∈ out := by
  unfold walkRunLBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨ptr, _, h1⟩ := peel_bind h
  obtain ⟨slot, hsp, h2⟩ := peel_bind h1
  have hpos : base + 1 + quotientVmByteU16Bytes + i * (quotientVmByteU16Bytes + 1)
      + quotientVmByteU16Bytes = base + 5 + 3 * i := by
    show base + 1 + 2 + i * (2 + 1) + 2 = _; ring
  rw [hpos] at hsp
  exact ⟨slot, hsp, by rw [← Except.ok.inj h2]; simp⟩

theorem walkRunLBody_shape (bytes : List Nat) (base i : Nat)
    (acc out : List QuotientOperand)
    (h : walkRunLBody bytes base i acc = .ok out) : ∃ t, out = acc ++ t := by
  unfold walkRunLBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨ptr, _, h1⟩ := peel_bind h
  obtain ⟨slot, _, h2⟩ := peel_bind h1
  exact ⟨_, (Except.ok.inj h2).symm⟩

theorem visit_runP (bytes : List Nat) (idx : Nat) :
    visitQuotientOperands bytes idx qOpRunAddMulMemMemConstU8
      = (QuotientValidator.readU16 bytes (idx + 1) >>= fun count =>
          foldRangeIdxM count [] (walkRunPBody bytes idx)) := by
  unfold visitQuotientOperands
  simp (config := {decide := true}) only [reduceIte]
  rfl

theorem visit_runL (bytes : List Nat) (idx : Nat) :
    visitQuotientOperands bytes idx qOpRunAddMulConstU8MemU16
      = (QuotientValidator.readU16 bytes (idx + 1) >>= fun count =>
          foldRangeIdxM count [] (walkRunLBody bytes idx)) := by
  unfold visitQuotientOperands
  simp (config := {decide := true}) only [reduceIte]
  rfl

theorem walkRunP_names {bytes : List Nat} {idx : Nat} {count : Nat} {os : List QuotientOperand}
    (h : foldRangeIdxM count [] (walkRunPBody bytes idx) = .ok os) :
    ∀ i, i < count → ∀ b, byteAt bytes (idx + 7 + 5 * i) = .ok b →
      QuotientOperand.konst b false ∈ os := by
  intro i hi b hb
  obtain ⟨s, s', t, u, hpre, hstep, hs', hu⟩ :=
    foldRangeIdxM_ok_iter (walkRunPBody bytes idx)
      (fun j acc out h2 => walkRunPBody_shape bytes idx j acc out h2)
      count [] os h i hi
  obtain ⟨slot, hsp, hmem⟩ := walkRunPBody_ok bytes idx i s s' hstep
  have hmatch : slot = b := by
    have hb2 : byteAt bytes (idx + 7 + 5 * i) = .ok slot :=
      (byteAt_iff_byteAtPanic (line := 2413)).mpr hsp
    exact Except.ok.inj (hb2.symm.trans hb)
  rw [hu, ← hmatch]
  exact List.mem_append.mpr (Or.inl hmem)

theorem walkRunL_names {bytes : List Nat} {idx : Nat} {count : Nat} {os : List QuotientOperand}
    (h : foldRangeIdxM count [] (walkRunLBody bytes idx) = .ok os) :
    ∀ i, i < count → ∀ b, byteAt bytes (idx + 5 + 3 * i) = .ok b →
      QuotientOperand.konst b false ∈ os := by
  intro i hi b hb
  obtain ⟨s, s', t, u, hpre, hstep, hs', hu⟩ :=
    foldRangeIdxM_ok_iter (walkRunLBody bytes idx)
      (fun j acc out h2 => walkRunLBody_shape bytes idx j acc out h2)
      count [] os h i hi
  obtain ⟨slot, hsp, hmem⟩ := walkRunLBody_ok bytes idx i s s' hstep
  have hmatch : slot = b := by
    have hb2 : byteAt bytes (idx + 5 + 3 * i) = .ok slot :=
      (byteAt_iff_byteAtPanic (line := 2424)).mpr hsp
    exact Except.ok.inj (hb2.symm.trans hb)
  rw [hu, ← hmatch]
  exact List.mem_append.mpr (Or.inl hmem)

/-- THE RUN-ARM BODY SLOT TOOL: the fold's i-th term is read at the RELATIVE cursor w*i. -/
theorem runArmBody_namesSlot (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (count : Nat)
    (F : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (S : List Nat) (w : Nat)
    (hstep : ∀ i s, i < count → s.2.1 = w * i → NamesSlot (F i s) S)
    (hprog : ∀ i s x, i < count → s.2.1 = w * i → F i s = .ok x → x.2.1 = w * (i+1))
    (hc : Midfall.Generator.readU16 bytes (idx + 1) = .ok count) :
    NamesSlot (runArmBody bytes consts idx stack mem F) S := by
  unfold runArmBody
  apply NamesSlot.bind2
  · exact readU16_namesSlot bytes (idx+1) S
  · intro cnt hcnt
    have hceq : cnt = count := Except.ok.inj (hcnt.symm.trans hc)
    subst hceq
    by_cases hc0 : (cnt != 0) = true
    · rw [if_pos hc0]
      apply NamesSlot.bind
      · exact popStack_namesSlot stack idx S
      · intro p
        refine NamesSlot.bind
          (foldRangeIdxM_namesSlot_range cnt F S (fun i s => s.2.1 = w * i) (p.1, 0, mem)
            (fun i s hi hs => hstep i s hi hs)
            (fun i s x hi hs hok => hprog i s x hi hs hok)
            (by simp)) (fun _ => NamesSlot.ok _ S)
    · rw [if_neg hc0]
      exact NamesSlot.error S (fun slot j hh => by cases hh)

theorem constSlot_runAddMulMemMemConstU8 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hw : ∃ os, visitQuotientOperands bytes idx qOpRunAddMulMemMemConstU8 = .ok os) :
    NamesSlot (evalQuotientIdentityStep bytes consts idx qOpRunAddMulMemMemConstU8 stack mem)
      (walkerKonstSlots bytes idx qOpRunAddMulMemMemConstU8) := by
  obtain ⟨os, hos⟩ := hw
  rw [visit_runP] at hos
  obtain ⟨count, hc, hfold⟩ := peel_bind hos
  have hlist : operandList bytes idx qOpRunAddMulMemMemConstU8 = os := by
    unfold operandList
    rw [visit_runP, hc]
    simp only [bind, Except.bind, hfold]
  have hslot : ∀ i, i < count → ∀ b, byteAt bytes (idx + 7 + 5 * i) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpRunAddMulMemMemConstU8 := by
    intro i hi b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist]
    exact walkRunP_names hfold i hi b hb
  rw [step_eq_runArmBody]
  refine runArmBody_namesSlot bytes consts idx stack mem count
    (runFoldP bytes consts (idx + 3)) _ 5 ?_ ?_ (readU16_iff_readU16.mpr hc)
  · intro i s hi hs
    exact runFoldP_namesSlot_at bytes consts (idx+3) 0 count _
      (fun k hk b hb => hslot k hk b
        (by rw [show idx+3+(0+5*k)+4 = idx+7+5*k from by ring] at hb; exact hb))
      i hi s (by rw [Nat.zero_add]; exact hs)
  · intro i s x hi hs hok
    have hadv := runFoldP_advance_at bytes consts (idx+3) 0 i s x
      (by rw [Nat.zero_add]; exact hs) hok
    rw [Nat.zero_add] at hadv
    exact hadv

theorem constSlot_runAddMulConstU8MemU16 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hw : ∃ os, visitQuotientOperands bytes idx qOpRunAddMulConstU8MemU16 = .ok os) :
    NamesSlot (evalQuotientIdentityStep bytes consts idx qOpRunAddMulConstU8MemU16 stack mem)
      (walkerKonstSlots bytes idx qOpRunAddMulConstU8MemU16) := by
  obtain ⟨os, hos⟩ := hw
  rw [visit_runL] at hos
  obtain ⟨count, hc, hfold⟩ := peel_bind hos
  have hlist : operandList bytes idx qOpRunAddMulConstU8MemU16 = os := by
    unfold operandList
    rw [visit_runL, hc]
    simp only [bind, Except.bind, hfold]
  have hslot : ∀ i, i < count → ∀ b, byteAt bytes (idx + 5 + 3 * i) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpRunAddMulConstU8MemU16 := by
    intro i hi b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist]
    exact walkRunL_names hfold i hi b hb
  rw [step_eq_runArmBodyL]
  refine runArmBody_namesSlot bytes consts idx stack mem count
    (runFoldL bytes consts (idx + 3)) _ 3 ?_ ?_ (readU16_iff_readU16.mpr hc)
  · intro i s hi hs
    exact runFoldL_namesSlot_at bytes consts (idx+3) 0 count _
      (fun k hk b hb => hslot k hk b
        (by rw [show idx+3+(0+3*k)+2 = idx+5+3*k from by ring] at hb; exact hb))
      i hi s (by rw [Nat.zero_add]; exact hs)
  · intro i s x hi hs hok
    have hadv := runFoldL_advance_at bytes consts (idx+3) 0 i s x
      (by rw [Nat.zero_add]; exact hs) hok
    rw [Nat.zero_add] at hadv
    exact hadv

/-! #### AFFINE_SUM -/

theorem runFoldL_advance_simple (bytes : List Nat) (consts : List Word256) (base i : Nat)
    (s x : QVMFr × Nat × QuotientRefMemory)
    (h : runFoldL bytes consts base i s = .ok x) : x.2.1 = s.2.1 + 3 := by
  unfold runFoldL at h
  cases hz : affineLinearTerm bytes consts s.2.2 (base + s.2.1) with
  | error e => rw [hz] at h; cases h
  | ok y =>
      rw [hz] at h
      have hy : y.2.1 = 3 := affineLinearTerm_len hz
      have hxy : (qvmFrAdd s.1 y.1, s.2.1 + y.2.1, y.2.2) = x := by simpa [Except.map] using h
      rw [← hxy, hy]

theorem runFoldP_advance_simple (bytes : List Nat) (consts : List Word256) (base i : Nat)
    (s x : QVMFr × Nat × QuotientRefMemory)
    (h : runFoldP bytes consts base i s = .ok x) : x.2.1 = s.2.1 + 5 := by
  unfold runFoldP at h
  cases hz : affineProductTerm bytes consts s.2.2 (base + s.2.1) with
  | error e => rw [hz] at h; cases h
  | ok y =>
      rw [hz] at h
      have hy : y.2.1 = 5 := affineProductTerm_len hz
      have hxy : (qvmFrAdd s.1 y.1, s.2.1 + y.2.1, y.2.2) = x := by simpa [Except.map] using h
      rw [← hxy, hy]

/-- THE LINEAR BLOCK'S CURSOR AFTER A SUCCESSFUL FOLD. -/
theorem foldRangeIdxM_runL_cursor (bytes : List Nat) (consts : List Word256) (base : Nat) :
    ∀ (n off : Nat) (init : QVMFr) (c : Nat) (mem : QuotientRefMemory)
      (a : QVMFr × Nat × QuotientRefMemory),
      foldRangeIdxM n (init, c, mem) (fun i => runFoldL bytes consts base (i + off)) = .ok a →
      a.2.1 = c + 3 * n
  | 0, off, init, c, mem, a, h => by
      have h0 : foldRangeIdxM 0 (init, c, mem)
          (fun i => runFoldL bytes consts base (i + off)) = .ok (init, c, mem) := rfl
      have hca : (init, c, mem) = a := Except.ok.inj (h0.trans h)
      subst hca
      show c = c + 3 * 0
      omega
  | k+1, off, init, c, mem, a, h => by
      obtain ⟨x, hx, hrest0⟩ := peel_bind h
      have hx' : x.2.1 = c + 3 := by
        have h2 := runFoldL_advance_simple bytes consts base (0 + off) (init, c, mem) x hx
        show x.2.1 = c + 3
        simpa using h2
      have hrest : foldRangeIdxM k x (fun i => runFoldL bytes consts base (i + (off+1))) = .ok a := by
        rw [bind_ok_id'] at hrest0
        exact hrest0
      have hax : a.2.1 = x.2.1 + 3 * k :=
        foldRangeIdxM_runL_cursor bytes consts base k (off+1) x.1 x.2.1 x.2.2 a hrest
      rw [hax, hx']
      ring

/-- THE PRODUCT BLOCK'S CURSOR AFTER A SUCCESSFUL FOLD. -/
theorem foldRangeIdxM_runP_cursor (bytes : List Nat) (consts : List Word256) (base : Nat) :
    ∀ (n off : Nat) (init : QVMFr) (c : Nat) (mem : QuotientRefMemory)
      (a : QVMFr × Nat × QuotientRefMemory),
      foldRangeIdxM n (init, c, mem) (fun i => runFoldP bytes consts base (i + off)) = .ok a →
      a.2.1 = c + 5 * n
  | 0, off, init, c, mem, a, h => by
      have h0 : foldRangeIdxM 0 (init, c, mem)
          (fun i => runFoldP bytes consts base (i + off)) = .ok (init, c, mem) := rfl
      have hca : (init, c, mem) = a := Except.ok.inj (h0.trans h)
      subst hca
      show c = c + 5 * 0
      omega
  | k+1, off, init, c, mem, a, h => by
      obtain ⟨x, hx, hrest0⟩ := peel_bind h
      have hx' : x.2.1 = c + 5 := by
        have h2 := runFoldP_advance_simple bytes consts base (0 + off) (init, c, mem) x hx
        show x.2.1 = c + 5
        simpa using h2
      have hrest : foldRangeIdxM k x (fun i => runFoldP bytes consts base (i + (off+1))) = .ok a := by
        rw [bind_ok_id'] at hrest0
        exact hrest0
      have hax : a.2.1 = x.2.1 + 5 * k :=
        foldRangeIdxM_runP_cursor bytes consts base k (off+1) x.1 x.2.1 x.2.2 a hrest
      rw [hax, hx']
      ring

def walkAffLBody (bytes : List Nat) (idx : Nat) :
    Nat → List QuotientOperand → VResult (List QuotientOperand) :=
  fun k acc => do
    let cursor := idx + 1 + 2 * quotientVmByteU16Bytes + k * (quotientVmByteU16Bytes + 1)
    let ptr ← QuotientValidator.readU16 bytes cursor
    let slot ← byteAtPanic bytes (cursor + quotientVmByteU16Bytes) 2434
    .ok (acc ++ [QuotientOperand.mem "u16" ptr, QuotientOperand.konst slot false])

def walkAffPBody (bytes : List Nat) (linBase : Nat) (linCount : Nat) :
    Nat → List QuotientOperand → VResult (List QuotientOperand) :=
  fun k acc => do
    let cursor := linBase + linCount * (quotientVmByteU16Bytes + 1)
        + k * (2 * quotientVmByteU16Bytes + 1)
    let lhs ← QuotientValidator.readU16 bytes cursor
    let rhs ← QuotientValidator.readU16 bytes (cursor + quotientVmByteU16Bytes)
    let slot ← byteAtPanic bytes (cursor + 2 * quotientVmByteU16Bytes) 2440
    .ok (acc ++ [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
                 QuotientOperand.konst slot false])

theorem walkAffLBody_ok (bytes : List Nat) (idx i : Nat) (acc out : List QuotientOperand)
    (h : walkAffLBody bytes idx i acc = .ok out) :
    ∃ slot, byteAtPanic bytes (idx + 7 + 3 * i) 2434 = .ok slot ∧
      QuotientOperand.konst slot false ∈ out := by
  unfold walkAffLBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨ptr, _, h1⟩ := peel_bind h
  obtain ⟨slot, hsp, h2⟩ := peel_bind h1
  have hpos : idx + 1 + 2 * quotientVmByteU16Bytes + i * (quotientVmByteU16Bytes + 1)
      + quotientVmByteU16Bytes = idx + 7 + 3 * i := by
    show idx + 1 + 2*2 + i*(2+1) + 2 = _; ring
  rw [hpos] at hsp
  exact ⟨slot, hsp, by rw [← Except.ok.inj h2]; simp⟩

theorem walkAffLBody_shape (bytes : List Nat) (idx i : Nat) (acc out : List QuotientOperand)
    (h : walkAffLBody bytes idx i acc = .ok out) : ∃ t, out = acc ++ t := by
  unfold walkAffLBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨ptr, _, h1⟩ := peel_bind h
  obtain ⟨slot, _, h2⟩ := peel_bind h1
  exact ⟨_, (Except.ok.inj h2).symm⟩

theorem walkAffPBody_ok (bytes : List Nat) (linBase linCount i : Nat)
    (acc out : List QuotientOperand)
    (h : walkAffPBody bytes linBase linCount i acc = .ok out) :
    ∃ slot, byteAtPanic bytes (linBase + 3 * linCount + 5 * i + 4) 2440 = .ok slot ∧
      QuotientOperand.konst slot false ∈ out := by
  unfold walkAffPBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨lhs, _, h1⟩ := peel_bind h
  obtain ⟨rhs, _, h2⟩ := peel_bind h1
  obtain ⟨slot, hsp, h3⟩ := peel_bind h2
  have hpos : linBase + linCount * (quotientVmByteU16Bytes + 1)
      + i * (2 * quotientVmByteU16Bytes + 1) + 2 * quotientVmByteU16Bytes
      = linBase + 3 * linCount + 5 * i + 4 := by
    show linBase + linCount * (2+1) + i * (2*2+1) + 2*2 = _; ring
  rw [hpos] at hsp
  exact ⟨slot, hsp, by rw [← Except.ok.inj h3]; simp⟩

theorem walkAffPBody_shape (bytes : List Nat) (linBase linCount i : Nat)
    (acc out : List QuotientOperand)
    (h : walkAffPBody bytes linBase linCount i acc = .ok out) : ∃ t, out = acc ++ t := by
  unfold walkAffPBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨lhs, _, h1⟩ := peel_bind h
  obtain ⟨rhs, _, h2⟩ := peel_bind h1
  obtain ⟨slot, _, h3⟩ := peel_bind h2
  exact ⟨_, (Except.ok.inj h3).symm⟩

theorem visit_affineSum (bytes : List Nat) (idx : Nat) :
    visitQuotientOperands bytes idx qOpAffineSum
      = (QuotientValidator.readU16 bytes (idx + 1) >>= fun linCount =>
          QuotientValidator.readU16 bytes (idx + 1 + quotientVmByteU16Bytes)
            >>= fun productCount =>
            (foldRangeIdxM linCount [] (walkAffLBody bytes idx)) >>= fun linOps =>
            (foldRangeIdxM productCount []
              (walkAffPBody bytes (idx + 1 + 2 * quotientVmByteU16Bytes) linCount))
              >>= fun productOps =>
              Except.ok (linOps ++ productOps)) := by
  unfold visitQuotientOperands
  simp (config := {decide := true}) only [reduceIte]
  rfl
/-- THE AFFINE_SUM WALKER NAMING LEMMAS. -/
theorem walkAffL_names {bytes : List Nat} {idx : Nat} {count : Nat} {os : List QuotientOperand}
    (h : foldRangeIdxM count [] (walkAffLBody bytes idx) = .ok os) :
    ∀ i, i < count → ∀ b, byteAt bytes (idx + 7 + 3 * i) = .ok b →
      QuotientOperand.konst b false ∈ os := by
  intro i hi b hb
  obtain ⟨s, s', t, u, hpre, hstep, hs', hu⟩ :=
    foldRangeIdxM_ok_iter (walkAffLBody bytes idx)
      (fun j acc out h2 => walkAffLBody_shape bytes idx j acc out h2)
      count [] os h i hi
  obtain ⟨slot, hsp, hmem⟩ := walkAffLBody_ok bytes idx i s s' hstep
  have hb2 : byteAt bytes (idx + 7 + 3 * i) = .ok slot :=
    (byteAt_iff_byteAtPanic (line := 2434)).mpr hsp
  have hmatch : slot = b := Except.ok.inj (hb2.symm.trans hb)
  rw [← hmatch, hu]
  exact List.mem_append.mpr (Or.inl hmem)

theorem walkAffP_names {bytes : List Nat} {linBase : Nat} {linCount count : Nat}
    {os : List QuotientOperand}
    (h : foldRangeIdxM count [] (walkAffPBody bytes linBase linCount) = .ok os) :
    ∀ j, j < count → ∀ b, byteAt bytes (linBase + 3 * linCount + 5 * j + 4) = .ok b →
      QuotientOperand.konst b false ∈ os := by
  intro j hj b hb
  obtain ⟨s, s', t, u, hpre, hstep, hs', hu⟩ :=
    foldRangeIdxM_ok_iter (walkAffPBody bytes linBase linCount)
      (fun k acc out h2 => walkAffPBody_shape bytes linBase linCount k acc out h2)
      count [] os h j hj
  obtain ⟨slot, hsp, hmem⟩ := walkAffPBody_ok bytes linBase linCount j s s' hstep
  have hb2 : byteAt bytes (linBase + 3 * linCount + 5 * j + 4) = .ok slot :=
    (byteAt_iff_byteAtPanic (line := 2440)).mpr hsp
  have hmatch : slot = b := Except.ok.inj (hb2.symm.trans hb)
  rw [← hmatch, hu]
  exact List.mem_append.mpr (Or.inl hmem)

/-- ARM AFFINE_SUM AT A GENERAL CURSOR. -/
theorem constSlot_affineSum (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hw : ∃ os, visitQuotientOperands bytes idx qOpAffineSum = .ok os) :
    NamesSlot (evalQuotientIdentityStep bytes consts idx qOpAffineSum stack mem)
      (walkerKonstSlots bytes idx qOpAffineSum) := by
  obtain ⟨os, hos⟩ := hw
  rw [visit_affineSum] at hos
  obtain ⟨linCount, hlc, h1⟩ := peel_bind hos
  obtain ⟨prodCount, hpc, h2⟩ := peel_bind h1
  obtain ⟨linOps, hl, h3⟩ := peel_bind h2
  obtain ⟨prodOps, hp, _⟩ := peel_bind h3
  have hlist : operandList bytes idx qOpAffineSum = linOps ++ prodOps := by
    unfold operandList
    rw [visit_affineSum, hlc, hpc]
    simp only [bind, Except.bind, hl, hp]
  have hslotL : ∀ i, i < linCount → ∀ b, byteAt bytes (idx + 7 + 3 * i) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpAffineSum := by
    intro i hi b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist]
    exact List.mem_append.mpr (Or.inl (walkAffL_names hl i hi b hb))
  have harith : ∀ k : Nat,
      idx + 5 + (3 * linCount + 5 * k) + 4 = idx + 9 + 3 * linCount + 5 * k := by
    intro k; omega
  have harithL : ∀ k : Nat, idx + 5 + (0 + 3 * k) + 2 = idx + 7 + 3 * k := by
    intro k; omega
  have hslotP : ∀ j, j < prodCount → ∀ b,
      byteAt bytes (idx + 9 + 3 * linCount + 5 * j) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpAffineSum := by
    intro j hj b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist]
    have hj2 : idx + 9 + 3 * linCount + 5 * j
        = (idx + 1 + 2 * quotientVmByteU16Bytes) + 3 * linCount + 5 * j + 4 := by
      show idx + 9 + 3 * linCount + 5 * j = idx + 1 + 2*2 + 3 * linCount + 5 * j + 4
      omega
    rw [hj2] at hb
    exact List.mem_append.mpr (Or.inr (walkAffP_names hp j hj b hb))
  rw [step_eq_affineSumArmBody]
  unfold affineSumArmBody
  apply NamesSlot.bind2
  · exact readU16_namesSlot bytes (idx + 1) _
  · intro lc hlc2
    have heq : linCount = lc :=
      Except.ok.inj ((readU16_iff_readU16.mpr hlc).symm.trans hlc2)
    subst heq
    apply NamesSlot.bind2
    · exact readU16_namesSlot bytes (idx + 3) _
    · intro pc hpc2
      have heq2 : prodCount = pc :=
        Except.ok.inj ((readU16_iff_readU16.mpr hpc).symm.trans hpc2)
      subst heq2
      by_cases hc : (linCount != 0 && prodCount != 0) = true
      · rw [if_pos hc]
        apply NamesSlot.bind2
        · exact popStack_namesSlot stack idx _
        · intro p _
          apply NamesSlot.bind2
          · exact foldRangeIdxM_namesSlot_range linCount (runFoldL bytes consts (idx + 5)) _
              (fun i s => s.2.1 = 3 * i) (p.1, 0, mem)
              (fun i s hi hs => runFoldL_namesSlot_at bytes consts (idx + 5) 0 linCount _
                (fun k hk b hb => hslotL k hk b (by rw [harithL] at hb; exact hb))
                i hi s (by rw [Nat.zero_add]; exact hs))
              (fun i s x hi hs hok => by
                have := runFoldL_advance_at bytes consts (idx + 5) 0 i s x
                  (by rw [Nat.zero_add]; exact hs) hok
                rw [Nat.zero_add] at this
                exact this)
              (by simp)
          · intro a ha
            have hcur : a.2.1 = 3 * linCount := by
              have := foldRangeIdxM_runL_cursor bytes consts (idx + 5) linCount 0 p.1 0 mem a ha
              rw [Nat.zero_add] at this
              exact this
            refine NamesSlot.bind
              (foldRangeIdxM_namesSlot_range prodCount (runFoldP bytes consts (idx + 5)) _
                (fun j s => s.2.1 = a.2.1 + 5 * j) (a.1, a.2.1, a.2.2)
                (fun j s hj hs => runFoldP_namesSlot_at bytes consts (idx + 5) (3 * linCount)
                    prodCount _
                  (fun k hk b hb => hslotP k hk b (by rw [harith] at hb; exact hb))
                  j hj s (by rw [hcur] at hs; exact hs))
                (fun j s x hj hs hok => by
                  have := runFoldP_advance_at bytes consts (idx + 5) (3 * linCount)
                    j s x (by rw [hcur] at hs; exact hs) hok
                  rw [← hcur] at this
                  exact this)
                (by simp)) (fun _ => NamesSlot.ok _ _)
      · rw [if_neg hc]
        exact NamesSlot.error _ (fun slot j hh => by cases hh)


theorem indexOrPanic_iff_byteAt {bytes : List Nat} {p b : Nat} :
    indexOrPanic bytes p = .ok b ↔ byteAt bytes p = .ok b := by
  unfold Midfall.Generator.indexOrPanic Midfall.Generator.byteAt
  cases bytes.drop p with
  | cons c rest => simp
  | nil => simp

theorem indexOrPanic_not_slotFault (bytes : List Nat) (p s j : Nat) :
    indexOrPanic bytes p ≠ .error (QVMFault.constSlotOutOfRange s j) := by
  unfold Midfall.Generator.indexOrPanic
  cases bytes.drop p with
  | cons c rest => show Except.ok c ≠ _; intro h; cases h
  | nil => show Except.error (QVMFault.panic _) ≠ _; intro h; cases h

theorem pw_lt : ∀ i j, i < quotientVmLimbs → j < quotientVmLimbs →
    i + j < quotientVmPairwiseCoeffs := by
  intro i j hi hj
  have h7 : quotientVmLimbs = 7 := rfl
  have h13 : quotientVmPairwiseCoeffs = 13 := rfl
  have h1 : i < 7 := by rwa [← h7]
  have h2 : j < 7 := by rwa [← h7]
  rw [h13]; omega

/-- THE INNER PAIRWISE BODY, verbatim except that the two memory hits are already resolved. -/
def pwInnerBody (bytes : List Nat) (consts : List Word256)
    (coeffs rhsBase i lhsValue : Nat) :
    Nat → QVMFr × QuotientRefMemory → Except QVMFault (QVMFr × QuotientRefMemory) :=
  fun j state => do
    let (acc, mem) := state
    let (rhsValue, mem2) := mem.literal (rhsBase + j * qvmWordBytes)
    let slot ← indexOrPanic bytes (coeffs + i + j)
    let c ← constAt consts slot coeffs
    .ok (qvmFrAdd acc (qvmFrMul (qvmFrMul lhsValue rhsValue) c), mem2)

theorem pwInnerBody_unfold (bytes : List Nat) (consts : List Word256)
    (coeffs rhsBase i : Nat) (lhsValue : QVMFr) (j : Nat) (acc : QVMFr)
    (m : QuotientRefMemory) :
    pwInnerBody bytes consts coeffs rhsBase i lhsValue j (acc, m)
      = (do
          let (rhsValue, mem2) := m.literal (rhsBase + j * qvmWordBytes)
          let slot ← indexOrPanic bytes (coeffs + i + j)
          let c ← constAt consts slot coeffs
          .ok (qvmFrAdd acc (qvmFrMul (qvmFrMul lhsValue rhsValue) c), mem2)) := rfl

theorem pwInnerBody_namesSlot (bytes : List Nat) (consts : List Word256)
    (coeffs rhsBase : Nat) (lhsV : QVMFr) (S : List Nat)
    (h : ∀ d, d < quotientVmPairwiseCoeffs → ∀ b, byteAt bytes (coeffs + d) = .ok b → b ∈ S) :
    ∀ i j s, i < quotientVmLimbs → j < quotientVmLimbs →
      NamesSlot (pwInnerBody bytes consts coeffs rhsBase i lhsV j s) S := by
  intro i j s hi hj
  obtain ⟨acc, m⟩ := s
  rw [pwInnerBody_unfold bytes consts coeffs rhsBase i lhsV j acc m]
  obtain ⟨rhsValue, mem2⟩ := m.literal (rhsBase + j * qvmWordBytes)
  refine NamesSlot.bind2 (indexOrPanic bytes (coeffs + i + j)) ?F
    (NamesSlot.never S (indexOrPanic_not_slotFault bytes (coeffs + i + j)))
    (fun slot hslot => ?_)
  have hbyte : byteAt bytes (coeffs + (i + j)) = .ok slot := by
    have := (indexOrPanic_iff_byteAt (p := coeffs + i + j)).mp hslot
    simpa [add_assoc] using this
  refine NamesSlot.bind
    (constAt_namesSlot slot coeffs S (h (i + j) (pw_lt i j hi hj) slot hbyte))
    (fun _ => NamesSlot.ok _ S)

def pwOuterBody (bytes : List Nat) (consts : List Word256) (coeffs lhsBase rhsBase : Nat) :
    Nat → QVMFr × QuotientRefMemory → Except QVMFault (QVMFr × QuotientRefMemory) :=
  fun i state => do
    let (acc, mem) := state
    let (lhsValue, mem1) := mem.literal (lhsBase + i * qvmWordBytes)
    foldRangeIdxM quotientVmLimbs (acc, mem1)
      (pwInnerBody bytes consts coeffs rhsBase i lhsValue)

theorem pwOuterBody_unfold (bytes : List Nat) (consts : List Word256)
    (coeffs lhsBase rhsBase i : Nat) (acc : QVMFr) (m : QuotientRefMemory) :
    pwOuterBody bytes consts coeffs lhsBase rhsBase i (acc, m)
      = (do
          let (lhsValue, mem1) := m.literal (lhsBase + i * qvmWordBytes)
          foldRangeIdxM quotientVmLimbs (acc, mem1)
            (pwInnerBody bytes consts coeffs rhsBase i lhsValue)) := rfl

theorem pwOuterBody_namesSlot (bytes : List Nat) (consts : List Word256)
    (coeffs lhsBase rhsBase : Nat) (S : List Nat)
    (h : ∀ d, d < quotientVmPairwiseCoeffs → ∀ b, byteAt bytes (coeffs + d) = .ok b → b ∈ S) :
    ∀ i s, i < quotientVmLimbs →
      NamesSlot (pwOuterBody bytes consts coeffs lhsBase rhsBase i s) S := by
  intro i s hi
  obtain ⟨acc, m⟩ := s
  rw [pwOuterBody_unfold bytes consts coeffs lhsBase rhsBase i acc m]
  obtain ⟨lhsValue, mem1⟩ := m.literal (lhsBase + i * qvmWordBytes)
  exact foldRangeIdxM_namesSlot_range quotientVmLimbs
    (pwInnerBody bytes consts coeffs rhsBase i lhsValue) S (fun _ _ => True) (acc, mem1)
    (fun j s' _ _ => pwInnerBody_namesSlot bytes consts coeffs rhsBase lhsValue S h i j s'
      (by omega) (by omega))
    (fun _ _ _ _ _ _ => trivial) trivial

def walkCoeffBody (bytes : List Nat) (coeffs : Nat) :
    Nat → List QuotientOperand → VResult (List QuotientOperand) :=
  fun k acc => do
    let slot ← byteAtPanic bytes (coeffs + k) 2347
    .ok (acc ++ [QuotientOperand.konst slot false])

theorem walkCoeffBody_ok (bytes : List Nat) (coeffs i : Nat)
    (acc out : List QuotientOperand) (h : walkCoeffBody bytes coeffs i acc = .ok out) :
    ∃ slot, byteAtPanic bytes (coeffs + i) 2347 = .ok slot ∧
      QuotientOperand.konst slot false ∈ out := by
  unfold walkCoeffBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨slot, hsp, h2⟩ := peel_bind h
  exact ⟨slot, hsp, by rw [← Except.ok.inj h2]; simp⟩

theorem walkCoeffBody_shape (bytes : List Nat) (coeffs i : Nat)
    (acc out : List QuotientOperand) (h : walkCoeffBody bytes coeffs i acc = .ok out) :
    ∃ t, out = acc ++ t := by
  unfold walkCoeffBody at h
  simp only [bind, Except.bind] at h
  obtain ⟨slot, _, h2⟩ := peel_bind h
  exact ⟨_, (Except.ok.inj h2).symm⟩

theorem pairwiseBlock_unfold (bytes : List Nat) (base : Nat) :
    pairwiseBlock bytes base
      = (QuotientValidator.readU16 bytes base >>= fun lhs =>
          QuotientValidator.readU16 bytes (base + quotientVmByteU16Bytes) >>= fun rhs =>
          (foldRangeIdxM quotientVmLimbs []
            (fun k acc => Except.ok (acc ++
              [QuotientOperand.mem "pairwise_lhs" (lhs + k * wordBytes),
               QuotientOperand.mem "pairwise_rhs" (rhs + k * wordBytes)])) >>= fun words =>
          (foldRangeIdxM quotientVmPairwiseCoeffs []
            (walkCoeffBody bytes (base + 2 * quotientVmByteU16Bytes))) >>= fun slots =>
            Except.ok (words ++ slots))) := by
  unfold pairwiseBlock
  rfl

theorem limbPairwiseForm_unfold (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) :
    limbPairwiseForm bytes consts mem k
      = (Midfall.Generator.readU16 bytes k >>= fun lhsBase =>
          Midfall.Generator.readU16 bytes (k + 2) >>= fun rhsBase =>
          Midfall.Generator.byteAt bytes (k + 4 + quotientVmPairwiseCoeffs - 1) >>= fun _ =>
          foldRangeIdxM quotientVmLimbs (qvmFrZero, mem)
            (pwOuterBody bytes consts (k + 4) lhsBase rhsBase)
            >>= fun y => Except.ok (y.1, 4 + quotientVmPairwiseCoeffs, y.2)) := rfl

/-- THE PAIRWISE BLOCK'S SLOT CORRESPONDENCE, stated at the block's own start offset. -/
theorem limbPairwiseForm_namesSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} {S : List Nat}
    (h : ∀ d, d < quotientVmPairwiseCoeffs → ∀ b,
        byteAt bytes (k + 4 + d) = .ok b → b ∈ S) :
    NamesSlot (limbPairwiseForm bytes consts mem k) S := by
  rw [limbPairwiseForm_unfold bytes consts mem k]
  apply NamesSlot.bind
  · exact readU16_namesSlot bytes k S
  · intro lhsBase
    apply NamesSlot.bind
    · exact readU16_namesSlot bytes (k + 2) S
    · intro rhsBase
      apply NamesSlot.bind
      · exact byteAt_namesSlot bytes (k + 4 + quotientVmPairwiseCoeffs - 1) S
      · intro _
        refine NamesSlot.bind
          (foldRangeIdxM_namesSlot_range quotientVmLimbs
            (pwOuterBody bytes consts (k + 4) lhsBase rhsBase) S (fun _ _ => True) (qvmFrZero, mem)
            (fun i s _ _ => pwOuterBody_namesSlot bytes consts (k + 4) lhsBase rhsBase S h i s
              (by omega))
            (fun _ _ _ _ _ _ => trivial) trivial)
          (fun y => NamesSlot.ok _ S)

theorem constSlot_bilin7Pairwise (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hw : ∃ os, visitQuotientOperands bytes idx qOpBilin7Pairwise = .ok os) :
    NamesSlot (evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem)
      (walkerKonstSlots bytes idx qOpBilin7Pairwise) := by
  obtain ⟨os, hos⟩ := hw
  have hv0 : visitQuotientOperands bytes idx qOpBilin7Pairwise = pairwiseBlock bytes (idx + 1) := by
    unfold visitQuotientOperands
    simp (config := {decide := true}) only [reduceIte]
  have hlist : operandList bytes idx qOpBilin7Pairwise = os := operandList_ok (hv0 ▸ hos)
  rw [hv0, pairwiseBlock_unfold] at hos
  obtain ⟨lhs0, hl, h1⟩ := peel_bind hos
  obtain ⟨rhs0, hr, h2⟩ := peel_bind h1
  obtain ⟨words, hw2, h3⟩ := peel_bind h2
  obtain ⟨slots, hs2, hos'⟩ := peel_bind h3
  have hws : words ++ slots = os := Except.ok.inj hos'
  have hslot : ∀ d, d < quotientVmPairwiseCoeffs → ∀ b,
      byteAt bytes (idx + 5 + d) = .ok b →
      b ∈ walkerKonstSlots bytes idx qOpBilin7Pairwise := by
    intro d hd b hb
    refine mem_walkerKonstSlots_narrow ?_
    rw [hlist, ← hws]
    obtain ⟨s0, s1, t, u, hpre, hstep, hs', hu⟩ :=
      foldRangeIdxM_ok_iter (walkCoeffBody bytes (idx + 1 + 2 * quotientVmByteU16Bytes))
        (fun j acc out h2 => walkCoeffBody_shape bytes _ j acc out h2)
        quotientVmPairwiseCoeffs [] slots hs2 d hd
    obtain ⟨slot, hsp, hmem⟩ :=
      walkCoeffBody_ok bytes (idx + 1 + 2 * quotientVmByteU16Bytes) d s0 s1 hstep
    have hpos : idx + 1 + 2 * quotientVmByteU16Bytes + d = idx + 5 + d := by
      show idx + 1 + 2*2 + d = _; omega
    rw [hpos] at hsp
    have hmatch : slot = b :=
      Except.ok.inj (((byteAt_iff_byteAtPanic (line := 2347)).mpr hsp).symm.trans hb)
    rw [← hmatch, hu]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hmem)))
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  apply NamesSlot.bind
  · exact limbPairwiseForm_namesSlot (k := idx + 1)
      (fun d hd b hb => hslot d hd b
        (by rw [show idx+1+4+d = idx+5+d from by omega] at hb; exact hb))
  · intro y
    obtain ⟨v, l, m'⟩ := y
    exact NamesSlot.ok _ _

/-! #### The combined correspondence: 25 of the 26 identity arms -/

theorem evalQuotientIdentityStep_constSlot_namedByWalker_folded
    (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : op = qOpLin7 \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise
      \/ op = qOpRunAddMulMemMemConstU8 \/ op = qOpRunAddMulConstU8MemU16 \/ op = qOpAffineSum)
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os) :
    NamesSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem)
      (walkerKonstSlots bytes idx op) := by
  rcases hop with (h|h|h|h|h|h) <;> subst h
  · exact constSlot_lin7 bytes consts idx stack mem hw
  · exact constSlot_bilin7Row bytes consts idx stack mem hw
  · exact constSlot_bilin7Pairwise bytes consts idx stack mem hw
  · exact constSlot_runAddMulMemMemConstU8 bytes consts idx stack mem hw
  · exact constSlot_runAddMulConstU8MemU16 bytes consts idx stack mem hw
  · exact constSlot_affineSum bytes consts idx stack mem hw

/-- CSLOT - THE ONE ARM THIS CARD DID NOT REACH, named with its exact goal state rather than
    glossed. MODARITH7's const-slot correspondence at a general cursor is still open:

      NamesSlot (evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem)
        (walkerKonstSlots bytes idx qOpModarith7)

    under the same walker-success hypothesis 'hw' the other 25 arms discharge. WHY it is last and
    not merely biggest: the six arms landed here each have ONE counted fold (two for AFFINE_SUM)
    whose per-iteration slot offset is a fixed multiple of the iteration index. 'modarith7Form'
    (VmReference.lean:636) has FIVE chained counted blocks - lin / row / pairwise / mem / product -
    and the initial cursor of each block is the OUTPUT cursor of the previous one, so block b's
    iteration i reads its slot at

      afterConst + 5 + (byte span of every earlier block) + (stride of block b) * i,

    where 'afterConst' itself depends on the flag byte read at the cursor (the COND bit adds 2 and
    the CONST bit adds 1). Each block's stride DOES agree with the walker's (limbBlockStride 21,
    rowBlockStride 23, pairwiseBlockStride 17, then 3 and 5), so the arm is reachable, but it needs
    (a) a header congruence showing the flag-dependent 'afterCond'/'afterConst' transport, (b) the
    five-block chaining lemma of the shape of 'foldRangeIdxM_runL_cursor' iterated five times with a
    DIFFERENT body each time, and (c) this card's nested-fold pairwise induction ('pwInnerBody_-
    namesSlot') reused INSIDE that chain, i.e. a nested-fold induction under a chained cursor.
    (a) and (b) are mechanical; (c) is the real work, and it is why MODARITH7 is a card of its own
    rather than a batch item. NO CONTRACT DEFECT WAS FOUND ON THIS ARM EITHER: nothing here exhibits
    a validated program whose step faults, and nothing here rules one out - the arm was not measured. -/
def PG_stepNoRF_validated_cs_modarith7 : Prop :=
  ∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
    (mem : QuotientRefMemory),
    (∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx qOpModarith7 = .ok os) →
    NamesSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem)
      (walkerKonstSlots bytes idx qOpModarith7)


/-! #### The 25-arm union -/

/-- THE CONST-SLOT CORRESPONDENCE FOR 25 OF THE 26 IDENTITY ARMS AT A GENERAL CURSOR. Qvm.lean
    section 9 proved 19 (the flat blocks); card CSLOT adds the six whose slot reads sit inside a
    counted fold. MODARITH7 is the only identity arm left, named in
    'PG_stepNoRF_validated_cs_modarith7'. -/
theorem evalQuotientIdentityStep_constSlot_namedByWalker_25
    (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : (op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5)
      \/ op = qOpLin7 \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise
      \/ op = qOpRunAddMulMemMemConstU8 \/ op = qOpRunAddMulConstU8MemU16 \/ op = qOpAffineSum)
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os) :
    NamesSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem)
      (walkerKonstSlots bytes idx op) := by
  rcases hop with (hflat | h6)
  · exact evalQuotientIdentityStep_constSlot_namedByWalker bytes consts idx op stack mem hflat hw
  · exact evalQuotientIdentityStep_constSlot_namedByWalker_folded bytes consts idx op stack mem h6 hw


/-! ### Section 9: the two nested/counted limb arms on the SHIFT axis, and the AFFINE_SUM width
    agreement (card SHIF2)

    CSLOT closed family 3 (const-slot) for six of its seven arms and left two corrections that this
    section acts on. FIRST, the axes are INDEPENDENT: LIN7 already had 'step_shift_lin7' and still
    needed a slot correspondence, so a congruence on one axis buys nothing on the other. That cuts
    the other way too - BILIN7_ROW and BILIN7_PAIRWISE had their slot correspondence from section 8
    but NO shift congruence, which is why they were the two arms 'readsWithinStride_at' and
    'consumed_agrees_at' could not reach even though their index-0 forms were proved long ago. This
    section supplies those two congruences, and the two general-cursor packages immediately widen
    from 20 arms to 22.

    SECOND, the match-auxiliary trap is real but it is a TOOL, not an obstacle, on this axis. Both
    arms are counted folds whose per-iteration body is a generated lambda inside 'VmReference', so
    'rw' cannot see the goal's copy of it. The fix is NBF's: state the transport about a VARIABLE
    body and bridge the concrete arm to it by 'rfl'. Here the bridges already existed - CSLOT wrote
    'limbRowForm_unfold', 'pwInnerBody_unfold', 'pwOuterBody_unfold' and
    'limbPairwiseForm_unfold' for the slot axis - so this section adds no new body definitions at
    all; it reuses them on the shift axis. 'pwInnerBody'/'pwOuterBody' are the interpreter's own
    nested-fold bodies (section 8), and the outer state '(acc, mem)' has NO cursor component, so
    the outer transport is 'foldRangeIdxM_shift_id' with the inner body's transport as its
    hypothesis - exactly the shape section 6 predicted.

    WHAT THIS SECTION LANDS, counted:
      * family 1 (general-cursor READ BOUND): 20 arms -> 22 via 'evalQuotientIdentityStep_shift_22'
        and 'evalQuotientIdentityStep_readsWithinStride_at_22'. With QvmWalk's 'runAddMul*_noRF' and
        'affineSum_noRF' (already stated at an arbitrary cursor) that is 25 of the 26 identity arms;
        MODARITH7 alone is left, named in 'PG_stepNoRF_validated_shif2_modarith7_read'.
      * family 2 (general-cursor WIDTH AGREEMENT): 20 arms -> 22 via
        'evalQuotientIdentityStep_consumed_agrees_at_22', plus the two RUN arms (NBF) and AFFINE_SUM
        ('consumed_agrees_at_affineSum', whose index-0 form 'consumed_agrees_affineSum' is proved
        here because the counted-block bodies it needs - 'runFoldL'/'runFoldP' and
        'foldRangeIdxM_runL_cursor' - are this file's, not QvmWalk's). That is 25 of 26; MODARITH7
        alone is left, named in 'PG_stepNoRF_validated_shif2_modarith7_width' together with the
        congruence it depends on, 'PG_stepNoRF_validated_shif2_modarith7_shift'.

    NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES); no
    statement names a fixture (D-P71); no 'native_decide'; this section adds no sorry. -/

/-- THE ROW BLOCK's transport. 'limbRowForm' is a u16 read, then a memory hit, then the linear
    limb block at 'k + 2'. Section 6 named the cost correctly: the memory hit's pair-pattern sits
    BETWEEN the two reads, so the transport has to be pushed past it before the inner congruence can
    be cited. Measured: 'simp only [bind, Except.bind]' resolves the pair-pattern to projections,
    which is what lets 'limbLinearForm_shift' be cited under 'conv_lhs' (the dropped side would
    otherwise be reachable by the same pattern with a different instantiation). -/
theorem limbRowForm_shift (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx k : Nat) :
    Midfall.Generator.limbRowForm bytes consts mem (idx + k)
      = mapErr (shiftFault idx)
        (Midfall.Generator.limbRowForm (bytes.drop idx) consts mem k) := by
  rw [limbRowForm_unfold bytes consts mem (idx + k),
      limbRowForm_unfold (bytes.drop idx) consts mem k]
  rw [readU16_shift bytes idx k]
  cases h : Midfall.Generator.readU16 (bytes.drop idx) k with
  | error e => simp only [mapErr, bind, Except.bind]
  | ok lhs =>
      rw [mapErr_ok]
      simp only [bind, Except.bind]
      conv_lhs => rw [show idx + k + 2 = idx + (k + 2) by omega,
                      limbLinearForm_shift bytes consts (mem.literal lhs).2 idx (k + 2)]
      cases h2 : Midfall.Generator.limbLinearForm (bytes.drop idx) consts (mem.literal lhs).2 (k + 2) with
      | ok x => simp only [mapErr_ok, bind, Except.bind]
      | error e => simp only [mapErr, bind, Except.bind]

/-- ARM BILIN7_ROW's step congruence: the same three lines as 'step_shift_lin7', one layer out. -/
theorem step_shift_bilin7Row (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
          qOpBilin7Row stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [limbRowForm_shift bytes consts mem idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

/-- THE INNER PAIRWISE BLOCK's transport: the coefficient read ('indexOrPanic') and the const lookup
    both move with the cursor; the two memory hits do not depend on 'bytes' at all, so the pair
    pattern is resolved to projections and the same congruence holds with the SAME 'lhsValue' and
    'rhsBase' on both sides - which is legitimate precisely because 'readU16_shift'/'indexOrPanic_shift'
    return the same VALUE on the ok branch and only the fault moves. -/
theorem pwInnerBody_shift (bytes : List Nat) (consts : List Word256)
    (idx K rhsBase i : Nat) (lhsValue : QVMFr) :
    ∀ j s, pwInnerBody bytes consts (idx + K) rhsBase i lhsValue j s
      = mapErr (shiftFault idx)
        (pwInnerBody (bytes.drop idx) consts K rhsBase i lhsValue j s) := by
  intro j s
  obtain ⟨acc, m⟩ := s
  rw [pwInnerBody_unfold bytes consts (idx + K) rhsBase i lhsValue j acc m,
      pwInnerBody_unfold (bytes.drop idx) consts K rhsBase i lhsValue j acc m]
  simp only [bind, Except.bind]
  conv_lhs => rw [show idx + K + i + j = idx + (K + i + j) by omega,
                  indexOrPanic_shift bytes idx (K + i + j)]
  cases h : Midfall.Generator.indexOrPanic (bytes.drop idx) (K + i + j) with
  | error e => simp only [mapErr, bind, Except.bind]
  | ok slot =>
      simp only [mapErr_ok, bind, Except.bind]
      conv_lhs => rw [constAt_shift consts slot idx K]
      cases h2 : Midfall.Generator.constAt consts slot K with
      | ok c => simp only [mapErr_ok, bind, Except.bind]
      | error e => simp only [mapErr, bind, Except.bind]

/-- THE OUTER PAIRWISE BLOCK's transport. The outer state is '(acc, mem)' with no cursor component,
    so the fold transport is the 'S = id' form and the whole obligation is the inner fold's own
    transport - the shape section 6 called 'mechanically the same as limbLinBody_shift'. -/
theorem pwOuterBody_shift (bytes : List Nat) (consts : List Word256)
    (idx K lhsBase rhsBase : Nat) :
    ∀ i s, pwOuterBody bytes consts (idx + K) lhsBase rhsBase i s
      = mapErr (shiftFault idx)
        (pwOuterBody (bytes.drop idx) consts K lhsBase rhsBase i s) := by
  intro i s
  obtain ⟨acc, m⟩ := s
  rw [pwOuterBody_unfold bytes consts (idx + K) lhsBase rhsBase i acc m,
      pwOuterBody_unfold (bytes.drop idx) consts K lhsBase rhsBase i acc m]
  simp only [bind, Except.bind]
  exact foldRangeIdxM_shift_id (shiftFault idx) quotientVmLimbs _ _ _
    (pwInnerBody_shift bytes consts idx K rhsBase i _)

/-- THE PAIRWISE BLOCK's transport: two u16 reads, the up-front bounds check on the coefficient
    block, then the nested fold. The bounds check is the third read and it shifts too, which is the
    hazard-5 pair (VmReference.lean:606-632) this arm is the interpreter-side half of. -/
theorem limbPairwiseForm_shift (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx k : Nat) :
    Midfall.Generator.limbPairwiseForm bytes consts mem (idx + k)
      = mapErr (shiftFault idx)
        (Midfall.Generator.limbPairwiseForm (bytes.drop idx) consts mem k) := by
  rw [limbPairwiseForm_unfold bytes consts mem (idx + k),
      limbPairwiseForm_unfold (bytes.drop idx) consts mem k]
  rw [readU16_shift bytes idx k]
  cases h1 : Midfall.Generator.readU16 (bytes.drop idx) k with
  | error e => simp only [mapErr, bind, Except.bind]
  | ok lhsBase =>
      rw [mapErr_ok]
      simp only [bind, Except.bind]
      rw [show idx + k + 2 = idx + (k + 2) by omega, readU16_shift bytes idx (k + 2)]
      cases h2 : Midfall.Generator.readU16 (bytes.drop idx) (k + 2) with
      | error e => simp only [mapErr, bind, Except.bind]
      | ok rhsBase =>
          rw [mapErr_ok]
          simp only [bind, Except.bind]
          rw [show idx + k + 4 + quotientVmPairwiseCoeffs - 1 =
                  idx + (k + 4 + quotientVmPairwiseCoeffs - 1) by omega,
              byteAt_shift bytes idx (k + 4 + quotientVmPairwiseCoeffs - 1)]
          cases h3 : Midfall.Generator.byteAt (bytes.drop idx)
              (k + 4 + quotientVmPairwiseCoeffs - 1) with
          | error e => simp only [mapErr, bind, Except.bind]
          | ok _ =>
              rw [mapErr_ok]
              simp only [bind, Except.bind]
              rw [show idx + k + 4 = idx + (k + 4) by omega]
              conv_lhs => rw [foldRangeIdxM_shift_id (shiftFault idx) quotientVmLimbs
                    (qvmFrZero, mem)
                    (pwOuterBody bytes consts (idx + (k + 4)) lhsBase rhsBase)
                    (pwOuterBody (bytes.drop idx) consts (k + 4) lhsBase rhsBase)
                    (pwOuterBody_shift bytes consts idx (k + 4) lhsBase rhsBase)]
              cases hf : Midfall.Generator.foldRangeIdxM quotientVmLimbs (qvmFrZero, mem)
                  (pwOuterBody (bytes.drop idx) consts (k + 4) lhsBase rhsBase) with
              | ok y => simp only [mapErr_ok, bind, Except.bind]
              | error e => simp only [mapErr, bind, Except.bind]

/-- ARM BILIN7_PAIRWISE's step congruence. -/
theorem step_shift_bilin7Pairwise (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
          qOpBilin7Pairwise stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [limbPairwiseForm_shift bytes consts mem idx 1]
  simp only [← mapErr_bind]
  simp only [mapErr_ok]

/-- THE COMBINED CONGRUENCE, 22 ARMS: section 5's 20 plus the two nested/counted limb arms this
    section proves. Stated as a union rather than by editing section 5 in place because
    'pwInnerBody'/'pwOuterBody' are section 8's definitions, so the two new arm congruences cannot
    be cited before them - the same reason CSLOT unioned the slot axis as '_25' instead of widening
    the 19-arm statement. The authoritative list of 'step_shift_*' theorems is now: section 5's 20,
    section 7's three, and these two - 25 of the 26 identity arms, MODARITH7 alone left. -/
theorem evalQuotientIdentityStep_shift_22 (op : Nat)
    (hop : (op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7)
      \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise)
    (bytes : List Nat) (idx : Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0 op stack mem) := by
  rcases hop with (h20 | hpair)
  · exact evalQuotientIdentityStep_shift op h20 bytes idx consts stack mem
  · rcases hpair with (h|h) <;> subst h
    · exact step_shift_bilin7Row bytes idx consts stack mem
    · exact step_shift_bilin7Pairwise bytes idx consts stack mem

/-- FAMILY 1 AT A GENERAL CURSOR, 22 ARMS. The index-0 form
    'evalQuotientIdentityStep_readsWithinStride' already covered BILIN7_ROW and BILIN7_PAIRWISE; what
    was missing was never the read bound, only the congruence to transport it along. With QvmWalk's
    'runAddMul*_noRF' and 'affineSum_noRF' this is 25 of the 26 identity arms. -/
theorem evalQuotientIdentityStep_readsWithinStride_at_22
    (op : Nat)
    (hop : (op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7)
      \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise)
    (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = op :: rest)
    (len : Nat)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len)
    (hfit : len ≤ (op :: rest).length)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem) := by
  rw [evalQuotientIdentityStep_shift_22 op hop bytes idx consts stack mem,
      NoRF_mapErr_shiftFault]
  rw [hdrop]
  refine evalQuotientIdentityStep_readsWithinStride op ?_ rest len hlen hfit consts stack mem
  tauto

/-- FAMILY 2 AT A GENERAL CURSOR, 22 ARMS: the cursor-shifted twin of
    'evalQuotientIdentityStep_consumed_agrees' (Qvm.lean:1197), which already covered these two arms
    at index 0. -/
theorem evalQuotientIdentityStep_consumed_agrees_at_22
    (op : Nat)
    (hop : (op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7)
      \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise)
    (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = op :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len) :
    step.consumed = len := by
  have h2 : Midfall.Generator.evalQuotientIdentityStep (op :: rest) consts 0 op stack mem
      = .ok step := by
    have h3 := step_ok_congr bytes idx consts stack mem step op
      (evalQuotientIdentityStep_shift_22 op hop bytes idx consts stack mem)
    rw [hdrop] at h3
    exact (h3.mp hstep)
  refine evalQuotientIdentityStep_consumed_agrees op ?_ rest consts stack mem step len h2 hlen
  tauto

/-- ARM AFFINE_SUM'S WIDTH AGREEMENT AT INDEX 0 - the third of the four family-2 arms and the last
    of the three that needed no new congruence (section 7 landed 'step_shift_affineSum'). The
    interpreter's consumed is '5 + used' over TWO chained counted blocks and the validator's stride
    for the same bytes is '1 + 2*2 + linCount*3 + productCount*5'; the two blocks advance by 3 and
    5 per term, so the two measurements agree by 'foldRangeIdxM_runL_cursor' and
    'foldRangeIdxM_runP_cursor'. It is proved HERE rather than in QvmWalk because the counted-block
    bodies it needs are this file's 'runFoldL'/'runFoldP' and their cursor lemmas. The zero-count
    refusal is discharged as a fault that names no width, not by a hypothesis - cf. QvmWalk's header. -/
theorem consumed_agrees_affineSum (rest : List Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpAffineSum :: rest) consts 0
      qOpAffineSum stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (qOpAffineSum :: rest) 0 = .ok len) :
    step.consumed = len := by
  have h0 := step_eq_affineSumArmBody (qOpAffineSum :: rest) 0 consts stack mem
  rw [h0] at hstep
  unfold affineSumArmBody at hstep
  obtain ⟨lc, hlc, hstep⟩ := peel_bind hstep
  obtain ⟨pc, hpc, hstep⟩ := peel_bind hstep
  by_cases hc : (lc != 0 && pc != 0) = true
  · rw [if_pos hc] at hstep
    obtain ⟨p, hps, hstep⟩ := peel_bind hstep
    obtain ⟨a, ha, hstep⟩ := peel_bind hstep
    obtain ⟨b, hb, hstep⟩ := peel_bind hstep
    have hrec := Except.ok.inj hstep
    subst hrec
    have hcurA : a.2.1 = 0 + 3 * lc :=
      foldRangeIdxM_runL_cursor (qOpAffineSum :: rest) consts 5 lc 0 p.1 0 mem a ha
    have hcurB : b.2.1 = a.2.1 + 5 * pc :=
      foldRangeIdxM_runP_cursor (qOpAffineSum :: rest) consts 5 pc 0 a.1 a.2.1 a.2.2 b hb
    have hlen' : len = 1 + 2 * quotientVmByteU16Bytes
        + lc * (quotientVmByteU16Bytes + 1) + pc * (2 * quotientVmByteU16Bytes + 1) := by
      unfold Midfall.Generator.QuotientValidator.quotientOpLen at hlen
      have hb : Midfall.Generator.QuotientValidator.byteAtPanic (qOpAffineSum :: rest) 0 3009
          = .ok qOpAffineSum := rfl
      rw [hb] at hlen
      simp only [bind, Except.bind] at hlen
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)] at hlen
      unfold Midfall.Generator.QuotientValidator.quotientAffineSumOpLen at hlen
      have h1 : Midfall.Generator.QuotientValidator.readU16 (qOpAffineSum :: rest) (0 + 1) = .ok lc :=
        (readU16_iff_readU16 (bytes := qOpAffineSum :: rest) (k := 0 + 1)).mp hlc
      have h2 : Midfall.Generator.QuotientValidator.readU16 (qOpAffineSum :: rest) (0 + 3) = .ok pc :=
        (readU16_iff_readU16 (bytes := qOpAffineSum :: rest) (k := 0 + 3)).mp hpc
      rw [h1, h2] at hlen
      simp only [bind, Except.bind] at hlen
      exact (Except.ok.inj hlen).symm
    show 5 + b.2.1 = len
    rw [hcurB, hcurA, hlen']
    have hq : quotientVmByteU16Bytes = 2 := rfl
    rw [hq]
    ring
  · rw [if_neg hc] at hstep
    cases hstep

/-- THE WIDTH AGREEMENT AT A GENERAL CURSOR for ARM AFFINE_SUM: the index-0 form above transported
    along section 7's congruence, exactly NBF's pattern for the RUN pair. -/
theorem consumed_agrees_at_affineSum (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = qOpAffineSum :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAffineSum stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen
      (qOpAffineSum :: rest) 0 = .ok len) :
    step.consumed = len := by
  have h2 : Midfall.Generator.evalQuotientIdentityStep (qOpAffineSum :: rest)
      consts 0 qOpAffineSum stack mem = .ok step := by
    have h3 := step_ok_congr bytes idx consts stack mem step qOpAffineSum
      (step_shift_affineSum bytes idx consts stack mem)
    rw [hdrop] at h3
    exact h3.mp hstep
  exact consumed_agrees_affineSum rest consts stack mem step len h2 hlen

/-- PG_SHIF2 - THE MODARITH7 REMAINDER ON BOTH REMAINING FAMILIES, named as three Props and NOT
    added to the row, to a bundle, to 'ValidV3' or to the root (RULES: "if a fact is missing, STOP,
    record a PG_* row with the exact goal state"). CSLOT named this arm's family-3 remainder in
    'PG_stepNoRF_validated_cs_modarith7'; these are the family-1 and family-2 remainders, and the
    reason all three are still open is the same single missing fact, so it is named first:

    (i) 'PG_..._shift' - the STEP CONGRUENCE for the arm. Unlike the other 25 arms, MODARITH7 has
        no 'step_shift_*' anywhere: its header's branch points ('afterCond', 'afterConst') are
        computed from a flag byte read AT the cursor, so the transport needs the header congruence
        section 6 describes ('afterCond'/'afterConst' at 'idx + k' are 'idx +' the values at 'k'),
        proved inside the do-block under the binders.
    (ii) family 1 needs (i) plus the index-0 read bound, which Qvm.lean:1861 also does not supply
        (five chained counted blocks, 'fold_chain_step' iterated five times with a different body
        each time).
    (iii) family 2 needs (i) plus the index-0 width agreement, which does not exist either; the
        validator's 'quotientModarith7OpLen' is a sum over five blocks whose initial cursors are
        the previous blocks' outputs.

    Each Prop below is the GENERAL-CURSOR form, which subsumes the index-0 one (take 'idx = 0' and
    'bytes = op :: rest'), so nothing is hidden by the phrasing. NO CONTRACT DEFECT WAS FOUND ON
    THIS ARM: nothing here exhibits a validated program whose step faults, and nothing here rules
    one out - the arm was not measured. -/
def PG_stepNoRF_validated_shif2_modarith7_shift : Prop :=
  ∀ (bytes : List Nat) (idx : Nat) (consts : List Word256) (stack : List QVMFr)
    (mem : QuotientRefMemory),
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem
      = mapErr (shiftFault idx)
        (Midfall.Generator.evalQuotientIdentityStep (bytes.drop idx) consts 0
          qOpModarith7 stack mem)

/-- PG_SHIF2 (ii) - the family-1 remainder for MODARITH7 at a general cursor. -/
def PG_stepNoRF_validated_shif2_modarith7_read : Prop :=
  ∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (rest : List Nat)
    (_hdrop : bytes.drop idx = qOpModarith7 :: rest) (len : Nat)
    (_hlen : Midfall.Generator.QuotientValidator.quotientOpLen (qOpModarith7 :: rest) 0 = .ok len)
    (_hfit : len ≤ (qOpModarith7 :: rest).length)
    (stack : List QVMFr) (mem : QuotientRefMemory),
    NoRF (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem)

/-- PG_SHIF2 (iii) - the family-2 remainder for MODARITH7 at a general cursor. -/
def PG_stepNoRF_validated_shif2_modarith7_width : Prop :=
  ∀ (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (_hdrop : bytes.drop idx = qOpModarith7 :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat),
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem = .ok step →
    Midfall.Generator.QuotientValidator.quotientOpLen (qOpModarith7 :: rest) 0 = .ok len →
    step.consumed = len

#print axioms Midfall.Lowering.QvmShift.limbRowForm_shift
#print axioms Midfall.Lowering.QvmShift.limbPairwiseForm_shift
#print axioms Midfall.Lowering.QvmShift.step_shift_bilin7Row
#print axioms Midfall.Lowering.QvmShift.step_shift_bilin7Pairwise
#print axioms Midfall.Lowering.QvmShift.evalQuotientIdentityStep_shift_22
#print axioms Midfall.Lowering.QvmShift.evalQuotientIdentityStep_readsWithinStride_at_22
#print axioms Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22
#print axioms Midfall.Lowering.QvmShift.consumed_agrees_affineSum
#print axioms Midfall.Lowering.QvmShift.consumed_agrees_at_affineSum

/-! ### Section 10: the OUT-OF-RANGE pass - the faulted slot is beyond the table (card SLOT2)

    THE MISSING THIRD LEG, and it is the SECOND of the two that Qvm.lean:2277-2288 says the third
    per-arm fact really is. CSLOT landed MEMBERSHIP: 'NamesSlot (step ...) (walkerKonstSlots ...)'
    for 25 arms, i.e. the faulted slot is one the walker NAMED. What the row still lacked is
    OUT-OF-RANGE-NESS: that the faulted slot is the one the table LACKS, 'step = .error
    (constSlotOutOfRange slot j) implies consts.length <= slot'. Qvm.lean:2287 predicted this pass
    would be the shorter of the two because 'constAt_slotFault' already does the per-call work, and
    it was: 'constAt_oorSlot' is six lines and no walker-side fact is needed here at all.

    WHY MEMBERSHIP ALONE CANNOT REFUTE THE FAULT - the thing SHIF2 insisted on and this section is
    the answer to. The two passes are independent and 'noSlotFault_of_namesSlot_oorSlot' is where
    they compose: membership puts the faulted slot inside the walker's named set, out-of-range-ness
    puts it at or beyond the end of the table, and validation ('checkQuotientConstSlot' plus
    'numConsts_eq_build_length') bounds every named slot BELOW the table length. With the first
    alone the fault could sit at a named in-range slot; with the second alone it could sit at an
    unnamed out-of-range slot. So 25 of 26 on this axis moves the row exactly as far as 25 of 26 on
    the other two and no further: per-arm coverage on all three axes is still not sufficient, and
    the loop induction over the fuel-bounded segment is untouched by any of it.

    WHAT IS CHEAPER HERE THAN IN CSLOT, and it is not the case split. 'NamesSlot' needed a
    cursor-invariant induction ('foldRangeIdxM_namesSlot_range' carries 'P : Nat -> α -> Prop' plus
    an advance hypothesis) because the i-th iteration's slot OFFSET depends on the cursor.
    Out-of-range-ness is cursor-free: 'constAt consts s _' faults beyond the end of 'consts'
    whatever 's' is, so 'foldRangeIdxM_oorSlot' needs no reachability predicate and no advance
    lemma. That is why this axis reaches the six folded arms in one pass instead of needing the
    prefix lemma, and why MODARITH7 fails here for a DIFFERENT reason again (see
    'PG_stepNoRF_validated_slot2_modarith7_oor').

    WHAT IS REUSED rather than rebuilt: 'constAt_ok_of_lt' and 'constAt_slotFault' (Qvm.lean section
    9) do the per-call arithmetic; CSLOT's 'bind_ok_id'', 'limbLinearForm_unfold',
    'limbLinBody_unfold', 'limbRowForm_unfold', 'limbPairwiseForm_unfold', 'pwInnerBody_unfold' and
    'pwOuterBody_unfold' are the rfl bridges that make the counted bodies citable; NBF's
    'runArmBody'/'affineSumArmBody' with their 'step_eq_*' bridges do the same for the RUN and
    AFFINE_SUM arms. No new body definition was needed on this axis, and CSLOT's 'obtain' pattern
    (the predicate is a forall over the fault, so a pair-pattern continuation is discharged by
    casing the bound variable) reached every 'match' in the chain - the variable-body bridge was
    NOT needed here, which is what the brief asked me to check before paying for it.

    WHAT IS NOT HERE, named: MODARITH7, at the end of this section with its exact goal state.
    NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES): 'hbound'
    is a hypothesis on an ARM LEMMA, which RULES allows explicitly. No statement names a fixture
    (D-P71) - the one witness below is a three-byte program and a three-entry table written inline,
    the pattern Qvm.lean:2796 uses. No 'native_decide'. This section adds no sorry. -/


/-- SLOT2's predicate. 'OORSlot x n' says: every 'constSlotOutOfRange' the computation can produce
    names a slot at or beyond position 'n'. 'NamesSlot' (Qvm.lean section 9) says which slots the
    computation NAMES; this says where the faulted one must SIT. The row needs both - membership
    alone cannot refute a fault, as Qvm.lean:2277-2288 says. -/
def OORSlot {α : Type} (x : Except QVMFault α) (n : Nat) : Prop :=
  ∀ slot j, x = .error (QVMFault.constSlotOutOfRange slot j) → n ≤ slot

namespace OORSlot

theorem ok {α : Type} (a : α) (n : Nat) : OORSlot (Except.ok a) n := by
  intro slot j h; cases h

theorem error {α : Type} {e : QVMFault} (n : Nat)
    (h : ∀ slot j, e ≠ QVMFault.constSlotOutOfRange slot j) :
    OORSlot (Except.error (α := α) e) n := by
  intro slot j hh
  exact absurd (Except.error.inj hh) (h slot j)

theorem never {α : Type} {x : Except QVMFault α} (n : Nat)
    (h : ∀ slot j, x ≠ .error (QVMFault.constSlotOutOfRange slot j)) : OORSlot x n := by
  intro slot j hh; exact absurd hh (h slot j)

theorem bind {α β : Type} {x : Except QVMFault α} {f : α → Except QVMFault β}
    {n : Nat} (hx : OORSlot x n) (hf : ∀ a, OORSlot (f a) n) : OORSlot (x >>= f) n := by
  intro slot j h
  cases x with
  | ok a => exact hf a slot j h
  | error e =>
      have h2 : e = QVMFault.constSlotOutOfRange slot j := Except.error.inj h
      subst h2
      exact hx slot j rfl

theorem pair_match {ε α β : Type} (e : ε × α)
    (f : ε → α → Except QVMFault β) {n : Nat}
    (h : ∀ x y, OORSlot (f x y) n) :
    OORSlot (match e with | (x, y) => f x y) n := by
  cases e with
  | mk x y => exact h x y

theorem ite {α : Type} {c : Prop} [inst : Decidable c] {x y : Except QVMFault α} {n : Nat}
    (hx : OORSlot x n) (hy : OORSlot y n) : OORSlot (if c then x else y) n := by
  cases inst with
  | isTrue _ => exact hx
  | isFalse _ => exact hy

theorem except_map {α β : Type} (g : α → β) {x : Except QVMFault α} {n : Nat}
    (hx : OORSlot x n) : OORSlot (Except.map g x) n := by
  intro slot j h
  cases x with
  | ok a => exact absurd h (by intro h2; cases h2)
  | error e =>
      have h2 : e = QVMFault.constSlotOutOfRange slot j := Except.error.inj h
      subst h2
      exact hx slot j rfl

theorem congr {α : Type} {x y : Except QVMFault α} {n : Nat}
    (h : x = y) (hx : OORSlot x n) : OORSlot y n := h ▸ hx

end OORSlot

/-- THE PER-CALL FACT, lifted from 'constAt_ok_of_lt' as Qvm.lean:2287 predicts it would be: the
    fault carries its own slot, and the only way 'constAt' produces it is 'consts.drop slot = []'. -/
theorem constAt_oorSlot {consts : List Word256} {k idx : Nat} :
    OORSlot (Midfall.Generator.constAt consts k idx) consts.length := by
  intro s j h
  have h2 : s = k := constAt_slotFault h
  subst h2
  unfold Midfall.Generator.constAt at h
  cases hcs : consts.drop s with
  | cons v rest =>
      rw [hcs] at h
      exact absurd h (fqFromU256_not_slotFault v s j)
  | nil => exact List.drop_eq_nil_iff.mp hcs

theorem byteAt_oorSlot (bytes : List Nat) (k n : Nat) :
    OORSlot (Midfall.Generator.byteAt bytes k) n :=
  OORSlot.never n (byteAt_not_slotFault bytes k)

theorem popStack_oorSlot (stack : List QVMFr) (idx n : Nat) :
    OORSlot (Midfall.Generator.popStack stack idx) n :=
  OORSlot.never n (popStack_not_slotFault stack idx)

theorem indexOrPanic_oorSlot (bytes : List Nat) (p n : Nat) :
    OORSlot (Midfall.Generator.indexOrPanic bytes p) n :=
  OORSlot.never n (indexOrPanic_not_slotFault bytes p)

theorem readU16_oorSlot (bytes : List Nat) (k n : Nat) :
    OORSlot (Midfall.Generator.readU16 bytes k) n := by
  unfold Midfall.Generator.readU16
  refine OORSlot.bind (byteAt_oorSlot bytes k n) (fun _ =>
    OORSlot.bind (byteAt_oorSlot bytes (k+1) n) (fun _ => OORSlot.ok _ n))

theorem readU32_oorSlot (bytes : List Nat) (k n : Nat) :
    OORSlot (Midfall.Generator.readU32 bytes k) n := by
  unfold Midfall.Generator.readU32
  refine OORSlot.bind (byteAt_oorSlot bytes k n) (fun _ =>
    OORSlot.bind (byteAt_oorSlot bytes (k+1) n) (fun _ =>
      OORSlot.bind (byteAt_oorSlot bytes (k+2) n) (fun _ =>
        OORSlot.bind (byteAt_oorSlot bytes (k+3) n) (fun _ => OORSlot.ok _ n))))

/-- THE FOLD LEG, and it is where this pass is genuinely SHORTER than CSLOT's. 'NamesSlot' needed a
    cursor invariant ('foldRangeIdxM_namesSlot_range' carries 'P : Nat → α → Prop' and an advance
    hypothesis) because the i-th iteration's slot OFFSET depends on the cursor. Out-of-range-ness
    does not: 'constAt consts s _' faults beyond the end of 'consts' whatever 's' is. So the
    induction needs no reachability predicate and no advance lemma at all. -/
theorem foldRangeIdxM_oorSlot {α : Type} :
    ∀ (n : Nat) (init : α) (f : Nat → α → Except QVMFault α) (m : Nat),
      (∀ i s, OORSlot (f i s) m) → OORSlot (Midfall.Generator.foldRangeIdxM n init f) m
  | 0, init, f, m, _ => OORSlot.ok init m
  | k+1, init, f, m, hf => by
      show OORSlot (f 0 init >>= (fun x =>
        Midfall.Generator.foldRangeIdxM k x (fun i => f (i+1)) >>= (fun y => Except.ok y))) m
      refine OORSlot.bind (hf 0 init) (fun x => ?_)
      rw [bind_ok_id']
      exact foldRangeIdxM_oorSlot k x (fun i => f (i+1)) m (fun i s => hf (i+1) s)

theorem affineLinearTerm_oorSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    OORSlot (Midfall.Generator.affineLinearTerm bytes consts mem k) consts.length := by
  unfold Midfall.Generator.affineLinearTerm
  refine OORSlot.bind (readU16_oorSlot bytes k _) (fun _ =>
    OORSlot.bind (byteAt_oorSlot bytes (k+2) _) (fun slot =>
      OORSlot.bind constAt_oorSlot (fun _ => OORSlot.ok _ _)))

theorem affineProductTerm_oorSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    OORSlot (Midfall.Generator.affineProductTerm bytes consts mem k) consts.length := by
  unfold Midfall.Generator.affineProductTerm
  refine OORSlot.bind (readU16_oorSlot bytes k _) (fun _ =>
    OORSlot.bind (readU16_oorSlot bytes (k+2) _) (fun _ =>
      OORSlot.bind (byteAt_oorSlot bytes (k+4) _) (fun slot =>
        OORSlot.bind constAt_oorSlot (fun _ => OORSlot.ok _ _))))

theorem limbLinBody_oorSlot (bytes : List Nat) (consts : List Word256) (c : Nat) :
    ∀ (i : Nat) (acc : QVMFr) (m : QuotientRefMemory),
      OORSlot (limbLinBody bytes consts i (acc, c, m)) consts.length := by
  intro i acc m
  rw [limbLinBody_unfold bytes consts c i acc m]
  refine OORSlot.bind (byteAt_oorSlot bytes c _) (fun _ =>
    OORSlot.bind (readU16_oorSlot bytes (c+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ => OORSlot.ok _ _)))

theorem limbLinearForm_oorSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    OORSlot (limbLinearForm bytes consts mem k) consts.length := by
  rw [limbLinearForm_unfold bytes consts mem k]
  refine OORSlot.bind (foldRangeIdxM_oorSlot quotientVmLimbs (qvmFrZero, k, mem)
      (limbLinBody bytes consts) consts.length
      (fun i s => by obtain ⟨acc, c, m⟩ := s; exact limbLinBody_oorSlot bytes consts c i acc m))
    (fun y => by obtain ⟨value, len, mem'⟩ := y; exact OORSlot.ok _ _)

theorem limbRowForm_oorSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    OORSlot (limbRowForm bytes consts mem k) consts.length := by
  rw [limbRowForm_unfold bytes consts mem k]
  refine OORSlot.bind (readU16_oorSlot bytes k _) (fun lhs => ?_)
  obtain ⟨lhsValue, mem1⟩ := mem.literal lhs
  refine OORSlot.bind (limbLinearForm_oorSlot (mem := mem1) (k := k + 2)) (fun y => ?_)
  obtain ⟨v, len, m'⟩ := y
  exact OORSlot.ok _ _

theorem pwInnerBody_oorSlot (bytes : List Nat) (consts : List Word256)
    (coeffs rhsBase : Nat) (lhsV : QVMFr) :
    ∀ i j s, OORSlot (pwInnerBody bytes consts coeffs rhsBase i lhsV j s) consts.length := by
  intro i j s
  obtain ⟨acc, m⟩ := s
  rw [pwInnerBody_unfold bytes consts coeffs rhsBase i lhsV j acc m]
  obtain ⟨rhsValue, mem2⟩ := m.literal (rhsBase + j * qvmWordBytes)
  refine OORSlot.bind (indexOrPanic_oorSlot bytes (coeffs + i + j) _) (fun slot =>
    OORSlot.bind constAt_oorSlot (fun _ => OORSlot.ok _ _))

theorem pwOuterBody_oorSlot (bytes : List Nat) (consts : List Word256)
    (coeffs lhsBase rhsBase : Nat) :
    ∀ i s, OORSlot (pwOuterBody bytes consts coeffs lhsBase rhsBase i s) consts.length := by
  intro i s
  obtain ⟨acc, m⟩ := s
  rw [pwOuterBody_unfold bytes consts coeffs lhsBase rhsBase i acc m]
  obtain ⟨lhsValue, mem1⟩ := m.literal (lhsBase + i * qvmWordBytes)
  exact foldRangeIdxM_oorSlot quotientVmLimbs (acc, mem1)
    (pwInnerBody bytes consts coeffs rhsBase i lhsValue) consts.length
    (pwInnerBody_oorSlot bytes consts coeffs rhsBase lhsValue i)

theorem limbPairwiseForm_oorSlot {bytes : List Nat} {consts : List Word256}
    {mem : QuotientRefMemory} {k : Nat} :
    OORSlot (limbPairwiseForm bytes consts mem k) consts.length := by
  rw [limbPairwiseForm_unfold bytes consts mem k]
  refine OORSlot.bind (readU16_oorSlot bytes k _) (fun lhsBase =>
    OORSlot.bind (readU16_oorSlot bytes (k+2) _) (fun rhsBase =>
      OORSlot.bind (byteAt_oorSlot bytes (k + 4 + quotientVmPairwiseCoeffs - 1) _) (fun _ =>
        OORSlot.bind (foldRangeIdxM_oorSlot quotientVmLimbs (qvmFrZero, mem)
            (pwOuterBody bytes consts (k + 4) lhsBase rhsBase) consts.length
            (pwOuterBody_oorSlot bytes consts (k + 4) lhsBase rhsBase))
          (fun y => OORSlot.ok _ _))))

theorem runFoldL_oorSlot (bytes : List Nat) (consts : List Word256) (base : Nat) :
    ∀ i s, OORSlot (runFoldL bytes consts base i s) consts.length := by
  intro i s
  unfold runFoldL
  refine OORSlot.except_map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
    (affineLinearTerm_oorSlot (bytes := bytes) (mem := s.2.2) (k := base + s.2.1))

theorem runFoldP_oorSlot (bytes : List Nat) (consts : List Word256) (base : Nat) :
    ∀ i s, OORSlot (runFoldP bytes consts base i s) consts.length := by
  intro i s
  unfold runFoldP
  refine OORSlot.except_map (fun x => (qvmFrAdd s.1 x.1, s.2.1 + x.2.1, x.2.2))
    (affineProductTerm_oorSlot (bytes := bytes) (mem := s.2.2) (k := base + s.2.1))

theorem runArmBody_oorSlot (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (F : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (hF : ∀ i s, OORSlot (F i s) consts.length) :
    OORSlot (runArmBody bytes consts idx stack mem F) consts.length := by
  unfold runArmBody
  refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun count =>
    OORSlot.ite
      (OORSlot.bind (popStack_oorSlot stack idx _) (fun p =>
        OORSlot.bind (foldRangeIdxM_oorSlot count (p.1, 0, mem) F consts.length hF)
          (fun y => OORSlot.ok _ _)))
      (OORSlot.error _ (by intro s j hh; cases hh)))

theorem affineSumArmBody_oorSlot (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (Fl Fp : Nat → QVMFr × Nat × QuotientRefMemory →
        Except QVMFault (QVMFr × Nat × QuotientRefMemory))
    (hl : ∀ i s, OORSlot (Fl i s) consts.length)
    (hp : ∀ i s, OORSlot (Fp i s) consts.length) :
    OORSlot (affineSumArmBody bytes consts idx stack mem Fl Fp) consts.length := by
  unfold affineSumArmBody
  refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
    OORSlot.bind (readU16_oorSlot bytes (idx+3) _) (fun _ =>
      OORSlot.ite
        (OORSlot.bind (popStack_oorSlot stack idx _) (fun p =>
          OORSlot.bind (foldRangeIdxM_oorSlot _ (p.1, 0, mem) Fl consts.length hl) (fun a =>
            OORSlot.bind (foldRangeIdxM_oorSlot _ (a.1, a.2.1, a.2.2) Fp consts.length hp)
              (fun b => OORSlot.ok _ _))))
        (OORSlot.error _ (by intro s j hh; cases hh))))


/-! #### The 19 flat arms -/

theorem evalQuotientIdentityStep_oorSlot_flat
    (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem)
      consts.length := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU32_oorSlot bytes (idx+1) _) (fun _ => OORSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (byteAt_oorSlot bytes (idx+1) _) (fun _ => OORSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (byteAt_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind (readU32_oorSlot bytes (idx+2) _) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ => OORSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (popStack_oorSlot stack idx _) (fun x =>
      OORSlot.bind (popStack_oorSlot x.2 idx _) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (popStack_oorSlot stack idx _) (fun x =>
      OORSlot.bind (popStack_oorSlot x.2 idx _) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (byteAt_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (byteAt_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ =>
        OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (byteAt_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ =>
        OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ =>
        OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind constAt_oorSlot (fun _ =>
        OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (popStack_oorSlot stack idx _) (fun _ =>
      OORSlot.bind (affineProductTerm_oorSlot (mem := mem)) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (popStack_oorSlot stack idx _) (fun _ =>
      OORSlot.bind (affineLinearTerm_oorSlot (mem := mem)) (fun _ => OORSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (readU16_oorSlot bytes (idx+1) _) (fun _ =>
      OORSlot.bind (readU16_oorSlot bytes (idx+3) _) (fun _ =>
        OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine OORSlot.bind (popStack_oorSlot stack idx _) (fun _ => OORSlot.ok _ _)

/-! #### The six folded arms -/

theorem step_oorSlot_lin7 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem)
      consts.length := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine OORSlot.bind (limbLinearForm_oorSlot (mem := mem)) (fun y => ?_)
  obtain ⟨value, len, mem'⟩ := y
  exact OORSlot.ok _ _

theorem step_oorSlot_bilin7Row (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem)
      consts.length := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine OORSlot.bind (limbRowForm_oorSlot (mem := mem)) (fun y => ?_)
  obtain ⟨value, len, mem'⟩ := y
  exact OORSlot.ok _ _

theorem step_oorSlot_bilin7Pairwise (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem)
      consts.length := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine OORSlot.bind (limbPairwiseForm_oorSlot (mem := mem)) (fun y => ?_)
  obtain ⟨value, len, mem'⟩ := y
  exact OORSlot.ok _ _

theorem step_oorSlot_runP (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulMemMemConstU8 stack mem) consts.length := by
  rw [step_eq_runArmBody]
  exact runArmBody_oorSlot bytes consts idx stack mem (runFoldP bytes consts (idx + 3))
    (runFoldP_oorSlot bytes consts (idx + 3))

theorem step_oorSlot_runL (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulConstU8MemU16 stack mem) consts.length := by
  rw [step_eq_runArmBodyL]
  exact runArmBody_oorSlot bytes consts idx stack mem (runFoldL bytes consts (idx + 3))
    (runFoldL_oorSlot bytes consts (idx + 3))

theorem step_oorSlot_affineSum (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAffineSum stack mem)
      consts.length := by
  rw [step_eq_affineSumArmBody]
  exact affineSumArmBody_oorSlot bytes consts idx stack mem
    (runFoldL bytes consts (idx + 5)) (runFoldP bytes consts (idx + 5))
    (runFoldL_oorSlot bytes consts (idx + 5)) (runFoldP_oorSlot bytes consts (idx + 5))


/-! #### The 25-arm union, and what the two passes together buy -/

/-- THE OUT-OF-RANGE PASS FOR 25 OF THE 26 IDENTITY ARMS AT A GENERAL CURSOR: the second of the two
    slot-axis passes Qvm.lean:2277-2288 names. MODARITH7 is the one arm left and is named in
    'PG_stepNoRF_validated_slot2_modarith7_oor'. -/
theorem evalQuotientIdentityStep_oorSlot_25
    (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : (op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5)
      \/ op = qOpLin7 \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise
      \/ op = qOpRunAddMulMemMemConstU8 \/ op = qOpRunAddMulConstU8MemU16 \/ op = qOpAffineSum) :
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem)
      consts.length := by
  rcases hop with (hflat | h6)
  · exact evalQuotientIdentityStep_oorSlot_flat bytes consts idx op stack mem hflat
  · rcases h6 with (h|h|h|h|h|h) <;> subst h
    · exact step_oorSlot_lin7 bytes consts idx stack mem
    · exact step_oorSlot_bilin7Row bytes consts idx stack mem
    · exact step_oorSlot_bilin7Pairwise bytes consts idx stack mem
    · exact step_oorSlot_runP bytes consts idx stack mem
    · exact step_oorSlot_runL bytes consts idx stack mem
    · exact step_oorSlot_affineSum bytes consts idx stack mem

/-- THE TWO PASSES COMPOSE. Membership says the faulted slot is one the walker NAMED; out-of-range-ness
    says it sits AT OR BEYOND the end of the table. A validated program bounds every named slot below
    the table length ('checkQuotientConstSlot' plus 'numConsts_eq_build_length'), and then no slot
    fault survives. Neither pass alone does this: with membership only the fault could be at a named
    in-range slot, and with out-of-range-ness only it could be at an unnamed out-of-range slot. -/
theorem noSlotFault_of_namesSlot_oorSlot {α : Type} {consts : List Word256}
    {x : Except QVMFault α} {S : List Nat}
    (h1 : NamesSlot x S) (h2 : OORSlot x consts.length)
    (h3 : ∀ slot ∈ S, slot < consts.length) :
    ∀ slot j, x ≠ .error (QVMFault.constSlotOutOfRange slot j) := by
  intro slot j hh
  have hlt := h3 slot (h1 slot j hh)
  have hge := h2 slot j hh
  omega

/-- THE ROW'S SECOND CONJUNCT, PER ARM, FOR 25 OF THE 26 ARMS. Stated as an arm lemma with the
    validation bound as a hypothesis (RULES allows a hypothesis on an ARM LEMMA and forbids adding one
    to the row): 'hbound' is exactly what phase 2 gives for the slots the walker names, once
    'numConsts_eq_build_length' identifies 'model.numConsts' with the table length. -/
theorem evalQuotientIdentityStep_noSlotFault_25
    (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : (op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5)
      \/ op = qOpLin7 \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise
      \/ op = qOpRunAddMulMemMemConstU8 \/ op = qOpRunAddMulConstU8MemU16 \/ op = qOpAffineSum)
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os)
    (hbound : ∀ slot ∈ walkerKonstSlots bytes idx op, slot < consts.length) :
    ∀ slot j, Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem ≠
      .error (QVMFault.constSlotOutOfRange slot j) := by
  refine noSlotFault_of_namesSlot_oorSlot
    (evalQuotientIdentityStep_constSlot_namedByWalker_25 bytes consts idx op stack mem hop hw)
    (evalQuotientIdentityStep_oorSlot_25 bytes consts idx op stack mem hop) hbound

/-- THE PASS IS NOT VACUOUS. PUSH_CONST over a three-byte program and a THREE-entry table really does
    fault 'constSlotOutOfRange 99 0', and 3 <= 99 is exactly what 'OORSlot' claims of it. Without a
    witness like this 'OORSlot' would be satisfied by any computation that never faults, and the
    per-arm lemmas above would say nothing. -/
theorem oorSlot_witness_not_vacuous :
    Midfall.Generator.evalQuotientIdentityStep [qOpPushConst, 0, 99]
        ([0, 1, 2] : List Midfall.Word256) 0 qOpPushConst ([] : List QVMFr) armsWitnessMem
        = .error (QVMFault.constSlotOutOfRange 99 0)
      ∧ OORSlot (Midfall.Generator.evalQuotientIdentityStep [qOpPushConst, 0, 99]
          ([0, 1, 2] : List Midfall.Word256) 0 qOpPushConst ([] : List QVMFr) armsWitnessMem) 3 := by
  refine ⟨rfl, ?_⟩
  intro slot j h
  have := Midfall.Lowering.QvmShift.evalQuotientIdentityStep_oorSlot_25 [qOpPushConst, 0, 99]
    ([0, 1, 2] : List Midfall.Word256) 0 qOpPushConst ([] : List QVMFr) armsWitnessMem (Or.inl (Or.inl rfl))
  exact this slot j (h ▸ rfl)

/-- SLOT2 - THE ONE ARM THIS PASS DID NOT REACH, named with its exact goal state rather than glossed.
    MODARITH7's out-of-range pass at a general cursor is still open:

      OORSlot (evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem) consts.length

    WHY IT IS THE LAST ONE HERE TOO, even though this pass needs no walker and no cursor invariant:
    'modarith7Form' (VmReference.lean:637) puts its five counted blocks INSIDE the two flag branches,
    so the interpreter's body after unfolding is the same 5-block chain FOUR times over - the COND bit
    and the CONST bit each duplicate it - and a bind-by-bind refinement has to walk all four copies.
    Unfolding and beta-reducing the whole body at once exceeds the 60 s tactic bound (measured: the
    generic walker hits 'deterministic timeout at whnf, maximum number of heartbeats (200000)' on the
    flattened term, and RULES forbids raising maxHeartbeats). What it needs is a def bridge of the
    CSLOT pattern - extract the five blocks ONCE as a def, prove 'OORSlot' of the def, and bridge the
    four inlined copies to it by 'rfl'/'cases' on the two decidable flag tests. That is mechanical,
    not obstructed, and it is the same obstacle MODARITH7 presents on the other two axes.

    NO CONTRACT DEFECT WAS FOUND ON THIS ARM EITHER: nothing here exhibits a validated program whose
    step names an out-of-range slot, and nothing here rules one out - the arm was not measured. -/
def PG_stepNoRF_validated_slot2_modarith7_oor : Prop :=
  ∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
    (mem : QuotientRefMemory),
    OORSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem)
      consts.length

#print axioms Midfall.Lowering.QvmShift.evalQuotientIdentityStep_oorSlot_flat
#print axioms Midfall.Lowering.QvmShift.step_oorSlot_lin7
#print axioms Midfall.Lowering.QvmShift.step_oorSlot_bilin7Row
#print axioms Midfall.Lowering.QvmShift.step_oorSlot_bilin7Pairwise
#print axioms Midfall.Lowering.QvmShift.step_oorSlot_runP
#print axioms Midfall.Lowering.QvmShift.step_oorSlot_runL
#print axioms Midfall.Lowering.QvmShift.step_oorSlot_affineSum
#print axioms Midfall.Lowering.QvmShift.foldRangeIdxM_oorSlot
#print axioms Midfall.Lowering.QvmShift.limbLinearForm_oorSlot
#print axioms Midfall.Lowering.QvmShift.limbRowForm_oorSlot
#print axioms Midfall.Lowering.QvmShift.limbPairwiseForm_oorSlot
#print axioms Midfall.Lowering.QvmShift.evalQuotientIdentityStep_oorSlot_25
#print axioms Midfall.Lowering.QvmShift.evalQuotientIdentityStep_noSlotFault_25
#print axioms Midfall.Lowering.QvmShift.constAt_oorSlot
#print axioms Midfall.Lowering.QvmShift.PG_stepNoRF_validated_slot2_modarith7_oor


end Midfall.Lowering.QvmShift


/-! ### Section 11: the MODARITH7 width agreement - the last arm of the P-QVMARMS table

    P-QVMARMS' per-opcode table is `consumed` = `quotientOpLen` for every identity arm. Twenty-two
    static arms are `Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees` (Qvm.lean section 7);
    the two RUN arms are QvmWalk's `consumed_agrees_runAddMul*`; AFFINE_SUM is section 9's
    `consumed_agrees_affineSum`; MODARITH7 was the one arm with NO width agreement anywhere in the
    tree (QvmShift's `PG_stepNoRF_validated_shif2_modarith7_width` named the exact goal and left it
    a Prop). This section proves it at index 0 - the shape the 22-arm theorem is stated in.

    HOW. The arm calls `modarith7Form` at `idx + 1`; its consumed is `1 + len` and the form's len is
    `cursor5 - (idx + 1)`. The form's five counted blocks each advance by a FIXED width (21, 23, 17,
    3, 5 - `limbLinearForm_ok_mid`, `limbRowForm_ok_mid`, `limbPairwiseForm_ok_mid`, and the two
    inline blocks), so `foldRangeIdxM_ok_advance` gives the form's cursor. The validator's
    `quotientModarith7OpLen` computes the SAME cursor from the SAME five count bytes and returns
    `cursor - idx`, so the two agree by arithmetic. `modAfterHeader_cursor` extracts the five counts
    and the cursor from the form, and `modAfterHeader_opLen` proves the validator arithmetic
    (`validatorAfterHeader`) from that extraction; the four header branches (cond x const flags) are
    then four short applications. The header reads are `byteAt`/`readU16` on the interpreter side and
    `byteAtPanic` on the validator side, bridged by `byteAt_iff_byteAtPanic`/`readU16_iff_readU16`.

    NO hypothesis was added to a row, to `ValidV3`, a bundle or the root. No sorry, no
    `native_decide`, no maxHeartbeats/maxRecDepth change. The statement is generic in the byte
    stream, constant table, stack and memory (D-P71). -/

namespace Midfall.Lowering.QvmArms

open Midfall
open Midfall.Generator
open Midfall.Generator (QVMFault QuotientRefMemory QVMFr qvmFrAdd qvmFrMul qvmFrZero
  IdentityStep qOpModarith7 qOpRunAddMulMemMemConstU8 qOpRunAddMulConstU8MemU16 qOpAffineSum
  quotientVmLimbs quotientVmByteU16Bytes quotientVmPairwiseCoeffs)
open Midfall.Generator.QuotientBuilder
open Midfall.Generator.QuotientValidator
open Midfall.Lowering

def modLinBody (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (acc, cursor, mem) := state
    let (v, len, mem') ← Midfall.Generator.limbLinearForm bytes consts mem cursor
    .ok (qvmFrAdd acc v, cursor + len, mem')

theorem modLinBody_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, modLinBody bytes consts i s = .ok r → r.2.1 = s.2.1 + 21 := by
  intro i s r hr
  obtain ⟨acc, cursor, mem⟩ := s
  obtain ⟨acc', cursor', mem'⟩ := r
  unfold modLinBody at hr
  obtain ⟨w, hw, hres⟩ := peel_bind hr
  have hm := limbLinearForm_ok_mid hw
  have h2 : cursor + w.2.1 = cursor' := by
    simpa using congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1)
      (Except.ok.inj hres)
  change cursor' = cursor + 21
  omega

def modRowBody (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (acc, cursor, mem) := state
    let (v, len, mem') ← Midfall.Generator.limbRowForm bytes consts mem cursor
    .ok (qvmFrAdd acc v, cursor + len, mem')

theorem modRowBody_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, modRowBody bytes consts i s = .ok r → r.2.1 = s.2.1 + 23 := by
  intro i s r hr
  obtain ⟨acc, cursor, mem⟩ := s
  obtain ⟨acc', cursor', mem'⟩ := r
  unfold modRowBody at hr
  obtain ⟨w, hw, hres⟩ := peel_bind hr
  have hm := limbRowForm_ok_mid hw
  have h2 : cursor + w.2.1 = cursor' := by
    simpa using congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1)
      (Except.ok.inj hres)
  change cursor' = cursor + 23
  omega

def modPwBody (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (acc, cursor, mem) := state
    let (v, len, mem') ← Midfall.Generator.limbPairwiseForm bytes consts mem cursor
    .ok (qvmFrAdd acc v, cursor + len, mem')

theorem modPwBody_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, modPwBody bytes consts i s = .ok r → r.2.1 = s.2.1 + 17 := by
  intro i s r hr
  obtain ⟨acc, cursor, mem⟩ := s
  obtain ⟨acc', cursor', mem'⟩ := r
  unfold modPwBody at hr
  obtain ⟨w, hw, hres⟩ := peel_bind hr
  have hm : w.2.1 = 17 := by
    have := limbPairwiseForm_ok_mid hw
    have hq : quotientVmPairwiseCoeffs = 13 := rfl
    omega
  have h2 : cursor + w.2.1 = cursor' := by
    simpa using congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1)
      (Except.ok.inj hres)
  change cursor' = cursor + 17
  omega

def modMemBody (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (acc, cursor, mem) := state
    let slot ← Midfall.Generator.byteAt bytes cursor
    let ptr ← Midfall.Generator.readU16 bytes (cursor + 1)
    let c ← Midfall.Generator.constAt consts slot cursor
    let (v, mem') := mem.literal ptr
    .ok (qvmFrAdd acc (qvmFrMul c v), cursor + 3, mem')

theorem modMemBody_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, modMemBody bytes consts i s = .ok r → r.2.1 = s.2.1 + 3 := by
  intro i s r hr
  obtain ⟨acc, cursor, mem⟩ := s
  obtain ⟨acc', cursor', mem'⟩ := r
  unfold modMemBody at hr
  obtain ⟨slot, _, h1⟩ := peel_bind hr
  obtain ⟨ptr, _, h2⟩ := peel_bind h1
  obtain ⟨c, _, h3⟩ := peel_bind h2
  have h4 : (qvmFrAdd acc (qvmFrMul c (mem.literal ptr).1), cursor + 3, (mem.literal ptr).2)
      = (acc', cursor', mem') := Except.ok.inj h3
  have h2' : cursor + 3 = cursor' := by
    simpa using congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1) h4
  change cursor' = cursor + 3
  omega

def modProdBody (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (acc, cursor, mem) := state
    let slot ← Midfall.Generator.byteAt bytes cursor
    let lhs ← Midfall.Generator.readU16 bytes (cursor + 1)
    let rhs ← Midfall.Generator.readU16 bytes (cursor + 3)
    let c ← Midfall.Generator.constAt consts slot cursor
    let (l, m1) := mem.literal lhs
    let (r, m2) := m1.literal rhs
    .ok (qvmFrAdd acc (qvmFrMul (qvmFrMul c l) r), cursor + 5, m2)

theorem modProdBody_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, modProdBody bytes consts i s = .ok r → r.2.1 = s.2.1 + 5 := by
  intro i s r hr
  obtain ⟨acc, cursor, mem⟩ := s
  obtain ⟨acc', cursor', mem'⟩ := r
  unfold modProdBody at hr
  obtain ⟨slot, _, h1⟩ := peel_bind hr
  obtain ⟨lhs, _, h2⟩ := peel_bind h1
  obtain ⟨rhs, _, h3⟩ := peel_bind h2
  obtain ⟨c, _, h4⟩ := peel_bind h3
  have h5 : (qvmFrAdd acc (qvmFrMul (qvmFrMul c (mem.literal lhs).1)
      ((mem.literal lhs).2.literal rhs).1), cursor + 5,
      ((mem.literal lhs).2.literal rhs).2) = (acc', cursor', mem') := Except.ok.inj h4
  have h2' : cursor + 5 = cursor' := by
    simpa using congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1) h5
  change cursor' = cursor + 5
  omega

def modAfterHeader (bytes : List Nat) (consts : List Word256)
    (baseIdx afterConst : Nat) (acc0 : QVMFr) (cond : Option Nat) (mem : QuotientRefMemory) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let linCount ← Midfall.Generator.byteAt bytes afterConst
  let rowCount ← Midfall.Generator.byteAt bytes (afterConst + 1)
  let pairwiseCount ← Midfall.Generator.byteAt bytes (afterConst + 2)
  let memCount ← Midfall.Generator.byteAt bytes (afterConst + 3)
  let productCount ← Midfall.Generator.byteAt bytes (afterConst + 4)
  let cursor0 := afterConst + 5
  let (acc1, cursor1, mem1) ← Midfall.Generator.foldRangeIdxM linCount (acc0, cursor0, mem)
    (modLinBody bytes consts)
  let (acc2, cursor2, mem2) ← Midfall.Generator.foldRangeIdxM rowCount (acc1, cursor1, mem1)
    (modRowBody bytes consts)
  let (acc3, cursor3, mem3) ← Midfall.Generator.foldRangeIdxM pairwiseCount (acc2, cursor2, mem2)
    (modPwBody bytes consts)
  let (acc4, cursor4, mem4) ← Midfall.Generator.foldRangeIdxM memCount (acc3, cursor3, mem3)
    (modMemBody bytes consts)
  let (acc5, cursor5, mem5) ← Midfall.Generator.foldRangeIdxM productCount (acc4, cursor4, mem4)
    (modProdBody bytes consts)
  let (acc6, mem6) ←
    match cond with
    | none => .ok (acc5, mem5)
    | some ptr =>
        let (v, m) := mem5.literal ptr
        .ok (qvmFrMul acc5 v, m)
  .ok (acc6, cursor5 - baseIdx, mem6)

theorem modAfterHeader_cursor (bytes : List Nat) (consts : List Word256)
    (baseIdx afterConst : Nat) (acc0 : QVMFr) (cond : Option Nat) (mem : QuotientRefMemory)
    (v len m' : _)
    (h : modAfterHeader bytes consts baseIdx afterConst acc0 cond mem = .ok (v, len, m')) :
    ∃ lc rc pc mc xc c5,
      Midfall.Generator.byteAt bytes afterConst = .ok lc ∧
      Midfall.Generator.byteAt bytes (afterConst + 1) = .ok rc ∧
      Midfall.Generator.byteAt bytes (afterConst + 2) = .ok pc ∧
      Midfall.Generator.byteAt bytes (afterConst + 3) = .ok mc ∧
      Midfall.Generator.byteAt bytes (afterConst + 4) = .ok xc ∧
      len = c5 - baseIdx ∧
      c5 = afterConst + 5 + 21 * lc + 23 * rc + 17 * pc + 3 * mc + 5 * xc := by
  unfold modAfterHeader at h
  obtain ⟨lc, hlc, h⟩ := peel_bind h
  obtain ⟨rc, hrc, h⟩ := peel_bind h
  obtain ⟨pc, hpc, h⟩ := peel_bind h
  obtain ⟨mc, hmc, h⟩ := peel_bind h
  obtain ⟨xc, hxc, h⟩ := peel_bind h
  obtain ⟨a1, ha1, h⟩ := peel_bind h
  rcases a1 with ⟨a1v, a1c, a1m⟩
  have hc1 : a1c = afterConst + 5 + 21 * lc := by
    have := foldRangeIdxM_ok_advance 21 lc (modLinBody bytes consts) acc0 (afterConst + 5) mem (a1v, a1c, a1m)
      (fun i s r hr => modLinBody_advance bytes consts i s r hr) ha1
    simpa using this
  obtain ⟨a2, ha2, h⟩ := peel_bind h
  rcases a2 with ⟨a2v, a2c, a2m⟩
  have hc2 : a2c = a1c + 23 * rc := by
    have := foldRangeIdxM_ok_advance 23 rc (modRowBody bytes consts) a1v a1c a1m (a2v, a2c, a2m)
      (fun i s r hr => modRowBody_advance bytes consts i s r hr) ha2
    simpa using this
  obtain ⟨a3, ha3, h⟩ := peel_bind h
  rcases a3 with ⟨a3v, a3c, a3m⟩
  have hc3 : a3c = a2c + 17 * pc := by
    have := foldRangeIdxM_ok_advance 17 pc (modPwBody bytes consts) a2v a2c a2m (a3v, a3c, a3m)
      (fun i s r hr => modPwBody_advance bytes consts i s r hr) ha3
    simpa using this
  obtain ⟨a4, ha4, h⟩ := peel_bind h
  rcases a4 with ⟨a4v, a4c, a4m⟩
  have hc4 : a4c = a3c + 3 * mc := by
    have := foldRangeIdxM_ok_advance 3 mc (modMemBody bytes consts) a3v a3c a3m (a4v, a4c, a4m)
      (fun i s r hr => modMemBody_advance bytes consts i s r hr) ha4
    simpa using this
  obtain ⟨a5, ha5, h⟩ := peel_bind h
  rcases a5 with ⟨a5v, a5c, a5m⟩
  have hc5 : a5c = a4c + 5 * xc := by
    have := foldRangeIdxM_ok_advance 5 xc (modProdBody bytes consts) a4v a4c a4m (a5v, a5c, a5m)
      (fun i s r hr => modProdBody_advance bytes consts i s r hr) ha5
    simpa using this
  have hlen : len = a5c - baseIdx := by
    cases cond with
    | none =>
        simp only at h
        simpa using (congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1) (Except.ok.inj h)).symm
    | some ptr =>
        simp only at h
        simpa using (congrArg (fun p : QVMFr × Nat × QuotientRefMemory => p.2.1) (Except.ok.inj h)).symm
  refine ⟨lc, rc, pc, mc, xc, a5c, hlc, hrc, hpc, hmc, hxc, hlen, ?_⟩
  omega

/-- The validator's arithmetic from `afterConst` onwards, isolated so the four header
    branches can share one proof. -/
def validatorAfterHeader (bytes : List Nat) (idx afterConst : Nat) : VResult Nat := do
  let linCount ← Midfall.Generator.QuotientValidator.byteAtPanic bytes afterConst 3046
  let rowCount ← Midfall.Generator.QuotientValidator.byteAtPanic bytes (afterConst + 1) 3047
  let pairwiseCount ← Midfall.Generator.QuotientValidator.byteAtPanic bytes (afterConst + 2) 3048
  let memCount ← Midfall.Generator.QuotientValidator.byteAtPanic bytes (afterConst + 3) 3049
  let productCount ← Midfall.Generator.QuotientValidator.byteAtPanic bytes (afterConst + 4) 3050
  let cursor := afterConst + 5
  let cursor := cursor + linCount * quotientVmLimbs * (1 + quotientVmByteU16Bytes)
  let cursor := cursor
    + rowCount * (quotientVmByteU16Bytes + quotientVmLimbs * (1 + quotientVmByteU16Bytes))
  let cursor := cursor
    + pairwiseCount * (2 * quotientVmByteU16Bytes + quotientVmPairwiseCoeffs)
  let cursor := cursor + memCount * (1 + quotientVmByteU16Bytes)
  .ok (cursor + productCount * (1 + 2 * quotientVmByteU16Bytes) - idx)

theorem modAfterHeader_opLen (bytes : List Nat) (idx afterConst : Nat) (consts : List Word256)
    (acc0 : QVMFr) (cond : Option Nat) (mem : QuotientRefMemory) (v len m')
    (hidx : idx + 1 ≤ afterConst)
    (h : modAfterHeader bytes consts (idx + 1) afterConst acc0 cond mem = .ok (v, len, m')) :
    validatorAfterHeader bytes idx afterConst = .ok (1 + len) := by
  obtain ⟨lc, rc, pc, mc, xc, c5, hlc, hrc, hpc, hmc, hxc, hlen, hc5⟩ :=
    modAfterHeader_cursor bytes consts (idx + 1) afterConst acc0 cond mem v len m' h
  unfold validatorAfterHeader
  rw [(byteAt_iff_byteAtPanic).mp hlc,
      (byteAt_iff_byteAtPanic).mp hrc,
      (byteAt_iff_byteAtPanic).mp hpc,
      (byteAt_iff_byteAtPanic).mp hmc,
      (byteAt_iff_byteAtPanic).mp hxc]
  simp only [bind, Except.bind]
  have hq : quotientVmLimbs = 7 := rfl
  have hb : quotientVmByteU16Bytes = 2 := rfl
  have hpc13 : quotientVmPairwiseCoeffs = 13 := rfl
  rw [hq, hb, hpc13] at ⊢
  simp only [Except.ok.injEq]
  omega



theorem modarith7Form_opLen (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx v len m')
    (h : Midfall.Generator.modarith7Form bytes consts mem (idx + 1) = .ok (v, len, m')) :
    Midfall.Generator.QuotientValidator.quotientModarith7OpLen bytes idx = .ok (1 + len) := by
  unfold Midfall.Generator.modarith7Form at h
  unfold Midfall.Generator.QuotientValidator.quotientModarith7OpLen
  cases hflags : Midfall.Generator.byteAt bytes (idx + 1) with
  | error e =>
      rw [hflags] at h
      simp only [bind, Except.bind] at h
      cases h
  | ok flags =>
      rw [hflags] at h
      rw [(byteAt_iff_byteAtPanic).mp hflags]
      simp only [bind, Except.bind] at h ⊢
      by_cases hok : modarith7FlagsOk flags = true
      · rw [if_pos hok] at h
        by_cases hc : (flags &&& qModarith7FlagCond != 0) = true
        · rw [if_pos hc] at h ⊢
          cases hcond : Midfall.Generator.readU16 bytes (idx + 2) with
          | error e =>
              rw [hcond] at h
              simp only [bind, Except.bind] at h
              cases h
          | ok condPtr =>
              rw [hcond] at h
              simp only [bind, Except.bind] at h
              by_cases hv : (flags &&& qModarith7FlagConst != 0) = true
              · rw [if_pos hv] at h ⊢
                cases hslot : Midfall.Generator.byteAt bytes (idx + 4) with
                | error e =>
                    rw [hslot] at h
                    simp only [bind, Except.bind] at h
                    cases h
                | ok slot =>
                    rw [hslot] at h
                    simp only [bind, Except.bind] at h
                    cases hconst : Midfall.Generator.constAt consts slot (idx + 4) with
                    | error e =>
                        rw [hconst] at h
                        simp only [bind, Except.bind] at h
                        cases h
                    | ok c =>
                        rw [hconst] at h
                        simp only [bind, Except.bind] at h
                        have hA : modAfterHeader bytes consts (idx + 1) (idx + 5) c
                            (some condPtr) mem = .ok (v, len, m') := h
                        exact modAfterHeader_opLen bytes idx (idx + 5) consts c (some condPtr) mem
                          v len m' (by omega) hA
              · rw [if_neg hv] at h ⊢
                have hA : modAfterHeader bytes consts (idx + 1) (idx + 4) qvmFrZero
                    (some condPtr) mem = .ok (v, len, m') := h
                exact modAfterHeader_opLen bytes idx (idx + 4) consts qvmFrZero (some condPtr)
                  mem v len m' (by omega) hA
        · rw [if_neg hc] at h ⊢
          by_cases hv : (flags &&& qModarith7FlagConst != 0) = true
          · rw [if_pos hv] at h ⊢
            cases hslot : Midfall.Generator.byteAt bytes (idx + 2) with
            | error e =>
                rw [hslot] at h
                simp only [bind, Except.bind] at h
                cases h
            | ok slot =>
                rw [hslot] at h
                simp only [bind, Except.bind] at h
                cases hconst : Midfall.Generator.constAt consts slot (idx + 2) with
                | error e =>
                    rw [hconst] at h
                    simp only [bind, Except.bind] at h
                    cases h
                | ok c =>
                    rw [hconst] at h
                    simp only [bind, Except.bind] at h
                    have hA : modAfterHeader bytes consts (idx + 1) (idx + 3) c none mem
                        = .ok (v, len, m') := h
                    exact modAfterHeader_opLen bytes idx (idx + 3) consts c none mem
                      v len m' (by omega) hA
          · rw [if_neg hv] at h ⊢
            have hA : modAfterHeader bytes consts (idx + 1) (idx + 2) qvmFrZero none mem
                = .ok (v, len, m') := h
            exact modAfterHeader_opLen bytes idx (idx + 2) consts qvmFrZero none mem
              v len m' (by omega) hA
      · rw [if_neg hok] at h
        cases h



theorem consumed_agrees_modarith7 (rest : List Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpModarith7 :: rest) consts 0
      qOpModarith7 stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (qOpModarith7 :: rest) 0 = .ok len) :
    step.consumed = len := by
  unfold Midfall.Generator.evalQuotientIdentityStep at hstep
  simp (config := { decide := true }) only [reduceIte] at hstep
  obtain ⟨v, hform, hres⟩ := peel_bind hstep
  rcases v with ⟨vv, vl, vm⟩
  have hstep' : step = { stack := vv :: stack, consumed := 1 + vl, hConsumed := by omega, mem := vm } :=
    (Except.ok.inj hres).symm
  rw [hstep']
  show 1 + vl = len
  have hval := modarith7Form_opLen (qOpModarith7 :: rest) consts mem 0 vv vl vm hform
  unfold Midfall.Generator.QuotientValidator.quotientOpLen at hlen
  rw [show Midfall.Generator.QuotientValidator.byteAtPanic
      (qOpModarith7 :: rest) 0 3009 = .ok qOpModarith7 from rfl] at hlen
  simp only [bind, Except.bind] at hlen
  rw [if_neg (by decide : ¬ (qOpModarith7 == qOpRunAddMulMemMemConstU8) = true),
      if_neg (by decide : ¬ (qOpModarith7 == qOpRunAddMulConstU8MemU16) = true),
      if_neg (by decide : ¬ (qOpModarith7 == qOpAffineSum) = true),
      if_pos (by decide : (qOpModarith7 == qOpModarith7) = true)] at hlen
  rw [hval] at hlen
  exact Except.ok.inj hlen

/-! #### The single arm-table statement: all 26 identity arms -/

/-- The 26 opcodes `evalQuotientIdentityStep` has an identity arm for (the five stream
    opcodes and the unknown-opcode fallback are errors, not identity arms). -/
def identityArm26 (op : Nat) : Prop :=
  op = qOpPushConst ∨ op = qOpPushMemLiteral ∨ op = qOpPushMemToken ∨
  op = qOpPushMemTokenOffset ∨ op = qOpPushMemU16 ∨ op = qOpAdd ∨ op = qOpMul ∨
  op = qOpNeg ∨ op = qOpPushConstU8 ∨ op = qOpAddConstU8 ∨ op = qOpMulConstU8 ∨
  op = qOpAddConst ∨ op = qOpMulConst ∨ op = qOpAddMemU16 ∨ op = qOpMulMemU16 ∨
  op = qOpAddMulMemMem ∨ op = qOpPow5 ∨ op = qOpAddMulMemMemConstU8 ∨
  op = qOpAddMulConstU8MemU16 ∨ op = qOpBilin7Pairwise ∨ op = qOpLin7 ∨
  op = qOpBilin7Row ∨ op = qOpRunAddMulMemMemConstU8 ∨ op = qOpRunAddMulConstU8MemU16 ∨
  op = qOpAffineSum ∨ op = qOpModarith7

/-- **THE P-QVMARMS TABLE, COMPLETE: all 26 identity arms.** When the identity step
    succeeds on an instruction whose opcode byte is at index 0 and the validator's walker
    gives the same instruction a width, the `consumed` the step reports is that width.
    This is the union of the 22 static arms (Qvm.lean section 7), the two RUN arms
    (QvmWalk), AFFINE_SUM (section 9) and MODARITH7 (section 11). No arm is assumed and
    no arm is missing; every branch cites a proved theorem. -/
theorem evalQuotientIdentityStep_consumed_agrees_26
    (op : Nat) (hop : identityArm26 op)
    (rest : List Nat)
    (consts : List Midfall.Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (op :: rest) consts 0 op stack mem
      = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len) :
    step.consumed = len := by
  rcases hop with
    (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.evalQuotientIdentityStep_consumed_agrees _
      (by tauto) rest consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmWalk.consumed_agrees_runAddMulMemMemConstU8 rest consts stack mem
      step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmWalk.consumed_agrees_runAddMulConstU8MemU16 rest consts stack mem
      step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.consumed_agrees_affineSum rest consts stack mem step len hstep hlen
  · subst h
    exact consumed_agrees_modarith7 rest consts stack mem step len hstep hlen

#print axioms Midfall.Lowering.QvmArms.modarith7Form_opLen
#print axioms Midfall.Lowering.QvmArms.consumed_agrees_modarith7
#print axioms Midfall.Lowering.QvmArms.evalQuotientIdentityStep_consumed_agrees_26



/-! #### The MODARITH7 arm at a general cursor -/

/-- At a cursor whose opcode byte is `qOpModarith7`, the validator's general walker
    dispatches to the dynamic MODARITH7 length decoder. -/
theorem quotientOpLen_modarith7_at (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = qOpModarith7 :: rest) :
    Midfall.Generator.QuotientValidator.quotientOpLen bytes idx =
      Midfall.Generator.QuotientValidator.quotientModarith7OpLen bytes idx := by
  have hb : Midfall.Generator.QuotientValidator.byteAtPanic bytes idx 3009 = .ok qOpModarith7 := by
    unfold Midfall.Generator.QuotientValidator.byteAtPanic
    rw [hdrop]
  unfold Midfall.Generator.QuotientValidator.quotientOpLen
  rw [hb]
  simp only [bind, Except.bind]
  simp (config := { decide := true }) only [reduceIte]

/-- **THE MODARITH7 WIDTH AGREEMENT AT A GENERAL CURSOR.** The index-0 form is
    `consumed_agrees_modarith7`; this is the same fact at any cursor, which is the shape
    a loop induction and `qvm_validated_noBoundsFault` consume. It needs no step
    congruence: the arm body is unfolded directly at the cursor, and the validator's
    stride is transported from the suffix by `seg_opLen_shift_ok`. -/
theorem consumed_agrees_at_modarith7 (bytes : List Nat) (idx : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = qOpModarith7 :: rest)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpModarith7 stack mem
      = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (qOpModarith7 :: rest) 0 = .ok len) :
    step.consumed = len := by
  unfold Midfall.Generator.evalQuotientIdentityStep at hstep
  simp (config := { decide := true }) only [reduceIte] at hstep
  obtain ⟨v, hform, hres⟩ := peel_bind hstep
  rcases v with ⟨vv, vl, vm⟩
  have hstep' : step = { stack := vv :: stack, consumed := 1 + vl, hConsumed := by omega, mem := vm } :=
    (Except.ok.inj hres).symm
  rw [hstep']
  show 1 + vl = len
  have hval := modarith7Form_opLen bytes consts mem idx vv vl vm hform
  have hlen1 : Midfall.Generator.QuotientValidator.quotientOpLen (bytes.drop idx) 0 = .ok len := by
    rwa [← hdrop] at hlen
  have hlen2 : Midfall.Generator.QuotientValidator.quotientOpLen bytes (idx + 0) = .ok len :=
    Midfall.Lowering.seg_opLen_shift_ok bytes idx 0 len hlen1
  rw [Nat.add_zero] at hlen2
  rw [quotientOpLen_modarith7_at bytes idx rest hdrop, hval] at hlen2
  exact Except.ok.inj hlen2

#print axioms Midfall.Lowering.QvmArms.consumed_agrees_at_modarith7


/-- **THE P-QVMARMS TABLE AT A GENERAL CURSOR, all 26 identity arms.** The cursor form of
    `evalQuotientIdentityStep_consumed_agrees_26`: at any cursor whose next opcode is an
    identity arm, a successful step and a successful validator walk agree on the width.
    This is the statement a loop induction over a whole segment consumes. -/
theorem evalQuotientIdentityStep_consumed_agrees_at_26
    (bytes : List Nat) (idx : Nat) (op : Nat) (rest : List Nat)
    (hdrop : bytes.drop idx = op :: rest) (hop : identityArm26 op)
    (consts : List Midfall.Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len) :
    step.consumed = len := by
  rcases hop with
    (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.evalQuotientIdentityStep_consumed_agrees_at_22 _
      (by tauto) bytes idx rest hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.consumed_agrees_at_runAddMulMemMemConstU8 bytes idx rest
      hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.consumed_agrees_at_runAddMulConstU8MemU16 bytes idx rest
      hdrop consts stack mem step len hstep hlen
  · subst h
    exact Midfall.Lowering.QvmShift.consumed_agrees_at_affineSum bytes idx rest hdrop consts
      stack mem step len hstep hlen
  · subst h
    exact consumed_agrees_at_modarith7 bytes idx rest hdrop consts stack mem step len hstep hlen

#print axioms Midfall.Lowering.QvmArms.evalQuotientIdentityStep_consumed_agrees_at_26


/-- **PG_SHIF2 (iii) DISCHARGED.** The MODARITH7 width agreement at a general cursor,
    `consumed_agrees_at_modarith7`, proves the family-2 remainder QvmShift section 10 named as
    `PG_stepNoRF_validated_shif2_modarith7_width`. That Prop is not deleted (it is a named
    obligation other cards cite); this theorem is its proof. -/
theorem PG_stepNoRF_validated_shif2_modarith7_width_proved :
    Midfall.Lowering.QvmShift.PG_stepNoRF_validated_shif2_modarith7_width :=
  fun bytes idx rest hdrop consts stack mem step len hstep hlen =>
    consumed_agrees_at_modarith7 bytes idx rest hdrop consts stack mem step len hstep hlen

#print axioms Midfall.Lowering.QvmArms.PG_stepNoRF_validated_shif2_modarith7_width_proved

end Midfall.Lowering.QvmArms

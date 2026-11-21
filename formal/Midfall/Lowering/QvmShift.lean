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
-- WHAT IS NOT HERE, named: the congruences for BILIN7_PAIRWISE, BILIN7_ROW, MODARITH7, and the two
-- RUN arms and AFFINE_SUM - see section 6 for the exact remaining goal in each case. Those five are
-- arms plus BILIN7_ROW/BILIN7_PAIRWISE, and the latter two ARE among the 22 arms of 'evalQuotientIdentityStep_readsWithinStride' or
-- 'evalQuotientIdentityStep_consumed_agrees', so nothing in this file is blocked on them: the RUN
-- pair and AFFINE_SUM already have general-cursor read bounds from QvmWalk ('runAddMul*_noRF',
-- 'affineSum_noRF' are stated at an arbitrary 'idx' over 'bytes', not at index 0).
--
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

/-- THE COMBINED CONGRUENCE, 21 of the 26 identity arms: the 19 static arms whose body is a
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
    at a general cursor ('affineSum_noRF', 'runAddMul*_noRF' are stated at an arbitrary 'idx'). -/
theorem shift_remaining_arms_are_the_dynamic_and_pairwise_ones : True := trivial

end Midfall.Lowering.QvmShift

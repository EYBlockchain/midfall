-- |
-- Midfall.Lowering.QvmEmit
--
-- QIDENT (card qvm_compile_correct_identity). This file attacks need (3) of the three things
-- QFOLD named: BUILDER-EMITTED BYTES DENOTE THE SHAPE.
--
-- WHY HERE. 'denoteLin', 'denoteLimbShape' and 'denoteModarith7' (Qvm.lean:460-504) are the
-- shape-level denotations 'RecognizersSound' quantifies over, and 'limbLinearForm',
-- 'limbRowForm', 'limbPairwiseForm' and 'modarith7Form' (VmReference.lean:577-698) are the byte
-- decoders the interpreter actually runs. The two have never been tied by a THEOREM: the only
-- tie in the tree is the Bool fixture 'denoteLimbShape_matchesByteDecoder_ok' (Qvm.lean:4060),
-- which measures three hand-written shapes and proves nothing about any of them.
-- 'qvm_compile_correct_identity' needs the tie for EVERY shape a recognizer can return, so it
-- has to be a theorem.
--
-- WHAT LANDS HERE.
--   1. 'foldRangeIdxM_eq_foldlM': the transport between the interpreter's index-driven loop
--      (VmReference.lean:537-544) and the element-driven fold the denotations are written with.
--      Nothing in the tree joined these two shapes of fold, and every denote-theorem needs it.
--   2. 'limbLinearForm_eq_denoteLinFrom' and 'limbLinearForm_eq_denoteLin': the INTERPRETER
--      half of the LIN7 tie, proved for a general byte stream, constant table, memory and
--      valuation. Generic in everything (D-P71): no fixture appears in either statement.
--   3. 'ConstTableSound', 'termBlock', and the two PG_* Props that name precisely what is left.
--
-- WHAT DOES NOT LAND HERE, NAMED. The BUILDER half of the tie - that the bytes 'termFold'
-- (VmBuilder.lean:573) appends are 'termBlock' and that each slot it wrote indexes its own
-- term's coefficient - is recorded as 'PG_termFold_structure'. And the row itself needs more
-- than the limb tie at all: 'identityExpr' is a fuel-bounded mutual block of about 40 panic
-- sites whose arms include the generic stack path, the limb-subshape residue split, the
-- RUN / AFFINE_SUM decomposition and the 'compactQuotientRuns' pass; the segment-totality fact
-- nothing in the tree supplies is 'PG_identity_segment'. Both are Props, not sorries: this
-- file adds NO sorry and moves NO cone, and it adds no hypothesis to any row, to 'ValidV3', to
-- a bundle or to the root (WORKER-RULES hard rule).
--
-- NAMING. Everything here lives in 'Midfall.Lowering.QvmEmit': 'except_bind_ok' is already
-- taken by Midfall/Lowering/Calldata.lean, and a collision in the root import file is a build
-- failure, not a warning.
--
-- NO Midfall/Instances/ IMPORT (D-P17). HAZARD 2: every statement runs at the real modulus
-- through QVMFr and 'qvmFrModulus'.

import Midfall.Lowering.Qvm

namespace Midfall.Lowering.QvmEmit

open Midfall
open Midfall.Lowering
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientExpr QuotientRefMemory fqFromU256 qvmFrAdd
  qvmFrMul qvmFrZero qvmFrModulus quotientVmLimbs deriveReferenceMemory)
open Midfall.Generator.QuotientBuilder

/-! ### 1. Transport between the interpreter's index fold and the denotation's element fold -/

/-- The trailing '>>= fun y => ok y' a 'do' block leaves behind is the identity on 'Except'. -/
theorem except_bind_ok {ε α : Type} (z : Except ε α) : (z >>= fun y => Except.ok y) = z := by
  cases z <;> rfl

/-- TRANSPORT BETWEEN THE TWO FOLD SHAPES. 'foldRangeIdxM' (VmReference.lean:537-544) is the
    interpreter's index-driven loop - the step function receives the INDEX and reaches into
    whatever it reads. 'List.foldlM' is the element-driven fold the denotations are written
    with - 'denoteLin' (Qvm.lean:460-463) is one. When the i-th index step IS the i-th element
    step the two agree, and this is the one place that fact is proved. 'List.get?' does not
    exist in this Lean (WORKER-RULES), so 'List.getD' carries the indexing and 'd' is its
    out-of-range default; every caller supplies hypotheses that only mention indices below the
    length. -/
theorem foldRangeIdxM_eq_foldlM {α β ε : Type} (d : β) :
    ∀ (terms : List β) (f : Nat → α → Except ε α) (g : β → α → Except ε α),
      (∀ i a, f i a = g (terms.getD i d) a) →
      ∀ init, foldRangeIdxM terms.length init f = terms.foldlM (fun a b => g b a) init := by
  intro terms
  induction terms with
  | nil => intro f g h init; rfl
  | cons c rest ih =>
      intro f g h init
      show (f 0 init >>= fun x =>
              foldRangeIdxM rest.length x (fun i => f (i + 1)) >>= fun y => Except.ok y) = _
      have key : ∀ x, foldRangeIdxM rest.length x (fun i => f (i + 1)) =
          rest.foldlM (fun a b => g b a) x :=
        ih (fun i => f (i + 1)) g (by intro j a; exact h (j + 1) a)
      simp only [key, List.foldlM_cons, except_bind_ok]
      rw [h 0 init]
      rfl

/-! ### 2. The LIN7 denotation with a general accumulator -/

/-- 'denoteLin' (Qvm.lean:460) with an explicit accumulator start. Not a second definition of
    the value: 'denoteLinFrom ρ 0' IS 'denoteLin ρ', pinned by 'denoteLin_eq_denoteLinFrom'.
    The general form is needed because the interpreter's fold carries a running sum that starts
    at its caller's accumulator, not at zero. -/
def denoteLinFrom (ρ : Valuation) (init : QVMFr) (terms : List (Word256 × Nat)) :
    Except QVMFault QVMFr :=
  terms.foldlM (fun acc t => do
    let c ← fqFromU256 t.1
    pure (qvmFrAdd acc (qvmFrMul c (ρ 0 (t.2 % 2 ^ 32))))) init

theorem denoteLin_eq_denoteLinFrom (ρ : Valuation) (terms : List (Word256 × Nat)) :
    denoteLin ρ terms = denoteLinFrom ρ 0 terms := rfl

/-- One step of the seven-limb decoder as a function of the state alone. 'limbLinearForm's body
    (VmReference.lean:580-588) reads nothing but the cursor and the memory, so it IS this
    function; 'limbLinearForm_unfold' pins that with 'rfl'. -/
def limbStep (bytes : List Nat) (consts : List Word256)
    (st : QVMFr × Nat × QuotientRefMemory) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  let (acc, cursor, mem) := st
  do let slot ← byteAt bytes cursor
     let ptr ← readU16 bytes (cursor + 1)
     let c ← constAt consts slot cursor
     let (v, mem') := mem.literal ptr
     .ok (qvmFrAdd acc (qvmFrMul c v), cursor + 3, mem')

theorem limbLinearForm_unfold (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    limbLinearForm bytes consts mem idx =
      ((foldRangeIdxM quotientVmLimbs (qvmFrZero, idx, mem)
            (fun _ st => limbStep bytes consts st)) >>=
        fun p => Except.ok (p.1, p.2.1 - idx, p.2.2)) := rfl

theorem getD_drop_one (slots : List Nat) (i : Nat) :
    (slots.drop 1).getD i 0 = slots.getD (i + 1) 0 := by
  cases slots with
  | nil => rfl
  | cons x xs => rfl

/-- THE DECODER-SIDE LIN7 TIE, induction-step form. Run the interpreter's seven-limb decoder
    over a byte stream whose next '3 * terms.length' bytes are the (slot byte, big-endian u16
    pointer) triples of 'terms', over a constant table whose slot lookups return those terms'
    coefficients and a memory whose literal reads are 'ρ': the running sum is
    'denoteLinFrom ρ acc terms' and the cursor has advanced by exactly '3 * terms.length'.
    Stated for a general accumulator and a general starting cursor because the induction needs
    both: the recursive call runs from 'idx + 3' with the head's product already in the sum. -/
theorem limbLinearForm_eq_denoteLinFrom (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (ρ : Valuation) :
    ∀ (terms : List (Word256 × Nat)) (slots : List Nat) (idx : Nat) (acc : QVMFr),
      (∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
          byteAt bytes (idx + 3 * i) = .ok slot) →
      (∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
          readU16 bytes (idx + 3 * i + 1) = .ok t.2) →
      (∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
          constAt consts slot (idx + 3 * i) = fqFromU256 t.1) →
      (∀ p ∈ terms.map Prod.snd, mem.literal p = (ρ 0 (p % 2 ^ 32), mem)) →
      terms.foldlM (fun st _t => limbStep bytes consts st) (acc, idx, mem) =
        (denoteLinFrom ρ acc terms).map (fun v => (v, idx + 3 * terms.length, mem)) := by
  intro terms
  induction terms with
  | nil => intro slots idx acc h1 h2 h3 hmem; rfl
  | cons c rest ih =>
      intro slots idx acc h1 h2 h3 hmem
      obtain ⟨cc, cp, rfl⟩ : ∃ cc cp, c = (cc, cp) := ⟨c.1, c.2, Prod.eta c⟩
      have hlen0 : 0 < ((cc, cp) :: rest).length := by simp
      have hget0 : ((cc, cp) :: rest).getD 0 (0, 0) = (cc, cp) := by simp
      have hb : byteAt bytes idx = .ok (slots.getD 0 0) :=
        by simpa using h1 0 (cc, cp) (slots.getD 0 0) hlen0 hget0 rfl
      have hp : readU16 bytes (idx + 1) = .ok cp :=
        by simpa using h2 0 (cc, cp) (slots.getD 0 0) hlen0 hget0 rfl
      have hc : constAt consts (slots.getD 0 0) idx = fqFromU256 cc :=
        by simpa using h3 0 (cc, cp) (slots.getD 0 0) hlen0 hget0 rfl
      have hm : mem.literal cp = (ρ 0 (cp % 2 ^ 32), mem) := hmem cp (by simp)
      have hrest : ∀ p ∈ rest.map Prod.snd,
          mem.literal p = (ρ 0 (p % 2 ^ 32), mem) := by
        intro p hp'
        exact hmem p (by rw [List.map_cons]; right; exact hp')
      have h1' : ∀ i t slot, i < rest.length → rest.getD i (0, 0) = t →
          (slots.drop 1).getD i 0 = slot → byteAt bytes (idx + 3 + 3 * i) = .ok slot := by
        intro i t slot hi ht hs
        have hz : idx + 3 * (i + 1) = idx + 3 + 3 * i := by omega
        have hdd : slots.getD (i + 1) 0 = slot := by rw [← getD_drop_one]; exact hs
        have := h1 (i + 1) t slot (by simpa using hi)
          (by rw [List.getD_cons_succ]; exact ht) hdd
        rwa [hz] at this
      have h2' : ∀ i t slot, i < rest.length → rest.getD i (0, 0) = t →
          (slots.drop 1).getD i 0 = slot →
          readU16 bytes (idx + 3 + 3 * i + 1) = .ok t.2 := by
        intro i t slot hi ht hs
        have hz : idx + 3 * (i + 1) + 1 = idx + 3 + 3 * i + 1 := by omega
        have hdd : slots.getD (i + 1) 0 = slot := by rw [← getD_drop_one]; exact hs
        have := h2 (i + 1) t slot (by simpa using hi)
          (by rw [List.getD_cons_succ]; exact ht) hdd
        rwa [hz] at this
      have h3' : ∀ i t slot, i < rest.length → rest.getD i (0, 0) = t →
          (slots.drop 1).getD i 0 = slot →
          constAt consts slot (idx + 3 + 3 * i) = fqFromU256 t.1 := by
        intro i t slot hi ht hs
        have hz : idx + 3 * (i + 1) = idx + 3 + 3 * i := by omega
        have hdd : slots.getD (i + 1) 0 = slot := by rw [← getD_drop_one]; exact hs
        have := h3 (i + 1) t slot (by simpa using hi)
          (by rw [List.getD_cons_succ]; exact ht) hdd
        rwa [hz] at this
      cases hcv : fqFromU256 cc with
      | error e =>
          have hstep : limbStep bytes consts (acc, idx, mem) = .error e := by
            show ((byteAt bytes idx >>= fun slot => readU16 bytes (idx + 1) >>= fun ptr =>
                    constAt consts slot idx >>= fun c =>
                      let (v, mem') := mem.literal ptr
                      Except.ok (qvmFrAdd acc (qvmFrMul c v), idx + 3, mem')) :
                  Except QVMFault (QVMFr × Nat × QuotientRefMemory)) = _
            rw [hb, hp]
            show ((constAt consts (slots.getD 0 0) idx >>= fun c =>
                    let (v, mem') := mem.literal cp
                    Except.ok (qvmFrAdd acc (qvmFrMul c v), idx + 3, mem')) :
                  Except QVMFault (QVMFr × Nat × QuotientRefMemory)) = _
            rw [hc, hcv]
            rfl
          have hden : denoteLinFrom ρ acc ((cc, cp) :: rest) = .error e := by
            unfold denoteLinFrom
            rw [List.foldlM_cons, hcv]
            rfl
          rw [List.foldlM_cons, hstep, hden]
          rfl
      | ok cv =>
          have hstep : limbStep bytes consts (acc, idx, mem) =
              .ok (qvmFrAdd acc (qvmFrMul cv (ρ 0 (cp % 2 ^ 32))), idx + 3, mem) := by
            show ((byteAt bytes idx >>= fun slot => readU16 bytes (idx + 1) >>= fun ptr =>
                    constAt consts slot idx >>= fun c =>
                      let (v, mem') := mem.literal ptr
                      Except.ok (qvmFrAdd acc (qvmFrMul c v), idx + 3, mem')) :
                  Except QVMFault (QVMFr × Nat × QuotientRefMemory)) = _
            rw [hb, hp]
            show ((constAt consts (slots.getD 0 0) idx >>= fun c =>
                    let (v, mem') := mem.literal cp
                    Except.ok (qvmFrAdd acc (qvmFrMul c v), idx + 3, mem')) :
                  Except QVMFault (QVMFr × Nat × QuotientRefMemory)) = _
            rw [hc, hcv, hm]
            rfl
          have hden : denoteLinFrom ρ acc ((cc, cp) :: rest) =
              denoteLinFrom ρ (qvmFrAdd acc (qvmFrMul cv (ρ 0 (cp % 2 ^ 32)))) rest := by
            unfold denoteLinFrom
            rw [List.foldlM_cons, hcv]
            rfl
          rw [List.foldlM_cons, hstep, hden]
          show (List.foldlM (fun st _t => limbStep bytes consts st)
                  (qvmFrAdd acc (qvmFrMul cv (ρ 0 (cp % 2 ^ 32))), idx + 3, mem) rest) = _
          rw [ih (slots.drop 1) (idx + 3) (qvmFrAdd acc (qvmFrMul cv (ρ 0 (cp % 2 ^ 32))))
            h1' h2' h3' hrest]
          have hlen' : 3 * ((cc, cp) :: rest).length = 3 + 3 * rest.length := by
            rw [List.length_cons]
            omega
          rw [show (fun v => (v, idx + 3 * ((cc, cp) :: rest).length, mem)) =
              (fun v => (v, idx + 3 + 3 * rest.length, mem)) from by
            funext v
            rw [hlen']
            rw [← Nat.add_assoc]]

/-- THE DECODER-SIDE LIN7 TIE. The interpreter's seven-limb decoder over a byte stream that
    spells 'terms' as (slot byte, big-endian u16 pointer) triples, over a constant table whose
    slots return those terms' coefficients and a memory whose literal reads are 'ρ', computes
    'denoteLin ρ terms' and consumes exactly '3 * terms.length' bytes. This is the half of
    QIDENT need (3) that lives on the interpreter side; the builder half is
    'PG_termFold_structure'. -/
theorem limbLinearForm_eq_denoteLin (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (ρ : Valuation)
    (terms : List (Word256 × Nat)) (slots : List Nat) (idx : Nat)
    (hlen : terms.length = quotientVmLimbs)
    (hbyte : ∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        byteAt bytes (idx + 3 * i) = .ok slot)
    (hptr : ∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        readU16 bytes (idx + 3 * i + 1) = .ok t.2)
    (hconst : ∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        constAt consts slot (idx + 3 * i) = fqFromU256 t.1)
    (hmem : ∀ p ∈ terms.map Prod.snd, mem.literal p = (ρ 0 (p % 2 ^ 32), mem)) :
    limbLinearForm bytes consts mem idx =
      (denoteLin ρ terms).map (fun v => (v, 3 * terms.length, mem)) := by
  rw [limbLinearForm_unfold, ← hlen]
  rw [foldRangeIdxM_eq_foldlM (d := (0, 0)) (terms := terms)
    (f := fun _ st => limbStep bytes consts st) (g := fun _t st => limbStep bytes consts st)
    (by intro i a; rfl) (qvmFrZero, idx, mem)]
  rw [limbLinearForm_eq_denoteLinFrom bytes consts mem ρ terms slots idx qvmFrZero
    hbyte hptr hconst hmem]
  cases hdl : denoteLinFrom ρ qvmFrZero terms with
  | ok v =>
      have hden : denoteLin ρ terms = .ok v := hdl
      rw [hden]
      show Except.ok (v, idx + 3 * terms.length - idx, mem) =
        Except.ok (v, 3 * terms.length, mem)
      rw [show idx + 3 * terms.length - idx = 3 * terms.length from by omega]
  | error e =>
      have hden : denoteLin ρ terms = .error e := hdl
      rw [hden]
      rfl

/-! ### 3. The builder side, and what is named rather than sorried -/

/-- The builder's slot map agrees with its constant table: every coefficient the builder can
    look up is indexed by the slot it would emit for it. 'builderDefault' satisfies it
    vacuously and 'constSlot' (VmBuilder.lean:359-370) preserves it - the found arm reads the
    table it was told, and the fresh arm appends the value at exactly the slot it returns - so
    every state the builder reaches from the default one does. This is the invariant the
    emitted slot BYTES depend on, and the reason 'hconsts' appears on the row. -/
def ConstTableSound (s : QuotientProgramBuilder) : Prop :=
  ∀ c slot, constSlotOf s c = some slot → ∃ rest, s.consts.drop slot = c :: rest

/-- The byte block 'termFold' (VmBuilder.lean:573-581) appends: one (slot byte, big-endian u16
    pointer) triple per term, in order. Defined here rather than read off the builder because
    the builder's fold threads the whole state; 'PG_termFold_structure' is the claim that this
    IS what the builder writes. -/
def termBlock : List Nat → List (Word256 × Nat) → List Nat
  | [], _ => []
  | _, [] => []
  | slot :: slots, (_c, ptr) :: terms =>
      slot :: ptr / 256 :: ptr % 256 :: termBlock slots terms

/-- THE MISSING BUILDER LINK, named rather than sorried. Combined with
    'limbLinearForm_eq_denoteLin' above this is exactly the theorem form of
    'denoteLimbShape_matchesByteDecoder_ok' (Qvm.lean:4060) for the LIN7 arm: the bytes
    'termFold' appends are 'termBlock', the slots it wrote are u8, and each slot indexes its
    own term's coefficient in the table it produced. It is a Prop, so it adds no sorry and
    moves no cone. What stops it being a theorem in the time available is one specific thing:
    the fourth conjunct needs 'ConstTableSound' as an INDUCTIVE invariant of 'foldLeftM' over
    the slot list, and the append that 'constSlot' performs makes the lookup in the grown slot
    map agree with the lookup in the grown table only under a prefix-stability argument on
    'List.find?' - three lemmas ('constSlot_step', 'find?_append_prefix', 'drop_append_prefix')
    that are each short but none of which exists in the tree today. -/
def PG_termFold_structure : Prop :=
  ∀ (terms : List (Word256 × Nat)) (s s' : QuotientProgramBuilder) (site : String),
    ConstTableSound s →
    termFold s terms site = .ok s' →
    (∀ p ∈ terms.map Prod.snd, p ≤ 0xffff) →
    ∃ (slots : List Nat),
      slots.length = terms.length ∧
      s'.bytes = s.bytes ++ termBlock slots terms ∧
      (∀ i slot, i < terms.length → slots.getD i 0 = slot → slot ≤ 255) ∧
      (∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        ∃ rest, s'.consts.drop slot = t.1 :: rest)

/-- THE ROW'S REAL OBSTACLE, named. 'qvm_compile_correct_identity' (Qvm.lean:619-631) is not
    blocked on the limb tie alone. Its 'hemit' is 'identityExpr r s₀ e t gap = .ok s₁', and
    'identityExpr' (VmBuilder.lean:934) is the fuel-bounded mutual block with about 40 panic
    sites whose arms include the generic stack path (PUSH_MEM_*, ADD, MUL, NEG, POW5), the
    limb-SUBSHAPE residue split, the RUN / AFFINE_SUM decomposition and the
    'compactQuotientRuns' pass the row's own 'hcompact' names. What nothing in the tree
    supplies is that the emitted segment NEVER FAULTS: every read it performs lies inside the
    pointers 'e' names, so 'evalQuotientIdentity' on it returns for every valuation. That is a
    second induction - over the emitted instruction sequence rather than over the expression -
    and it is what this Prop names. It is also exactly what 'builder_segments_total'
    (Qvm.lean:992-1003) needs, so the two holes are one hole. -/
def PG_identity_segment : Prop :=
  ∀ (r : QuotientShapeRecognizers) (_hr : RecognizersSound r)
    (s₀ s₁ : QuotientProgramBuilder) (e : QuotientExpr) (t : QuotientTarget)
    (gap : Option Nat) (cseg seg : List Nat),
    identityExpr r s₀ e t gap = .ok s₁ →
    exprBounded e →
    (∀ c ∈ s₁.consts, c.toNat < qvmFrModulus) →
    compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg →
    finalizedIdentitySegment cseg = some seg →
    ∀ (ρ : Valuation),
      (Midfall.Generator.evalQuotientIdentity seg s₁.consts (memOfρ ρ (leafKeys e))).isOk

end Midfall.Lowering.QvmEmit

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


/-- THE DECODER-SIDE ROW TIE. `limbRowForm` reads the lhs pointer first, hits it, then runs
    the seven-limb linear decoder on the remaining terms and multiplies. The shape
    denotation `denoteLimbShape ρ (.bilin7Row lhs terms)` is the same product. The lhs and
    term pointers are required to be memory hits at `ρ`, which is the no-miss condition the
    valuation layer supplies; this is the ROW analogue of `limbLinearForm_eq_denoteLin`. -/
theorem limbRowForm_eq_denoteLimbRow (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (ρ : Valuation) (lhs : Nat) (terms : List (Word256 × Nat))
    (slots : List Nat) (idx : Nat)
    (hlen : terms.length = quotientVmLimbs)
    (hlhs : Midfall.Generator.readU16 bytes idx = .ok lhs)
    (hbyte : ∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        Midfall.Generator.byteAt bytes (idx + 2 + 3 * i) = .ok slot)
    (hptr : ∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        Midfall.Generator.readU16 bytes (idx + 2 + 3 * i + 1) = .ok t.2)
    (hconst : ∀ i t slot, i < terms.length → terms.getD i (0, 0) = t → slots.getD i 0 = slot →
        Midfall.Generator.constAt consts slot (idx + 2 + 3 * i) = fqFromU256 t.1)
    (hmem : ∀ p ∈ terms.map Prod.snd, mem.literal p = (ρ 0 (p % 2 ^ 32), mem))
    (hlhsmem : mem.literal lhs = (ρ 0 (lhs % 2 ^ 32), mem)) :
    Midfall.Generator.limbRowForm bytes consts mem idx =
      (denoteLimbShape ρ (.bilin7Row lhs terms)).map (fun v => (v, 23, mem)) := by
  unfold Midfall.Generator.limbRowForm
  rw [hlhs]
  simp only [bind, Except.bind]
  rw [hlhsmem]
  rw [limbLinearForm_eq_denoteLin bytes consts mem ρ terms slots (idx + 2) hlen
    (by intro i t sl hi ht hs; exact hbyte i t sl hi ht hs)
    (by intro i t sl hi ht hs; exact hptr i t sl hi ht hs)
    (by intro i t sl hi ht hs; exact hconst i t sl hi ht hs) hmem]
  unfold denoteLimbShape
  cases hd : denoteLin ρ terms with
  | error e =>
      simp only [hd, Except.map, bind, Except.bind, pure, Except.pure]
  | ok v =>
      have h7 : 3 * terms.length = 21 := by
        rw [hlen]; rfl
      simp only [hd, Except.map, bind, Except.bind, pure, Except.pure]
      rw [h7]

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
    finalizedIdentitySegment t cseg = some seg →
    ∀ (ρ : Valuation),
      (Midfall.Generator.evalQuotientIdentity seg s₁.consts (memOfρ ρ (leafKeys e))).isOk

end Midfall.Lowering.QvmEmit


/-! ### 4. `PG_identity_preFold` DISCHARGED: the emitter is append-only and ends in its fold

    The identity row's reduction (`Qvm.lean` IDVALUE) needs the emitted body to be the bytes
    `finalizedIdentitySegment` can strip: `identityExpr` must append to `s₀.bytes` and its last
    instruction must be `foldIdentity`. This section proves both.

    THE METHOD. Every byte-writing primitive (`op0`, `pushByte`, `emitU16/24/32`) appends a suffix;
    `constSlot` and `popStackAcct` change the table/depth but not the bytes; the non-recursive
    emitters (`emitConst`, `emitMemLiteral`, `emitAccLeaf`, `emitProductAdd`, `termFold`,
    `emitLimbShape`, `emitModarith7Shape`, `tryEmitLimbShape`, `tryEmitModarith7Shape`,
    `foldIdentity`) are chained with `AppendTo_trans`. For the seven mutually recursive emitters the
    proof is a STRONG INDUCTION ON FUEL (`Nat.strong_induction_on`), not `emitExpr.induct`: every
    recursive call is at the predecessor fuel, so one induction hypothesis (`EmitAppend r m`) covers
    all seven functions and the 24-case induction principle is not needed.

    The final two lemmas record the exact trailing instruction: `foldIdentity` appends
    `[FOLD_MAIN]` or `[FOLD_SELECTOR, b1, b2, b3]`, and `finalizedIdentitySegment` returns `some`
    on either suffix. `PG_identity_preFold` follows by dropping the input prefix.

    NO hypothesis was added to a row, to `ValidV3`, a bundle or the root. No sorry, no
    `native_decide`, no maxHeartbeats/maxRecDepth change. Statements are generic in the emitter,
    recognizer bundle, expression, target, gap and builder. -/

namespace Midfall.Lowering.QvmEmit

open Midfall
open Midfall.Generator
open Midfall.Generator.QuotientBuilder

def AppendTo (s s' : QuotientProgramBuilder) : Prop := ∃ t, s'.bytes = s.bytes ++ t

theorem AppendTo_trans {a b c : QuotientProgramBuilder} (h1 : AppendTo a b) (h2 : AppendTo b c) :
    AppendTo a c := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  exact ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

theorem AppendTo_refl (a : QuotientProgramBuilder) : AppendTo a a := ⟨[], by simp⟩

theorem appendBytes_append (s : QuotientProgramBuilder) (bs : List Nat) :
    AppendTo s (appendBytes s bs) := ⟨bs, rfl⟩

theorem emitU16_append (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU16 s v = .ok s') : AppendTo s s' := by
  unfold emitU16 at h
  split at h
  · cases h
  · cases h
    exact ⟨_, rfl⟩

theorem emitU24_append (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU24 s v = .ok s') : AppendTo s s' := by
  unfold emitU24 at h
  split at h
  · cases h
  · cases h
    exact ⟨_, rfl⟩

theorem emitU32_append (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU32 s v = .ok s') : AppendTo s s' := by
  unfold emitU32 at h
  cases h
  exact ⟨_, rfl⟩

theorem pushByte_append (s : QuotientProgramBuilder) (b : Nat) : AppendTo s (pushByte s b) :=
  ⟨[b], rfl⟩

theorem op0_append (s : QuotientProgramBuilder) (op : Nat) : AppendTo s (op0 s op) :=
  ⟨[op], rfl⟩

theorem pushStackAcct_append (s : QuotientProgramBuilder) : AppendTo s (pushStackAcct s) := by
  refine ⟨[], ?_⟩
  simp [pushStackAcct]

theorem popStackAcct_bytes (s : QuotientProgramBuilder) (s' : QuotientProgramBuilder)
    (h : popStackAcct s = .ok s') : s'.bytes = s.bytes := by
  unfold popStackAcct at h
  split at h
  · cases h
  · cases h
    rfl

theorem popStackAcct_append (s : QuotientProgramBuilder) (s' : QuotientProgramBuilder)
    (h : popStackAcct s = .ok s') : AppendTo s s' := by
  unfold popStackAcct at h
  split at h
  · cases h
  · cases h
    refine ⟨[], ?_⟩
    simp

theorem opBinary_append (s : QuotientProgramBuilder) (op : Nat) (s' : QuotientProgramBuilder)
    (h : opBinary s op = .ok s') : AppendTo s s' := by
  unfold opBinary at h
  have h1 := popStackAcct_append (op0 s op) s' h
  obtain ⟨t, ht⟩ := h1
  refine ⟨[op] ++ t, ?_⟩
  rw [ht]
  simp [op0, List.append_assoc]

theorem constSlot_bytes (s : QuotientProgramBuilder) (v : Word256)
    (s' : QuotientProgramBuilder) (slot : Nat) (h : constSlot s v = .ok (s', slot)) :
    s'.bytes = s.bytes := by
  unfold constSlot at h
  cases hcs : constSlotOf s v with
  | some sl =>
      rw [hcs] at h
      obtain ⟨rfl, rfl⟩ := Except.ok.inj h
      rfl
  | none =>
      rw [hcs] at h
      simp only [bind, Except.bind] at h
      by_cases hs : s.consts.length > 0xffff
      · rw [if_pos hs] at h
        cases h
      · rw [if_neg hs] at h
        obtain ⟨rfl, rfl⟩ := Except.ok.inj h
        rfl

theorem constSlot_append (s : QuotientProgramBuilder) (v : Word256)
    (s' : QuotientProgramBuilder) (slot : Nat) (h : constSlot s v = .ok (s', slot)) :
    AppendTo s s' := ⟨[], by rw [constSlot_bytes s v s' slot h]; simp⟩

theorem emitConst_append (s : QuotientProgramBuilder) (v : Word256) (s' : QuotientProgramBuilder)
    (h : emitConst s v = .ok s') : AppendTo s s' := by
  unfold emitConst at h
  obtain ⟨a, h1, h2⟩ := peel_bind h
  rcases a with ⟨s1, slot⟩
  have hb := constSlot_bytes s v s1 slot h1
  by_cases hle : slot ≤ 255
  · simp only [hle, decide_eq_true_eq] at h2
    cases h2
    exact ⟨[qOpPushConstU8, slot], by simp [pushByte, appendBytes, hb]⟩
  · simp only [hle, decide_eq_false_iff_not] at h2
    exact AppendTo_trans
      (AppendTo_trans ⟨[], by simp [hb]⟩ (pushByte_append s1 qOpPushConst))
      (emitU16_append (pushByte s1 qOpPushConst) slot s' h2)

theorem emitMemLiteral_append (s : QuotientProgramBuilder) (ptr : Nat)
    (s' : QuotientProgramBuilder) (h : emitMemLiteral s ptr = .ok s') : AppendTo s s' := by
  unfold emitMemLiteral at h
  split at h
  · exact AppendTo_trans (pushByte_append s qOpPushMemU16)
      (emitU16_append (pushByte s qOpPushMemU16) ptr s' h)
  · exact AppendTo_trans (pushByte_append s qOpPushMemLiteral)
      (emitU32_append (pushByte s qOpPushMemLiteral) ptr s' h)

def termStep (s : QuotientProgramBuilder) (cp : Word256 × Nat) (site : String) :
    M QuotientProgramBuilder := do
  let (coeff, ptr) := cp
  let (s, slot) ← constSlot s coeff
  if slot > 255 then panicAt site
  else do
    let s ← emitU16 (pushByte s slot) ptr
    .ok s

theorem termStep_append (s : QuotientProgramBuilder) (cp : Word256 × Nat) (site : String)
    (s' : QuotientProgramBuilder) (h : termStep s cp site = .ok s') : AppendTo s s' := by
  unfold termStep at h
  obtain ⟨coeff, ptr⟩ := cp
  obtain ⟨a, h1, h2⟩ := peel_bind h
  rcases a with ⟨s1, slot⟩
  dsimp only at h2
  have hb := constSlot_bytes s coeff s1 slot h1
  by_cases hslot : slot > 255
  · rw [if_pos hslot] at h2; cases h2
  · rw [if_neg hslot] at h2
    cases h3 : emitU16 (pushByte s1 slot) ptr with
    | error e => rw [h3] at h2; cases h2
    | ok s2 =>
        rw [h3] at h2
        have hs : s2 = s' := Except.ok.inj h2
        subst hs
        exact AppendTo_trans (AppendTo_trans ⟨[], by simp [hb]⟩ (pushByte_append s1 slot))
          (emitU16_append (pushByte s1 slot) ptr s2 h3)

theorem termFold_append (s : QuotientProgramBuilder) (terms : List (Word256 × Nat)) (site : String)
    (s' : QuotientProgramBuilder) (h : termFold s terms site = .ok s') : AppendTo s s' := by
  unfold termFold at h
  induction terms generalizing s with
  | nil => simp at h; cases h; exact ⟨[], by simp⟩
  | cons cp rest ih =>
      simp only [foldLeftM] at h
      obtain ⟨a, h1, h2⟩ := peel_bind h
      have h1' : termStep s cp site = .ok a := h1
      exact AppendTo_trans (termStep_append s cp site a h1') (ih a h2)

theorem emitProductAdd_append (s : QuotientProgramBuilder) (p : QuotientProductAdd)
    (s' : QuotientProgramBuilder) (h : emitProductAdd s p = .ok s') : AppendTo s s' := by
  cases p with
  | memMemConstU8 lhs rhs scalar =>
      unfold emitProductAdd at h
      obtain ⟨a, h1, h2⟩ := peel_bind h
      rcases a with ⟨s1, slot⟩
      dsimp only at h2
      have hb := constSlot_bytes s scalar s1 slot h1
      by_cases hslot : slot > 255
      · rw [if_pos hslot] at h2; cases h2
      · rw [if_neg hslot] at h2
        simp only [bind, Except.bind] at h2
        obtain ⟨s2, h3, h4⟩ := peel_bind h2
        obtain ⟨s3, h5, h6⟩ := peel_bind h4
        cases h6
        exact AppendTo_trans (AppendTo_trans ⟨[], by simp [hb]⟩
          (AppendTo_trans (pushByte_append s1 qOpAddMulMemMemConstU8)
            (AppendTo_trans (emitU16_append (pushByte s1 qOpAddMulMemMemConstU8) lhs s2 h3)
              (emitU16_append s2 rhs s3 h5)))) (pushByte_append s3 slot)
  | constU8Mem scalar ptr =>
      unfold emitProductAdd at h
      obtain ⟨a, h1, h2⟩ := peel_bind h
      rcases a with ⟨s1, slot⟩
      dsimp only at h2
      have hb := constSlot_bytes s scalar s1 slot h1
      by_cases hslot : slot > 255
      · rw [if_pos hslot] at h2; cases h2
      · rw [if_neg hslot] at h2
        simp only [bind, Except.bind] at h2
        obtain ⟨s2, h3, h4⟩ := peel_bind h2
        cases h4
        exact AppendTo_trans (AppendTo_trans ⟨[], by simp [hb]⟩
          (AppendTo_trans (pushByte_append s1 qOpAddMulConstU8MemU16)
            (emitU16_append (pushByte s1 qOpAddMulConstU8MemU16) ptr s2 h3)))
          (pushByte_append s2 slot)
  | memMem lhs rhs =>
      unfold emitProductAdd at h
      obtain ⟨s2, h3, h4⟩ := peel_bind h
      exact AppendTo_trans (AppendTo_trans (pushByte_append s qOpAddMulMemMem)
        (emitU16_append (pushByte s qOpAddMulMemMem) lhs s2 h3))
        (emitU16_append s2 rhs s' h4)



theorem emitAccLeaf_append (s : QuotientProgramBuilder) (leaf : QuotientLeaf) (constU8Op constOp memU16Op : Nat)
    (p : Bool × QuotientProgramBuilder)
    (h : emitAccLeaf s leaf constU8Op constOp memU16Op = .ok p) : AppendTo s p.2 := by
  cases leaf with
  | const value =>
      unfold emitAccLeaf at h
      obtain ⟨a, h1, h2⟩ := peel_bind h
      rcases a with ⟨s1, slot⟩
      dsimp only at h2
      have hb := constSlot_bytes s value s1 slot h1
      by_cases hslot : slot ≤ 255
      · rw [if_pos hslot] at h2
        cases h2
        exact ⟨[constU8Op, slot], by simp [pushByte, appendBytes, hb]⟩
      · rw [if_neg hslot] at h2
        cases h3 : emitU16 (pushByte s1 constOp) slot with
        | error e => rw [h3] at h2; cases h2
        | ok s2 =>
            rw [h3] at h2
            cases h2
            exact AppendTo_trans (AppendTo_trans ⟨[], by simp [hb]⟩ (pushByte_append s1 constOp))
              (emitU16_append (pushByte s1 constOp) slot s2 h3)
  | mem m =>
      cases m with
      | literal ptr =>
          unfold emitAccLeaf at h
          dsimp only at h
          by_cases hp : ptr ≤ 0xffff
          · rw [if_pos hp] at h
            cases h3 : emitU16 (pushByte s memU16Op) ptr with
            | error e => rw [h3] at h; cases h
            | ok s2 =>
                rw [h3] at h
                cases h
                exact AppendTo_trans (pushByte_append s memU16Op)
                  (emitU16_append (pushByte s memU16Op) ptr s2 h3)
          · rw [if_neg hp] at h
            cases h
            exact ⟨[], by simp⟩
      | token t =>
          unfold emitAccLeaf at h
          dsimp only at h
          cases h
          exact ⟨[], by simp⟩
      | tokenOffset t o =>
          unfold emitAccLeaf at h
          dsimp only at h
          cases h
          exact ⟨[], by simp⟩



theorem foldLeftM_append {β : Type} (f : QuotientProgramBuilder → β → M QuotientProgramBuilder)
    (hstep : ∀ s x a, f s x = .ok a → AppendTo s a) :
    ∀ (xs : List β) (init out : QuotientProgramBuilder),
      foldLeftM f init xs = .ok out → AppendTo init out := by
  intro xs
  induction xs with
  | nil => intro init out h; simp [foldLeftM] at h; cases h; exact ⟨[], by simp⟩
  | cons x rest ih =>
      intro init out h
      simp only [foldLeftM] at h
      obtain ⟨a, h1, h2⟩ := peel_bind h
      exact AppendTo_trans (hstep init x a h1) (ih a out h2)

def pwCoeffStep (s : QuotientProgramBuilder) (coeff : Word256) : M QuotientProgramBuilder := do
  let (s, slot) ← constSlot s coeff
  if slot > 255 then panicAt siteBilin7PairwiseSlot
  else .ok (pushByte s slot)

theorem emitLimbShape_append (s : QuotientProgramBuilder) (shape : QuotientLimbShape)
    (s' : QuotientProgramBuilder) (h : emitLimbShape s shape = .ok s') : AppendTo s s' := by
  unfold emitLimbShape at h
  obtain ⟨a, h1, h2⟩ := peel_bind h
  cases h2
  cases shape with
  | lin7 terms =>
      exact AppendTo_trans (AppendTo_trans (pushByte_append s qOpLin7)
          (termFold_append (pushByte s qOpLin7) terms siteLin7Slot a h1)) (pushStackAcct_append a)
  | bilin7Row lhs terms =>
      obtain ⟨a1, h3, h4⟩ := peel_bind h1
      exact AppendTo_trans (AppendTo_trans (pushByte_append s qOpBilin7Row)
          (emitU16_append (pushByte s qOpBilin7Row) lhs a1 h3))
        (AppendTo_trans (termFold_append a1 terms siteBilin7RowSlot a h4) (pushStackAcct_append a))
  | bilin7Pairwise lhs rhs coeffs =>
      obtain ⟨a1, h3, h4⟩ := peel_bind h1
      obtain ⟨a2, h5, h6⟩ := peel_bind h4
      have hcoeff : AppendTo a2 a := by
        refine foldLeftM_append _ ?_ coeffs a2 a h6
        intro s0 coeff a0 h0
        unfold pwCoeffStep at h0
        obtain ⟨b, hb1, hb2⟩ := peel_bind h0
        rcases b with ⟨s1, slot⟩
        dsimp only at hb2
        have hbytes := constSlot_bytes s0 coeff s1 slot hb1
        by_cases hslot : slot > 255
        · rw [if_pos hslot] at hb2; cases hb2
        · rw [if_neg hslot] at hb2
          cases hb2
          exact ⟨[slot], by simp [pushByte, appendBytes, hbytes]⟩
      exact AppendTo_trans (AppendTo_trans (pushByte_append s qOpBilin7Pairwise)
          (emitU16_append (pushByte s qOpBilin7Pairwise) lhs a1 h3))
        (AppendTo_trans (emitU16_append a1 rhs a2 h5)
          (AppendTo_trans hcoeff (pushStackAcct_append a)))



def modRowStep (s : QuotientProgramBuilder) (row : Nat × List (Word256 × Nat)) :
    M QuotientProgramBuilder := do
  let (lhs, terms) := row
  let s ← emitU16 s lhs
  termFold s terms siteModarith7RowSlot

theorem modRowStep_append (s : QuotientProgramBuilder) (row : Nat × List (Word256 × Nat))
    (s' : QuotientProgramBuilder) (h : modRowStep s row = .ok s') : AppendTo s s' := by
  unfold modRowStep at h
  obtain ⟨lhs, terms⟩ := row
  obtain ⟨a, h1, h2⟩ := peel_bind h
  exact AppendTo_trans (emitU16_append s lhs a h1) (termFold_append a terms siteModarith7RowSlot s' h2)

def modPwInnerStep (s : QuotientProgramBuilder) (coeff : Word256) : M QuotientProgramBuilder := do
  let (s, slot) ← constSlot s coeff
  if slot > 255 then panicAt siteModarith7PairwiseSlot
  else .ok (pushByte s slot)

theorem modPwInnerStep_append (s : QuotientProgramBuilder) (coeff : Word256)
    (s' : QuotientProgramBuilder) (h : modPwInnerStep s coeff = .ok s') : AppendTo s s' := by
  unfold modPwInnerStep at h
  obtain ⟨a, h1, h2⟩ := peel_bind h
  rcases a with ⟨s1, slot⟩
  dsimp only at h2
  have hb := constSlot_bytes s coeff s1 slot h1
  by_cases hslot : slot > 255
  · rw [if_pos hslot] at h2; cases h2
  · rw [if_neg hslot] at h2; cases h2
    exact ⟨[slot], by simp [pushByte, appendBytes, hb]⟩

def modPwStep (s : QuotientProgramBuilder) (pw : Nat × Nat × List Word256) :
    M QuotientProgramBuilder := do
  let (lhs, rhs, coeffs) := pw
  let s ← emitU16 s lhs
  let s ← emitU16 s rhs
  foldLeftM modPwInnerStep s coeffs

theorem modPwStep_append (s : QuotientProgramBuilder) (pw : Nat × Nat × List Word256)
    (s' : QuotientProgramBuilder) (h : modPwStep s pw = .ok s') : AppendTo s s' := by
  unfold modPwStep at h
  obtain ⟨lhs, rhs, coeffs⟩ := pw
  obtain ⟨a1, h1, h2⟩ := peel_bind h
  obtain ⟨a2, h3, h4⟩ := peel_bind h2
  exact AppendTo_trans (emitU16_append s lhs a1 h1)
    (AppendTo_trans (emitU16_append a1 rhs a2 h3)
      (foldLeftM_append modPwInnerStep
        (fun s0 c a0 h0 => modPwInnerStep_append s0 c a0 h0) coeffs a2 s' h4))

def modProdStep (s : QuotientProgramBuilder) (tp : Word256 × Nat × Nat) :
    M QuotientProgramBuilder := do
  let (coeff, lhs, rhs) := tp
  let (s, slot) ← constSlot s coeff
  if slot > 255 then panicAt siteModarith7ProductSlot
  else do
    let s ← emitU16 (pushByte s slot) lhs
    emitU16 s rhs

theorem modProdStep_append (s : QuotientProgramBuilder) (tp : Word256 × Nat × Nat)
    (s' : QuotientProgramBuilder) (h : modProdStep s tp = .ok s') : AppendTo s s' := by
  unfold modProdStep at h
  obtain ⟨coeff, lhs, rhs⟩ := tp
  obtain ⟨a, h1, h2⟩ := peel_bind h
  rcases a with ⟨s1, slot⟩
  dsimp only at h2
  have hb := constSlot_bytes s coeff s1 slot h1
  by_cases hslot : slot > 255
  · rw [if_pos hslot] at h2; cases h2
  · rw [if_neg hslot] at h2
    simp only [bind, Except.bind] at h2
    obtain ⟨a1, h3, h4⟩ := peel_bind h2
    exact AppendTo_trans (AppendTo_trans ⟨[], by simp [hb]⟩ (pushByte_append s1 slot))
      (AppendTo_trans (emitU16_append (pushByte s1 slot) lhs a1 h3)
        (emitU16_append a1 rhs s' h4))



theorem foldlPushByte_append (counts : List Nat) :
    ∀ s : QuotientProgramBuilder, AppendTo s (counts.foldl pushByte s) := by
  induction counts with
  | nil => intro s; exact ⟨[], by simp⟩
  | cons c rest ih =>
      intro s
      show AppendTo s (rest.foldl pushByte (pushByte s c))
      exact AppendTo_trans (pushByte_append s c) (ih (pushByte s c))

theorem emitModarith7Shape_append (s : QuotientProgramBuilder) (shape : QuotientModarith7Shape)
    (s' : QuotientProgramBuilder) (h : emitModarith7Shape s shape = .ok s') : AppendTo s s' := by
  unfold emitModarith7Shape at h
  by_cases hbig : (shape.lin.length > 255 || shape.rows.length > 255 ||
      shape.pairwise.length > 255 || shape.memTerms.length > 255 ||
      shape.productTerms.length > 255) = true
  · rw [if_pos hbig] at h
    cases h
  · rw [if_neg hbig] at h
    dsimp only at h
    -- The two opcode/flag bytes are the first writes.
    set s0 : QuotientProgramBuilder :=
      pushByte (pushByte s qOpModarith7)
        ((if shape.cond.isSome = true then qModarith7FlagCond else 0) |||
          if (BitVec.toNat shape.constant != 0) = true then qModarith7FlagConst else 0) with hs0
    have hhead : AppendTo s s0 := by
      rw [hs0]
      exact AppendTo_trans (pushByte_append s qOpModarith7)
        (pushByte_append (pushByte s qOpModarith7) _)
    -- cond pointer
    obtain ⟨s1, hcondM, h⟩ := peel_bind h
    have hcond : AppendTo s0 s1 := by
      cases hc : shape.cond with
      | none => rw [hc] at hcondM; cases hcondM; exact ⟨[], by simp⟩
      | some cond => rw [hc] at hcondM; exact emitU16_append s0 cond s1 hcondM
    -- optional const slot
    set constM : M QuotientProgramBuilder :=
      if (BitVec.toNat shape.constant != 0) = true then do
        let (s, slot) ← constSlot s1 shape.constant
        if slot > 255 then panicAt siteModarith7ConstSlot
        else .ok (pushByte s slot)
      else .ok s1 with hconstM_def
    obtain ⟨s2, hconstM, h⟩ := peel_bind h
    have hconst : AppendTo s1 s2 := by
      rw [hconstM_def] at hconstM
      by_cases hc : (BitVec.toNat shape.constant != 0) = true
      · rw [if_pos hc] at hconstM
        obtain ⟨a, h1, h2⟩ := peel_bind hconstM
        rcases a with ⟨sa, slot⟩
        dsimp only at h2
        have hb := constSlot_bytes s1 shape.constant sa slot h1
        by_cases hslot : slot > 255
        · rw [if_pos hslot] at h2; cases h2
        · rw [if_neg hslot] at h2; cases h2
          exact ⟨[slot], by simp [pushByte, appendBytes, hb]⟩
      · rw [if_neg hc] at hconstM
        cases hconstM
        exact ⟨[], by simp⟩
    -- the five count bytes
    set s3 : QuotientProgramBuilder :=
      [shape.lin.length, shape.rows.length, shape.pairwise.length, shape.memTerms.length,
        shape.productTerms.length].foldl pushByte s2 with hs3
    have hcounts : AppendTo s2 s3 := by
      rw [hs3]
      exact foldlPushByte_append _ s2
    -- five blocks
    obtain ⟨s4, hlin, h⟩ := peel_bind h
    have hlinA : AppendTo s3 s4 := by
      refine foldLeftM_append (fun acc terms => termFold acc terms siteModarith7LinSlot) ?_ shape.lin s3 s4 hlin
      intro s0' terms a0 h0
      exact termFold_append s0' terms siteModarith7LinSlot a0 h0
    obtain ⟨s5, hrows, h⟩ := peel_bind h
    have hrowsA : AppendTo s4 s5 := by
      have h' : foldLeftM modRowStep s4 shape.rows = .ok s5 := hrows
      exact foldLeftM_append modRowStep (fun s0' r a0 h0 => modRowStep_append s0' r a0 h0) shape.rows s4 s5 h'
    obtain ⟨s6, hpw, h⟩ := peel_bind h
    have hpwA : AppendTo s5 s6 := by
      have h' : foldLeftM modPwStep s5 shape.pairwise = .ok s6 := hpw
      exact foldLeftM_append modPwStep (fun s0' r a0 h0 => modPwStep_append s0' r a0 h0) shape.pairwise s5 s6 h'
    obtain ⟨s7, hmem, h⟩ := peel_bind h
    have hmemA : AppendTo s6 s7 := termFold_append s6 shape.memTerms siteModarith7MemSlot s7 hmem
    obtain ⟨s8, hprod, h⟩ := peel_bind h
    have hprodA : AppendTo s7 s8 := by
      have h' : foldLeftM modProdStep s7 shape.productTerms = .ok s8 := hprod
      exact foldLeftM_append modProdStep (fun s0' r a0 h0 => modProdStep_append s0' r a0 h0) shape.productTerms s7 s8 h'
    have hfinal : s' = pushStackAcct s8 := by
      exact (Except.ok.inj h).symm
    rw [hfinal]
    exact AppendTo_trans hhead (AppendTo_trans hcond (AppendTo_trans hconst
      (AppendTo_trans hcounts (AppendTo_trans hlinA (AppendTo_trans hrowsA
        (AppendTo_trans hpwA (AppendTo_trans hmemA (AppendTo_trans hprodA
          (pushStackAcct_append s8)))))))))



theorem tryEmitLimbShape_append (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (expr : QuotientExpr) (p : Bool × QuotientProgramBuilder)
    (h : tryEmitLimbShape r s expr = .ok p) : AppendTo s p.2 := by
  unfold tryEmitLimbShape at h
  by_cases hb : (!s.limbVmOps) = true
  · rw [if_pos hb] at h; cases h; exact ⟨[], by simp⟩
  · rw [if_neg hb] at h
    cases hs : r.limbShape expr with
    | none => rw [hs] at h; cases h; exact ⟨[], by simp⟩
    | some shape =>
        rw [hs] at h
        dsimp only at h
        by_cases hc : (!limbShapeHasU8ConstSlots s shape) = true
        · rw [if_pos hc] at h; cases h; exact ⟨[], by simp⟩
        · rw [if_neg hc] at h
          obtain ⟨s1, h1, h2⟩ := peel_bind h
          cases h2
          exact emitLimbShape_append s shape s1 h1

theorem tryEmitModarith7Shape_append (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (expr : QuotientExpr) (p : Bool × QuotientProgramBuilder)
    (h : tryEmitModarith7Shape r s expr = .ok p) : AppendTo s p.2 := by
  unfold tryEmitModarith7Shape at h
  by_cases hb : (!s.limbVmOps) = true
  · rw [if_pos hb] at h; cases h; exact ⟨[], by simp⟩
  · rw [if_neg hb] at h
    cases hs : r.modarith7Shape expr with
    | none => rw [hs] at h; cases h; exact ⟨[], by simp⟩
    | some shape =>
        rw [hs] at h
        dsimp only at h
        by_cases hc : (!modarith7ShapeHasU8ConstSlots s shape) = true
        · rw [if_pos hc] at h; cases h; exact ⟨[], by simp⟩
        · rw [if_neg hc] at h
          obtain ⟨s1, h1, h2⟩ := peel_bind h
          cases h2
          exact emitModarith7Shape_append s shape s1 h1

theorem foldIdentity_append (s : QuotientProgramBuilder) (target : QuotientTarget)
    (gap : Option Nat) (s' : QuotientProgramBuilder)
    (h : foldIdentity s target gap = .ok s') : AppendTo s s' := by
  unfold foldIdentity at h
  cases target with
  | main =>
      dsimp only at h
      exact AppendTo_trans (op0_append s qOpFoldMain)
        (popStackAcct_append (op0 s qOpFoldMain) s' h)
  | selector idx =>
      dsimp only at h
      cases hg : gap with
      | none => rw [hg] at h; cases h
      | some g =>
          rw [hg] at h
          dsimp only at h
          simp only [bind, Except.bind] at h
          by_cases hi : idx > 255
          · rw [if_pos hi] at h; cases h
          · rw [if_neg hi] at h
            by_cases hgap : g > 0xffff
            · rw [if_pos hgap] at h; cases h
            · rw [if_neg hgap] at h
              obtain ⟨a1, h1, h2⟩ := peel_bind h
              exact AppendTo_trans (AppendTo_trans (pushByte_append s qOpFoldSelector)
                (emitU24_append (pushByte s qOpFoldSelector) ((idx * 65536) ||| g) a1 h1))
                (popStackAcct_append a1 s' h2)



structure EmitAppend (r : QuotientShapeRecognizers) (n : Nat) : Prop where
  expr : ∀ (s : QuotientProgramBuilder) (e : QuotientExpr) (s' : QuotientProgramBuilder),
    emitExpr r n s e = .ok s' → AppendTo s s'
  binary : ∀ (s : QuotientProgramBuilder) (lhs rhs : QuotientExpr)
    (stackOp constU8Op constOp memU16Op : Nat) (s' : QuotientProgramBuilder),
    emitBinaryExpr r n s lhs rhs stackOp constU8Op constOp memU16Op = .ok s' → AppendTo s s'
  addProduct : ∀ (s : QuotientProgramBuilder) (base product : QuotientExpr)
    (p : Bool × QuotientProgramBuilder),
    tryEmitAddProduct r n s base product = .ok p → AppendTo s p.2
  limbDecomp : ∀ (s : QuotientProgramBuilder) (expr : QuotientExpr)
    (p : Bool × QuotientProgramBuilder),
    tryEmitLimbDecomposition r n s expr = .ok p → AppendTo s p.2
  affine : ∀ (s : QuotientProgramBuilder) (terms : List QuotientExpr)
    (s' : QuotientProgramBuilder),
    emitAffineTerms r n s terms = .ok s' → AppendTo s s'
  affineRest : ∀ (s : QuotientProgramBuilder) (terms : List QuotientExpr)
    (s' : QuotientProgramBuilder),
    emitAffineTermsRest r n s terms = .ok s' → AppendTo s s'
  pow5 : ∀ (s : QuotientProgramBuilder) (e : QuotientExpr) (p : Bool × QuotientProgramBuilder),
    tryEmitPow5 r n s e = .ok p → AppendTo s p.2

theorem emitAppend_all (r : QuotientShapeRecognizers) : ∀ n, EmitAppend r n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero =>
      constructor
      · intro s e s' h; simp [emitExpr] at h; cases h
      · intro s lhs rhs a b c d s' h; simp [emitBinaryExpr] at h; cases h
      · intro s base product p h; simp [tryEmitAddProduct] at h; cases h
      · intro s expr p h; simp [tryEmitLimbDecomposition] at h; cases h
      · intro s terms s' h; simp [emitAffineTerms] at h; cases h
      · intro s terms s' h; simp [emitAffineTermsRest] at h; cases h
      · intro s e p h; simp [tryEmitPow5] at h; cases h
  | succ m =>
      have IH := ih m (by omega)
      constructor
      · intro s e s' h
        simp only [emitExpr] at h
        obtain ⟨p1, h1, h2⟩ := peel_bind h
        have hp1 := IH.pow5 s e p1 h1
        cases hp1b : p1.1 with
        | true =>
            rw [hp1b] at h2
            cases h2
            exact hp1
        | false =>
            rw [hp1b] at h2
            obtain ⟨p2, h3, h4⟩ := peel_bind h2
            have hp2 := tryEmitModarith7Shape_append r p1.2 e p2 h3
            have h12 : AppendTo s p2.2 := AppendTo_trans hp1 hp2
            cases hp2b : p2.1 with
            | true =>
                rw [hp2b] at h4
                cases h4
                exact h12
            | false =>
                rw [hp2b] at h4
                obtain ⟨p3, h5, h6⟩ := peel_bind h4
                have hp3 := tryEmitLimbShape_append r p2.2 e p3 h5
                have h123 : AppendTo s p3.2 := AppendTo_trans h12 hp3
                cases hp3b : p3.1 with
                | true =>
                    rw [hp3b] at h6
                    cases h6
                    exact h123
                | false =>
                    rw [hp3b] at h6
                    obtain ⟨p4, h7, h8⟩ := peel_bind h6
                    have hp4 := IH.limbDecomp p3.2 e p4 h7
                    have h1234 : AppendTo s p4.2 := AppendTo_trans h123 hp4
                    cases hp4b : p4.1 with
                    | true =>
                        rw [hp4b] at h8
                        cases h8
                        exact h1234
                    | false =>
                        rw [hp4b] at h8
                        cases e with
                        | const value =>
                            obtain ⟨s1, h9, h10⟩ := peel_bind h8
                            have hc := emitConst_append p4.2 value s1 h9
                            have h11 : s' = pushStackAcct s1 := (Except.ok.inj h10).symm
                            rw [h11]
                            exact AppendTo_trans (AppendTo_trans h1234 hc) (pushStackAcct_append s1)
                        | mem m =>
                            cases m with
                            | literal ptr =>
                                obtain ⟨s1, h9, h10⟩ := peel_bind h8
                                have hc := emitMemLiteral_append p4.2 ptr s1 h9
                                have h11 : s' = pushStackAcct s1 := (Except.ok.inj h10).symm
                                rw [h11]
                                exact AppendTo_trans (AppendTo_trans h1234 hc) (pushStackAcct_append s1)
                            | token t =>
                                cases h8
                                exact AppendTo_trans h1234 ⟨[qOpPushMemToken, t],
                                  by simp [pushByte, appendBytes, pushStackAcct]⟩
                            | tokenOffset t o =>
                                obtain ⟨s1, h9, h10⟩ := peel_bind h8
                                cases h10
                                exact AppendTo_trans h1234 (AppendTo_trans
                                  (AppendTo_trans (pushByte_append p4.2 qOpPushMemTokenOffset)
                                    (pushByte_append (pushByte p4.2 qOpPushMemTokenOffset) t))
                                  (AppendTo_trans (emitU32_append
                                    (pushByte (pushByte p4.2 qOpPushMemTokenOffset) t) o s1 h9)
                                    (pushStackAcct_append s1)))
                        | add lhs rhs =>
                            obtain ⟨p5, h9, h10⟩ := peel_bind h8
                            have hp5 := IH.addProduct p4.2 lhs rhs p5 h9
                            have h5c : AppendTo s p5.2 := AppendTo_trans h1234 hp5
                            cases hp5b : p5.1 with
                            | true =>
                                rw [hp5b] at h10; cases h10; exact h5c
                            | false =>
                                rw [hp5b] at h10
                                obtain ⟨p6, h11, h12⟩ := peel_bind h10
                                have hp6 := IH.addProduct p5.2 rhs lhs p6 h11
                                have h6c : AppendTo s p6.2 := AppendTo_trans h5c hp6
                                cases hp6b : p6.1 with
                                | true =>
                                    rw [hp6b] at h12; cases h12; exact h6c
                                | false =>
                                    rw [hp6b] at h12
                                    exact AppendTo_trans h6c
                                      (IH.binary p6.2 lhs rhs qOpAdd qOpAddConstU8 qOpAddConst
                                        qOpAddMemU16 s' h12)
                        | mul lhs rhs =>
                            exact AppendTo_trans h1234
                              (IH.binary p4.2 lhs rhs qOpMul qOpMulConstU8 qOpMulConst qOpMulMemU16 s' h8)
                        | neg inner =>
                            obtain ⟨s1, h9, h10⟩ := peel_bind h8
                            cases h10
                            exact AppendTo_trans h1234 (AppendTo_trans (IH.expr p4.2 inner s1 h9)
                              (op0_append s1 qOpNeg))
      · intro s lhs rhs stackOp constU8Op constOp memU16Op s' h
        simp only [emitBinaryExpr] at h
        cases hr : quotientLeaf rhs with
        | some leaf =>
            rw [hr] at h
            dsimp only at h
            obtain ⟨s1, h1, h2⟩ := peel_bind h
            have hp1 := IH.expr s lhs s1 h1
            obtain ⟨res, h3, h4⟩ := peel_bind h2
            rcases res with ⟨hit, s2⟩
            cases hit with
            | true =>
                dsimp only at h4
                have hs : s2 = s' := Except.ok.inj h4
                subst hs
                exact AppendTo_trans hp1 (emitAccLeaf_append s1 leaf constU8Op constOp memU16Op
                  (true, s2) h3)
            | false =>
                dsimp only at h4
                obtain ⟨s3, h5, h6⟩ := peel_bind h4
                exact AppendTo_trans hp1 (AppendTo_trans
                  (emitAccLeaf_append s1 leaf constU8Op constOp memU16Op (false, s2) h3)
                  (AppendTo_trans (IH.expr s2 rhs s3 h5) (opBinary_append s3 stackOp s' h6)))
        | none =>
            rw [hr] at h
            dsimp only at h
            cases hl : quotientLeaf lhs with
            | some leaf =>
                rw [hl] at h
                dsimp only at h
                obtain ⟨s1, h1, h2⟩ := peel_bind h
                have hp1 := IH.expr s rhs s1 h1
                obtain ⟨res, h3, h4⟩ := peel_bind h2
                rcases res with ⟨hit, s2⟩
                cases hit with
                | true =>
                    dsimp only at h4
                    have hs : s2 = s' := Except.ok.inj h4
                    subst hs
                    exact AppendTo_trans hp1 (emitAccLeaf_append s1 leaf constU8Op constOp memU16Op
                      (true, s2) h3)
                | false =>
                    dsimp only at h4
                    obtain ⟨s3, h5, h6⟩ := peel_bind h4
                    exact AppendTo_trans hp1 (AppendTo_trans
                      (emitAccLeaf_append s1 leaf constU8Op constOp memU16Op (false, s2) h3)
                      (AppendTo_trans (IH.expr s2 lhs s3 h5) (opBinary_append s3 stackOp s' h6)))
            | none =>
                rw [hl] at h
                dsimp only at h
                obtain ⟨s1, h1, h2⟩ := peel_bind h
                obtain ⟨s2, h3, h4⟩ := peel_bind h2
                exact AppendTo_trans (IH.expr s lhs s1 h1) (AppendTo_trans (IH.expr s1 rhs s2 h3)
                  (opBinary_append s2 stackOp s' h4))
      · intro s base product p h
        simp only [tryEmitAddProduct] at h
        cases hc : collectProductLeaves product with
        | none => rw [hc] at h; cases h; exact ⟨[], by simp⟩
        | some leaves =>
            rw [hc] at h
            dsimp only at h
            cases hm : productAddMacro s leaves with
            | none => rw [hm] at h; cases h; exact ⟨[], by simp⟩
            | some fused =>
                rw [hm] at h
                dsimp only at h
                obtain ⟨s1, h1, h2⟩ := peel_bind h
                have hp1 := IH.expr s base s1 h1
                cases hf : productAddFitsU8Slot s1 fused with
                | true =>
                    rw [hf] at h2
                    obtain ⟨s2, h3, h4⟩ := peel_bind h2
                    cases h4
                    exact AppendTo_trans hp1 (emitProductAdd_append s1 fused s2 h3)
                | false =>
                    rw [hf] at h2
                    obtain ⟨s2, h3, h4⟩ := peel_bind h2
                    cases hb : opBinary s2 qOpAdd with
                    | error e => rw [hb] at h4; cases h4
                    | ok s3 =>
                        rw [hb] at h4
                        cases h4
                        exact AppendTo_trans hp1 (AppendTo_trans (IH.expr s1 product s2 h3)
                          (opBinary_append s2 qOpAdd s3 hb))
      · intro s expr p h
        simp only [tryEmitLimbDecomposition] at h
        by_cases hv : (!s.limbVmOps) = true
        · rw [if_pos hv] at h; cases h; exact ⟨[], by simp⟩
        · rw [if_neg hv] at h
          cases hs : r.limbSubshape expr with
          | none => rw [hs] at h; cases h; exact ⟨[], by simp⟩
          | some t =>
              obtain ⟨shape, residue, matched⟩ := t
              rw [hs] at h
              dsimp only at h
              by_cases hc : (!limbShapeHasU8ConstSlots s shape) = true
              · rw [if_pos hc] at h; cases h; exact ⟨[], by simp⟩
              · rw [if_neg hc] at h
                obtain ⟨s1, h1, h2⟩ := peel_bind h
                have hp1 := IH.expr s residue s1 h1
                by_cases hc2 : (limbShapeHasU8ConstSlots s1 shape) = true
                · rw [if_pos hc2] at h2
                  obtain ⟨s2, h3, h4⟩ := peel_bind h2
                  obtain ⟨s3, h5, h6⟩ := peel_bind h4
                  cases h6
                  exact AppendTo_trans hp1 (AppendTo_trans (emitLimbShape_append s1 shape s2 h3)
                    (opBinary_append s2 qOpAdd s3 h5))
                · rw [if_neg hc2] at h2
                  obtain ⟨s2, h3, h4⟩ := peel_bind h2
                  obtain ⟨s3, h5, h6⟩ := peel_bind h4
                  cases h6
                  exact AppendTo_trans hp1 (AppendTo_trans (IH.affine s1 matched s2 h3)
                    (opBinary_append s2 qOpAdd s3 h5))
      · intro s terms s' h
        unfold emitAffineTerms at h
        cases terms with
        | nil => cases h; exact ⟨[], by simp⟩
        | cons term rest =>
            obtain ⟨s1, h1, h2⟩ := peel_bind h
            exact AppendTo_trans (IH.expr s term s1 h1) (IH.affineRest s1 rest s' h2)
      · intro s terms s' h
        unfold emitAffineTermsRest at h
        cases terms with
        | nil => cases h; exact ⟨[], by simp⟩
        | cons term rest =>
            obtain ⟨s1, h1, h2⟩ := peel_bind h
            obtain ⟨s2, h3, h4⟩ := peel_bind h2
            exact AppendTo_trans (IH.expr s term s1 h1) (AppendTo_trans
              (opBinary_append s1 qOpAdd s2 h3) (IH.affineRest s2 rest s' h4))
      · intro s e p h
        simp only [tryEmitPow5] at h
        cases hp : r.pow5Base e with
        | none => rw [hp] at h; cases h; exact ⟨[], by simp⟩
        | some base =>
            rw [hp] at h
            obtain ⟨s1, h1, h2⟩ := peel_bind h
            cases h2
            exact AppendTo_trans (IH.expr s base s1 h1) (pushByte_append s1 qOpPow5)



theorem emitU24_bytes (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU24 s v = .ok s') : ∃ a b c, s'.bytes = s.bytes ++ [a, b, c] := by
  unfold emitU24 at h
  split at h
  · cases h
  · cases h
    exact ⟨_, _, _, rfl⟩

theorem foldIdentity_suffix (s : QuotientProgramBuilder) (t : QuotientTarget)
    (gap : Option Nat) (s' : QuotientProgramBuilder) (h : foldIdentity s t gap = .ok s') :
    (t = .main ∧ s'.bytes = s.bytes ++ [qOpFoldMain]) ∨
    (∃ (idx : Nat) (g b1 b2 b3 : Nat), t = .selector idx ∧ gap = some g ∧
      s'.bytes = s.bytes ++ [qOpFoldSelector, b1, b2, b3]) := by
  unfold foldIdentity at h
  cases t with
  | main =>
      dsimp only at h
      have hb : s'.bytes = (op0 s qOpFoldMain).bytes :=
        popStackAcct_bytes (op0 s qOpFoldMain) s' h
      left
      refine ⟨rfl, ?_⟩
      rw [hb]
      simp [op0]
  | selector idx =>
      dsimp only at h
      cases hg : gap with
      | none => rw [hg] at h; cases h
      | some g =>
          rw [hg] at h
          dsimp only at h
          simp only [bind, Except.bind] at h
          by_cases hi : idx > 255
          · rw [if_pos hi] at h; cases h
          · rw [if_neg hi] at h
            by_cases hgap : g > 0xffff
            · rw [if_pos hgap] at h; cases h
            · rw [if_neg hgap] at h
              obtain ⟨a1, h1, h2⟩ := peel_bind h
              obtain ⟨b1, b2, b3, hb⟩ := emitU24_bytes (pushByte s qOpFoldSelector)
                ((idx * 65536) ||| g) a1 h1
              have h2' : s'.bytes = a1.bytes := popStackAcct_bytes a1 s' h2
              right
              refine ⟨idx, g, b1, b2, b3, rfl, rfl, ?_⟩
              rw [h2', hb]
              simp [pushByte, appendBytes, List.append_assoc]

theorem finalizedIdentitySegment_some_of_append_main (a : List Nat) :
    ∃ body, finalizedIdentitySegment QuotientTarget.main (a ++ [qOpFoldMain]) = some body := by
  refine ⟨a, ?_⟩
  unfold finalizedIdentitySegment
  dsimp only
  have hne : (a ++ [qOpFoldMain]).length ≠ 0 := by simp
  rw [if_neg (by simpa using hne)]
  have hlast : ((a ++ [qOpFoldMain]).getD ((a ++ [qOpFoldMain]).length - 1) 0 == qOpFoldMain) = true := by
    simp [List.length_append]
  rw [if_pos hlast]
  simp

theorem finalizedIdentitySegment_some_of_append_selector (idx : Nat) (a : List Nat)
    (b1 b2 b3 : Nat) :
    ∃ body, finalizedIdentitySegment (QuotientTarget.selector idx)
      (a ++ [qOpFoldSelector, b1, b2, b3]) = some body := by
  refine ⟨a, ?_⟩
  unfold finalizedIdentitySegment
  dsimp only
  have hsel : (decide (4 ≤ (a ++ [qOpFoldSelector, b1, b2, b3]).length) &&
      ((a ++ [qOpFoldSelector, b1, b2, b3]).getD
        ((a ++ [qOpFoldSelector, b1, b2, b3]).length - 4) 0 == qOpFoldSelector)) = true := by
    simp [List.length_append]
  rw [if_pos hsel]
  simp

/-- The trailing fold shape a target requires of the emitted bytes. -/
def FoldSuffix (t : QuotientTarget) (extra : List Nat) : Prop :=
  match t with
  | .main => ∃ pre, extra = pre ++ [qOpFoldMain]
  | .selector _ => ∃ pre b1 b2 b3, extra = pre ++ [qOpFoldSelector, b1, b2, b3]

theorem emitExprTop_append (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (e : QuotientExpr) (s' : QuotientProgramBuilder) (h : emitExprTop r s e = .ok s') :
    AppendTo s s' :=
  (emitAppend_all r (emitFuel e)).expr s e s' h

theorem identityExpr_suffix (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (e : QuotientExpr) (t : QuotientTarget) (gap : Option Nat) (s' : QuotientProgramBuilder)
    (h : identityExpr r s e t gap = .ok s') :
    ∃ extra, s'.bytes = s.bytes ++ extra ∧ FoldSuffix t extra := by
  unfold identityExpr at h
  dsimp only at h
  obtain ⟨s1, h1, h2⟩ := peel_bind h
  obtain ⟨s2, h3, h4⟩ := peel_bind h2
  have ha := emitExprTop_append r { s with vars := [], stackDepth := 0 } e s1 h1
  obtain ⟨e1, he1⟩ := ha
  have he1' : s1.bytes = s.bytes ++ e1 := by simpa using he1
  have hs' : s' = s2 := by
    by_cases hd : s2.stackDepth != 0
    · simp [hd] at h4; cases h4
    · simp [hd] at h4
      exact h4.symm
  rcases foldIdentity_suffix s1 t gap s2 h3 with hsuf | hsuf
  · obtain ⟨ht, hb⟩ := hsuf
    subst ht
    have hs2 : s2.bytes = s1.bytes ++ [qOpFoldMain] := hb
    refine ⟨e1 ++ [qOpFoldMain], ?_, ?_⟩
    · rw [hs', hs2, he1']; simp [List.append_assoc]
    · exact ⟨e1, rfl⟩
  · obtain ⟨idx, g, b1, b2, b3, ht, hg, hb⟩ := hsuf
    subst ht
    have hs2 : s2.bytes = s1.bytes ++ [qOpFoldSelector, b1, b2, b3] := hb
    refine ⟨e1 ++ [qOpFoldSelector, b1, b2, b3], ?_, ?_⟩
    · rw [hs', hs2, he1']; simp [List.append_assoc]
    · exact ⟨e1, b1, b2, b3, rfl⟩

theorem PG_identity_preFold_proof : Midfall.Lowering.PG_identity_preFold := by
  intro r s0 s1 e t gap h
  obtain ⟨extra, hextra, hsuf⟩ := identityExpr_suffix r s0 e t gap s1 h
  have hdrop : s1.bytes.drop s0.bytes.length = extra := by
    rw [hextra]; simp
  rw [hdrop]
  cases t with
  | main =>
      obtain ⟨pre, rfl⟩ := hsuf
      exact finalizedIdentitySegment_some_of_append_main pre
  | selector idx =>
      obtain ⟨pre, b1, b2, b3, rfl⟩ := hsuf
      exact finalizedIdentitySegment_some_of_append_selector idx pre b1 b2 b3

/-- **THE CORRECTED ROW REDUCED TO TWO FACTS.** With D-GATE3's target-aware helper,
    `qvm_compile_correct_identity` follows from `PG_identity_emitterValue` and
    `PG_identity_compactionValue` alone: the third IDVALUE fact (`PG_identity_preFold`) is
    PROVED above. This is the exact remaining goal state of the registered row. -/
theorem qvm_compile_correct_identity_of_two_parts
    (hemit : Midfall.Lowering.PG_identity_emitterValue)
    (hcomp : Midfall.Lowering.PG_identity_compactionValue)
    (r : QuotientShapeRecognizers) (hr : RecognizersSound r)
    (s₀ s₁ : QuotientProgramBuilder) (e : QuotientExpr) (t : QuotientTarget) (gap : Option Nat)
    (hb : exprBounded e)
    (hidentity : identityExpr r s₀ e t gap = .ok s₁)
    (hconsts : ∀ c ∈ s₁.consts, c.toNat < qvmFrModulus)
    (cseg seg : List Nat)
    (hcompact : compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg)
    (hseg : finalizedIdentitySegment t cseg = some seg)
    (ρ : Valuation) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity seg s₁.consts (memOfρ ρ (leafKeys e)) =
      .ok (v, mem') ∧ evalExprρ ρ e = .ok v :=
  Midfall.Lowering.qvm_compile_correct_identity_of_parts hemit hcomp PG_identity_preFold_proof
    r hr s₀ s₁ e t gap hb hidentity hconsts cseg seg hcompact hseg ρ

#print axioms Midfall.Lowering.QvmEmit.qvm_compile_correct_identity_of_two_parts

end Midfall.Lowering.QvmEmit


/-! ### 5. `PG_termFold_structure` DISCHARGED: the LIN7 term fold writes `termBlock`

    The builder half of the LIN7 denotation tie (`QvmEmit` section 3) is now a theorem. The
    invariant `ConstTableSound` is preserved by `constSlot`, the fresh arm grows the table by the
    quoted coefficient, and `termFold` writes exactly `termBlock slots terms` - one
    (slot byte, big-endian u16 pointer) triple per term - with every slot a u8 and every slot
    indexing its own coefficient. `termFold_structure` carries `ConstTableSound` and the consts
    prefix through the fold; `PG_termFold_structure_proof` is the named Prop's proof.

    NO hypothesis on a row/bundle/root; no sorry; standard three axioms. -/

namespace Midfall.Lowering.QvmEmit

open Midfall
open Midfall.Generator
open Midfall.Generator.QuotientBuilder

theorem constSlot_found_structure {s : QuotientProgramBuilder} {c : Word256}
    {s' : QuotientProgramBuilder} {slot : Nat} (hcs : ConstTableSound s)
    (h : constSlot s c = .ok (s', slot)) (hsome : constSlotOf s c = some slot) :
    s' = s ∧ ∃ rest, s.consts.drop slot = c :: rest := by
  unfold constSlot at h
  rw [hsome] at h
  obtain ⟨rfl, rfl⟩ := Except.ok.inj h
  exact ⟨rfl, hcs c slot hsome⟩

theorem constSlotOf_grow (s : QuotientProgramBuilder) (c c0 : Word256) (slot : Nat) :
    constSlotOf { s with consts := s.consts ++ [c], constSlots := s.constSlots ++ [(c, slot)] } c0
      = (match constSlotOf s c0 with
         | some x => some x
         | none => if c == c0 then some slot else none) := by
  unfold constSlotOf
  rw [List.find?_append]
  cases hf : List.find? (fun k : Word256 × Nat => k.1 == c0) s.constSlots with
  | some x =>
      simp only [hf, Option.or, Option.map]
  | none =>
      simp only [hf, Option.none_or, Option.map]
      cases hc : (c == c0) with
      | true =>
          rw [List.find?_cons]
          simp only [Prod.fst, hc, if_true]
      | false =>
          rw [List.find?_cons]
          simp only [Prod.fst, hc, if_false, Bool.false_eq_true, List.find?]

theorem constSlot_preserves_sound {s : QuotientProgramBuilder} {c : Word256}
    {s' : QuotientProgramBuilder} {slot : Nat} (hcs : ConstTableSound s)
    (h : constSlot s c = .ok (s', slot)) : ConstTableSound s' := by
  unfold constSlot at h
  cases hsome : constSlotOf s c with
  | some found =>
      rw [hsome] at h
      obtain ⟨rfl, rfl⟩ := Except.ok.inj h
      exact hcs
  | none =>
      rw [hsome] at h
      dsimp only at h
      by_cases hmax : s.consts.length > 0xffff
      · rw [if_pos hmax] at h; cases h
      · rw [if_neg hmax] at h
        obtain ⟨rfl, rfl⟩ := Except.ok.inj h
        intro c0 slot0 h0
        rw [constSlotOf_grow] at h0
        cases hf : constSlotOf s c0 with
        | some x =>
            rw [hf] at h0
            simp only [Option.some.injEq] at h0
            subst h0
            have hd := hcs c0 x hf
            obtain ⟨rest, hrest⟩ := hd
            refine ⟨rest ++ [c], ?_⟩
            have hlen : x < s.consts.length := by
              by_contra hlt
              have hnil : s.consts.drop x = [] := List.drop_eq_nil_of_le (by omega)
              rw [hnil] at hrest
              cases hrest
            rw [List.drop_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlen), List.drop_zero, hrest]
            rfl
        | none =>
            rw [hf] at h0
            simp only [Option.none_or, Option.map] at h0
            by_cases hc : (c == c0) = true
            · have hc' : c = c0 := by simpa using hc
              subst hc'
              rw [if_pos hc] at h0
              simp only [Option.some.injEq] at h0
              subst h0
              exact ⟨[], by simp⟩
            · rw [if_neg hc] at h0
              cases h0



theorem emitU16_bytes (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU16 s v = .ok s') : s'.bytes = s.bytes ++ [v / 256, v % 256] := by
  unfold emitU16 at h
  split at h
  · cases h
  · cases h
    rfl

theorem constSlot_consts_grow (s : QuotientProgramBuilder) (c : Word256)
    (s' : QuotientProgramBuilder) (slot : Nat) (h : constSlot s c = .ok (s', slot)) :
    ∃ extra, s'.consts = s.consts ++ extra := by
  unfold constSlot at h
  cases hf : constSlotOf s c with
  | some found => rw [hf] at h; obtain ⟨rfl, rfl⟩ := Except.ok.inj h; exact ⟨[], by simp⟩
  | none =>
      rw [hf] at h
      dsimp only at h
      by_cases hmax : s.consts.length > 0xffff
      · rw [if_pos hmax] at h; cases h
      · rw [if_neg hmax] at h
        obtain ⟨rfl, rfl⟩ := Except.ok.inj h
        exact ⟨[c], rfl⟩

theorem termStep_structure (s : QuotientProgramBuilder) (cp : Word256 × Nat) (site : String)
    (s' : QuotientProgramBuilder) (hcs : ConstTableSound s) (hptr : cp.2 ≤ 0xffff)
    (h : termStep s cp site = .ok s') :
    ∃ slot cextra, slot ≤ 255 ∧ s'.bytes = s.bytes ++ [slot, cp.2 / 256, cp.2 % 256] ∧
      ConstTableSound s' ∧ (∃ rest, s'.consts.drop slot = cp.1 :: rest) ∧
      s'.consts = s.consts ++ cextra := by
  unfold termStep at h
  obtain ⟨coeff, ptr⟩ := cp
  obtain ⟨a, h1, h2⟩ := peel_bind h
  rcases a with ⟨s1, slot⟩
  dsimp only at h2
  have hsnd := constSlot_preserves_sound hcs h1
  have hdrop0 : ∃ rest, s1.consts.drop slot = coeff :: rest := by
    unfold constSlot at h1
    cases hf : constSlotOf s coeff with
    | some _ => rw [hf] at h1; obtain ⟨rfl, rfl⟩ := Except.ok.inj h1; exact hcs coeff slot hf
    | none =>
        rw [hf] at h1
        dsimp only at h1
        by_cases hmax : s.consts.length > 0xffff
        · rw [if_pos hmax] at h1; cases h1
        · rw [if_neg hmax] at h1
          obtain ⟨rfl, rfl⟩ := Except.ok.inj h1
          exact ⟨[], by simp⟩
  obtain ⟨cextra1, hconsts1⟩ := constSlot_consts_grow s coeff s1 slot h1
  by_cases hslot : slot > 255
  · rw [if_pos hslot] at h2; cases h2
  · rw [if_neg hslot] at h2
    obtain ⟨a2, h3, h4⟩ := peel_bind h2
    have hb : a2.bytes = (pushByte s1 slot).bytes ++ [ptr / 256, ptr % 256] :=
      emitU16_bytes (pushByte s1 slot) ptr a2 h3
    have ha2 : a2 = s' := Except.ok.inj h4
    rw [ha2] at h3 hb
    have hcbytes : s'.consts = s1.consts := by
      unfold emitU16 at h3
      split at h3
      · cases h3
      · cases h3; rfl
    have hcslots : s'.constSlots = s1.constSlots := by
      unfold emitU16 at h3
      split at h3
      · cases h3
      · cases h3; rfl
    have hsnd' : ConstTableSound s' := by
      intro c sl h0
      have h0' : constSlotOf s1 c = some sl := by
        unfold constSlotOf at h0 ⊢
        simpa [hcslots] using h0
      have hd := hsnd c sl h0'
      simpa [hcbytes] using hd
    have hdrop0' : ∃ rest, s'.consts.drop slot = coeff :: rest := by
      obtain ⟨rest, hr⟩ := hdrop0
      exact ⟨rest, by simpa [hcbytes] using hr⟩
    refine ⟨slot, cextra1, by omega, ?_, hsnd', hdrop0', ?_⟩
    · have hb1 : s1.bytes = s.bytes := Midfall.Lowering.QvmEmit.constSlot_bytes s coeff s1 slot h1
      rw [hb]
      simp [pushByte, appendBytes, hb1, List.append_assoc]
    · have hconsts' : s'.consts = (pushByte s1 slot).consts := by
        unfold emitU16 at h3
        split at h3
        · cases h3
        · cases h3; rfl
      rw [hconsts']
      simpa [pushByte, appendBytes] using hconsts1

theorem termFold_structure (s : QuotientProgramBuilder) (terms : List (Word256 × Nat)) (site : String)
    (s' : QuotientProgramBuilder) (hcs : ConstTableSound s)
    (hptr : ∀ p ∈ terms.map Prod.snd, p ≤ 0xffff)
    (h : termFold s terms site = .ok s') :
    ∃ slots, slots.length = terms.length ∧
      s'.bytes = s.bytes ++ termBlock slots terms ∧
      (∀ i slot, i < terms.length → slots.getD i 0 = slot → slot ≤ 255) ∧
      (∀ i t slot, i < terms.length → terms.getD i (0, 0) = t →
        slots.getD i 0 = slot → ∃ rest, s'.consts.drop slot = t.1 :: rest) ∧
      ConstTableSound s' ∧ ∃ cextra, s'.consts = s.consts ++ cextra := by
  unfold termFold at h
  induction terms generalizing s with
  | nil =>
      simp [foldLeftM] at h
      cases h
      refine ⟨[], by simp [termBlock], by simp [termBlock], by simp, by simp, hcs, ⟨[], by simp⟩⟩
  | cons cp rest ih =>
      simp only [foldLeftM] at h
      obtain ⟨a, h1, h2⟩ := peel_bind h
      have h1' : termStep s cp site = .ok a := h1
      have hptr0 : cp.2 ≤ 0xffff := by
        have := hptr cp.2 (by simp)
        simpa using this
      obtain ⟨slot, cextra1, hslot, hbytes, hcs1, hdrop0, hconsts1⟩ :=
        termStep_structure s cp site a hcs hptr0 h1'
      have hptr' : ∀ p ∈ rest.map Prod.snd, p ≤ 0xffff := by
        intro p hp; exact hptr p (by simp [hp])
      obtain ⟨slots, hlen, hbytes', hslots, hconsts, hcs', cextra2, hconsts2⟩ :=
        ih a hcs1 hptr' h2
      refine ⟨slot :: slots, by simp [hlen], ?_, ?_, ?_, hcs', ?_⟩
      · rw [hbytes', hbytes]
        obtain ⟨coeff, ptr⟩ := cp
        simp only [termBlock]
        simp [List.append_assoc]
      · intro i s0 hi hget
        cases i with
        | zero =>
            simp only [List.getD_cons_zero] at hget
            subst hget
            exact hslot
        | succ j => simp only [List.getD_cons_succ] at hget; exact hslots j s0 (by simpa using hi) hget
      · intro i t s0 hi ht hget
        cases i with
        | zero =>
            simp only [List.getD_cons_zero] at ht hget
            subst ht; subst hget
            obtain ⟨restc, hrc⟩ := hdrop0
            have hlen0 : slot < a.consts.length := by
              by_contra hlt
              have hnil : a.consts.drop slot = [] := List.drop_eq_nil_of_le (by omega)
              rw [hnil] at hrc; cases hrc
            refine ⟨restc ++ cextra2, ?_⟩
            rw [hconsts2, List.drop_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlen0), List.drop_zero, hrc]
            rfl
        | succ j =>
            simp only [List.getD_cons_succ] at ht hget
            exact hconsts j t s0 (by simpa using hi) ht hget
      · rw [hconsts2, hconsts1]
        exact ⟨cextra1 ++ cextra2, by simp [List.append_assoc]⟩

theorem PG_termFold_structure_proof : Midfall.Lowering.QvmEmit.PG_termFold_structure := by
  intro terms s s' site hcs h hptr
  obtain ⟨slots, hlen, hbytes, hslots, hconsts, _⟩ :=
    termFold_structure s terms site s' hcs hptr h
  exact ⟨slots, hlen, hbytes, hslots, hconsts⟩

#print axioms Midfall.Lowering.QvmEmit.PG_termFold_structure_proof

/-! #### The ROW builder half -/

theorem emitU16_consts (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU16 s v = .ok s') : s'.consts = s.consts := by
  unfold emitU16 at h
  split at h
  · cases h
  · cases h; rfl

theorem emitU16_constSlots (s : QuotientProgramBuilder) (v : Nat) (s' : QuotientProgramBuilder)
    (h : emitU16 s v = .ok s') : s'.constSlots = s.constSlots := by
  unfold emitU16 at h
  split at h
  · cases h
  · cases h; rfl

theorem emitLimbRow_bytes (s : QuotientProgramBuilder) (lhs : Nat)
    (terms : List (Word256 × Nat)) (s' : QuotientProgramBuilder)
    (hcs : ConstTableSound s) (hlhs : lhs ≤ 0xffff)
    (htermptr : ∀ p ∈ terms.map Prod.snd, p ≤ 0xffff)
    (h : emitLimbShape s (.bilin7Row lhs terms) = .ok s') :
    ∃ slots, slots.length = terms.length ∧
      s'.bytes = s.bytes ++ [qOpBilin7Row, lhs / 256, lhs % 256] ++ termBlock slots terms ∧
      (∀ i slot, i < terms.length → slots.getD i 0 = slot → slot ≤ 255) ∧
      (∀ i t slot, i < terms.length → terms.getD i (0, 0) = t →
        slots.getD i 0 = slot → ∃ rest, s'.consts.drop slot = t.1 :: rest) := by
  unfold emitLimbShape at h
  obtain ⟨a1, h1, h2⟩ := peel_bind h
  obtain ⟨a2, h3, h4⟩ := peel_bind h1
  have hs' : s' = pushStackAcct a1 := (Except.ok.inj h2).symm
  have hcsl : a2.constSlots = s.constSlots := by
    rw [emitU16_constSlots (pushByte s qOpBilin7Row) lhs a2 h3]; rfl
  have hcst : a2.consts = s.consts := by
    rw [emitU16_consts (pushByte s qOpBilin7Row) lhs a2 h3]; rfl
  have hcs2 : ConstTableSound a2 := by
    intro c sl h0
    have h0' : constSlotOf s c = some sl := by
      unfold constSlotOf at h0 ⊢
      rw [hcsl] at h0
      exact h0
    obtain ⟨rest, hrest⟩ := hcs c sl h0'
    exact ⟨rest, by rw [hcst]; exact hrest⟩
  obtain ⟨slots, hlen, hbytes, hslots, hconsts, _⟩ :=
    termFold_structure a2 terms siteBilin7RowSlot a1 hcs2 htermptr h4
  refine ⟨slots, hlen, ?_, hslots, ?_⟩
  · rw [hs']
    change a1.bytes = s.bytes ++ [qOpBilin7Row, lhs / 256, lhs % 256] ++ termBlock slots terms
    rw [hbytes]
    have hb2 : a2.bytes = (pushByte s qOpBilin7Row).bytes ++ [lhs / 256, lhs % 256] :=
      emitU16_bytes (pushByte s qOpBilin7Row) lhs a2 h3
    rw [hb2]
    simp only [pushStackAcct, pushByte, appendBytes]
    simp [List.append_assoc]
  · intro i t sl hi ht hs
    have hcons : s'.consts = a1.consts := by rw [hs']; rfl
    obtain ⟨rest, hrest⟩ := hconsts i t sl hi ht hs
    exact ⟨rest, by rw [hcons]; exact hrest⟩

end Midfall.Lowering.QvmEmit

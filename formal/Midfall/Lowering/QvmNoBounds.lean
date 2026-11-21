-- |
-- Midfall.Lowering.QvmNoBounds
--
-- Card RELOC - THE ROW MOVED DOWNSTREAM. This file exists because of the structural finding the
-- SLOT2 commit (3b7eab6) named: 'qvm_validated_noBoundsFault' lived at 'Qvm.lean:751', but all THREE
-- per-arm families it has to be proved from - the read bound, the width agreement and the const-slot
-- correspondence - live in 'QvmShift.lean' and 'QvmWalk.lean', which IMPORT 'Qvm.lean'. Nothing
-- imported 'QvmShift'. So the row sat UPSTREAM of every fact that could discharge it and could not be
-- closed in place however many arms were landed: a fourth per-arm family would have arrived on the far
-- side of the same edge. This card writes no new per-arm fact. It fixes the direction.
--
-- THE PATTERN, COPIED AND NOT INVENTED. 'Midfall/Lowering/QuotientInterp.lean' already solves this
-- shape: 'QInterpRefines' is a sorry-free 'def : Prop' in the module that OWNS the vocabulary, and the
-- ROW that proves it is stated separately, where the dependencies are visible. So here: the obligation
-- is now the sorry-free 'def QvmNoBoundsFault : QVMFault -> Prop' in 'Qvm.lean' section 6 - DECLARED
-- EXACTLY ONCE, upstream, where 'Obligations.lean', 'QuotientRows.lean' and the register can all see
-- it - and the theorem below is the PROOF SITE, in the first module in the tree that imports
-- 'QvmShift'.
--
-- WHAT DID NOT CHANGE, and the gate that says so. Same name
-- ('Midfall.Lowering.qvm_validated_noBoundsFault'), same binders, same hypotheses in the same order,
-- and a conclusion that is the committed conjunction by 'Iff.rfl':
-- 'Midfall.Lowering.qvmNoBoundsFault_conj' in 'Qvm.lean' is the PROVED pin that the def unfolds to
-- exactly '(∀ i, f ≠ QVMFault.readPastEnd i) ∧ (∀ slot idx, f ≠ QVMFault.constSlotOutOfRange slot idx)'.
-- Nothing was weakened and nothing was added: no hypothesis joined the row, the bundle, 'ValidV3' or the
-- root, and 'hbound' stays where SLOT2 put it - on an ARM LEMMA, never here.
--
-- THE ROW IS STILL OPEN, AND THIS CARD DOES NOT CLOSE IT. Relocating it makes closing it POSSIBLE; it
-- does not do the closing. The four legs, stated from here:
--   (i)   'evalQuotientIdentityStep_noSlotFault_25' (SLOT2) - LANDED, 25 of 26 arms, and now IN SCOPE.
--   (ii)  the const-slot membership pass (CSLOT, 'evalQuotientIdentityStep_constSlot_namedByWalker_25')
--         - LANDED, 25 of 26, in scope.
--   (iii) the read-bound and width families (SHIF2, 'evalQuotientIdentityStep_readsWithinStride_at_22'
--         and 'evalQuotientIdentityStep_consumed_agrees_at_22', plus QvmWalk's three dynamic arms)
--         - LANDED, 25 of 26, in scope.
--   (iv)  THE LOOP INDUCTION over the fuel-bounded segment - LANDED HERE, PROVED, as
--         'qvmNoBounds_stepErrorIsReachable'. SLOT2 named it as an independent remaining item and it
--         is: the proof cites NO per-arm fact, only 'IdentityStep.hConsumed'.
-- SO WHAT DOES STILL BLOCK THE ROW? Three things now, and VALP2 is what turned two into three:
--   (A) THE VALIDATOR-SIDE WHOLE-TO-PART STEP - AND VALP2 MEASURED IT: IT IS FALSE AS STATED.
--       'hvalidated' unfolds, through 'supportedQvmBool' and 'operands_ok_of_validated'
--       (Qvm.lean:840, PROVED), to 'checkQuotientOperand' passing on every operand of every instruction
--       of the WHOLE PROGRAM BYTES. The natural transfer - "so it passes at cursor 'cursor + j' of the
--       SEGMENT '(bytes.drop cursor).take (exprEnd - cursor)'" - is REFUTED, not proved: phase 1 walks
--       from offset 0 and phase 2 checks the instructions THAT walk names, so 'supportedQvm' says
--       nothing about a buffer cut at an arbitrary cursor. The counterexample is
--       'valp2_heredityFails_measure' and its reducing conjuncts in 'VmValidator.lean' (a validating
--       4-byte program, a cursor in the middle of its first instruction, a segment that decodes
--       PUSH_CONST_U8 0x80 against a 100-entry constant table). What the segment needs is not an
--       induction but an ALIGNMENT hypothesis, named as 'PG_valp2_walkAlignment' with the whole-to-part
--       lemma 'operands_ok_of_validated_segment' PROVED from it (offset 'cursor + i', and
--       'checkQuotientOperand_ok_index' shows the offset carries no constraint either way). The bridge
--       from 'itemStarts q.plan q.build' to the offsets of 'quotientBytecodeOps' is a VmCertify /
--       VmBuilder fact and is NOT in this tree yet: so (A) splits into (A1) the walk-alignment bridge
--       and (A2) the two drop/take congruence legs inside 'PG_valp2_walkAlignment'.
--   (B) MODARITH7, absent from (i)-(iii) - QvmShift names it in
--       'PG_stepNoRF_validated_slot2_modarith7_oor', '..._shif2_modarith7_read' and
--       '..._shif2_modarith7_width'.
-- Given (A) and (B), 'qvm_validated_noBoundsFault_of_stepErrorIsReachable' (PROVED below) closes the
-- row by a case split over the segment's cursors and nothing else. VALP2 corrects the RELOC reading of
-- (A): it is not an induction that is owed, it is a hypothesis the row does not have.
--
-- NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES); no statement
-- names a fixture (D-P71); no 'native_decide'. The file carries exactly one sorry and it is the row
-- that moved; the non-vacuity gates for both excluded fault classes (Qvm.lean GATE 13 and GATE 14)
-- stayed upstream with the def, where they still apply to it.
import Midfall.Lowering.Qvm
import Midfall.Lowering.QvmShift
import Midfall.Lowering.QvmWalk

set_option autoImplicit false

namespace Midfall.Lowering

open Midfall
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientRefMemory QuotientProgramPlan
  QuotientProgramBuild qvmFrModulus qvmBytesToNats)
open Midfall.Generator.QuotientCertify
open Midfall.Generator.QuotientValidator

/-! ### The row, downstream of every family it has to be proved from -/

/-- **THE NO-BOUNDS-FAULT ROW, RELOCATED DOWNSTREAM (card RELOC).** The statement is the one committed
    at 'Qvm.lean:751' since P-QVM restored it to the sketch's strength (docs/REVIEW.md R-69): the same
    binders, the same hypotheses in the same order, and the conclusion 'QvmNoBoundsFault f', which is
    that committed conjunction by 'Iff.rfl' (the pin is 'qvmNoBoundsFault_conj', next to the def in
    'Qvm.lean'). It moved because the three per-arm families it needs live in modules that import
    'Qvm.lean', so no proof of it could be written where it stood; the PROOF HOLE and its history are in
    the doc comment that stayed with the def.

    STILL OPEN, and what stands between this row and a proof, named rather than glossed - VALP2
    corrected this list from two items to three. (A1) NOTHING IN THE TREE BRIDGES 'itemStarts q.plan
    q.build' TO THE OFFSETS OF 'quotientBytecodeOps', and without that bridge the whole-to-part step is
    FALSE: see 'PG_valp2_naturalWholeToPart' (stated, refuted) and 'valp2_heredityFails_measure' in
    'VmValidator.lean'. (A2) The two legs of 'PG_valp2_walkAlignment' - the walk-shift and the
    operand-read congruence for a drop-take segment - are inductions over 'quotientBytecodeOpsGo', whose
    reader ingredients ('byteAtPanic_drop' and twins) are PROVED. (B) MODARITH7 on legs (i)-(iii), named
    in QvmShift's three 'PG_stepNoRF_validated_*_modarith7_*' Props. Leg (iv), the loop inversion, is
    PROVED below. No hypothesis was added to THIS row: (A1) and (A2) are lemmas about the segment, stated
    where they belong, and the row's binders are untouched. -/
theorem qvm_validated_noBoundsFault {Program Layout : Type}
    (model : QuotientOperandModel)
    (L : Midfall.Generator.LoweringPlan Program Layout)
    (hvm : L.lowering = Midfall.Generator.QuotientLowering.vm)
    (q : Midfall.Generator.PlannedQuotient) (hq : L.quotient = some q)
    (hmodel : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
      q.build q.plan.selectorFold = .ok model)
    (hvalidated : Midfall.Generator.LoweringPlan.supportedQvm L)
    (hconsts : ∀ c ∈ q.build.consts, c.toNat < qvmFrModulus)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts q.plan q.build)
    (hseg : identitySegment (qvmBytesToNats q.build.bytes) cursor = .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory) (f : QVMFault)
    (hf : Midfall.Generator.evalQuotientIdentity
        (((qvmBytesToNats q.build.bytes).drop cursor).take (exprEnd - cursor))
        q.build.consts mem = .error f) :
    QvmNoBoundsFault f := by
  sorry

/-! ### Leg (iv): the loop induction over the fuel-bounded segment -/

/-- **THE MISSING LEG, STATED.** Every per-arm family in the tree is about
    'evalQuotientIdentityStep' at ONE cursor, and the row is about 'evalQuotientIdentity' over a whole
    segment. What transports one to the other is an induction over the fuel-bounded walk
    ('evalQuotientIdentityLoop.go', VmReference.lean:875-892), and NOTHING IN THE TREE STATED IT as a
    fact about which fault a segment error can be: 'evalQuotientIdentityLoop_fuelNeverBinds'
    (Qvm.lean:1481) is the template and is PROVED, but it is a statement about the fuel arm being
    unreachable under a hypothesis that every step SUCCEEDS - the opposite of the row's case, where a
    step faults. This Prop is that missing shape, and 'qvmNoBounds_stepErrorIsReachable' PROVES it: a
    segment error either names a step that faults at a cursor inside the segment, or it is the final
    singleton-stack refusal, which is 'stackLengthMismatch' and is neither excluded class.

    KEPT AS A NAMED 'def : Prop' rather than inlined into the theorem, so the obligation has ONE address
    in the tree and the theorem that discharges it says which Prop it discharges - the
    'QInterpRefines' shape. It adds no hole to the register: it is a def, not a sorry. -/
def PG_qvmNoBounds_stepErrorIsReachable : Prop :=
  ∀ (bytes : List Nat) (consts : List Word256) (mem : QuotientRefMemory) (f : QVMFault),
    Midfall.Generator.evalQuotientIdentity bytes consts mem = .error f →
    (∃ (j : Nat) (stack : List QVMFr) (m : QuotientRefMemory),
        j < bytes.length ∧
        Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0) stack m
          = .error f) ∨
      ∃ n, f = QVMFault.stackLengthMismatch n

/-- **LEG (iv) AT THE STEP LEVEL. PROVED.** A fuel-bounded walk that ERRORS errored at a STEP, at a
    cursor inside the buffer, on the stack and memory the walk actually reached it with. This is the
    shape the per-arm families are stated about, and without it they could not be attached to the row
    at all: legs (i)-(iii) are per-cursor and the row is per-segment.

    WHY THE FUEL ARM CANNOT FIRE. 'bytes.length - j ≤ fuel' is the fuel-adequacy condition, and every
    successful step preserves it because 'IdentityStep.hConsumed' forces the cursor to advance by at
    least one: 'bytes.length - (j + s.consumed) ≤ bytes.length - (j + 1) ≤ fuel'. So the walk runs out
    of BUFFER before it runs out of FUEL, and the only errors 'go' can return are a step's. The proof
    is an induction on the fuel and cites NO per-arm fact - which is exactly why this leg was the
    cheapest of the four and the only one no card had been asked for. -/
theorem evalQuotientIdentityLoop_error_namesStep
    (bytes : List Nat) (consts : List Word256) :
    ∀ (fuel j : Nat) (stack : List QVMFr) (mem : QuotientRefMemory),
      bytes.length - j ≤ fuel →
      ∀ (f : QVMFault),
        Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel j stack mem = .error f →
        ∃ (k : Nat) (stk : List QVMFr) (m : QuotientRefMemory),
          k < bytes.length ∧
          Midfall.Generator.evalQuotientIdentityStep bytes consts k (bytes.getD k 0) stk m
            = .error f := by
  intro fuel
  induction fuel with
  | zero =>
      intro j stack mem hbound f h
      have hnot : ¬ (j < bytes.length) := by omega
      have hok : Midfall.Generator.evalQuotientIdentityLoop.go bytes consts 0 j stack mem
          = .ok (stack, mem) := by
        simp [Midfall.Generator.evalQuotientIdentityLoop.go, hnot]
      rw [hok] at h; exact absurd h (by simp)
  | succ k ih =>
      intro j stack mem hbound f h
      by_cases hlt : j < bytes.length
      · have hgo : Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (k + 1) j stack mem
            = (Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0) stack mem
                >>= fun s =>
              Midfall.Generator.evalQuotientIdentityLoop.go bytes consts k (j + s.consumed)
                s.stack s.mem) := by
          simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]
        rw [hgo] at h
        cases hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0)
            stack mem with
        | error e =>
            rw [hstep] at h
            simp only [bind, Except.bind] at h
            have he : e = f := Except.error.inj h
            exact ⟨j, stack, mem, hlt, by rwa [← he]⟩
        | ok s =>
            rw [hstep] at h
            simp only [bind, Except.bind] at h
            have hpos : 1 ≤ s.consumed := s.hConsumed
            refine ih (j + s.consumed) s.stack s.mem ?_ f h
            omega
      · have hok : Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (k + 1) j stack mem
            = .ok (stack, mem) := by
          simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]
        rw [hok] at h; exact absurd h (by simp)

/-- **LEG (iv), PROVED: the loop inversion the row was waiting for.** A segment that ERRORS either
    errors at a STEP inside the segment - the shape legs (i)-(iii) discharge, 25 of the 26 arms - or it
    errors with 'stackLengthMismatch', the caller's singleton refusal, which is neither excluded fault
    class. So the leg SLOT2 named as independent of every per-arm fact is now CLOSED, with no per-arm
    fact and no new hypothesis anywhere. The fuel is the program's own length and the walk starts at
    cursor 0, so the adequacy condition is free. -/
theorem qvmNoBounds_stepErrorIsReachable : PG_qvmNoBounds_stepErrorIsReachable := by
  intro bytes consts mem f hf
  unfold Midfall.Generator.evalQuotientIdentity at hf
  cases h : Midfall.Generator.evalQuotientIdentityLoop bytes consts 0 ([] : List QVMFr) mem with
  | error e =>
      simp only [h, bind, Except.bind] at hf
      have he : e = f := Except.error.inj hf
      refine Or.inl (evalQuotientIdentityLoop_error_namesStep bytes consts bytes.length 0
        ([] : List QVMFr) mem (by omega) f ?_)
      rw [← he]; exact h
  | ok p =>
      obtain ⟨stack, mem'⟩ := p
      simp only [h, bind, Except.bind] at hf
      right
      cases stack with
      | nil =>
          have h0 : QVMFault.stackLengthMismatch 0 = f := by simpa using hf
          exact ⟨0, h0.symm⟩
      | cons v rest =>
          cases rest with
          | nil => exact absurd hf (by simp)
          | cons w rest' =>
              have h0 : QVMFault.stackLengthMismatch (v :: w :: rest').length = f := by
                simpa using hf
              exact ⟨(v :: w :: rest').length, h0.symm⟩

/-- **THE ROW, GIVEN LEG (iv). PROVED, no sorry** - the machine-checked answer to "is the row now
    closable". Feed a segment error through 'qvmNoBounds_stepErrorIsReachable' and the obligation
    collapses from "no excluded fault class is reachable over a segment" to "none is reachable at a
    step", which is exactly the shape legs (i)-(iii) already supply for 25 of the 26 arms. So the row
    is NOT waiting on a new idea: it is waiting on the per-arm families to reach MODARITH7.

    The two hypotheses are premises of THIS lemma, not binders on the row - the row's own statement is
    untouched, and no hypothesis was added to it, to a bundle, to 'ValidV3' or to the root. -/
theorem qvm_validated_noBoundsFault_of_stepErrorIsReachable
    (hstep : ∀ (bytes : List Nat) (consts : List Word256) (j : Nat)
      (stack : List QVMFr) (m : QuotientRefMemory) (f : QVMFault),
        j < bytes.length →
        Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0) stack m
          = .error f →
        QvmNoBoundsFault f)
    (bytes : List Nat) (consts : List Word256) (mem : QuotientRefMemory) (f : QVMFault)
    (hf : Midfall.Generator.evalQuotientIdentity bytes consts mem = .error f) :
    QvmNoBoundsFault f := by
  rcases qvmNoBounds_stepErrorIsReachable bytes consts mem f hf with
      ⟨j, stack, m, hj, hstep'⟩ | ⟨n, rfl⟩
  · exact hstep bytes consts j stack m f hj hstep'
  · refine ⟨?_, ?_⟩
    · intro i h
      cases h
    · intro slot idx h
      cases h

#print axioms Midfall.Lowering.evalQuotientIdentityLoop_error_namesStep
#print axioms Midfall.Lowering.qvmNoBounds_stepErrorIsReachable
#print axioms Midfall.Lowering.qvm_validated_noBoundsFault
#print axioms Midfall.Lowering.qvm_validated_noBoundsFault_of_stepErrorIsReachable

end Midfall.Lowering

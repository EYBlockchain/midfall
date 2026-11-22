-- |
-- Midfall.Lowering.QvmSegment
--
-- IDSEG (card PG_identity_segment). QIDENT named 'PG_identity_segment' (QvmEmit.lean:337) as the real
-- blocker for 'qvm_compile_correct_identity' (Qvm.lean:619) and for 'builder_segments_total'
-- (Qvm.lean:992), and described it correctly: 'a second induction - over the emitted instruction
-- sequence rather than over the expression'. THIS FILE LANDS THAT INDUCTION and reduces the Prop to six
-- named per-cursor obligations whose implication chain is PROVED, not asserted.
--
-- WHAT THE BRIEF ASKED ME TO CHECK FIRST, AND WHAT I MEASURED. The brief hoped the per-arm non-fault
-- facts 'largely exist and may only need assembling'. They do not, and the gap is not assembly:
--
--   * READ axis ('readPastEnd'): 'evalQuotientIdentityStep_readsWithinStride_at_22' (QvmShift:2685)
--     plus QvmWalk's 'runAddMul*_noRF' / 'affineSum_noRF' cover 25 of the 26 identity arms at a
--     general cursor. MODARITH7 is open and named ('PG_stepNoRF_validated_cs_modarith7').
--   * SLOT axis ('constSlotOutOfRange'): 'evalQuotientIdentityStep_noSlotFault_25' (QvmShift:3348)
--     covers the same 25 of 26. MODARITH7 open, named 'PG_stepNoRF_validated_slot2_modarith7_oor'.
--   * DEPTH axis ('stackUnderflow'): NOTHING IN THE TREE. Not one lemma in QvmShift, QvmWalk, QvmFold,
--     QvmFoldLin, QvmEmit or QuotientArms bounds the stack length a step needs. QvmShift's two passes
--     are per-fault-class predicates ('NoRF', 'OORSlot') and the underflow class was never given one.
--   * SHAPE axis ('unknownOpcode', 'streamOpcodeInIdentity', 'zeroLengthRun', 'affineSumZeroCounts',
--     'modarith7UnknownFlags', and the 'panic' class): almost nothing. 'streamArms_error'
--     (Qvm.lean:1469) CHARACTERISES the five stream arms - it proves they fault, which is what lets a
--     caller exclude them by showing the opcode is not one of the five - but nothing excludes a zero
--     run length, a zero AFFINE_SUM count, unknown MODARITH7 flags, an unknown opcode, or a panic at a
--     cursor the emitter reached. Those are emitter facts - the opcode at a cursor the emitter wrote,
--     the counts it emitted nonzero - not interpreter facts.
--   * LOOP axis: TWO LOOP INDUCTIONS ALREADY EXIST and the brief is wrong that none does -
--     'evalQuotientIdentityLoop_fuelNeverBinds' (Qvm.lean:1489) and
--     'evalQuotientIdentityLoop_error_namesStep' (QvmNoBounds.lean:156). THE FUEL LEMMA THE SURVEY OWED
--     IS THEREFORE ALREADY DISCHARGED, not by this card. What did NOT exist is a loop induction that
--     carries a configuration INVARIANT and concludes '.ok': both existing ones demand step-success for
--     EVERY stack at every in-bounds cursor (unusable for a real segment - QvmShift:759
--     'shift_bare_equation_is_false_no_bytes' proves ADD faults 'stackUnderflow' on a short stack) or
--     reason about which error a failing walk names. 'loop_ok_of_walk' supplies the missing form and
--     'fuelNeverBinds_recovered' shows the existing fuel lemma is an INSTANCE of it, so nothing is
--     re-derived and nothing is duplicated.
--
-- So the brief's premise is wrong on the LOOP axis and on the DEPTH and SHAPE axes, and right only about
-- READ and SLOT. What this file lands is the form none of the three existing loop-level lemmas has: an
-- induction that carries a configuration INVARIANT and CONCLUDES '.ok' rather than excluding one fault
-- class - which is the only shape a real emitted segment can satisfy.
--
-- WHAT LANDS HERE. No sorry, and no hypothesis added to any row, to 'ValidV3', to a bundle or to the
-- root (WORKER-RULES hard rule; the Props below are all standalone, and the hypotheses they carry are
-- hypotheses on ARM-level lemmas, which RULES allows explicitly).
--   1. 'stepAt': the step the loop ACTUALLY takes, pairing the cursor with the opcode read out of the
--      bytes. Every per-arm lemma in the tree takes the opcode as a separate argument, so nothing
--      existed that named the pair - which is why none of them could be cited by a walk induction.
--   2. 'WalkInvariant' and 'loop_ok_of_walk': THE SECOND INDUCTION, over the emitted instruction
--      sequence, against an ABSTRACT configuration predicate so the emitter card can supply it without
--      restating the interpreter. 'evalQuotientIdentity_ok_of_walk' carries it to the row's granularity.
--   3. 'fuelNeverBinds_recovered': the existing fuel lemma (Qvm.lean:1489) recovered as an INSTANCE of
--      the new induction, so the generalisation is measured rather than claimed.
--   4. 'step_ok_of_noFaultClasses': the assembly lemma - 'QVMFault' has ten constructors and excluding
--      all ten from one step gives ok. The enumeration lives in exactly one place, so a new fault
--      constructor reddens here rather than hiding.
--   5. The six named axes 'PG_stepNoRF_at' / 'PG_stepSlot_at' / 'PG_stepDepth_at' / 'PG_stepShape_at' /
--      'PG_stepProgress_at' / 'PG_stepInitTerm', with 'walkInvariant_of_axes' proving they assemble,
--      and 'pg_identity_segment_of_walk' proving that the walk form IS 'PG_identity_segment'. The
--      reduction is a theorem, so the remaining distance is checkable rather than rhetorical.
--   6. 'demoSegment_runs': a real five-byte segment - two PUSH_CONST_U8 and an ADD - run through the
--      whole chain, so none of 1-5 is vacuous.
--
-- WHAT THIS DOES NOT BUY, stated plainly. The six axes still need the EMITTER to say which instruction
-- it wrote at which cursor and what it did to the stack depth: 'identityExpr' (VmBuilder.lean:934),
-- 'emitExpr' and its ~40 panic sites, plus 'compactQuotientRuns' (VmBuilder.lean:1398), which rewrites
-- the byte stream AFTER the emitter accounted for its own depth and so can move both the cursor
-- sequence and the stack effects. That is a different card. What this file changes is that it is now
-- the ONLY thing left, and each of the six has an exact goal state below.
--
-- EXCLUSIONS, declared rather than assumed. MODARITH7 is excluded on the read and slot axes exactly as
-- QvmShift excludes it, and the exclusion is inherited by 'PG_stepNoRF_at' / 'PG_stepSlot_at' here. The
-- four LIMB-family arms (LIN7, BILIN7_ROW, BILIN7_PAIRWISE, MODARITH7) additionally sit behind
-- 'PG_limbCountAgrees' (QuotientArms.lean:4425), an OPEN HUMAN DECISION; nothing here assumes
-- 'tcq.limbCount = quotientVmLimbs' and no statement in this file mentions a template table at all, so
-- no limb arm is silently admitted.
--
-- NO Midfall/Instances/ IMPORT (D-P17). No fixture in any statement a row consumes (D-P71): the demo
-- segment is written inline as a non-vacuity witness, the pattern QvmShift:3366 uses. No 'decide' on
-- any 2^256 numeral; 'maxRecDepth' and 'maxHeartbeats' untouched.

import Midfall.Lowering.QvmEmit
import Midfall.Lowering.QvmShift
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QvmSegment

open Midfall
open Midfall.Lowering
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientExpr QuotientRefMemory qvmFrModulus)
open Midfall.Generator.QuotientBuilder
open Midfall.Lowering.QvmEmit

/-! ### 1. The step the loop takes, and the invariant a walk needs -/

/-- THE STEP THE LOOP ACTUALLY TAKES at cursor 'idx': the opcode is read out of the bytes, exactly the
    way 'evalQuotientIdentityLoop' reads it. Every per-arm lemma in QvmShift and QvmWalk is stated with
    the opcode as a SEPARATE argument, so nothing in the tree named the pair together - and a walk
    induction cannot cite a per-arm fact until something does. -/
def stepAt (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) : Except QVMFault IdentityStep :=
  Midfall.Generator.evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem

/-- The bridge to the per-arm statements: 'stepAt' IS the step with the opcode read from the bytes. -/
theorem stepAt_def (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt bytes consts idx stack mem =
      Midfall.Generator.evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem := rfl

/-- A WALK INVARIANT for a segment: a predicate on configurations (cursor, stack, memory) that holds at
    the start, is preserved by every step taken strictly inside the segment, and forces a singleton
    stack once the cursor has left it. The three legs are exactly the three things no existing lemma in
    the tree composes: the emitter's initial state, per-arm non-fault plus per-arm stack effect, and
    the emitter's depth accounting. Stated against an ABSTRACT 'P' so the card that knows the emitter
    can supply it without restating the interpreter. -/
def WalkInvariant (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (start : Nat) (stack₀ : List QVMFr) (mem₀ : QuotientRefMemory) : Prop :=
  P start stack₀ mem₀ ∧
    (∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ st, stepAt bytes consts idx stack mem = .ok st ∧
              P (idx + st.consumed) st.stack st.mem) ∧
    (∀ idx stack mem, ¬ idx < bytes.length → P idx stack mem → ∃ v, stack = [v])

/-- The loop's own equation, so the induction can reach the fuel-bounded auxiliary. The 'where' function
    is named 'evalQuotientIdentityLoop.go' and takes the parent's parameters first. -/
theorem evalQuotientIdentityLoop_eq_go (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityLoop bytes consts idx stack mem =
      Midfall.Generator.evalQuotientIdentityLoop.go bytes consts bytes.length idx stack mem := rfl

/-- THE OUT-OF-SEGMENT ARM, at every fuel. 'simp only [go]' unfolds exactly one level of the compiled
    structural recursion; 'show' and 'rw' do not reach it, which is why the two arm lemmas are proved by
    'simp only' on the auxiliary's own name rather than by defeq. -/
theorem go_out (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : ¬ idx < bytes.length) (fuel : Nat) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel idx stack mem =
      .ok (stack, mem) := by
  induction fuel with
  | zero =>
      simp only [Midfall.Generator.evalQuotientIdentityLoop.go]
      exact ite_eq_right_iff.mpr (fun hh => absurd hh h)
  | succ fuel ih =>
      simp only [Midfall.Generator.evalQuotientIdentityLoop.go]
      exact ite_eq_right_iff.mpr (fun hh => absurd hh h)

/-- THE IN-SEGMENT ARM: one step, then the rest of the walk with one less fuel. The 'do' block is a
    bind, and 'Except.ok a >>= f' reduces only by defeq (WORKER-RULES), so the arm is stated as an
    equation over the bind and the bind is reduced separately by 'bind_stepAt'. -/
theorem go_step (bytes : List Nat) (consts : List Word256) (fuel idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : idx < bytes.length) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (fuel + 1) idx stack mem =
      (stepAt bytes consts idx stack mem >>= fun st =>
          Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel
            (idx + st.consumed) st.stack st.mem) := by
  simp only [Midfall.Generator.evalQuotientIdentityLoop.go, stepAt]
  exact ite_eq_left_iff.mpr (fun hh => absurd h hh)

/-- A successful step's bind reduces. Kept as its own lemma because 'simp' will not do it (WORKER-RULES)
    and 'rw' alone leaves the 'do' block in the way. -/
theorem bind_stepAt {bytes : List Nat} {consts : List Word256} {fuel idx : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {st : IdentityStep}
    (hst : stepAt bytes consts idx stack mem = .ok st) :
    (stepAt bytes consts idx stack mem >>= fun st' =>
        Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel
          (idx + st'.consumed) st'.stack st'.mem) =
      Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel
        (idx + st.consumed) st.stack st.mem := by
  rw [hst]
  rfl

/-- The cursor measure the walk induction runs on. Every 'IdentityStep' arm carries
    'hConsumed : 0 < consumed', so the distance to the end of the segment drops by at least one per step
    - which is the ONLY reason the fuel and the cursor line up, since the fuel drops by one per step
    while the cursor can jump by as many as six bytes. Note that NO upper bound on 'st.consumed' is
    needed: a step that runs off the end simply lands outside the segment, where 'go_out' takes over,
    so the walk cannot stall and is not blocked by an over-long instruction. -/
theorem measure_drops (bytes : List Nat) (idx : Nat) (st : IdentityStep)
    (h : idx < bytes.length) : bytes.length - (idx + st.consumed) < bytes.length - idx := by
  have hpos : 0 < st.consumed := st.hConsumed
  omega

/-! ### 2. THE INDUCTION OVER THE EMITTED INSTRUCTION SEQUENCE -/

/-- **THE SECOND INDUCTION QIDENT NAMED.** Running the emitted instruction sequence from any cursor
    whose distance to the end of the segment fits the fuel reaches the end without faulting, provided
    the configuration predicate 'P' is preserved by every step taken. The induction is on the fuel and
    the measure is the distance to the end of the segment, so NO hypothesis about the segment itself is
    needed beyond the invariant: the progress of the walk comes from 'IdentityStep.hConsumed', not from
    a length bound. The conclusion reports the END CURSOR and carries 'P' to it, because the caller
    cannot apply the terminal leg of 'WalkInvariant' without knowing where the walk stopped. -/
theorem loop_ok_of_walk (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hstep : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ st, stepAt bytes consts idx stack mem = .ok st ∧ P (idx + st.consumed) st.stack st.mem) :
    ∀ (fuel idx : Nat) (stack : List QVMFr) (mem : QuotientRefMemory),
      bytes.length - idx ≤ fuel → P idx stack mem →
        ∃ fin s m, idx ≤ fin ∧ ¬ fin < bytes.length ∧
          Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel idx stack mem = .ok (s, m) ∧
          P fin s m := by
  intro fuel
  induction fuel with
  | zero =>
      intro idx stack mem hlen hP
      have hout : ¬ idx < bytes.length := by omega
      exact ⟨idx, stack, mem, Nat.le_refl idx, hout,
        go_out bytes consts idx stack mem hout 0, hP⟩
  | succ fuel ih =>
      intro idx stack mem hlen hP
      by_cases h : idx < bytes.length
      · obtain ⟨st, hst, hP'⟩ := hstep idx stack mem h hP
        obtain ⟨fin, s, m, _hle, hout, hgo, hPend⟩ :=
          ih (idx + st.consumed) st.stack st.mem
            (by have hd := measure_drops bytes idx st h; omega) hP'
        rw [go_step bytes consts fuel idx stack mem h, bind_stepAt hst]
        exact ⟨fin, s, m, by omega, hout, hgo, hPend⟩
      · exact ⟨idx, stack, mem, Nat.le_refl idx, h,
          go_out bytes consts idx stack mem h (fuel + 1), hP⟩

/-- THE LOOP AT THE FUEL THE ENTRY POINT ACTUALLY USES ('bytes.length'), with the end cursor and the
    invariant carried to it. -/
theorem evalQuotientIdentityLoop_ok_of_walk (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hstep : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ st, stepAt bytes consts idx stack mem = .ok st ∧ P (idx + st.consumed) st.stack st.mem) :
    ∀ idx stack mem, bytes.length - idx ≤ bytes.length → P idx stack mem →
        ∃ fin s m, idx ≤ fin ∧ ¬ fin < bytes.length ∧
          Midfall.Generator.evalQuotientIdentityLoop bytes consts idx stack mem = .ok (s, m) ∧
          P fin s m := by
  intro idx stack mem hlen hP
  rw [evalQuotientIdentityLoop_eq_go]
  exact loop_ok_of_walk bytes consts P hstep bytes.length idx stack mem hlen hP

/-- **THE EXISTING FUEL LEMMA, RECOVERED AS AN INSTANCE.** 'evalQuotientIdentityLoop_fuelNeverBinds'
    (Qvm.lean:1489) is the same conclusion under the TRIVIAL invariant: it asks the step to succeed for
    EVERY stack at every in-bounds cursor, which no real emitted segment satisfies - ADD faults
    'stackUnderflow' on a short stack, and QvmShift:759 'shift_bare_equation_is_false_no_bytes' proves
    exactly that. Taking 'P := fun _ _ _ => True' here derives it, which is the measurement that
    'loop_ok_of_walk' is a generalisation and not a second copy. Nothing is re-derived: one line over the
    new induction. -/
theorem fuelNeverBinds_recovered (bytes : List Nat) (consts : List Word256)
    (hsteps : ∀ (j : Nat) (stk : List QVMFr) (m : QuotientRefMemory), j < bytes.length →
        ∃ step, stepAt bytes consts j stk m = .ok step) :
    ∀ (fuel j : Nat) (stk : List QVMFr) (m : QuotientRefMemory),
      bytes.length - j ≤ fuel →
        Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel j stk m ≠
          .error (QVMFault.panic "reference VM fuel exhausted") := by
  have hP : ∀ idx stack mem, idx < bytes.length → True →
      ∃ st, stepAt bytes consts idx stack mem = .ok st ∧ True := by
    intro idx stack mem hidx _
    obtain ⟨st, hst⟩ := hsteps idx stack mem hidx
    exact ⟨st, hst, trivial⟩
  intro fuel j stk m hlen
  obtain ⟨_fin, s, m', _hle, _hout, hgo, _hP'⟩ :=
    loop_ok_of_walk bytes consts (fun _ _ _ => True) hP fuel j stk m hlen trivial
  rw [hgo]
  intro hh
  exact absurd hh (by simp)

/-! ### 3. From the loop to the row's granularity -/

/-- THE TOP-LEVEL COMPOSITION. 'evalQuotientIdentity' is the loop PLUS a singleton-stack test, so a walk
    invariant buys the row's conclusion only if its third leg pins the terminal stack. That leg is the
    emitter's depth accounting, and it is the reason 'WalkInvariant' carries it rather than the caller. -/
theorem evalQuotientIdentity_ok_of_walk (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hP : WalkInvariant bytes consts P 0 [] mem) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity bytes consts mem = .ok (v, mem') := by
  obtain ⟨hinit, hstep, hterm⟩ := hP
  obtain ⟨fin, s, m, _hle, hout, hloop, hPend⟩ :=
    evalQuotientIdentityLoop_ok_of_walk bytes consts P hstep 0 ([] : List QVMFr) mem
      (by omega) hinit
  obtain ⟨v, hv⟩ := hterm fin s m hout hPend
  subst hv
  unfold Midfall.Generator.evalQuotientIdentity
  rw [hloop]
  exact ⟨v, m, rfl⟩

/-- The same conclusion in the exact Bool form 'PG_identity_segment' states it in. -/
theorem evalQuotientIdentity_isOk_of_walk (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hP : WalkInvariant bytes consts P 0 [] mem) :
    (Midfall.Generator.evalQuotientIdentity bytes consts mem).isOk = true := by
  obtain ⟨v, mem', h⟩ := evalQuotientIdentity_ok_of_walk bytes consts mem P hP
  rw [h]
  rfl

/-! ### 4. The fault-class assembly -/

/-- **THE ASSEMBLY LEMMA.** 'QVMFault' has ten constructors and this enumerates all ten: excluding each
    from one step gives ok. The tenth, 'stackLengthMismatch', is raised only by 'evalQuotientIdentity'
    on the FINAL stack and never by a step - but nothing here ASSUMES that, because proving it per arm
    means walking the whole 26-arm body, and the honest version asks the caller for it alongside the
    other nine. It is carried inside AXIS 4 below. Keeping the enumeration in one place means a new
    fault constructor reddens here rather than hiding. -/
theorem step_ok_of_noFaultClasses {α : Type} (x : Except QVMFault α)
    (h1 : ∀ i, x ≠ .error (QVMFault.readPastEnd i))
    (h2 : ∀ slot j, x ≠ .error (QVMFault.constSlotOutOfRange slot j))
    (h3 : ∀ j, x ≠ .error (QVMFault.stackUnderflow j))
    (h4 : ∀ j, x ≠ .error (QVMFault.zeroLengthRun j))
    (h5 : ∀ j, x ≠ .error (QVMFault.affineSumZeroCounts j))
    (h6 : ∀ flags j, x ≠ .error (QVMFault.modarith7UnknownFlags flags j))
    (h7 : ∀ op j, x ≠ .error (QVMFault.streamOpcodeInIdentity op j))
    (h8 : ∀ op j, x ≠ .error (QVMFault.unknownOpcode op j))
    (h9 : ∀ s, x ≠ .error (QVMFault.panic s))
    (h10 : ∀ n, x ≠ .error (QVMFault.stackLengthMismatch n)) :
    ∃ a, x = .ok a := by
  cases x with
  | ok a => exact ⟨a, rfl⟩
  | error f =>
      cases f with
      | stackUnderflow j => exact absurd rfl (h3 j)
      | readPastEnd i => exact absurd rfl (h1 i)
      | constSlotOutOfRange slot j => exact absurd rfl (h2 slot j)
      | zeroLengthRun j => exact absurd rfl (h4 j)
      | affineSumZeroCounts j => exact absurd rfl (h5 j)
      | modarith7UnknownFlags flags j => exact absurd rfl (h6 flags j)
      | streamOpcodeInIdentity op j => exact absurd rfl (h7 op j)
      | unknownOpcode op j => exact absurd rfl (h8 op j)
      | stackLengthMismatch n => exact absurd rfl (h10 n)
      | panic s => exact absurd rfl (h9 s)

/-! ### 5. The six named axes, and the reduction -/

/-- **AXIS 1 - READ.** No step at a reachable cursor reads past the end of the segment. QvmShift supplies
    this for 25 of the 26 identity arms at a general cursor
    ('evalQuotientIdentityStep_readsWithinStride_at_22' plus QvmWalk's 'affineSum_noRF' and
    'runAddMul*_noRF'), each under the VALIDATOR's width hypothesis 'quotientOpLen (op :: rest) 0 = .ok
    len' with 'len ≤ (op :: rest).length'. What is missing is not the arm lemmas but the bridge from the
    segment's own bytes to 'bytes.drop idx = op :: rest' at a cursor the walk reaches - which is AXIS 5.
    MODARITH7 is excluded, exactly as QvmShift excludes it. -/
def PG_stepNoRF_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) : Prop :=
  ∀ idx stack mem, idx < bytes.length → P idx stack mem →
    Midfall.Lowering.NoRF (stepAt bytes consts idx stack mem)

/-- **AXIS 2 - SLOT.** No step at a reachable cursor faults a constant slot out of range.
    'evalQuotientIdentityStep_noSlotFault_25' (QvmShift:3348) supplies this for the same 25 of 26 arms,
    under 'visitQuotientOperands' succeeding and every slot the WALKER names being below the table. The
    row's own 'hconsts' is about the VALUES in the table, not about slot INDICES, so this axis is not
    discharged by the row's hypotheses - it needs the validator's 'checkQuotientConstSlot' leg, which is
    why it is named separately. MODARITH7 open as 'PG_stepNoRF_validated_slot2_modarith7_oor'. -/
def PG_stepSlot_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) : Prop :=
  ∀ idx stack mem, idx < bytes.length → P idx stack mem →
    ∀ slot j, stepAt bytes consts idx stack mem ≠
      .error (QVMFault.constSlotOutOfRange slot j)

/-- **AXIS 3 - DEPTH. NOTHING IN THE TREE SUPPLIES ANY PART OF THIS.** No step at a reachable cursor
    underflows the stack. This is the axis the brief most overestimated: QvmShift's two passes are
    per-fault-class and the underflow class has no predicate at all, because the reference's own comment
    (VmReference.lean:719-722) says the pop helpers 'only fire on validator drift' - the OFFLINE
    VALIDATOR proves depth safety, and 'VmValidator.lean' is out of bounds from here. Exact goal state,
    per arm 'op':

      ∀ (stack : List QVMFr) (mem : QuotientRefMemory) (idx : Nat),
        P idx stack mem → idx < bytes.length → op = bytes.getD idx 0 →
        ∀ j, evalQuotientIdentityStep bytes consts idx op stack mem ≠
          .error (QVMFault.stackUnderflow j)

    discharged from a hypothesis of the shape 'stack.length ≥ popCount op' for a per-arm 'popCount'.
    'popCount' does not exist in the tree: the validator computes depth with its own fold and no lemma
    ties it to the interpreter's 'popStack'. -/
def PG_stepDepth_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) : Prop :=
  ∀ idx stack mem, idx < bytes.length → P idx stack mem →
    ∀ j, stepAt bytes consts idx stack mem ≠ .error (QVMFault.stackUnderflow j)

/-- **AXIS 4 - SHAPE. NOTHING IN THE TREE SUPPLIES ANY PART OF THIS EITHER.** The opcode at a reachable
    cursor is an identity opcode whose operands the emitter actually filled in: not one of the five
    stream opcodes, not unknown, not a zero-length run, not an AFFINE_SUM with a zero count, not a
    MODARITH7 with unknown flag bits, no panic - which covers the 'fqFromU256' rejection at
    reference.rs:548, the class the row's 'hconsts' is about - and not the singleton-stack class, which
    a step does not raise but which 'step_ok_of_noFaultClasses' asks for rather than assumes. These are
    facts about what 'identityExpr' WROTE, not about the interpreter, so no amount of per-arm
    interpreter work reaches them; 'compactQuotientRuns' has to be reasoned about too, because it
    rewrites the byte stream after the emitter accounted for it. -/
def PG_stepShape_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) : Prop :=
  ∀ idx stack mem, idx < bytes.length → P idx stack mem →
    (∀ op j, stepAt bytes consts idx stack mem ≠ .error (QVMFault.streamOpcodeInIdentity op j)) ∧
      (∀ op j, stepAt bytes consts idx stack mem ≠ .error (QVMFault.unknownOpcode op j)) ∧
      (∀ j, stepAt bytes consts idx stack mem ≠ .error (QVMFault.zeroLengthRun j)) ∧
      (∀ j, stepAt bytes consts idx stack mem ≠ .error (QVMFault.affineSumZeroCounts j)) ∧
      (∀ flags j, stepAt bytes consts idx stack mem ≠
        .error (QVMFault.modarith7UnknownFlags flags j)) ∧
      (∀ s, stepAt bytes consts idx stack mem ≠ .error (QVMFault.panic s)) ∧
      (∀ n, stepAt bytes consts idx stack mem ≠ .error (QVMFault.stackLengthMismatch n))

/-- **AXIS 5 - PROGRESS.** The invariant survives one step. This is where the interpreter's 'consumed'
    has to be tied to the emitter's own byte count: the successor cursor is 'idx + st.consumed', so the
    invariant can only be stated in terms of the emitter's cursor sequence once
    'st.consumed = quotientOpLen bytes idx'. QvmShift's
    'evalQuotientIdentityStep_consumed_agrees_at_22' is exactly that equation for 25 of the 26 arms, so
    this axis is the assembly of the width agreements with the emitter's cursor arithmetic - and it is
    also the axis on which 'compactQuotientRuns' first bites, because the compaction rewrites the widths
    of the two RUN arms and of AFFINE_SUM. -/
def PG_stepProgress_at (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) : Prop :=
  ∀ idx stack mem st, idx < bytes.length → P idx stack mem →
    stepAt bytes consts idx stack mem = .ok st →
      P (idx + st.consumed) st.stack st.mem

/-- **AXIS 6 - INITIAL AND TERMINAL CONFIGURATION.** The walk starts at cursor 0 with the empty stack the
    reference hands it, and every configuration it can stop at has exactly one value on the stack. The
    second leg is the emitter's 'stackDepth' accounting read back through the interpreter: 'identityExpr'
    (VmBuilder.lean:934) resets 'stackDepth' to 0, runs 'emitExprTop', then 'foldIdentity' pops, and
    refuses with 'siteStackLeak' unless the depth is 0 again - so the SEGMENT, which is the bytes with
    the trailing fold instruction stripped by 'finalizedIdentitySegment', has to leave exactly one value.
    That is a real claim and nothing in the tree states it: 'segmentMaxStack' (VmBuilder.lean:1500)
    MEASURES the high-water mark but never asserts the final depth. -/
def PG_stepInitTerm (bytes : List Nat)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) (mem₀ : QuotientRefMemory) : Prop :=
  P 0 ([] : List QVMFr) mem₀ ∧
    (∀ idx stack mem, ¬ idx < bytes.length → P idx stack mem → ∃ v, stack = [v])

/-- **THE SIX AXES ASSEMBLE.** Proved here so that the reduction below is a theorem and not a wish: the
    four non-fault axes give a successful step by 'step_ok_of_noFaultClasses', and the fifth carries the
    invariant across it. -/
theorem walkInvariant_of_axes (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) (mem₀ : QuotientRefMemory)
    (h1 : PG_stepNoRF_at bytes consts P)
    (h2 : PG_stepSlot_at bytes consts P)
    (h3 : PG_stepDepth_at bytes consts P)
    (h4 : PG_stepShape_at bytes consts P)
    (h5 : PG_stepProgress_at bytes consts P)
    (h6 : PG_stepInitTerm bytes P mem₀) :
    WalkInvariant bytes consts P 0 ([] : List QVMFr) mem₀ := by
  refine ⟨h6.1, ?_, h6.2⟩
  intro idx stack mem hidx hP
  obtain ⟨sh, un, zr, af, mf, pa, sl⟩ := h4 idx stack mem hidx hP
  obtain ⟨a, ha⟩ := step_ok_of_noFaultClasses (stepAt bytes consts idx stack mem)
    (h1 idx stack mem hidx hP) (h2 idx stack mem hidx hP) (h3 idx stack mem hidx hP)
    zr af mf sh un pa sl
  exact ⟨a, ha, h5 idx stack mem a hidx hP ha⟩

/-- **THE REDUCED BLOCKER.** 'PG_identity_segment' with its conclusion replaced by the EXISTENCE OF A
    WALK INVARIANT. Strictly more concrete than the original: the original asks for a whole-segment
    totality property of the interpreter, and this asks for a per-cursor predicate with six local
    obligations, two of which are already supplied per arm by QvmShift and QvmWalk and two of which
    (DEPTH and SHAPE) are named above with their exact goal states. -/
def PG_identity_segment_walk : Prop :=
  ∀ (r : QuotientShapeRecognizers) (_hr : RecognizersSound r)
    (s₀ s₁ : QuotientProgramBuilder) (e : QuotientExpr) (t : QuotientTarget)
    (gap : Option Nat) (cseg seg : List Nat),
    identityExpr r s₀ e t gap = .ok s₁ →
    exprBounded e →
    (∀ c ∈ s₁.consts, c.toNat < qvmFrModulus) →
    compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg →
    finalizedIdentitySegment cseg = some seg →
    ∀ (ρ : Valuation),
      ∃ (P : Nat → List QVMFr → QuotientRefMemory → Prop),
        WalkInvariant seg s₁.consts P 0 [] (memOfρ ρ (leafKeys e))

/-- **THE REDUCTION, PROVED.** 'PG_identity_segment_walk' implies 'PG_identity_segment'. Nothing was
    added to either Prop's hypotheses; the implication runs entirely through the walk induction landed
    above. -/
theorem pg_identity_segment_of_walk : PG_identity_segment_walk → PG_identity_segment := by
  intro h r hr s₀ s₁ e t gap cseg seg hemit hb hconsts hcompact hseg ρ
  obtain ⟨P, hP⟩ := h r hr s₀ s₁ e t gap cseg seg hemit hb hconsts hcompact hseg ρ
  exact evalQuotientIdentity_isOk_of_walk seg s₁.consts (memOfρ ρ (leafKeys e)) P hP

/-! ### 6. Non-vacuity: a real segment run through the whole chain -/

/-- A five-byte identity segment: push slot 0, push slot 1, add. Two bytes each for the pushes, one for
    the ADD, and the stack ends at exactly one value - the shape of everything 'identityExpr' emits for
    a binary leaf expression. Written inline as a witness and in no statement a row consumes (D-P71). -/
def demoSegment : List Nat := [qOpPushConstU8, 0, qOpPushConstU8, 1, qOpAdd]

/-- The constant table the witness runs against: two canonical entries. -/
def demoConsts : List Word256 := [0, 1]

/-- The memory the witness runs against: the empty seeded memory. -/
def demoMem : QuotientRefMemory :=
  Midfall.Generator.quotientRefMemoryNew (Midfall.Generator.qvmBytesOfNats [])

/-- THE WALK INVARIANT OF THE WITNESS: the cursor sequence 0, 2, 4, 5 with the stack depth the walk
    actually has at each. This is the shape AXIS 5 and AXIS 6 have to produce for a real emitted
    segment, exhibited here so the API is known usable. -/
def demoP (idx : Nat) (stack : List QVMFr) (_mem : QuotientRefMemory) : Prop :=
  (idx = 0 ∧ stack = []) ∨
    (idx = 2 ∧ stack.length = 1) ∨
    (idx = 4 ∧ stack.length = 2) ∨
    (idx ≥ 5 ∧ stack.length = 1)

theorem demo_len : demoSegment.length = 5 := rfl

/-- A list of length two is a two-element list. Stated here because 'List.length_eq_two' is not in this
    Lean's core and the replacement is not in QvmFold, QvmFoldLin, QuotientFrame or QuotientArms. -/
theorem length_eq_two {α : Type} {s : List α} (h : s.length = 2) : ∃ x y, s = [x, y] := by
  cases s with
  | nil => exact absurd h (by simp)
  | cons x rest =>
      cases rest with
      | nil => exact absurd h (by simp)
      | cons y ys =>
          cases ys with
          | nil => exact ⟨x, y, rfl⟩
          | cons z zs => exact absurd h (by simp)

theorem length_eq_one' {α : Type} {s : List α} (h : s.length = 1) : ∃ x, s = [x] := by
  cases s with
  | nil => exact absurd h (by simp)
  | cons x rest =>
      cases rest with
      | nil => exact ⟨x, rfl⟩
      | cons y ys => exact absurd h (by simp)

/-- The three steps of the witness, computed. -/
theorem demo_step0 (mem : QuotientRefMemory) :
    stepAt demoSegment demoConsts 0 ([] : List QVMFr) mem =
      .ok { stack := [0], consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep demoSegment demoConsts 0
          (demoSegment.getD 0 0) ([] : List QVMFr) mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem demo_step1 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt demoSegment demoConsts 2 stack mem =
      .ok { stack := 1 :: stack, consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep demoSegment demoConsts 2
          (demoSegment.getD 2 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem demo_step2 (a b : QVMFr) (mem : QuotientRefMemory) :
    stepAt demoSegment demoConsts 4 [a, b] mem =
      .ok { stack := [qvmFrAdd b a], consumed := 1, hConsumed := Nat.succ_pos 0,
            mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep demoSegment demoConsts 4
          (demoSegment.getD 4 0) [a, b] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

/-- THE WITNESS HAS A WALK INVARIANT. -/
theorem demo_walkInvariant : WalkInvariant demoSegment demoConsts demoP 0 [] demoMem := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro idx stack mem hidx hP
    rw [demo_len] at hidx
    rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, hl⟩)
    · subst hs
      refine ⟨_, demo_step0 mem, ?_⟩
      show demoP 2 [0] mem
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · obtain ⟨a, rfl⟩ := length_eq_one' hl
      refine ⟨_, demo_step1 [a] mem, ?_⟩
      show demoP 4 [1, a] mem
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp⟩))
    · obtain ⟨a, b, rfl⟩ := length_eq_two hl
      refine ⟨_, demo_step2 a b mem, ?_⟩
      show demoP 5 [qvmFrAdd b a] mem
      exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))
    · omega
  · intro idx stack mem hout hP
    rw [demo_len] at hout
    rcases hP with (⟨h1, _⟩ | ⟨h2, hl⟩ | ⟨h3, hl⟩ | ⟨h4, hl⟩)
    · omega
    · omega
    · omega
    · exact length_eq_one' hl

/-- **THE CHAIN IS NOT VACUOUS.** The witness runs end to end through 'evalQuotientIdentity_ok_of_walk'
    - not by evaluating the interpreter directly. -/
theorem demoSegment_runs :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity demoSegment demoConsts demoMem =
      .ok (v, mem') :=
  evalQuotientIdentity_ok_of_walk demoSegment demoConsts demoMem demoP demo_walkInvariant

/-- And the same through the Bool form the Prop uses. -/
theorem demoSegment_isOk : (Midfall.Generator.evalQuotientIdentity demoSegment demoConsts demoMem).isOk :=
  evalQuotientIdentity_isOk_of_walk demoSegment demoConsts demoMem demoP demo_walkInvariant

#print axioms Midfall.Lowering.QvmSegment.PG_identity_segment_walk
#print axioms Midfall.Lowering.QvmSegment.PG_stepDepth_at
#print axioms Midfall.Lowering.QvmSegment.PG_stepShape_at
#print axioms Midfall.Lowering.QvmSegment.loop_ok_of_walk
#print axioms Midfall.Lowering.QvmSegment.fuelNeverBinds_recovered
#print axioms Midfall.Lowering.QvmSegment.evalQuotientIdentity_ok_of_walk
#print axioms Midfall.Lowering.QvmSegment.step_ok_of_noFaultClasses
#print axioms Midfall.Lowering.QvmSegment.walkInvariant_of_axes
#print axioms Midfall.Lowering.QvmSegment.pg_identity_segment_of_walk
#print axioms Midfall.Lowering.QvmSegment.demoSegment_runs
#cone_sorries Midfall.Lowering.QvmSegment.evalQuotientIdentity_ok_of_walk
#cone_sorries Midfall.Lowering.QvmSegment.pg_identity_segment_of_walk
#cone_sorries Midfall.Lowering.QvmSegment.demoSegment_runs

end Midfall.Lowering.QvmSegment

/-! ### 8. Where the six axes were taken next (pointer appended by card SEGPROVE; nothing above changes)

**POINTER, NOT A PROOF STEP.** The six axes of section 5 have since been discharged for REAL EMITTED
segments - the bytes 'identityExpr' writes, not a hand-typed list - in
'Midfall/Lowering/QvmSegmentReal.lean'. Two findings there bear on this file's header claim that 'the six
axes still need the EMITTER to say which instruction it wrote at which cursor':

  (a) the hand-built 'demoSegment' above is NOT what the emitter produces for the expression it was meant
      to model: the accumulator peephole fires, so 'add (const 5) (const 11)' lowers to FOUR bytes
      (PUSH_CONST_U8 then ADD_CONST_U8), not five. 'walkInvariant_of_axes' is now instantiated by
      segments the emitter actually wrote, including two whose bytes 'compactQuotientRuns' rewrote.

  (b) 'identityExpr' is a well-founded recursion the kernel will not unfold, so 'decide' and 'rfl' on 'the
      emitter wrote these bytes' fail at ANY program size - the emitter-agreement facts have to be VM
      gates, the convention of 'VmBuilder.lean:1751-1773'. That is also why 'builder_segments_total'
      cannot be closed by exhibiting one concrete build; the new file reduces it instead to a single
      named Prop, 'PG_planSegmentWalk', and proves that Prop implies the row's exact conclusion. -/

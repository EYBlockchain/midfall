-- |
-- Midfall.Lowering.QvmCursor
--
-- Card WCURSOR - 'PG_stackWalkCursor' (QFIX's obligation O4): THE DECODED INSTRUCTION WIDTH IS THE
-- REFERENCE'S 'consumed' FIELD, per arm, at a general cursor. STKINV (QuotientStackInv.lean:770-780)
-- proved the stack invariant chains for four arms and reported that whole-segment iteration is blocked
-- on the CURSOR and not on the depth; DEPTH discharged the depth axis for 22 arms; this card discharges
-- the cursor for 25 of the 26 identity arms and names the one that remains.
--
-- THE MISMATCH, MEASURED - AND IT DOES BITE, IN A DIFFERENT PLACE THAN DEPTH REPORTED.
-- DEPTH found nothing for the depth axis because the validator's fault named the REQUIREMENT
-- ('QuotientValidationFault.stackUnderflow op idx required found', four fields) while the interpreter's
-- named only the CURSOR ('QVMFault.stackUnderflow idx', one field), so the two had no shared vocabulary.
-- Here the two sides DO share a vocabulary - both name a width - but they name TWO DIFFERENT WIDTH
-- FUNCTIONS and nothing in the tree connected them:
--
--   * the REQUIREMENT is stated against the CHECKED decoder 'decodeByteQuotientInstruction'
--     (VmValidator.lean:846), which is what 'qSegmentDepthGo' (QuotientInterp.lean:1120), 'FoldDepth'
--     (QvmDepth.lean:1163) and therefore the validator's whole-segment walk actually step with. It
--     bounds-checks the instruction, refuses a zero-length run, refuses unknown MODARITH7 flags and
--     validates memory tokens.
--   * the interpreter-side prior art is stated against the UNCHECKED general walker 'quotientOpLen'
--     (VmValidator.lean:651): 'evalQuotientIdentityStep_consumed_agrees' (Qvm.lean:1197), its
--     general-cursor twin 'evalQuotientIdentityStep_consumed_agrees_at_22' (QvmShift.lean:2705),
--     'consumed_agrees_at_runAddMul*' and 'consumed_agrees_at_affineSum'. NONE of them mentions the
--     checked decoder. So QvmShift's 25-arm width package could not be cited by the walk at all.
--
-- SECTION 2 LANDS THE BRIDGE: when the checked decoder succeeds, the unchecked walker gives the SAME
-- number, because the checked decoder's extra work is bounds checks and refusals, not arithmetic - the
-- two length functions compute the same expression per arm ('checkedQuotientLenMul'/'Add' cannot fail on
-- 'Nat', which is why the checked branch reduces to the unchecked formula - landed as
-- 'checkedQuotientLenMul_ok' / 'checkedQuotientLenAdd_ok'). Composing it with QvmShift's
-- interpreter-side package is sections 2 and 3; section 4 discharges 'PG_stackWalkCursor' itself; section 5
-- lands the walk and section 6 runs it on IDSEG's witness.
--
-- WHAT LANDS HERE, no sorry:
--   1. 'decode_ok_parts' / 'decode_ok_getD' / 'decode_ok_drop' - what a successful decode carries.
--      'decode_ok_getD' is the equation DEPTH explicitly declined to prove ('QvmDepth.lean:50': "this
--      card does not prove decodeByteQuotientInstruction bytes idx = .ok (op, len) -> bytes.getD idx 0
--      = op"); it is a fact about the decoder's do-block, and it is here, so DEPTH's carried hypothesis
--      'hh' is now derivable from the fold rather than given.
--   2. THE BRIDGE, per arm: 'dec_width_of_table' and its 22 instances 'dec_width_X' (the checked
--      decoder's width for a static arm IS its table width), plus 'lenChecked_runP' / '_runL' /
--      '_affineSum' for the three arms whose width the decoder DECODES from an operand count.
--   3. THE CURSOR EQUATION for 25 of the 26 identity arms at a GENERAL cursor: 'cursor_X', pairing the
--      validator-side bridge with QvmShift's interpreter-side width agreement - the same two-halves
--      shape DEPTH used for the depth axis ('step_noUF_*' beside 'vpop_*').
--   4. 'pG_stackWalkCursor_of_cursorArm25' (section 4): the published Prop, discharged for the roster - and
--      'decode_ok_getD' supplies the opcode equation DEPTH left as a carried hypothesis.
--   5. THE WALK (section 5): 'PG_stepProgress_at_of_decoded_steps', 'loop_ok_of_decoded_steps' and
--      'foldDepth_getD' - IDSEG's walk
--      induction re-entered so the EMITTER can supply its step leg in the VALIDATOR's cursor vocabulary
--      ('idx + len' for the decoded 'len') instead of the interpreter's 'idx + st.consumed'. That is the
--      sense in which the walk can now iterate: the cursor is no longer the blocker.
--   6. NON-VACUITY (section 6): 'demoPG_stackWalkCursor', 'demo_decoded_steps' and
--      'demo_walk_iterates_of_decoded' - IDSEG's own five-byte witness segment, so the axis is discharged
--      for a real segment and the walk is iterated on it, not merely named.
--
-- EXCLUSIONS, declared rather than assumed. ONE of the 26 identity arms is not covered:
--   * MODARITH7 is excluded GENUINELY, and not by the limb decision: it is the one arm with no
--     'step_shift_*' congruence anywhere (QvmShift.lean:2810 'PG_stepNoRF_validated_shif2_modarith7_shift'),
--     so no general-cursor width agreement exists for it to be composed with. Named as
--     'PG_stackWalkCursor_modarith7'.
--   * THE THREE LIMB ARMS LIN7, BILIN7_ROW, BILIN7_PAIRWISE ARE COVERED, and that is a finding: unlike
--     DEPTH (where the exclusion was vacuous because all four limb arms PUSH), here it is vacuous for a
--     different reason - their widths are STATIC TABLE ENTRIES (22, 24, 18) and the reference's own
--     'limbLinearForm'/'limbRowForm'/'limbPairwiseForm' advance by exactly those amounts with no
--     template table in sight, and QvmShift's package already carries all three. Nothing here assumes
--     'tcq.limbCount = quotientVmLimbs' and no statement mentions a template table, so no limb arm is
--     silently admitted either: the equation is between the validator's table and the reference's fold,
--     both of which use 'quotientVmLimbs' as a literal 7.
--   * The two RUN arms and AFFINE_SUM are covered in section 3 (dynamic widths), so the covered set is
--     25 of 26 - see 'cursorArm25'. The five stream opcodes and the unknown-opcode class are not identity
--     arms at all: the reference refuses them ('step_noUnderflow_stream5', QvmDepth), so they cannot be
--     admitted to a cursor equation about a successful step.
--
-- THE THIRD CURSOR, NAMED AND NOT PROVED. The brief describes O4 as "the emitted arm's q_pc advance must
-- equal the reference step's consumed field". The published Prop does NOT say that: it says DECODED WIDTH
-- = consumed, and this card discharges that. The emitted machine's 'q_pc' is a THIRD object, and the
-- arm contracts that STKINV cites do not constrain it at all: 'qArmValueAll_neg'
-- (QuotientFrame.lean:935-946) has post 'V' = VEnv.set V "q_top" ...' with NO q_pc clause, and the
-- convention (QuotientArms.lean:4466-4469) is that the reference's 'consumed' counts the opcode byte
-- while the arm's 'q_pc' advance counts the operand bytes only - so the two differ by exactly the one
-- byte the dispatch consumed. That equation is an ARM-LAYER fact about 'qvmLoopPre' plus the arm body,
-- it is not in this card's ownership, and it is NOT quietly folded into what was proved: what this card
-- discharges is the equation the published Prop actually states. If the loop contract is ever to name the
-- arm's own advance, the missing ingredient is a q_pc clause in the 'qArmValueAll_*' posts (arm layer,
-- QuotientArms/QuotientFrame - not this card's files), and that is reported here rather than invented.
--
-- HARD RULES HONOURED. No hypothesis added to a row, 'ValidV3', a bundle or the root; 'PG_stackWalkCursor'
-- and 'QStackCorr' are cited, not restated; 'Obligations.lean' untouched; no frozen file; no v1;
-- 'vendor/', 'VmReference.lean' and the Rust under 'proofs/' read-only. No 'decide' on any 2^256 numeral
-- (every 'decide' here is on a Bool opcode-byte comparison or on the five-byte witness), no
-- 'native_decide', no fixture in any statement a row consumes (D-P71), 'maxRecDepth'/'maxHeartbeats'
-- untouched.

import Midfall.Lowering.QvmDepth
import Midfall.Lowering.QuotientStackInv
import Midfall.Generator.Quotient.VmValidator
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QvmCursor
open Midfall
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientRefMemory qvmFrModulus)
open Midfall.Lowering.QvmSegment
open Midfall.Lowering.QvmShift
open Midfall.Lowering.QvmDepth
open Midfall.Generator.QuotientValidator

/-! ### 1. What a successful decode carries -/

/-- A successful 'byteAtPanic' means the cursor is inside the bytes and names the head. -/
theorem byteAtPanic_ok_cons {bytes : List Nat} {idx line op : Nat}
    (h : byteAtPanic bytes idx line = .ok op) :
    ∃ rest : List Nat, bytes.drop idx = op :: rest := by
  cases h' : bytes.drop idx with
  | nil => unfold byteAtPanic at h; rw [h'] at h; cases h
  | cons b rest =>
      unfold byteAtPanic at h
      rw [h'] at h
      cases h
      exact ⟨rest, rfl⟩

/-- 'byteAtPanic' carries its Rust site string only in the ERROR payload, so a success at one site is a
    success at any site. Needed because the decoder reads the opcode at QVM:2511 and its length helper
    reads the same byte again at QVM:2539. -/
theorem byteAtPanic_line {bytes : List Nat} {idx line line' op : Nat}
    (h : byteAtPanic bytes idx line = .ok op) : byteAtPanic bytes idx line' = .ok op := by
  obtain ⟨rest, hr⟩ := byteAtPanic_ok_cons h
  unfold byteAtPanic
  rw [hr]

/-- 'List.getD' is a drop followed by a head, stated as a theorem because the equation form the core
    exposes is through 'getElem?' and does not reduce under 'unfold'. -/
theorem getD_eq_drop_headD (xs : List Nat) (i : Nat) :
    xs.getD i 0 = (xs.drop i).headD 0 := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons a as ih =>
      cases i with
      | zero => rfl
      | succ k =>
          rw [List.getD_cons_succ, List.drop_cons (by omega : 0 < k + 1), Nat.succ_sub_one, ih]

/-- **THE TWO FACTS A SUCCESSFUL DECODE CARRIES**: the opcode byte at the cursor, and the CHECKED width.
    Read out of the decoder's own do-block - the decoder is a 'requireQuotientBytes' / 'byteAtPanic' /
    'quotientOpcodeSpec' / 'quotientByteInstructionLenChecked' / token / nonzero chain, and every leg
    that could have refused is discharged by the success itself rather than assumed. -/
theorem decode_ok_parts {bytes : List Nat} {idx op len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (op, len)) :
    byteAtPanic bytes idx 2511 = .ok op ∧
      quotientByteInstructionLenChecked bytes idx = .ok len := by
  unfold decodeByteQuotientInstruction at h
  obtain ⟨_w, _hw, h1⟩ := peel_bind h
  obtain ⟨op', hop, h2⟩ := peel_bind h1
  cases hspec : quotientOpcodeSpec op' with
  | none =>
      rw [hspec] at h2
      simp only [Bind.bind, Except.bind] at h2
      cases h2
  | some spec =>
      rw [hspec] at h2
      simp only [Bind.bind, Except.bind] at h2
      obtain ⟨len', hlen, h4⟩ := peel_bind h2
      have hgoal : op' = op ∧ len' = len := by
        cases hb : (op' == qOpPushMemToken || op' == qOpPushMemTokenOffset) with
        | true =>
            rw [hb] at h4
            obtain ⟨_tok, _htok, h5⟩ := peel_bind h4
            obtain ⟨_u, _hu, h6⟩ := peel_bind h5
            cases hl : (len' == 0) with
            | true =>
                rw [hl] at h6
                simp (config := {decide := true}) only [reduceIte] at h6
                cases h6
            | false =>
                rw [hl] at h6
                simp (config := {decide := true}) only [reduceIte] at h6
                rcases Except.ok.inj h6 with ⟨rfl, rfl⟩
                exact ⟨rfl, rfl⟩
        | false =>
            rw [hb] at h4
            cases hl : (len' == 0) with
            | true =>
                rw [hl] at h4
                simp (config := {decide := true}) only [reduceIte] at h4
                cases h4
            | false =>
                rw [hl] at h4
                simp (config := {decide := true}) only [reduceIte] at h4
                rcases Except.ok.inj h4 with ⟨rfl, rfl⟩
                exact ⟨rfl, rfl⟩
      rcases hgoal with ⟨rfl, rfl⟩
      exact ⟨hop, hlen⟩

/-- THE OPCODE THE DECODER NAMES IS THE BYTE AT THE CURSOR. This is the equation DEPTH named and
    deliberately left open ('QvmDepth.lean:49-51'), so 'FoldDepth' now supplies 'hh' itself. -/
theorem decode_ok_getD {bytes : List Nat} {idx op len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (op, len)) : bytes.getD idx 0 = op := by
  obtain ⟨rest, hr⟩ := byteAtPanic_ok_cons (decode_ok_parts h).1
  rw [getD_eq_drop_headD, hr]
  rfl

/-- The dropped-prefix form the interpreter-side width agreements are stated against. -/
theorem decode_ok_drop {bytes : List Nat} {idx op len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (op, len)) :
    ∃ rest : List Nat, bytes.drop idx = op :: rest :=
  byteAtPanic_ok_cons (decode_ok_parts h).1

/-! ### 2. THE BRIDGE AND THE 22 STATIC ARMS: checked decoder width = unchecked walker width -/

/-- The four dynamic opcodes have no table width. 'rfl' each: this is the theorem form of the
    'opcodeTable_pinnedByteLengths_ok' gate. -/
theorem byteLen_none_runP : quotientOpcodeByteLen qOpRunAddMulMemMemConstU8 = none := rfl
theorem byteLen_none_runL : quotientOpcodeByteLen qOpRunAddMulConstU8MemU16 = none := rfl
theorem byteLen_none_affineSum : quotientOpcodeByteLen qOpAffineSum = none := rfl
theorem byteLen_none_modarith7 : quotientOpcodeByteLen qOpModarith7 = none := rfl

/-- **THE CHECKED LENGTH HELPER'S TABLE BRANCH.** If the opcode is not one of the four dynamic arms, a
    successful checked length is exactly a table hit. The bounds check the helper performs after the
    table lookup is discharged by the success, not assumed. -/
theorem lenChecked_table {bytes : List Nat} {idx op len : Nat}
    (h1 : byteAtPanic bytes idx 2539 = .ok op)
    (hP : op ≠ qOpRunAddMulMemMemConstU8) (hL : op ≠ qOpRunAddMulConstU8MemU16)
    (hS : op ≠ qOpAffineSum) (hM : op ≠ qOpModarith7)
    (h : quotientByteInstructionLenChecked bytes idx = .ok len) :
    quotientOpcodeByteLen op = some len := by
  unfold quotientByteInstructionLenChecked at h
  obtain ⟨op', hop, h2⟩ := peel_bind h
  have hop_eq : op' = op := Except.ok.inj (hop.symm.trans h1)
  rw [hop_eq] at h2
  have hP' : (op == qOpRunAddMulMemMemConstU8) = false := by simp [hP]
  have hL' : (op == qOpRunAddMulConstU8MemU16) = false := by simp [hL]
  have hS' : (op == qOpAffineSum) = false := by simp [hS]
  have hM' : (op == qOpModarith7) = false := by simp [hM]
  rw [hP', hL', hS', hM'] at h2
  simp (config := {decide := true}) only [reduceIte] at h2
  cases hq : quotientOpcodeByteLen op with
  | none => rw [hq] at h2; cases h2
  | some l =>
      rw [hq] at h2
      simp only [Bind.bind, Except.bind] at h2
      obtain ⟨_u, _hu, h3⟩ := peel_bind h2
      rcases Except.ok.inj h3 with ⟨rfl⟩
      rfl

/-- **THE VALIDATOR-SIDE HALF, STATIC ARMS.** A table opcode's CHECKED width is its table width, so it is
    also what the UNCHECKED walker reports. This is the bridge the walk needed: the requirement names the
    checked decoder and the interpreter-side package names the unchecked walker. -/
theorem dec_width_of_table {bytes : List Nat} {idx op len w : Nat}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (op, len))
    (hw : quotientOpcodeByteLen op = some w) : len = w := by
  obtain ⟨hop, hlen⟩ := decode_ok_parts hdec
  have hP : op ≠ qOpRunAddMulMemMemConstU8 := by
    intro t; rw [t] at hw; rw [byteLen_none_runP] at hw; cases hw
  have hL : op ≠ qOpRunAddMulConstU8MemU16 := by
    intro t; rw [t] at hw; rw [byteLen_none_runL] at hw; cases hw
  have hS : op ≠ qOpAffineSum := by
    intro t; rw [t] at hw; rw [byteLen_none_affineSum] at hw; cases hw
  have hM : op ≠ qOpModarith7 := by
    intro t; rw [t] at hw; rw [byteLen_none_modarith7] at hw; cases hw
  have := lenChecked_table (byteAtPanic_line hop) hP hL hS hM hlen
  rw [hw] at this
  exact (Option.some.inj this).symm

theorem dec_width_pushConst {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPushConst, len)) : len = 3 :=
  dec_width_of_table h rfl

theorem cursor_pushConst {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPushConst, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConst stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPushConst :: rest) 0 = .ok len := by
    rw [dec_width_pushConst hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPushConst (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_pushMemLiteral {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemLiteral, len)) : len = 5 :=
  dec_width_of_table h rfl

theorem cursor_pushMemLiteral {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemLiteral, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemLiteral stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPushMemLiteral :: rest) 0 = .ok len := by
    rw [dec_width_pushMemLiteral hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPushMemLiteral (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_pushMemToken {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemToken, len)) : len = 2 :=
  dec_width_of_table h rfl

theorem cursor_pushMemToken {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemToken, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemToken stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPushMemToken :: rest) 0 = .ok len := by
    rw [dec_width_pushMemToken hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPushMemToken (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_pushMemTokenOffset {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemTokenOffset, len)) : len = 6 :=
  dec_width_of_table h rfl

theorem cursor_pushMemTokenOffset {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemTokenOffset, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemTokenOffset stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPushMemTokenOffset :: rest) 0 = .ok len := by
    rw [dec_width_pushMemTokenOffset hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPushMemTokenOffset (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_pushMemU16 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemU16, len)) : len = 3 :=
  dec_width_of_table h rfl

theorem cursor_pushMemU16 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPushMemU16, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushMemU16 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPushMemU16 :: rest) 0 = .ok len := by
    rw [dec_width_pushMemU16 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPushMemU16 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_add {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAdd, len)) : len = 1 :=
  dec_width_of_table h rfl

theorem cursor_add {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAdd, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAdd stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAdd :: rest) 0 = .ok len := by
    rw [dec_width_add hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAdd (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_mul {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpMul, len)) : len = 1 :=
  dec_width_of_table h rfl

theorem cursor_mul {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpMul, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMul stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpMul :: rest) 0 = .ok len := by
    rw [dec_width_mul hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpMul (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_neg {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpNeg, len)) : len = 1 :=
  dec_width_of_table h rfl

theorem cursor_neg {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpNeg, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpNeg stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpNeg :: rest) 0 = .ok len := by
    rw [dec_width_neg hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpNeg (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_pushConstU8 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPushConstU8, len)) : len = 2 :=
  dec_width_of_table h rfl

theorem cursor_pushConstU8 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPushConstU8, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPushConstU8 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPushConstU8 :: rest) 0 = .ok len := by
    rw [dec_width_pushConstU8 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPushConstU8 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_addConstU8 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAddConstU8, len)) : len = 2 :=
  dec_width_of_table h rfl

theorem cursor_addConstU8 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAddConstU8, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddConstU8 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAddConstU8 :: rest) 0 = .ok len := by
    rw [dec_width_addConstU8 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAddConstU8 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_mulConstU8 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpMulConstU8, len)) : len = 2 :=
  dec_width_of_table h rfl

theorem cursor_mulConstU8 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpMulConstU8, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulConstU8 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpMulConstU8 :: rest) 0 = .ok len := by
    rw [dec_width_mulConstU8 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpMulConstU8 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_addConst {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAddConst, len)) : len = 3 :=
  dec_width_of_table h rfl

theorem cursor_addConst {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAddConst, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddConst stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAddConst :: rest) 0 = .ok len := by
    rw [dec_width_addConst hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAddConst (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_mulConst {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpMulConst, len)) : len = 3 :=
  dec_width_of_table h rfl

theorem cursor_mulConst {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpMulConst, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulConst stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpMulConst :: rest) 0 = .ok len := by
    rw [dec_width_mulConst hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpMulConst (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_addMemU16 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMemU16, len)) : len = 3 :=
  dec_width_of_table h rfl

theorem cursor_addMemU16 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMemU16, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMemU16 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAddMemU16 :: rest) 0 = .ok len := by
    rw [dec_width_addMemU16 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAddMemU16 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_mulMemU16 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpMulMemU16, len)) : len = 3 :=
  dec_width_of_table h rfl

theorem cursor_mulMemU16 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpMulMemU16, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpMulMemU16 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpMulMemU16 :: rest) 0 = .ok len := by
    rw [dec_width_mulMemU16 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpMulMemU16 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_addMulMemMem {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMulMemMem, len)) : len = 5 :=
  dec_width_of_table h rfl

theorem cursor_addMulMemMem {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMulMemMem, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMulMemMem stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAddMulMemMem :: rest) 0 = .ok len := by
    rw [dec_width_addMulMemMem hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAddMulMemMem (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_pow5 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpPow5, len)) : len = 1 :=
  dec_width_of_table h rfl

theorem cursor_pow5 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpPow5, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpPow5 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpPow5 :: rest) 0 = .ok len := by
    rw [dec_width_pow5 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpPow5 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_addMulMemMemConstU8 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMulMemMemConstU8, len)) : len = 6 :=
  dec_width_of_table h rfl

theorem cursor_addMulMemMemConstU8 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMulMemMemConstU8, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMulMemMemConstU8 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAddMulMemMemConstU8 :: rest) 0 = .ok len := by
    rw [dec_width_addMulMemMemConstU8 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAddMulMemMemConstU8 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_addMulConstU8MemU16 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMulConstU8MemU16, len)) : len = 4 :=
  dec_width_of_table h rfl

theorem cursor_addMulConstU8MemU16 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAddMulConstU8MemU16, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpAddMulConstU8MemU16 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpAddMulConstU8MemU16 :: rest) 0 = .ok len := by
    rw [dec_width_addMulConstU8MemU16 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpAddMulConstU8MemU16 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_lin7 {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpLin7, len)) : len = 22 :=
  dec_width_of_table h rfl

theorem cursor_lin7 {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpLin7, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpLin7 :: rest) 0 = .ok len := by
    rw [dec_width_lin7 hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpLin7 (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_bilin7Row {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpBilin7Row, len)) : len = 24 :=
  dec_width_of_table h rfl

theorem cursor_bilin7Row {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpBilin7Row, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpBilin7Row :: rest) 0 = .ok len := by
    rw [dec_width_bilin7Row hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpBilin7Row (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm

theorem dec_width_bilin7Pairwise {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpBilin7Pairwise, len)) : len = 18 :=
  dec_width_of_table h rfl

theorem cursor_bilin7Pairwise {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpBilin7Pairwise, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨rest, hdrop⟩ := decode_ok_drop hdec
  have hlen : quotientOpLen (qOpBilin7Pairwise :: rest) 0 = .ok len := by
    rw [dec_width_bilin7Pairwise hdec]
    rfl
  exact (evalQuotientIdentityStep_consumed_agrees_at_22 qOpBilin7Pairwise (by tauto) bytes idx rest hdrop
    consts stack mem s len hstep hlen).symm


/-! ### 3. The three DYNAMIC-width arms: RUN x2 and AFFINE_SUM -/

theorem checkedQuotientLenMul_ok (lhs rhs op idx : Nat) :
    checkedQuotientLenMul lhs rhs op idx = .ok (lhs * rhs) := by
  unfold checkedQuotientLenMul
  have key : (lhs != 0 && lhs * rhs / lhs != rhs) = false := by
    by_cases h0 : lhs = 0
    · subst h0
      simp
    · have hd : lhs * rhs / lhs = rhs := Nat.mul_div_cancel_left rhs (Nat.pos_of_ne_zero h0)
      simp [hd]
  simp (config := {decide := true}) only [key, reduceIte]

theorem checkedQuotientLenAdd_ok (lhs rhs op idx : Nat) :
    checkedQuotientLenAdd lhs rhs op idx = .ok (lhs + rhs) := by
  unfold checkedQuotientLenAdd
  have key : (lhs + rhs < lhs) = false := by simp
  simp (config := {decide := true}) only [key, reduceIte]


theorem lenChecked_runP {bytes : List Nat} {idx len : Nat}
    (h1 : byteAtPanic bytes idx 2539 = .ok qOpRunAddMulMemMemConstU8)
    (h : quotientByteInstructionLenChecked bytes idx = .ok len) :
    ∃ count : Nat, QuotientValidator.readU16 bytes (idx + 1) = .ok count ∧
      len = 1 + quotientVmByteU16Bytes + count * (2 * quotientVmByteU16Bytes + 1) := by
  unfold quotientByteInstructionLenChecked at h
  obtain ⟨op', hop, h2⟩ := peel_bind h
  have hop_eq : op' = qOpRunAddMulMemMemConstU8 := Except.ok.inj (hop.symm.trans h1)
  rw [hop_eq] at h2
  simp (config := {decide := true}) only [reduceIte] at h2
  obtain ⟨_u, _hu, h3⟩ := peel_bind h2
  obtain ⟨count, hcount, h4⟩ := peel_bind h3
  cases hc : (count == 0) with
  | true => rw [hc] at h4; simp (config := {decide := true}) only [reduceIte] at h4; cases h4
  | false =>
      rw [hc] at h4
      simp (config := {decide := true}) only [reduceIte] at h4
      obtain ⟨_v, _hv, h5⟩ := peel_bind h4
      obtain ⟨pl, hpl, h6⟩ := peel_bind h5
      obtain ⟨l2, hl2, h7⟩ := peel_bind h6
      cases hq : requireQuotientBytes bytes idx l2 "instruction" with
      | error e => rw [hq] at h7; cases h7
      | ok u =>
          rw [hq] at h7
          rcases Except.ok.inj h7 with ⟨rfl⟩
          rw [checkedQuotientLenMul_ok] at hpl
          rcases hpl with ⟨rfl⟩
          rw [checkedQuotientLenAdd_ok] at hl2
          rcases hl2 with ⟨rfl⟩
          exact ⟨count, hcount, rfl⟩

theorem lenChecked_runL {bytes : List Nat} {idx len : Nat}
    (h1 : byteAtPanic bytes idx 2539 = .ok qOpRunAddMulConstU8MemU16)
    (h : quotientByteInstructionLenChecked bytes idx = .ok len) :
    ∃ count : Nat, QuotientValidator.readU16 bytes (idx + 1) = .ok count ∧
      len = 1 + quotientVmByteU16Bytes + count * (quotientVmByteU16Bytes + 1) := by
  unfold quotientByteInstructionLenChecked at h
  obtain ⟨op', hop, h2⟩ := peel_bind h
  have hop_eq : op' = qOpRunAddMulConstU8MemU16 := Except.ok.inj (hop.symm.trans h1)
  rw [hop_eq] at h2
  simp (config := {decide := true}) only [reduceIte] at h2
  obtain ⟨_u, _hu, h3⟩ := peel_bind h2
  obtain ⟨count, hcount, h4⟩ := peel_bind h3
  cases hc : (count == 0) with
  | true => rw [hc] at h4; simp (config := {decide := true}) only [reduceIte] at h4; cases h4
  | false =>
      rw [hc] at h4
      simp (config := {decide := true}) only [reduceIte] at h4
      obtain ⟨_v, _hv, h5⟩ := peel_bind h4
      obtain ⟨pl, hpl, h6⟩ := peel_bind h5
      obtain ⟨l2, hl2, h7⟩ := peel_bind h6
      cases hq : requireQuotientBytes bytes idx l2 "instruction" with
      | error e => rw [hq] at h7; cases h7
      | ok u =>
          rw [hq] at h7
          rcases Except.ok.inj h7 with ⟨rfl⟩
          rw [checkedQuotientLenMul_ok] at hpl
          rcases hpl with ⟨rfl⟩
          rw [checkedQuotientLenAdd_ok] at hl2
          rcases hl2 with ⟨rfl⟩
          exact ⟨count, hcount, rfl⟩

theorem lenChecked_affineSum {bytes : List Nat} {idx len : Nat}
    (h1 : byteAtPanic bytes idx 2539 = .ok qOpAffineSum)
    (h : quotientByteInstructionLenChecked bytes idx = .ok len) :
    ∃ lin prod : Nat, QuotientValidator.readU16 bytes (idx + 1) = .ok lin ∧
      QuotientValidator.readU16 bytes (idx + 3) = .ok prod ∧
      len = 1 + 2 * quotientVmByteU16Bytes
        + (lin * (quotientVmByteU16Bytes + 1) + prod * (2 * quotientVmByteU16Bytes + 1)) := by
  unfold quotientByteInstructionLenChecked at h
  obtain ⟨op', hop, h2⟩ := peel_bind h
  have hop_eq : op' = qOpAffineSum := Except.ok.inj (hop.symm.trans h1)
  rw [hop_eq] at h2
  simp (config := {decide := true}) only [reduceIte] at h2
  obtain ⟨la, hla, h3⟩ := peel_bind h2
  cases hq : requireQuotientBytes bytes idx la "instruction" with
  | error e => rw [hq] at h3; cases h3
  | ok u =>
      rw [hq] at h3
      rcases Except.ok.inj h3 with ⟨rfl⟩
      unfold quotientAffineSumOpLenChecked at hla
      obtain ⟨_u, _hu, h4⟩ := peel_bind hla
      obtain ⟨lin, hlin, h5⟩ := peel_bind h4
      obtain ⟨prod, hprod, h6⟩ := peel_bind h5
      cases hz : (lin == 0 || prod == 0) with
      | true => rw [hz] at h6; simp (config := {decide := true}) only [reduceIte] at h6; cases h6
      | false =>
          rw [hz] at h6
          simp (config := {decide := true}) only [reduceIte] at h6
          simp only [checkedQuotientLenMul_ok, checkedQuotientLenAdd_ok, Bind.bind, Except.bind] at h6
          rcases Except.ok.inj h6 with ⟨rfl⟩
          have hconv : idx + 1 + quotientVmByteU16Bytes = idx + 3 := by
            unfold quotientVmByteU16Bytes
            omega
          rw [hconv] at hprod
          refine ⟨lin, prod, hlin, hprod, ?_⟩
          rfl

theorem cursor_runP {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpRunAddMulMemMemConstU8, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulMemMemConstU8 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨hop, hlen⟩ := decode_ok_parts hdec
  obtain ⟨rest, hdrop⟩ := byteAtPanic_ok_cons hop
  obtain ⟨count, hcount, rfl⟩ :=
    lenChecked_runP (by rw [byteAtPanic_line hop]) hlen
  have hr : QuotientValidator.readU16 (qOpRunAddMulMemMemConstU8 :: rest) 1 = .ok count := by
    have h1 : (qOpRunAddMulMemMemConstU8 :: rest).drop 1 = bytes.drop (idx + 1) := by
      rw [← hdrop, List.drop_drop]
    unfold QuotientValidator.readU16
    rw [h1]
    exact hcount
  have hlen' : quotientOpLen (qOpRunAddMulMemMemConstU8 :: rest) 0 =
      .ok (1 + quotientVmByteU16Bytes + count * (2 * quotientVmByteU16Bytes + 1)) := by
    unfold quotientOpLen
    simp only [Bind.bind, Except.bind, byteAtPanic, List.drop_zero, Nat.zero_add, hr]
    simp (config := {decide := true}) only [reduceIte]
  exact (consumed_agrees_at_runAddMulMemMemConstU8 bytes idx rest hdrop consts stack mem s
    (1 + quotientVmByteU16Bytes + count * (2 * quotientVmByteU16Bytes + 1)) hstep hlen').symm


theorem cursor_runL {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpRunAddMulConstU8MemU16, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulConstU8MemU16 stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨hop, hlen⟩ := decode_ok_parts hdec
  obtain ⟨rest, hdrop⟩ := byteAtPanic_ok_cons hop
  obtain ⟨count, hcount, rfl⟩ :=
    lenChecked_runL (by rw [byteAtPanic_line hop]) hlen
  have hr : QuotientValidator.readU16 (qOpRunAddMulConstU8MemU16 :: rest) 1 = .ok count := by
    have h1 : (qOpRunAddMulConstU8MemU16 :: rest).drop 1 = bytes.drop (idx + 1) := by
      rw [← hdrop, List.drop_drop]
    unfold QuotientValidator.readU16
    rw [h1]
    exact hcount
  have hlen' : quotientOpLen (qOpRunAddMulConstU8MemU16 :: rest) 0 =
      .ok (1 + quotientVmByteU16Bytes + count * (quotientVmByteU16Bytes + 1)) := by
    unfold quotientOpLen
    simp only [Bind.bind, Except.bind, byteAtPanic, List.drop_zero, Nat.zero_add, hr]
    simp (config := {decide := true}) only [reduceIte]
  exact (consumed_agrees_at_runAddMulConstU8MemU16 bytes idx rest hdrop consts stack mem s
    (1 + quotientVmByteU16Bytes + count * (quotientVmByteU16Bytes + 1)) hstep hlen').symm


theorem cursor_affineSum {bytes : List Nat} {consts : List Word256} {idx len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (qOpAffineSum, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAffineSum stack mem = .ok s) :
    len = s.consumed := by
  obtain ⟨hop, hlen⟩ := decode_ok_parts hdec
  obtain ⟨rest, hdrop⟩ := byteAtPanic_ok_cons hop
  obtain ⟨lin, prod, hlin, hprod, rfl⟩ :=
    lenChecked_affineSum (by rw [byteAtPanic_line hop]) hlen
  have h1 : (qOpAffineSum :: rest).drop 1 = bytes.drop (idx + 1) := by
    rw [← hdrop, List.drop_drop]
  have h3 : (qOpAffineSum :: rest).drop 3 = bytes.drop (idx + 3) := by
    rw [← hdrop, List.drop_drop]
  have hr1 : QuotientValidator.readU16 (qOpAffineSum :: rest) 1 = .ok lin := by
    unfold QuotientValidator.readU16
    rw [h1]
    exact hlin
  have hr3 : QuotientValidator.readU16 (qOpAffineSum :: rest) 3 = .ok prod := by
    unfold QuotientValidator.readU16
    rw [h3]
    exact hprod
  have hlen' : quotientOpLen (qOpAffineSum :: rest) 0 = .ok (1 + 2 * quotientVmByteU16Bytes
      + (lin * (quotientVmByteU16Bytes + 1) + prod * (2 * quotientVmByteU16Bytes + 1))) := by
    unfold quotientOpLen quotientAffineSumOpLen
    simp only [Bind.bind, Except.bind, byteAtPanic, List.drop_zero, Nat.zero_add, hr1, hr3]
    simp (config := {decide := true}) only [reduceIte]
    congr 1
    ring
  exact (consumed_agrees_at_affineSum bytes idx rest hdrop consts stack mem s
    (1 + 2 * quotientVmByteU16Bytes
      + (lin * (quotientVmByteU16Bytes + 1) + prod * (2 * quotientVmByteU16Bytes + 1)))
    hstep hlen').symm

/-! ### 4. The roster and the discharge of 'PG_stackWalkCursor' -/

/-- The 25 identity arms covered: QvmShift's own general-cursor roster of 22, plus the two RUN arms and
    AFFINE_SUM, whose widths the decoder DECODES from the operand bytes rather than reading from the table. -/
def cursorArm25 (op : Nat) : Prop :=
  op = qOpPushConst
  \/ op = qOpPushMemLiteral
  \/ op = qOpPushMemToken
  \/ op = qOpPushMemTokenOffset
  \/ op = qOpPushMemU16
  \/ op = qOpAdd
  \/ op = qOpMul
  \/ op = qOpNeg
  \/ op = qOpPushConstU8
  \/ op = qOpAddConstU8
  \/ op = qOpMulConstU8
  \/ op = qOpAddConst
  \/ op = qOpMulConst
  \/ op = qOpAddMemU16
  \/ op = qOpMulMemU16
  \/ op = qOpAddMulMemMem
  \/ op = qOpPow5
  \/ op = qOpAddMulMemMemConstU8
  \/ op = qOpAddMulConstU8MemU16
  \/ op = qOpLin7
  \/ op = qOpBilin7Row
  \/ op = qOpBilin7Pairwise
  \/ op = qOpRunAddMulMemMemConstU8
  \/ op = qOpRunAddMulConstU8MemU16
  \/ op = qOpAffineSum

/-- **THE DISCHARGE OF QFIX'S O4, 25 ARMS.** 'PG_stackWalkCursor' as published, for every arm in the
    roster (25 of the 26 identity arms), at a general cursor. No hypothesis was added to a row, to 'ValidV3', to a bundle or to the
    root; the two hypotheses are the two the Prop itself states. -/
theorem pG_stackWalkCursor_of_cursorArm25 {bytes : List Nat} {consts : List Word256}
    {idx op len : Nat} {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hop : cursorArm25 op) :
    Midfall.Lowering.QuotientStackInv.PG_stackWalkCursor bytes consts idx op len stack mem s := by
  intro hdec hstep
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h) <;> subst h
  · exact cursor_pushConst hdec hstep
  · exact cursor_pushMemLiteral hdec hstep
  · exact cursor_pushMemToken hdec hstep
  · exact cursor_pushMemTokenOffset hdec hstep
  · exact cursor_pushMemU16 hdec hstep
  · exact cursor_add hdec hstep
  · exact cursor_mul hdec hstep
  · exact cursor_neg hdec hstep
  · exact cursor_pushConstU8 hdec hstep
  · exact cursor_addConstU8 hdec hstep
  · exact cursor_mulConstU8 hdec hstep
  · exact cursor_addConst hdec hstep
  · exact cursor_mulConst hdec hstep
  · exact cursor_addMemU16 hdec hstep
  · exact cursor_mulMemU16 hdec hstep
  · exact cursor_addMulMemMem hdec hstep
  · exact cursor_pow5 hdec hstep
  · exact cursor_addMulMemMemConstU8 hdec hstep
  · exact cursor_addMulConstU8MemU16 hdec hstep
  · exact cursor_lin7 hdec hstep
  · exact cursor_bilin7Row hdec hstep
  · exact cursor_bilin7Pairwise hdec hstep
  · exact cursor_runP hdec hstep
  · exact cursor_runL hdec hstep
  · exact cursor_affineSum hdec hstep


/-! ### 5. THE WALK: the cursor equation lets the emitter drive the reference's walk in the VALIDATOR's
    cursor arithmetic -/

/-- **THE CURSOR EQUATION FOR THE ROSTER.** The same statement as 'pG_stackWalkCursor_of_cursorArm25' in
    equation form, for the composition lemmas below. -/
theorem cursor_of_cursorArm25 {bytes : List Nat} {consts : List Word256} {idx op len : Nat}
    {stack : List QVMFr} {mem : QuotientRefMemory} {s : IdentityStep}
    (hop : cursorArm25 op)
    (hdec : decodeByteQuotientInstruction bytes idx = .ok (op, len))
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok s) :
    len = s.consumed :=
  pG_stackWalkCursor_of_cursorArm25 hop hdec hstep

/-- **DEPTH'S CARRIED HYPOTHESIS IS NOW DERIVABLE, NOT GIVEN.** 'QvmDepth.step_noUnderflow_of_validator_fold'
    ('QvmDepth.lean:1146') takes 'hh : bytes.getD idx 0 = op' as an explicit hypothesis because that card
    declined to prove it from the decoder ('QvmDepth.lean:49-51'). 'FoldDepth' carries a
    'decodeByteQuotientInstruction' equation at its target, so 'decode_ok_getD' supplies 'hh' outright: the
    depth composition and the cursor composition now run off the SAME decoder fact, and neither needs the
    opcode equation handed to it. -/
theorem foldDepth_getD {bytes : List Nat} {start target op d : Nat}
    (h : FoldDepth bytes start target op d) :
    bytes.getD target 0 = op := by
  obtain ⟨_len, _d', _ms', hdec, _heff⟩ := foldDepth_certifies h
  exact decode_ok_getD hdec

/-- **AXIS 5 ('PG_stepProgress_at') DISCHARGED FROM DECODED STEPS.** IDSEG's progress axis asks the
    emitter to carry its invariant across 'idx + st.consumed' - the INTERPRETER's cursor. The emitter does
    not know that number: it knows the width its own encoder wrote, which is what the validator's decoder
    reads back. This is the lemma that closes the gap: a step leg stated in the DECODED cursor ('idx + len')
    carries 'PG_stepProgress_at', because the cursor equation says the two successors are the same number.
    'decode_ok_getD' is what makes the opcode the walk reaches and the opcode the decoder names one fact
    rather than a hypothesis - the equation DEPTH left open. -/
theorem PG_stepProgress_at_of_decoded_steps (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hstep : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ op len s, decodeByteQuotientInstruction bytes idx = .ok (op, len) ∧
          cursorArm25 op ∧ stepAt bytes consts idx stack mem = .ok s ∧
            P (idx + len) s.stack s.mem) :
    PG_stepProgress_at bytes consts P := by
  intro idx stack mem st hidx hP hst
  obtain ⟨op, len, s, hdec, hop, hst', hP'⟩ := hstep idx stack mem hidx hP
  have hh : bytes.getD idx 0 = op := decode_ok_getD hdec
  have hse : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok s := by
    rw [← hh, ← stepAt_def]
    exact hst'
  have hse' : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok st := by
    rw [← hh, ← stepAt_def]
    exact hst
  have hseq : s = st := Except.ok.inj (hse.symm.trans hse')
  subst hseq
  rw [← cursor_of_cursorArm25 hop hdec hse]
  exact hP'

/-- **THE WHOLE SEGMENT ITERATES ON THE DECODED CURSOR.** IDSEG's second induction, with its step leg
    supplied in the validator's vocabulary: at every reachable cursor the decoder names a covered arm and
    width, the reference's step succeeds, and the invariant holds at the DECODED successor. Then the walk
    reaches the end of the segment without faulting, at any fuel that covers the distance. This is the
    precise answer to 'can the walk iterate a whole segment for the arms covered': YES, modulo the emitter
    supplying its own cursor sequence, which is the only thing the SHAPE and INIT/TERM axes still ask for. -/
theorem loop_ok_of_decoded_steps (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop)
    (hstep : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ op len s, decodeByteQuotientInstruction bytes idx = .ok (op, len) ∧
          cursorArm25 op ∧ stepAt bytes consts idx stack mem = .ok s ∧
            P (idx + len) s.stack s.mem) :
    ∀ fuel idx stack mem, bytes.length - idx ≤ fuel → P idx stack mem →
        ∃ fin s m, idx ≤ fin ∧ ¬ fin < bytes.length ∧
          Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel idx stack mem = .ok (s, m) ∧
          P fin s m := by
  intro fuel
  refine loop_ok_of_walk bytes consts P ?_ fuel
  intro idx stack mem hidx hP
  obtain ⟨op, len, s, hdec, hop, hst, hP'⟩ := hstep idx stack mem hidx hP
  have hh : bytes.getD idx 0 = op := decode_ok_getD hdec
  have hse : Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok s := by
    rw [← hh, ← stepAt_def]
    exact hst
  refine ⟨s, hst, ?_⟩
  rw [← cursor_of_cursorArm25 hop hdec hse]
  exact hP'

/-! ### 6. Non-vacuity: IDSEG's own witness segment -/

/-- The three decoded steps of IDSEG's five-byte witness: two 'PUSH_CONST_U8' and an 'ADD'. Computed, not
    assumed - the widths are what the CHECKED decoder reports, and they are the widths the reference's
    'consumed' field reports (section 3). -/
theorem demo_dec_0 : decodeByteQuotientInstruction demoSegment 0 = .ok (qOpPushConstU8, 2) := rfl
theorem demo_dec_2 : decodeByteQuotientInstruction demoSegment 2 = .ok (qOpPushConstU8, 2) := rfl
theorem demo_dec_4 : decodeByteQuotientInstruction demoSegment 4 = .ok (qOpAdd, 1) := rfl

/-- **THE AXIS DISCHARGED FOR A REAL SEGMENT.** IDSEG's own witness and its own 'demoP': the published
    'PG_stackWalkCursor' holds at every cursor the walk reaches. The axis is therefore not merely named
    for a roster - it has a proof for a concrete emitted-shape segment, exactly as DEPTH landed
    'demoPG_stepDepth_at'. -/
theorem demoPG_stackWalkCursor (idx op len : Nat) (stack : List QVMFr)
    (mem : QuotientRefMemory) (s : IdentityStep) (hidx : idx < demoSegment.length)
    (hP : demoP idx stack mem) :
    Midfall.Lowering.QuotientStackInv.PG_stackWalkCursor demoSegment demoConsts idx op len stack mem s := by
  intro hdec hstep
  rw [demo_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs
    have h20 : (Except.ok (op, len) : Midfall.Generator.QuotientValidator.VResult (Nat × Nat)) = Except.ok (qOpPushConstU8, 2) := by rw [← hdec, demo_dec_0]
    rcases Except.ok.inj h20 with ⟨rfl, rfl⟩
    exact cursor_pushConstU8 hdec hstep
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    have h22 : (Except.ok (op, len) : Midfall.Generator.QuotientValidator.VResult (Nat × Nat)) = Except.ok (qOpPushConstU8, 2) := by rw [← hdec, demo_dec_2]
    rcases Except.ok.inj h22 with ⟨rfl, rfl⟩
    exact cursor_pushConstU8 hdec hstep
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    have h24 : (Except.ok (op, len) : Midfall.Generator.QuotientValidator.VResult (Nat × Nat)) = Except.ok (qOpAdd, 1) := by rw [← hdec, demo_dec_4]
    rcases Except.ok.inj h24 with ⟨rfl, rfl⟩
    exact cursor_add hdec hstep
  · omega

/-- THE WITNESS'S STEP LEG IN THE VALIDATOR'S VOCABULARY: cursor sequence 0, 2, 4, 5 with the decoded
    widths 2, 2, 1 - the same numbers the reference's 'consumed' field reports, by section 3. -/
theorem demo_decoded_steps : ∀ idx stack mem, idx < demoSegment.length → demoP idx stack mem →
    ∃ op len s, decodeByteQuotientInstruction demoSegment idx = .ok (op, len) ∧
      cursorArm25 op ∧ stepAt demoSegment demoConsts idx stack mem = .ok s ∧
        demoP (idx + len) s.stack s.mem := by
  intro idx stack mem hidx hP
  rw [demo_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs
    refine ⟨qOpPushConstU8, 2, _, demo_dec_0, by tauto, demo_step0 mem, ?_⟩
    show demoP 2 [0] mem
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    refine ⟨qOpPushConstU8, 2, _, demo_dec_2, by tauto, demo_step1 [a] mem, ?_⟩
    show demoP 4 (1 :: [a]) mem
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp⟩))
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    refine ⟨qOpAdd, 1, _, demo_dec_4, by tauto, demo_step2 a b mem, ?_⟩
    show demoP 5 [qvmFrAdd b a] mem
    exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))
  · omega

/-- **THE WALK ITERATES THE WHOLE WITNESS SEGMENT ON THE DECODED CURSOR**: the reference's loop reaches a
    cursor at or past the end of the segment and returns '.ok', and the induction that got it there is
    'loop_ok_of_decoded_steps' - i.e. it came from the CURSOR EQUATION, not from evaluating the
    interpreter by hand. 'demo_decoded_widths_sum' pins that the three decoded widths are exactly the
    segment's five bytes, so the walk stops at cursor 5. -/
theorem demo_walk_iterates_of_decoded :
    ∃ fin s m, 5 ≤ fin ∧
      Midfall.Generator.evalQuotientIdentityLoop.go demoSegment demoConsts 5 0 ([] : List QVMFr) demoMem
        = .ok (s, m) := by
  obtain ⟨fin, s, m, _hle, hout, hgo, _hP⟩ :=
    loop_ok_of_decoded_steps demoSegment demoConsts demoP demo_decoded_steps 5 0 [] demoMem
      (by rw [demo_len]) (Or.inl ⟨rfl, rfl⟩)
  rw [demo_len] at hout
  exact ⟨fin, s, m, by omega, hgo⟩

/-- The three decoded widths of the witness add up to the segment's length: the walk's cursor sequence is
    0, 2, 4, 5 and it stops exactly at the end. -/
theorem demo_decoded_widths_sum : 2 + 2 + 1 = demoSegment.length := by
  rw [demo_len]

/-! ### 7. What is still open, named -/

/-- **MODARITH7 - THE ONE IDENTITY ARM NOT COVERED, AND WHY IT IS NOT THE LIMB DECISION.** The three other
    limb arms (LIN7, BILIN7_ROW, BILIN7_PAIRWISE) ARE covered here: their widths are static table entries
    (22, 24, 18) and the reference's own limb forms advance by exactly those amounts with no template table
    in sight, so 'PG_limbCountAgrees' does not gate the cursor axis - the exclusion IDSEG and DEPTH carried
    for the limb family is VACUOUS on this axis too, and this card says so rather than assuming it.
    MODARITH7 is excluded for a DIFFERENT and genuine reason: it is the only identity arm with no
    'step_shift_*' congruence anywhere in the tree (QvmShift.lean:2810
    'PG_stepNoRF_validated_shif2_modarith7_shift', and its family-2 twin
    'PG_stepNoRF_validated_shif2_modarith7_width'), so there is no general-cursor width agreement to
    compose the bridge with. Its header's branch points are computed from a flag byte read AT the cursor,
    which is what the missing congruence has to transport. Exact goal state, in the published Prop's own
    vocabulary: -/
def PG_stackWalkCursor_modarith7 : Prop :=
  ∀ (bytes : List Nat) (consts : List Word256) (idx len : Nat) (stack : List QVMFr)
    (mem : QuotientRefMemory) (s : IdentityStep),
    Midfall.Lowering.QuotientStackInv.PG_stackWalkCursor bytes consts idx qOpModarith7 len stack mem s

/-- **WHAT IS ESTABLISHED FOR MODARITH7, AND WHAT IS NOT.** The opcode equation below IS proved for the
    arm - 'decode_ok_getD' is arm-independent, so the decoder's head read is settled for all 26 arms and
    the validator-side half of the composition needs no more for MODARITH7 than for any other. What is NOT
    proved here is the WIDTH BRIDGE for MODARITH7: its checked branch threads ten 'advanceQuotientCursor'
    steps and five 'checkedQuotientLenMul' blocks against the unchecked 'quotientModarith7OpLen', and while
    each individual helper cannot fail on 'Nat' (this card proves 'checkedQuotientLenMul_ok' and
    'checkedQuotientLenAdd_ok'), the two MODARITH7 length functions were NOT shown to telescope to the same
    number, and this card does not claim they were. So the arm needs BOTH halves: the validator-side bridge
    for its counted blocks and the interpreter-side 'consumed_agrees_*' congruence QvmShift names as open.
    'PG_stackWalkCursor_modarith7' above is the whole obligation, not just its interpreter half. -/
theorem modarith7_decode_ok_getD {bytes : List Nat} {idx len : Nat}
    (h : decodeByteQuotientInstruction bytes idx = .ok (qOpModarith7, len)) :
    bytes.getD idx 0 = qOpModarith7 :=
  decode_ok_getD h

-- EVERY CURSOR LEMMA, AXIOMS AND CONE: the 25 covered arms, one line each.
#print axioms Midfall.Lowering.QvmCursor.cursor_pushConst
#print axioms Midfall.Lowering.QvmCursor.cursor_pushMemLiteral
#print axioms Midfall.Lowering.QvmCursor.cursor_pushMemToken
#print axioms Midfall.Lowering.QvmCursor.cursor_pushMemTokenOffset
#print axioms Midfall.Lowering.QvmCursor.cursor_pushMemU16
#print axioms Midfall.Lowering.QvmCursor.cursor_add
#print axioms Midfall.Lowering.QvmCursor.cursor_mul
#print axioms Midfall.Lowering.QvmCursor.cursor_neg
#print axioms Midfall.Lowering.QvmCursor.cursor_pushConstU8
#print axioms Midfall.Lowering.QvmCursor.cursor_addConstU8
#print axioms Midfall.Lowering.QvmCursor.cursor_mulConstU8
#print axioms Midfall.Lowering.QvmCursor.cursor_addConst
#print axioms Midfall.Lowering.QvmCursor.cursor_mulConst
#print axioms Midfall.Lowering.QvmCursor.cursor_addMemU16
#print axioms Midfall.Lowering.QvmCursor.cursor_mulMemU16
#print axioms Midfall.Lowering.QvmCursor.cursor_addMulMemMem
#print axioms Midfall.Lowering.QvmCursor.cursor_pow5
#print axioms Midfall.Lowering.QvmCursor.cursor_addMulMemMemConstU8
#print axioms Midfall.Lowering.QvmCursor.cursor_addMulConstU8MemU16
#print axioms Midfall.Lowering.QvmCursor.cursor_lin7
#print axioms Midfall.Lowering.QvmCursor.cursor_bilin7Row
#print axioms Midfall.Lowering.QvmCursor.cursor_bilin7Pairwise
#print axioms Midfall.Lowering.QvmCursor.cursor_runP
#print axioms Midfall.Lowering.QvmCursor.cursor_runL
#print axioms Midfall.Lowering.QvmCursor.cursor_affineSum
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pushConst
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pushMemLiteral
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pushMemToken
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pushMemTokenOffset
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pushMemU16
#cone_sorries Midfall.Lowering.QvmCursor.cursor_add
#cone_sorries Midfall.Lowering.QvmCursor.cursor_mul
#cone_sorries Midfall.Lowering.QvmCursor.cursor_neg
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pushConstU8
#cone_sorries Midfall.Lowering.QvmCursor.cursor_addConstU8
#cone_sorries Midfall.Lowering.QvmCursor.cursor_mulConstU8
#cone_sorries Midfall.Lowering.QvmCursor.cursor_addConst
#cone_sorries Midfall.Lowering.QvmCursor.cursor_mulConst
#cone_sorries Midfall.Lowering.QvmCursor.cursor_addMemU16
#cone_sorries Midfall.Lowering.QvmCursor.cursor_mulMemU16
#cone_sorries Midfall.Lowering.QvmCursor.cursor_addMulMemMem
#cone_sorries Midfall.Lowering.QvmCursor.cursor_pow5
#cone_sorries Midfall.Lowering.QvmCursor.cursor_addMulMemMemConstU8
#cone_sorries Midfall.Lowering.QvmCursor.cursor_addMulConstU8MemU16
#cone_sorries Midfall.Lowering.QvmCursor.cursor_lin7
#cone_sorries Midfall.Lowering.QvmCursor.cursor_bilin7Row
#cone_sorries Midfall.Lowering.QvmCursor.cursor_bilin7Pairwise
#cone_sorries Midfall.Lowering.QvmCursor.cursor_runP
#cone_sorries Midfall.Lowering.QvmCursor.cursor_runL
#cone_sorries Midfall.Lowering.QvmCursor.cursor_affineSum

#print axioms Midfall.Lowering.QvmCursor.pG_stackWalkCursor_of_cursorArm25
#print axioms Midfall.Lowering.QvmCursor.cursor_pushConst
#print axioms Midfall.Lowering.QvmCursor.cursor_add
#print axioms Midfall.Lowering.QvmCursor.cursor_lin7
#print axioms Midfall.Lowering.QvmCursor.cursor_runP
#print axioms Midfall.Lowering.QvmCursor.cursor_runL
#print axioms Midfall.Lowering.QvmCursor.cursor_affineSum
#print axioms Midfall.Lowering.QvmCursor.decode_ok_parts
#print axioms Midfall.Lowering.QvmCursor.decode_ok_getD
#print axioms Midfall.Lowering.QvmCursor.dec_width_of_table
#print axioms Midfall.Lowering.QvmCursor.lenChecked_runP
#print axioms Midfall.Lowering.QvmCursor.foldDepth_getD
#print axioms Midfall.Lowering.QvmCursor.PG_stepProgress_at_of_decoded_steps
#print axioms Midfall.Lowering.QvmCursor.loop_ok_of_decoded_steps
#print axioms Midfall.Lowering.QvmCursor.demoPG_stackWalkCursor
#print axioms Midfall.Lowering.QvmCursor.demo_walk_iterates_of_decoded
#cone_sorries Midfall.Lowering.QvmCursor.pG_stackWalkCursor_of_cursorArm25
#cone_sorries Midfall.Lowering.QvmCursor.foldDepth_getD
#cone_sorries Midfall.Lowering.QvmCursor.loop_ok_of_decoded_steps
#cone_sorries Midfall.Lowering.QvmCursor.demoPG_stackWalkCursor
#cone_sorries Midfall.Lowering.QvmCursor.demo_walk_iterates_of_decoded
#assert_axioms Midfall.Lowering.QvmCursor.pG_stackWalkCursor_of_cursorArm25 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QvmCursor.loop_ok_of_decoded_steps [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QvmCursor.demoPG_stackWalkCursor [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QvmCursor.cursor_affineSum [propext, Classical.choice, Quot.sound] native []

end Midfall.Lowering.QvmCursor

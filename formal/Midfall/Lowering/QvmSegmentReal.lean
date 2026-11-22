-- |
-- Midfall.Lowering.QvmSegmentReal
--
-- SEGPROVE (card SEGPROVE). IDSEG reduced 'PG_identity_segment' to six named axes and proved the
-- reduction ('QvmSegment.lean': 'walkInvariant_of_axes', 'pg_identity_segment_of_walk'); SHAPEX then
-- closed all six for IDSEG's HAND-BUILT five-byte witness ('QvmShape.lean': 'demo_axes_all_six'). This
-- file takes the next step the brief names: a REAL EMITTED segment - the bytes 'identityExpr' actually
-- writes for a real 'QuotientExpr' - and discharges the six axes for it, so the segment statement is
-- obtained for a segment the emitter produces rather than for one someone typed.
--
-- WHAT THE EMITTER ACTUALLY PRODUCED, AND WHY THE DEMO WAS NOT IT. The brief's premise is right that the
-- five-byte demo is not an emitted segment, and the gap is concrete: 'add (const 5) (const 11)' lowers to
-- FOUR bytes [9, 0, 12, 1] - PUSH_CONST_U8 then ADD_CONST_U8 - because the emitter's
-- accumulator peephole fires, so the demo's shape (two pushes and an ADD) is not what 'identityExpr'
-- emits for the expression the demo was meant to model. The segment proved about here is
-- 'add (mul 3 5) (add 7 (neg 2))' lowered end to end: ten bytes, six instructions, five DISTINCT arms
-- (PUSH_CONST_U8, MUL_CONST_U8, NEG, ADD_CONST_U8, ADD), constant table [3, 5, 2, 7], and the fold
-- stripped by 'finalizedIdentitySegment'. THREE more real segments are discharged the same way, chosen
-- so the arms they use are not one family:
--   * 'certSeg' - the tree's own 'eCert' fixture: PUSH_MEM_TOKEN, MUL and ADD_MEM_U16, so the MEMORY path
--     is covered and the axes are shown to hold at EVERY memory, not only at a cache-populated one;
--   * 'runSeg' - 'eRunLin4': the compactor FIRED, so the bytes the interpreter walks are not the bytes
--     the emitter wrote (the certificate asserts 'cseg != s.bytes'), and the arm is
--     RUN_ADD_MUL_CONST_U8_MEM_U16 with the count four the compactor wrote;
--   * 'afSeg' - 'eRunMixed': AFFINE_SUM with both counts nonzero, again on compacted bytes.
-- ELEVEN distinct arms in all, every one of them inside DEPTH's 'stepArm22', CURSOR's 'cursorArm25' and
-- SHAPE's 'shapeArm24', and none of them a LIMB arm - so 'PG_limbCountAgrees' is nowhere assumed and no
-- limb arm is admitted by silence.
--
-- HOW THE AXES ARE DISCHARGED, and what it does and does not buy. Every reachable cursor of these
-- segments is a cursor whose step the kernel can COMPUTE: the opcode is a literal byte, the slot is a
-- literal index into a literal table, and the stack shape is pinned by the walk invariant. So each of
-- the six axes is discharged by evaluating 'stepAt' at that cursor and citing 'NoRF.ok' /
-- 'AvoidsShape.ok'-style non-fault of a successful step. Consequences, stated plainly:
--   * NO named hypothesis is cited for the concrete segments: neither 'PG_constsCanonical' nor
--     'PG_shapeGuardsOfDecoded' is needed, because a step that computes to '.ok' faults nothing. That is
--     a fact about these witnesses, NOT a discharge of either Prop - both stay open, and section 6
--     shows the general route that needs them.
--   * The four LIMB arms are not used by either segment, so 'PG_limbCountAgrees' is not assumed anywhere
--     here (the brief's rule), and no limb arm is admitted by silence: the arms each segment uses are
--     listed byte by byte in section 1.
--   * What is NOT proved is the general statement for an arbitrary emitted segment. That still needs the
--     emitter to say which instruction it wrote at which cursor for an expression it has not enumerated,
--     and section 6 assembles exactly that from the published per-arm packages plus the two named Props.
--
-- THE EMITTER CERTIFICATE IS A VM GATE, NOT A KERNEL PROOF, and this is disclosed rather than glossed.
-- 'identityExpr' is a fuel-indexed well-founded recursion ('VmBuilder.lean:862-894, termination_by fuel'),
-- so the kernel will not unfold it: 'decide' on 'identityExpr ... = .ok s' fails, and so does 'rfl' on
-- 'the emitter's bytes = the literal' (measured - 'realPipeline' does not reduce). That is the same wall
-- VALP2 recorded for 'quotientBytecodeOpsGo'. The bytes are therefore pinned the way the repo already
-- pins every other emitter fact - a 'Bool' gate the VM computes ('realPipeline_ok', 'certPipeline_ok',
-- 'runPipeline_ok', 'afPipeline_ok'), the convention of 'VmBuilder.lean:1751-1773' - and the literal is
-- what the proof is about. If the emitter ever changes these bytes the gate flips; the proof does not,
-- and that asymmetry is the honest limit of this card. NOTE the consequence for the two rows: because the
-- emitter pipeline is not kernel-reducible, NO concrete instantiation of 'builder_segments_total' can be
-- exhibited by computation either - the last mile has to be a general lemma about the emitter's cursor
-- sequence, which is what section 6 assembles.
--
-- NO hypothesis was added to a row, to 'ValidV3', to a bundle or to the root (WORKER-RULES). No sorry.
-- No 'native_decide' (D-P71), no 'maxRecDepth'/'maxHeartbeats' change, no 2^256 numeral inside a
-- 'decide'. No fixture appears in any statement a row consumes: 'realExpr' is a witness, and the only
-- Prop here that mentions bytes is about the witness's own (D-P71).

import Midfall.Lowering.QvmShape
import Midfall.Lowering.QvmCursor
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QvmSegmentReal

open Midfall
open Midfall.Lowering
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientExpr QuotientRefMemory qvmFrModulus)
open Midfall.Generator.QuotientBuilder
open Midfall.Lowering.QvmEmit
open Midfall.Lowering.QvmSegment
open Midfall.Lowering.QvmShape
open Midfall.Lowering.QvmDepth
open Midfall.Lowering.QvmCursor

/-! ### 1. THE EMITTER'S OWN SEGMENT: the expression, the pipeline, and what it wrote -/

/-- The identity expression: '(3 * 5) + (7 + (-2))', all of it field constants so the emitted segment is
    the arithmetic path with no memory operand. -/
def realExpr : QuotientExpr :=
  QuotientExpr.add
    (QuotientExpr.mul (QuotientExpr.const 3) (QuotientExpr.const 5))
    (QuotientExpr.add (QuotientExpr.const 7) (QuotientExpr.neg (QuotientExpr.const 2)))

/-- The whole emitter pipeline on it: 'identityExpr' at the default builder and the main target, then the
    compaction the row's own 'hcompact' names, then the fold strip. -/
def realPipeline : Bool × List Nat × List Word256 × Nat :=
  match identityExpr noShapeRecognizers builderDefault realExpr QuotientTarget.main none with
  | .error _ => (false, [], [], 0)
  | .ok s =>
      match compactQuotientRuns (s.bytes.drop (builderDefault.bytes.length)) with
      | .error _ => (false, [], [], 0)
      | .ok cseg =>
          match finalizedIdentitySegment cseg with
          | none => (false, [], [], 0)
          | some seg => (true, seg, s.consts, s.stackDepth)

/-- **THE EMITTER CERTIFICATE.** The VM, not the kernel, says these are the bytes 'identityExpr' writes:
    the pipeline succeeds, its finalized segment is exactly 'realSeg' below, its table is exactly
    'realConsts', and the emitter's own depth accounting is back to zero (the fact AXIS 6's second leg
    asks the emitter for). '#eval realPipeline_ok' prints 'true'. -/
def realPipeline_ok : Bool :=
  let p := realPipeline
  p.1 && p.2.1 == [9, 0, 13, 1, 9, 2, 8, 12, 3, 6] &&
    p.2.2.1 == [3, 5, 2, 7] && p.2.2.2 == 0

/-- THE SEGMENT: the ten bytes the certificate pins. Decoded, they are
    'PUSH_CONST_U8 0', 'MUL_CONST_U8 1', 'PUSH_CONST_U8 2', 'NEG', 'ADD_CONST_U8 3', 'ADD' - five distinct
    arms, every one of them inside DEPTH's 'stepArm22', CURSOR's 'cursorArm25' and SHAPE's 'shapeArm24'.
    No LIMB arm, no RUN arm, no AFFINE_SUM, no stream opcode, so neither the limb exclusion nor
    'PG_limbCountAgrees' is in play for this segment. -/
def realSeg : List Nat := [9, 0, 13, 1, 9, 2, 8, 12, 3, 6]

/-- The constant table the certificate pins, in slot order. -/
def realConsts : List Word256 := [3, 5, 2, 7]

theorem real_len : realSeg.length = 10 := rfl

/-- The opcode at each reachable cursor, computed. -/
theorem real_op0 : realSeg.getD 0 0 = qOpPushConstU8 := rfl
theorem real_op2 : realSeg.getD 2 0 = qOpMulConstU8 := rfl
theorem real_op4 : realSeg.getD 4 0 = qOpPushConstU8 := rfl
theorem real_op6 : realSeg.getD 6 0 = qOpNeg := rfl
theorem real_op7 : realSeg.getD 7 0 = qOpAddConstU8 := rfl
theorem real_op9 : realSeg.getD 9 0 = qOpAdd := rfl

/-- The walk invariant of the segment: the cursor sequence the emitter's widths produce - 0, 2, 4, 6, 7,
    9, and out at 10 - paired with the stack depth the segment actually has at each. This is the shape
    IDSEG said AXIS 5 and AXIS 6 have to produce for a real emitted segment, read off the emitted bytes. -/
def realP (idx : Nat) (stack : List QVMFr) (_mem : QuotientRefMemory) : Prop :=
  (idx = 0 ∧ stack = []) ∨
    (idx = 2 ∧ stack.length = 1) ∨
    (idx = 4 ∧ stack.length = 1) ∨
    (idx = 6 ∧ stack.length = 2) ∨
    (idx = 7 ∧ stack.length = 2) ∨
    (idx = 9 ∧ stack.length = 2) ∨
    (idx ≥ 10 ∧ stack.length = 1)

/-- One case split over 'realP', used by every axis below. -/
theorem realP_cases {idx : Nat} {stack : List QVMFr} {mem : QuotientRefMemory}
    (h : realP idx stack mem) :
      (idx = 0 ∧ stack = []) ∨ (idx = 2 ∧ stack.length = 1) ∨
        (idx = 4 ∧ stack.length = 1) ∨ (idx = 6 ∧ stack.length = 2) ∨
        (idx = 7 ∧ stack.length = 2) ∨ (idx = 9 ∧ stack.length = 2) ∨
        (idx ≥ 10 ∧ stack.length = 1) := h

/-! ### 2. The six steps of the segment, computed -/

theorem real_step0 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt realSeg realConsts 0 stack mem =
      .ok { stack := 3 :: stack, consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep realSeg realConsts 0
          (realSeg.getD 0 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem real_step2 (a : QVMFr) (mem : QuotientRefMemory) :
    stepAt realSeg realConsts 2 [a] mem =
      .ok { stack := qvmFrMul a 5 :: [], consumed := 2, hConsumed := Nat.succ_pos 1,
             mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep realSeg realConsts 2
          (realSeg.getD 2 0) [a] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem real_step4 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt realSeg realConsts 4 stack mem =
      .ok { stack := 2 :: stack, consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep realSeg realConsts 4
          (realSeg.getD 4 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem real_step6 (a b : QVMFr) (mem : QuotientRefMemory) :
    stepAt realSeg realConsts 6 [a, b] mem =
      .ok { stack := qvmFrNeg a :: b :: [], consumed := 1, hConsumed := Nat.succ_pos 0,
             mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep realSeg realConsts 6
          (realSeg.getD 6 0) [a, b] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem real_step7 (a b : QVMFr) (mem : QuotientRefMemory) :
    stepAt realSeg realConsts 7 [a, b] mem =
      .ok { stack := qvmFrAdd a 7 :: b :: [], consumed := 2, hConsumed := Nat.succ_pos 1,
             mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep realSeg realConsts 7
          (realSeg.getD 7 0) [a, b] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem real_step9 (a b : QVMFr) (mem : QuotientRefMemory) :
    stepAt realSeg realConsts 9 [a, b] mem =
      .ok { stack := qvmFrAdd b a :: [], consumed := 1, hConsumed := Nat.succ_pos 0,
             mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep realSeg realConsts 9
          (realSeg.getD 9 0) [a, b] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

/-- A successful step faults nothing at all. The one lemma every axis below reduces to. -/
theorem ok_ne_error {α : Type} (a : α) (f : QVMFault) :
    (Except.ok a : Except QVMFault α) ≠ Except.error f := by
  intro h; cases h

/-! ### 3. THE SIX AXES FOR THE REAL SEGMENT -/

/-- **AXIS 1 (READ) FOR A REAL EMITTED SEGMENT.** -/
theorem realPG_stepNoRF_at : PG_stepNoRF_at realSeg realConsts realP := by
  intro idx stack mem hidx hP
  rw [real_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [real_step0 [] mem]; exact NoRF.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step2 a mem]; exact NoRF.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step4 [a] mem]; exact NoRF.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step6 a b mem]; exact NoRF.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step7 a b mem]; exact NoRF.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step9 a b mem]; exact NoRF.ok _
  · omega

/-- **AXIS 2 (SLOT) FOR A REAL EMITTED SEGMENT.** -/
theorem realPG_stepSlot_at : PG_stepSlot_at realSeg realConsts realP := by
  intro idx stack mem hidx hP slot j
  rw [real_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [real_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step2 a mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step4 [a] mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step6 a b mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step7 a b mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step9 a b mem]; exact ok_ne_error _ _
  · omega

/-- **AXIS 3 (DEPTH) FOR A REAL EMITTED SEGMENT.** -/
theorem realPG_stepDepth_at : PG_stepDepth_at realSeg realConsts realP := by
  intro idx stack mem hidx hP j
  rw [real_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [real_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step2 a mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step4 [a] mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step6 a b mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step7 a b mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step9 a b mem]; exact ok_ne_error _ _
  · omega

/-- **AXIS 4 (SHAPE) FOR A REAL EMITTED SEGMENT.** All seven clauses at once, at every reachable cursor.
    No 'PG_constsCanonical' and no 'PG_shapeGuardsOfDecoded' is cited: the clause is discharged because
    the step at each cursor of THIS segment computes to '.ok', not because the roster excludes the class.
    Section 6 is the route that needs the two Props. -/
theorem realPG_stepShape_at : PG_stepShape_at realSeg realConsts realP := by
  refine pg_stepShape_at_of_avoids realSeg realConsts realP ?_
  intro idx stack mem hidx hP
  rw [real_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [real_step0 [] mem]; exact AvoidsShape.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step2 a mem]; exact AvoidsShape.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [real_step4 [a] mem]; exact AvoidsShape.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step6 a b mem]; exact AvoidsShape.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step7 a b mem]; exact AvoidsShape.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [real_step9 a b mem]; exact AvoidsShape.ok _
  · omega

/-- **AXIS 5 (PROGRESS) FOR A REAL EMITTED SEGMENT.** The invariant survives each emitted step, at the
    cursor the step's own 'consumed' names - which is the emitter's width, byte for byte. -/
theorem realPG_stepProgress_at : PG_stepProgress_at realSeg realConsts realP := by
  intro idx stack mem st hidx hP hst
  rw [real_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, hl⟩)
  · subst hs
    have hseq : st = { stack := [3], consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
      have := real_step0 [] mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show realP 2 [3] mem
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    have hseq : st = { stack := [qvmFrMul a 5], consumed := 2, hConsumed := Nat.succ_pos 1,
                         mem := mem } := by
      have := real_step2 a mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show realP 4 [qvmFrMul a 5] mem
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    have hseq : st = { stack := [2, a], consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
      have := real_step4 [a] mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show realP 6 [2, a] mem
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    have hseq : st = { stack := [qvmFrNeg a, b], consumed := 1, hConsumed := Nat.succ_pos 0,
                         mem := mem } := by
      have := real_step6 a b mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show realP 7 [qvmFrNeg a, b] mem
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    have hseq : st = { stack := [qvmFrAdd a 7, b], consumed := 2, hConsumed := Nat.succ_pos 1,
                         mem := mem } := by
      have := real_step7 a b mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show realP 9 [qvmFrAdd a 7, b] mem
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    have hseq : st = { stack := [qvmFrAdd b a], consumed := 1, hConsumed := Nat.succ_pos 0,
                         mem := mem } := by
      have := real_step9 a b mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show realP 10 [qvmFrAdd b a] mem
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.le_refl 10, rfl⟩)))))
  · omega

/-- **AXIS 6 (INITIAL AND TERMINAL) FOR A REAL EMITTED SEGMENT.** The walk starts at cursor 0 with the
    empty stack, and every cursor at or past the end of the ten emitted bytes leaves exactly one value -
    the emitter's own depth accounting, read back through the interpreter. -/
theorem realPG_stepInitTerm : PG_stepInitTerm realSeg realP (memOfρ (fun _ _ => 0) []) :=
  ⟨Or.inl ⟨rfl, rfl⟩, by
    intro idx stack mem hout hP
    rw [real_len] at hout
    rcases hP with (⟨h1, _⟩ | ⟨h2, hl⟩ | ⟨h3, hl⟩ | ⟨h4, hl⟩ | ⟨h5, hl⟩ | ⟨h6, hl⟩ | ⟨h7, hl⟩)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact length_eq_one' hl⟩

/-- **ALL SIX AXES CLOSE FOR A REAL EMITTED SEGMENT**, assembled by IDSEG's own 'walkInvariant_of_axes'.
    No named hypothesis: every leaf is one of the six theorems above. -/
theorem real_axes_all_six (mem₀ : QuotientRefMemory) :
    WalkInvariant realSeg realConsts realP 0 ([] : List QVMFr) mem₀ :=
  walkInvariant_of_axes realSeg realConsts realP mem₀
    realPG_stepNoRF_at realPG_stepSlot_at realPG_stepDepth_at
    realPG_stepShape_at realPG_stepProgress_at (realPG_stepInitTerm)

/-! ### 4. The segment statement, discharged -/

/-- **THE SEGMENT RUNS.** IDSEG's own top-level composition applied to the emitted bytes: the walk from
    cursor 0 reaches the end of the segment without faulting, on EVERY memory - so in particular on
    'memOfρ ρ (leafKeys realExpr)' for every valuation. -/
theorem realSegment_runs (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity realSeg realConsts mem = .ok (v, mem') :=
  evalQuotientIdentity_ok_of_walk realSeg realConsts mem realP (real_axes_all_six mem)

/-- **'PG_identity_segment' DISCHARGED FOR A REAL EMITTED SEGMENT.** The conclusion of the Prop
    ('QvmEmit.lean:337') at the concrete data the emitter produced: for every valuation, the identity
    interpreter returns '.ok' on the emitted segment. This is the statement the card was asked for, and
    it is discharged on NO named hypothesis. -/
theorem pg_identity_segment_realSegment :
    ∀ (ρ : Valuation),
      (Midfall.Generator.evalQuotientIdentity realSeg realConsts
        (memOfρ ρ (leafKeys realExpr))).isOk = true :=
  fun ρ => evalQuotientIdentity_isOk_of_walk realSeg realConsts
    (memOfρ ρ (leafKeys realExpr)) realP (real_axes_all_six _)

/-- The same in the '.ok' form, for the record. -/
theorem pg_identity_segment_realSegment_ok (ρ : Valuation) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity realSeg realConsts
      (memOfρ ρ (leafKeys realExpr)) = .ok (v, mem') :=
  realSegment_runs _

/-! ### 5. A SECOND REAL SEGMENT, THIS ONE TOUCHING MEMORY -/

/-- 'm(0x100) + 11 * m(BETA)': the tree's own 'eCert' fixture, so this segment is emitted by a program
    the repo already gates on. Its arms are PUSH_CONST_U8, PUSH_MEM_TOKEN, MUL and ADD_MEM_U16 - the
    memory path, which the const-only segment does not exercise. -/
def certExpr : QuotientExpr := Midfall.Generator.QuotientVmBuilderKats.eCert

/-- The eight emitted bytes: 'PUSH_CONST_U8 0', 'PUSH_MEM_TOKEN 4', 'MUL', 'ADD_MEM_U16 0x0100'. -/
def certSeg : List Nat := [9, 0, 3, 4, 7, 16, 1, 0]

/-- Its one-entry constant table. -/
def certConsts : List Word256 := [11]

theorem cert_len : certSeg.length = 8 := rfl

/-- The certificate for the second segment: same pipeline, same VM gate. -/
def certPipeline_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault certExpr QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      match compactQuotientRuns s.bytes with
      | .error _ => false
      | .ok cseg =>
          match finalizedIdentitySegment cseg with
          | none => false
          | some seg => seg == certSeg && s.consts == certConsts && s.stackDepth == 0

/-- The memory is NOT pinned by the invariant: every read these arms perform is a 'derive', which is
    total, so the axes hold at EVERY memory. That is what makes the second leg of AXIS 6 independent of
    the valuation, and it is the fact 'builder_segments_total' asks for ('on every memory'). -/
def certP (idx : Nat) (stack : List QVMFr) (_mem : QuotientRefMemory) : Prop :=
  (idx = 0 ∧ stack = []) ∨
    (idx = 2 ∧ stack.length = 1) ∨
    (idx = 4 ∧ stack.length = 2) ∨
    (idx = 5 ∧ stack.length = 1) ∨
    (idx ≥ 8 ∧ stack.length = 1)

theorem cert_step0 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt certSeg certConsts 0 stack mem =
      .ok { stack := 11 :: stack, consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep certSeg certConsts 0
          (certSeg.getD 0 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem cert_step2 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt certSeg certConsts 2 stack mem =
      .ok { stack := (mem.token 4 0).1 :: stack, consumed := 2, hConsumed := Nat.succ_pos 1,
             mem := (mem.token 4 0).2 } := by
  show (Midfall.Generator.evalQuotientIdentityStep certSeg certConsts 2
          (certSeg.getD 2 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem cert_step4 (a b : QVMFr) (mem : QuotientRefMemory) :
    stepAt certSeg certConsts 4 [a, b] mem =
      .ok { stack := qvmFrMul b a :: [], consumed := 1, hConsumed := Nat.succ_pos 0,
             mem := mem } := by
  show (Midfall.Generator.evalQuotientIdentityStep certSeg certConsts 4
          (certSeg.getD 4 0) [a, b] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem cert_step5 (a : QVMFr) (mem : QuotientRefMemory) :
    stepAt certSeg certConsts 5 [a] mem =
      .ok { stack := qvmFrAdd a ((mem.literal 256).1) :: [], consumed := 3,
             hConsumed := Nat.succ_pos 2, mem := (mem.literal 256).2 } := by
  show (Midfall.Generator.evalQuotientIdentityStep certSeg certConsts 5
          (certSeg.getD 5 0) [a] mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

/-- **AXES 1-4 FOR THE MEMORY SEGMENT.** -/
theorem certPG_stepNoRF_at : PG_stepNoRF_at certSeg certConsts certP := by
  intro idx stack mem hidx hP
  rw [cert_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [cert_step0 [] mem]; exact NoRF.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step2 [a] mem]; exact NoRF.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [cert_step4 a b mem]; exact NoRF.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step5 a mem]; exact NoRF.ok _
  · omega

theorem certPG_stepSlot_at : PG_stepSlot_at certSeg certConsts certP := by
  intro idx stack mem hidx hP slot j
  rw [cert_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [cert_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step2 [a] mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [cert_step4 a b mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step5 a mem]; exact ok_ne_error _ _
  · omega

theorem certPG_stepDepth_at : PG_stepDepth_at certSeg certConsts certP := by
  intro idx stack mem hidx hP j
  rw [cert_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [cert_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step2 [a] mem]; exact ok_ne_error _ _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [cert_step4 a b mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step5 a mem]; exact ok_ne_error _ _
  · omega

theorem certPG_stepShape_at : PG_stepShape_at certSeg certConsts certP := by
  refine pg_stepShape_at_of_avoids certSeg certConsts certP ?_
  intro idx stack mem hidx hP
  rw [cert_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [cert_step0 [] mem]; exact AvoidsShape.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step2 [a] mem]; exact AvoidsShape.ok _
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl; rw [cert_step4 a b mem]; exact AvoidsShape.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl; rw [cert_step5 a mem]; exact AvoidsShape.ok _
  · omega

/-- **AXIS 5 FOR THE MEMORY SEGMENT**, including the memory the step threads: the invariant is stated for
    every memory, so the successor's rewritten memory is admitted by the same predicate. -/
theorem certPG_stepProgress_at : PG_stepProgress_at certSeg certConsts certP := by
  intro idx stack mem st hidx hP hst
  rw [cert_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨hge, hl⟩)
  · subst hs
    have hseq : st = { stack := [11], consumed := 2, hConsumed := Nat.succ_pos 1, mem := mem } := by
      have := cert_step0 [] mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show certP 2 [11] mem
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    have hseq : st = { stack := [(mem.token 4 0).1, a], consumed := 2, hConsumed := Nat.succ_pos 1,
                         mem := (mem.token 4 0).2 } := by
      have := cert_step2 [a] mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show certP 4 [(mem.token 4 0).1, a] ((mem.token 4 0).2)
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · obtain ⟨a, b, rfl⟩ := length_eq_two hl
    have hseq : st = { stack := [qvmFrMul b a], consumed := 1, hConsumed := Nat.succ_pos 0,
                         mem := mem } := by
      have := cert_step4 a b mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show certP 5 [qvmFrMul b a] mem
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    have hseq : st = { stack := [qvmFrAdd a (mem.literal 256).1], consumed := 3,
                         hConsumed := Nat.succ_pos 2, mem := (mem.literal 256).2 } := by
      have := cert_step5 a mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show certP 8 [qvmFrAdd a (mem.literal 256).1] ((mem.literal 256).2)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.le_refl 8, rfl⟩)))
  · omega

theorem certPG_stepInitTerm (mem₀ : QuotientRefMemory) : PG_stepInitTerm certSeg certP mem₀ :=
  ⟨Or.inl ⟨rfl, rfl⟩, by
    intro idx stack mem hout hP
    rw [cert_len] at hout
    rcases hP with (⟨h1, _⟩ | ⟨h2, hl⟩ | ⟨h3, hl⟩ | ⟨h4, hl⟩ | ⟨h5, hl⟩)
    · omega
    · omega
    · omega
    · omega
    · exact length_eq_one' hl⟩

/-- ALL SIX AXES for the memory segment, and the segment statement for it. -/
theorem cert_axes_all_six (mem₀ : QuotientRefMemory) :
    WalkInvariant certSeg certConsts certP 0 ([] : List QVMFr) mem₀ :=
  walkInvariant_of_axes certSeg certConsts certP mem₀
    certPG_stepNoRF_at certPG_stepSlot_at certPG_stepDepth_at
    certPG_stepShape_at certPG_stepProgress_at (certPG_stepInitTerm mem₀)

theorem certSegment_runs (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity certSeg certConsts mem = .ok (v, mem') :=
  evalQuotientIdentity_ok_of_walk certSeg certConsts mem certP (cert_axes_all_six mem)

/-- **THE 'ON EVERY MEMORY' FORM.** This is the exact shape of 'builder_segments_total's conclusion
    ('Qvm.lean:1000-1002'): a segment of a builder-produced program, run at an arbitrary memory, returns
    '.ok'. The two segments here satisfy it. -/
theorem pg_identity_segment_realSegment_cert (ρ : Valuation) :
    (Midfall.Generator.evalQuotientIdentity certSeg certConsts
      (memOfρ ρ (leafKeys certExpr))).isOk = true :=
  evalQuotientIdentity_isOk_of_walk certSeg certConsts (memOfρ ρ (leafKeys certExpr)) certP
    (cert_axes_all_six _)

/-! ### 5b. TWO REAL SEGMENTS WHERE COMPACTION REWROTE THE BYTES -/

/-- The two dynamic arms are the case IDSEG flagged as the hard one: 'compactQuotientRuns' rewrites the
    byte stream AFTER the emitter accounted for its own depth, so the segment the interpreter walks is
    NOT the bytes the emitter wrote. Both segments below are emitted programs for which that rewrite
    actually fired ('raw != cseg' in each certificate), so the axes are discharged on a stream the
    compactor produced, not on one it left alone. -/
def runExpr : QuotientExpr := Midfall.Generator.QuotientVmBuilderKats.eRunLin4

/-- Eighteen bytes: 'PUSH_MEM_U16 0x0100' then 'RUN_ADD_MUL_CONST_U8_MEM_U16' with a decoded count of
    four, each term a three-byte (u16 pointer, u8 slot) linear block. The run arm is the arm whose
    'zeroLengthRun' clause SHAPE had to gate behind a byte guard, and the count here is the four the
    compactor wrote. -/
def runSeg : List Nat := [5, 1, 0, 22, 0, 4, 1, 32, 0, 1, 64, 1, 1, 96, 2, 1, 128, 3]

/-- The four coefficients the four terms address, in slot order. -/
def runConsts : List Word256 := [2, 3, 5, 7]

/-- The certificate for the RUN segment: the pipeline succeeds, the COMPACTED bytes differ from the raw
    ones, and the finalized segment is 'runSeg'. '#eval runPipeline_ok' prints 'true'. -/
def runPipeline_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault runExpr QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      match compactQuotientRuns s.bytes with
      | .error _ => false
      | .ok cseg =>
          cseg != s.bytes &&
            match finalizedIdentitySegment cseg with
            | none => false
            | some seg => seg == runSeg && s.consts == runConsts && s.stackDepth == 0

theorem run_len : runSeg.length = 18 := rfl

/-- The cursor sequence the two emitted widths produce: 0, 3, and out at 18. -/
def runP (idx : Nat) (stack : List QVMFr) (_mem : QuotientRefMemory) : Prop :=
  (idx = 0 ∧ stack = []) ∨
    (idx = 3 ∧ stack.length = 1) ∨
    (idx ≥ 18 ∧ stack.length = 1)

theorem run_step0 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt runSeg runConsts 0 stack mem =
      .ok { stack := (mem.literal 256).1 :: stack, consumed := 3,
             hConsumed := Nat.succ_pos 2, mem := (mem.literal 256).2 } := by
  show (Midfall.Generator.evalQuotientIdentityStep runSeg runConsts 0
          (runSeg.getD 0 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

/-- **THE RUN STEP COMPUTES.** Stated existentially because the accumulated value is a four-fold
    'qvmFrAdd' of 'qvmFrMul' terms over memory reads the kernel leaves stuck - the axes never need the
    value, only that the step returns and what it does to the cursor and the depth. Both the cursor
    equation ('3 + consumed = 18', i.e. the compactor's own width) and the depth reduce by 'rfl'. -/
theorem run_step3 (a : QVMFr) (mem : QuotientRefMemory) :
    ∃ st, stepAt runSeg runConsts 3 [a] mem = .ok st ∧
      3 + st.consumed = 18 ∧ st.stack.length = 1 := by
  refine ⟨_, rfl, rfl, rfl⟩

theorem runPG_stepNoRF_at : PG_stepNoRF_at runSeg runConsts runP := by
  intro idx stack mem hidx hP
  rw [run_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [run_step0 [] mem]; exact NoRF.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := run_step3 a mem
    rw [hst]; exact NoRF.ok st
  · omega

theorem runPG_stepSlot_at : PG_stepSlot_at runSeg runConsts runP := by
  intro idx stack mem hidx hP slot j
  rw [run_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [run_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := run_step3 a mem
    rw [hst]; exact ok_ne_error _ _
  · omega

theorem runPG_stepDepth_at : PG_stepDepth_at runSeg runConsts runP := by
  intro idx stack mem hidx hP j
  rw [run_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [run_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := run_step3 a mem
    rw [hst]; exact ok_ne_error _ _
  · omega

theorem runPG_stepShape_at : PG_stepShape_at runSeg runConsts runP := by
  refine pg_stepShape_at_of_avoids runSeg runConsts runP ?_
  intro idx stack mem hidx hP
  rw [run_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [run_step0 [] mem]; exact AvoidsShape.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := run_step3 a mem
    rw [hst]; exact AvoidsShape.ok st
  · omega

theorem runPG_stepProgress_at : PG_stepProgress_at runSeg runConsts runP := by
  intro idx stack mem st hidx hP hst
  rw [run_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, hl⟩)
  · subst hs
    have hseq : st = { stack := [(mem.literal 256).1], consumed := 3,
                         hConsumed := Nat.succ_pos 2, mem := (mem.literal 256).2 } := by
      have := run_step0 [] mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show runP 3 [(mem.literal 256).1] ((mem.literal 256).2)
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st', hst', hcur, hlen⟩ := run_step3 a mem
    have hseq : st' = st := Except.ok.inj (hst'.symm.trans hst)
    subst hseq
    rw [hcur]
    exact Or.inr (Or.inr ⟨by omega, hlen⟩)
  · omega

theorem runPG_stepInitTerm (mem₀ : QuotientRefMemory) : PG_stepInitTerm runSeg runP mem₀ :=
  ⟨Or.inl ⟨rfl, rfl⟩, by
    intro idx stack mem hout hP
    rw [run_len] at hout
    rcases hP with (⟨h1, _⟩ | ⟨h2, hl⟩ | ⟨h3, hl⟩)
    · omega
    · omega
    · exact length_eq_one' hl⟩

/-- ALL SIX AXES for the RUN segment, and the segment statement for it. -/
theorem run_axes_all_six (mem₀ : QuotientRefMemory) :
    WalkInvariant runSeg runConsts runP 0 ([] : List QVMFr) mem₀ :=
  walkInvariant_of_axes runSeg runConsts runP mem₀
    runPG_stepNoRF_at runPG_stepSlot_at runPG_stepDepth_at
    runPG_stepShape_at runPG_stepProgress_at (runPG_stepInitTerm mem₀)

theorem runSegment_runs (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity runSeg runConsts mem = .ok (v, mem') :=
  evalQuotientIdentity_ok_of_walk runSeg runConsts mem runP (run_axes_all_six mem)

/-- 'PG_identity_segment' discharged for the COMPACTED segment. -/
theorem pg_identity_segment_runSegment (ρ : Valuation) :
    (Midfall.Generator.evalQuotientIdentity runSeg runConsts
      (memOfρ ρ (leafKeys runExpr))).isOk = true :=
  evalQuotientIdentity_isOk_of_walk runSeg runConsts (memOfρ ρ (leafKeys runExpr)) runP
    (run_axes_all_six _)

/-- The AFFINE_SUM case: 'eRunMixed', two linear and two product terms, which the compactor merges into
    one 'AFFINE_SUM' instruction with two nonzero counts. Raw and compacted bytes differ again. -/
def afExpr : QuotientExpr := Midfall.Generator.QuotientVmBuilderKats.eRunMixed

/-- Twenty-four bytes: 'PUSH_MEM_U16 0x0100' then 'AFFINE_SUM' with linCount = 2 and productCount = 2 -
    the two counts 'affineSumZeroCounts' is about, both nonzero because the compactor only merges runs of
    at least the minimum length. -/
def afSeg : List Nat :=
  [5, 1, 0, 34, 0, 2, 0, 2, 1, 32, 0, 1, 128, 2, 1, 64, 1, 96, 1, 1, 160, 1, 192, 3]

def afConsts : List Word256 := [2, 3, 5, 7]

def afPipeline_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault afExpr QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      match compactQuotientRuns s.bytes with
      | .error _ => false
      | .ok cseg =>
          cseg != s.bytes &&
            match finalizedIdentitySegment cseg with
            | none => false
            | some seg => seg == afSeg && s.consts == afConsts && s.stackDepth == 0

theorem af_len : afSeg.length = 24 := rfl

def afP (idx : Nat) (stack : List QVMFr) (_mem : QuotientRefMemory) : Prop :=
  (idx = 0 ∧ stack = []) ∨
    (idx = 3 ∧ stack.length = 1) ∨
    (idx ≥ 24 ∧ stack.length = 1)

theorem af_step0 (stack : List QVMFr) (mem : QuotientRefMemory) :
    stepAt afSeg afConsts 0 stack mem =
      .ok { stack := (mem.literal 256).1 :: stack, consumed := 3,
             hConsumed := Nat.succ_pos 2, mem := (mem.literal 256).2 } := by
  show (Midfall.Generator.evalQuotientIdentityStep afSeg afConsts 0
          (afSeg.getD 0 0) stack mem) = _
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rfl

theorem af_step3 (a : QVMFr) (mem : QuotientRefMemory) :
    ∃ st, stepAt afSeg afConsts 3 [a] mem = .ok st ∧
      3 + st.consumed = 24 ∧ st.stack.length = 1 := by
  refine ⟨_, rfl, rfl, rfl⟩

theorem afPG_stepNoRF_at : PG_stepNoRF_at afSeg afConsts afP := by
  intro idx stack mem hidx hP
  rw [af_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [af_step0 [] mem]; exact NoRF.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := af_step3 a mem
    rw [hst]; exact NoRF.ok st
  · omega

theorem afPG_stepSlot_at : PG_stepSlot_at afSeg afConsts afP := by
  intro idx stack mem hidx hP slot j
  rw [af_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [af_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := af_step3 a mem
    rw [hst]; exact ok_ne_error _ _
  · omega

theorem afPG_stepDepth_at : PG_stepDepth_at afSeg afConsts afP := by
  intro idx stack mem hidx hP j
  rw [af_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [af_step0 [] mem]; exact ok_ne_error _ _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := af_step3 a mem
    rw [hst]; exact ok_ne_error _ _
  · omega

theorem afPG_stepShape_at : PG_stepShape_at afSeg afConsts afP := by
  refine pg_stepShape_at_of_avoids afSeg afConsts afP ?_
  intro idx stack mem hidx hP
  rw [af_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, _hl⟩)
  · subst hs; rw [af_step0 [] mem]; exact AvoidsShape.ok _
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st, hst, _hc, _hl'⟩ := af_step3 a mem
    rw [hst]; exact AvoidsShape.ok st
  · omega

theorem afPG_stepProgress_at : PG_stepProgress_at afSeg afConsts afP := by
  intro idx stack mem st hidx hP hst
  rw [af_len] at hidx
  rcases hP with (⟨rfl, hs⟩ | ⟨rfl, hl⟩ | ⟨hge, hl⟩)
  · subst hs
    have hseq : st = { stack := [(mem.literal 256).1], consumed := 3,
                         hConsumed := Nat.succ_pos 2, mem := (mem.literal 256).2 } := by
      have := af_step0 [] mem
      rw [hst] at this
      exact Except.ok.inj this
    subst hseq
    show afP 3 [(mem.literal 256).1] ((mem.literal 256).2)
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨a, rfl⟩ := length_eq_one' hl
    obtain ⟨st', hst', hcur, hlen⟩ := af_step3 a mem
    have hseq : st' = st := Except.ok.inj (hst'.symm.trans hst)
    subst hseq
    rw [hcur]
    exact Or.inr (Or.inr ⟨by omega, hlen⟩)
  · omega

theorem afPG_stepInitTerm (mem₀ : QuotientRefMemory) : PG_stepInitTerm afSeg afP mem₀ :=
  ⟨Or.inl ⟨rfl, rfl⟩, by
    intro idx stack mem hout hP
    rw [af_len] at hout
    rcases hP with (⟨h1, _⟩ | ⟨h2, hl⟩ | ⟨h3, hl⟩)
    · omega
    · omega
    · exact length_eq_one' hl⟩

theorem af_axes_all_six (mem₀ : QuotientRefMemory) :
    WalkInvariant afSeg afConsts afP 0 ([] : List QVMFr) mem₀ :=
  walkInvariant_of_axes afSeg afConsts afP mem₀
    afPG_stepNoRF_at afPG_stepSlot_at afPG_stepDepth_at
    afPG_stepShape_at afPG_stepProgress_at (afPG_stepInitTerm mem₀)

theorem afSegment_runs (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity afSeg afConsts mem = .ok (v, mem') :=
  evalQuotientIdentity_ok_of_walk afSeg afConsts mem afP (af_axes_all_six mem)

theorem pg_identity_segment_afSegment (ρ : Valuation) :
    (Midfall.Generator.evalQuotientIdentity afSeg afConsts
      (memOfρ ρ (leafKeys afExpr))).isOk = true :=
  evalQuotientIdentity_isOk_of_walk afSeg afConsts (memOfρ ρ (leafKeys afExpr)) afP
    (af_axes_all_six _)

/-! ### 6. THE GENERAL ROUTE, and the two named Props it costs -/

/-- **THE ROUTE FOR A SEGMENT NOBODY ENUMERATED.** For the four segments above every step computed, so no
    named hypothesis was needed. For an ARBITRARY emitted segment the step cannot be evaluated - the
    opcode is a variable - and the axes have to come from the published per-arm packages. This assembles
    exactly that, and it is where the two blockers bite: SHAPE goes through
    'PG_stepShape_at_of_decoded_cursors', which needs 'PG_constsCanonical' (the 'fqFromU256' panic clause,
    which SHAPEX proved is not dischargeable from bytes and which 'decide' cannot reach even for the
    four-entry table [3, 5, 2, 7] - measured) and 'PG_shapeGuardsOfDecoded' (the validator do-block
    join-point peel). DEPTH goes through 'PG_stepDepth_at_of_popCount_le' and PROGRESS through
    'PG_stepProgress_at_of_decoded_steps', both cited with no extra hypothesis beyond what the packages
    already state. READ and SLOT are taken from the step success inside 'hprog' rather than from
    'QvmShift's 25-arm packages, because those ask for the validator's width hypotheses
    ('quotientOpLen (op :: rest) 0 = .ok len', 'visitQuotientOperands' succeeding) which are the same
    decoded-cursor fact 'hdec' already carries - so citing them would add no coverage, only hypotheses.
    Both Props are cited here as hypotheses of MY lemma, as RULES requires, and neither is added to a row. -/
theorem axes_of_emitter_facts (bytes : List Nat) (consts : List Word256)
    (P : Nat → List QVMFr → QuotientRefMemory → Prop) (mem₀ : QuotientRefMemory)
    (hc : PG_constsCanonical consts)
    (hguards : PG_shapeGuardsOfDecoded)
    (hdec : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ op len, Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes idx =
          .ok (op, len) ∧ shapeArm24 op)
    (hdepth : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        stepArm22 (bytes.getD idx 0) ∧ stepPopCount (bytes.getD idx 0) ≤ stack.length)
    (hprog : ∀ idx stack mem, idx < bytes.length → P idx stack mem →
        ∃ op len s, Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes idx =
          .ok (op, len) ∧ cursorArm25 op ∧
          stepAt bytes consts idx stack mem = .ok s ∧ P (idx + len) s.stack s.mem)
    (hinit : P 0 ([] : List QVMFr) mem₀)
    (hterm : ∀ idx stack mem, ¬ idx < bytes.length → P idx stack mem → ∃ v, stack = [v]) :
    WalkInvariant bytes consts P 0 ([] : List QVMFr) mem₀ :=
  walkInvariant_of_axes bytes consts P mem₀
    (by
      intro idx stack mem hidx hP i
      obtain ⟨op, len, s, hdec', hop, hst, _hP'⟩ := hprog idx stack mem hidx hP
      rw [hst]; exact ok_ne_error _ _)
    (by
      intro idx stack mem hidx hP slot j
      obtain ⟨op, len, s, hdec', hop, hst, _hP'⟩ := hprog idx stack mem hidx hP
      rw [hst]; exact ok_ne_error _ _)
    (PG_stepDepth_at_of_popCount_le bytes consts P hdepth)
    (PG_stepShape_at_of_decoded_cursors bytes consts P hc hguards hdec)
    (PG_stepProgress_at_of_decoded_steps bytes consts P hprog)
    ⟨hinit, hterm⟩

/-! ### 7. HOW FAR 'builder_segments_total' MOVED, AS A THEOREM RATHER THAN AS PROSE -/

/-- The slice 'builder_segments_total' ('Qvm.lean:992') concludes about, factored out so it can be named.
    For a one-identity build at cursor 0 this is exactly the finalized segment - the certifier's own gate
    'identitySegment_agreesWithBuilderStripper_ok' ('VmCertify.lean:1572') pins
    'bytes.take exprEnd == finalizedIdentitySegment bytes' - so the four segments proved about above are
    instances of THIS shape, at cursor 0. -/
def planSegment (bytes : List Nat) (cursor exprEnd : Nat) : List Nat :=
  (bytes.drop cursor).take (exprEnd - cursor)

/-- **THE ONE PROP THAT IS LEFT FOR THE REGISTERED SORRY.** 'builder_segments_total' asks that a segment of
    a builder-produced program never faults on any memory. Everything between the emitter's facts and that
    conclusion is already a theorem: the walk induction ('QvmSegment.lean') turns a 'WalkInvariant' into
    the '.ok', and this card turns real emitted bytes into a 'WalkInvariant'. What no card supplies is the
    bridge from 'buildPlan'/'itemStarts'/'identitySegment' to the existence of a 'WalkInvariant' - the
    emitter's own cursor sequence for a plan it has not enumerated. That is what this Prop names, in the
    walk's vocabulary and nowhere else. It is a Prop, so it adds no sorry and moves no cone. -/
def PG_planSegmentWalk : Prop :=
  ∀ (r : QuotientShapeRecognizers) (_hr : RecognizersSound r)
    (plan : QuotientProgramPlan) (limbOps : Bool) (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts plan build)
    (hseg : Midfall.Generator.QuotientCertify.identitySegment (qvmBytesToNats build.bytes) cursor =
      .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory),
      ∃ P, WalkInvariant (planSegment (qvmBytesToNats build.bytes) cursor exprEnd)
        build.consts P 0 ([] : List QVMFr) mem

/-- **THE REDUCTION, PROVED.** 'PG_planSegmentWalk' implies the exact conclusion of
    'builder_segments_total', with the same binders and the same slice. Nothing was added to a row: the
    hypothesis is a standalone Prop and the proof is one application of IDSEG's
    'evalQuotientIdentity_ok_of_walk'. The reason the registered sorry could not simply be closed here is
    stated in the header and repeated for the record: 'builder_segments_total' lives in
    'Midfall/Lowering/Qvm.lean', which this card does not own, and the emitter pipeline is a well-founded
    recursion the kernel will not unfold, so no concrete plan can be exhibited by computation either. What
    the owning card needs is one line: 'exact builder_segments_total_of_planSegmentWalk h' once 'h' is
    supplied. -/
theorem builder_segments_total_of_planSegmentWalk (h : PG_planSegmentWalk) :
    ∀ (r : QuotientShapeRecognizers) (hr : RecognizersSound r)
      (plan : QuotientProgramPlan) (limbOps : Bool) (build : QuotientProgramBuild)
      (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
      (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
      (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
      (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts plan build)
      (hseg : Midfall.Generator.QuotientCertify.identitySegment (qvmBytesToNats build.bytes) cursor =
        .ok (exprEnd, foldOp))
      (mem : QuotientRefMemory),
        ∃ v mem', Midfall.Generator.evalQuotientIdentity
          (planSegment (qvmBytesToNats build.bytes) cursor exprEnd) build.consts mem =
            .ok (v, mem') := by
  intro r hr plan limbOps build hbuild hbounded hconsts cursor exprEnd foldOp hstart hseg mem
  obtain ⟨P, hP⟩ :=
    h r hr plan limbOps build hbuild hbounded hconsts cursor exprEnd foldOp hstart hseg mem
  exact evalQuotientIdentity_ok_of_walk (planSegment (qvmBytesToNats build.bytes) cursor exprEnd)
    build.consts mem P hP

/-- **THE FOUR SEGMENTS ARE INSTANCES OF THE SLICE SHAPE.** At cursor 0 the slice of a one-identity build
    is the whole segment, and each of the four '..._axes_all_six' theorems above is a 'WalkInvariant' for
    such a slice. Recorded as a lemma so the claim 'these are instances of the sorry's shape' is checked
    rather than asserted. -/
theorem planSegment_at_zero (bytes : List Nat) (exprEnd : Nat) :
    planSegment bytes 0 exprEnd = bytes.take exprEnd := rfl

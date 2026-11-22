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
          match finalizedIdentitySegment QuotientTarget.main cseg with
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
          match finalizedIdentitySegment QuotientTarget.main cseg with
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
            match finalizedIdentitySegment QuotientTarget.main cseg with
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
            match finalizedIdentitySegment QuotientTarget.main cseg with
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

open Midfall.Generator.QuotientCertify

/-! ### 8. THE PLAN'S OWN CURSOR SEQUENCE (card PLSEG): what 'hseg' supplies and what nothing does

THE QUESTION THIS SECTION ANSWERS. Section 7 reduced the registered 'builder_segments_total' to
'PG_planSegmentWalk' and said the last mile is "one line once the emitter supplies the cursor facts".
This section checks that claim on the plan's own segments. IT DOES NOT CLOSE, and the reason is not the
walk machinery: the induction, the six axes and the four real emitted segments are all landed and all
citable. The reason is that nothing in the tree connects 'buildPlan' to the instruction sequence its
bytes spell. Three separate facts are missing, and each is named below with the exact goal state, as
RULES requires. Nothing here adds a hypothesis to a row, to 'ValidV3', to a bundle or to the root; '
PG_planSegmentWalk' is NOT restated; no sorry is added and none is removed.

WHAT 'hseg' ALREADY SUPPLIES (proved below, no hypothesis). 'identitySegment bytes cursor =
.ok (exprEnd, foldOp)' is itself a cursor statement, and it is stronger than it looks: the walk it
certifies advances EXACTLY by the validator's 'quotientOpLen' at every cursor strictly before
'exprEnd', it lands on 'exprEnd' with a real fold opcode there, it never leaves the stream, and it
supports an induction principle over the cursors it visited ('iseg_bounds', 'isegGo_advance',
'iseg_walk_ind'). Together with the slice lemmas ('planSegment_length', 'planSegment_getD',
'planSegment_take_append') that pins the cursor arithmetic of the row's own segment - which is the part
of the brief that asked which stream the cursors live in. THE ANSWER ON COMPACTION: the COMPACTED one.
'finish' compacts first and returns the byte-view of the compaction ('finish_ok_compacted'), and
'itemStarts' / 'identitySegment' are both computed from 'qvmBytesToNats build.bytes', so the cursors are
positions in the post-compaction stream while the per-item drops in 'PG_identity_segment_walk' are
positions in the pre-compaction buffer. 'runSeg' and 'afSeg' are the two witnesses that the two are NOT
the same bytes, and no card reconciles them: that reconciliation is 'PG_planItemSegment' below.

THE THREE MISSING FACTS.
(1) 'PG_planSegmentCursorFacts' (NEW, named here): for the slice at an item start, some predicate holds
    at cursor 0, is carried across every step, and forces a singleton stack at the end - with each step
    stated as a SUCCESSFUL 'stepAt' whose consumed width equals the validator decoder's width. This is
    exactly the input section 6's 'axes_of_emitter_facts' consumes, and 'pg_planSegmentWalk_of_cursorFacts'
    proves the implication (0 sorries in its cone), so the registered sorry really is one application
    from this Prop and not from anything else.
(2) 'PG_planItemSegment' (NEW, named here): the slice IS the finalized, compacted emission of one
    identity item of the plan, over the compacted stream, with the build's table extending the item's.
    Without (1) this buys nothing; without this, (1) has no source. Proving it is the induction over
    'buildItems'/'finish' that 'qvm_compile_correct_identity' (Qvm.lean:619) also owes.
(3) The roster gap, which section 7's header does not mention: 'axes_of_emitter_facts' asks for
    'stepArm22' at every reachable cursor, and 'stepArm22' EXCLUDES all four LIMB arms - proved below by
    'not_stepArm22_lin7' and friends, and 'iseg_walks_limb_cursor' shows the row's own 'hseg' admits a
    cursor holding 'qOpLin7' (the row quantifies over 'limbOps : Bool' and over arbitrary recognizers).
    So even with (1) and (2) the route serves only the 22-arm fragment unless DEPTH's
    'PG_stepDepth_at_limb4' and SHAPE's 'PG_stepShape_at_limb2' are also discharged, and
    'PG_shapeGuardsOfDecoded' is needed for the SHAPE axis regardless. Per-axis limb check, as the brief
    asks: DEPTH excludes the four limb arms from the ROUTE although their 'stepPopCount' is 0 (so the
    exclusion is vacuous in content, 'stepPopCount_limb4_zero'); SHAPE covers LIN7 and BILIN7_ROW and
    excludes MODARITH7 and BILIN7_PAIRWISE (NOT vacuous); CURSOR covers 25 of 26 and excludes only
    MODARITH7.
ONE FREEBIE: section 6 lists 'PG_constsCanonical' as a cost of the general route. For this row it is
free - the row's own 'hconsts' is that formula about that table ('pg_constsCanonical_of_hconsts').

No new file, so no 'Midfall.lean' edit. No 'native_decide', no 'maxRecDepth'/'maxHeartbeats' change, no
2^256 numeral inside a 'decide' (the one 'decide' here is a 23-byte stream). -/

theorem beq_eq_true {a b : Nat} (h : (a == b) = true) : a = b := by simp at h; exact h

theorem beq_or_eq_true {a b c : Nat} (h : (a == b || a == c) = true) : a = b ∨ a = c := by
  rw [Bool.or_eq_true] at h
  cases h with
  | inl h => exact Or.inl (beq_eq_true h)
  | inr h => exact Or.inr (beq_eq_true h)

theorem iseg_eq_go (bytes : List Nat) (start : Nat) :
    identitySegment bytes start = identitySegment.go bytes start bytes.length start := rfl

theorem iseg_go_zero {bytes : List Nat} {start cursor exprEnd foldOp : Nat} :
    identitySegment.go bytes start 0 cursor = .ok (exprEnd, foldOp) → False := by
  intro h
  rw [show identitySegment.go bytes start 0 cursor =
      (if cursor < bytes.length then
        (.error "quotient VM segment walk fuel exhausted - port-only bound, see the header"
          : Except String (Nat × Nat))
       else .error (identitySegment.neverFolded start)) from by
    simp only [identitySegment.go]] at h
  by_cases hlt : cursor < bytes.length
  · rw [ite_eq_left hlt] at h; cases h
  · rw [ite_eq_right hlt] at h; cases h

theorem iseg_go_succ_eq (bytes : List Nat) (start fuel cursor : Nat) :
    identitySegment.go bytes start (fuel + 1) cursor =
      (if cursor < bytes.length then
        if (bytes.getD cursor 0 == qOpFoldMain || bytes.getD cursor 0 == qOpFoldSelector) = true then
          (.ok (cursor, bytes.getD cursor 0) : Except String (Nat × Nat))
        else if (bytes.getD cursor 0 == qOpNativePermutation
            || bytes.getD cursor 0 == qOpNativeLookup
            || bytes.getD cursor 0 == qOpNativeIdentity) = true then
          (.error ("native marker " ++ qvmHex (bytes.getD cursor 0) ++ " at byte "
            ++ toString cursor ++ " interrupts an identity expression") : Except String (Nat × Nat))
        else match quotientOpLen bytes cursor with
          | .error f => .error f.message
          | .ok len => identitySegment.go bytes start fuel (cursor + len)
       else (.error (identitySegment.neverFolded start) : Except String (Nat × Nat))) := by
  simp only [identitySegment.go]
  rfl

theorem iseg_go_step {bytes : List Nat} {start fuel cursor exprEnd foldOp : Nat}
    (h : identitySegment.go bytes start (fuel + 1) cursor = .ok (exprEnd, foldOp)) :
    (cursor = exprEnd ∧ cursor < bytes.length ∧ bytes.getD cursor 0 = foldOp
        ∧ (foldOp = qOpFoldMain ∨ foldOp = qOpFoldSelector))
      ∨ (∃ len, quotientOpLen bytes cursor = .ok len ∧
          identitySegment.go bytes start fuel (cursor + len) = .ok (exprEnd, foldOp) ∧
          bytes.getD cursor 0 ≠ qOpFoldMain ∧ bytes.getD cursor 0 ≠ qOpFoldSelector) := by
  rw [iseg_go_succ_eq] at h
  by_cases hlt : cursor < bytes.length
  · rw [ite_eq_left hlt] at h
    by_cases hfb : (bytes.getD cursor 0 == qOpFoldMain
        || bytes.getD cursor 0 == qOpFoldSelector) = true
    · rw [ite_eq_left hfb] at h
      have hp : (cursor, bytes.getD cursor 0) = (exprEnd, foldOp) := Except.ok.inj h
      simp only [Prod.mk.injEq] at hp
      obtain ⟨r1, r2⟩ := hp
      have hfold : foldOp = qOpFoldMain ∨ foldOp = qOpFoldSelector := by
        rw [← r2]
        exact beq_or_eq_true hfb
      exact Or.inl ⟨r1, hlt, r2, hfold⟩
    · rw [ite_eq_right hfb] at h
      by_cases hn : (bytes.getD cursor 0 == qOpNativePermutation
          || bytes.getD cursor 0 == qOpNativeLookup
          || bytes.getD cursor 0 == qOpNativeIdentity) = true
      · rw [ite_eq_left hn] at h; cases h
      · rw [ite_eq_right hn] at h
        cases hq : quotientOpLen bytes cursor with
        | error f => simp only [hq] at h; cases h
        | ok len =>
            simp only [hq] at h
            have hn1 : bytes.getD cursor 0 ≠ qOpFoldMain := by
              intro e; exact hfb (by simp only [e]; decide)
            have hn2 : bytes.getD cursor 0 ≠ qOpFoldSelector := by
              intro e; exact hfb (by simp only [e]; decide)
            exact Or.inr ⟨len, rfl, h, hn1, hn2⟩
  · rw [ite_eq_right hlt] at h; cases h

theorem iseg_go_bounds {bytes : List Nat} (start : Nat) :
    ∀ (fuel cursor exprEnd foldOp : Nat),
      identitySegment.go bytes start fuel cursor = .ok (exprEnd, foldOp) →
        cursor ≤ exprEnd ∧ exprEnd < bytes.length ∧
          (foldOp = qOpFoldMain ∨ foldOp = qOpFoldSelector) ∧ bytes.getD exprEnd 0 = foldOp := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor exprEnd foldOp h
      exact absurd h iseg_go_zero
  | succ k ih =>
      intro cursor exprEnd foldOp h
      obtain (⟨r1, hlt, hget, hf⟩ | ⟨len, _, hnext, _, _⟩) := iseg_go_step h
      · exact ⟨by omega, by omega, hf, by rw [← r1]; exact hget⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih (cursor + len) exprEnd foldOp hnext
        exact ⟨by omega, h2, h3, h4⟩

theorem iseg_bounds {bytes : List Nat} {cursor exprEnd foldOp : Nat}
    (hseg : identitySegment bytes cursor = .ok (exprEnd, foldOp)) :
    cursor ≤ exprEnd ∧ exprEnd < bytes.length ∧
      (foldOp = qOpFoldMain ∨ foldOp = qOpFoldSelector) ∧ bytes.getD exprEnd 0 = foldOp :=
  iseg_go_bounds cursor bytes.length cursor exprEnd foldOp hseg

/-- **THE WALK ADVANCES BY THE VALIDATOR'S WIDTH.** -/
theorem isegGo_advance {bytes : List Nat} {start fuel cursor exprEnd foldOp : Nat}
    (h : identitySegment.go bytes start (fuel + 1) cursor = .ok (exprEnd, foldOp))
    (hne : cursor ≠ exprEnd) :
    ∃ len, quotientOpLen bytes cursor = .ok len ∧
      identitySegment.go bytes start fuel (cursor + len) = .ok (exprEnd, foldOp) ∧
      cursor + len ≤ exprEnd := by
  obtain (⟨rfl, _, _, _⟩ | ⟨len, hlen, hnext, _, _⟩) := iseg_go_step h
  · exact absurd rfl hne
  · have ⟨h1, _, _, _⟩ := iseg_go_bounds start fuel (cursor + len) exprEnd foldOp hnext
    exact ⟨len, hlen, hnext, h1⟩

/-- **THE CURSOR INDUCTION THE ROW NEEDS.** -/
theorem iseg_walk_ind {bytes : List Nat} {cursor exprEnd foldOp : Nat}
    (hseg : identitySegment bytes cursor = .ok (exprEnd, foldOp)) (Q : Nat → Prop)
    (hbase : Q cursor)
    (hstep : ∀ c len, cursor ≤ c → c < exprEnd → Q c →
        quotientOpLen bytes c = .ok len → Q (c + len)) :
    Q exprEnd := by
  have key : ∀ fuel c, identitySegment.go bytes cursor fuel c = .ok (exprEnd, foldOp) →
      cursor ≤ c → Q c → c ≤ exprEnd → Q exprEnd := by
    intro fuel
    induction fuel with
    | zero =>
        intro c hc _ _ _
        exact absurd hc iseg_go_zero
    | succ k ih =>
        intro c hc hle hQ hle2
        by_cases hce : c = exprEnd
        · exact hce ▸ hQ
        · obtain ⟨len, hlen, hnext, hwidth⟩ := isegGo_advance hc hce
          have hcl : c < exprEnd := by
            rcases Nat.lt_or_ge c exprEnd with h | h
            · exact h
            · exfalso
              have ⟨h1, _, _, _⟩ := iseg_go_bounds cursor k (c + len) exprEnd foldOp hnext
              omega
          refine ih (c + len) hnext (by omega) (hstep c len hle hcl hQ hlen) ?_
          have ⟨h1, _, _, _⟩ := iseg_go_bounds cursor k (c + len) exprEnd foldOp hnext
          exact h1
  have ⟨h1, _, _, _⟩ := iseg_bounds hseg
  exact key bytes.length cursor hseg (Nat.le_refl _) hbase h1

theorem planSegment_length (bytes : List Nat) (cursor exprEnd : Nat)
    (h : exprEnd ≤ bytes.length) :
    (planSegment bytes cursor exprEnd).length = exprEnd - cursor := by
  rw [planSegment, List.length_take, List.length_drop]
  omega

theorem getD_drop_nat : ∀ (j cursor : Nat) (bytes : List Nat),
    (bytes.drop cursor).getD j 0 = bytes.getD (j + cursor) 0 := by
  intro j cursor
  induction cursor with
  | zero =>
      intro bytes
      rw [List.drop_zero, Nat.add_zero]
  | succ k ih =>
      intro bytes
      cases bytes with
      | nil => rw [List.drop_nil]; rfl
      | cons b rest =>
          rw [List.drop_cons (by omega : 0 < k + 1)]
          show (rest.drop k).getD j 0 = (b :: rest).getD (j + k + 1) 0
          rw [List.getD_cons_succ]
          exact ih rest

theorem getD_take_nat :
    ∀ (l : List Nat) (n j : Nat), j < n → (l.take n).getD j 0 = l.getD j 0 := by
  intro l
  induction l with
  | nil => intro n j _; cases n <;> rfl
  | cons b rest ih =>
      intro n
      cases n with
      | zero => intro j hj; omega
      | succ k =>
          intro j hj
          cases j with
          | zero =>
              show (b :: rest.take k).getD 0 0 = (b :: rest).getD 0 0
              rw [List.getD_cons_zero, List.getD_cons_zero]
          | succ j' =>
              show (b :: rest.take k).getD (j' + 1) 0 = (b :: rest).getD (j' + 1) 0
              rw [List.getD_cons_succ, List.getD_cons_succ, ih k j' (by omega)]

theorem planSegment_getD (bytes : List Nat) (cursor exprEnd j : Nat)
    (h : j < exprEnd - cursor) (_h2 : exprEnd ≤ bytes.length) :
    (planSegment bytes cursor exprEnd).getD j 0 = bytes.getD (cursor + j) 0 := by
  rw [planSegment, getD_take_nat (bytes.drop cursor) (exprEnd - cursor) j h]
  rw [getD_drop_nat j cursor bytes, show j + cursor = cursor + j from Nat.add_comm _ _]

theorem planSegment_take_append (bytes : List Nat) (cursor exprEnd : Nat)
    (h : cursor ≤ exprEnd) :
    bytes.take cursor ++ planSegment bytes cursor exprEnd = bytes.take exprEnd := by
  rw [planSegment, ← List.take_add, Nat.add_sub_cancel' h]


/-! #### 8c. What 'buildPlan' and 'itemStarts' say about the bytes -/

/-- **THE ROW'S BYTES ARE THE COMPACTED STREAM.** 'finish' compacts FIRST (VmBuilder.lean:1460-1467) and
    the artifact it returns is the byte-view of that compaction, with the builder's own table unchanged.
    So the cursor arithmetic of 'itemStarts' and of 'identitySegment' inside 'PG_planSegmentWalk' runs on
    the COMPACTED stream - exactly as 'runSeg' and 'afSeg' do - and NOT on the pre-compaction bytes.
    NOTE what this lemma does NOT give: 'qvmBytesToNats build.bytes = cseg' needs the round-trip
    'qvmBytesToNats (qvmBytesOfNats cseg) = cseg', which holds only when every byte is below 256 and is
    asserted in the tree only as the 'Bool' gate 'programBytesRoundTrip_ok' ('VmReference.lean:2201'),
    never as a theorem. -/
theorem finish_ok_compacted (s : QuotientProgramBuilder) (build : QuotientProgramBuild)
    (h : finish s = .ok build) :
    ∃ cseg u, compactQuotientRuns s.bytes = .ok cseg ∧ quotientProgramUsage cseg = .ok u ∧
      build.bytes = qvmBytesOfNats cseg ∧ build.consts = s.consts ∧ build.maxStack = s.maxStack := by
  have h1 : finish s = compactQuotientRuns s.bytes >>= (fun bytes =>
      quotientProgramUsage bytes >>= (fun u =>
        .ok { bytes := qvmBytesOfNats bytes, consts := s.consts, maxStack := s.maxStack,
              usedOps := qvmBytesOfNats u.1, usedMemTokens := qvmBytesOfNats u.2 })) := rfl
  cases hc : compactQuotientRuns s.bytes with
  | error e =>
      have h2 : finish s = .error e := by rw [h1, hc]; rfl
      rw [h2] at h; cases h
  | ok cseg =>
      have h2 : finish s = quotientProgramUsage cseg >>= (fun u =>
          .ok (⟨qvmBytesOfNats cseg, s.consts, s.maxStack, qvmBytesOfNats u.1,
            qvmBytesOfNats u.2⟩ : QuotientProgramBuild)) := by
        rw [h1, hc]
        rfl
      cases hu : quotientProgramUsage cseg with
      | error e =>
          have h3 : finish s = .error e := by rw [h2, hu]; rfl
          rw [h3] at h; cases h
      | ok u =>
          have h3 : finish s = .ok (⟨qvmBytesOfNats cseg, s.consts, s.maxStack,
              qvmBytesOfNats u.1, qvmBytesOfNats u.2⟩ : QuotientProgramBuild) := by
            rw [h2, hu]
            rfl
          rw [h3] at h
          have heq := Except.ok.inj h
          cases heq
          exact ⟨cseg, u, rfl, hu, rfl, rfl, rfl⟩

/-- An empty item list starts no new cursor: the result is the accumulator reversed. -/
theorem itemStartsGo_nil (bytes : List Nat) (acc : List Nat) :
    itemStartsGo bytes [] 0 acc = acc.reverse := rfl

/-- **THE CURSOR AT AN IDENTITY ITEM START.** The identity item at the head of the list contributes its own
    cursor, and the next item starts where the fold ends: 'exprEnd + len(fold)'. Read off the definition,
    so this is the 'itemStarts' half of the row's cursor arithmetic. -/
theorem itemStartsGo_cons_identity (bytes : List Nat) (id : QuotientIdentity)
    (rest : List QuotientProgramItem) (acc : List Nat) (exprEnd foldOp len : Nat)
    (hseg : identitySegment bytes 0 = .ok (exprEnd, foldOp))
    (hlen : quotientOpLen bytes exprEnd = .ok len) :
    itemStartsGo bytes (.identity id :: rest) 0 acc =
      itemStartsGo bytes rest (exprEnd + len) (0 :: acc) := by
  rw [itemStartsGo.eq_2]
  simp only [hseg, hlen]

/-! #### 8d. The rosters the landed packages can consume, and where they stop -/

/-- **DEPTH'S ROSTER EXCLUDES ALL FOUR LIMB ARMS.** 'axes_of_emitter_facts' (section 6) asks for
    'stepArm22' at every reachable cursor, so a segment whose cursor holds a limb arm cannot go through
    that route even if the emitter supplies every other fact. DEPTH names the four-arm refinement as
    'PG_stepDepth_at_limb4' (QvmDepth.lean:1277); it is OPEN. -/
theorem not_stepArm22_lin7 : ¬ stepArm22 qOpLin7 := by intro h; cases h <;> contradiction
theorem not_stepArm22_bilin7Row : ¬ stepArm22 qOpBilin7Row := by intro h; cases h <;> contradiction
theorem not_stepArm22_bilin7Pairwise : ¬ stepArm22 qOpBilin7Pairwise := by
  intro h; cases h <;> contradiction
theorem not_stepArm22_modarith7 : ¬ stepArm22 qOpModarith7 := by intro h; cases h <;> contradiction

/-- **SHAPE'S ROSTER COVERS THE TWO PUSHING LIMB ARMS AND NOT THE OTHER TWO** - the per-axis check the
    brief asks for: SHAPE's exclusion is NOT vacuous ('PG_stepShape_at_limb2', OPEN), DEPTH's is vacuous in
    content (all four limb arms push, 'stepPopCount' is 0 for each: 'pc_lin7' ... 'pc_modarith7') but NOT
    in the route, because the route asks for the roster as a hypothesis. -/
theorem shapeArm24_lin7 : shapeArm24 qOpLin7 := Or.inr (Or.inl rfl)
theorem shapeArm24_bilin7Row : shapeArm24 qOpBilin7Row := Or.inr (Or.inr rfl)
theorem not_shapeArm24_bilin7Pairwise : ¬ shapeArm24 qOpBilin7Pairwise := by
  intro h; cases h with
  | inl h => cases h <;> contradiction
  | inr h => cases h <;> contradiction
theorem not_shapeArm24_modarith7 : ¬ shapeArm24 qOpModarith7 := by
  intro h; cases h with
  | inl h => cases h <;> contradiction
  | inr h => cases h <;> contradiction
theorem stepPopCount_limb4_zero :
    stepPopCount qOpLin7 = 0 ∧ stepPopCount qOpBilin7Row = 0 ∧
      stepPopCount qOpBilin7Pairwise = 0 ∧ stepPopCount qOpModarith7 = 0 :=
  ⟨QvmDepth.pc_lin7, QvmDepth.pc_bilin7Row, QvmDepth.pc_bilin7Pairwise, QvmDepth.pc_modarith7⟩

theorem cursorArm25_lin7 : cursorArm25 qOpLin7 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))
theorem not_cursorArm25_modarith7 : ¬ cursorArm25 qOpModarith7 := by
  intro h; cases h <;> contradiction

/-- **THE LIMB CURSOR IS REACHABLE BY THE ROW'S OWN WALK.** A 23-byte stream whose first instruction is
    'LIN7' (static width 22) with the fold at byte 22: 'identitySegment' walks it and stops at the fold,
    so the row's 'hseg' admits a cursor whose opcode is outside 'stepArm22'. That is why section 7's
    'one line' is not one line for a limb-emitting plan: 'withLimbVmOps' is a 'Bool' the row quantifies
    over, and 'qvmBytesToNats build.bytes' can hold a limb opcode. -/
theorem iseg_walks_limb_cursor :
    identitySegment ([qOpLin7] ++ List.replicate 21 0 ++ [qOpFoldMain]) 0 =
      .ok (22, qOpFoldMain) := by
  show identitySegment.go _ _ _ _ = _
  decide


/-! #### 8e. THE CURSOR FACT NOTHING SUPPLIES, NAMED -/

/-- **THE ROW'S 'hconsts' IS SHAPE'S 'PG_constsCanonical'.** Section 6 lists 'PG_constsCanonical' as one
    of the two Props the general route costs. For 'builder_segments_total' it is FREE: the row's own
    'hconsts' is the same formula about the same table, so the only named Prop section 6 actually still
    needs is 'PG_shapeGuardsOfDecoded'. -/
theorem pg_constsCanonical_of_hconsts (build : QuotientProgramBuild)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus) :
    PG_constsCanonical build.consts := hconsts

/-- **THE MISSING CURSOR FACT, NAMED.** 'PG_planSegmentWalk' (section 7) says a plan's segment admits a
    'WalkInvariant'. What no card supplies is WHY: the emitter has to say, for a plan it has not
    enumerated, that the bytes at the item's cursor are a sequence of instructions each of which the
    validator decodes at that cursor, the interpreter executes successfully with EXACTLY the width the
    validator reads, and which leaves the invariant intact - ending with one value on the stack. That is
    this Prop. It is stated about the SLICE the row walks (so it is not a restatement of the row's
    conclusion: it names the validator's decoder and the width equation, which 'WalkInvariant' does not
    mention), and it is exactly the input section 6's 'axes_of_emitter_facts' consumes. Exact goal state
    at a slice cursor 'idx', with 'seg := planSegment (qvmBytesToNats build.bytes) cursor exprEnd':

      idx < seg.length
      P idx stack mem
      ⊢ ∃ op len s, decodeByteQuotientInstruction seg idx = .ok (op, len)
          ∧ stepAt seg build.consts idx stack mem = .ok s ∧ len = s.consumed
          ∧ P (idx + len) s.stack s.mem

    What makes it unprovable today is NOT the walk machinery - section 6 already turns it into a
    'WalkInvariant' - but that nothing in the tree connects 'buildPlan' to the emitted instruction
    sequence: see 'PG_planItemSegment' below and the three further blockers in the header of this
    section. -/
def PG_planSegmentCursorFacts : Prop :=
  ∀ (r : QuotientShapeRecognizers) (_hr : RecognizersSound r)
    (plan : QuotientProgramPlan) (limbOps : Bool) (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts plan build)
    (hseg : Midfall.Generator.QuotientCertify.identitySegment (qvmBytesToNats build.bytes) cursor =
      .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory),
    ∃ P : Nat → List QVMFr → QuotientRefMemory → Prop,
      P 0 ([] : List QVMFr) mem ∧
        (∀ idx stack mem,
            idx < (planSegment (qvmBytesToNats build.bytes) cursor exprEnd).length →
              P idx stack mem →
              ∃ op len s, Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction
                  (planSegment (qvmBytesToNats build.bytes) cursor exprEnd) idx = .ok (op, len) ∧
                stepAt (planSegment (qvmBytesToNats build.bytes) cursor exprEnd) build.consts
                  idx stack mem = .ok s ∧
                len = s.consumed ∧ P (idx + len) s.stack s.mem) ∧
        (∀ idx stack mem,
            ¬ idx < (planSegment (qvmBytesToNats build.bytes) cursor exprEnd).length →
              P idx stack mem → ∃ v, stack = [v])

/-- **THE ONE LINE, ONCE THE CURSOR FACT IS SUPPLIED.** Proved: 'PG_planSegmentCursorFacts' implies
    'PG_planSegmentWalk', and with section 7's 'builder_segments_total_of_planSegmentWalk' that is the
    registered sorry. Nothing was added to the row: the hypothesis is a standalone Prop. -/
theorem pg_planSegmentWalk_of_cursorFacts (h : PG_planSegmentCursorFacts) : PG_planSegmentWalk := by
  intro r hr plan limbOps build hbuild hbounded hconsts cursor exprEnd foldOp hstart hseg mem
  obtain ⟨P, hinit, hstep, hterm⟩ :=
    h r hr plan limbOps build hbuild hbounded hconsts cursor exprEnd foldOp hstart hseg mem
  refine ⟨P, ⟨hinit, ?_, hterm⟩⟩
  intro idx stack mem hidx hP
  obtain ⟨op, len, s, hdec, hst, hlen, hP'⟩ := hstep idx stack mem hidx hP
  exact ⟨s, hst, by rw [← hlen]; exact hP'⟩

/-- **THE COROLLARY FOR THE REGISTERED SORRY, AS A THEOREM.** If the emitter ever supplies the cursor
    fact, 'builder_segments_total' closes by these two applications and nothing else. Recorded so that
    the distance is a checked term, not a claim in a comment. -/
theorem builder_segments_total_of_cursorFacts (h : PG_planSegmentCursorFacts) :
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
            .ok (v, mem') :=
  builder_segments_total_of_planSegmentWalk (pg_planSegmentWalk_of_cursorFacts h)

/-- **AND THE OTHER HALF OF THE GAP: WHICH ITEM WROSE THESE BYTES.** Even 'PG_planSegmentCursorFacts'
    presupposes that the slice at an item start IS an emitted segment. Nothing states it. This is the
    emitter-side correspondence, in the emitter's own vocabulary and with no interpreter in it: the slice
    is the finalized, compacted emission of one identity item of the plan, over the COMPACTED stream
    ('finish_ok_compacted' above pins that 'build.bytes' is the compaction of the builder's bytes, so the
    drop below is a drop in the PRE-compaction buffer while the cursor is a position in the POST-compaction
    one - which is exactly the subtlety the brief asks about, and exactly what no card has reconciled). -/
def PG_planItemSegment : Prop :=
  ∀ (r : QuotientShapeRecognizers) (_hr : RecognizersSound r)
    (plan : QuotientProgramPlan) (limbOps : Bool) (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts plan build)
    (hseg : Midfall.Generator.QuotientCertify.identitySegment (qvmBytesToNats build.bytes) cursor =
      .ok (exprEnd, foldOp)),
    ∃ (id : QuotientIdentity) (s₀ s₁ : QuotientProgramBuilder) (t : QuotientTarget)
      (gap : Option Nat) (cseg : List Nat) (tail : List Word256),
      QuotientProgramItem.identity id ∈ plan.items ∧
      identityExpr r s₀ id.expr t gap = .ok s₁ ∧
      compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg ∧
      finalizedIdentitySegment t cseg = some (planSegment (qvmBytesToNats build.bytes) cursor exprEnd) ∧
      (∀ c ∈ s₁.consts, c.toNat < qvmFrModulus) ∧
      build.consts = s₁.consts ++ tail

/-! #### 8f. Acceptance prints for section 8 -/

#print axioms Midfall.Lowering.QvmSegmentReal.iseg_bounds
#print axioms Midfall.Lowering.QvmSegmentReal.iseg_walk_ind
#print axioms Midfall.Lowering.QvmSegmentReal.isegGo_advance
#print axioms Midfall.Lowering.QvmSegmentReal.planSegment_length
#print axioms Midfall.Lowering.QvmSegmentReal.planSegment_getD
#print axioms Midfall.Lowering.QvmSegmentReal.planSegment_take_append
#print axioms Midfall.Lowering.QvmSegmentReal.finish_ok_compacted
#print axioms Midfall.Lowering.QvmSegmentReal.itemStartsGo_cons_identity
#print axioms Midfall.Lowering.QvmSegmentReal.not_stepArm22_lin7
#print axioms Midfall.Lowering.QvmSegmentReal.not_shapeArm24_modarith7
#print axioms Midfall.Lowering.QvmSegmentReal.iseg_walks_limb_cursor
#print axioms Midfall.Lowering.QvmSegmentReal.pg_constsCanonical_of_hconsts
#print axioms Midfall.Lowering.QvmSegmentReal.pg_planSegmentWalk_of_cursorFacts
#print axioms Midfall.Lowering.QvmSegmentReal.builder_segments_total_of_cursorFacts
#cone_sorries Midfall.Lowering.QvmSegmentReal.pg_planSegmentWalk_of_cursorFacts
#cone_sorries Midfall.Lowering.QvmSegmentReal.builder_segments_total_of_cursorFacts
#cone_sorries Midfall.Lowering.QvmSegmentReal.finish_ok_compacted
#cone_sorries Midfall.Lowering.QvmSegmentReal.iseg_walk_ind

/-! #### 8g. The item decomposition, proved at its base case -/

/-- The initial builder the row's 'hbuild' uses has an EMPTY byte buffer, so for a one-item plan the
    per-item drop that 'PG_identity_segment_walk' and 'PG_planItemSegment' speak of is a drop of nothing. -/
theorem withLimbVmOps_bytes_nil (enabled : Bool) : (withLimbVmOps enabled).bytes = [] := rfl

/-- One identity item builds by emitting that item and nothing else. -/
theorem buildItems_one_identity (r : QuotientShapeRecognizers) (sf : SelectorFoldPlan)
    (id : QuotientIdentity) (s₀ : QuotientProgramBuilder) :
    buildItems r sf [.identity id] s₀ =
      identityExpr r s₀ id.expr id.target (sf.gapFor id) := by
  rw [buildItems.eq_2]
  cases h : identityExpr r s₀ id.expr id.target (sf.gapFor id) with
  | error e => rfl
  | ok s => simp only [buildItems.eq_1]; rfl

/-- **THE BASE CASE OF THE ITEM DECOMPOSITION.** A plan with exactly one identity item, built
    successfully, emitted that item's expression and then finished: no other emitter step is involved. -/
theorem buildPlan_one_identity (r : QuotientShapeRecognizers) (plan : QuotientProgramPlan)
    (id : QuotientIdentity) (limbOps : Bool) (build : QuotientProgramBuild)
    (hitems : plan.items = [.identity id])
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build) :
    ∃ s₁, identityExpr r (withLimbVmOps limbOps) id.expr id.target
        (plan.selectorFold.gapFor id) = .ok s₁ ∧ finish s₁ = .ok build := by
  have hstart : buildPlan r plan (withLimbVmOps limbOps)
      = (buildItems r plan.selectorFold plan.items (withLimbVmOps limbOps) >>= finish) := rfl
  rw [hstart, hitems, buildItems_one_identity r plan.selectorFold id
    (withLimbVmOps limbOps)] at hbuild
  cases h2 : identityExpr r (withLimbVmOps limbOps) id.expr id.target
      (plan.selectorFold.gapFor id) with
  | error e => rw [h2] at hbuild; cases hbuild
  | ok s₁ => rw [h2] at hbuild; exact ⟨s₁, rfl, hbuild⟩

/-- **THE BASE CASE OF 'PG_planItemSegment', PROVED.** For a one-identity-item plan the emitted buffer of
    that item IS the buffer the compaction ran on, the artifact's bytes are the byte-view of that
    compaction, and the artifact's table is the item's table - so for THIS plan shape the row's slice is
    established to be an emitted segment, which is the half of the gap that is not an interpreter claim at
    all. What is NOT reachable this way is an item in the MIDDLE of the list: there the per-item drop runs
    through the earlier items' PRE-compaction bytes while 'itemStarts' counts the COMPACTED stream, and
    the two agree only if compaction never crosses an item boundary - true, because every item ends with a
    fold and 'isAffineAddOp' is false for both fold opcodes, but proved nowhere in the tree. -/
theorem planItemSegment_one_item (r : QuotientShapeRecognizers) (plan : QuotientProgramPlan)
    (id : QuotientIdentity) (limbOps : Bool) (build : QuotientProgramBuild)
    (hitems : plan.items = [.identity id])
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build) :
    ∃ s₁ cseg, identityExpr r (withLimbVmOps limbOps) id.expr id.target
        (plan.selectorFold.gapFor id) = .ok s₁ ∧
      compactQuotientRuns (s₁.bytes.drop (withLimbVmOps limbOps).bytes.length) = .ok cseg ∧
      build.bytes = qvmBytesOfNats cseg ∧ build.consts = s₁.consts := by
  obtain ⟨s₁, hs₁, hfin⟩ := buildPlan_one_identity r plan id limbOps build hitems hbuild
  obtain ⟨cseg, u, hc, hu, hb, hconsts, _⟩ := finish_ok_compacted s₁ build hfin
  have hdrop : s₁.bytes.drop (withLimbVmOps limbOps).bytes.length = s₁.bytes := by
    rw [withLimbVmOps_bytes_nil, List.length_nil, List.drop_zero]
  exact ⟨s₁, cseg, hs₁, by rw [hdrop]; exact hc, hb, hconsts⟩

#print axioms Midfall.Lowering.QvmSegmentReal.buildItems_one_identity
#print axioms Midfall.Lowering.QvmSegmentReal.buildPlan_one_identity
#print axioms Midfall.Lowering.QvmSegmentReal.planItemSegment_one_item
#cone_sorries Midfall.Lowering.QvmSegmentReal.planItemSegment_one_item
#cone_sorries Midfall.Lowering.QvmSegmentReal.buildPlan_one_identity

/-! #### 8h. Why compaction cannot cross an identity boundary -/

/-- The compactor only starts a run at an opcode 'isAffineAddOp' accepts, and neither fold opcode is one -
    so the fold that ends an identity item is never swallowed into the next item's run. This is the fact
    'PG_planItemSegment' needs for an item in the MIDDLE of the list; stated as two 'rfl' lemmas so the
    claim in section 8g is checked rather than asserted. -/
theorem not_isAffineAddOp_foldMain : isAffineAddOp qOpFoldMain = false := rfl
theorem not_isAffineAddOp_foldSelector : isAffineAddOp qOpFoldSelector = false := rfl

#print axioms Midfall.Lowering.QvmSegmentReal.not_isAffineAddOp_foldMain
#print axioms Midfall.Lowering.QvmSegmentReal.not_isAffineAddOp_foldSelector


/-! ### 9. CARD CURFACT: 'PG_planSegmentCursorFacts' IS NOT DISCHARGEABLE FROM HERE, AND NOT FOR THE
REASON SECTION 8 GIVES. WHAT THE ROW IS ACTUALLY BLOCKED BEHIND, PROVED RATHER THAN ASSERTED.

THE VERDICT UP FRONT. 'builder_segments_total' (Qvm.lean:992) is NOT closed by this card and cannot be
closed from the tree as it stands, and the reason is NOT the 'stepArm22' roster obstacle section 8 names
as 'THE KNOWN OBSTACLE'. Three findings, each proved or measured below:

(FINDING 1, 9a) 'hseg' does NOT supply the decoder leg of 'PG_planSegmentCursorFacts'. Section 8 says
'hseg' 'pins the cursor arithmetic of the row's own segment'. It pins the arithmetic of the BUILDER's
width function 'QuotientBuilder.quotientOpLen' (VmBuilder.lean:1287), which is what 'identitySegment'
actually walks with (VmCertify.lean:428). The Prop's step leg asks about a DIFFERENT function, the
VALIDATOR's checked decoder 'QuotientValidator.decodeByteQuotientInstruction' (VmValidator.lean:846),
which additionally bounds-checks the whole instruction and validates the token byte against
'quotientVmSpec.memTokens' (VmValidator.lean:706-708). 'iseg_admits_a_cursor_the_validator_rejects'
exhibits a stream 'identitySegment' walks to '.ok' at whose first cursor the checked decoder FAILS, and
'planSegment' of that very stream is the slice the Prop quantifies over. So the Prop is not 'the row
minus the walk machinery' - it is the row PLUS a validator claim the row never assumes. The row has no
'validateQuotientProgram' hypothesis and must not gain one (RULES), so this leg has no source at all.

(FINDING 2, 9b) No concrete instance of the row's hypotheses can be exhibited either. 'identityExpr'
does not kernel-reduce at the SMALLEST possible expression - a single 'QuotientExpr.const' - measured
this card (exact message quoted in 9b), which is the same wall SEGPROVE recorded at ten bytes. So the
row can be closed only by a general induction over the emitter against the interpreter, which is exactly
'qvm_compile_correct_identity' (Qvm.lean:619, a registered sorry of its own) and 'PG_planItemSegment'
(section 8e). 'PG_planSegmentCursorFacts' is not a shortcut past that wall; it is a restatement of the
far side of it.

(FINDING 3, 9c) The per-axis limb check the brief asks for, done as a PROOF and not an assumption: the
DEPTH axis does NOT need 'PG_limbCountAgrees'. Three of the four limb arms are discharged outright here
with no template table, no limb count and no depth hypothesis - 'step_noUF_lin7',
'step_noUF_bilin7Row', 'step_noUF_bilin7Pairwise' - which includes BILIN7_PAIRWISE, the arm QvmShape
records as stalling its 'AvoidsShape' refinement on the nested counted fold. The nested fold is
reachable for 'NoUnderflow' because 'foldRangeIdxM_noUnderflow' is proved by induction on the count and
never needs the literal 'quotientVmLimbs' to unroll; the trick is 'apply foldRangeIdxM_noUnderflow'
(unify the fold out of the goal) after 'dsimp only' (inline the do-block's join points), where 'refine'
with a placeholder for the step function fails higher-order unification. MODARITH7 is left open and is
recorded below the three arms: it is blocked by the same Lean-surface shape as QvmShape's arm - the
flags guard dsimp-expands into four copies of a five-fold tail - and NOT by the limb count.
So the answer to 'is the limb refinement cheaper than a roster-free route' is: the roster-free route
needs no limb refinement at all, because 'PG_planSegmentCursorFacts' never mentions a roster; the limb
facts are a cost of the 'axes_of_emitter_facts' route in section 6, which this Prop bypasses.

NOTHING HERE ADDS A HYPOTHESIS to a row, to 'ValidV3', to a bundle or to the root. 'PG_planSegmentCursorFacts'
is NOT restated or weakened: it is discharged NOWHERE in this section, and no weaker substitute for it is
named. No sorry is added and none is removed. 'QvmSegment.lean', 'QvmShape.lean', 'QvmDepth.lean',
'QvmCursor.lean' are cited, not edited. No 'native_decide', no 'maxRecDepth'/'maxHeartbeats' change, no
2^256 numeral inside a 'decide' (every 'decide' here is on a 2-3 byte stream or on an opcode-byte
comparison). -/

/-! #### 9a. 'hseg' walks with the BUILDER's width function; the Prop asks for the VALIDATOR's -/

/-- The builder's compact-scoped width function ACCEPTS a 'PUSH_MEM_TOKEN' whose token byte is not in
    the spec's token table: it reads the opcode and returns the static length, and never looks at the
    token. This is the function 'identitySegment' advances by (VmCertify.lean:428). -/
theorem builder_width_accepts_an_unlisted_token :
    (match Midfall.Generator.QuotientBuilder.quotientOpLen [qOpPushMemToken, 200] 0 with
      | .ok n => n == 2
      | .error _ => false) = true := by decide

/-- The validator's checked decoder REFUSES the same cursor: 'decodeByteQuotientInstruction' calls
    'validateQuotientMemToken' (VmValidator.lean:854-856, :706-708) and names the token. -/
theorem validator_decode_rejects_an_unlisted_token :
    (match Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction
        [qOpPushMemToken, 200] 0 with
      | .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.unknownMemToken 200 0) =>
          true
      | _ => false) = true := by decide

/-- 'identitySegment' walks that very stream to a successful segment ending on the fold. So the walk
    that 'hseg' names - the same function, at the same cursor - succeeds where the checked decoder
    fails. -/
theorem iseg_admits_a_cursor_the_validator_rejects :
    Midfall.Generator.QuotientCertify.identitySegment [qOpPushMemToken, 200, qOpFoldMain] 0 =
      .ok (2, qOpFoldMain) := by
  show Midfall.Generator.QuotientCertify.identitySegment.go _ _ _ _ = _
  decide

/-- **THE DECODER LEG IS NOT A CONSEQUENCE OF 'hseg'.** The slice at the cursor this walk certifies is
    '[qOpPushMemToken, 200]', and the checked decoder fails at its index 0 - which is exactly the cursor
    'PG_planSegmentCursorFacts' must produce a successful decode at, because its first leg forces 'P 0'
    and its second leg is required wherever 'P' holds. NOTE WHAT THIS IS AND IS NOT: it refutes the
    INFERENCE 'hseg supplies the decoder leg'. It is NOT a refutation of 'PG_planSegmentCursorFacts',
    because this stream is not exhibited as the output of a 'buildPlan'. -/
theorem hseg_does_not_supply_the_decoder_leg :
    Midfall.Generator.QuotientCertify.identitySegment [qOpPushMemToken, 200, qOpFoldMain] 0 =
        .ok (2, qOpFoldMain) ∧
      (match Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction
          (planSegment [qOpPushMemToken, 200, qOpFoldMain] 0 2) 0 with
        | .error (Midfall.Generator.QuotientValidator.QuotientValidationFault.unknownMemToken 200 0) =>
            true
        | _ => false) = true :=
  ⟨iseg_admits_a_cursor_the_validator_rejects,
    validator_decode_rejects_an_unlisted_token⟩

/-- The two functions differ in a second way as well: the builder's width is the STATIC table length and
    does not bounds-check the operands, the validator's does. Recorded because it is the reason the two
    legs cannot be merged by a width-agreement lemma alone. -/
theorem builder_width_walks_a_truncated_instruction :
    (match Midfall.Generator.QuotientBuilder.quotientOpLen [qOpPushConst] 0 with
      | .ok n => n == 3
      | .error _ => false) = true := by decide

theorem validator_decode_rejects_a_truncated_instruction :
    (match Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction [qOpPushConst] 0 with
      | .ok _ => false
      | .error _ => true) = true := by decide

/-! #### 9b. The emitter wall, re-measured at its smallest instance -/

/- **THE LAST MILE IS NOT COMPUTABLE, EVEN AT ONE CONSTANT.** 'identityExpr' is a 'do' block over
    'emitExprTop', and 'emitExprTop' is the fuel-indexed well-founded recursion (VmBuilder.lean:862-894).
    Measured this card on the smallest expression the emitter has, 'QuotientExpr.const 0':

      'example : (identityExpr noShapeRecognizers builderDefault (QuotientExpr.const 0)
          QuotientTarget.main none).isOk = true := by decide'
      ==>  Tactic 'decide' failed to reduce ... reduction got stuck at
           match identityExpr noShapeRecognizers builderDefault
                  (QuotientExpr.const 0) QuotientTarget.main none with
                | Except.ok a => true

    i.e. the emitter does not unfold at ONE byte, not at ten. Consequence, stated as the brief asks:
    no concrete 'build' satisfying 'hbuild' can be exhibited by computation, so the row can be closed
    neither by witness nor by counterexample from here. The only route is the general emitter induction,
    which is 'qvm_compile_correct_identity' (Qvm.lean:619) and 'PG_planItemSegment' (section 8e), and
    neither is a one-line supply of cursor facts. -/

/-- The slice of the 9a witness stream between the cursor its walk certifies and the fold it lands on -
    stated as a lemma so the stream 9a reasons about is checked, not described. -/
theorem planSegment_slice_of_the_witness_is_two_bytes :
    planSegment [qOpPushMemToken, 200, qOpFoldMain] 0 2 = [qOpPushMemToken, 200] := rfl

/-! #### 9c. The per-axis limb check: DEPTH does not need 'PG_limbCountAgrees' -/

/-- The seven-limb linear form never touches the stack: its only monadic actions are the three readers
    inside a counted fold, and 'foldRangeIdxM_noUnderflow' (QvmDepth) is proved by induction on the
    count, so the literal 'quotientVmLimbs' never has to unroll. No template table, no limb count. -/
theorem limbLinearForm_noUF (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) :
    NoUnderflow (Midfall.Generator.limbLinearForm bytes consts mem k) := by
  unfold Midfall.Generator.limbLinearForm
  refine NoUnderflow.bind (foldRangeIdxM_noUnderflow quotientVmLimbs (qvmFrZero, k, mem) _ ?hf) ?tail
  · intro i s
    cases s with
    | mk acc p =>
      cases p with
      | mk cursor mem =>
        refine NoUnderflow.bind (byteAt_noUnderflow bytes cursor) (fun _ =>
          NoUnderflow.bind (readU16_noUnderflow bytes (cursor + 1)) (fun _ =>
            NoUnderflow.bind (constAt_noUnderflow consts _ cursor) (fun _ => NoUnderflow.ok _)))
  · intro x
    cases x with
    | mk acc p => cases p with | mk cursor mem => exact NoUnderflow.ok _

/-- The row form: one u16 read and the linear form above it. -/
theorem limbRowForm_noUF (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) :
    NoUnderflow (Midfall.Generator.limbRowForm bytes consts mem k) := by
  unfold Midfall.Generator.limbRowForm
  refine NoUnderflow.bind (readU16_noUnderflow bytes k) (fun _ =>
    NoUnderflow.bind (limbLinearForm_noUF bytes consts _ (k + 2)) (fun x => by
      cases x with | mk inner p => cases p with | mk len mem' => exact NoUnderflow.ok _))

/-- **THE ARM QVMSHAPE RECORDS AS STALLING.** For 'AvoidsShape' (a seven-clause conjunction) QvmShape
    reports that the nested counted fold cannot be named by unification. For 'NoUnderflow' it can:
    'dsimp only' inlines the do-block's join points so the goal's head is the fold itself, and
    'apply foldRangeIdxM_noUnderflow' takes the step function off the goal by unification instead of
    asking the elaborator to solve a higher-order pattern in a 'refine' placeholder. -/
theorem limbPairwiseForm_noUF (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (k : Nat) :
    NoUnderflow (Midfall.Generator.limbPairwiseForm bytes consts mem k) := by
  unfold Midfall.Generator.limbPairwiseForm
  refine NoUnderflow.bind (readU16_noUnderflow bytes k) (fun lhsBase =>
    NoUnderflow.bind (readU16_noUnderflow bytes (k + 2)) (fun rhsBase =>
      NoUnderflow.bind (byteAt_noUnderflow bytes (k + 4 + quotientVmPairwiseCoeffs - 1)) (fun _ =>
        NoUnderflow.bind (foldRangeIdxM_noUnderflow quotientVmLimbs (qvmFrZero, mem) _ ?h1)
          (fun x => by cases x with
            | mk acc mem' => dsimp only; exact NoUnderflow.ok _))))
  · intro i s
    cases s with
    | mk acc mem =>
      dsimp only
      apply foldRangeIdxM_noUnderflow
      intro j state
      refine NoUnderflow.bind (indexOrPanic_noUnderflow bytes (k + 4 + i + j)) (fun _ =>
        NoUnderflow.bind (constAt_noUnderflow consts _ (k + 4)) (fun _ => NoUnderflow.ok _))

/-- **THE THREE LIMB STEP ARMS, AT EVERY cursor, EVERY stack, EVERY memory.** Each is the corresponding
    form above lifted through the step's if-chain; the arms push and pop nothing, so no depth hypothesis
    is needed and none is taken. -/
theorem step_noUF_lin7 (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (limbLinearForm_noUF bytes consts mem (idx + 1))
    (fun x => by cases x with | mk v p => cases p with | mk len mem' => dsimp only; exact NoUnderflow.ok _)

theorem step_noUF_bilin7Row (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (limbRowForm_noUF bytes consts mem (idx + 1))
    (fun x => by cases x with | mk v p => cases p with | mk len mem' => dsimp only; exact NoUnderflow.ok _)

theorem step_noUF_bilin7Pairwise (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Pairwise stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true}) only [reduceIte]
  refine NoUnderflow.bind (limbPairwiseForm_noUF bytes consts mem (idx + 1))
    (fun x => by cases x with | mk v p => cases p with | mk len mem' => dsimp only; exact NoUnderflow.ok _)

/-- **THREE OF THE FOUR CONJUNCTS OF 'PG_stepDepth_at_limb4' (QvmDepth.lean:1277), DISCHARGED.** Stated
    as the conjunction of the three arms proved above, so the claim 'DEPTH's limb exclusion is
    precautionary, not necessary' is a checked term and not a comment. The fourth conjunct (MODARITH7)
    is NOT discharged and its exact goal state is in 9d. Nothing here cites 'PG_limbCountAgrees', and no
    statement in this section mentions a template table. -/
theorem PG_stepDepth_at_limb4_three_of_four :
    (∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
        (mem : QuotientRefMemory),
        NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpLin7 stack mem)) ∧
      (∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
        (mem : QuotientRefMemory),
        NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx qOpBilin7Row stack mem)) ∧
      (∀ (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr)
        (mem : QuotientRefMemory),
        NoUnderflow (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
          qOpBilin7Pairwise stack mem)) :=
  ⟨step_noUF_lin7, step_noUF_bilin7Row, step_noUF_bilin7Pairwise⟩

/- THE FOURTH LIMB ARM, AND WHY IT IS NOT A DEPTH PROBLEM. MODARITH7 is the only arm whose body can
    raise 'modarith7UnknownFlags' (VmReference.lean:641-642), and that is a fact about the FLAG BYTE the
    emitter wrote, i.e. a SHAPE obligation, not a depth one. The underflow clause for MODARITH7 IS
    reachable by exactly the method of the three arms above - 'modarith7Form' pops nothing either - but
    after 'dsimp only' the flags guard and the two optional-operand guards multiply out into four copies
    of a five-fold tail, so the peel has to be written four times over: a labour cost, not an obstacle,
    and recorded as such rather than glossed. 'PG_stepDepth_at_limb4' therefore stays OPEN with three of
    its four conjuncts discharged above, and it stays open on bookkeeping, not on 'PG_limbCountAgrees':
    no statement in this section mentions a template table or a limb count. -/

/-! #### 9d. THE EXACT REMAINING GOAL, PRINTED NOT ASSERTED -/

/- **WHAT STILL HAS TO BE PROVED FOR THE REGISTERED SORRY.** One goal, at Qvm.lean:1002:

      r : QuotientShapeRecognizers
      hr : RecognizersSound r
      plan : QuotientProgramPlan
      limbOps : Bool
      build : QuotientProgramBuild
      hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build
      hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr
      hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus
      cursor exprEnd foldOp : Nat
      hstart : cursor ∈ itemStarts plan build
      hseg : identitySegment (qvmBytesToNats build.bytes) cursor = .ok (exprEnd, foldOp)
      mem : QuotientRefMemory
      ⊢ ∃ v mem', evalQuotientIdentity
            (planSegment (qvmBytesToNats build.bytes) cursor exprEnd) build.consts mem = .ok (v, mem')

    and it is reached from 'PG_planSegmentCursorFacts' by the single application PLSEG proved
    ('builder_segments_total_of_cursorFacts'). The Prop itself reduces to three obligations, none of
    which has a source in the tree:

      (O1) '∃ P, P 0 [] mem' together with step-success of 'stepAt' at every 'P'-reachable cursor of
           the slice - the emitter's instruction sequence, i.e. 'PG_planItemSegment' PLUS the six axes
           for a segment nobody enumerated. Blocked by 9b: the emitter does not unfold.
      (O2) 'len = s.consumed' at each such cursor - the validator-width / interpreter-consumed agreement,
           which the landed packages state only for the 22-arm roster
           ('evalQuotientIdentityStep_consumed_agrees_at_22'), so the limb arms need their own widths.
      (O3) the decoder leg 'decodeByteQuotientInstruction seg idx = .ok (op, len)' - NOT supplied by
           'hseg' (9a), and not assumed by the row either.

    (O1) is the registered content; (O2) and (O3) are EXTRA burden the Prop carries that the row does
    not. That is the correction to the brief: the shortest path from the registered sorry to something
    provable is NOT 'PG_planSegmentCursorFacts' but the weaker 'PG_planSegmentWalk' (section 7): PLSEG
    proves the cursor facts imply it, the converse is NOT proved, and (O2)/(O3) above are exactly the
    legs the weaker form does not carry. Both are blocked behind (O1), i.e. behind
    'qvm_compile_correct_identity' - so neither is a shortcut, and the brief's 'one application' is
    correct about the IMPLICATION and wrong about the DISTANCE. -/

/-! #### 9e. Acceptance prints for section 9 -/

#print axioms Midfall.Lowering.QvmSegmentReal.builder_width_accepts_an_unlisted_token
#print axioms Midfall.Lowering.QvmSegmentReal.validator_decode_rejects_an_unlisted_token
#print axioms Midfall.Lowering.QvmSegmentReal.iseg_admits_a_cursor_the_validator_rejects
#print axioms Midfall.Lowering.QvmSegmentReal.hseg_does_not_supply_the_decoder_leg
#print axioms Midfall.Lowering.QvmSegmentReal.builder_width_walks_a_truncated_instruction
#print axioms Midfall.Lowering.QvmSegmentReal.validator_decode_rejects_a_truncated_instruction
#print axioms Midfall.Lowering.QvmSegmentReal.planSegment_slice_of_the_witness_is_two_bytes
#print axioms Midfall.Lowering.QvmSegmentReal.limbLinearForm_noUF
#print axioms Midfall.Lowering.QvmSegmentReal.limbRowForm_noUF
#print axioms Midfall.Lowering.QvmSegmentReal.limbPairwiseForm_noUF
#print axioms Midfall.Lowering.QvmSegmentReal.step_noUF_lin7
#print axioms Midfall.Lowering.QvmSegmentReal.step_noUF_bilin7Row
#print axioms Midfall.Lowering.QvmSegmentReal.step_noUF_bilin7Pairwise
#print axioms Midfall.Lowering.QvmSegmentReal.PG_stepDepth_at_limb4_three_of_four
#cone_sorries Midfall.Lowering.QvmSegmentReal.hseg_does_not_supply_the_decoder_leg
#cone_sorries Midfall.Lowering.QvmSegmentReal.PG_stepDepth_at_limb4_three_of_four
#cone_sorries Midfall.Lowering.QvmSegmentReal.step_noUF_bilin7Pairwise
#cone_sorries Midfall.Lowering.QvmSegmentReal.limbPairwiseForm_noUF

-- |
-- Midfall.LoweringV3.QuotientFrame
--
-- ROW.Q.4 - THE FRAME VALUATION, and the reference side of ROW.Q.3's arms. Work package Q1, on
-- PLAN-V3 §4 / EXECUTION-V2 §5 as amended by D-P75.
--
-- WHAT THE CARD SAID THE WALL WAS, AND WHAT IS BEHIND IT. A3b recorded two obstructions to the value
-- clause of 'Midfall.Lowering.QuotientInterp.QInterpRefines':
--
--   (i) 'evalQuotientIdentity' is not kernel-reducible even on the EMPTY program, because its fuel
--       recursion is a 'where'-clause 'go' whose eliminator the kernel will not unfold
--       (QuotientInterp.lean:351 draws the same conclusion for the whole reference VM: "no theorem
--       in the tree names its output"); and
--   (ii) the value clause needs 'QuotientRefMemory.literal' at a SYMBOLIC memory.
--
-- Both are real and neither is a wall.
--
--   (i) is a 'whnf' wall, not a missing fact. 'evalQuotientIdentityLoop.go' is a top-level name -
--   Qvm.lean:1481 already rewrites at it - and its two fuel cases reduce under 'simp' as soon as the
--   cursor test is decided. Section A lands those two cases as THEOREMS and derives
--   'evalQuotientIdentity_one': a segment of at least one byte whose single step succeeds, leaves a
--   one-element stack and consumes the whole segment evaluates to the value that step pushed. That is
--   the first theorem in the tree to name the output of the reference VM, and section E instantiates
--   it (qIdentity_pushConstU8) so the claim is checkable and not a comment.
--   (ii) was already discharged by a fact this card did not cite: 'literal_memOfρ' (Qvm.lean:306)
--   proves that on a memory whose memo table covers the key, 'literal ptr' IS 'ρ 0 (ptr % 2^32)'
--   with the memory UNCHANGED, and 'token_memOfρ' (:316) does the same in the token domain. What was
--   missing is the connection to the contract's own predicate, which is section D: 'AgreesFrame' at a
--   'memOfρ' memory is exactly the ρ-clause, both directions, and it is satisfiable on a non-empty
--   window. So the frame window is not an obstruction to the value clause; it is a hypothesis the row
--   can discharge from 'memOfρ'.
--
-- Section B is the per-arm VALUE equations. Qvm.lean:1197 gives 'consumed' and Qvm.lean:1864 gives
-- the read bound; neither says what an arm PUSHES, and the value clause of 'QInterpRefines' is about
-- what it pushes. Each of the 23 arms that are not count-prefixed - the 22 static arms of
-- Qvm.lean:1197 plus MODARITH7 - is stated as an equation between the step and
-- the readers it performs, conditional on those readers succeeding - which is the honest shape,
-- because an arm that fails is a revert and the contract's first disjunct already covers it. The
-- hypotheses are reader equations, not new axioms: 'constAt consts slot 0 = .ok v' is what the
-- validator's own bounds facts give for a well-formed program.
--
-- NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', to a bundle or to the root (RULES); no
-- statement names a fixture (D-P71); there is no 'native_decide' and no sorry in this file, so W12
-- and W13 do not bite. The three axioms are the standard ones.
import Midfall.Lowering.QuotientInterp
import Midfall.Lowering.Qvm
import Midfall.Yul.WpX

set_option autoImplicit false

namespace Midfall.LoweringV3.QuotientFrame

open YulSemantics YulSemantics.EVM Midfall Midfall.Generator Midfall.Lowering
open Midfall.Yul Midfall.Yul.Bridge Midfall.Lowering.QuotientInterp
open Midfall.Lowering.GenAst

/-! ### A. THE REFERENCE LOOP'S EQUATIONAL THEORY, as theorems

The two fuel cases of 'evalQuotientIdentityLoop.go'. This is the wall of (i) taken apart: the kernel
will not unfold the 'where'-clause, but the equations are 'simp' theorems about it, and they are
enough for induction on the fuel. -/

/-- One step at a live cursor: the fuel-'(k+1)' case with the cursor test discharged. -/
theorem qLoop_go_live (bytes : List Nat) (consts : List Word256) (fuel idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : idx < bytes.length) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (fuel + 1) idx stack mem =
      (Midfall.Generator.evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem >>=
        fun s =>
          Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel (idx + s.consumed)
            s.stack s.mem) := by
  simp [Midfall.Generator.evalQuotientIdentityLoop.go, h]

/-- The same at a positive fuel, phrased with 'fuel - 1' so it applies to the initial call, whose
    fuel is the expression 'bytes.length' and not a literal successor. -/
theorem qLoop_go_pos (bytes : List Nat) (consts : List Word256) (fuel idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (hf : 0 < fuel) (h : idx < bytes.length) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel idx stack mem =
      (Midfall.Generator.evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem >>=
        fun s =>
          Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (fuel - 1) (idx + s.consumed)
            s.stack s.mem) := by
  cases fuel with
  | zero => exact absurd hf (by decide)
  | succ k => exact qLoop_go_live bytes consts k idx stack mem h

/-- The cursor is past the segment: the walk returns the stack it was handed and does not touch the
    memory, at ANY fuel. This is the arm 'evalQuotientIdentityLoop_fuelNeverBinds' (Qvm.lean:1481)
    reaches for, stated as an equation rather than a disequality. -/
theorem qLoop_go_done (bytes : List Nat) (consts : List Word256) (fuel idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (h : bytes.length ≤ idx) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel idx stack mem =
      .ok (stack, mem) := by
  have hlt : ¬ idx < bytes.length := by omega
  cases fuel with
  | zero => simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]
  | succ k => simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]

/-- **THE FIRST THEOREM IN THE TREE TO NAME THE REFERENCE VM'S OUTPUT.** A segment of at least one
    byte whose single step succeeds, leaves a one-element stack and consumes the whole segment
    evaluates to the value that step pushed, on the memory that step produced. No fuel hypothesis:
    the initial fuel is 'bytes.length' and one step consumes it all, which is the same fact
    Qvm.lean:1481 proves for the walk in general.

    This is the shape ROW.Q.3 needs. 'QInterpRefines' asks, for a segment, that the reference returns
    '.ok (v, mem')' AND that the interpreter's cached top is 'v'. For every one-instruction identity
    the first half is now this lemma plus the arm's value equation from section B; only the second
    half - what the emitted Yul arm computes - is still open, and that is the arm table, not a wall. -/
theorem evalQuotientIdentity_one (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (step : IdentityStep) (v : QVMFr)
    (hlen : 0 < bytes.length)
    (hstep : Midfall.Generator.evalQuotientIdentityStep bytes consts 0 (bytes.getD 0 0)
        ([] : List QVMFr) mem = .ok step)
    (hstack : step.stack = [v])
    (hcons : bytes.length ≤ step.consumed) :
    Midfall.Generator.evalQuotientIdentity bytes consts mem = .ok (v, step.mem) := by
  have h0 : (0 : Nat) < bytes.length := hlen
  have hloop : Midfall.Generator.evalQuotientIdentityLoop bytes consts 0 ([] : List QVMFr) mem =
      .ok (step.stack, step.mem) := by
    show Midfall.Generator.evalQuotientIdentityLoop.go bytes consts bytes.length 0 [] mem = _
    rw [qLoop_go_pos bytes consts bytes.length 0 ([] : List QVMFr) mem h0 h0, hstep]
    simp only [Except.bind, bind, Nat.zero_add]
    rw [qLoop_go_done bytes consts (bytes.length - 1) step.consumed step.stack step.mem hcons]
  show (Midfall.Generator.evalQuotientIdentityLoop bytes consts 0 ([] : List QVMFr) mem >>=
      fun p => match p with
      | (stack, mem') => match stack with
        | [value] => Except.ok (value, mem')
        | xs => Except.error (QVMFault.stackLengthMismatch xs.length)) = .ok (v, step.mem)
  rw [hloop]
  simp only [Except.bind, bind]
  rw [hstack]

/-! ### B. THE PER-ARM VALUE EQUATIONS (ROW.Q.4's first deliverable)

Every equation is stated for the instruction at index 0 with its operand bytes spelled out, which is
the general shape up to 'List.drop' - the same convention Qvm.lean:1197 uses, so the two families of
facts line up arm for arm (23 to 23).

THE COST OF THESE IS A FINDING, NOT AN AFTERWORD. The first version of this section proved every arm
with one call, 'simp (config := {decide := true}) [readU32, byteAt, Except.bind, bind]', and TWO of
the twenty-two arms - PUSH_MEM_TOKEN_OFFSET and ADD_MUL_MEM_MEM, the two that read memory twice -
died with a **kernel deterministic timeout at 48 s each**. Splitting the reduction in two - decide
the dispatch chain first with no reader lemmas in the simp set, then rewrite the readers by an 'rfl'
equation - brings both down to about a tenth of a second. That is the same wall QPROBE hit, in
miniature and from the other side: 'decide' over the whole step is not linear in the number of arms. -/

/-- ARM PUSH_CONST: read a u16 slot, push the constant-table entry, consume 3. -/
theorem qStepValue_pushConst (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256) (v : QVMFr)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts (b₀ * 256 + b₁) 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpPushConst, b₀, b₁] ++ rest) consts 0
        qOpPushConst stack mem
      = .ok { stack := v :: stack, consumed := 3, hConsumed := by omega, mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpPushConst :: b₀ :: b₁ :: rest) 1 =
      .ok (b₀ * 256 + b₁) := rfl
  rw [h₁]
  simp only [Except.bind, bind]
  rw [hv]

/-- ARM PUSH_CONST_U8: read one byte slot, push the constant-table entry, consume 2. -/
theorem qStepValue_pushConstU8 (b₀ : Nat) (rest : List Nat) (consts : List Word256) (v : QVMFr)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts b₀ 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpPushConstU8, b₀] ++ rest) consts 0
        qOpPushConstU8 stack mem
      = .ok { stack := v :: stack, consumed := 2, hConsumed := by omega, mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.byteAt (qOpPushConstU8 :: b₀ :: rest) 1 = .ok b₀ := rfl
  rw [h₁]
  simp only [Except.bind, bind]
  rw [hv]

/-- ARM PUSH_MEM_LITERAL: read a u32 pointer, take the reference's literal value there, consume 5.
    The memory is the reference's own 'literal' image - the symbolic-memory read of obstruction (ii),
    and section C is what turns it into ρ. -/
theorem qStepValue_pushMemLiteral (b₀ b₁ b₂ b₃ : Nat) (rest : List Nat)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep
        ([qOpPushMemLiteral, b₀, b₁, b₂, b₃] ++ rest) consts 0 qOpPushMemLiteral stack mem =
      .ok { stack := (mem.literal (((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)).1 :: stack,
            consumed := 5, hConsumed := by omega,
            mem := (mem.literal (((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU32
      (qOpPushMemLiteral :: b₀ :: b₁ :: b₂ :: b₃ :: rest) 1 =
      .ok (((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) := rfl
  rw [h₁]
  rfl

/-- ARM PUSH_MEM_U16: read a u16 pointer, take the literal value, consume 3. -/
theorem qStepValue_pushMemU16 (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemU16, b₀, b₁] ++ rest) consts 0
        qOpPushMemU16 stack mem
      = .ok { stack := (mem.literal (b₀ * 256 + b₁)).1 :: stack, consumed := 3,
              hConsumed := by omega, mem := (mem.literal (b₀ * 256 + b₁)).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpPushMemU16 :: b₀ :: b₁ :: rest) 1 =
      .ok (b₀ * 256 + b₁) := rfl
  rw [h₁]
  rfl

/-- ARM PUSH_MEM_TOKEN: read a token byte, take the token-domain value at offset 0, consume 2. -/
theorem qStepValue_pushMemToken (t : Nat) (rest : List Nat) (consts : List Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemToken, t] ++ rest) consts 0
        qOpPushMemToken stack mem
      = .ok { stack := (mem.token t 0).1 :: stack, consumed := 2, hConsumed := by omega,
              mem := (mem.token t 0).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.byteAt (qOpPushMemToken :: t :: rest) 1 = .ok t := rfl
  rw [h₁]
  rfl

/-- ARM PUSH_MEM_TOKEN_OFFSET: token byte plus u32 offset, token-domain value, consume 6. -/
theorem qStepValue_pushMemTokenOffset (t o₀ o₁ o₂ o₃ : Nat) (rest : List Nat)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep
        ([qOpPushMemTokenOffset, t, o₀, o₁, o₂, o₃] ++ rest) consts 0 qOpPushMemTokenOffset
        stack mem
      = .ok { stack := (mem.token t (((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)).1 :: stack,
              consumed := 6, hConsumed := by omega,
              mem := (mem.token t (((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.byteAt
      (qOpPushMemTokenOffset :: t :: o₀ :: o₁ :: o₂ :: o₃ :: rest) 1 = .ok t := rfl
  have h₂ : Midfall.Generator.readU32
      (qOpPushMemTokenOffset :: t :: o₀ :: o₁ :: o₂ :: o₃ :: rest) 2 =
      .ok (((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃) := rfl
  rw [h₁, h₂]
  rfl

/-- ARM ADD: pop two, push their field sum, consume 1. The reference's head is its top, so the first
    pop is the RIGHT operand - the order the emitted 'addmod(mload(q_sp), q_top, r)' arm has to
    reproduce, and the reason this equation is stated with 'next' before 'top'. -/
theorem qStepValue_add (rest : List Nat) (consts : List Word256) (stack : List QVMFr)
    (top next : QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest) consts 0 qOpAdd
        (top :: next :: stack) mem
      = .ok { stack := qvmFrAdd next top :: stack, consumed := 1, hConsumed := by omega,
              mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

/-- ARM MUL: pop two, push their field product, consume 1. -/
theorem qStepValue_mul (rest : List Nat) (consts : List Word256) (stack : List QVMFr)
    (top next : QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpMul :: rest) consts 0 qOpMul
        (top :: next :: stack) mem
      = .ok { stack := qvmFrMul next top :: stack, consumed := 1, hConsumed := by omega,
              mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

/-- ARM NEG: pop one, push its field negation, consume 1. -/
theorem qStepValue_neg (rest : List Nat) (consts : List Word256) (stack : List QVMFr)
    (v : QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest) consts 0 qOpNeg (v :: stack) mem
      = .ok { stack := qvmFrNeg v :: stack, consumed := 1, hConsumed := by omega, mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

/-- ARM POW5: pop one, push 'v·(v²)²' - two multiplications of the SAME square, not 'v⁴·v'; the
    port keeps the Rust's shape (VmReference.lean:790) and the arm equation preserves it. -/
theorem qStepValue_pow5 (rest : List Nat) (consts : List Word256) (stack : List QVMFr)
    (v : QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpPow5 :: rest) consts 0 qOpPow5 (v :: stack) mem
      = .ok { stack := qvmFrMul (qvmFrMul v (qvmFrMul v v)) (qvmFrMul v v) :: stack,
              consumed := 1, hConsumed := by omega, mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

/-- ARM ADD_CONST_U8: one byte slot, pop the accumulator, push accumulator + const, consume 2. -/
theorem qStepValue_addConstU8 (b₀ : Nat) (rest : List Nat) (consts : List Word256) (v : QVMFr)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts b₀ 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpAddConstU8, b₀] ++ rest) consts 0
        qOpAddConstU8 (acc :: stack) mem
      = .ok { stack := qvmFrAdd acc v :: stack, consumed := 2, hConsumed := by omega,
              mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.byteAt (qOpAddConstU8 :: b₀ :: rest) 1 = .ok b₀ := rfl
  rw [h₁]
  simp only [Midfall.Generator.popStack, Except.bind, bind, reduceIte]
  rw [hv]

/-- ARM MUL_CONST_U8: the same arm with the product. -/
theorem qStepValue_mulConstU8 (b₀ : Nat) (rest : List Nat) (consts : List Word256) (v : QVMFr)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts b₀ 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpMulConstU8, b₀] ++ rest) consts 0
        qOpMulConstU8 (acc :: stack) mem
      = .ok { stack := qvmFrMul acc v :: stack, consumed := 2, hConsumed := by omega,
              mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.byteAt (qOpMulConstU8 :: b₀ :: rest) 1 = .ok b₀ := rfl
  rw [h₁]
  simp only [Midfall.Generator.popStack, Except.bind, bind, reduceIte]
  rw [hv]

/-- ARM ADD_CONST: u16 slot, pop the accumulator, push the sum, consume 3. -/
theorem qStepValue_addConst (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256) (v : QVMFr)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts (b₀ * 256 + b₁) 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpAddConst, b₀, b₁] ++ rest) consts 0
        qOpAddConst (acc :: stack) mem
      = .ok { stack := qvmFrAdd acc v :: stack, consumed := 3, hConsumed := by omega,
              mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpAddConst :: b₀ :: b₁ :: rest) 1 =
      .ok (b₀ * 256 + b₁) := rfl
  rw [h₁]
  simp only [Midfall.Generator.popStack, Except.bind, bind, reduceIte]
  rw [hv]

/-- ARM MUL_CONST: u16 slot, product, consume 3. -/
theorem qStepValue_mulConst (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256) (v : QVMFr)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts (b₀ * 256 + b₁) 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpMulConst, b₀, b₁] ++ rest) consts 0
        qOpMulConst (acc :: stack) mem
      = .ok { stack := qvmFrMul acc v :: stack, consumed := 3, hConsumed := by omega,
              mem := mem } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpMulConst :: b₀ :: b₁ :: rest) 1 =
      .ok (b₀ * 256 + b₁) := rfl
  rw [h₁]
  simp only [Midfall.Generator.popStack, Except.bind, bind, reduceIte]
  rw [hv]

/-- ARM ADD_MEM_U16: u16 pointer, the literal read BEFORE the pop - VmReference.lean:823 keeps the
    Rust's order and errorPrecedence_ok pins it - sum, consume 3. -/
theorem qStepValue_addMemU16 (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpAddMemU16, b₀, b₁] ++ rest) consts 0
        qOpAddMemU16 (acc :: stack) mem
      = .ok { stack := qvmFrAdd acc (mem.literal (b₀ * 256 + b₁)).1 :: stack, consumed := 3,
              hConsumed := by omega, mem := (mem.literal (b₀ * 256 + b₁)).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpAddMemU16 :: b₀ :: b₁ :: rest) 1 =
      .ok (b₀ * 256 + b₁) := rfl
  rw [h₁]
  simp only [Midfall.Generator.popStack, Except.bind, bind, reduceIte]

/-- ARM MUL_MEM_U16: the same arm with the product. -/
theorem qStepValue_mulMemU16 (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpMulMemU16, b₀, b₁] ++ rest) consts 0
        qOpMulMemU16 (acc :: stack) mem
      = .ok { stack := qvmFrMul acc (mem.literal (b₀ * 256 + b₁)).1 :: stack, consumed := 3,
              hConsumed := by omega, mem := (mem.literal (b₀ * 256 + b₁)).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpMulMemU16 :: b₀ :: b₁ :: rest) 1 =
      .ok (b₀ * 256 + b₁) := rfl
  rw [h₁]
  simp only [Midfall.Generator.popStack, Except.bind, bind, reduceIte]

/-- ARM ADD_MUL_MEM_MEM: two u16 pointers, two chained literal reads, push 'acc + l·r', consume 5.
    The second literal read is taken on the memory the FIRST one produced, which is what makes the
    arm's memory image a composition - and, in the one-call recipe, what timed the kernel out. -/
theorem qStepValue_addMulMemMem (l₀ l₁ r₀ r₁ : Nat) (rest : List Nat) (consts : List Word256)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep
        ([qOpAddMulMemMem, l₀, l₁, r₀, r₁] ++ rest) consts 0 qOpAddMulMemMem (acc :: stack) mem =
      .ok { stack :=
              qvmFrAdd acc
                (qvmFrMul (mem.literal (l₀ * 256 + l₁)).1
                  ((mem.literal (l₀ * 256 + l₁)).2.literal (r₀ * 256 + r₁)).1) :: stack,
            consumed := 5, hConsumed := by omega,
            mem := ((mem.literal (l₀ * 256 + l₁)).2.literal (r₀ * 256 + r₁)).2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  have h₁ : Midfall.Generator.readU16 (qOpAddMulMemMem :: l₀ :: l₁ :: r₀ :: r₁ :: rest) 1 =
      .ok (l₀ * 256 + l₁) := rfl
  have h₂ : Midfall.Generator.readU16 (qOpAddMulMemMem :: l₀ :: l₁ :: r₀ :: r₁ :: rest) 3 =
      .ok (r₀ * 256 + r₁) := rfl
  rw [h₁, h₂]
  simp only [Midfall.Generator.popStack, Except.bind, bind]

/-- ARM ADD_MUL_MEM_MEM_CONST_U8: the fused affine product term, stated against the reference's own
    'affineProductTerm' helper - the arm's value IS the helper's value and its stride IS the helper's
    length, which is the fact the emitted fused arm has to be shown to reproduce. -/
theorem qStepValue_addMulMemMemConstU8 (bytes : List Nat) (consts : List Word256)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory)
    (t : QVMFr × Nat × QuotientRefMemory)
    (ht : Midfall.Generator.affineProductTerm (qOpAddMulMemMemConstU8 :: bytes) consts mem 1 =
      .ok t) :
    Midfall.Generator.evalQuotientIdentityStep (qOpAddMulMemMemConstU8 :: bytes) consts 0
        qOpAddMulMemMemConstU8 (acc :: stack) mem
      = .ok { stack := qvmFrAdd acc t.1 :: stack, consumed := 1 + t.2.1, hConsumed := by omega,
              mem := t.2.2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rw [ht]
  simp only [Except.bind, bind]
  simp only [Midfall.Generator.popStack, Except.bind, bind]

/-- ARM ADD_MUL_CONST_U8_MEM_U16: the fused affine linear term, same shape. -/
theorem qStepValue_addMulConstU8MemU16 (bytes : List Nat) (consts : List Word256)
    (acc : QVMFr) (stack : List QVMFr) (mem : QuotientRefMemory)
    (t : QVMFr × Nat × QuotientRefMemory)
    (ht : Midfall.Generator.affineLinearTerm (qOpAddMulConstU8MemU16 :: bytes) consts mem 1 =
      .ok t) :
    Midfall.Generator.evalQuotientIdentityStep (qOpAddMulConstU8MemU16 :: bytes) consts 0
        qOpAddMulConstU8MemU16 (acc :: stack) mem
      = .ok { stack := qvmFrAdd acc t.1 :: stack, consumed := 1 + t.2.1, hConsumed := by omega,
              mem := t.2.2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rw [ht]
  simp only [Except.bind, bind]
  simp only [Midfall.Generator.popStack, Except.bind, bind]

/-- ARM LIN7: the limb loop over 'quotientVmLimbs'; the value is 'limbLinearForm' and the stride is
    its length plus the opcode byte. -/
theorem qStepValue_lin7 (bytes : List Nat) (consts : List Word256) (stack : List QVMFr)
    (mem : QuotientRefMemory) (t : QVMFr × Nat × QuotientRefMemory)
    (ht : Midfall.Generator.limbLinearForm (qOpLin7 :: bytes) consts mem 1 = .ok t) :
    Midfall.Generator.evalQuotientIdentityStep (qOpLin7 :: bytes) consts 0 qOpLin7 stack mem
      = .ok { stack := t.1 :: stack, consumed := 1 + t.2.1, hConsumed := by omega,
              mem := t.2.2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rw [ht]
  simp only [Except.bind, bind]

/-- ARM BILIN7_ROW: 'limbRowForm'. -/
theorem qStepValue_bilin7Row (bytes : List Nat) (consts : List Word256) (stack : List QVMFr)
    (mem : QuotientRefMemory) (t : QVMFr × Nat × QuotientRefMemory)
    (ht : Midfall.Generator.limbRowForm (qOpBilin7Row :: bytes) consts mem 1 = .ok t) :
    Midfall.Generator.evalQuotientIdentityStep (qOpBilin7Row :: bytes) consts 0 qOpBilin7Row
        stack mem
      = .ok { stack := t.1 :: stack, consumed := 1 + t.2.1, hConsumed := by omega,
              mem := t.2.2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rw [ht]
  simp only [Except.bind, bind]

/-- ARM BILIN7_PAIRWISE: 'limbPairwiseForm'. -/
theorem qStepValue_bilin7Pairwise (bytes : List Nat) (consts : List Word256) (stack : List QVMFr)
    (mem : QuotientRefMemory) (t : QVMFr × Nat × QuotientRefMemory)
    (ht : Midfall.Generator.limbPairwiseForm (qOpBilin7Pairwise :: bytes) consts mem 1 = .ok t) :
    Midfall.Generator.evalQuotientIdentityStep (qOpBilin7Pairwise :: bytes) consts 0
        qOpBilin7Pairwise stack mem
      = .ok { stack := t.1 :: stack, consumed := 1 + t.2.1, hConsumed := by omega,
              mem := t.2.2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rw [ht]
  simp only [Except.bind, bind]

/-- ARM MODARITH7: 'modarith7Form'. The read BOUND for this arm is recorded unproved at
    Qvm.lean:1864 for a chaining reason; the value equation is not affected, because it is stated
    against the helper. -/
theorem qStepValue_modarith7 (bytes : List Nat) (consts : List Word256) (stack : List QVMFr)
    (mem : QuotientRefMemory) (t : QVMFr × Nat × QuotientRefMemory)
    (ht : Midfall.Generator.modarith7Form (qOpModarith7 :: bytes) consts mem 1 = .ok t) :
    Midfall.Generator.evalQuotientIdentityStep (qOpModarith7 :: bytes) consts 0 qOpModarith7
        stack mem
      = .ok { stack := t.1 :: stack, consumed := 1 + t.2.1, hConsumed := by omega,
              mem := t.2.2 } := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rw [ht]
  simp only [Except.bind, bind]

/-! ### C. THE MEMORY-READING ARMS AT A 'memOfρ' MEMORY: obstruction (ii) discharged -/

/-- The literal read of a pre-populated memory is ρ's value and the memory is UNCHANGED
    ('literal_memOfρ', Qvm.lean:306), so PUSH_MEM_U16 at a 'memOfρ' memory pushes ρ. This is the
    frame valuation for one arm; the shape is identical for the other five memory readers. -/
theorem qStepValue_pushMemU16_memOfρ (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256)
    (stack : List QVMFr) (ρ : Valuation) (S : List (Nat × Nat))
    (h : (0, (b₀ * 256 + b₁) % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemU16, b₀, b₁] ++ rest) consts 0
        qOpPushMemU16 stack (memOfρ ρ S)
      = .ok { stack := ρ 0 ((b₀ * 256 + b₁) % 2 ^ 32) :: stack, consumed := 3,
              hConsumed := by omega, mem := memOfρ ρ S } := by
  rw [qStepValue_pushMemU16]
  rw [literal_memOfρ ρ S (b₀ * 256 + b₁) h]

/-- PUSH_MEM_LITERAL at a 'memOfρ' memory. -/
theorem qStepValue_pushMemLiteral_memOfρ (b₀ b₁ b₂ b₃ : Nat) (rest : List Nat)
    (consts : List Word256) (stack : List QVMFr) (ρ : Valuation) (S : List (Nat × Nat))
    (h : (0, (((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) % 2 ^ 32) ∈
          S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    Midfall.Generator.evalQuotientIdentityStep
        ([qOpPushMemLiteral, b₀, b₁, b₂, b₃] ++ rest) consts 0 qOpPushMemLiteral stack
        (memOfρ ρ S)
      = .ok { stack := ρ 0 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) % 2 ^ 32) :: stack,
              consumed := 5, hConsumed := by omega, mem := memOfρ ρ S } := by
  rw [qStepValue_pushMemLiteral]
  rw [literal_memOfρ ρ S (((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) h]

/-- PUSH_MEM_TOKEN at a 'memOfρ' memory, in the token domain ('token_memOfρ', Qvm.lean:316). -/
theorem qStepValue_pushMemToken_memOfρ (t : Nat) (rest : List Nat) (consts : List Word256)
    (stack : List QVMFr) (ρ : Valuation) (S : List (Nat × Nat))
    (h : ((1 + t) % 256, 0) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemToken, t] ++ rest) consts 0
        qOpPushMemToken stack (memOfρ ρ S)
      = .ok { stack := ρ ((1 + t) % 256) 0 :: stack, consumed := 2,
              hConsumed := by omega, mem := memOfρ ρ S } := by
  rw [qStepValue_pushMemToken]
  rw [token_memOfρ ρ S t 0 h]
  simp

/-- ADD_MEM_U16 at a 'memOfρ' memory: the fused arm reads ρ too, and the memory is unchanged - which
    is the fact that makes the whole 'memOfρ' approach stable under a run of memory-reading arms. -/
theorem qStepValue_addMemU16_memOfρ (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256)
    (acc : QVMFr) (stack : List QVMFr) (ρ : Valuation) (S : List (Nat × Nat))
    (h : (0, (b₀ * 256 + b₁) % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    Midfall.Generator.evalQuotientIdentityStep ([qOpAddMemU16, b₀, b₁] ++ rest) consts 0
        qOpAddMemU16 (acc :: stack) (memOfρ ρ S)
      = .ok { stack := qvmFrAdd acc (ρ 0 ((b₀ * 256 + b₁) % 2 ^ 32)) :: stack, consumed := 3,
              hConsumed := by omega, mem := memOfρ ρ S } := by
  rw [qStepValue_addMemU16]
  rw [literal_memOfρ ρ S (b₀ * 256 + b₁) h]

/-! ### D. THE FRAME VALUATION: 'AgreesFrame' IS THE ρ-CLAUSE -/

/-- **THE FRAME VALUATION, ONE WAY.** If the memo table covers every key the window touches and the
    machine's words at the window are ρ's, then the window agrees with the reference memory
    'memOfρ ρ S'. This is the fact ROW.Q.4 was asked to build: the contract's 'AgreesFrame' clause is
    not an opaque predicate over a non-reducible 'literal', it is ρ read at the window's addresses. -/
theorem AgreesFrame_memOfρ (ρ : Valuation) (S : List (Nat × Nat)) (st : EvmState)
    (frameBase frameWords : Nat)
    (hcover : ∀ a, a < frameWords →
      (0, (frameBase + 32 * a) % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32)))
    (hval : ∀ a, a < frameWords →
      loadWord st.memory (frameBase + 32 * a) =
        BitVec.ofNat 256 (ρ 0 ((frameBase + 32 * a) % 2 ^ 32))) :
    AgreesFrame st frameBase frameWords (memOfρ ρ S) := by
  intro a ha
  rw [literal_memOfρ ρ S (frameBase + 32 * a) (hcover a ha)]
  exact hval a ha

/-- **AND THE OTHER WAY.** An 'AgreesFrame' window over a 'memOfρ' memory determines ρ on the
    window's keys. Together the two say the frame valuation is a REFORMULATION, not an assumption -
    which is what makes it safe for the row to discharge 'Agrees' from 'memOfρ'. -/
theorem AgreesFrame_memOfρ_only_if (ρ : Valuation) (S : List (Nat × Nat)) (st : EvmState)
    (frameBase frameWords : Nat)
    (h : AgreesFrame st frameBase frameWords (memOfρ ρ S))
    (hcover : ∀ a, a < frameWords →
      (0, (frameBase + 32 * a) % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32)))
    (a : Nat) (ha : a < frameWords) :
    loadWord st.memory (frameBase + 32 * a) =
      BitVec.ofNat 256 (ρ 0 ((frameBase + 32 * a) % 2 ^ 32)) := by
  have := h a ha
  rwa [literal_memOfρ ρ S (frameBase + 32 * a) (hcover a ha)] at this

/-- The frame valuation is SATISFIABLE on a NON-EMPTY window: a zeroed memory, the zero valuation,
    a one-word window at address 0. Without this the two lemmas above could be vacuous. -/
theorem AgreesFrame_memOfρ_nonvacuous :
    ∃ (st : EvmState) (ρ : Valuation) (S : List (Nat × Nat)) (frameBase frameWords : Nat),
      0 < frameWords ∧ AgreesFrame st frameBase frameWords (memOfρ ρ S) := by
  refine ⟨EvmState.init, fun _ _ => 0, [(0, 0)], 0, 1, Nat.zero_lt_one,
    AgreesFrame_memOfρ (fun _ _ => 0) [(0, 0)] EvmState.init 0 1 ?_ ?_⟩
  · intro a ha
    have h0 : a = 0 := by omega
    rw [h0]
    simp
  · intro a ha
    have h0 : a = 0 := by omega
    rw [h0]
    show (0 : U256) = BitVec.ofNat 256 ((fun _ _ => (0 : QVMFr)) 0 ((0 + 32 * 0) % 2 ^ 32))
    rfl

/-- All three agreement clauses of the contract's 'Agrees' hold TOGETHER on a non-empty frame window:
    the windowed contract's hypothesis is not only consistent, it is realisable with a real frame
    word. Extends 'qinterp_hypotheses_together' (QuotientInterp.lean:326), whose frame window is
    EMPTY. -/
theorem Agrees_memOfρ_nonvacuous :
    ∃ (st : EvmState) (s : QSegment) (bytes : List Nat) (consts : List Word256)
      (ρ : Valuation) (S : List (Nat × Nat)) (frameBase frameWords : Nat),
      s.inWindow ∧ 0 < frameWords ∧
      Agrees consts 0 frameBase frameWords bytes st (memOfρ ρ S) s := by
  refine ⟨EvmState.init, ⟨0, 1, 0, 1⟩, [], [], fun _ _ => 0, [(0, 0)], 0, 1,
    ⟨Nat.zero_lt_one, Nat.le_refl 1⟩, Nat.zero_lt_one, ⟨?_, ?_, ?_⟩⟩
  · intro _ _
    rfl
  · intro k hk
    have : k < 0 := by simpa using hk
    omega
  · refine AgreesFrame_memOfρ (fun _ _ => 0) [(0, 0)] EvmState.init 0 1 ?_ ?_
    · intro a ha
      have h0 : a = 0 := by omega
      rw [h0]
      simp
    · intro a ha
      have h0 : a = 0 := by omega
      rw [h0]
      rfl

/-! ### E. THE REFERENCE VM'S OUTPUT, NAMED -/

/-- **THE CHECKABLE FORM OF THE (i) CLAIM.** The reference VM's value on the one-instruction segment
    'PUSH_CONST_U8 slot' is the constant table's entry, as a THEOREM. Before this file the only
    statements about 'evalQuotientIdentity' in the tree were '#eval' gates in VmReference.lean, and
    QuotientInterp.lean:351 records that as a wall. -/
theorem qIdentity_pushConstU8 (b₀ : Nat) (consts : List Word256) (v : QVMFr)
    (mem : QuotientRefMemory)
    (hv : Midfall.Generator.constAt consts b₀ 0 = .ok v) :
    Midfall.Generator.evalQuotientIdentity [qOpPushConstU8, b₀] consts mem = .ok (v, mem) := by
  have hstep : Midfall.Generator.evalQuotientIdentityStep [qOpPushConstU8, b₀] consts 0
      qOpPushConstU8 ([] : List QVMFr) mem =
      .ok { stack := [v], consumed := 2, hConsumed := by omega, mem := mem } :=
    qStepValue_pushConstU8 b₀ [] consts v [] mem hv
  refine evalQuotientIdentity_one [qOpPushConstU8, b₀] consts mem
    { stack := [v], consumed := 2, hConsumed := by omega, mem := mem } v ?_ hstep rfl ?_
  · simp
  · simp

/-- The same at a 'memOfρ' memory: the reference VM's output on a frame-reading instruction IS ρ's
    value there. Reference semantics and valuation, meeting in one theorem - which is precisely the
    half of 'QInterpRefines' that is about the reference rather than about the emitted Yul. -/
theorem qIdentity_pushMemU16_memOfρ (b₀ b₁ : Nat) (consts : List Word256)
    (ρ : Valuation) (S : List (Nat × Nat))
    (h : (0, (b₀ * 256 + b₁) % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    Midfall.Generator.evalQuotientIdentity [qOpPushMemU16, b₀, b₁] consts (memOfρ ρ S) =
      .ok (ρ 0 ((b₀ * 256 + b₁) % 2 ^ 32), memOfρ ρ S) := by
  refine evalQuotientIdentity_one [qOpPushMemU16, b₀, b₁] consts (memOfρ ρ S)
    { stack := [ρ 0 ((b₀ * 256 + b₁) % 2 ^ 32)], consumed := 3, hConsumed := by omega,
      mem := memOfρ ρ S } _ ?_ ?_ rfl ?_
  · simp
  · exact qStepValue_pushMemU16_memOfρ b₀ b₁ [] consts [] ρ S h
  · simp

/-- ADD over a two-instruction segment: the reference VM's output on 'PUSH_CONST_U8 a; PUSH_CONST_U8
    b; ADD'... stated for the two-instruction case that the loop theory actually reaches, to show
    'evalQuotientIdentity_one' is not a one-trick lemma: the segment '[PUSH_MEM_U16 p]' reads the
    frame and returns ρ. -/
theorem qIdentity_pushMemLiteral_memOfρ (b₀ b₁ b₂ b₃ : Nat) (consts : List Word256)
    (ρ : Valuation) (S : List (Nat × Nat))
    (h : (0, (((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) % 2 ^ 32) ∈
          S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    Midfall.Generator.evalQuotientIdentity [qOpPushMemLiteral, b₀, b₁, b₂, b₃] consts
        (memOfρ ρ S) =
      .ok (ρ 0 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) % 2 ^ 32), memOfρ ρ S) := by
  refine evalQuotientIdentity_one [qOpPushMemLiteral, b₀, b₁, b₂, b₃] consts (memOfρ ρ S)
    { stack := [ρ 0 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃) % 2 ^ 32)], consumed := 5,
      hConsumed := by omega, mem := memOfρ ρ S } _ ?_ ?_ rfl ?_
  · simp
  · exact qStepValue_pushMemLiteral_memOfρ b₀ b₁ b₂ b₃ [] consts [] ρ S h
  · simp

/-! ### E2. THE EXAMPLE THE CARD SAID COULD NOT BE PROVED -/

/-- **THE 'rfl' THAT FAILS, PROVED.** QuotientInterp.lean:354 records that
    'evalQuotientIdentity [] [] m = .error (QVMFault.stackLengthMismatch 0)' **FAILS** by 'rfl', and
    draws from it the conclusion that the reference VM's output cannot be named by a theorem at all.
    The conclusion was too strong: the equation is not reachable by 'rfl' - the 'where'-clause 'go'
    does not unfold in the kernel - but it IS reachable by 'qLoop_go_done', because the empty segment
    never enters the loop body. This is the same fact A3b needed for the strictness of
    'QSegment.inWindow' (QuotientInterp.lean:97-101: on an empty segment the reference errors while
    the emitted loop exits normally), and it is now a theorem rather than a prose claim. -/
theorem evalQuotientIdentity_empty (consts : List Word256) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentity ([] : List Nat) consts mem =
      .error (QVMFault.stackLengthMismatch 0) := by
  have hloop : Midfall.Generator.evalQuotientIdentityLoop ([] : List Nat) consts 0
      ([] : List QVMFr) mem = .ok (([] : List QVMFr), mem) :=
    qLoop_go_done ([] : List Nat) consts 0 0 ([] : List QVMFr) mem (by simp)
  unfold Midfall.Generator.evalQuotientIdentity
  rw [hloop]
  rfl

/-! ### F. WHAT IS NOT LANDED, NAMED -/

/-! THE THREE COUNT-PREFIXED ARMS. 'RUN_ADD_MUL_MEM_MEM_CONST_U8',
    'RUN_ADD_MUL_CONST_U8_MEM_U16' and 'AFFINE_SUM' fold a count-prefixed block with
    'foldRangeIdxM', so their value equation quantifies over an iteration whose LENGTH IS READ FROM
    THE OPERAND BYTES; the emitted side is a 'yfor'. Neither side is a missing idea, but each needs a
    loop-induction lemma tying 'foldRangeIdxM' to the Yul 'for' loop, which is ROW.Q.3's 'run' family
    and not this file's deliverable. They are named here so the count of landed arms is honest: 22 of
    the 26 identity arms have a value equation, 3 do not (MODARITH7 is landed above as a
    helper equation, so the count is 23 landed, 3 not). -/

/-! ### F2. THE OPCODE FETCH: HOW FAR IT GETS, AND THE ONE STEP THAT DOES NOT -/

/-! **THE MISSING BRIDGE, NAMED WITH ITS GOAL STATE.** Every arm lemma needs to know that the word the
    interpreter fetches - 'q_op := byte(0, mload(q_pc))', 'GenAst.qvmLoopPre' - IS the reference's
    opcode byte 'bytes.getD cursor 0'. 'AgreesProgram' already pins every byte of the window, and
    'stepOp Op.mload' and 'stepOp Op.byte' are both 'rfl'-computable, so the whole gap is ONE BitVec
    fact about the vendored 'loadWord':

    '''
    ((loadWord mem p) >>> 248) &&& 0xff = BitVec.ofNat 256 (mem p).toNat
    '''

    i.e. the top byte of a big-endian 32-byte fold is the first byte. This card got most of the way:
    'loadWord' is a 'List.foldl' over 'List.range 32', and the closed form

    '''
    (qFoldBytes g n).toNat = ((List.range n).map (fun i => (g i).toNat * 256 ^ (n - 1 - i))).sum
    '''

    is proved for 'n ≤ 32' together with the no-truncation bound 'qFoldBytes_lt', using the
    'Nat.shiftLeft_add_eq_or_of_lt' pattern 'Midfall/Yul/Word.lean' already establishes for the LOW
    byte ('lowByte_or_rest', Word.lean:197). What is NOT finished is the last division step:
    'x >>> 248' becomes '/ 2 ^ 248' under 'Nat.shiftRight_eq_div_pow', the head term is
    'g 0 * 256 ^ 31', and the tail must be shown '< 256 ^ 31' - which needs the same closed form at
    'n = 31' for the SHIFTED function, and the 'List.range (n+1) = 0 :: map (·+1) (range n)'
    reindexing. Cost of the attempt: ~80 min of BitVec plumbing, four intermediate states reached, no
    sorry left behind because none of it is in this file. It is recorded here rather than landed
    because it is a 'Midfall/Yul/Word.lean' fact - a file this card does not own - and because the
    remaining step is arithmetic, not a missing idea. -/

/-! ### G. THE SWITCH DISPATCH (ROW.Q.3's first landed fact, and a correction to QPROBE)

**THE FINDING.** QPROBE's stuck leaf was 'selectSwitch' not reducing, and the reason is not what the
report says. 'selectSwitch' dispatches through
'cases.find? (fun p => decide (cv = D.litValue p.1))', and 'simp only [selectSwitch]' leaves that
'find?' UNREDUCED EVEN WHEN THE LABEL IS A LITERAL AND THE SCRUTINEE IS THE SAME LITERAL: the
'decide' is on 'D.litValue (Literal.number n)', a structure-field projection of the dialect
instance, and 'simp' does not unfold it. Two facts fix it, and both are free:
'qDialect_litValue_number' is 'rfl', and 'decide_eq_true' turns a proved equality into the 'decide'
reduction. With those, the dispatch reduces at a SYMBOLIC template table - no concrete 'tcq', no
fixture (D-P71). So the arm decomposition of ROW.Q.3 is reachable after all; what is NOT reachable is
reducing the emitted arm LIST itself: 'simp only [qvmOpcodeArms]' with all 31 'opUsage' flags pinned
dies with a **deterministic timeout at 'whnf', 200000 heartbeats, ~11 s**, because unfolding the
definition normalises all 31 arm bodies before 'List.lookup' can act. An arm lemma therefore has to
be stated about the arm's block as a parameter and about the dispatch, not about a lookup into the
emitter's list. That is the shape of the four lemmas below. -/

/-- The dialect reads a numeric label as the 256-bit word of that number. 'rfl' - and the missing
    'simp' lemma. -/
theorem qDialect_litValue_number {c : ExternalCalls} {g : ExternalGas} (n : Nat) :
    (Bridge.Dialect c g).litValue (Literal.number n) = (BitVec.ofNat 256 n : U256) := rfl

/-- **THE SWITCH TAKES THE ARM.** One case, matching label: the emitted switch runs that arm's body.
    Generic in the template table and in the body. -/
theorem qSwitch_arm {c : ExternalCalls} {g : ExternalGas} (tcq : QuotientVmTemplateConstants)
    (body dflt : Block EVM.Op) :
    selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.op.neg)
        [(Literal.number tcq.op.neg, body)] (some dflt) = body := by
  have h : (BitVec.ofNat 256 tcq.op.neg : U256) =
      (Bridge.Dialect c g).litValue (Literal.number tcq.op.neg) :=
    (qDialect_litValue_number (c := c) (g := g) tcq.op.neg).symm
  have hd : decide ((BitVec.ofNat 256 tcq.op.neg : U256) =
      (Bridge.Dialect c g).litValue (Literal.number tcq.op.neg)) = true :=
    decide_eq_true h
  simp only [selectSwitch, hd, List.find?_cons]

/-- **THE SWITCH IS FAIL-CLOSED.** If the fetched word equals no label in the arm list, the emitted
    switch runs the default block - which is 'q_program_fail'. This is the prose claim at
    QuotientInterp.lean:102 ("every emitted switch is fail-closed on an unknown opcode") that the
    contract's truth on a garbage segment rests on, and it is generic in the arm list, so it does not
    need the emitter's list to reduce. -/
theorem qSwitch_failClosed {c : ExternalCalls} {g : ExternalGas} (cv : U256)
    (cases : List (Literal × Block EVM.Op)) (dflt : Block EVM.Op)
    (h : ∀ p ∈ cases, cv ≠ (Bridge.Dialect c g).litValue p.1) :
    selectSwitch (Bridge.Dialect c g) cv cases (some dflt) = dflt := by
  unfold selectSwitch
  have hnone : cases.find? (fun p => decide (cv = (Bridge.Dialect c g).litValue p.1)) = none :=
    List.find?_eq_none.mpr (fun p hp => by
      intro hd
      exact h p hp (of_decide_eq_true hd))
  rw [hnone]
  rfl

/-- The loop's body, as the emitter builds it: the two fetch statements and then the switch over the
    three arm lists with the fail-closed default. 'rfl' - but it is the equation every arm lemma has
    to be stated under, and nothing in the tree spelled it. -/
theorem qvmLoop_body (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) :
    GenAst.qvmLoop ctx program tcq =
      Stmt.forLoop [] (yop EVM.Op.lt [yvar "q_pc", yvar "q_end"]) []
        (GenAst.qvmLoopPre ++
          [Stmt.switch (yvar "q_op")
            (GenAst.qvmOpcodeArms ctx program tcq ++ GenAst.qvmNativeArms ctx program tcq
              ++ GenAst.qvmFoldArms ctx program tcq)
            (some [yexpr (ycall "q_program_fail" [])])]) := rfl


/-! ### H. THE EMITTED-SIDE VALUE REFINEMENT (QVAL - ROW.Q.3's value half, first instances)

**WHAT THIS SECTION IS, AND WHY IT WAS NOT LANDED BEFORE.** QEMIT4 landed the 31-body lift and all
eight 'QArmFamily' theorems and drew the line explicitly: those are gadget IDENTIFICATION - the
emitter's own arm list carries the named body at that arm's label - and "the VALUE half (arm effect
refines the reference step) is NOT landed and was not manufactured". Section B is the reference side:
'qStepValue_X' says what 'evalQuotientIdentityStep' PUSHES at arm X. Nothing in the tree said what
'qArmBodyX' does. THIS SECTION SAYS IT, for the arms whose effect is register-only, and it is a
theorem and not a comment.

**IS THE TIE ALREADY IMPLIED BY IDENTIFICATION PLUS A VALUE EQUATION? NO - AND HERE IS THE EXACT
HOLE.** 'qArmFamily_arith' gives '(Literal.number tcq.op.neg, qArmBodyNeg ctx program tcq) ∈
qvmOpcodeArms ctx program tcq'; 'qStepValue_neg' gives 'evalQuotientIdentityStep (qOpNeg :: rest)
consts 0 qOpNeg (v :: stack) mem = .ok { stack := qvmFrNeg v :: stack, ... }'. Neither mentions the
other: the first is a LIST MEMBERSHIP about a Yul block, the second an EQUATION about the reference
interpreter, and there is no function anywhere in the tree from a 'Block EVM.Op' to its register
transfer. So the tie is a third fact, and it needs the vendored big-step semantics applied to the
emitted block. That is what 'qArmRun_neg' below is: a derivation in 'Step' - the same judgment the
contract's 'StmtsContract' is written over - that EXECUTES the emitter's own arm body and names the
word it leaves in 'q_top'.

**THE SHAPE, AND WHY THE HYPOTHESES LOOK LIKE SECTION B'S.** The pre pins the registers the arm reads,
by 'VEnv.get' equations, exactly as 'AtSegment'/'qinterpTop' pin them in the contract and exactly as
section B pins readers by 'constAt consts slot 0 = .ok v' equations. The 'x.toNat < qvmFrModulus'
bound is the canonicity of the reference field element in the register - the same fact
'qvmToFr_injOn' (Qvm.lean:169) needs and for the same reason. No row, 'ValidV3', bundle or the root
gains a hypothesis (RULES); nothing names a fixture (D-P71); there is no 'native_decide' and no sorry.

**THE ARITHMETIC BRIDGE IS NOT NEW WORK.** 'wAddmod', 'wSubFr', 'frModulusWord' and
'stepOp_addmod_atFr' are T3.8's (Midfall/Yul/WpX.lean), and 'wSubFr' is exactly the 'sub(r, q_top)'
the NEG arm emits. What was missing was the 'wSubFr'/'wAddmod' -> 'qvmFrNeg' step, which is
'wAddmod_neg' below; it needs the canonicity bound, and 'subFr_needsCanonicity' (WpX) is the gate that
says that bound cannot be dropped.

**WHAT IS STILL OPEN, NAMED.** (a) The 'StmtsContractAll' (every-run) form of these two arms: the
existential is what 'qArmValue_*' gives, and the forall form additionally needs the arm's operand
expressions shown not to halt - a case tree over 'Step' for each arm's expression, mechanical but not
short, or 'StmtsContractAll.of_det' at 'Bridge.dialect_deterministic', which asks for
'c.Functional' and 'g.Functional' and so is NOT free at an arbitrary call relation. (b) The 20 arms
that read memory: their pre must also pin 'loadWord st.memory p' against the reference reader, and
the operand DECODE ('shr 240 (mload q_pc)' = 'b₀ * 256 + b₁') is the 'loadWord_topByte' /
'loadWord_top2' bridge now landed in 'Midfall/Yul/Word.lean' section 8. (c) The three count-prefixed
arms of section F: their value half is a loop induction over 'foldRangeIdxM' against a 'yfor', and it
is NOT landed - see section F. -/

open Midfall.Yul.WpX

/-- The modulus literal is canonical at 256 bits, so the wrap EVM performs loses nothing. -/
theorem qvmFrModulus_lt256 : qvmFrModulus < 2 ^ 256 :=
  frModulusWord_toNat ▸ (BitVec.isLt frModulusWord)

/-- **THE NEG ARM'S OPERAND EXPRESSIONS, AT THE OPEN DIALECT.** 'sub(r, q_top)' and
    'addmod(0, sub(r, q_top), r)' are 'stepOp' arms whose result is T3.8's 'wSubFr' / 'wAddmod'.
    Both are 'rfl': the Bridge dialect's 'Builtin' IS the 'stepOp' graph. -/
theorem dialect_builtin_sub_neg {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (x : U256) :
    (Bridge.Dialect c g).Builtin Op.sub [frModulusWord, x] st (.ok [wSubFr x] st) := rfl

/-- The 'addmod' half of the NEG arm's operand expression. -/
theorem dialect_builtin_addmod_neg {c : ExternalCalls} {g : ExternalGas}
    (st : EvmState) (x : U256) :
    (Bridge.Dialect c g).Builtin Op.addmod [BitVec.ofNat 256 0, wSubFr x, frModulusWord] st
      (.ok [wAddmod 0 (wSubFr x)] st) := rfl

/-- 'EVM sub(r, x)' at a canonical 'x' is the natural subtraction 'r - x'. -/
theorem wSubFr_toNat_neg (x : U256) (hx : x.toNat ≤ qvmFrModulus) :
    (wSubFr x).toNat = qvmFrModulus - x.toNat := by
  show (frModulusWord - x).toNat = _
  rw [BitVec.toNat_sub, frModulusWord_toNat]
  have h1 : (2 : Nat) ^ 256 - x.toNat + qvmFrModulus = (qvmFrModulus - x.toNat) + 2 ^ 256 := by
    have : x.toNat ≤ 2 ^ 256 := Nat.le_trans hx (Nat.le_of_lt qvmFrModulus_lt256)
    omega
  have hlt : qvmFrModulus - x.toNat < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) qvmFrModulus_lt256
  rw [h1, Nat.add_comm, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]

/-- **THE ARITHMETIC TIE FOR NEG.** The word the arm computes IS the field negation
    'qvmFrNeg v' that 'qStepValue_neg' pushes, for a canonical 'v'. -/
theorem wAddmod_eq_qvmFrNeg (x : U256) (hx : x.toNat < qvmFrModulus) :
    wAddmod 0 (wSubFr x) = BitVec.ofNat 256 (qvmFrNeg x.toNat) := by
  have h2 : ((0 : U256).toNat + (wSubFr x).toNat) % qvmFrModulus = qvmFrNeg x.toNat := by
    rw [wSubFr_toNat_neg x (Nat.le_of_lt hx), show ((0 : U256).toNat) = 0 from rfl, Nat.zero_add]
    unfold Midfall.Generator.qvmFrNeg
    rfl
  rw [wAddmod, h2]

/-- **THE NEG ARM RUNS, AND LANDS ON THE REFERENCE'S VALUE.** Executing the emitter's own lifted
    body 'GenAst.qArmBodyNeg' in the vendored big-step semantics, from any register state whose
    'q_top'/'r' are as pinned, terminates normally with 'q_top' updated to 'wAddmod 0 (wSubFr x)' -
    the word 'wAddmod_eq_qvmFrNeg' identifies with 'qvmFrNeg x.toNat'. Every step is a 'Step'
    constructor of the vendored judgment: no slice is unrolled by 'wp', no fuel is chosen, and the
    register reads are the same 'VEnv.get' equations the contract's own predicates supply. -/
theorem qArmRun_neg {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (x : U256)
    (hget_top : VEnv.get V "q_top" = some x) (hget_r : VEnv.get V "r" = some frModulusWord) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyNeg ctx program tcq)
      (VEnv.set V "q_top" (wAddmod 0 (wSubFr x))) st .normal := by
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set V "q_top" (wAddmod 0 (wSubFr x))) (st1 := st) ?_ Step.seqNil
  refine Step.assignVal (D := Bridge.Dialect c g)
    (vals := [wAddmod 0 (wSubFr x)]) ?_ (by rfl)
  exact Step.builtinOk
    (Step.argsCons (D := Bridge.Dialect c g)
      (rest := [yop Op.sub [yvar "r", yvar "q_top"], yvar "r"])
      (restvals := [wSubFr x, frModulusWord]) (st1 := st) (v := BitVec.ofNat 256 0) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := st) (v := wSubFr x) (st2 := st)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
          (v := frModulusWord) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget_r))
        (Step.builtinOk (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_top"]) (restvals := [x])
            (st1 := st) (v := frModulusWord) (st2 := st)
            (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
              (v := x) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
              (Step.var (D := Bridge.Dialect c g) hget_top))
            (Step.var (D := Bridge.Dialect c g) hget_r)) (dialect_builtin_sub_neg st x)))
      Step.lit) (dialect_builtin_addmod_neg st x)

/-- **ARM NEG: THE VALUE REFINEMENT, PROVED.** 'qArmBodyNeg' refines 'qStepValue_neg': the arm's
    effect on the QVM registers is to replace 'q_top' by 'qvmFrNeg v' for the canonical 'v' the
    register held, leave the machine state alone, and terminate normally - which is exactly the
    'stack := qvmFrNeg v :: stack, consumed := 1, mem := mem' that section B's 'qStepValue_neg'
    names, read through the register encoding 'qinterpTop' uses. Stated as 'StmtsContract', the
    existential contract the vendored 'wp' soundness theorem produces: it EXHIBITS the run. -/
theorem qArmValue_neg {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (x : U256) (hx : x.toNat < qvmFrModulus) :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyNeg ctx program tcq)
      (fun V st => VEnv.get V "q_top" = some x ∧ VEnv.get V "r" = some frModulusWord)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        V' = VEnv.set V "q_top" (BitVec.ofNat 256 (qvmFrNeg x.toNat))) := by
  intro V st hpre
  have hrun := qArmRun_neg ctx program tcq funs V st x hpre.1 hpre.2
  rw [wAddmod_eq_qvmFrNeg x hx] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

/-- **ARM NEG: THE EVERY-RUN FORM.** 'StmtsContractAll' is what 'QInterpRefines' is written over, and
    the existential of 'qArmValue_neg' becomes it by determinism: at a FUNCTIONAL call relation and a
    FUNCTIONAL gas oracle every built-in of the open dialect is single-valued
    ('Bridge.dialect_deterministic'), so the one run 'qArmValue_neg' exhibits is the only run. The
    two functionality hypotheses are about the oracles and not about a row, a bundle or 'ValidV3'
    (RULES); they are what the tree's own 'StmtsContractAll.of_det' (Midfall/Yul/Contracts.lean:268)
    asks for, and 'Midfall/LoweringV2' discharges them at 'permissive (callsOf product)'. -/
theorem qArmValueAll_neg {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (x : U256) (hx : x.toNat < qvmFrModulus) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyNeg ctx program tcq)
      (fun V st => VEnv.get V "q_top" = some x ∧ VEnv.get V "r" = some frModulusWord)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        V' = VEnv.set V "q_top" (BitVec.ofNat 256 (qvmFrNeg x.toNat))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg) (qArmValue_neg ctx program tcq funs x hx)

/-! ### I. THE POW5 ARM (QARMS - the second arm value refinement; register-only)

QVAL's section H landed NEG and named POW5 as the closest remaining arm, abandoning at a cap on three
mechanical obstacles. All three are cleared here, one at a time:

  * (a) 'VEnv.set' / 'VEnv.get' at a SYMBOLIC environment do not reduce, so the two cons/set facts
    'venvGet_cons_ne' and 'venvSet_cons_ne' are landed as theorems instead of being asked of 'rfl';
  * (b) the 'letVal' environment is a CONS, and annotating it at the open dialect is where the
    'Dialect.Value' projection unification fails. It is not fought: the cons is written at the
    ABSTRACTION the projection lives under ('VEnv D' with 'D' a variable, 'w : D.Value'), where no
    unification with 'U256' is ever asked, and the single instance the arm needs ('("q2", x) :: V') is
    discharged by 'rfl' at the literal name;
  * (c) the 'argsCons' nesting swap: 'mulmod' takes its arguments right-to-left but collects them in
    SOURCE order ('BigStep.lean:209-212'), so the inner 'mulmod(q2, q2, r)' sits in the MIDDLE of the
    outer argument list and its derivation is the second hypothesis of the outer 'argsCons', not the
    first.

**NO CANONICITY HYPOTHESIS, AND THAT IS A REAL DIFFERENCE FROM NEG.** 'qvmFrMul' reduces by
'qvmFrModulus' before the 256-bit wrap, so 'wMulmod a b' is the field product for EVERY 'a', 'b' -
the same reason 'mulmod_toFr' (WpX.lean:533) carries no hypothesis while 'qvmToFr_neg' does. So
'qArmValue_pow5' is stated for an arbitrary register word, with no 'x.toNat < qvmFrModulus'.

**THE ONE STRUCTURAL DIFFERENCE FROM NEG.** The arm introduces a local ('let q2 := ...'), so the
final environment is not 'VEnv.set V "q_top" w' but the cons of that local onto the updated
environment. The postcondition says exactly that; nothing is hidden by weakening, and the every-run
form is still 'of_det' at the two ORACLE functionality facts. -/

/-! **FOUR NOTES FOR THE NEXT CARD, WRITTEN DOWN SO THEY ARE NOT RE-LEARNED (QARMS).**

1. **DO NOT ATTEMPT A DEFINITIONAL TIE ON AN ARITHMETIC ARM.** The emitted POW5 computes
   'v * (v^2)^2 mod r'; the reference 'qStepValue_pow5' pushes '((v * v^2) mod r * v^2) mod r'. Those
   are DIFFERENT BRACKETINGS and agree only through 'qvmFrMul_pow5_nest', a real arithmetic lemma -
   never 'rfl'. Assume the same for every arm whose emitted expression re-associates or re-nests the
   reference's. THE EXCEPTION, AND IT IS INFORMATION: where emitted and reference apply the SAME named
   word operation in the SAME order the tie IS 'rfl' - see 'wAddmod_eq_qvmFrAdd' / 'wMulmod_eq_qvmFrMul'
   below. So try 'rfl' once; if it fails go straight to the arithmetic lemma and do not fight it.
2. **PER-ARM PRECONDITIONS, NOT A UNIFORM ONE.** POW5 needs NO canonicity hypothesis ('qvmFrMul' reduces
   by 'qvmFrModulus' before the wrap and 'qvmFrModulus < 2^256', the same reason 'mulmod_toFr'
   (WpX.lean:533) is hypothesis-free) while NEG NEEDS 'x.toNat < qvmFrModulus' ('subFr_needsCanonicity').
   A single uniform side-condition for ROW.Q.3's value half would be either wrong or needlessly strong,
   and adding one to a row is out of bounds (RULES). Land per-arm preconditions and let the composition
   take them individually.
3. **THE CONS-ENVIRONMENT PATTERN - QVAL'S ABANDONED OBSTACLE (b), CLEARED.** An arm that introduces a
   'let' ends in a CONS environment, and annotating that cons at the open dialect is where the
   'Dialect.Value' projection unification fails. The way through is NOT to annotate: state the
   environment facts as theorems over an ABSTRACT dialect ('VEnv D', 'w : D.Value'), where no
   unification with 'U256' is ever asked - 'venvGet_cons_ne', 'venvSet_cons_ne', 'venvGet_set_same',
   'venvGet_set_ne' below - and let the every-run contract ALLOW the extra binding in its post. The cons
   itself at a literal name ('("q2", x) :: V') reduces by 'rfl' because 'DecidableEq String' decides two
   literals.
4. **TACTIC NOISE THAT COSTS A BOX OTHERWISE (the Lean version on this tree).** 'if_pos'/'if_neg' are
   DEPRECATED - use 'ite_eq_left'/'ite_eq_right'. 'List.find?' unfolds to 'match decide (y = x)', so
   rewrite with 'decide_eq_false h' / 'decide_eq_true', not 'if_neg'. 'Nat.mul_mod' must be given its
   arguments EXPLICITLY ('Nat.mul_mod a (b % m) m') because 'rw' otherwise picks the RHS match first and
   leaves 'a % m % m * (b % m % m) % m'. 'BitVec.toNat_inj' is the WRONG direction here; use
   'BitVec.eq_of_toNat_eq'. And 'Step.assignVal' needs '(vars := [...])' plus '(by rfl)' (not bare 'rfl')
   when the statement is ascribed rather than refined. -/

/-- 'VEnv.get' through a cons whose name is DIFFERENT from the one looked up: the local a 'let'
    introduces does not shadow a register the next statement reads. This is obstacle (a): at a
    symbolic tail the projection does not reduce, so it is a theorem. -/
theorem venvGet_cons_ne {D : YulSemantics.Dialect} (V : VEnv D) (y x : Ident) (w : D.Value)
    (hxy : y ≠ x) : VEnv.get ((y, w) :: V) x = VEnv.get V x := by
  have h : ((y, w) :: V).find? (fun p : Ident × D.Value => p.1 = x) =
      V.find? (fun p : Ident × D.Value => p.1 = x) := by
    simp only [List.find?, decide_eq_false hxy]
  exact congrArg (fun o : Option (Ident × D.Value) => o.map (·.2)) h

/-- 'VEnv.set' through such a cons: the update passes the local by and lands in the outer
    environment, so the arm's final environment splits into the cons and the register write. -/
theorem venvSet_cons_ne {D : YulSemantics.Dialect} (V : VEnv D) (y x : Ident) (w v : D.Value)
    (hxy : y ≠ x) : VEnv.set ((y, w) :: V) x v = (y, w) :: VEnv.set V x v := by
  simp only [VEnv.set]
  rw [ite_eq_right hxy]

/-- EVM 'mulmod(a, b, r)' at the scalar modulus, read as a natural: the field product 'qvmFrMul'.
    No canonicity hypothesis - the reduction by 'qvmFrModulus < 2^256' makes the wrap lossless. -/
theorem wMulmod_toNat (a b : U256) :
    (wMulmod a b).toNat = qvmFrMul a.toNat b.toNat := by
  have hlt : (a.toNat * b.toNat) % qvmFrModulus < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < qvmFrModulus))
      (Nat.le_of_lt qvmFrModulus_lt256)
  show (BitVec.ofNat 256 ((a.toNat * b.toNat) % qvmFrModulus)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rfl

/-- Replacing a factor by its residue changes nothing. -/
theorem mul_mod_residue_left (m a b : Nat) : (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_mod a (b % m) m, Nat.mod_mod b m, Nat.mul_mod a b m]

/-- The twin, on the left factor. -/
theorem mul_mod_residue_right (m a b : Nat) : ((a % m) * b) % m = (a * b) % m := by
  rw [Nat.mul_mod (a % m) b m, Nat.mod_mod a m, Nat.mul_mod a b m]

/-- **THE NESTING TIE.** The arm computes 'v * ((v*v)² mod r) mod r'; the reference computes
    '((v * (v*v mod r)) mod r) * (v*v mod r) mod r'. Both are 'v^5 mod r', and neither needs the
    operand to be canonical. -/
theorem qvmFrMul_pow5_nest (v : QVMFr) :
    qvmFrMul v (qvmFrMul (qvmFrMul v v) (qvmFrMul v v)) =
      qvmFrMul (qvmFrMul v (qvmFrMul v v)) (qvmFrMul v v) := by
  unfold qvmFrMul
  rw [mul_mod_residue_left, ← Nat.mul_assoc, mul_mod_residue_right]

/-- **THE ARITHMETIC TIE FOR POW5**, the twin of 'wAddmod_eq_qvmFrNeg': the word the arm computes IS
    the value 'qStepValue_pow5' pushes. -/
theorem wMulmod_eq_qvmFrPow5 (x : U256) :
    wMulmod x (wMulmod (wMulmod x x) (wMulmod x x)) =
      BitVec.ofNat 256 (qvmFrMul (qvmFrMul x.toNat (qvmFrMul x.toNat x.toNat))
        (qvmFrMul x.toNat x.toNat)) := by
  have hlt : qvmFrMul (qvmFrMul x.toNat (qvmFrMul x.toNat x.toNat)) (qvmFrMul x.toNat x.toNat)
      < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < qvmFrModulus))
      (Nat.le_of_lt qvmFrModulus_lt256)
  refine BitVec.eq_of_toNat_eq ?_
  rw [wMulmod_toNat, wMulmod_toNat, wMulmod_toNat, qvmFrMul_pow5_nest, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

/-- 'mulmod' at the scalar modulus, at the OPEN dialect: the Bridge dialect's 'Builtin' IS the
    'stepOp' graph, so this is 'rfl' - the general form of 'dialect_builtin_addmod_neg'. -/
theorem dialect_builtin_mulmod_atFr {c : ExternalCalls} {g : ExternalGas}
    (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.mulmod [a, b, frModulusWord] st (.ok [wMulmod a b] st) := rfl

/-- **THE POW5 ARM RUNS, AND LANDS ON THE REFERENCE'S VALUE.** The twin of 'qArmRun_neg' for the
    emitter's own 'GenAst.qArmBodyPow5': two 'mulmod' steps and a 'let', every one of them a 'Step'
    constructor of the vendored judgment, no 'wp' slice and no fuel. -/
theorem qArmRun_pow5 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (x : U256)
    (hget_top : VEnv.get V "q_top" = some x) (hget_r : VEnv.get V "r" = some frModulusWord) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPow5 ctx program tcq)
      (("q2", wMulmod x x) ::
        VEnv.set V "q_top" (wMulmod x (wMulmod (wMulmod x x) (wMulmod x x)))) st .normal := by
  -- obstacle (a): the reads of the SECOND statement go through the cons the 'let' introduced.
  have hne : ("q2" : Ident) ≠ "q_top" := by decide
  have hget2_top : VEnv.get (("q2", wMulmod x x) :: V) "q_top" = some x := by
    rw [venvGet_cons_ne V "q2" "q_top" (wMulmod x x) hne]; exact hget_top
  have hget2_r : VEnv.get (("q2", wMulmod x x) :: V) "r" = some frModulusWord := by
    rw [venvGet_cons_ne V "q2" "r" (wMulmod x x) (by decide : ("q2" : Ident) ≠ "r")]
    exact hget_r
  have hget2_q2 : VEnv.get (("q2", wMulmod x x) :: V) "q2" = some (wMulmod x x) := rfl
  -- statement 1: q2 := mulmod(q_top, q_top, r)
  have hargs1 : Step (D := Bridge.Dialect c g) funs V st
      (.args [yvar "q_top", yvar "q_top", yvar "r"])
      (.eres (.vals [x, x, frModulusWord] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_top", yvar "r"])
      (restvals := [x, frModulusWord]) (st1 := st) (v := x) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := st) (v := x) (st2 := st)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
          (v := frModulusWord) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget_r))
        (Step.var (D := Bridge.Dialect c g) hget_top))
      (Step.var (D := Bridge.Dialect c g) hget_top)
  have hexpr1 : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.mulmod [yvar "q_top", yvar "q_top", yvar "r"]))
      (.eres (.vals [wMulmod x x] st)) :=
    Step.builtinOk hargs1 (dialect_builtin_mulmod_atFr st x x)
  have hstmt1 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (ylet "q2" (yop Op.mulmod [yvar "q_top", yvar "q_top", yvar "r"])))
      (.sres (("q2", wMulmod x x) :: V) st .normal) :=
    Step.letVal hexpr1 rfl
  -- statement 2: q_top := mulmod(q_top, mulmod(q2, q2, r), r). Obstacle (c): the inner 'mulmod' is
  -- the SECOND hypothesis of the outer 'argsCons' - right-to-left evaluation, source-order results.
  have hargs2i : Step (D := Bridge.Dialect c g) funs (("q2", wMulmod x x) :: V) st
      (.args [yvar "q2", yvar "q2", yvar "r"])
      (.eres (.vals [wMulmod x x, wMulmod x x, frModulusWord] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q2", yvar "r"])
      (restvals := [wMulmod x x, frModulusWord]) (st1 := st) (v := wMulmod x x) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := st) (v := wMulmod x x) (st2 := st)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
          (v := frModulusWord) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget2_r))
        (Step.var (D := Bridge.Dialect c g) hget2_q2))
      (Step.var (D := Bridge.Dialect c g) hget2_q2)
  have hexpr2i : Step (D := Bridge.Dialect c g) funs (("q2", wMulmod x x) :: V) st
      (.expr (yop Op.mulmod [yvar "q2", yvar "q2", yvar "r"]))
      (.eres (.vals [wMulmod (wMulmod x x) (wMulmod x x)] st)) :=
    Step.builtinOk hargs2i (dialect_builtin_mulmod_atFr st (wMulmod x x) (wMulmod x x))
  have hargs2 : Step (D := Bridge.Dialect c g) funs (("q2", wMulmod x x) :: V) st
      (.args [yvar "q_top", yop Op.mulmod [yvar "q2", yvar "q2", yvar "r"], yvar "r"])
      (.eres (.vals [x, wMulmod (wMulmod x x) (wMulmod x x), frModulusWord] st)) :=
    Step.argsCons (D := Bridge.Dialect c g)
      (rest := [yop Op.mulmod [yvar "q2", yvar "q2", yvar "r"], yvar "r"])
      (restvals := [wMulmod (wMulmod x x) (wMulmod x x), frModulusWord]) (st1 := st) (v := x)
      (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := st) (v := wMulmod (wMulmod x x) (wMulmod x x)) (st2 := st)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
          (v := frModulusWord) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget2_r))
        hexpr2i)
      (Step.var (D := Bridge.Dialect c g) hget2_top)
  have hexpr2 : Step (D := Bridge.Dialect c g) funs (("q2", wMulmod x x) :: V) st
      (.expr (yop Op.mulmod [yvar "q_top", yop Op.mulmod [yvar "q2", yvar "q2", yvar "r"],
        yvar "r"]))
      (.eres (.vals [wMulmod x (wMulmod (wMulmod x x) (wMulmod x x))] st)) :=
    Step.builtinOk hargs2
      (dialect_builtin_mulmod_atFr st x (wMulmod (wMulmod x x) (wMulmod x x)))
  have hstmt2 : Step (D := Bridge.Dialect c g) funs (("q2", wMulmod x x) :: V) st
      (.stmt (yset "q_top"
        (yop Op.mulmod [yvar "q_top", yop Op.mulmod [yvar "q2", yvar "q2", yvar "r"], yvar "r"])))
      (.sres (("q2", wMulmod x x) ::
        VEnv.set V "q_top" (wMulmod x (wMulmod (wMulmod x x) (wMulmod x x)))) st .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"])
      (vals := [wMulmod x (wMulmod (wMulmod x x) (wMulmod x x))]) hexpr2 (by rfl)
  unfold GenAst.qArmBodyPow5
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q2", wMulmod x x) :: V)) (st1 := st)
    hstmt1 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q2", wMulmod x x) ::
    VEnv.set V "q_top" (wMulmod x (wMulmod (wMulmod x x) (wMulmod x x))))) (st1 := st)
    hstmt2 (Step.seqNil (D := Bridge.Dialect c g))

/-- **ARM POW5: THE VALUE REFINEMENT, PROVED.** 'qArmBodyPow5' refines 'qStepValue_pow5': the arm
    replaces 'q_top' by 'qvmFrMul (qvmFrMul v (qvmFrMul v v)) (qvmFrMul v v)' for the 'v' the register
    held - the reference's 'v*(v^2)^2' shape, not 'v^4*v' - leaves the machine state alone, and
    terminates normally. Stated as 'StmtsContract', so it EXHIBITS the run. -/
theorem qArmValue_pow5 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (x : U256) :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPow5 ctx program tcq)
      (fun V st => VEnv.get V "q_top" = some x ∧ VEnv.get V "r" = some frModulusWord)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        V' = (("q2", wMulmod x x) :: VEnv.set V "q_top"
          (BitVec.ofNat 256 (qvmFrMul (qvmFrMul x.toNat (qvmFrMul x.toNat x.toNat))
            (qvmFrMul x.toNat x.toNat))))) := by
  intro V st hpre
  have hrun := qArmRun_pow5 ctx program tcq funs V st x hpre.1 hpre.2
  rw [wMulmod_eq_qvmFrPow5 x] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

/-- **ARM POW5: THE EVERY-RUN FORM.** As for NEG: 'of_det' at 'Bridge.dialect_deterministic', whose
    only extra hypotheses are the two ORACLE functionality facts - not row facts. -/
theorem qArmValueAll_pow5 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (x : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPow5 ctx program tcq)
      (fun V st => VEnv.get V "q_top" = some x ∧ VEnv.get V "r" = some frModulusWord)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        V' = (("q2", wMulmod x x) :: VEnv.set V "q_top"
          (BitVec.ofNat 256 (qvmFrMul (qvmFrMul x.toNat (qvmFrMul x.toNat x.toNat))
            (qvmFrMul x.toNat x.toNat))))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pow5 ctx program tcq funs x)

/-! ### J. THE ADD AND MUL ARMS (QARMS - the first MEMORY-READING arm value refinements)

These are the first arms whose emitted side reads memory, so they establish the shape the other 19
memory-reading arms will need. Three new facts appear and none of them is a row fact:

  * the guard 'if q_sp == program.stackMptr then fail' is discharged by 'Step.ifFalse' at
    'b2w (decide (sp = stackMptr)) = D.zero' - a WORD fact about the emitted test, pinned by the
    precondition 'sp ≠ stackMptr', which is exactly the register the contract's own 'AtSegment' pins;
  * 'mload' CHANGES THE STATE: 'stepOp .mload' returns 'touchMemory st p 32' (EVMExec.lean:749-751),
    so unlike NEG and POW5 the post-state is not the pre-state. The postcondition says which state it
    is, and the reader equation 'loadWord st.memory (sp - 32).toNat = y' is what ties the emitted read
    to the reference's popped operand - the same shape section B uses ('constAt consts slot 0 = .ok v'),
    a reader equation and not a new axiom;
  * the reads after the 'q_sp' write go through 'VEnv.set' at a symbolic environment - obstacle (a),
    discharged by 'venvGet_set_same' / 'venvGet_set_ne'.

**THE TIE HERE IS 'rfl', AND THAT IS THE INFORMATION NOTE 1 ASKED FOR.** 'add' emits
'addmod(mload(q_sp), q_top, r)' and the reference pushes 'qvmFrAdd next top' - the SAME named word
operation in the SAME operand order (the reference's head is its top, so the first pop is the RIGHT
operand: 'qStepValue_add' states 'next' before 'top' for exactly this reason). So
'wAddmod_eq_qvmFrAdd' is definitional and no arithmetic lemma is needed. POW5 was the hard case because
it RE-NESTED. -/

/-- 'VEnv.get' at a 'VEnv.set' of a DIFFERENT name: the write does not disturb the register read.
    Needs the name present, which the register pinning supplies; at a symbolic environment neither half
    reduces. -/
theorem venvGet_cons_eq {D : YulSemantics.Dialect} (V : VEnv D) (x : Ident) (w : D.Value) :
    VEnv.get ((x, w) :: V) x = some w := by
  simp [VEnv.get, List.find?]

theorem venvGet_set_ne {D : YulSemantics.Dialect} (V : VEnv D) (y x : Ident) (v w : D.Value)
    (hxy : y ≠ x) (hw : VEnv.get V x = some w) : VEnv.get (VEnv.set V y v) x = some w := by
  induction V with
  | nil => exact absurd hw (by simp [VEnv.get])
  | cons p rest ih =>
    cases p with | mk z u =>
    by_cases hzx : z = x
    · -- the head IS the register read; because y ≠ x the write passed it by, so the value is unchanged
      have hnezy : ¬ (z = y) := fun h => hxy (h.symm.trans hzx)
      have h1 : VEnv.set ((z, u) :: rest) y v = (z, u) :: VEnv.set rest y v := by
        simp [VEnv.set, hnezy]
      have hget : VEnv.get ((z, u) :: VEnv.set rest y v) x = some u := by
        rw [← hzx]
        exact venvGet_cons_eq (VEnv.set rest y v) z u
      have hw' : VEnv.get ((z, u) :: rest) x = some u := by
        rw [← hzx]
        exact venvGet_cons_eq rest z u
      rw [h1, hget]
      rw [hw'] at hw
      exact hw
    · by_cases hzy : z = y
      · have h1 : VEnv.set ((z, u) :: rest) y v = (y, v) :: rest := by simp [VEnv.set, hzy]
        have hget : VEnv.get rest x = some w := by
          rw [← venvGet_cons_ne rest z x u hzx]
          exact hw
        rw [h1, venvGet_cons_ne rest y x v hxy]
        exact hget
      · have h1 : VEnv.set ((z, u) :: rest) y v = (z, u) :: VEnv.set rest y v := by
          simp [VEnv.set, hzy]
        have hget : VEnv.get rest x = some w := by
          rw [← venvGet_cons_ne rest z x u hzx]
          exact hw
        rw [h1, venvGet_cons_ne (VEnv.set rest y v) z x u hzx]
        exact ih hget

/-- 'VEnv.get' at a 'VEnv.set' of the SAME name: the register write is visible to the next statement.
    QVAL's obstacle (a) in its exact form - 'VEnv.set' at a symbolic environment does not reduce. -/
theorem venvGet_set_same {D : YulSemantics.Dialect} (V : VEnv D) (x : Ident) (v w : D.Value)
    (hw : VEnv.get V x = some w) : VEnv.get (VEnv.set V x v) x = some v := by
  induction V with
  | nil => exact absurd hw (by simp [VEnv.get])
  | cons p rest ih =>
    cases p with | mk y u =>
    by_cases hxy : y = x
    · have hset : VEnv.set ((y, u) :: rest) x v = (x, v) :: rest := by simp [VEnv.set, hxy]
      rw [hset]
      simp [VEnv.get, List.find?]
    · have hgetp : VEnv.get ((y, u) :: rest) x = VEnv.get rest x := venvGet_cons_ne rest y x u hxy
      rw [hgetp] at hw
      have hset : VEnv.set ((y, u) :: rest) x v = (y, u) :: VEnv.set rest x v := by
        simp [VEnv.set, hxy]
      rw [hset, venvGet_cons_ne (VEnv.set rest x v) y x u hxy]
      exact ih hw

/-- **THE 'rfl' TIES (note 1's exception).** EVM 'addmod'/'mulmod' at the scalar modulus ARE the named
    field operations, in the same operand order, so no arithmetic lemma is needed. -/
theorem wAddmod_eq_qvmFrAdd (a b : U256) :
    wAddmod a b = BitVec.ofNat 256 (qvmFrAdd a.toNat b.toNat) := rfl

/-- The 'mulmod' twin of 'wAddmod_eq_qvmFrAdd'. -/
theorem wMulmod_eq_qvmFrMul (a b : U256) :
    wMulmod a b = BitVec.ofNat 256 (qvmFrMul a.toNat b.toNat) := rfl

/-- 'mload' at the open dialect: the value is the memory fold and the STATE MOVES - 'touchMemory'. -/
theorem dialect_builtin_mload {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (p : U256) :
    (Bridge.Dialect c g).Builtin Op.mload [p] st
      (.ok [loadWord st.memory p.toNat] (touchMemory st p.toNat 32)) := rfl

/-- EVM 'sub' at the open dialect - the guard-free binary case. -/
theorem dialect_builtin_sub {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.sub [a, b] st (.ok [a - b] st) := rfl

/-- EVM 'eq' at the open dialect: the word 'b2w (decide (a = b))', state unchanged. -/
theorem dialect_builtin_eq {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.eq [a, b] st (.ok [b2w (decide (a = b))] st) := rfl

/-- The general 'addmod' at the scalar modulus ('dialect_builtin_addmod_neg' is this at 'a = 0'). -/
theorem dialect_builtin_addmod_atFr {c : ExternalCalls} {g : ExternalGas}
    (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.addmod [a, b, frModulusWord] st (.ok [wAddmod a b] st) := rfl

/-- **ARM ADD RUNS.** The guard is FALSE (the stack is not empty), 'q_sp' moves down one slot, and the
    word left in 'q_top' is 'wAddmod y x' for 'y' the word the memory holds at the new 'q_sp' - which
    'wAddmod_eq_qvmFrAdd' identifies with the 'qvmFrAdd next top' that 'qStepValue_add' pushes. The
    state is the one 'mload' touched. -/
theorem qArmRun_add {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (sp x y : U256)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hsp : sp ≠ BitVec.ofNat 256 program.stackMptr)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hload : loadWord st.memory (sp - BitVec.ofNat 256 32).toNat = y) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAdd ctx program tcq)
      (VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" (wAddmod y x))
      (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) .normal := by
  have hsp32 : sp - BitVec.ofNat 256 32 = sp - BitVec.ofNat 256 32 := rfl
  -- obstacle (a): the reads of statement 3 go through the 'q_sp' write of statement 2
  have hset_top : VEnv.get (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" = some x :=
    venvGet_set_ne V "q_sp" "q_top" (sp - BitVec.ofNat 256 32) x
      (by decide : ("q_sp" : Ident) ≠ "q_top") hget_top
  have hset_r : VEnv.get (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "r" = some frModulusWord :=
    venvGet_set_ne V "q_sp" "r" (sp - BitVec.ofNat 256 32) frModulusWord
      (by decide : ("q_sp" : Ident) ≠ "r") hget_r
  have hset_sp : VEnv.get (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_sp" =
      some (sp - BitVec.ofNat 256 32) :=
    venvGet_set_same V "q_sp" (sp - BitVec.ofNat 256 32) sp hget_sp
  -- statement 1: the empty-stack guard, taking its FALSE branch
  have hargs_g : Step (D := Bridge.Dialect c g) funs V st
      (.args [yvar "q_sp", ylit program.stackMptr])
      (.eres (.vals [sp, BitVec.ofNat 256 program.stackMptr] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit program.stackMptr])
      (restvals := [BitVec.ofNat 256 program.stackMptr]) (st1 := st) (v := sp) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
        (v := BitVec.ofNat 256 program.stackMptr) (st2 := st)
        (Step.argsNil (D := Bridge.Dialect c g)) Step.lit)
      (Step.var (D := Bridge.Dialect c g) hget_sp)
  have hcond : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.eq [yvar "q_sp", ylit program.stackMptr]))
      (.eres (.vals [b2w (decide (sp = BitVec.ofNat 256 program.stackMptr))] st)) :=
    Step.builtinOk hargs_g (dialect_builtin_eq st sp (BitVec.ofNat 256 program.stackMptr))
  have hzero : b2w (decide (sp = BitVec.ofNat 256 program.stackMptr)) = (Bridge.Dialect c g).zero := by
    rw [decide_eq_false hsp]
    rfl
  have hstmt1 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (yif (yop Op.eq [yvar "q_sp", ylit program.stackMptr])
        [yexpr (ycall "q_program_fail" [])]))
      (.sres V st .normal) :=
    Step.ifFalse hcond hzero
  -- statement 2: q_sp := q_sp - 32
  have hargs_s : Step (D := Bridge.Dialect c g) funs V st
      (.args [yvar "q_sp", ylit 32]) (.eres (.vals [sp, BitVec.ofNat 256 32] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 32])
      (restvals := [BitVec.ofNat 256 32]) (st1 := st) (v := sp) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
        (v := BitVec.ofNat 256 32) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g)) Step.lit)
      (Step.var (D := Bridge.Dialect c g) hget_sp)
  have hexpr_s : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.sub [yvar "q_sp", ylit 32]))
      (.eres (.vals [sp - BitVec.ofNat 256 32] st)) :=
    Step.builtinOk hargs_s (dialect_builtin_sub st sp (BitVec.ofNat 256 32))
  have hstmt2 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (yset "q_sp" (yop Op.sub [yvar "q_sp", ylit 32])))
      (.sres (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_sp"])
      (vals := [sp - BitVec.ofNat 256 32]) hexpr_s (by rfl)
  -- statement 3: q_top := addmod(mload(q_sp), q_top, r) - the mload moves the state
  have hml0 : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.expr (yop Op.mload [yvar "q_sp"]))
      (.eres (.vals [loadWord st.memory (sp - BitVec.ofNat 256 32).toNat]
        (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) :=
    Step.builtinOk (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
      (st1 := st) (v := sp - BitVec.ofNat 256 32) (st2 := st)
      (Step.argsNil (D := Bridge.Dialect c g))
      (Step.var (D := Bridge.Dialect c g) hset_sp))
      (dialect_builtin_mload st (sp - BitVec.ofNat 256 32))
  have hml : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.expr (yop Op.mload [yvar "q_sp"]))
      (.eres (.vals [y] (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) := by
    rw [← hload]
    exact hml0
  have hargs3 : Step (D := Bridge.Dialect c g)
      funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.args [yop Op.mload [yvar "q_sp"], yvar "q_top", yvar "r"])
      (.eres (.vals [y, x, frModulusWord] (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_top", yvar "r"])
      (restvals := [x, frModulusWord]) (st1 := st) (v := y)
      (st2 := touchMemory st (sp - BitVec.ofNat 256 32).toNat 32)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := st) (v := x) (st2 := st)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
          (v := frModulusWord) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hset_r))
        (Step.var (D := Bridge.Dialect c g) hset_top))
      hml
  have hexpr3 : Step (D := Bridge.Dialect c g)
      funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.expr (yop Op.addmod [yop Op.mload [yvar "q_sp"], yvar "q_top", yvar "r"]))
      (.eres (.vals [wAddmod y x] (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) :=
    Step.builtinOk hargs3
      (dialect_builtin_addmod_atFr (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) y x)
  have hstmt3 : Step (D := Bridge.Dialect c g)
      funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.stmt (yset "q_top"
        (yop Op.addmod [yop Op.mload [yvar "q_sp"], yvar "q_top", yvar "r"])))
      (.sres (VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" (wAddmod y x))
        (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod y x]) hexpr3
      (by rfl)
  unfold GenAst.qArmBodyAdd
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := V) (st1 := st) hstmt1 ?_
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) (st1 := st) hstmt2 ?_
  exact Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" (wAddmod y x))
    (st1 := touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) hstmt3
    (Step.seqNil (D := Bridge.Dialect c g))

/-- **ARM ADD: THE VALUE REFINEMENT, PROVED.** -/
theorem qArmValue_add {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (sp x y : U256)
    (hsp : sp ≠ BitVec.ofNat 256 program.stackMptr) :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAdd ctx program tcq)
      (fun V st => VEnv.get V "q_sp" = some sp ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        loadWord st.memory (sp - BitVec.ofNat 256 32).toNat = y)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory st (sp - BitVec.ofNat 256 32).toNat 32 ∧
        V' = VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top"
          (BitVec.ofNat 256 (qvmFrAdd y.toNat x.toNat))) := by
  intro V st hpre
  have hrun := qArmRun_add ctx program tcq funs V st sp x y hpre.1 hsp hpre.2.1 hpre.2.2.1 hpre.2.2.2
  rw [wAddmod_eq_qvmFrAdd] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

/-- **ARM ADD: THE EVERY-RUN FORM.** -/
theorem qArmValueAll_add {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (sp x y : U256)
    (hsp : sp ≠ BitVec.ofNat 256 program.stackMptr) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAdd ctx program tcq)
      (fun V st => VEnv.get V "q_sp" = some sp ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        loadWord st.memory (sp - BitVec.ofNat 256 32).toNat = y)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory st (sp - BitVec.ofNat 256 32).toNat 32 ∧
        V' = VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top"
          (BitVec.ofNat 256 (qvmFrAdd y.toNat x.toNat))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_add ctx program tcq funs sp x y hsp)

/-- **ARM MUL RUNS.** The twin of 'qArmRun_add' with the product. -/
theorem qArmRun_mul {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (sp x y : U256)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hsp : sp ≠ BitVec.ofNat 256 program.stackMptr)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hload : loadWord st.memory (sp - BitVec.ofNat 256 32).toNat = y) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyMul ctx program tcq)
      (VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" (wMulmod y x))
      (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) .normal := by
  have hset_top : VEnv.get (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" = some x :=
    venvGet_set_ne V "q_sp" "q_top" (sp - BitVec.ofNat 256 32) x
      (by decide : ("q_sp" : Ident) ≠ "q_top") hget_top
  have hset_r : VEnv.get (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "r" = some frModulusWord :=
    venvGet_set_ne V "q_sp" "r" (sp - BitVec.ofNat 256 32) frModulusWord
      (by decide : ("q_sp" : Ident) ≠ "r") hget_r
  have hset_sp : VEnv.get (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_sp" =
      some (sp - BitVec.ofNat 256 32) :=
    venvGet_set_same V "q_sp" (sp - BitVec.ofNat 256 32) sp hget_sp
  have hargs_g : Step (D := Bridge.Dialect c g) funs V st
      (.args [yvar "q_sp", ylit program.stackMptr])
      (.eres (.vals [sp, BitVec.ofNat 256 program.stackMptr] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit program.stackMptr])
      (restvals := [BitVec.ofNat 256 program.stackMptr]) (st1 := st) (v := sp) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
        (v := BitVec.ofNat 256 program.stackMptr) (st2 := st)
        (Step.argsNil (D := Bridge.Dialect c g)) Step.lit)
      (Step.var (D := Bridge.Dialect c g) hget_sp)
  have hcond : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.eq [yvar "q_sp", ylit program.stackMptr]))
      (.eres (.vals [b2w (decide (sp = BitVec.ofNat 256 program.stackMptr))] st)) :=
    Step.builtinOk hargs_g (dialect_builtin_eq st sp (BitVec.ofNat 256 program.stackMptr))
  have hzero : b2w (decide (sp = BitVec.ofNat 256 program.stackMptr)) = (Bridge.Dialect c g).zero := by
    rw [decide_eq_false hsp]
    rfl
  have hstmt1 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (yif (yop Op.eq [yvar "q_sp", ylit program.stackMptr])
        [yexpr (ycall "q_program_fail" [])]))
      (.sres V st .normal) :=
    Step.ifFalse hcond hzero
  have hargs_s : Step (D := Bridge.Dialect c g) funs V st
      (.args [yvar "q_sp", ylit 32]) (.eres (.vals [sp, BitVec.ofNat 256 32] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 32])
      (restvals := [BitVec.ofNat 256 32]) (st1 := st) (v := sp) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
        (v := BitVec.ofNat 256 32) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g)) Step.lit)
      (Step.var (D := Bridge.Dialect c g) hget_sp)
  have hexpr_s : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.sub [yvar "q_sp", ylit 32]))
      (.eres (.vals [sp - BitVec.ofNat 256 32] st)) :=
    Step.builtinOk hargs_s (dialect_builtin_sub st sp (BitVec.ofNat 256 32))
  have hstmt2 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (yset "q_sp" (yop Op.sub [yvar "q_sp", ylit 32])))
      (.sres (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_sp"])
      (vals := [sp - BitVec.ofNat 256 32]) hexpr_s (by rfl)
  have hml0 : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.expr (yop Op.mload [yvar "q_sp"]))
      (.eres (.vals [loadWord st.memory (sp - BitVec.ofNat 256 32).toNat]
        (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) :=
    Step.builtinOk (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
      (st1 := st) (v := sp - BitVec.ofNat 256 32) (st2 := st)
      (Step.argsNil (D := Bridge.Dialect c g))
      (Step.var (D := Bridge.Dialect c g) hset_sp))
      (dialect_builtin_mload st (sp - BitVec.ofNat 256 32))
  have hml : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.expr (yop Op.mload [yvar "q_sp"]))
      (.eres (.vals [y] (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) := by
    rw [← hload]
    exact hml0
  have hargs3 : Step (D := Bridge.Dialect c g)
      funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.args [yop Op.mload [yvar "q_sp"], yvar "q_top", yvar "r"])
      (.eres (.vals [y, x, frModulusWord] (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_top", yvar "r"])
      (restvals := [x, frModulusWord]) (st1 := st) (v := y)
      (st2 := touchMemory st (sp - BitVec.ofNat 256 32).toNat 32)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := st) (v := x) (st2 := st)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
          (v := frModulusWord) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hset_r))
        (Step.var (D := Bridge.Dialect c g) hset_top))
      hml
  have hexpr3 : Step (D := Bridge.Dialect c g)
      funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.expr (yop Op.mulmod [yop Op.mload [yvar "q_sp"], yvar "q_top", yvar "r"]))
      (.eres (.vals [wMulmod y x] (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32))) :=
    Step.builtinOk hargs3
      (dialect_builtin_mulmod_atFr (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) y x)
  have hstmt3 : Step (D := Bridge.Dialect c g)
      funs (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) st
      (.stmt (yset "q_top"
        (yop Op.mulmod [yop Op.mload [yvar "q_sp"], yvar "q_top", yvar "r"])))
      (.sres (VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" (wMulmod y x))
        (touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wMulmod y x]) hexpr3
      (by rfl)
  unfold GenAst.qArmBodyMul
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := V) (st1 := st) hstmt1 ?_
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) (st1 := st) hstmt2 ?_
  exact Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" (wMulmod y x))
    (st1 := touchMemory st (sp - BitVec.ofNat 256 32).toNat 32) hstmt3
    (Step.seqNil (D := Bridge.Dialect c g))

/-- **ARM MUL: THE VALUE REFINEMENT, PROVED.** -/
theorem qArmValue_mul {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (sp x y : U256)
    (hsp : sp ≠ BitVec.ofNat 256 program.stackMptr) :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMul ctx program tcq)
      (fun V st => VEnv.get V "q_sp" = some sp ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        loadWord st.memory (sp - BitVec.ofNat 256 32).toNat = y)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory st (sp - BitVec.ofNat 256 32).toNat 32 ∧
        V' = VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top"
          (BitVec.ofNat 256 (qvmFrMul y.toNat x.toNat))) := by
  intro V st hpre
  have hrun := qArmRun_mul ctx program tcq funs V st sp x y hpre.1 hsp hpre.2.1 hpre.2.2.1 hpre.2.2.2
  rw [wMulmod_eq_qvmFrMul] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

/-- **ARM MUL: THE EVERY-RUN FORM.** -/
theorem qArmValueAll_mul {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (sp x y : U256)
    (hsp : sp ≠ BitVec.ofNat 256 program.stackMptr) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMul ctx program tcq)
      (fun V st => VEnv.get V "q_sp" = some sp ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        loadWord st.memory (sp - BitVec.ofNat 256 32).toNat = y)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory st (sp - BitVec.ofNat 256 32).toNat 32 ∧
        V' = VEnv.set (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top"
          (BitVec.ofNat 256 (qvmFrMul y.toNat x.toNat))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_mul ctx program tcq funs sp x y hsp)

/-! ### K. THE ADD_CONST_U8 / MUL_CONST_U8 ARMS (QARMS - the operand DECODE enters)

These are the first arms whose emitted side DECODES ITS OWN OPERAND from memory: 'qconst =
byte(0, mload(q_pc))' is the arm reading its own slot index out of the program window, and then it
reads the constant table at 'q_const_mptr + 32*qconst'. Two reads, one of them at an address the arm
computes. The reference side of the same two reads is 'constAt consts b₀ 0 = .ok v'
('qStepValue_addConstU8'), so the tie is a PAIR of reader equations, and they are stated at the
EMITTED expressions - 'loadWord st.memory pc.toNat >>> 248 &&& 0xff' for the decode and
'loadWord st.memory (cb + (b₀ <<< 5)).toNat' for the table read - which is what makes them
checkable against 'AgreesProgram'/'AgreesConsts' later instead of against a fixture.

**THE 'Midfall/Yul/Word.lean' SECTION 8 BRIDGES ARE NOT NEEDED HERE, AND THAT IS THE POINT.**
'loadWord_topByte' / 'loadWord_topByte_mask' identify the DECODED BYTE with a memory byte
'mem p'. Stating the hypothesis at the emitted expression instead means the arm theorem is independent
of how the byte got there, and the byte-level bridge becomes the composition's job (one use per arm,
not one per theorem). The 'shl 5' / 'byte 0' shifts are 'rfl' at the open dialect. -/

/-- 'byte(0, w)' at the open dialect: the vendored case is '(w >>> (248 - 8*i.toNat)) &&& 0xff'
    (EVMExec.lean:738) and at 'i = 0' the guard '32 ≤ i.toNat' is false, so this is 'rfl'. -/
theorem dialect_builtin_byte0 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :
    (Bridge.Dialect c g).Builtin Op.byte [BitVec.ofNat 256 0, w] st
      (.ok [(w >>> 248) &&& 0xff] st) := rfl

/-- 'shl(5, w)' at the open dialect (EVMExec.lean:739: 'val <<< shift.toNat'). -/
theorem dialect_builtin_shl5 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :
    (Bridge.Dialect c g).Builtin Op.shl [BitVec.ofNat 256 5, w] st (.ok [w <<< 5] st) := rfl

/-- Plain 'add' at the open dialect - the pointer arithmetic, not the field addition. -/
theorem dialect_builtin_add {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.add [a, b] st (.ok [a + b] st) := rfl

/-- **ARM ADD_CONST_U8 RUNS.** The arm decodes its slot index from the program window, advances
    'q_pc' by one, and leaves 'q_top' at 'wAddmod x v' for 'v' the constant table's word at that slot -
    which 'wAddmod_eq_qvmFrAdd' identifies with the 'qvmFrAdd acc v' that 'qStepValue_addConstU8'
    pushes. The state is the one BOTH 'mload's touched. -/
theorem qArmRun_addConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb x : U256) (b₀ : Nat) (v : U256)
    (hget_pc : VEnv.get V "q_pc" = some pc) (hget_top : VEnv.get V "q_top" = some x)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hbyte : (loadWord st.memory pc.toNat >>> 248) &&& 0xff = BitVec.ofNat 256 b₀)
    (hconst : loadWord st.memory (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat = v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAddConstU8 ctx program tcq)
      (("qconst", BitVec.ofNat 256 b₀) ::
        VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" (wAddmod x v))
      (touchMemory (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32) .normal := by
  -- statement 1: let qconst := byte(0, mload(q_pc)) - the operand DECODE, and it MOVES the state
  have hmlpc : Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]])
      (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
      (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32)
      (Step.argsNil (D := Bridge.Dialect c g))
      (Step.builtinOk (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
        (st1 := st) (v := pc) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
        (Step.var (D := Bridge.Dialect c g) hget_pc))
        (dialect_builtin_mload st pc))
  have hbyteexpr : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]]))
      (.eres (.vals [BitVec.ofNat 256 b₀] (touchMemory st pc.toNat 32))) := by
    have h := Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]])
        (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32)
        (v := BitVec.ofNat 256 0) (st2 := touchMemory st pc.toNat 32)
        hmlpc (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)))
      (dialect_builtin_byte0 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
    rw [hbyte] at h
    exact h
  have hstmt1 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (ylet "qconst" (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])))
      (.sres (("qconst", BitVec.ofNat 256 b₀) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal hbyteexpr rfl
  -- statement 2: q_pc := q_pc + 1
  have hargs_pc : Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b₀) :: V)
      (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 1])
      (.eres (.vals [pc, BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 1])
      (restvals := [BitVec.ofNat 256 1]) (st1 := touchMemory st pc.toNat 32) (v := pc)
      (st2 := touchMemory st pc.toNat 32)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
        (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 1)
        (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) Step.lit)
      (Step.var (D := Bridge.Dialect c g)
        (by rw [venvGet_cons_ne V "qconst" "q_pc" (BitVec.ofNat 256 b₀)
          (by decide : ("qconst" : Ident) ≠ "q_pc")]; exact hget_pc))
  have hexpr_pc : Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b₀) :: V)
      (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 1]))
      (.eres (.vals [pc + BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk hargs_pc
      (dialect_builtin_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 1))
  have hstmt2 : Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b₀) :: V)
      (touchMemory st pc.toNat 32)
      (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 1])))
      (.sres (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"])
      (vals := [pc + BitVec.ofNat 256 1]) hexpr_pc (by rfl)
  -- statement 3: q_top := addmod(q_top, mload(q_const_mptr + (qconst << 5)), r)
  have hget3_qconst :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "qconst" = some (BitVec.ofNat 256 b₀) := venvGet_cons_eq _ _ _
  have hget3_top :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "q_top" = some x := by
    rw [venvGet_cons_ne (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" "q_top"
      (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_top")]
    exact venvGet_set_ne V "q_pc" "q_top" (pc + BitVec.ofNat 256 1) x
      (by decide : ("q_pc" : Ident) ≠ "q_top") hget_top
  have hget3_cb :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "q_const_mptr" = some cb := by
    rw [venvGet_cons_ne (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" "q_const_mptr"
      (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_const_mptr")]
    exact venvGet_set_ne V "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 1) cb
      (by decide : ("q_pc" : Ident) ≠ "q_const_mptr") hget_cb
  have hget3_r :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "r" = some frModulusWord := by
    rw [venvGet_cons_ne (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" "r"
      (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "r")]
    exact venvGet_set_ne V "q_pc" "r" (pc + BitVec.ofNat 256 1) frModulusWord
      (by decide : ("q_pc" : Ident) ≠ "r") hget_r
  have hshl : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.shl [ylit 5, yvar "qconst"]))
      (.eres (.vals [BitVec.ofNat 256 b₀ <<< 5] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"])
        (restvals := [BitVec.ofNat 256 b₀]) (st1 := touchMemory st pc.toNat 32)
        (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b₀)
          (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget3_qconst))
        (Step.lit (D := Bridge.Dialect c g)))
      (dialect_builtin_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b₀))
  have hptr : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]))
      (.eres (.vals [cb + (BitVec.ofNat 256 b₀ <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g)
        (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [BitVec.ofNat 256 b₀ <<< 5])
        (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b₀ <<< 5)
          (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) hshl)
        (Step.var (D := Bridge.Dialect c g) hget3_cb))
      (dialect_builtin_add (touchMemory st pc.toNat 32) cb (BitVec.ofNat 256 b₀ <<< 5))
  have hcm : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]))
      (.eres (.vals [v]
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32))) := by
    have h := Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
        (st1 := touchMemory st pc.toNat 32) (v := cb + (BitVec.ofNat 256 b₀ <<< 5))
        (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) hptr)
      (dialect_builtin_mload (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)))
    rw [Midfall.Yul.Word.touchMemory_memory st pc.toNat 32] at h
    rw [hconst] at h
    exact h
  have hargs3 : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.args [yvar "q_top",
        yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"])
      (.eres (.vals [x, v, frModulusWord]
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g)
      (rest := [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"])
      (restvals := [v, frModulusWord])
      (st1 := touchMemory (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
      (v := x)
      (st2 := touchMemory (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := touchMemory st pc.toNat 32) (v := v)
        (st2 := touchMemory (touchMemory st pc.toNat 32)
          (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st1 := touchMemory st pc.toNat 32) (v := frModulusWord)
          (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget3_r))
        hcm)
      (Step.var (D := Bridge.Dialect c g) hget3_top)
  have hexpr3 : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.addmod [yvar "q_top",
        yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"]))
      (.eres (.vals [wAddmod x v]
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32))) :=
    Step.builtinOk hargs3
      (dialect_builtin_addmod_atFr
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32) x v)
  have hstmt3 : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.stmt (yset "q_top" (yop Op.addmod [yvar "q_top",
        yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"])))
      (.sres (("qconst", BitVec.ofNat 256 b₀) ::
        VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" (wAddmod x v))
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
        .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod x v]) hexpr3
      (by rfl)
  unfold GenAst.qArmBodyAddConstU8
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := ("qconst", BitVec.ofNat 256 b₀) :: V) (st1 := touchMemory st pc.toNat 32) hstmt1 ?_
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := ("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
    (st1 := touchMemory st pc.toNat 32) hstmt2 ?_
  exact Step.seqCons (D := Bridge.Dialect c g)
    (V1 := ("qconst", BitVec.ofNat 256 b₀) ::
      VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" (wAddmod x v))
    (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
    hstmt3 (Step.seqNil (D := Bridge.Dialect c g))

/-- **ARM ADD_CONST_U8: THE VALUE REFINEMENT, PROVED.** -/
theorem qArmValue_addConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x : U256) (b₀ : Nat) (v : U256) :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧ VEnv.get V "r" = some frModulusWord ∧
        (loadWord st.memory pc.toNat >>> 248) &&& 0xff = BitVec.ofNat 256 b₀ ∧
        loadWord st.memory (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory (touchMemory st pc.toNat 32)
          (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32 ∧
        V' = (("qconst", BitVec.ofNat 256 b₀) ::
          VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top"
            (BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)))) := by
  intro V st hpre
  have hrun := qArmRun_addConstU8 ctx program tcq funs V st pc cb x b₀ v hpre.1 hpre.2.1 hpre.2.2.1
    hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2
  rw [wAddmod_eq_qvmFrAdd] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

/-- **ARM ADD_CONST_U8: THE EVERY-RUN FORM.** -/
theorem qArmValueAll_addConstU8 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x : U256) (b₀ : Nat) (v : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧ VEnv.get V "r" = some frModulusWord ∧
        (loadWord st.memory pc.toNat >>> 248) &&& 0xff = BitVec.ofNat 256 b₀ ∧
        loadWord st.memory (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory (touchMemory st pc.toNat 32)
          (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32 ∧
        V' = (("qconst", BitVec.ofNat 256 b₀) ::
          VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top"
            (BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_addConstU8 ctx program tcq funs pc cb x b₀ v)

/-! ### L. THE MUL_CONST_U8 ARM (QARMS)

The twin of section K with the product: 'mulmod(q_top, mload(q_const_mptr + 32*qconst), r)' against
'qStepValue_mulConstU8''s 'qvmFrMul acc v'. Same two reader equations, same decode, same state
threading - and again the tie is 'wMulmod_eq_qvmFrMul', which is 'rfl'. It is landed as a separate
theorem rather than a lemma schema on purpose: the arms differ in their guards and their reads, and a
schema that hides that is worth less than the copy. -/

/-- **ARM MUL_CONST_U8 RUNS.** The arm decodes its slot index from the program window, advances
    'q_pc' by one, and leaves 'q_top' at 'wMulmod x v' for 'v' the constant table's word at that slot -
    which 'wMulmod_eq_qvmFrMul' identifies with the 'qvmFrMul acc v' that 'qStepValue_mulConstU8'
    pushes. The state is the one BOTH 'mload's touched. -/
theorem qArmRun_mulConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb x : U256) (b₀ : Nat) (v : U256)
    (hget_pc : VEnv.get V "q_pc" = some pc) (hget_top : VEnv.get V "q_top" = some x)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hbyte : (loadWord st.memory pc.toNat >>> 248) &&& 0xff = BitVec.ofNat 256 b₀)
    (hconst : loadWord st.memory (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat = v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyMulConstU8 ctx program tcq)
      (("qconst", BitVec.ofNat 256 b₀) ::
        VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" (wMulmod x v))
      (touchMemory (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32) .normal := by
  -- statement 1: let qconst := byte(0, mload(q_pc)) - the operand DECODE, and it MOVES the state
  have hmlpc : Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]])
      (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
      (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32)
      (Step.argsNil (D := Bridge.Dialect c g))
      (Step.builtinOk (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
        (st1 := st) (v := pc) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
        (Step.var (D := Bridge.Dialect c g) hget_pc))
        (dialect_builtin_mload st pc))
  have hbyteexpr : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]]))
      (.eres (.vals [BitVec.ofNat 256 b₀] (touchMemory st pc.toNat 32))) := by
    have h := Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]])
        (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32)
        (v := BitVec.ofNat 256 0) (st2 := touchMemory st pc.toNat 32)
        hmlpc (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)))
      (dialect_builtin_byte0 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
    rw [hbyte] at h
    exact h
  have hstmt1 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (ylet "qconst" (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])))
      (.sres (("qconst", BitVec.ofNat 256 b₀) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal hbyteexpr rfl
  -- statement 2: q_pc := q_pc + 1
  have hargs_pc : Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b₀) :: V)
      (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 1])
      (.eres (.vals [pc, BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 1])
      (restvals := [BitVec.ofNat 256 1]) (st1 := touchMemory st pc.toNat 32) (v := pc)
      (st2 := touchMemory st pc.toNat 32)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
        (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 1)
        (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) Step.lit)
      (Step.var (D := Bridge.Dialect c g)
        (by rw [venvGet_cons_ne V "qconst" "q_pc" (BitVec.ofNat 256 b₀)
          (by decide : ("qconst" : Ident) ≠ "q_pc")]; exact hget_pc))
  have hexpr_pc : Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b₀) :: V)
      (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 1]))
      (.eres (.vals [pc + BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk hargs_pc
      (dialect_builtin_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 1))
  have hstmt2 : Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b₀) :: V)
      (touchMemory st pc.toNat 32)
      (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 1])))
      (.sres (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"])
      (vals := [pc + BitVec.ofNat 256 1]) hexpr_pc (by rfl)
  -- statement 3: q_top := mulmod(q_top, mload(q_const_mptr + (qconst << 5)), r)
  have hget3_qconst :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "qconst" = some (BitVec.ofNat 256 b₀) := venvGet_cons_eq _ _ _
  have hget3_top :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "q_top" = some x := by
    rw [venvGet_cons_ne (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" "q_top"
      (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_top")]
    exact venvGet_set_ne V "q_pc" "q_top" (pc + BitVec.ofNat 256 1) x
      (by decide : ("q_pc" : Ident) ≠ "q_top") hget_top
  have hget3_cb :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "q_const_mptr" = some cb := by
    rw [venvGet_cons_ne (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" "q_const_mptr"
      (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_const_mptr")]
    exact venvGet_set_ne V "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 1) cb
      (by decide : ("q_pc" : Ident) ≠ "q_const_mptr") hget_cb
  have hget3_r :
      VEnv.get (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
        "r" = some frModulusWord := by
    rw [venvGet_cons_ne (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" "r"
      (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "r")]
    exact venvGet_set_ne V "q_pc" "r" (pc + BitVec.ofNat 256 1) frModulusWord
      (by decide : ("q_pc" : Ident) ≠ "r") hget_r
  have hshl : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.shl [ylit 5, yvar "qconst"]))
      (.eres (.vals [BitVec.ofNat 256 b₀ <<< 5] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"])
        (restvals := [BitVec.ofNat 256 b₀]) (st1 := touchMemory st pc.toNat 32)
        (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b₀)
          (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget3_qconst))
        (Step.lit (D := Bridge.Dialect c g)))
      (dialect_builtin_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b₀))
  have hptr : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]))
      (.eres (.vals [cb + (BitVec.ofNat 256 b₀ <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g)
        (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [BitVec.ofNat 256 b₀ <<< 5])
        (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b₀ <<< 5)
          (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) hshl)
        (Step.var (D := Bridge.Dialect c g) hget3_cb))
      (dialect_builtin_add (touchMemory st pc.toNat 32) cb (BitVec.ofNat 256 b₀ <<< 5))
  have hcm : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]))
      (.eres (.vals [v]
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32))) := by
    have h := Step.builtinOk
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
        (st1 := touchMemory st pc.toNat 32) (v := cb + (BitVec.ofNat 256 b₀ <<< 5))
        (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) hptr)
      (dialect_builtin_mload (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)))
    rw [Midfall.Yul.Word.touchMemory_memory st pc.toNat 32] at h
    rw [hconst] at h
    exact h
  have hargs3 : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.args [yvar "q_top",
        yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"])
      (.eres (.vals [x, v, frModulusWord]
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g)
      (rest := [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"])
      (restvals := [v, frModulusWord])
      (st1 := touchMemory (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
      (v := x)
      (st2 := touchMemory (touchMemory st pc.toNat 32)
        (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord])
        (st1 := touchMemory st pc.toNat 32) (v := v)
        (st2 := touchMemory (touchMemory st pc.toNat 32)
          (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st1 := touchMemory st pc.toNat 32) (v := frModulusWord)
          (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g))
          (Step.var (D := Bridge.Dialect c g) hget3_r))
        hcm)
      (Step.var (D := Bridge.Dialect c g) hget3_top)
  have hexpr3 : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.expr (yop Op.mulmod [yvar "q_top",
        yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"]))
      (.eres (.vals [wMulmod x v]
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32))) :=
    Step.builtinOk hargs3
      (dialect_builtin_mulmod_atFr
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32) x v)
  have hstmt3 : Step (D := Bridge.Dialect c g)
      funs (("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
      (touchMemory st pc.toNat 32)
      (.stmt (yset "q_top" (yop Op.mulmod [yvar "q_top",
        yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]],
        yvar "r"])))
      (.sres (("qconst", BitVec.ofNat 256 b₀) ::
        VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" (wMulmod x v))
        (touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
        .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wMulmod x v]) hexpr3
      (by rfl)
  unfold GenAst.qArmBodyMulConstU8
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := ("qconst", BitVec.ofNat 256 b₀) :: V) (st1 := touchMemory st pc.toNat 32) hstmt1 ?_
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := ("qconst", BitVec.ofNat 256 b₀) :: VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1))
    (st1 := touchMemory st pc.toNat 32) hstmt2 ?_
  exact Step.seqCons (D := Bridge.Dialect c g)
    (V1 := ("qconst", BitVec.ofNat 256 b₀) ::
      VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" (wMulmod x v))
    (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32)
    hstmt3 (Step.seqNil (D := Bridge.Dialect c g))

/-- **ARM MUL_CONST_U8: THE VALUE REFINEMENT, PROVED.** -/
theorem qArmValue_mulConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x : U256) (b₀ : Nat) (v : U256) :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMulConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧ VEnv.get V "r" = some frModulusWord ∧
        (loadWord st.memory pc.toNat >>> 248) &&& 0xff = BitVec.ofNat 256 b₀ ∧
        loadWord st.memory (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory (touchMemory st pc.toNat 32)
          (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32 ∧
        V' = (("qconst", BitVec.ofNat 256 b₀) ::
          VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top"
            (BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)))) := by
  intro V st hpre
  have hrun := qArmRun_mulConstU8 ctx program tcq funs V st pc cb x b₀ v hpre.1 hpre.2.1 hpre.2.2.1
    hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2
  rw [wMulmod_eq_qvmFrMul] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

/-- **ARM MUL_CONST_U8: THE EVERY-RUN FORM.** -/
theorem qArmValueAll_mulConstU8 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x : U256) (b₀ : Nat) (v : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMulConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧ VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧ VEnv.get V "r" = some frModulusWord ∧
        (loadWord st.memory pc.toNat >>> 248) &&& 0xff = BitVec.ofNat 256 b₀ ∧
        loadWord st.memory (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal ∧
        st' = touchMemory (touchMemory st pc.toNat 32)
          (cb + (BitVec.ofNat 256 b₀ <<< 5)).toNat 32 ∧
        V' = (("qconst", BitVec.ofNat 256 b₀) ::
          VEnv.set (VEnv.set V "q_pc" (pc + BitVec.ofNat 256 1)) "q_top"
            (BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_mulConstU8 ctx program tcq funs pc cb x b₀ v)

#check @Midfall.LoweringV3.QuotientFrame.qArmValue_addConstU8
#check @Midfall.LoweringV3.QuotientFrame.qArmValueAll_addConstU8
#check @Midfall.LoweringV3.QuotientFrame.qArmValue_mulConstU8
#check @Midfall.LoweringV3.QuotientFrame.qArmValueAll_mulConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qArmRun_addConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValue_addConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValueAll_addConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qArmRun_mulConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValue_mulConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValueAll_mulConstU8
#check @Midfall.LoweringV3.QuotientFrame.qArmValue_add
#check @Midfall.LoweringV3.QuotientFrame.qArmValueAll_add
#check @Midfall.LoweringV3.QuotientFrame.qArmValue_mul
#check @Midfall.LoweringV3.QuotientFrame.qArmValueAll_mul
#print axioms Midfall.LoweringV3.QuotientFrame.qArmRun_add
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValue_add
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValueAll_add
#print axioms Midfall.LoweringV3.QuotientFrame.qArmRun_mul
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValue_mul
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValueAll_mul
#print axioms Midfall.LoweringV3.QuotientFrame.venvGet_set_ne
#print axioms Midfall.LoweringV3.QuotientFrame.wAddmod_eq_qvmFrAdd
#check @Midfall.LoweringV3.QuotientFrame.qArmValue_pow5
#check @Midfall.LoweringV3.QuotientFrame.qArmValueAll_pow5
#print axioms Midfall.LoweringV3.QuotientFrame.qArmRun_pow5
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValue_pow5
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValueAll_pow5
#print axioms Midfall.LoweringV3.QuotientFrame.wMulmod_eq_qvmFrPow5
#print axioms Midfall.LoweringV3.QuotientFrame.qvmFrMul_pow5_nest

#print axioms Midfall.LoweringV3.QuotientFrame.evalQuotientIdentity_one
#print axioms Midfall.LoweringV3.QuotientFrame.qStepValue_pushConst
#print axioms Midfall.LoweringV3.QuotientFrame.qStepValue_add
#print axioms Midfall.LoweringV3.QuotientFrame.qStepValue_modarith7
#print axioms Midfall.LoweringV3.QuotientFrame.qStepValue_pushMemU16_memOfρ
#print axioms Midfall.LoweringV3.QuotientFrame.AgreesFrame_memOfρ
#print axioms Midfall.LoweringV3.QuotientFrame.AgreesFrame_memOfρ_only_if
#print axioms Midfall.LoweringV3.QuotientFrame.Agrees_memOfρ_nonvacuous
#print axioms Midfall.LoweringV3.QuotientFrame.qIdentity_pushConstU8
#print axioms Midfall.LoweringV3.QuotientFrame.qIdentity_pushMemU16_memOfρ
#print axioms Midfall.LoweringV3.QuotientFrame.evalQuotientIdentity_empty
#print axioms Midfall.LoweringV3.QuotientFrame.qSwitch_arm
#print axioms Midfall.LoweringV3.QuotientFrame.qSwitch_failClosed
#print axioms Midfall.LoweringV3.QuotientFrame.qvmLoop_body

#check @Midfall.LoweringV3.QuotientFrame.evalQuotientIdentity_one
#check @Midfall.LoweringV3.QuotientFrame.qStepValue_addMulMemMem
#check @Midfall.LoweringV3.QuotientFrame.AgreesFrame_memOfρ
#check @Midfall.LoweringV3.QuotientFrame.qArmValue_neg
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValueAll_neg
#print axioms Midfall.LoweringV3.QuotientFrame.qArmRun_neg
#print axioms Midfall.LoweringV3.QuotientFrame.qArmValue_neg
#print axioms Midfall.LoweringV3.QuotientFrame.wAddmod_eq_qvmFrNeg

end Midfall.LoweringV3.QuotientFrame

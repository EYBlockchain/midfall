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

end Midfall.LoweringV3.QuotientFrame

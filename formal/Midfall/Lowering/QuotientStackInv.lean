-- |
-- Midfall.Lowering.QuotientStackInv
--
-- STKINV: THE INDUCTIVE STACK INVARIANT - D-QVM2 item 3's residue, QFIX's obligation O2.
--
-- WHY A NEW FILE AND NOT AN APPENDIX TO 'QuotientInterp.lean'. The brief prefers appending, and the
-- reason it prefers it is cost: 'QuotientInterp.lean' is imported by 'QuotientFrame', 'QuotientArms',
-- 'QuotientRows' and 'QuotientLoopCompose', so one appended line rebuilds the cone-walk region
-- (25-30 MINUTES a cycle under contention). The invariant is also on the WRONG SIDE of that edge: its
-- step needs the per-arm every-run contracts 'qArmValueAll_X' and RTIE's ties 'rtie_X', and those
-- live in 'Midfall/LoweringV3', which IMPORTS 'QuotientInterp'. Stated in 'QuotientInterp' the
-- invariant could only ever be stated and left unproved - which is exactly what QFIX did with
-- 'QStackInvariant' ('QuotientRows.lean:1509'). So this file sits above the V3 arm layer, imports the
-- contract file, and PROVES the step. 'QuotientInterp.lean' is not edited by this card, not one byte,
-- so no cone-walk file rebuilds at all; 'QInterpRefinesSegment' is not restated, edited or
-- re-instantiated (RULES). 'Obligations.lean' is untouched, so the two PG_* props of section 6 are
-- named here and reported, not registered.
--
-- WHAT THE INVARIANT IS. 'QStackCorr program V st stk' relates the EMITTED machine's three stack
-- registers ('q_sp', 'q_has_top', 'q_top') to the REFERENCE's stack 'stk : List QVMFr' at an arm
-- boundary: the pointer is 'stackMptr + 32 * n' for exactly the 'n' words the machine has spilled
-- below its cached top, the cached-top flag is live exactly when the reference's stack is non-empty,
-- the cached word IS the reference's head (hence canonical, as every reference value is), and the
-- words spilled below it ARE the reference's tail in the reference's order. Then 'qStackCorr_neg',
-- 'qStackCorr_pow5', 'qStackCorr_add' and 'qStackCorr_mul' are the induction: run one arm, run the
-- reference's own step at the same opcode, and the correspondence holds again at the next boundary.
-- That is the fact QFIX said no start-state hypothesis can supply, and it is what turns RTIE's 19
-- one-step ties into a statement about a LOOP: the ties say what one arm computes; these theorems say
-- the arm boundary is a fixed point of the correspondence. 'qStackCorr_neg_then_add' is the witness
-- that two steps CHAIN - the second consumes what the first produced - the property a per-arm tie
-- structurally cannot have.
--
-- HOW IT RELATES TO 'QSegmentStackSafe', WHICH IS WHAT THE BRIEF ASKS TO CHECK FIRST. Item 3 is
-- 'qSegmentDepthGo (segment bytes) length 0 0 = some 1': a WALK over the validator's own decoder and
-- stack-effect table, from depth 0, ending at depth 1. It already contains the per-instruction stack
-- effect, machine-checked - but folded ONCE, from one fixed start to one fixed end, over a whole
-- segment, and about NO machine state. It is a certificate, not an invariant. This card lands the
-- generalisation and says how it sits:
--   * 'QSegmentStackSafeFrom bytes s d0 d1' - item 3 with an arbitrary start and end depth.
--     'QSegmentStackSafe bytes s ↔ QSegmentStackSafeFrom bytes s 0 1' is 'Iff.rfl': the generalisation
--     is CONSERVATIVE, item 3 is its (0,1) instance, and 'QInterpRefinesSegment' keeps using the (0,1)
--     form untouched.
--   * 'qSegmentDepthGo_step' - the walk's own induction step as an equation: one certified instruction
--     at depth 'd' IS the walk from the effect's depth 'd''. Item 3 only uses this implicitly by
--     computing; the loop needs it stated.
--   * 'qStackShape_neg' / '_pow5' / '_add' / '_mul' - the BRIDGE between the two worlds: for those
--     arms, whenever the reference's step succeeds, the validator's static effect applied to the
--     CURRENT STACK LENGTH returns exactly the reference's new length. So the walk's depth and the
--     invariant's depth clause are the same number at every boundary the reference reaches, which is
--     the sense in which item 3 is the fold of this invariant.
--
-- WHAT IS NOT CLAIMED, NAMED IN SECTION 6. (i) The push family's inductive step is blocked, and not
-- by anything here: every published push-arm contract pins 'q_has_top = some 0' in its PRE
-- ('qArmValueAll_pushConst', QuotientArms.lean:3081), i.e. it describes the arm's NO-SPILL branch,
-- while an inductive boundary is exactly the branch where the cached top is live and gets spilled.
-- 'PG_spillArmTriple' states that missing contract with its exact goal state. (ii) The whole-segment
-- iteration of the shape bridge needs the CURSOR agreement - decoded width = reference 'consumed' -
-- which is QFIX's (O4): 'PG_stackWalkCursor'. (iii) The five stream opcodes and the three native
-- markers are outside the identity domain: the reference refuses them and item 3's certificate refuses
-- them, so their arms are not covered and cannot be, until QSTREAM lands.
--
-- TEETH. The invariant is shown non-vacuous three ways: it holds of the prologue start state the
-- contract's item 4 already requires ('qStackCorr_of_prologueStart', so item 4 IS its base case); its
-- depth is unique, so it is a function of the registers and not a wish; and it REFUTES a machine that
-- claims a live cached top over an empty reference stack - the exact mismatch O2 says a start-state
-- hypothesis cannot catch.

import Midfall.Lowering.QuotientInterp
import Midfall.LoweringV3.QuotientFrame
import Midfall.LoweringV3.QuotientArms
import Midfall.LoweringV3.Statements
import Midfall.Tools.Done
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QuotientStackInv
open YulSemantics YulSemantics.EVM Midfall.Generator Midfall.Lowering Midfall.Lowering.GenAst
open Midfall.Yul Midfall.Yul.Bridge Midfall.Yul.WpX
open Midfall.Lowering.QuotientInterp
open Midfall.LoweringV3
open Midfall.LoweringV3.QuotientFrame

/-! ### 1. THE SPILLED-WORD MODEL -/

/-- The 'n' words the emitted machine has spilled BELOW its cached top, innermost first: memory at
    'sp - 32', then 'sp - 64', and so on. This is the machine's side of the reference's stack tail. -/
def qSpilled (st : EvmState) : Nat → U256 → List U256
  | 0, _ => []
  | k + 1, sp =>
      loadWord st.memory (sp - BitVec.ofNat 256 32).toNat :: qSpilled st k (sp - BitVec.ofNat 256 32)

/-- One more spilled word: the head is the word at 'sp - 32'. Definitional, named because the steps
    rewrite through it. -/
theorem qSpilled_succ (st : EvmState) (k : Nat) (sp : U256) :
    qSpilled st (k + 1) sp =
      loadWord st.memory (sp - BitVec.ofNat 256 32).toNat :: qSpilled st k (sp - BitVec.ofNat 256 32) :=
  rfl

/-- The spilled list holds exactly the depth's worth of words - the clause that makes the invariant's
    'n' the reference's tail LENGTH and not a free variable. -/
theorem qSpilled_length (st : EvmState) : ∀ (n : Nat) (sp : U256), (qSpilled st n sp).length = n
  | 0, _ => rfl
  | k + 1, sp => by
      rw [qSpilled_succ, List.length_cons, qSpilled_length st k (sp - BitVec.ofNat 256 32)]

/-- An 'mload' that only grows the memory does not move the spilled words: 'touchMemory' leaves the
    memory function alone ('touchMemory_memory'), and that is the whole content of this lemma. The
    ADD and MUL steps pop from memory and touch it, and this is what lets the tail survive the step. -/
theorem qSpilled_touchMemory (st : EvmState) (o s : Nat) : ∀ (n : Nat) (sp : U256),
    qSpilled (touchMemory st o s) n sp = qSpilled st n sp := by
  intro n
  induction n with
  | zero => intro sp; rfl
  | succ k ih =>
      intro sp
      rw [qSpilled_succ, qSpilled_succ, ih (sp - BitVec.ofNat 256 32),
        Midfall.Yul.Word.touchMemory_memory]

/-! ### 2. THE INVARIANT -/

/-- **THE STACK POINTER DOES NOT WRAP**, at depth 'n' - the stack analogue of QFIX's guard 1
    ('QWindowNoWrap'), and the fact that lets the pointer be read back as a NUMBER of spilled words
    instead of only as a word. It is NOT a new burden on the caller: 'quotientProgramFits'
    ('Statements.lean:3225', the D-QVM1 address-fit clause of 'programFits', hence of 'ValidV3' at the
    row) carries 'stackMptr ≤ stackLast' and 'stackLast + 32 < 2 ^ 256', which is the 'n = 0' case
    plus the room the machine's own spill guard ('q_sp > stackLast ⇒ fail') keeps the pointer inside. -/
def QStackNoWrap (program : QuotientProgram) (n : Nat) : Prop :=
  program.stackMptr + 32 * n < 2 ^ 256

theorem QStackNoWrap_zero_of_fits (program : QuotientProgram)
    (h : quotientProgramFits program) : QStackNoWrap program 0 := by
  have hc : program.stackMptr ≤ program.guards.stackLast := h.2.2.1
  have hd : program.guards.stackLast + 32 < 2 ^ 256 := h.2.2.2.1
  show program.stackMptr + 32 * 0 < 2 ^ 256
  exact Nat.lt_of_le_of_lt (Nat.le_add_right program.stackMptr 0)
    (Nat.lt_of_le_of_lt hc (Nat.lt_of_le_of_lt (Nat.le_add_right program.guards.stackLast 32) hd))

theorem QStackNoWrap.pre (program : QuotientProgram) (k : Nat)
    (h : QStackNoWrap program (k + 1)) : QStackNoWrap program k :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 32 (Nat.le_add_right k 1)) _) h

/-- **THE INVARIANT'S WITNESS RELATION**, factored out so the depth can be talked about: 'n' is the
    number of spilled words, 'sp' the pointer, 'top' the cached word. -/
def QStackCorrWith {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (stk : List QVMFr)
    (n : Nat) (sp top : U256) : Prop :=
  VEnv.get V "q_sp" = some sp ∧
    VEnv.get V "q_top" = some top ∧
    sp = BitVec.ofNat 256 (program.stackMptr + 32 * n) ∧
    QStackNoWrap program n ∧
    ((VEnv.get V "q_has_top" = some 0 ∧ stk = [] ∧ n = 0) ∨
      (VEnv.get V "q_has_top" = some 1 ∧ top.toNat < qvmFrModulus ∧
        stk = top.toNat :: (qSpilled st n sp).map BitVec.toNat ∧
        ∀ w ∈ qSpilled st n sp, w.toNat < qvmFrModulus))

/-- **THE INDUCTIVE STACK CORRESPONDENCE (QFIX's O2, LANDED).** At an ARM BOUNDARY, with 'stk' the
    reference's stack:

  * the emitted 'q_sp' is the word 'stackMptr + 32 * n' for some 'n', and that address does not wrap;
  * 'q_has_top = 0' with 'stk = []' and 'n = 0' - the prologue case, and the only case with no cached
    top;
  * 'q_has_top = 1', 'q_top' IS the reference's head (so it is canonical), and the 'n' words spilled
    below the pointer ARE the reference's tail, in the reference's order and canonical too.

  This is a relation between the emitted 'q_sp' register and the reference stack LENGTH, plus the two
  clauses the length alone cannot carry (which word is on top, and what is below it). Section 4 proves
  it preserved; section 5 proves its depth clause is what item 3's walk computes. -/
def QStackCorr {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (stk : List QVMFr) : Prop :=
  ∃ (n : Nat) (sp top : U256), QStackCorrWith (c := c) (g := g) program V st stk n sp top

/-- **THE DEPTH IS A FUNCTION OF THE REGISTERS**, not a wish. Without 'QStackNoWrap' this is FALSE -
    depths differing by '2 ^ 251' name the same word - which is the same model gap guard 1 closes for
    the cursor, on the stack side. -/
theorem QStackCorrWith.depth_unique {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {stk : List QVMFr} {n m : Nat} {sp sp' top top' : U256}
    (h1 : QStackCorrWith (c := c) (g := g) program V st stk n sp top)
    (h2 : QStackCorrWith (c := c) (g := g) program V st stk m sp' top') : n = m := by
  obtain ⟨hget, _, heq, hwrap, _⟩ := h1
  obtain ⟨hget', _, heq', hwrap', _⟩ := h2
  have hsp : sp = sp' := Option.some.inj (hget.symm.trans hget')
  rw [← hsp, heq] at heq'
  have := congrArg BitVec.toNat heq'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap, Nat.mod_eq_of_lt hwrap'] at this
  omega

/-- **ITEM 4 IS THE BASE CASE.** 'QPrologueStart' is D-QVM2's fourth item - the start state the
    prologue establishes, sitting in the contract's pre beside 'AtSegment' and 'Agrees'. This proves it
    satisfies 'QStackCorr' against the EMPTY reference stack, so the contract's fourth hypothesis is
    exactly the invariant at depth 0: the induction has somewhere to start and the caller supplies
    nothing new. The only extra fact is the program's own address fit, which 'ValidV3' already gives. -/
theorem qStackCorr_of_prologueStart {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hfit : quotientProgramFits program)
    (h : QPrologueStart (c := c) (g := g) program V) :
    QStackCorr (c := c) (g := g) program V st [] := by
  obtain ⟨x, hx⟩ := h.2.2
  refine ⟨0, BitVec.ofNat 256 program.stackMptr, x, h.1, hx, rfl,
    QStackNoWrap_zero_of_fits program hfit, Or.inl ⟨h.2.1, rfl, rfl⟩⟩

/-- **THE INVARIANT IS NOT VACUOUS: IT REFUTES A LYING CACHED-TOP FLAG.** A machine that says its
    cached top is live while the reference's stack is empty does NOT satisfy the correspondence - at
    any depth. This is the mismatch QFIX said no start-state hypothesis can catch ('QHeadNoPop' is a
    head test for the FIRST arm only), and it is why the flag is inside the invariant. -/
theorem stkinv_refutes_live_top_over_empty {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hflag : VEnv.get V "q_has_top" = some 1) :
    ¬ QStackCorr (c := c) (g := g) program V st [] := by
  rintro ⟨n, sp, top, hsp, htop, heq, hwrap, hcase⟩
  rcases hcase with ⟨h0, _, _⟩ | ⟨_, _, hshape, _⟩
  · exact absurd (h0.symm.trans hflag) (by decide : ¬((some (0 : U256) : Option U256) = some 1))
  · exact absurd hshape (by simp)

/-- And it refutes a pointer that lies about its depth: 'q_sp' one word above the base, an empty
    reference stack and a dead cached top is not a boundary state. -/
theorem stkinv_refutes_pointer_lies {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hsp : VEnv.get V "q_sp" = some (BitVec.ofNat 256 (program.stackMptr + 32)))
    (hflag : VEnv.get V "q_has_top" = some 0)
    (hfit : program.stackMptr + 64 < 2 ^ 256) :
    ¬ QStackCorr (c := c) (g := g) program V st [] := by
  rintro ⟨n, sp, top, hget, _, heq, hwrap, hcase⟩
  rcases hcase with ⟨h0, _, hn0⟩ | ⟨h0, _, _, _⟩
  · subst hn0
    have hlt : program.stackMptr + 32 < 2 ^ 256 := Nat.lt_of_le_of_lt (by omega) hfit
    have he : BitVec.ofNat 256 (program.stackMptr + 32) =
        BitVec.ofNat 256 (program.stackMptr + 32 * 0) :=
      (Option.some.inj (hsp.symm.trans hget)).trans heq
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hwrap] at this
    omega
  · exact absurd (h0.symm.trans hflag) (by decide : ¬((some (1 : U256) : Option U256) = some 0))

/-! ### 3. WHERE THE REFERENCE FAULTS -/
/-- The four shapes section 4 consumes. Each is COMPUTED from the reference's own definition - the
    'unfold' then 'simp (config := {decide := true})' pattern 'qStepValue_X' uses - so an arm's
    enabling condition is read off the reference rather than assumed beside it. -/

theorem stkinv_neg_empty (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest) consts 0 qOpNeg [] mem
      = .error (QVMFault.stackUnderflow 0) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

theorem stkinv_pow5_empty (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpPow5 :: rest) consts 0 qOpPow5 [] mem
      = .error (QVMFault.stackUnderflow 0) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

theorem stkinv_add_short (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (x : QVMFr) :
    Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest) consts 0 qOpAdd [x] mem
      = .error (QVMFault.stackUnderflow 0) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

theorem stkinv_add_empty (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest) consts 0 qOpAdd [] mem
      = .error (QVMFault.stackUnderflow 0) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

theorem stkinv_mul_empty (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityStep (qOpMul :: rest) consts 0 qOpMul [] mem
      = .error (QVMFault.stackUnderflow 0) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

theorem stkinv_mul_short (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (x : QVMFr) :
    Midfall.Generator.evalQuotientIdentityStep (qOpMul :: rest) consts 0 qOpMul [x] mem
      = .error (QVMFault.stackUnderflow 0) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := {decide := true})
  rfl

/-! ### 4. THE INDUCTIVE STEP, ARM BY ARM -/

/-- The pointer equation the popping arms need: one word below 'stackMptr + 32 * (k + 1)' IS
    'stackMptr + 32 * k' - PROVIDED the pointer does not wrap, which is why the wrap clause is inside
    the invariant and not beside it. -/
theorem stkinv_sub_word (m k : Nat) (h : m + 32 * (k + 1) < 2 ^ 256) :
    BitVec.ofNat 256 (m + 32 * (k + 1)) - BitVec.ofNat 256 32 = BitVec.ofNat 256 (m + 32 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlower : m + 32 * k < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 32 (Nat.le_add_right k 1)) m) h
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hlower]
  have key : 2 ^ 256 - 32 + (m + 32 * (k + 1)) = 2 ^ 256 + (m + 32 * k) := by omega
  rw [key, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hlower

/-- **THE INDUCTION, NEG ARM.** The machine satisfies the correspondence, the reference's own step at
    'qOpNeg' succeeds, and the EMITTED neg arm runs to 'V'', 'st''. Then the correspondence holds again
    against the reference's NEW stack. Nothing about the arm is re-derived here: the proof consumes
    'qArmValueAll_neg' (the arm's every-run contract, QuotientFrame.lean:935) and 'rtie_neg' (RTIE's tie
    between the reference step and the arm's own word 'wAddmod 0 (wSubFr x)', QuotientFrame.lean:2297).
    The cached top is replaced by the arm's word and the pointer does not move: one-in-one-out. -/
theorem qStackCorr_neg {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyNeg ctx program tcq) V' st' o)
    (hr : VEnv.get V "r" = some frModulusWord)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest) consts 0 qOpNeg stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, sp, top, hsp, htop, heq, hwrap, hcase⟩ := hcorr
  have hne : stk ≠ [] := by
    intro t
    rcases hcase with ⟨_, hnil, _⟩ | ⟨_, _, hshape, _⟩
    · rw [hnil] at hstep
      rw [stkinv_neg_empty rest consts mem] at hstep
      exact absurd hstep (by simp)
    · exact absurd (hshape.symm.trans t) (by simp)
  obtain ⟨h1, hcan, hshape, hspill⟩ :=
    (or_iff_right (fun h : _ ∧ stk = [] ∧ _ => hne h.2.1)).mp hcase
  rw [hshape] at hstep
  have h2 := rtie_neg rest consts ((qSpilled st n sp).map BitVec.toNat) top hcan mem
  rw [h2] at hstep
  obtain rfl := Except.ok.inj hstep
  have hcontract :=
    qArmValueAll_neg hc hg ctx program tcq funs top hcan V st ⟨htop, hr⟩ V' st' o hrun
  obtain ⟨hnormal, hst', hV'⟩ := hcontract
  subst hnormal
  set wtop : U256 := BitVec.ofNat 256 (qvmFrNeg top.toNat) with hwtop
  have hcan' : wtop.toNat < qvmFrModulus := by
    rw [hwtop, rtie_ofNat_toNat _ (rtie_qvmFrNeg_lt _)]
    exact rtie_qvmFrNeg_lt _
  have hhead : (wAddmod 0 (wSubFr top)).toNat = wtop.toNat := by
    rw [hwtop, wAddmod_eq_qvmFrNeg top hcan, rtie_ofNat_toNat _ (rtie_qvmFrNeg_lt _)]
  refine ⟨rfl, ⟨n, sp, wtop, ?_, ?_, heq, hwrap, Or.inr ⟨?_, hcan', ?_, ?_⟩⟩⟩
  · rw [hV']; exact venvGet_set_ne V "q_top" "q_sp" _ sp (by decide : ("q_top" : Ident) ≠ "q_sp") hsp
  · rw [hV']; exact venvGet_set_same V "q_top" _ _ htop
  · rw [hV']
    exact venvGet_set_ne V "q_top" "q_has_top" _ 1 (by decide : ("q_top" : Ident) ≠ "q_has_top") h1
  · rw [hst']
    exact congrArg (fun x : QVMFr => x :: List.map BitVec.toNat (qSpilled st n sp)) hhead
  · intro w hw
    rw [hst'] at hw
    exact hspill w hw

/-- **THE INDUCTION, POW5 ARM.** The twin of the NEG step at the other one-in-one-out arm whose only
    operand is the cached top. 'qArmValueAll_pow5' leaves a LOCAL ('q2') on top of the environment, so
    the pointer and the flag are transported by 'venvGet_cons_ne' as well as 'venvGet_set_ne': the cons
    is real and the proof says so rather than pretending the post is 'VEnv.set V "q_top" w'. The head
    equality is 'rtie_pow5', the one tie that is not a 'rfl' because the two bracketings differ. -/
theorem qStackCorr_pow5 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPow5 ctx program tcq) V' st' o)
    (hr : VEnv.get V "r" = some frModulusWord)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPow5 :: rest) consts 0 qOpPow5 stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, sp, top, hsp, htop, heq, hwrap, hcase⟩ := hcorr
  have hne : stk ≠ [] := by
    intro t
    rcases hcase with ⟨_, hnil, _⟩ | ⟨_, _, hshape, _⟩
    · rw [hnil] at hstep
      rw [stkinv_pow5_empty rest consts mem] at hstep
      exact absurd hstep (by simp)
    · exact absurd (hshape.symm.trans t) (by simp)
  obtain ⟨h1, hcan, hshape, hspill⟩ :=
    (or_iff_right (fun h : _ ∧ stk = [] ∧ _ => hne h.2.1)).mp hcase
  rw [hshape] at hstep
  have h2 := rtie_pow5 rest consts ((qSpilled st n sp).map BitVec.toNat) top mem
  rw [h2] at hstep
  obtain rfl := Except.ok.inj hstep
  have hcontract := qArmValueAll_pow5 hc hg ctx program tcq funs top V st ⟨htop, hr⟩ V' st' o hrun
  obtain ⟨hnormal, hst', hV'⟩ := hcontract
  subst hnormal
  set w5 : U256 := BitVec.ofNat 256
    (qvmFrMul (qvmFrMul top.toNat (qvmFrMul top.toNat top.toNat)) (qvmFrMul top.toNat top.toNat)
      : QVMFr) with hw5
  have hcan' : w5.toNat < qvmFrModulus := by
    rw [hw5, rtie_ofNat_toNat _ (rtie_qvmFrMul_lt _ _)]
    exact rtie_qvmFrMul_lt _ _
  have hhead : (wMulmod top (wMulmod (wMulmod top top) (wMulmod top top))).toNat = w5.toNat := by
    rw [hw5, wMulmod_eq_qvmFrPow5, rtie_ofNat_toNat _ (rtie_qvmFrMul_lt _ _)]
  refine ⟨rfl, ⟨n, sp, w5, ?_, ?_, heq, hwrap, Or.inr ⟨?_, hcan', ?_, ?_⟩⟩⟩
  · rw [hV', hw5]
    exact (venvGet_cons_ne (VEnv.set V "q_top" w5) "q2" "q_sp" _
        (by decide : ("q2" : Ident) ≠ "q_sp")).trans
      (venvGet_set_ne V "q_top" "q_sp" _ sp (by decide : ("q_top" : Ident) ≠ "q_sp") hsp)
  · rw [hV', hw5]; exact venvGet_set_same V "q_top" _ _ htop
  · rw [hV', hw5]
    exact (venvGet_cons_ne (VEnv.set V "q_top" w5) "q2" "q_has_top" _
        (by decide : ("q2" : Ident) ≠ "q_has_top")).trans
      (venvGet_set_ne V "q_top" "q_has_top" _ 1 (by decide : ("q_top" : Ident) ≠ "q_has_top") h1)
  · rw [hst', hhead]
  · intro w hw
    rw [hst'] at hw
    exact hspill w hw


/-- **THE INDUCTION, ADD ARM - THE ONE THAT EXERCISES MEMORY.** Unlike NEG and POW5 this arm pops the
    cached top AND a spilled word, so the step is only true because the invariant carries the spilled
    tail: the reference's second operand is the head of its tail, which by the invariant is the word at
    'sp - 32', which is exactly what the emitted arm 'mload's. The pointer drops one word and the depth
    with it. And 'n ≥ 1' is FORCED by the reference's own second 'popStack' - the arm is not given it,
    it is derived, which is the difference between an invariant and a wish. -/
theorem qStackCorr_add {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAdd ctx program tcq) V' st' o)
    (hr : VEnv.get V "r" = some frModulusWord)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest) consts 0 qOpAdd stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, sp, top, hsp, htop, heq, hwrap, hcase⟩ := hcorr
  have hne : stk ≠ [] := by
    intro t
    rcases hcase with ⟨_, hnil, _⟩ | ⟨_, _, hshape, _⟩
    · rw [hnil] at hstep
      rw [stkinv_add_empty rest consts mem] at hstep
      exact absurd hstep (by simp)
    · exact absurd (hshape.symm.trans t) (by simp)
  obtain ⟨h1, hcan, hshape, hspill⟩ :=
    (or_iff_right (fun h : _ ∧ stk = [] ∧ _ => hne h.2.1)).mp hcase
  -- the reference pops twice, so the spilled tail is non-empty: n = k + 1
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    have hsh : stk = [top.toNat] := by rw [hshape]; rfl
    rw [hsh] at hstep
    rw [stkinv_add_short rest consts mem top.toNat] at hstep
    exact absurd hstep (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hshape, qSpilled_succ, List.map_cons] at hstep
  set yword : U256 := loadWord st.memory (sp - BitVec.ofNat 256 32).toNat with hyword
  set tail : List QVMFr := (qSpilled st k (sp - BitVec.ofNat 256 32)).map BitVec.toNat with htail
  have hstep2 : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest) consts 0 qOpAdd
      (top.toNat :: yword.toNat :: tail) mem = .ok s := hstep
  have h2 := rtie_add rest consts tail top yword mem
  rw [h2] at hstep2
  obtain rfl := Except.ok.inj hstep2
  have hsp_ne : sp ≠ BitVec.ofNat 256 program.stackMptr := by
    rw [heq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap] at this
    have hle : program.stackMptr + 32 * (k + 1) ≤ program.stackMptr := by
      rw [this]; exact Nat.mod_le _ _
    have : 32 * (k + 1) ≤ 0 := Nat.le_of_add_le_add_left hle
    omega
  have hcontract :=
    qArmValueAll_add hc hg ctx program tcq funs sp top yword hsp_ne V st
      ⟨hsp, htop, hr, hyword.symm⟩ V' st' o hrun
  obtain ⟨hnormal, hst', hV'⟩ := hcontract
  subst hnormal
  set wa : U256 := BitVec.ofNat 256 (qvmFrAdd yword.toNat top.toNat : QVMFr) with hwa
  have hwrap' : QStackNoWrap program k := hwrap.pre
  have hcan' : wa.toNat < qvmFrModulus := by
    rw [hwa, rtie_ofNat_toNat _ (rtie_qvmFrAdd_lt _ _)]
    exact rtie_qvmFrAdd_lt _ _
  have hhead : (wAddmod yword top).toNat = wa.toNat := by
    rw [hwa, wAddmod_eq_qvmFrAdd, rtie_ofNat_toNat _ (rtie_qvmFrAdd_lt _ _)]
  refine ⟨rfl, ⟨k, sp - BitVec.ofNat 256 32, wa, ?_, ?_, ?_, hwrap',
    Or.inr ⟨?_, hcan', ?_, ?_⟩⟩⟩
  · rw [hV', hwa]
    exact venvGet_set_ne (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" "q_sp" _ _
      (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same V "q_sp" _ _ hsp)
  · rw [hV', hwa]
    exact venvGet_set_same (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" _ _
      (venvGet_set_ne V "q_sp" "q_top" (sp - BitVec.ofNat 256 32) top
        (by decide : ("q_sp" : Ident) ≠ "q_top") htop)
  · rw [heq]; exact stkinv_sub_word program.stackMptr k hwrap
  · rw [hV', hwa]
    exact venvGet_set_ne (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" "q_has_top" _ 1
      (by decide : ("q_top" : Ident) ≠ "q_has_top")
      (venvGet_set_ne V "q_sp" "q_has_top" _ 1 (by decide : ("q_sp" : Ident) ≠ "q_has_top") h1)
  · show (wAddmod yword top).toNat :: tail =
        wa.toNat :: (qSpilled st' k (sp - BitVec.ofNat 256 32)).map BitVec.toNat
    rw [hhead, htail, hst', qSpilled_touchMemory]
  · intro w hw
    rw [hst', qSpilled_touchMemory] at hw
    exact hspill w (by rw [qSpilled_succ]; exact List.Mem.tail _ hw)


/-- **THE INDUCTION, ADD ARM - THE ONE THAT EXERCISES MEMORY.** Unlike NEG and POW5 this arm pops the
    cached top AND a spilled word, so the step is only true because the invariant carries the spilled
    tail: the reference's second operand is the head of its tail, which by the invariant is the word at
    'sp - 32', which is exactly what the emitted arm 'mload's. The pointer drops one word and the depth
    with it. And 'n ≥ 1' is FORCED by the reference's own second 'popStack' - the arm is not given it,
    it is derived, which is the difference between an invariant and a wish. -/
theorem qStackCorr_mul {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyMul ctx program tcq) V' st' o)
    (hr : VEnv.get V "r" = some frModulusWord)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpMul :: rest) consts 0 qOpMul stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, sp, top, hsp, htop, heq, hwrap, hcase⟩ := hcorr
  have hne : stk ≠ [] := by
    intro t
    rcases hcase with ⟨_, hnil, _⟩ | ⟨_, _, hshape, _⟩
    · rw [hnil] at hstep
      rw [stkinv_mul_empty rest consts mem] at hstep
      exact absurd hstep (by simp)
    · exact absurd (hshape.symm.trans t) (by simp)
  obtain ⟨h1, hcan, hshape, hspill⟩ :=
    (or_iff_right (fun h : _ ∧ stk = [] ∧ _ => hne h.2.1)).mp hcase
  -- the reference pops twice, so the spilled tail is non-empty: n = k + 1
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    have hsh : stk = [top.toNat] := by rw [hshape]; rfl
    rw [hsh] at hstep
    rw [stkinv_mul_short rest consts mem top.toNat] at hstep
    exact absurd hstep (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hshape, qSpilled_succ, List.map_cons] at hstep
  set yword : U256 := loadWord st.memory (sp - BitVec.ofNat 256 32).toNat with hyword
  set tail : List QVMFr := (qSpilled st k (sp - BitVec.ofNat 256 32)).map BitVec.toNat with htail
  have hstep2 : Midfall.Generator.evalQuotientIdentityStep (qOpMul :: rest) consts 0 qOpMul
      (top.toNat :: yword.toNat :: tail) mem = .ok s := hstep
  have h2 := rtie_mul rest consts tail top yword mem
  rw [h2] at hstep2
  obtain rfl := Except.ok.inj hstep2
  have hsp_ne : sp ≠ BitVec.ofNat 256 program.stackMptr := by
    rw [heq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap] at this
    have hle : program.stackMptr + 32 * (k + 1) ≤ program.stackMptr := by
      rw [this]; exact Nat.mod_le _ _
    have : 32 * (k + 1) ≤ 0 := Nat.le_of_add_le_add_left hle
    omega
  have hcontract :=
    qArmValueAll_mul hc hg ctx program tcq funs sp top yword hsp_ne V st
      ⟨hsp, htop, hr, hyword.symm⟩ V' st' o hrun
  obtain ⟨hnormal, hst', hV'⟩ := hcontract
  subst hnormal
  set wa : U256 := BitVec.ofNat 256 (qvmFrMul yword.toNat top.toNat : QVMFr) with hwa
  have hwrap' : QStackNoWrap program k := hwrap.pre
  have hcan' : wa.toNat < qvmFrModulus := by
    rw [hwa, rtie_ofNat_toNat _ (rtie_qvmFrMul_lt _ _)]
    exact rtie_qvmFrMul_lt _ _
  have hhead : (wMulmod yword top).toNat = wa.toNat := by
    rw [hwa, wMulmod_eq_qvmFrMul, rtie_ofNat_toNat _ (rtie_qvmFrMul_lt _ _)]
  refine ⟨rfl, ⟨k, sp - BitVec.ofNat 256 32, wa, ?_, ?_, ?_, hwrap',
    Or.inr ⟨?_, hcan', ?_, ?_⟩⟩⟩
  · rw [hV', hwa]
    exact venvGet_set_ne (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" "q_sp" _ _
      (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same V "q_sp" _ _ hsp)
  · rw [hV', hwa]
    exact venvGet_set_same (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" _ _
      (venvGet_set_ne V "q_sp" "q_top" (sp - BitVec.ofNat 256 32) top
        (by decide : ("q_sp" : Ident) ≠ "q_top") htop)
  · rw [heq]; exact stkinv_sub_word program.stackMptr k hwrap
  · rw [hV', hwa]
    exact venvGet_set_ne (VEnv.set V "q_sp" (sp - BitVec.ofNat 256 32)) "q_top" "q_has_top" _ 1
      (by decide : ("q_top" : Ident) ≠ "q_has_top")
      (venvGet_set_ne V "q_sp" "q_has_top" _ 1 (by decide : ("q_sp" : Ident) ≠ "q_has_top") h1)
  · show (wMulmod yword top).toNat :: tail =
        wa.toNat :: (qSpilled st' k (sp - BitVec.ofNat 256 32)).map BitVec.toNat
    rw [hhead, htail, hst', qSpilled_touchMemory]
  · intro w hw
    rw [hst', qSpilled_touchMemory] at hw
    exact hspill w (by rw [qSpilled_succ]; exact List.Mem.tail _ hw)



/-- **THE INDUCTION CHAINS - THE POINT OF THE CARD.** Two arm steps compose: the second consumes
    exactly what the first produced. A per-arm tie cannot do this - RTIE's 19 equations each stand alone
    at the prologue state - and this theorem is the smallest witness that the correspondence is a LOOP
    invariant and not 19 one-step facts. NEG then ADD: depth 2 → 2 → 1, with the pointer moving once.
    The field-modulus register 'r' is carried as a separate hypothesis at each boundary: it is a FRAME
    fact, not a stack fact, and this card deliberately does not fold frame facts into the stack
    invariant - that is what 'Agrees' is for, and RTIE left the memory bridge open on purpose. -/
theorem qStackCorr_neg_then_add {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V₁ V₂ : VEnv (Bridge.Dialect c g)) (st st₁ st₂ : EvmState) (o₁ o₂ : Outcome)
    (rest₁ rest₂ : List Nat) (consts : List Word256) (mem₁ mem₂ : QuotientRefMemory)
    (stk : List QVMFr) (s₁ : IdentityStep) (s₂ : IdentityStep)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hr : VEnv.get V "r" = some frModulusWord)
    (hr₁ : VEnv.get V₁ "r" = some frModulusWord)
    (hstep₁ : Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest₁) consts 0 qOpNeg stk mem₁ = .ok s₁)
    (hrun₁ : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyNeg ctx program tcq) V₁ st₁ o₁)
    (hstep₂ : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest₂) consts 0 qOpAdd s₁.stack mem₂ = .ok s₂)
    (hrun₂ : ExecStmts (Bridge.Dialect c g) funs V₁ st₁ (GenAst.qArmBodyAdd ctx program tcq) V₂ st₂ o₂) :
    o₁ = .normal ∧ o₂ = .normal ∧ QStackCorr (c := c) (g := g) program V₂ st₂ s₂.stack := by
  obtain ⟨hnormal₁, hcorr₁⟩ :=
    qStackCorr_neg hc hg ctx program tcq funs V V₁ st st₁ o₁ rest₁ consts mem₁ stk s₁ hrun₁ hr hcorr hstep₁
  obtain ⟨hnormal₂, hcorr₂⟩ :=
    qStackCorr_add hc hg ctx program tcq funs V₁ V₂ st₁ st₂ o₂ rest₂ consts mem₂ s₁.stack s₂ hrun₂ hr₁
      hcorr₁ hstep₂
  exact ⟨hnormal₁, hnormal₂, hcorr₂⟩

/-! ### 5. THE CERTIFICATE GENERALISED, AND THE BRIDGE TO IT -/

/-- **ITEM 3, GENERALISED TO AN ARBITRARY BOUNDARY.** 'QSegmentStackSafe' is the walk from depth 0 that
    must end at depth 1. This is the same walk from depth 'd0' ending at depth 'd1' - the form an
    induction needs, because an arm boundary sits at an arbitrary depth, not at 0. -/
def QSegmentStackSafeFrom (bytes : List Nat) (s : QSegment) (d0 d1 : Nat) : Prop :=
  qSegmentDepthGo (qSegmentBytes bytes s) (qSegmentBytes bytes s).length 0 d0 = some d1

/-- **THE GENERALISATION IS CONSERVATIVE.** Item 3 IS the (0,1) instance: the equivalence is 'rfl', so
    nothing 'QInterpRefinesSegment' assumes changes and nothing here restates it. -/
theorem QSegmentStackSafe_iff_from (bytes : List Nat) (s : QSegment) :
    QSegmentStackSafe bytes s ↔ QSegmentStackSafeFrom bytes s 0 1 := Iff.rfl

/-- The walk's own induction step, spelled as an equation: one certified instruction at depth 'd' IS the
    walk from the effect's depth 'd''. 'QSegmentStackSafe' uses this implicitly by COMPUTING; the loop
    needs it stated, because it is the half-step the invariant's depth has to track. -/
theorem qSegmentDepthGo_step (bytes : List Nat) (fuel idx depth op len depth' m : Nat)
    (hidx : idx < bytes.length)
    (hdec : Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes idx = .ok (op, len))
    (hstream : op ∉ qSegmentStreamOpcodes)
    (heff : Midfall.Generator.QuotientValidator.applyQuotientStackEffect op idx depth 0
      = .ok (depth', m)) :
    qSegmentDepthGo bytes (fuel + 1) idx depth = qSegmentDepthGo bytes fuel (idx + len) depth' := by
  simp only [qSegmentDepthGo, hidx, hdec, heff, hstream]
  exact rfl

/-- Past the end of the bytes the walk is the identity on the depth: the base case of any induction over
    it, and the reason 'fuel = bytes.length' is sound (the R10 note item 3 records). -/
theorem qSegmentDepthGo_pastEnd (bytes : List Nat) (fuel idx depth : Nat) (h : bytes.length ≤ idx) :
    qSegmentDepthGo bytes (fuel + 1) idx depth = some depth :=
  ite_eq_right (Nat.not_lt.mpr h)

/-- **THE BRIDGE, NEG.** Whenever the reference's own step at 'qOpNeg' succeeds, the validator's static
    effect applied to the CURRENT STACK LENGTH returns exactly the reference's NEW length. So the
    certificate's depth and the invariant's depth are the same number at the next boundary - which is
    the sense in which item 3 is the fold of this invariant, and why no parallel stack definition was
    needed. -/
theorem qStackShape_neg (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stack : List QVMFr) (s : IdentityStep)
    (h : Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest) consts 0 qOpNeg stack mem = .ok s) :
    Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpNeg 0 stack.length 0
      = .ok (s.stack.length, 0) := by
  cases stack with
  | nil =>
      rw [stkinv_neg_empty rest consts mem] at h
      exact absurd h (by simp)
  | cons v t =>
      have hshape := qStepValue_neg rest consts t v mem
      rw [hshape] at h
      obtain rfl := Except.ok.inj h
      unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
      simp (config := {decide := true})
      rfl

/-- **THE BRIDGE, POW5.** -/
theorem qStackShape_pow5 (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stack : List QVMFr) (s : IdentityStep)
    (h : Midfall.Generator.evalQuotientIdentityStep (qOpPow5 :: rest) consts 0 qOpPow5 stack mem = .ok s) :
    Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpPow5 0 stack.length 0
      = .ok (s.stack.length, 0) := by
  cases stack with
  | nil =>
      rw [stkinv_pow5_empty rest consts mem] at h
      exact absurd h (by simp)
  | cons v t =>
      have hshape := qStepValue_pow5 rest consts t v mem
      rw [hshape] at h
      obtain rfl := Except.ok.inj h
      unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
      simp (config := {decide := true})
      rfl

/-- **THE BRIDGE, ADD** - the two-pop case: the effect requires depth 2 and returns length − 1, and it
    is the reference's step SUCCEEDING that makes the depth large enough. The certificate and the
    reference refuse the same boundary state, from opposite ends. -/
theorem qStackShape_add (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stack : List QVMFr) (s : IdentityStep)
    (h : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest) consts 0 qOpAdd stack mem = .ok s) :
    ∃ m, Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpAdd 0 stack.length 0
      = .ok (s.stack.length, m) := by
  cases stack with
  | nil =>
      rw [stkinv_add_empty rest consts mem] at h
      exact absurd h (by simp)
  | cons v t =>
      cases t with
      | nil =>
          rw [stkinv_add_short rest consts mem v] at h
          exact absurd h (by simp)
      | cons w u =>
          have hshape := qStepValue_add rest consts u v w mem
          rw [hshape] at h
          obtain rfl := Except.ok.inj h
          unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
          simp (config := {decide := true})
          exact ⟨0, rfl⟩

/-- **THE BRIDGE, MUL.** -/
theorem qStackShape_mul (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stack : List QVMFr) (s : IdentityStep)
    (h : Midfall.Generator.evalQuotientIdentityStep (qOpMul :: rest) consts 0 qOpMul stack mem = .ok s) :
    ∃ m, Midfall.Generator.QuotientValidator.applyQuotientStackEffect qOpMul 0 stack.length 0
      = .ok (s.stack.length, m) := by
  cases stack with
  | nil =>
      rw [stkinv_mul_empty rest consts mem] at h
      exact absurd h (by simp)
  | cons v t =>
      cases t with
      | nil =>
          rw [stkinv_mul_short rest consts mem v] at h
          exact absurd h (by simp)
      | cons w u =>
          have hshape := qStepValue_mul rest consts u v w mem
          rw [hshape] at h
          obtain rfl := Except.ok.inj h
          unfold Midfall.Generator.QuotientValidator.applyQuotientStackEffect
          simp (config := {decide := true})
          exact ⟨0, rfl⟩

/-! ### 6. WHAT REMAINS, NAMED -/

/-- **PG_SPILLARM - THE PUSH FAMILY'S INDUCTIVE STEP IS BLOCKED HERE, AND NOT IN THIS FILE.** Every
    published push-arm contract pins 'q_has_top = some 0' in its PRE: 'qArmValueAll_pushConst'
    ('QuotientArms.lean:3079-3088') asks for the EMPTY cached top, i.e. it describes the arm's no-spill
    branch. An inductive boundary is the other branch - the cached top is live, the arm spills it to
    'q_sp', advances the pointer by one word and installs the new value. The emitted arm HAS that branch
    ('GenAstQvm.lean:138': 'yif q_has_top [guard stackLast, mstore q_sp q_top, q_sp += 32]'), so this is
    a missing PROOF about the arm, not a missing hypothesis about the state, and it belongs to the arm
    layer (QARMS' file), which this card does not own. The exact goal state, for the head arm: the arm's
    every-run contract at a LIVE cached top, post including the spill landing where the next arm's popped
    operand will be read - which is precisely the clause 'QStackCorr' needs to step across a push. -/
def PG_spillArmTriple {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (pc cb sp top : U256) (b v : Nat) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushConst ctx program tcq)
    (fun V st => VEnv.get V "q_pc" = some pc ∧
      VEnv.get V "q_sp" = some sp ∧
      VEnv.get V "q_has_top" = some 1 ∧
      VEnv.get V "q_top" = some top ∧
      VEnv.get V "q_const_mptr" = some cb ∧
      ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
      loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v ∧
      ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (fun _ _ V' st' o => o = .normal ∧
      VEnv.get V' "q_sp" = some (sp + BitVec.ofNat 256 32) ∧
      VEnv.get V' "q_has_top" = some 1 ∧
      VEnv.get V' "q_top" = some (BitVec.ofNat 256 v) ∧
      loadWord st'.memory sp.toNat = top)

/-- **PG_STACKWALKCURSOR - THE ITERATION IS BLOCKED ON THE CURSOR, NOT ON THE DEPTH.** Section 5 proves
    the per-arm bridge: the validator's effect on the current length gives the reference's new length.
    Folding that over a segment needs the two walks to stand at the SAME OFFSET at every boundary, i.e.
    the decoded width must equal the reference's own 'consumed' field - QFIX's (O4), untouched by this
    card and by LOOPPRE. Stated for one boundary, at the reference's own index: -/
def PG_stackWalkCursor (bytes : List Nat) (consts : List Word256) (idx op len : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) (s : IdentityStep) : Prop :=
    Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes idx = .ok (op, len) →
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem = .ok s →
    len = s.consumed

/-- **THE WRAP CLAUSE IS NOT A FIFTH CALLER OBLIGATION, AND THAT IS WORTH SAYING.** 'QStackCorr' carries
    'QStackNoWrap program n', which looks like a fifth item for the caller of
    'QInterpRefinesSegment'. It is not: 'quotientProgramFits' supplies 'n = 0'
    ('QStackNoWrap_zero_of_fits') and the machine's own spill guard bounds every later depth. No
    hypothesis was added to a row, to 'ValidV3', to a bundle or to the root (RULES), and
    'Obligations.lean' was not touched, so the two props above are named and reported, not registered. -/
theorem QStackNoWrap_of_fits_zero :
    ∀ (program : QuotientProgram), quotientProgramFits program → QStackNoWrap program 0 :=
  QStackNoWrap_zero_of_fits

/-! ### 7. ACCEPTANCE PRINTS -/

#print axioms Midfall.Lowering.QuotientStackInv.qSpilled_length
#print axioms Midfall.Lowering.QuotientStackInv.qStackCorr_of_prologueStart
#print axioms Midfall.Lowering.QuotientStackInv.QStackCorrWith.depth_unique
#print axioms Midfall.Lowering.QuotientStackInv.stkinv_refutes_live_top_over_empty
#print axioms Midfall.Lowering.QuotientStackInv.stkinv_refutes_pointer_lies
#print axioms Midfall.Lowering.QuotientStackInv.qStackCorr_neg
#print axioms Midfall.Lowering.QuotientStackInv.qStackCorr_pow5
#print axioms Midfall.Lowering.QuotientStackInv.qStackCorr_add
#print axioms Midfall.Lowering.QuotientStackInv.qStackCorr_mul
#print axioms Midfall.Lowering.QuotientStackInv.qStackCorr_neg_then_add
#print axioms Midfall.Lowering.QuotientStackInv.QSegmentStackSafe_iff_from
#print axioms Midfall.Lowering.QuotientStackInv.qSegmentDepthGo_step
#print axioms Midfall.Lowering.QuotientStackInv.qStackShape_neg
#print axioms Midfall.Lowering.QuotientStackInv.qStackShape_add

#cone_sorries Midfall.Lowering.QuotientStackInv.qStackCorr_neg
#cone_sorries Midfall.Lowering.QuotientStackInv.qStackCorr_pow5
#cone_sorries Midfall.Lowering.QuotientStackInv.qStackCorr_add
#cone_sorries Midfall.Lowering.QuotientStackInv.qStackCorr_mul
#cone_sorries Midfall.Lowering.QuotientStackInv.qStackCorr_neg_then_add
#cone_sorries Midfall.Lowering.QuotientStackInv.qStackCorr_of_prologueStart
#cone_sorries Midfall.Lowering.QuotientStackInv.qSegmentDepthGo_step
#cone_sorries Midfall.Lowering.QuotientStackInv.QSegmentStackSafe_iff_from

#assert_axioms Midfall.Lowering.QuotientStackInv.qStackCorr_neg [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qStackCorr_pow5 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qStackCorr_add [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qStackCorr_mul [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qStackCorr_of_prologueStart [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qStackCorr_neg_then_add [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qSegmentDepthGo_step [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.qStackShape_neg [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientStackInv.QStackCorrWith.depth_unique [propext, Classical.choice, Quot.sound] native []

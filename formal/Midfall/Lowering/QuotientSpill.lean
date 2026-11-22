-- |
-- Midfall.Lowering.QuotientSpill
--
-- SPILL: THE SPILL-BRANCH ARM CONTRACTS THAT 'QuotientStackInv' NAMED AND COULD NOT USE.
--
-- WHY THIS FILE EXISTS. 'QStackCorr' ('QuotientStackInv.lean:169') is an inductive invariant over ARM
-- BOUNDARIES, and at a boundary the emitted machine's cached top is LIVE whenever the reference's stack
-- is non-empty. Every published arm triple pins 'q_has_top = some 0' in its PRE - the NO-SPILL branch -
-- so the four push arms could not step across their own spill. STKINV named the gap 'PG_spillArmTriple'
-- and left it to the arm layer. This file is the arm layer discharging it: the spill branch of each push
-- arm, with the spilled word readable at the OLD pointer, which is exactly where the next arm's popped
-- operand will be read.
--
-- HOW IT IS BUILT, AND WHY THAT IS CHEAP. The spill is THE SAME THREE STATEMENTS in every push arm
-- ('GenAstQvm.lean:138' and the four bodies after it), so it is proved ONCE - 'qSpill_run' - and
-- composed with each arm's own prefix and tail by 'qExec_append'. Each arm's prefix lemma reuses the
-- generated no-spill proof's own 'have' lines verbatim, changed only in the one place STKINV identified:
-- the cached-top flag they transport is 'some 1' instead of 'some 0'. Nothing about an arm is
-- re-derived, and 'QuotientArms.lean' and 'QuotientFrame.lean' are not edited at all, so no cone-walk
-- file rebuilds.
--
-- WHAT IS NOT CLAIMED. (i) The four LIMB arms (LIN7, BILIN7_ROW, BILIN7_PAIRWISE, MODARITH7) are
-- EXCLUDED, exactly as IDSEG and STKINV excluded them: they sit behind 'PG_limbCountAgrees'
-- ('QuotientArms.lean:4425'), an OPEN HUMAN DECISION, and a spill contract for them would assume what
-- that decision is about. (ii) The two TOKEN arms (PUSH_MEM_TOKEN, PUSH_MEM_TOKEN_OFFSET) are not
-- landed: their prefix is a nine-way 'Stmt.switch' over 'program.memUsage' and their spill contract
-- needs that whole derivation again - the block route here applies to them unchanged, it just costs a
-- second prefix each. (iii) 'PG_spillArmTriple' AS PUBLISHED IS NOT PROVABLE, and section 6 says why
-- and lands the corrected contract instead. No hypothesis was added to a row, to 'ValidV3', to a bundle
-- or to the root (RULES); 'Obligations.lean' is untouched, so the two props section 6 names are
-- reported, not registered. No frozen file, no v1, no 'native_decide', no sorry.
--
import Midfall.Lowering.QuotientStackInv
import Midfall.LoweringV3.QuotientArms
import Midfall.LoweringV3.MemoryPairs

set_option autoImplicit false

namespace Midfall.Lowering.QuotientSpill
open YulSemantics YulSemantics.EVM Midfall Midfall.Generator Midfall.Lowering
open Midfall.Yul Midfall.Yul.Bridge Midfall.Lowering.QuotientInterp
open Midfall.Lowering.GenAst
open Midfall.Yul.WpX
open Midfall.LoweringV3
open Midfall.LoweringV3.QuotientFrame
open Midfall.LoweringV3.QuotientArms
open Midfall.Lowering.QuotientStackInv

/-! ### 1. THE SPILL BLOCK, PROVED ONCE -/

/-- The three statements a push arm runs when the cached top is live: refuse if the pointer has no room,
    write the cached word AT the pointer, advance the pointer by one word. Verbatim the emitted
    'yif q_has_top [...]' of 'GenAstQvm.lean:138', shared by all six push arms. -/
def qSpillBody (program : QuotientProgram) : Block Op :=
  [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)])
      [(yexpr (ycall "q_program_fail" []))]),
   (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])),
   (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]

/-- The whole spill statement, cached-top guard included: the arm-body element every push arm shares. -/
def qSpillStmt (program : QuotientProgram) : Stmt Op :=
  yif (yvar "q_has_top") (qSpillBody program)

/-- The state one spill leaves: the cached word written at the OLD pointer. The pointer register moves
    with it, but memory's only change is this write - which is what makes the spilled word readable. -/
def qSpillState (st : EvmState) (sp top : U256) : EvmState :=
  { touchMemory st sp.toNat 32 with memory := storeWord st.memory sp.toNat top }

/-- The spilled word reads back at the old pointer, whatever the arm's later 'mload's touched:
    'touchMemory' leaves the memory function alone. THE clause 'PG_spillArmTriple' asks for. -/
theorem qSpillState_loadWord_same (st : EvmState) (sp top : U256) :
    loadWord (qSpillState st sp top).memory sp.toNat = top :=
  Midfall.Yul.Word.loadWord_storeWord_same st.memory sp.toNat top

/-- And a word whose whole 32-byte window lies BELOW the old pointer is untouched by the spill. This is
    what lets the invariant's already-spilled tail survive a further spill. -/
theorem qSpillState_loadWord_below (st : EvmState) (sp top a : U256)
    (h : a.toNat + 32 <= sp.toNat \/ sp.toNat + 32 <= a.toNat) :
    loadWord (qSpillState st sp top).memory a.toNat = loadWord st.memory a.toNat :=
  Midfall.Yul.Word.loadWord_storeWord_disjoint st.memory sp.toNat a.toNat top h

/-- Forward sequencing over append: a block that runs its first slice normally and then its second slice
    runs the whole thing. 'Step.stmts_append_inv' ('Contracts.lean:115') is the inversion; a spill
    contract needs this direction, and nothing in the tree had it. -/
theorem qExec_append {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    {V Vm V' : VEnv (Bridge.Dialect c g)} {st stm st' : EvmState}
    {ss1 ss2 : Block Op} {o : Outcome}
    (h1 : ExecStmts (Bridge.Dialect c g) funs V st ss1 Vm stm .normal)
    (h2 : ExecStmts (Bridge.Dialect c g) funs Vm stm ss2 V' st' o) :
    ExecStmts (Bridge.Dialect c g) funs V st (ss1 ++ ss2) V' st' o := by
  revert h1 h2
  induction ss1 generalizing V st Vm stm with
  | nil =>
      intro h1 h2
      cases h1 with
      | seqNil => exact h2
  | cons s rest ih =>
      intro h1 h2
      cases h1 with
      | seqCons hs hrest => exact Step.seqCons (D := Bridge.Dialect c g) hs (ih hrest h2)
      | seqStop _ hne => exact absurd rfl hne

/-- **THE SPILL BLOCK RUNS.** Guard passes, the cached word is written at the pointer, the pointer moves
    up one word, and the flag stays live. One proof, six arms. The block's own 'Step.block' scope is
    'qSpillFuns'; the 'restore' it applies is discharged by 'restore_set' because the body binds nothing
    and only assigns 'q_sp'. -/
theorem qSpill_run {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (sp top : U256)
    (hht : VEnv.get V "q_has_top" = some 1)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast)) :
    ExecStmts (Bridge.Dialect c g) funs V st [qSpillStmt program]
      (VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState st sp top) .normal := by
  set F := hoist (Bridge.Dialect c g) (qSpillBody program) :: funs with hF
  have hcond : Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_has_top"))
      (.eres (.vals [1] st)) :=
    Step.var (D := Bridge.Dialect c g) hht
  have hnz : (1 : U256) ≠ (Bridge.Dialect c g).zero := by
    show (1 : U256) ≠ 0
    decide
  have k1 : Step (D := Bridge.Dialect c g) F V st (.expr (yvar "q_sp")) (.eres (.vals [sp] st)) :=
    Step.var (D := Bridge.Dialect c g) hsp
  have k2 : Step (D := Bridge.Dialect c g) F V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have k3 : Step (D := Bridge.Dialect c g) F V st (.expr (ylit program.guards.stackLast))
      (.eres (.vals [BitVec.ofNat 256 program.guards.stackLast] st)) :=
    qlit F V st program.guards.stackLast
  have k4 : Step (D := Bridge.Dialect c g) F V st (.args [ylit program.guards.stackLast])
      (.eres (.vals [BitVec.ofNat 256 program.guards.stackLast] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
      (v := BitVec.ofNat 256 program.guards.stackLast) (st2 := st) k2 k3
  have k5 : Step (D := Bridge.Dialect c g) F V st
      (.args [yvar "q_sp", ylit program.guards.stackLast])
      (.eres (.vals [sp, BitVec.ofNat 256 program.guards.stackLast] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit program.guards.stackLast])
      (restvals := [BitVec.ofNat 256 program.guards.stackLast]) (st1 := st) (v := sp) (st2 := st) k4 k1
  have k6 : Step (D := Bridge.Dialect c g) F V st
      (.expr (yop Op.gt [yvar "q_sp", ylit program.guards.stackLast]))
      (.eres (.vals [b2w (decide ((BitVec.ofNat 256 program.guards.stackLast).toNat < sp.toNat))] st)) :=
    Step.builtinOk k5 (qbi_gt st sp (BitVec.ofNat 256 program.guards.stackLast))
  have kz : b2w (decide ((BitVec.ofNat 256 program.guards.stackLast).toNat < sp.toNat)) =
      (Bridge.Dialect c g).zero := by
    have hnot : ¬ ((BitVec.ofNat 256 program.guards.stackLast).toNat < sp.toNat) := hguard
    rw [decide_eq_false hnot]
    rfl
  have k7 : Step (D := Bridge.Dialect c g) F V st
      (.stmt (yif (yop Op.gt [yvar "q_sp", ylit program.guards.stackLast])
        [yexpr (ycall "q_program_fail" [])])) (.sres V st .normal) :=
    Step.ifFalse k6 kz
  have m1 : Step (D := Bridge.Dialect c g) F V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have m2 : Step (D := Bridge.Dialect c g) F V st (.expr (yvar "q_top")) (.eres (.vals [top] st)) :=
    Step.var (D := Bridge.Dialect c g) htop
  have m3 : Step (D := Bridge.Dialect c g) F V st (.args [yvar "q_top"]) (.eres (.vals [top] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := top)
      (st2 := st) m1 m2
  have m4 : Step (D := Bridge.Dialect c g) F V st
      (.args [yvar "q_sp", yvar "q_top"]) (.eres (.vals [sp, top] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_top"]) (restvals := [top]) (st1 := st)
      (v := sp) (st2 := st) m3 k1
  have m5 : Step (D := Bridge.Dialect c g) F V st
      (.expr (yop Op.mstore [yvar "q_sp", yvar "q_top"]))
      (.eres (.vals [] (qSpillState st sp top))) :=
    Step.builtinOk m4 (qbi_mstore_at st st.memory sp top rfl)
  have m6 : Step (D := Bridge.Dialect c g) F V st
      (.stmt (yexpr (yop Op.mstore [yvar "q_sp", yvar "q_top"])))
      (.sres V (qSpillState st sp top) .normal) :=
    Step.exprStmt m5
  have n1 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top) (.args [])
      (.eres (.vals [] (qSpillState st sp top))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have n2 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top) (.expr (ylit 32))
      (.eres (.vals [BitVec.ofNat 256 32] (qSpillState st sp top))) :=
    qlit F V (qSpillState st sp top) 32
  have n3 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top) (.args [ylit 32])
      (.eres (.vals [BitVec.ofNat 256 32] (qSpillState st sp top))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
      (st1 := qSpillState st sp top) (v := BitVec.ofNat 256 32) (st2 := qSpillState st sp top) n1 n2
  have n4 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top) (.expr (yvar "q_sp"))
      (.eres (.vals [sp] (qSpillState st sp top))) :=
    Step.var (D := Bridge.Dialect c g) hsp
  have n5 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top)
      (.args [yvar "q_sp", ylit 32])
      (.eres (.vals [sp, BitVec.ofNat 256 32] (qSpillState st sp top))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 32])
      (restvals := [BitVec.ofNat 256 32]) (st1 := qSpillState st sp top) (v := sp)
      (st2 := qSpillState st sp top) n3 n4
  have n6 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top)
      (.expr (yop Op.add [yvar "q_sp", ylit 32]))
      (.eres (.vals [sp + BitVec.ofNat 256 32] (qSpillState st sp top))) :=
    Step.builtinOk n5 (qbi_add (qSpillState st sp top) sp (BitVec.ofNat 256 32))
  have n7 : Step (D := Bridge.Dialect c g) F V (qSpillState st sp top)
      (.stmt (yset "q_sp" (yop Op.add [yvar "q_sp", ylit 32])))
      (.sres (VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState st sp top) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_sp"])
      (vals := [sp + BitVec.ofNat 256 32]) n6 (by rfl)
  have hchain : Step (D := Bridge.Dialect c g) F V st (.stmts (qSpillBody program))
      (.sres (VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState st sp top) .normal) :=
    Step.seqCons (D := Bridge.Dialect c g) (V1 := V) (st1 := st) k7
      (Step.seqCons (D := Bridge.Dialect c g) (V1 := V) (st1 := qSpillState st sp top) m6
        (Step.seqCons (D := Bridge.Dialect c g)
          (V1 := VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32)) (st1 := qSpillState st sp top) n7
          (Step.seqNil (D := Bridge.Dialect c g))))
  have hres : restore V (VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32)) =
      VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32) :=
    restore_set V "q_sp" (sp + BitVec.ofNat 256 32)
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set V "q_sp" (sp + BitVec.ofNat 256 32)) (st1 := qSpillState st sp top) ?_
    (Step.seqNil (D := Bridge.Dialect c g))
  refine Step.ifTrue (D := Bridge.Dialect c g) hcond hnz ?_
  rw [<- hres]
  exact Step.block (D := Bridge.Dialect c g) (body := qSpillBody program) hchain

/-! ### 2. THE TWO TAIL BLOCKS THE PUSH ARMS SHARE -/

/-- The tail PUSH_MEM_U16 and PUSH_MEM_LITERAL run after the spill: load the word the pointer names,
    cache it, mark the cache live. Stated at an ARBITRARY starting environment and state, which is what
    lets one derivation serve the arm at the no-spill entry, at a spill, and at any depth. -/
def qArmTail_fromPtr : Block Op :=
  [(yset "q_top" (yop EVM.Op.mload [(yvar "q_ptr")])), (yset "q_has_top" (ylit 1))]

theorem qArmTail_fromPtr_run {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (p v : U256)
    (hp : VEnv.get V "q_ptr" = some p)
    (hl : loadWord st.memory p.toNat = v) :
    ExecStmts (Bridge.Dialect c g) funs V st qArmTail_fromPtr
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st p.toNat 32) .normal := by
  have t1 : Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have t2 : Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_ptr")) (.eres (.vals [p] st)) :=
    Step.var (D := Bridge.Dialect c g) hp
  have t3 : Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_ptr"]) (.eres (.vals [p] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := p)
      (st2 := st) t1 t2
  have t4 : Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_ptr"]))
      (.eres (.vals [loadWord st.memory p.toNat] (touchMemory st p.toNat 32))) :=
    Step.builtinOk t3 (qbi_mload_at st st.memory p rfl)
  have t5 : Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_ptr"]))
      (.eres (.vals [v] (touchMemory st p.toNat 32))) := by
    rw [← hl]
    exact t4
  have t6 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (yset "q_top" (yop Op.mload [yvar "q_ptr"])))
      (.sres (VEnv.set V "q_top" v) (touchMemory st p.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [v]) t5 (by rfl)
  have t7 : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_top" v) (touchMemory st p.toNat 32)
      (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory st p.toNat 32))) :=
    qlit funs (VEnv.set V "q_top" v) (touchMemory st p.toNat 32) 1
  have t8 : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_top" v) (touchMemory st p.toNat 32)
      (.stmt (yset "q_has_top" (ylit 1)))
      (.sres (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
        (touchMemory st p.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_has_top"])
      (vals := [BitVec.ofNat 256 1]) t7 (by rfl)
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := VEnv.set V "q_top" v)
    (st1 := touchMemory st p.toNat 32) t6 ?_
  exact Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
    (st1 := touchMemory st p.toNat 32) t8 (Step.seqNil (D := Bridge.Dialect c g))

/-- The tail PUSH_CONST and PUSH_CONST_U8 run after the spill: load the constant-table slot
    'q_const_mptr + 32 * qconst', cache it, mark the cache live, advance the cursor by the arm's own
    operand width. Again at an arbitrary starting environment; 'inc' is 2 for the u16 slot and 1 for the
    u8 one, which is the only difference between the two arms' tails. -/
def qArmTail_fromConstSlot (inc : Nat) : Block Op :=
  [(yset "q_top" (yop EVM.Op.mload
      [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])])),
   (yset "q_has_top" (ylit 1)),
   (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit inc)]))]

theorem qArmTail_fromConstSlot_run {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (cb slot v pc : U256) (inc : Nat)
    (hcb : VEnv.get V "q_const_mptr" = some cb)
    (hslot : VEnv.get V "qconst" = some slot)
    (hpc : VEnv.get V "q_pc" = some pc)
    (hl : loadWord st.memory (cb + (slot <<< 5)).toNat = v) :
    ExecStmts (Bridge.Dialect c g) funs V st (qArmTail_fromConstSlot inc)
      (VEnv.set (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
        "q_pc" (pc + BitVec.ofNat 256 inc))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) .normal := by
  have u1 : Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have u2 : Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "qconst")) (.eres (.vals [slot] st)) :=
    Step.var (D := Bridge.Dialect c g) hslot
  have u3 : Step (D := Bridge.Dialect c g) funs V st (.args [yvar "qconst"]) (.eres (.vals [slot] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := slot)
      (st2 := st) u1 u2
  have u4 : Step (D := Bridge.Dialect c g) funs V st (.expr (ylit 5))
      (.eres (.vals [BitVec.ofNat 256 5] st)) :=
    qlit funs V st 5
  have u5 : Step (D := Bridge.Dialect c g) funs V st (.args [ylit 5, yvar "qconst"])
      (.eres (.vals [BitVec.ofNat 256 5, slot] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [slot]) (st1 := st)
      (v := BitVec.ofNat 256 5) (st2 := st) u3 u4
  have u6 : Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shl [ylit 5, yvar "qconst"]))
      (.eres (.vals [slot <<< 5] st)) :=
    Step.builtinOk u5 (qbi_shl5 st slot)
  have u7 : Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.shl [ylit 5, yvar "qconst"]])
      (.eres (.vals [slot <<< 5] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
      (v := (slot <<< 5)) (st2 := st) u1 u6
  have u8 : Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_const_mptr"))
      (.eres (.vals [cb] st)) :=
    Step.var (D := Bridge.Dialect c g) hcb
  have u9 : Step (D := Bridge.Dialect c g) funs V st
      (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])
      (.eres (.vals [cb, slot <<< 5] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]])
      (restvals := [slot <<< 5]) (st1 := st) (v := cb) (st2 := st) u7 u8
  have u10 : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]))
      (.eres (.vals [cb + (slot <<< 5)] st)) :=
    Step.builtinOk u9 (qbi_add st cb (slot <<< 5))
  have u11 : Step (D := Bridge.Dialect c g) funs V st
      (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])
      (.eres (.vals [cb + (slot <<< 5)] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
      (v := (cb + (slot <<< 5))) (st2 := st) u1 u10
  have u12 : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]))
      (.eres (.vals [loadWord st.memory (cb + (slot <<< 5)).toNat]
        (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    Step.builtinOk u11 (qbi_mload_at st st.memory (cb + (slot <<< 5)) rfl)
  have u13 : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]))
      (.eres (.vals [v] (touchMemory st (cb + (slot <<< 5)).toNat 32))) := by
    rw [← hl]
    exact u12
  have u14 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (yset "q_top" (yop Op.mload
        [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])])))
      (.sres (VEnv.set V "q_top" v) (touchMemory st (cb + (slot <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [v]) u13 (by rfl)
  have u15 : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_top" v)
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.expr (ylit 1))
      (.eres (.vals [BitVec.ofNat 256 1] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    qlit funs (VEnv.set V "q_top" v) (touchMemory st (cb + (slot <<< 5)).toNat 32) 1
  have u16 : Step (D := Bridge.Dialect c g) funs (VEnv.set V "q_top" v)
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.stmt (yset "q_has_top" (ylit 1)))
      (.sres (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
        (touchMemory st (cb + (slot <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_has_top"])
      (vals := [BitVec.ofNat 256 1]) u15 (by rfl)
  have u17 : VEnv.get (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1)) "q_pc"
      = some pc :=
    venvGet_set_ne (VEnv.set V "q_top" v) "q_has_top" "q_pc" (BitVec.ofNat 256 1) pc
      (by decide : ("q_has_top" : Ident) ≠ "q_pc")
      (venvGet_set_ne V "q_top" "q_pc" v pc (by decide : ("q_top" : Ident) ≠ "q_pc") hpc)
  have u18 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.expr (yvar "q_pc"))
      (.eres (.vals [pc] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) u17
  have u19 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.args [])
      (.eres (.vals [] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have u20 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.expr (ylit inc))
      (.eres (.vals [BitVec.ofNat 256 inc] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    qlit funs (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) inc
  have u21 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.args [ylit inc])
      (.eres (.vals [BitVec.ofNat 256 inc] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
      (st1 := touchMemory st (cb + (slot <<< 5)).toNat 32) (v := BitVec.ofNat 256 inc)
      (st2 := touchMemory st (cb + (slot <<< 5)).toNat 32) u19 u20
  have u22 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.args [yvar "q_pc", ylit inc])
      (.eres (.vals [pc, BitVec.ofNat 256 inc] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit inc])
      (restvals := [BitVec.ofNat 256 inc]) (st1 := touchMemory st (cb + (slot <<< 5)).toNat 32)
      (v := pc) (st2 := touchMemory st (cb + (slot <<< 5)).toNat 32) u21 u18
  have u23 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32)
      (.expr (yop Op.add [yvar "q_pc", ylit inc]))
      (.eres (.vals [pc + BitVec.ofNat 256 inc] (touchMemory st (cb + (slot <<< 5)).toNat 32))) :=
    Step.builtinOk u22 (qbi_add (touchMemory st (cb + (slot <<< 5)).toNat 32) pc
      (BitVec.ofNat 256 inc))
  have u24 : Step (D := Bridge.Dialect c g) funs
      (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      (touchMemory st (cb + (slot <<< 5)).toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit inc])))
      (.sres (VEnv.set (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
        "q_pc" (pc + BitVec.ofNat 256 inc)) (touchMemory st (cb + (slot <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"])
      (vals := [pc + BitVec.ofNat 256 inc]) u23 (by rfl)
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := VEnv.set V "q_top" v)
    (st1 := touchMemory st (cb + (slot <<< 5)).toNat 32) u14 ?_
  refine Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
    (st1 := touchMemory st (cb + (slot <<< 5)).toNat 32) u16 ?_
  exact Step.seqCons (D := Bridge.Dialect c g)
    (V1 := VEnv.set (VEnv.set (VEnv.set V "q_top" v) "q_has_top" (BitVec.ofNat 256 1))
      "q_pc" (pc + BitVec.ofNat 256 inc))
    (st1 := touchMemory st (cb + (slot <<< 5)).toNat 32) u24 (Step.seqNil (D := Bridge.Dialect c g))

/-! ### 3. THE SPILL BRANCH OF THE TWO POINTER PUSH ARMS -/

def qArmPfx_pushMemU16  : Block Op :=
  [(ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])),
   (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)]))]

theorem qArmRun_pushMemU16_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc sp x : U256) (p v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 1)
    (hget_top : VEnv.get V "q_top" = some x)
    (hptr : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemU16 ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) .normal := by
  have a1 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a2 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x3 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc")) (.eres (.vals [pc] st)) :=
    Step.var (D := Bridge.Dialect c g) hget_pc
  have a4 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"]) (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc) (st2 := st) a2 x3
  have x5 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a4 (qbi_mload_at st st.memory pc rfl)
  have w6 :
    (touchMemory st pc.toNat 32).memory = st.memory :=
    Midfall.Yul.Word.touchMemory_memory st pc.toNat 32
  have a7 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a1 x5
  have x8 :
    Step (D := Bridge.Dialect c g) funs V (touchMemory st pc.toNat 32) (.expr (ylit 240)) (.eres (.vals [BitVec.ofNat 256 240] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 240)
  have a9 :
    Step (D := Bridge.Dialect c g) funs V st (.args [ylit 240, yop Op.mload [yvar "q_pc"]]) (.eres (.vals [BitVec.ofNat 256 240, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 240) (st2 := touchMemory st pc.toNat 32) a7 x8
  have x10 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shr [ylit 240, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 240)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a9 (qbi_shr240 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d11 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shr [ylit 240, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    by rw [<- hptr]; exact x10
  have s12 :
    Step (D := Bridge.Dialect c g) funs V st (.stmt (ylet "q_ptr" (yop Op.shr [ylit 240, yop Op.mload [yvar "q_pc"]]))) (.sres (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d11 rfl
  have g14 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_ptr" "q_pc" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_pc")]; exact hget_pc
  have g15 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_sp" = some sp :=
    by rw [venvGet_cons_ne V "q_ptr" "q_sp" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_sp")]; exact hget_sp
  have g16 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_top")]; exact hget_top
  have g17 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_cons_eq V "q_ptr" (BitVec.ofNat 256 p)
  have a18 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x19 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a20 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [ylit 2]) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory st pc.toNat 32) a18 x19
  have x21 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g14
  have a22 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 2]) (.eres (.vals [pc, BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 2]) (restvals := [BitVec.ofNat 256 2]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a20 x21
  have x23 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 2])) (.eres (.vals [(pc + BitVec.ofNat 256 2)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a22 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 2))
  have s24 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 2]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 2)]) x23 (by rfl)
  have g26 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_ptr" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "q_ptr") g17
  have g27 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" = some sp :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) sp (by decide : "q_pc" ≠ "q_sp") g15
  have g28 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" = some x :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) x (by decide : "q_pc" ≠ "q_top") g16
  have g29 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_same (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2) pc g14
  have gHT : VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_has_top" = some 1 := venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) 1
      (by decide : ("q_pc" : Ident) ≠ "q_has_top")
      (by rw [venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 p)
        (by decide : ("q_ptr" : Ident) ≠ "q_has_top")]; exact hget_ht)
  have hpre : ExecStmts (Bridge.Dialect c g) funs V st qArmPfx_pushMemU16 (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal := by
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
    exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s24 (Step.seqNil (D := (Bridge.Dialect c g)))
  have hsp2 : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) [qSpillStmt program] (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) .normal :=
    qSpill_run program funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) sp x gHT g27 g28 hguard
  have hmid2 : VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" "q_ptr" (sp + BitVec.ofNat 256 32) (BitVec.ofNat 256 p)
      (by decide : ("q_sp" : Ident) ≠ "q_ptr") g26
  have hload2 : loadWord (qSpillState (touchMemory st pc.toNat 32) sp x).memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v := by
    rw [qSpillState_loadWord_below (touchMemory st pc.toNat 32) sp x (BitVec.ofNat 256 p) hdisj]
    exact hload
  have htail : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) qArmTail_fromPtr (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) .normal :=
    qArmTail_fromPtr_run funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p) (BitVec.ofNat 256 v) hmid2 hload2
  have hbody : GenAst.qArmBodyPushMemU16 ctx program tcq
      = qArmPfx_pushMemU16 ++ [qSpillStmt program] ++ qArmTail_fromPtr := by
    unfold GenAst.qArmBodyPushMemU16 qArmPfx_pushMemU16 qArmTail_fromPtr qSpillStmt qSpillBody
    rfl
  rw [hbody]
  exact qExec_append funs (qExec_append funs hpre hsp2) htail

theorem qArmValue_pushMemU16_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    StmtsContract (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) := by
  intro V st hpre
  have hrun := qArmRun_pushMemU16_spill ctx program tcq funs V st pc sp x p v hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2 hguard hdisj
  refine ⟨_, _, _, hrun, ⟨rfl, rfl, rfl, ?_⟩⟩
  rw [Midfall.Yul.Word.touchMemory_memory, qSpillState_loadWord_same]

theorem qArmValueAll_pushMemU16_spill {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    StmtsContractAll (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushMemU16_spill ctx program tcq funs pc sp x p v hguard hdisj)

def qArmPfx_pushMemLiteral (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_ptr" (yop EVM.Op.shr [(ylit 224), (yop EVM.Op.mload [(yvar "q_pc")])])),
   (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.byteU32Bytes)]))]

theorem qArmRun_pushMemLiteral_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc sp x : U256) (p v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 1)
    (hget_top : VEnv.get V "q_top" = some x)
    (hptr : ((loadWord st.memory pc.toNat) >>> 224) = BitVec.ofNat 256 p)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemLiteral ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) .normal := by
  have a1 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a2 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x3 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc")) (.eres (.vals [pc] st)) :=
    Step.var (D := Bridge.Dialect c g) hget_pc
  have a4 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"]) (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc) (st2 := st) a2 x3
  have x5 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a4 (qbi_mload_at st st.memory pc rfl)
  have w6 :
    (touchMemory st pc.toNat 32).memory = st.memory :=
    Midfall.Yul.Word.touchMemory_memory st pc.toNat 32
  have a7 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a1 x5
  have x8 :
    Step (D := Bridge.Dialect c g) funs V (touchMemory st pc.toNat 32) (.expr (ylit 224)) (.eres (.vals [BitVec.ofNat 256 224] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 224)
  have a9 :
    Step (D := Bridge.Dialect c g) funs V st (.args [ylit 224, yop Op.mload [yvar "q_pc"]]) (.eres (.vals [BitVec.ofNat 256 224, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 224) (st2 := touchMemory st pc.toNat 32) a7 x8
  have x10 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shr [ylit 224, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 224)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a9 (qbi_shr224 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d11 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shr [ylit 224, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    by rw [<- hptr]; exact x10
  have s12 :
    Step (D := Bridge.Dialect c g) funs V st (.stmt (ylet "q_ptr" (yop Op.shr [ylit 224, yop Op.mload [yvar "q_pc"]]))) (.sres (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d11 rfl
  have g14 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_ptr" "q_pc" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_pc")]; exact hget_pc
  have g15 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_sp" = some sp :=
    by rw [venvGet_cons_ne V "q_ptr" "q_sp" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_sp")]; exact hget_sp
  have g16 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_top")]; exact hget_top
  have g17 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_cons_eq V "q_ptr" (BitVec.ofNat 256 p)
  have a18 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x19 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (ylit tcq.byteU32Bytes)) (.eres (.vals [BitVec.ofNat 256 tcq.byteU32Bytes] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number tcq.byteU32Bytes)
  have a20 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [ylit tcq.byteU32Bytes]) (.eres (.vals [BitVec.ofNat 256 tcq.byteU32Bytes] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 tcq.byteU32Bytes) (st2 := touchMemory st pc.toNat 32) a18 x19
  have x21 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g14
  have a22 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit tcq.byteU32Bytes]) (.eres (.vals [pc, BitVec.ofNat 256 tcq.byteU32Bytes] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit tcq.byteU32Bytes]) (restvals := [BitVec.ofNat 256 tcq.byteU32Bytes]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a20 x21
  have x23 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit tcq.byteU32Bytes])) (.eres (.vals [(pc + BitVec.ofNat 256 tcq.byteU32Bytes)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a22 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 tcq.byteU32Bytes))
  have s24 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit tcq.byteU32Bytes]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 tcq.byteU32Bytes)]) x23 (by rfl)
  have g26 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_ptr" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "q_ptr") g17
  have g27 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" = some sp :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) sp (by decide : "q_pc" ≠ "q_sp") g15
  have g28 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" = some x :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) x (by decide : "q_pc" ≠ "q_top") g16
  have g29 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_pc" = some (pc + BitVec.ofNat 256 tcq.byteU32Bytes) :=
    venvGet_set_same (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) pc g14
  have gHT : VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_has_top" = some 1 := venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) 1
      (by decide : ("q_pc" : Ident) ≠ "q_has_top")
      (by rw [venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 p)
        (by decide : ("q_ptr" : Ident) ≠ "q_has_top")]; exact hget_ht)
  have hpre : ExecStmts (Bridge.Dialect c g) funs V st (qArmPfx_pushMemLiteral tcq) (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) .normal := by
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
    exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes))) (st1 := (touchMemory st pc.toNat 32)) s24 (Step.seqNil (D := (Bridge.Dialect c g)))
  have hsp2 : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) [qSpillStmt program] (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) .normal :=
    qSpill_run program funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) sp x gHT g27 g28 hguard
  have hmid2 : VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" "q_ptr" (sp + BitVec.ofNat 256 32) (BitVec.ofNat 256 p)
      (by decide : ("q_sp" : Ident) ≠ "q_ptr") g26
  have hload2 : loadWord (qSpillState (touchMemory st pc.toNat 32) sp x).memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v := by
    rw [qSpillState_loadWord_below (touchMemory st pc.toNat 32) sp x (BitVec.ofNat 256 p) hdisj]
    exact hload
  have htail : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) qArmTail_fromPtr (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) .normal :=
    qArmTail_fromPtr_run funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p) (BitVec.ofNat 256 v) hmid2 hload2
  have hbody : GenAst.qArmBodyPushMemLiteral ctx program tcq
      = (qArmPfx_pushMemLiteral tcq) ++ [qSpillStmt program] ++ qArmTail_fromPtr := by
    unfold GenAst.qArmBodyPushMemLiteral qArmPfx_pushMemLiteral qArmTail_fromPtr qSpillStmt qSpillBody
    rfl
  rw [hbody]
  exact qExec_append funs (qExec_append funs hpre hsp2) htail

theorem qArmValue_pushMemLiteral_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    StmtsContract (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemLiteral ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 224) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) := by
  intro V st hpre
  have hrun := qArmRun_pushMemLiteral_spill ctx program tcq funs V st pc sp x p v hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2 hguard hdisj
  refine ⟨_, _, _, hrun, ⟨rfl, rfl, rfl, ?_⟩⟩
  rw [Midfall.Yul.Word.touchMemory_memory, qSpillState_loadWord_same]

theorem qArmValueAll_pushMemLiteral_spill {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    StmtsContractAll (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemLiteral ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 224) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushMemLiteral_spill ctx program tcq funs pc sp x p v hguard hdisj)

/-! ### 4. THE SPILL BRANCH OF THE TWO CONSTANT-TABLE PUSH ARMS -/

def qArmPfx_pushConstU8  : Block Op :=
  [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])]))]

theorem qArmRun_pushConstU8_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb sp x : U256) (b v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 1)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hdec : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b)
    (hconst : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushConstU8 ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal := by
  have a1 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a2 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x3 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc")) (.eres (.vals [pc] st)) :=
    Step.var (D := Bridge.Dialect c g) hget_pc
  have a4 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"]) (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc) (st2 := st) a2 x3
  have x5 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a4 (qbi_mload_at st st.memory pc rfl)
  have w6 :
    (touchMemory st pc.toNat 32).memory = st.memory :=
    Midfall.Yul.Word.touchMemory_memory st pc.toNat 32
  have a7 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a1 x5
  have x8 :
    Step (D := Bridge.Dialect c g) funs V (touchMemory st pc.toNat 32) (.expr (ylit 0)) (.eres (.vals [BitVec.ofNat 256 0] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)
  have a9 :
    Step (D := Bridge.Dialect c g) funs V st (.args [ylit 0, yop Op.mload [yvar "q_pc"]]) (.eres (.vals [BitVec.ofNat 256 0, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 0) (st2 := touchMemory st pc.toNat 32) a7 x8
  have x10 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a9 (qbi_byte0 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d11 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    by rw [<- hdec]; exact x10
  have s12 :
    Step (D := Bridge.Dialect c g) funs V st (.stmt (ylet "qconst" (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]]))) (.sres (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d11 rfl
  have g13 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne V "qconst" "q_const_mptr" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_const_mptr")]; exact hget_cb
  have g15 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "qconst" "q_pc" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_pc")]; exact hget_pc
  have g16 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" = some sp :=
    by rw [venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_sp")]; exact hget_sp
  have g17 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_top")]; exact hget_top
  have g18 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_cons_eq V "qconst" (BitVec.ofNat 256 b)
  have gHT : VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_has_top" = some 1 := by
    rw [venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b)
      (by decide : ("qconst" : Ident) ≠ "q_has_top")]
    exact hget_ht
  have hpre : ExecStmts (Bridge.Dialect c g) funs V st (qArmPfx_pushConstU8) (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal := by
    exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 (Step.seqNil (D := (Bridge.Dialect c g)))
  have hsp2 : ExecStmts (Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) [qSpillStmt program] (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) .normal :=
    qSpill_run program funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) sp x gHT g16 g17 hguard
  have hslot2 : VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" "qconst" (sp + BitVec.ofNat 256 32) (BitVec.ofNat 256 b)
      (by decide : ("q_sp" : Ident) ≠ "qconst") g18
  have hcb2 : VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" "q_const_mptr" (sp + BitVec.ofNat 256 32) cb
      (by decide : ("q_sp" : Ident) ≠ "q_const_mptr") g13
  have hpc2 : VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_pc" = some pc :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" "q_pc" (sp + BitVec.ofNat 256 32) pc
      (by decide : ("q_sp" : Ident) ≠ "q_pc") g15
  have hload2 : loadWord (qSpillState (touchMemory st pc.toNat 32) sp x).memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v := by
    rw [qSpillState_loadWord_below (touchMemory st pc.toNat 32) sp x (cb + ((BitVec.ofNat 256 b) <<< 5)) hdisj]
    exact hconst
  have htail : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) (qArmTail_fromConstSlot 1) (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal :=
    qArmTail_fromConstSlot_run funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) cb (BitVec.ofNat 256 b) (BitVec.ofNat 256 v) pc
      1 hcb2 hslot2 hpc2 hload2
  have hbody : GenAst.qArmBodyPushConstU8 ctx program tcq
      = (qArmPfx_pushConstU8) ++ [qSpillStmt program] ++ qArmTail_fromConstSlot 1 := by
    unfold GenAst.qArmBodyPushConstU8 qArmPfx_pushConstU8 qArmTail_fromConstSlot qSpillStmt qSpillBody
    rfl
  rw [hbody]
  exact qExec_append funs (qExec_append funs hpre hsp2) htail

theorem qArmValue_pushConstU8_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat) :
    StmtsContract (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) := by
  intro V st hpre
  have hrun := qArmRun_pushConstU8_spill ctx program tcq funs V st pc cb sp x b v hpre.1 hpre.2.1
    hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2 hguard hdisj
  refine ⟨_, _, _, hrun, ⟨rfl, rfl, rfl, ?_⟩⟩
  rw [Midfall.Yul.Word.touchMemory_memory, qSpillState_loadWord_same]

theorem qArmValueAll_pushConstU8_spill {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat) :
    StmtsContractAll (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushConstU8_spill ctx program tcq funs pc cb sp x b v hguard hdisj)

def qArmPfx_pushConst (program : QuotientProgram) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])),
   (yif (yop EVM.Op.gt [(yvar "qconst"), (ylit program.guards.constMax)]) [(yexpr (ycall "q_program_fail" []))])]

theorem qArmRun_pushConst_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb sp x : U256) (b v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 1)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hdec : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b)
    (hconst : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)

    (hconstMax : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushConst ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal := by
  have a1 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a2 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x3 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc")) (.eres (.vals [pc] st)) :=
    Step.var (D := Bridge.Dialect c g) hget_pc
  have a4 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"]) (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc) (st2 := st) a2 x3
  have x5 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a4 (qbi_mload_at st st.memory pc rfl)
  have w6 :
    (touchMemory st pc.toNat 32).memory = st.memory :=
    Midfall.Yul.Word.touchMemory_memory st pc.toNat 32
  have a7 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a1 x5
  have x8 :
    Step (D := Bridge.Dialect c g) funs V (touchMemory st pc.toNat 32) (.expr (ylit 240)) (.eres (.vals [BitVec.ofNat 256 240] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 240)
  have a9 :
    Step (D := Bridge.Dialect c g) funs V st (.args [ylit 240, yop Op.mload [yvar "q_pc"]]) (.eres (.vals [BitVec.ofNat 256 240, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 240) (st2 := touchMemory st pc.toNat 32) a7 x8
  have x10 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shr [ylit 240, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 240)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a9 (qbi_shr240 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d11 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.shr [ylit 240, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    by rw [<- hdec]; exact x10
  have s12 :
    Step (D := Bridge.Dialect c g) funs V st (.stmt (ylet "qconst" (yop Op.shr [ylit 240, yop Op.mload [yvar "q_pc"]]))) (.sres (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d11 rfl
  have g13 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne V "qconst" "q_const_mptr" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_const_mptr")]; exact hget_cb
  have g15 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "qconst" "q_pc" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_pc")]; exact hget_pc
  have g16 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" = some sp :=
    by rw [venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_sp")]; exact hget_sp
  have g17 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_top")]; exact hget_top
  have g18 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_cons_eq V "qconst" (BitVec.ofNat 256 b)
  have a19 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x20 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (ylit program.guards.constMax)) (.eres (.vals [BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number program.guards.constMax)
  have a21 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [ylit program.guards.constMax]) (.eres (.vals [BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 program.guards.constMax) (st2 := touchMemory st pc.toNat 32) a19 x20
  have x22 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g18
  have a23 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "qconst", ylit program.guards.constMax]) (.eres (.vals [BitVec.ofNat 256 b, BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit program.guards.constMax]) (restvals := [BitVec.ofNat 256 program.guards.constMax]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a21 x22
  have x24 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.gt [yvar "qconst", ylit program.guards.constMax])) (.eres (.vals [b2w (decide ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a23 (qbi_gt (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b) (BitVec.ofNat 256 program.guards.constMax))
  have z25 :
    b2w (decide ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat)) = (Bridge.Dialect c g).zero :=
    by rw [decide_eq_false (by omega : ¬ ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat))]; rfl
  have s26 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yif (yop Op.gt [yvar "qconst", ylit program.guards.constMax]) [yexpr (ycall "q_program_fail" [])])) (.sres (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x24 z25
  have gHT : VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_has_top" = some 1 := by
    rw [venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b)
      (by decide : ("qconst" : Ident) ≠ "q_has_top")]
    exact hget_ht
  have hpre : ExecStmts (Bridge.Dialect c g) funs V st (qArmPfx_pushConst program) (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal := by
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
    exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s26 (Step.seqNil (D := (Bridge.Dialect c g)))
  have hsp2 : ExecStmts (Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) [qSpillStmt program] (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) .normal :=
    qSpill_run program funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) sp x gHT g16 g17 hguard
  have hslot2 : VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" "qconst" (sp + BitVec.ofNat 256 32) (BitVec.ofNat 256 b)
      (by decide : ("q_sp" : Ident) ≠ "qconst") g18
  have hcb2 : VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" "q_const_mptr" (sp + BitVec.ofNat 256 32) cb
      (by decide : ("q_sp" : Ident) ≠ "q_const_mptr") g13
  have hpc2 : VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_pc" = some pc :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" "q_pc" (sp + BitVec.ofNat 256 32) pc
      (by decide : ("q_sp" : Ident) ≠ "q_pc") g15
  have hload2 : loadWord (qSpillState (touchMemory st pc.toNat 32) sp x).memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v := by
    rw [qSpillState_loadWord_below (touchMemory st pc.toNat 32) sp x (cb + ((BitVec.ofNat 256 b) <<< 5)) hdisj]
    exact hconst
  have htail : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) (qArmTail_fromConstSlot 2) (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal :=
    qArmTail_fromConstSlot_run funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) cb (BitVec.ofNat 256 b) (BitVec.ofNat 256 v) pc
      2 hcb2 hslot2 hpc2 hload2
  have hbody : GenAst.qArmBodyPushConst ctx program tcq
      = (qArmPfx_pushConst program) ++ [qSpillStmt program] ++ qArmTail_fromConstSlot 2 := by
    unfold GenAst.qArmBodyPushConst qArmPfx_pushConst qArmTail_fromConstSlot qSpillStmt qSpillBody
    rfl
  rw [hbody]
  exact qExec_append funs (qExec_append funs hpre hsp2) htail

theorem qArmValue_pushConst_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    (hconstMax : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat) :
    StmtsContract (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) ∧
        loadWord st'.memory sp.toNat = x) := by
  intro V st hpre
  have hrun := qArmRun_pushConst_spill ctx program tcq funs V st pc cb sp x b v hpre.1 hpre.2.1
    hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2 hconstMax hguard hdisj
  refine ⟨_, _, _, hrun, ⟨rfl, rfl, rfl, ?_⟩⟩
  rw [Midfall.Yul.Word.touchMemory_memory, qSpillState_loadWord_same]

theorem qArmValueAll_pushConst_spill {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    (hconstMax : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat) :
    StmtsContractAll (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) ∧
        loadWord st'.memory sp.toNat = x) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushConst_spill ctx program tcq funs pc cb sp x b v hconstMax hguard hdisj)


/-! ### 5. RUNNING THE INVARIANT ACROSS A SPILL -/

/-- A constant-table read that SUCCEEDS yields a CANONICAL field element: 'fqFromU256' REJECTS a
    non-canonical word rather than reducing it ('VmReference.lean:347-350', hazard 3), so the reference
    cannot push one. This is what makes a push arm's new cached top canonical with no separate hypothesis. -/
theorem spill_constAt_ok_lt (consts : List Word256) (slot idx v : Nat)
    (h : Midfall.Generator.constAt consts slot idx = .ok v) : v < qvmFrModulus := by
  cases md : consts.drop slot with
  | nil =>
      have h1 : Midfall.Generator.constAt consts slot idx =
          .error (Midfall.Generator.QVMFault.constSlotOutOfRange slot idx) := by
        simp [Midfall.Generator.constAt, md]
      rw [h1] at h
      exact absurd h (by simp)
  | cons w t =>
      have h1 : Midfall.Generator.constAt consts slot idx = Midfall.Generator.fqFromU256 w := by
        simp [Midfall.Generator.constAt, md]
      rw [h1] at h
      by_cases hcw : w.toNat < qvmFrModulus
      · have h2 : Midfall.Generator.fqFromU256 w = Except.ok w.toNat := if_pos hcw
        rw [h2] at h
        exact (Except.ok.inj h).symm ▸ hcw
      · have h2 : Midfall.Generator.fqFromU256 w = Except.error _ := if_neg hcw
        rw [h2] at h
        exact absurd h (by simp)

/-- The pointer arithmetic a spill needs: one word above 'stackMptr + 32 * n' IS
    'stackMptr + 32 * (n + 1)'. -/
theorem spill_add_word (m n : Nat) :
    BitVec.ofNat 256 (m + 32 * n) + BitVec.ofNat 256 32 = BitVec.ofNat 256 (m + 32 * (n + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The spill guard read as a NUMBER: '¬ (sp > stackLast)' plus the invariant's own no-wrap clause says
    the pointer's natural is at most 'stackLast', so one more word still fits below '2 ^ 256'. This is the
    'QStackNoWrap' step UP that a push needs; the arithmetic arms only ever step it down. -/
theorem spill_room_toNat (program : QuotientProgram) (n : Nat) (sp : U256)
    (heq : sp = BitVec.ofNat 256 (program.stackMptr + 32 * n))
    (hwrap : program.stackMptr + 32 * n < 2 ^ 256)
    (hlast : program.guards.stackLast + 32 < 2 ^ 256)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast)) :
    program.stackMptr + 32 * (n + 1) < 2 ^ 256 := by
  have hle : (BitVec.ofNat 256 (program.stackMptr + 32 * n)).toNat ≤
      (BitVec.ofNat 256 program.guards.stackLast).toNat := by
    have h0 : sp.toNat ≤ (BitVec.ofNat 256 program.guards.stackLast).toNat := Nat.not_lt.mp hroom
    rwa [heq] at h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right program.guards.stackLast 32) hlast)] at hle
  have hgoal : program.stackMptr + 32 * (n + 1) = program.stackMptr + 32 * n + 32 := by omega
  rw [hgoal]
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hle 32) hlast

/-- A spill writes AT the pointer, so every word BELOW it survives: the invariant's already-spilled tail
    is the same list after the spill. Inducted with the pointer as a variable, because 'qSpilled' walks it
    down one word at a time. -/
theorem qSpilled_spill_below (st : EvmState) (sp top : U256) :
    ∀ (n : Nat) (p : U256), p.toNat ≤ sp.toNat → 32 * n ≤ p.toNat →
      qSpilled (qSpillState st sp top) n p = qSpilled st n p := by
  intro n
  induction n with
  | zero => intro p _ _; rfl
  | succ k ih =>
      intro p hp h32
      have hge : 32 ≤ p.toNat := by omega
      have h32w : (BitVec.ofNat 256 32).toNat = 32 := rfl
      have hsub : (p - BitVec.ofNat 256 32).toNat = p.toNat - 32 := by
        rw [BitVec.toNat_sub, h32w]
        have key : 2 ^ 256 - 32 + p.toNat = 2 ^ 256 + (p.toNat - 32) := by omega
        rw [key, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le p.toNat 32) (BitVec.isLt p))
      have hhead : loadWord (qSpillState st sp top).memory (p.toNat - 32) =
          loadWord st.memory (p.toNat - 32) :=
        Midfall.Yul.Word.loadWord_storeWord_disjoint st.memory sp.toNat (p.toNat - 32) top
          (Or.inl (by omega))
      rw [qSpilled_succ, qSpilled_succ, hsub, hhead]
      exact congrArg (List.cons (loadWord st.memory (p.toNat - 32)))
        (ih (p - BitVec.ofNat 256 32) (by rw [hsub]; omega) (by rw [hsub]; omega))

/-- **THE INVARIANT STEPS ACROSS A SPILL - PUSH_CONST.** This is the step 'QuotientStackInv' could not
    state: the reference pushes a constant onto a NON-EMPTY stack, so the emitted arm takes its SPILL
    branch, and the correspondence holds again at the next boundary with the old cached top now spilled
    below the pointer. Two cases, because a push does not pop: at the empty reference stack the arm takes
    the branch the published triple already describes, and at a live cached top it takes the one this card
    lands. The extra hypotheses are bridges the arm layer cannot supply by itself, each named in section 6:
    'hbytes' (the operand bytes the reference decodes are the word the machine reads at its cursor - QFIX's
    O4 at one boundary), 'hread' and 'hv' (the const table in memory IS the reference's constant list at
    this slot - 'AgreesConsts'), 'hroom' (the spill guard passes), 'hdisj' (the spill slot does not overlap
    the word the arm is about to read), 'hfit' (the pointer does not wrap at depth 'n + 1'). None is a
    hypothesis on a row, on 'ValidV3', on a bundle or on the root (RULES). -/
theorem qStackCorr_pushConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (b₀ b₁ : Nat) (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (pc cb sp top : U256) (v : Nat)
    (hfit : quotientProgramFits program)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hconstMax : (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat ≤
      (BitVec.ofNat 256 program.guards.constMax).toNat)
    (hbytes : (loadWord st.memory pc.toNat) >>> 240 = BitVec.ofNat 256 (b₀ * 256 + b₁))
    (hread : loadWord st.memory (cb + ((BitVec.ofNat 256 (b₀ * 256 + b₁)) <<< 5)).toNat =
      BitVec.ofNat 256 v)
    (hv : Midfall.Generator.constAt consts (b₀ * 256 + b₁) 0 = .ok v)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 (b₀ * 256 + b₁)) <<< 5)).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 (b₀ * 256 + b₁)) <<< 5)).toNat)
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st
      (GenAst.qArmBodyPushConst ctx program tcq) V' st' o)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPushConst :: b₀ :: b₁ :: rest) consts 0
      qOpPushConst stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, spb, topb, hspb, htopb, heq0, hwrap0, hcase⟩ := hcorr
  have esp : sp = spb := Option.some.inj (hsp.symm.trans hspb)
  have etop : top = topb := Option.some.inj (htop.symm.trans htopb)
  subst esp; subst etop
  have hvx : v < qvmFrModulus := spill_constAt_ok_lt consts (b₀ * 256 + b₁) 0 v hv
  have hvc : (BitVec.ofNat 256 v).toNat = v := rtie_ofNat_toNat v hvx
  have hspn : 32 * n ≤ sp.toNat := by
    rw [heq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap0]
    omega
  have hstep' : Midfall.Generator.evalQuotientIdentityStep ([qOpPushConst, b₀, b₁] ++ rest) consts 0
      qOpPushConst stk mem = .ok s := hstep
  rw [← hvc] at hv
  rw [rtie_pushConst b₀ b₁ rest consts (BitVec.ofNat 256 v) stk mem hv] at hstep'
  obtain rfl := Except.ok.inj hstep'
  rcases hcase with ⟨h0, hnil, hn0⟩ | ⟨h1, hcan, hshape, hspill⟩
  · -- the empty reference stack: the arm takes the NO-SPILL branch, published by QARMS
    subst hn0
    obtain ⟨hnormal, hst'', hV''⟩ :=
      qArmValueAll_pushConst hc hg ctx program tcq funs pc cb sp top (b₀ * 256 + b₁) v hconstMax
        V st ⟨hget_pc, hsp, h0, htop, hget_cb, hbytes, hread⟩ V' st' o hrun
    subst hnormal; subst hV''; subst hst''
    refine ⟨rfl, ⟨0, sp, BitVec.ofNat 256 v, ?_, ?_, heq0, QStackNoWrap_zero_of_fits program hfit,
      Or.inr ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) sp
              (by decide : ("q_pc" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) sp
              (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" "q_sp" (BitVec.ofNat 256 v) sp
              (by decide : ("q_top" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 (b₀ * 256 + b₁))
                (by decide : ("qconst" : Ident) ≠ "q_sp")) (hsp)))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 v)
              (by decide : ("q_pc" : Ident) ≠ "q_top") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v)
              (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v) top (Eq.trans (venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 (b₀ * 256 + b₁))
                (by decide : ("qconst" : Ident) ≠ "q_top")) (htop)))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 1)
              (by decide : ("q_pc" : Ident) ≠ "q_has_top") (venvGet_set_same (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 0 (venvGet_set_ne (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_top" "q_has_top" (BitVec.ofNat 256 v) 0
              (by decide : ("q_top" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 (b₀ * 256 + b₁))
                (by decide : ("qconst" : Ident) ≠ "q_has_top")) (h0)))))
    · rw [hvc]
      exact hvx
    · rw [hnil]
      rfl
    · intro w hw
      have hq : ∀ (X : EvmState), qSpilled X 0 sp = [] := fun X => rfl
      rw [hq] at hw
      cases hw
  · -- the live cached top: the SPILL branch this card lands
    obtain ⟨hnormal, hst'', hV'', hspillsp⟩ :=
      qArmValueAll_pushConst_spill hc hg ctx program tcq funs pc cb sp top (b₀ * 256 + b₁) v
        hconstMax hroom hdisj V st ⟨hget_pc, hsp, h1, htop, hget_cb, hbytes, hread⟩ V' st' o hrun
    subst hnormal
    have htails : qSpilled st' (n + 1) (sp + BitVec.ofNat 256 32) = top :: qSpilled st n sp := by
      rw [qSpilled_succ, BitVec.add_sub_cancel, hspillsp]
      suffices h : qSpilled st' n sp = qSpilled st n sp by rw [h]
      rw [hst'', qSpilled_touchMemory,
          qSpilled_spill_below (touchMemory st pc.toNat 32) sp top n sp (le_refl sp.toNat) hspn,
          qSpilled_touchMemory]
    refine ⟨rfl, ⟨n + 1, sp + BitVec.ofNat 256 32, BitVec.ofNat 256 v, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) (sp + BitVec.ofNat 256 32)
              (by decide : ("q_pc" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32)
              (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32)
              (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32) sp (Eq.trans (venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 (b₀ * 256 + b₁))
                (by decide : ("qconst" : Ident) ≠ "q_sp")) (hsp))))))
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 v)
              (by decide : ("q_pc" : Ident) ≠ "q_top") (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v)
              (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) top (venvGet_set_ne (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) top
              (by decide : ("q_sp" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 (b₀ * 256 + b₁))
                (by decide : ("qconst" : Ident) ≠ "q_top")) (htop))))))
    · rw [heq0]
      exact spill_add_word program.stackMptr n
    · exact spill_room_toNat program n sp heq0 hwrap0 hfit.2.2.2.1 hroom
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 1)
              (by decide : ("q_pc" : Ident) ≠ "q_has_top") (venvGet_set_same (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 1 (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) 1
              (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("qconst", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) 1
              (by decide : ("q_sp" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 (b₀ * 256 + b₁))
                (by decide : ("qconst" : Ident) ≠ "q_has_top")) (h1))))))
    · rw [hvc]
      exact hvx
    · rw [hshape, htails, List.map_cons]
    · intro w hw
      rw [htails] at hw
      cases List.mem_cons.mp hw with
      | inl heq => exact heq ▸ hcan
      | inr hw2 => exact hspill w hw2

/-- **THE SPILL CHAINS.** The witness that the new step is an induction step and not a one-off: NEG moves
    the cached top, PUSH_CONST spills it, and ADD pops the spilled word back out of memory at the pointer
    the spill left behind. This is the fact that was structurally unavailable before this card: the middle
    step is the spill branch. -/
theorem qStackCorr_neg_then_pushConst_then_add {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V₁ V₂ V₃ : VEnv (Bridge.Dialect c g)) (st st₁ st₂ st₃ : EvmState) (o₁ o₂ o₃ : Outcome)
    (rest₁ : List Nat) (b₀ b₁ : Nat) (rest₂ : List Nat)
    (consts : List Word256) (mem₁ mem₂ mem₃ : QuotientRefMemory)
    (stk : List QVMFr) (s₁ s₂ s₃ : IdentityStep)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hfit : quotientProgramFits program)
    (hstep₁ : Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest₁) consts 0 qOpNeg stk mem₁ = .ok s₁)
    (hrun₁ : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyNeg ctx program tcq) V₁ st₁ o₁)
    (hr : VEnv.get V "r" = some frModulusWord)
    (_hr₁ : VEnv.get V₁ "r" = some frModulusWord)
    (hstep₂ : Midfall.Generator.evalQuotientIdentityStep (qOpPushConst :: b₀ :: b₁ :: rest₂) consts 0
      qOpPushConst s₁.stack mem₂ = .ok s₂)
    (hrun₂ : ExecStmts (Bridge.Dialect c g) funs V₁ st₁
      (GenAst.qArmBodyPushConst ctx program tcq) V₂ st₂ o₂)
    (pc cb sp top : U256) (v : Nat)
    (hget_pc : VEnv.get V₁ "q_pc" = some pc)
    (hget_cb : VEnv.get V₁ "q_const_mptr" = some cb)
    (hsp : VEnv.get V₁ "q_sp" = some sp)
    (htop : VEnv.get V₁ "q_top" = some top)
    (hconstMax : (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat ≤
      (BitVec.ofNat 256 program.guards.constMax).toNat)
    (hbytes : (loadWord st₁.memory pc.toNat) >>> 240 = BitVec.ofNat 256 (b₀ * 256 + b₁))
    (hread : loadWord st₁.memory (cb + ((BitVec.ofNat 256 (b₀ * 256 + b₁)) <<< 5)).toNat =
      BitVec.ofNat 256 v)
    (hv : Midfall.Generator.constAt consts (b₀ * 256 + b₁) 0 = .ok v)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 (b₀ * 256 + b₁)) <<< 5)).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 (b₀ * 256 + b₁)) <<< 5)).toNat)
    (hstep₃ : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest₂) consts 0 qOpAdd s₂.stack
      mem₃ = .ok s₃)
    (hrun₃ : ExecStmts (Bridge.Dialect c g) funs V₂ st₂ (GenAst.qArmBodyAdd ctx program tcq) V₃ st₃ o₃)
    (hr₂ : VEnv.get V₂ "r" = some frModulusWord) :
    o₁ = .normal ∧ o₂ = .normal ∧ o₃ = .normal ∧
      QStackCorr (c := c) (g := g) program V₃ st₃ s₃.stack := by
  obtain ⟨hn₁, hc₁⟩ := qStackCorr_neg hc hg ctx program tcq funs V V₁ st st₁ o₁ rest₁ consts mem₁ stk s₁
    hrun₁ hr hcorr hstep₁
  obtain ⟨hn₂, hc₂⟩ := qStackCorr_pushConst hc hg ctx program tcq funs V₁ V₂ st₁ st₂ o₂ b₀ b₁ rest₂
    consts mem₂ s₁.stack s₂ pc cb sp top v hfit hget_pc hget_cb hsp htop hconstMax hbytes hread hv hroom
    hdisj hrun₂ hc₁ hstep₂
  obtain ⟨hn₃, hc₃⟩ := qStackCorr_add hc hg ctx program tcq funs V₂ V₃ st₂ st₃ o₃ rest₂ consts mem₃
    s₂.stack s₃ hrun₃ hr₂ hc₂ hstep₃
  exact ⟨hn₁, hn₂, hn₃, hc₃⟩

/-! ### 6. WHAT 'PG_spillArmTriple' STILL LACKS, NAMED -/

/-- **THE FACT NOTHING SUPPLIES.** The spill writes the cached word AT 'q_sp'; the arm then reads the
    constant (or literal, or token) word it is about to cache. If those two 32-byte windows overlap, the
    arm reads back its own spill and the postcondition 'q_top = v' is simply FALSE. 'quotientProgramFits'
    ('Statements.lean:3225') bounds every region below '2 ^ 256' but says NOTHING about the const table
    and the stack being disjoint - exactly the gap MemoryPairs §(1) found for the vk windows, on the stack
    side. It is not a theorem of anything in the tree, so it is named here as a 'PG_*' Prop and reported;
    it is used ONLY as an arm-lemma hypothesis ('hdisj'), never on a row, on 'ValidV3', on a bundle or on
    the root (RULES). -/
def PG_spillSlotDisjoint (_program : QuotientProgram) (cb sp : U256) (b : Nat) : Prop :=
  (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨
    sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat

/-- **DEFECT IN THE PUBLISHED 'PG_spillArmTriple' ('QuotientStackInv.lean:752-769'), STATED PLAINLY.**
    Its PRE pins the spill guard and the two memory reads, but it omits TWO facts the arm itself demands.
    (1) The emitted arm's FIRST statement after the opcode read is
    'yif (qconst > ylit program.guards.constMax) [q_program_fail()]' ('GenAstQvm.lean:138'), so at
    'b > constMax' the arm HALTS: 'o = .normal' in the post is then false, and the PRE as published is
    satisfiable with 'b > constMax' (take any memory whose top 16 bits at 'pc' are 'b'). The published
    no-spill triple 'qArmValueAll_pushConst' carries exactly this hypothesis as 'hguard'
    ('QuotientArms.lean:3076'), which is the proof that the omission is an oversight and not a claim that
    the guard is unnecessary. (2) The spill's 'mstore' can overwrite the word the arm reads next, which is
    'PG_spillSlotDisjoint' above. So 'PG_spillArmTriple' is NOT dischargeable as written; the corrected
    contract is 'PG_spillArmTripleC' below, and 'qSpillContract_pushConst' PROVES it. Nothing in
    'QuotientStackInv.lean' was edited or restated (RULES). -/
def PG_spillArmTripleC {c : ExternalCalls} {g : ExternalGas}
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
      ¬ (sp > BitVec.ofNat 256 program.guards.stackLast) ∧
      (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat ∧
      PG_spillSlotDisjoint program cb sp b)
    (fun _ _ V' st' o => o = .normal ∧
      VEnv.get V' "q_sp" = some (sp + BitVec.ofNat 256 32) ∧
      VEnv.get V' "q_has_top" = some 1 ∧
      VEnv.get V' "q_top" = some (BitVec.ofNat 256 v) ∧
      loadWord st'.memory sp.toNat = top)

/-- **THE SPILL CONTRACT, IN 'PG_spillArmTriple'\'s OWN FORM, DISCHARGED.** Same post as the published
    Prop - spill guard, 'mstore', 'q_sp += 32', and the spilled word readable at the OLD pointer - proved
    for the head arm from the block-level run of section 1. -/
theorem qSpillContract_pushConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (pc cb sp top : U256) (b v : Nat) :
    PG_spillArmTripleC ctx program tcq funs pc cb sp top b v := by
  intro V st hpre V' st' o hrun
  obtain ⟨hget_pc, hsp, h1, htop, hget_cb, hbytes, hread, hroom, hconstMax, hdisj⟩ := hpre
  obtain ⟨hnormal, hst'', hV'', hspillsp⟩ :=
    qArmValueAll_pushConst_spill hc hg ctx program tcq funs pc cb sp top b v hconstMax hroom hdisj
      V st ⟨hget_pc, hsp, h1, htop, hget_cb, hbytes, hread⟩ V' st' o hrun
  refine ⟨hnormal, ?_, ?_, ?_, hspillsp⟩
  · rw [hV'']
    exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) (sp + BitVec.ofNat 256 32)
              (by decide : ("q_pc" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32)
              (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32)
              (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32) sp (Eq.trans (venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 b)
                  (by decide : ("qconst" : Ident) ≠ "q_sp")) (hsp))))))
  · rw [hV'']
    exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 1)
              (by decide : ("q_pc" : Ident) ≠ "q_has_top") (venvGet_set_same (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 1 (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) 1
              (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) 1
              (by decide : ("q_sp" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b)
                  (by decide : ("qconst" : Ident) ≠ "q_has_top")) (h1))))))
  · rw [hV'']
    exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 v)
              (by decide : ("q_pc" : Ident) ≠ "q_top") (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v)
              (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) top (venvGet_set_ne (("qconst", (BitVec.ofNat 256 b)) :: V) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) top
              (by decide : ("q_sp" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b)
                  (by decide : ("qconst" : Ident) ≠ "q_top")) (htop))))))

/-! ### 7. WHAT REMAINS, NAMED EXACTLY -/

/- **THE OTHER THREE PUSH ARMS' INVARIANT STEPS ARE MECHANICAL, AND WHAT EACH STILL NEEDS.** The spill
    branch is discharged for all four, and 'qStackCorr_pushConst' shows the step shape. The remaining
    three instances differ only in (i) the reference tie's reader hypothesis and (ii) the final
    environment's shape, which is where the peels live:
    * 'pushConstU8' - identical to 'pushConst' except the decoded slot is one byte
      ('(loadWord pc >>> 248) &&& 0xff'), the tail advances 'q_pc' by 1 not 2, and there is NO
      'constMax' guard in the arm at all, so 'hconstMax' drops out. 'spill_constAt_ok_lt' still supplies
      canonicity. Nothing is missing.
    * 'pushMemU16' and 'pushMemLiteral' - the reference's value is '(mem.literal p).1', and
      'QuotientRefMemory' is a FREE cache list ('VmReference.lean:410-415': 'cache : List (Nat × Nat ×
      QVMFr)', no canonicality invariant), so unlike 'constAt' the reader equation 'rtie_pushMemU16' asks
      for does NOT force the pushed word to be canonical. Those two steps therefore need one more named
      hypothesis, '(mem.literal p).1 < qvmFrModulus' - the literal-domain member of the same family as
      'AgreesFrame'. It is stated nowhere in the tree, so it is reported here rather than invented as a
      row hypothesis (RULES).
-/

/- **THE TWO TOKEN ARMS.** Not blocked conceptually: their spill block is the same 'qSpillStmt', and
    'qArmTail_fromPtr' already covers their tails verbatim ('yset q_top (mload q_ptr); yset q_has_top 1').
    What they cost is a THIRD prefix each - the nine-way 'Stmt.switch' over 'program.memUsage' that the
    published proofs expand in full ('QuotientArms.lean:3181-3449', '3490-3896'), which must be re-derived
    at 'q_has_top = some 1'. That is transcription, not a gap; it is left undone by this card for budget,
    and it is named here so the next card does not re-derive the block. -/

/- **THE FOUR LIMB ARMS ARE EXCLUDED, NOT UNFINISHED.** LIN7, BILIN7_ROW, BILIN7_PAIRWISE and MODARITH7
    sit behind 'PG_limbCountAgrees' ('QuotientArms.lean:4425'), an OPEN HUMAN DECISION. A spill contract
    for them would take 'hlimbs'/'hfit' as arm-lemma hypotheses and so would assume the very bound the
    decision gates. IDSEG and STKINV excluded them explicitly; this card does the same, and the count of
    affected arms this card addresses is therefore SIX push arms minus the two token ones, not ten.
-/

/-! ### 8. ACCEPTANCE PRINTS -/

#print axioms Midfall.Lowering.QuotientSpill.qExec_append
#print axioms Midfall.Lowering.QuotientSpill.qSpill_run
#print axioms Midfall.Lowering.QuotientSpill.qSpillState_loadWord_same
#print axioms Midfall.Lowering.QuotientSpill.qSpillState_loadWord_below
#print axioms Midfall.Lowering.QuotientSpill.qArmTail_fromPtr_run
#print axioms Midfall.Lowering.QuotientSpill.qArmTail_fromConstSlot_run
#print axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemU16_spill
#print axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemLiteral_spill
#print axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushConstU8_spill
#print axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushConst_spill
#print axioms Midfall.Lowering.QuotientSpill.qSpilled_spill_below
#print axioms Midfall.Lowering.QuotientSpill.spill_constAt_ok_lt
#print axioms Midfall.Lowering.QuotientSpill.spill_room_toNat
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushConst
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushConst_then_add
#print axioms Midfall.Lowering.QuotientSpill.qSpillContract_pushConst

#cone_sorries Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemU16_spill
#cone_sorries Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemLiteral_spill
#cone_sorries Midfall.Lowering.QuotientSpill.qArmValueAll_pushConstU8_spill
#cone_sorries Midfall.Lowering.QuotientSpill.qArmValueAll_pushConst_spill
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_pushConst
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushConst_then_add
#cone_sorries Midfall.Lowering.QuotientSpill.qSpillContract_pushConst
#cone_sorries Midfall.Lowering.QuotientSpill.qSpill_run

#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushConst [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushConst_spill [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemU16_spill [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemLiteral_spill [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushConstU8_spill [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qSpillContract_pushConst [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushConst_then_add [propext, Classical.choice, Quot.sound] native []


/-! ### 9. THE TWO TOKEN ARMS' SPILL BRANCH (SPILL2)

  SPILL section 7 named these two arms and left them undone: 'their spill block is the same
  'qSpillStmt', and 'qArmTail_fromPtr' already covers their tails verbatim... What they cost is a THIRD
  prefix each - the nine-way 'Stmt.switch' over 'program.memUsage' that the published proofs expand in
  full... That is transcription, not a gap.' THIS SECTION IS THAT TRANSCRIPTION. Each prefix below is the
  published no-spill proof's own 'have' lines ('QuotientArms.lean:3195-3364' for the token arm,
  ':3505-3797' for the offset arm) copied verbatim and changed in exactly one respect - the cached-top
  flag they transport is 'some 1' instead of 'some 0', which is the only place the two branches differ -
  and then composed with SPILL's 'qSpillStmt' and 'qArmTail_fromPtr' by 'qExec_append'. The switch is
  still taken by 'selectSwitch_head' + 'find?_head' on 'hl0'; the block scope is still discharged by
  'Step.block' + 'restore_set'; 'qSpill_run' is not rebuilt.

  WHAT THE TOKEN ARMS NEED THAT THE CONST ARMS DID NOT. There is no 'constMax' guard in either token arm:
  an unknown token falls to the switch's 'some [q_program_fail()]' default, so the arm's own PRE ('hl0',
  the case is present) is what keeps it running. But the spill's 'mstore' at 'q_sp' can still overwrite
  the word the arm reads next at 'q_ptr', so each contract carries a disjointness hypothesis of the SAME
  SHAPE as 'PG_spillSlotDisjoint' but about a DIFFERENT pair of windows - the token window at
  'L_0_MPTR' (or 'L_0_MPTR + q_off') and the stack, not the const table and the stack. BINDINV's
  'spillSlotDisjoint_of_ordered' orders the CONST window below the stack and therefore does NOT discharge
  these; see section 10 for exactly what it does discharge. -/

/-- The four statements PUSH_MEM_TOKEN runs before its spill: decode the token byte from the word at
    'q_pc', advance the cursor by the ONE operand byte, initialise 'q_ptr', and resolve the token through
    the nine-way 'Stmt.switch'. Verbatim the first four elements of 'GenAst.qArmBodyPushMemToken'
    ('GenAstQvm.lean:150'), which is what makes the arm body 'pfx ++ [qSpillStmt program] ++
    qArmTail_fromPtr' true by 'rfl'. -/
def qArmPfx_pushMemToken (program : QuotientProgram) (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_token" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])),
   (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)])),
   (ylet "q_ptr" (ylit 0)),
   (Stmt.switch (yvar "q_token") ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (some [(yexpr (ycall "q_program_fail" []))]))]

/-- **PUSH_MEM_TOKEN STEPS ACROSS ITS SPILL.** The cached top is live, so the arm spills 'x' at the old
    pointer before it reads the token word; the spilled word is readable at 'sp' afterwards, which is
    where the next arm's popped operand will be read. -/
theorem qArmRun_pushMemToken_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc sp x : U256) (p v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 1)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_l0 : VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p))
    (hbyte : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
    (hl0 : program.memUsage.l0 = true)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemToken ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) .normal := by
  have a1 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a2 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x3 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc")) (.eres (.vals [pc] st)) :=
    Step.var (D := Bridge.Dialect c g) hget_pc
  have a4 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"]) (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc) (st2 := st) a2 x3
  have x5 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a4 (qbi_mload_at st st.memory pc rfl)
  have w6 :
    (touchMemory st pc.toNat 32).memory = st.memory :=
    Midfall.Yul.Word.touchMemory_memory st pc.toNat 32
  have a7 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a1 x5
  have x8 :
    Step (D := Bridge.Dialect c g) funs V (touchMemory st pc.toNat 32) (.expr (ylit 0)) (.eres (.vals [BitVec.ofNat 256 0] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)
  have a9 :
    Step (D := Bridge.Dialect c g) funs V st (.args [ylit 0, yop Op.mload [yvar "q_pc"]]) (.eres (.vals [BitVec.ofNat 256 0, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 0) (st2 := touchMemory st pc.toNat 32) a7 x8
  have x10 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a9 (qbi_byte0 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d11 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])) (.eres (.vals [BitVec.ofNat 256 tcq.mem.l0] (touchMemory st pc.toNat 32))) :=
    by rw [<- hbyte]; exact x10
  have s12 :
    Step (D := Bridge.Dialect c g) funs V st (.stmt (ylet "q_token" (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]]))) (.sres (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d11 rfl
  have g13 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne V "q_token" "L_0_MPTR" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "L_0_MPTR")]; exact hget_l0
  have g14 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_has_top" = some 1 :=
    by rw [venvGet_cons_ne V "q_token" "q_has_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_has_top")]; exact hget_ht
  have g15 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_token" "q_pc" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_pc")]; exact hget_pc
  have g16 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_sp" = some sp :=
    by rw [venvGet_cons_ne V "q_token" "q_sp" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_sp")]; exact hget_sp
  have g17 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_token" "q_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_top")]; exact hget_top
  have g18 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    venvGet_cons_eq V "q_token" (BitVec.ofNat 256 tcq.mem.l0)
  have a19 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x20 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have a21 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.args [ylit 1]) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 1) (st2 := touchMemory st pc.toNat 32) a19 x20
  have x22 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g15
  have a23 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 1]) (.eres (.vals [pc, BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 1]) (restvals := [BitVec.ofNat 256 1]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a21 x22
  have x24 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 1])) (.eres (.vals [(pc + BitVec.ofNat 256 1)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a23 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 1))
  have s25 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 1]))) (.sres (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 1)]) x24 (by rfl)
  have g26 :
    VEnv.get (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" "L_0_MPTR" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "L_0_MPTR") g13
  have g27 :
    VEnv.get (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_has_top" = some 1 :=
    venvGet_set_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 1) 1 (by decide : "q_pc" ≠ "q_has_top") g14
  have g28 :
    VEnv.get (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_sp" = some sp :=
    venvGet_set_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 1) sp (by decide : "q_pc" ≠ "q_sp") g16
  have g29 :
    VEnv.get (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    venvGet_set_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" "q_token" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_pc" ≠ "q_token") g18
  have g30 :
    VEnv.get (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" = some x :=
    venvGet_set_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 1) x (by decide : "q_pc" ≠ "q_top") g17
  have g31 :
    VEnv.get (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_pc" = some (pc + BitVec.ofNat 256 1) :=
    venvGet_set_same (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1) pc g15
  have x32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory st pc.toNat 32) (.expr (ylit 0)) (.eres (.vals [BitVec.ofNat 256 0] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)
  have s33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory st pc.toNat 32) (.stmt (ylet "q_ptr" (ylit 0))) (.sres (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal x32 rfl
  have g34 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "L_0_MPTR" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "L_0_MPTR")]; exact g26
  have g35 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_has_top" = some 1 :=
    by rw [venvGet_cons_ne (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_has_top" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_has_top")]; exact g27
  have g36 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_pc" = some (pc + BitVec.ofNat 256 1) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_pc" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_pc")]; exact g31
  have g37 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_sp" = some sp :=
    by rw [venvGet_cons_ne (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_sp" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_sp")]; exact g28
  have g38 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_token" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_token")]; exact g29
  have g39 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_top" = some x :=
    by rw [venvGet_cons_ne (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_top" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_top")]; exact g30
  have g40 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" = some (BitVec.ofNat 256 0) :=
    venvGet_cons_eq (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" (BitVec.ofNat 256 0)
  have x41 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.expr (yvar "q_token")) (.eres (.vals [BitVec.ofNat 256 tcq.mem.l0] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g38
  have h42 :
    selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (some [(yexpr (ycall "q_program_fail" []))]) = [yset "q_ptr" (yvar "L_0_MPTR")] :=
    by refine selectSwitch_head (D := Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (Literal.number tcq.mem.l0, [yset "q_ptr" (yvar "L_0_MPTR")]) (some [(yexpr (ycall "q_program_fail" []))]) ?_
       rw [hl0]
       exact find?_head _ _ _ (decide_litValue_number_eq_self tcq.mem.l0)
  have x43 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yvar "L_0_MPTR")] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.expr (yvar "L_0_MPTR")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g34
  have s44 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yvar "L_0_MPTR")] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.stmt (yset "q_ptr" (yvar "L_0_MPTR"))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_ptr"]) (vals := [BitVec.ofNat 256 p]) x43 (by rfl)
  have g45 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "L_0_MPTR" (BitVec.ofNat 256 p) (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "L_0_MPTR") g34
  have g46 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_has_top" = some 1 :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_has_top" (BitVec.ofNat 256 p) 1 (by decide : "q_ptr" ≠ "q_has_top") g35
  have g47 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_pc" = some (pc + BitVec.ofNat 256 1) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_pc" (BitVec.ofNat 256 p) (pc + BitVec.ofNat 256 1) (by decide : "q_ptr" ≠ "q_pc") g36
  have g48 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" = some sp :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_sp" (BitVec.ofNat 256 p) sp (by decide : "q_ptr" ≠ "q_sp") g37
  have g49 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_token" (BitVec.ofNat 256 p) (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_ptr" ≠ "q_token") g38
  have g50 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" = some x :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_top" (BitVec.ofNat 256 p) x (by decide : "q_ptr" ≠ "q_top") g39
  have g51 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_same (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p) (BitVec.ofNat 256 0) g40
  have b52 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yvar "L_0_MPTR")] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.stmts [yset "q_ptr" (yvar "L_0_MPTR")]) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) .normal) :=
    by exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p))) (st1 := (touchMemory st pc.toNat 32)) s44 (Step.seqNil (D := Bridge.Dialect c g))
  have k53 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.stmt (.block (selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (some [(yexpr (ycall "q_program_fail" []))])))) (.sres (restore (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p))) (touchMemory st pc.toNat 32) .normal) :=
    by refine Step.block (D := Bridge.Dialect c g) ?_
       rw [h42]
       exact b52
  have k54 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.stmt (.block (selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (some [(yexpr (ycall "q_program_fail" []))])))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) .normal) :=
    by rw [restore_set] at k53
       exact k53
  have s55 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (touchMemory st pc.toNat 32) (.stmt (Stmt.switch (yvar "q_token") ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (some [(yexpr (ycall "q_program_fail" []))]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) .normal) :=
    Step.switchExec (D := Bridge.Dialect c g) x41 k54
  have hpre : ExecStmts (Bridge.Dialect c g) funs V st (qArmPfx_pushMemToken program tcq) (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) .normal := by
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) (st1 := (touchMemory st pc.toNat 32)) s25 ?_
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1)))) (st1 := (touchMemory st pc.toNat 32)) s33 ?_
    exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p))) (st1 := (touchMemory st pc.toNat 32)) s55 (Step.seqNil (D := Bridge.Dialect c g))
  have hsp2 : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) [qSpillStmt program] (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) .normal :=
    qSpill_run program funs (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) (touchMemory st pc.toNat 32) sp x g46 g48 g50 hguard
  have hmid2 : VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" "q_ptr" (sp + BitVec.ofNat 256 32) (BitVec.ofNat 256 p)
      (by decide : ("q_sp" : Ident) ≠ "q_ptr") g51
  have hload2 : loadWord (qSpillState (touchMemory st pc.toNat 32) sp x).memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v := by
    rw [qSpillState_loadWord_below (touchMemory st pc.toNat 32) sp x (BitVec.ofNat 256 p) hdisj]
    exact hload
  have htail : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) qArmTail_fromPtr (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) .normal :=
    qArmTail_fromPtr_run funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p) (BitVec.ofNat 256 v) hmid2 hload2
  have hbody : GenAst.qArmBodyPushMemToken ctx program tcq
      = qArmPfx_pushMemToken program tcq ++ [qSpillStmt program] ++ qArmTail_fromPtr := by
    unfold GenAst.qArmBodyPushMemToken qArmPfx_pushMemToken qArmTail_fromPtr qSpillStmt qSpillBody
    rfl
  rw [hbody]
  exact qExec_append funs (qExec_append funs hpre hsp2) htail

/-- The 'pushMemToken' spill contract in the shape 'qArmValue_pushMemU16_spill' has: PRE at
    'q_has_top = some 1', post naming the state, the environment, and the spilled word at the OLD pointer. -/
theorem qArmValue_pushMemToken_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    (hl0 : program.memUsage.l0 = true)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    StmtsContract (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemToken ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p) ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0 ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) := by
  intro V st hpre
  have hrun := qArmRun_pushMemToken_spill ctx program tcq funs V st pc sp x p v hpre.1 hpre.2.1
    hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2 hl0 hguard hdisj
  refine ⟨_, _, _, hrun, ⟨rfl, rfl, rfl, ?_⟩⟩
  rw [Midfall.Yul.Word.touchMemory_memory, qSpillState_loadWord_same]

theorem qArmValueAll_pushMemToken_spill {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    (hl0 : program.memUsage.l0 = true)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat) :
    StmtsContractAll (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemToken ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p) ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0 ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushMemToken_spill ctx program tcq funs pc sp x p v hl0 hguard hdisj)

/-- The five statements PUSH_MEM_TOKEN_OFFSET runs before its spill: read the whole operand word, take
    the token byte from it, take the u32 offset from bytes 1..4, advance the cursor by FIVE, initialise
    'q_ptr', and resolve the token to 'MPTR + q_off' in each case. Verbatim the first six elements of
    'GenAst.qArmBodyPushMemTokenOffset' ('GenAstQvm.lean:156'). -/
def qArmPfx_pushMemTokenOffset (program : QuotientProgram) (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])),
   (ylet "q_token" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])),
   (ylet "q_off" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 216), (yvar "q_word")]), (ylit 4294967295)])),
   (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])),
   (ylet "q_ptr" (ylit 0)),
   (Stmt.switch (yvar "q_token") ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (some [(yexpr (ycall "q_program_fail" []))]))]

/-- **PUSH_MEM_TOKEN_OFFSET STEPS ACROSS ITS SPILL.** Same shape as the token arm; the pointer it reads
    through is 'L_0_MPTR + q_off', so that is the window the disjointness speaks about. -/
theorem qArmRun_pushMemTokenOffset_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc sp x : U256) (ow p v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 1)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_l0 : VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p))
    (hbyte : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0)
    (hoff : (((loadWord st.memory pc.toNat) >>> 216) &&& BitVec.ofNat 256 4294967295) = BitVec.ofNat 256 ow)
    (hload : loadWord st.memory (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat = BitVec.ofNat 256 v)
    (hl0 : program.memUsage.l0 = true)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemTokenOffset ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat 32) .normal := by
  have a1 :
    Step (D := Bridge.Dialect c g) funs V st (.args []) (.eres (.vals [] st)) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x2 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc")) (.eres (.vals [pc] st)) :=
    Step.var (D := Bridge.Dialect c g) hget_pc
  have a3 :
    Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"]) (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc) (st2 := st) a1 x2
  have x4 :
    Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a3 (qbi_mload_at st st.memory pc rfl)
  have w5 :
    (touchMemory st pc.toNat 32).memory = st.memory :=
    Midfall.Yul.Word.touchMemory_memory st pc.toNat 32
  have s6 :
    Step (D := Bridge.Dialect c g) funs V st (.stmt (ylet "q_word" (yop Op.mload [yvar "q_pc"]))) (.sres (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal x4 rfl
  have g7 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne V "q_word" "L_0_MPTR" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "L_0_MPTR")]; exact hget_l0
  have g8 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_has_top" = some 1 :=
    by rw [venvGet_cons_ne V "q_word" "q_has_top" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_has_top")]; exact hget_ht
  have g9 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_word" "q_pc" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_pc")]; exact hget_pc
  have g10 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_sp" = some sp :=
    by rw [venvGet_cons_ne V "q_word" "q_sp" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_sp")]; exact hget_sp
  have g11 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_word" "q_top" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_top")]; exact hget_top
  have g12 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_cons_eq V "q_word" (loadWord st.memory pc.toNat)
  have a13 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x14 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g12
  have a15 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a13 x14
  have x16 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 0)) (.eres (.vals [BitVec.ofNat 256 0] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)
  have a17 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [ylit 0, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 0, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 0) (st2 := touchMemory st pc.toNat 32) a15 x16
  have x18 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.byte [ylit 0, yvar "q_word"])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a17 (qbi_byte0 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d19 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.byte [ylit 0, yvar "q_word"])) (.eres (.vals [BitVec.ofNat 256 tcq.mem.l0] (touchMemory st pc.toNat 32))) :=
    by rw [<- hbyte]; exact x18
  have s20 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.stmt (ylet "q_token" (yop Op.byte [ylit 0, yvar "q_word"]))) (.sres (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d19 rfl
  have g21 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" "L_0_MPTR" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "L_0_MPTR")]; exact g7
  have g22 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_has_top" = some 1 :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" "q_has_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_has_top")]; exact g8
  have g23 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" "q_pc" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_pc")]; exact g9
  have g24 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_sp" = some sp :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" "q_sp" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_sp")]; exact g10
  have g25 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" "q_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_top")]; exact g11
  have g26 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" "q_word" (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_token" ≠ "q_word")]; exact g12
  have g27 :
    VEnv.get (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    venvGet_cons_eq (("q_word", loadWord st.memory pc.toNat) :: V) "q_token" (BitVec.ofNat 256 tcq.mem.l0)
  have a28 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x29 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 4294967295)) (.eres (.vals [BitVec.ofNat 256 4294967295] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 4294967295)
  have a30 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 4294967295]) (.eres (.vals [BitVec.ofNat 256 4294967295] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 4294967295) (st2 := touchMemory st pc.toNat 32) a28 x29
  have a31 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x32 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a33 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a31 x32
  have x34 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 216)) (.eres (.vals [BitVec.ofNat 256 216] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 216)
  have a35 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 216, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 216, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 216) (st2 := touchMemory st pc.toNat 32) a33 x34
  have x36 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 216, yvar "q_word"])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 216)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a35 (qbi_shr216 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have a37 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yop Op.shr [ylit 216, yvar "q_word"], ylit 4294967295]) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 216), BitVec.ofNat 256 4294967295] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 4294967295]) (restvals := [BitVec.ofNat 256 4294967295]) (st1 := touchMemory st pc.toNat 32) (v := ((loadWord st.memory pc.toNat) >>> 216)) (st2 := touchMemory st pc.toNat 32) a30 x36
  have x38 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.and [yop Op.shr [ylit 216, yvar "q_word"], ylit 4294967295])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 216) &&& BitVec.ofNat 256 4294967295)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a37 (qbi_and (touchMemory st pc.toNat 32) ((loadWord st.memory pc.toNat) >>> 216) (BitVec.ofNat 256 4294967295))
  have d39 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.and [yop Op.shr [ylit 216, yvar "q_word"], ylit 4294967295])) (.eres (.vals [BitVec.ofNat 256 ow] (touchMemory st pc.toNat 32))) :=
    by rw [<- hoff]; exact x38
  have s40 :
    Step (D := Bridge.Dialect c g) funs (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.stmt (ylet "q_off" (yop Op.and [yop Op.shr [ylit 216, yvar "q_word"], ylit 4294967295]))) (.sres (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d39 rfl
  have g41 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "L_0_MPTR" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "L_0_MPTR")]; exact g21
  have g42 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_has_top" = some 1 :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "q_has_top" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "q_has_top")]; exact g22
  have g43 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "q_pc" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "q_pc")]; exact g23
  have g44 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_sp" = some sp :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "q_sp" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "q_sp")]; exact g24
  have g45 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "q_token" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "q_token")]; exact g27
  have g46 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "q_top" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "q_top")]; exact g25
  have g47 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" "q_word" (BitVec.ofNat 256 ow) (by decide : "q_off" ≠ "q_word")]; exact g26
  have g48 :
    VEnv.get (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_off" = some (BitVec.ofNat 256 ow) :=
    venvGet_cons_eq (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_off" (BitVec.ofNat 256 ow)
  have a49 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x50 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a51 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [ylit 5]) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a49 x50
  have x52 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g43
  have a53 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 5]) (.eres (.vals [pc, BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 5]) (restvals := [BitVec.ofNat 256 5]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a51 x52
  have x54 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 5])) (.eres (.vals [(pc + BitVec.ofNat 256 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a53 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 5))
  have s55 :
    Step (D := Bridge.Dialect c g) funs (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 5]))) (.sres (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 5)]) x54 (by rfl)
  have g56 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "L_0_MPTR" (pc + BitVec.ofNat 256 5) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "L_0_MPTR") g41
  have g57 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_has_top" = some 1 :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 5) 1 (by decide : "q_pc" ≠ "q_has_top") g42
  have g58 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_off" = some (BitVec.ofNat 256 ow) :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_off" (pc + BitVec.ofNat 256 5) (BitVec.ofNat 256 ow) (by decide : "q_pc" ≠ "q_off") g48
  have g59 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_sp" = some sp :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_sp" (pc + BitVec.ofNat 256 5) sp (by decide : "q_pc" ≠ "q_sp") g44
  have g60 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_token" (pc + BitVec.ofNat 256 5) (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_pc" ≠ "q_token") g45
  have g61 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" = some x :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_top" (pc + BitVec.ofNat 256 5) x (by decide : "q_pc" ≠ "q_top") g46
  have g62 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_word" (pc + BitVec.ofNat 256 5) (loadWord st.memory pc.toNat) (by decide : "q_pc" ≠ "q_word") g47
  have g63 :
    VEnv.get (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_pc" = some (pc + BitVec.ofNat 256 5) :=
    venvGet_set_same (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5) pc g43
  have x64 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (ylit 0)) (.eres (.vals [BitVec.ofNat 256 0] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)
  have s65 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.stmt (ylet "q_ptr" (ylit 0))) (.sres (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal x64 rfl
  have g66 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "L_0_MPTR" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "L_0_MPTR")]; exact g56
  have g67 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_has_top" = some 1 :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_has_top" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_has_top")]; exact g57
  have g68 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_off" = some (BitVec.ofNat 256 ow) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_off" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_off")]; exact g58
  have g69 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_pc" = some (pc + BitVec.ofNat 256 5) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_pc" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_pc")]; exact g63
  have g70 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_sp" = some sp :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_sp" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_sp")]; exact g59
  have g71 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_token" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_token")]; exact g60
  have g72 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_top" = some x :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_top" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_top")]; exact g61
  have g73 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_word" (BitVec.ofNat 256 0) (by decide : "q_ptr" ≠ "q_word")]; exact g62
  have g74 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" = some (BitVec.ofNat 256 0) :=
    venvGet_cons_eq (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" (BitVec.ofNat 256 0)
  have x75 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.expr (yvar "q_token")) (.eres (.vals [BitVec.ofNat 256 tcq.mem.l0] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g71
  have h76 :
    selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (some [(yexpr (ycall "q_program_fail" []))]) = [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :=
    by refine selectSwitch_head (D := Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (Literal.number tcq.mem.l0, [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])]) (some [(yexpr (ycall "q_program_fail" []))]) ?_
       rw [hl0]
       exact find?_head _ _ _ (decide_litValue_number_eq_self tcq.mem.l0)
  have a77 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x78 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.expr (yvar "q_off")) (.eres (.vals [BitVec.ofNat 256 ow] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g68
  have a79 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.args [yvar "q_off"]) (.eres (.vals [BitVec.ofNat 256 ow] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 ow) (st2 := touchMemory st pc.toNat 32) a77 x78
  have x80 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.expr (yvar "L_0_MPTR")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g66
  have a81 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.args [yvar "L_0_MPTR", yvar "q_off"]) (.eres (.vals [BitVec.ofNat 256 p, BitVec.ofNat 256 ow] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_off"]) (restvals := [BitVec.ofNat 256 ow]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 p) (st2 := touchMemory st pc.toNat 32) a79 x80
  have x82 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])) (.eres (.vals [(BitVec.ofNat 256 p + BitVec.ofNat 256 ow)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a81 (qbi_add (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p) (BitVec.ofNat 256 ow))
  have s83 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.stmt (yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_ptr"]) (vals := [(BitVec.ofNat 256 p + BitVec.ofNat 256 ow)]) x82 (by rfl)
  have g84 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "L_0_MPTR" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "L_0_MPTR" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "L_0_MPTR") g66
  have g85 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_has_top" = some 1 :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_has_top" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) 1 (by decide : "q_ptr" ≠ "q_has_top") g67
  have g86 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_off" = some (BitVec.ofNat 256 ow) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_off" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (BitVec.ofNat 256 ow) (by decide : "q_ptr" ≠ "q_off") g68
  have g87 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_pc" = some (pc + BitVec.ofNat 256 5) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_pc" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (pc + BitVec.ofNat 256 5) (by decide : "q_ptr" ≠ "q_pc") g69
  have g88 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" = some sp :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_sp" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) sp (by decide : "q_ptr" ≠ "q_sp") g70
  have g89 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_token" = some (BitVec.ofNat 256 tcq.mem.l0) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_token" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (BitVec.ofNat 256 tcq.mem.l0) (by decide : "q_ptr" ≠ "q_token") g71
  have g90 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_top" = some x :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_top" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) x (by decide : "q_ptr" ≠ "q_top") g72
  have g91 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_word" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (loadWord st.memory pc.toNat) (by decide : "q_ptr" ≠ "q_word") g73
  have g92 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_ptr" = some (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) :=
    venvGet_set_same (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (BitVec.ofNat 256 0) g74
  have b93 :
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])] :: funs) (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.stmts [yset "q_ptr" (yop Op.add [yvar "L_0_MPTR", yvar "q_off"])]) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) .normal) :=
    by exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow))) (st1 := (touchMemory st pc.toNat 32)) s83 (Step.seqNil (D := Bridge.Dialect c g))
  have k94 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.stmt (.block (selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (some [(yexpr (ycall "q_program_fail" []))])))) (.sres (restore (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow))) (touchMemory st pc.toNat 32) .normal) :=
    by refine Step.block (D := Bridge.Dialect c g) ?_
       rw [h76]
       exact b93
  have k95 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.stmt (.block (selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.mem.l0) ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (some [(yexpr (ycall "q_program_fail" []))])))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) .normal) :=
    by rw [restore_set] at k94
       exact k94
  have s96 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (touchMemory st pc.toNat 32) (.stmt (Stmt.switch (yvar "q_token") ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (some [(yexpr (ycall "q_program_fail" []))]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) .normal) :=
    Step.switchExec (D := Bridge.Dialect c g) x75 k95
  have hpre : ExecStmts (Bridge.Dialect c g) funs V st (qArmPfx_pushMemTokenOffset program tcq) (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) .normal := by
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_word", loadWord st.memory pc.toNat) :: V)) (st1 := (touchMemory st pc.toNat 32)) s6 ?_
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (st1 := (touchMemory st pc.toNat 32)) s20 ?_
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (st1 := (touchMemory st pc.toNat 32)) s40 ?_
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) (st1 := (touchMemory st pc.toNat 32)) s55 ?_
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)))) (st1 := (touchMemory st pc.toNat 32)) s65 ?_
    exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow))) (st1 := (touchMemory st pc.toNat 32)) s96 (Step.seqNil (D := Bridge.Dialect c g))
  have hsp2 : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) [qSpillStmt program] (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) .normal :=
    qSpill_run program funs (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) (touchMemory st pc.toNat 32) sp x g85 g88 g90 hguard
  have hmid2 : VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_ptr" = some (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" "q_ptr" (sp + BitVec.ofNat 256 32) (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)
      (by decide : ("q_sp" : Ident) ≠ "q_ptr") g92
  have hload2 : loadWord (qSpillState (touchMemory st pc.toNat 32) sp x).memory (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat = BitVec.ofNat 256 v := by
    rw [qSpillState_loadWord_below (touchMemory st pc.toNat 32) sp x
      (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) hdisj]
    exact hload
  have htail : ExecStmts (Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) qArmTail_fromPtr (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat 32) .normal :=
    qArmTail_fromPtr_run funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p + BitVec.ofNat 256 ow) (BitVec.ofNat 256 v)
      hmid2 hload2
  have hbody : GenAst.qArmBodyPushMemTokenOffset ctx program tcq
      = qArmPfx_pushMemTokenOffset program tcq ++ [qSpillStmt program] ++ qArmTail_fromPtr := by
    unfold GenAst.qArmBodyPushMemTokenOffset qArmPfx_pushMemTokenOffset qArmTail_fromPtr qSpillStmt
      qSpillBody
    rfl
  rw [hbody]
  exact qExec_append funs (qExec_append funs hpre hsp2) htail

theorem qArmValue_pushMemTokenOffset_spill {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (ow p v : Nat)
    (hl0 : program.memUsage.l0 = true)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat) :
    StmtsContract (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemTokenOffset ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p) ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0 ∧
        (((loadWord st.memory pc.toNat) >>> 216) &&& BitVec.ofNat 256 4294967295) = BitVec.ofNat 256 ow ∧
        loadWord st.memory (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) := by
  intro V st hpre
  have hrun := qArmRun_pushMemTokenOffset_spill ctx program tcq funs V st pc sp x ow p v hpre.1
    hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2.1
    hpre.2.2.2.2.2.2.2 hl0 hguard hdisj
  refine ⟨_, _, _, hrun, ⟨rfl, rfl, rfl, ?_⟩⟩
  rw [Midfall.Yul.Word.touchMemory_memory, qSpillState_loadWord_same]

theorem qArmValueAll_pushMemTokenOffset_spill {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (ow p v : Nat)
    (hl0 : program.memUsage.l0 = true)
    (hguard : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat) :
    StmtsContractAll (D := (Bridge.Dialect c g)) funs (GenAst.qArmBodyPushMemTokenOffset ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 1 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p) ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0 ∧
        (((loadWord st.memory pc.toNat) >>> 216) &&& BitVec.ofNat 256 4294967295) = BitVec.ofNat 256 ow ∧
        loadWord st.memory (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal ∧
        st' = (touchMemory (qSpillState (touchMemory st pc.toNat 32) sp x) (BitVec.ofNat 256 p + BitVec.ofNat 256 ow).toNat 32) ∧
        V' = (VEnv.set (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 0) :: (VEnv.set (("q_off", BitVec.ofNat 256 ow) :: (("q_token", BitVec.ofNat 256 tcq.mem.l0) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ow)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) ∧
        loadWord st'.memory sp.toNat = x) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushMemTokenOffset_spill ctx program tcq funs pc sp x ow p v hl0 hguard hdisj)


/-! ### 10. WHERE BINDINV'S DISCHARGE BITES - AND WHERE IT DOES NOT (SPILL2, item 3)

  SPILL section 6 named 'PG_spillSlotDisjoint' as the memory fact a spill contract needs and could not
  get. BINDINV discharged it ('MemoryPairs.lean:1364', 'spillSlotDisjoint_of_ordered') from the
  CONSTRUCTION ORDERING of the const and stack windows plus the arm's own 'b <= constMax' PRE, and proved
  that 'PG_spillArmTripleC' needs no OTHER named-but-unproved memory fact. This section wires that result
  into the spill layer: the ordering is CITED, never re-proved.

  WHICH FACE, STATED PLAINLY. 'spillSlotDisjoint_of_ordered' is stated of a GENERIC 'program' handed its
  pointer equations as hypotheses, so it is face-free and this file uses it directly. What BINDINV proved
  at the RENDER face is 'qvmWindows_disjoint_of_generated', whose hypothesis is the PLAN equation
  'R.plan.quotient = some q' - it delivers the ordering for 'q.program'. The MODEL face
  ('R.model.quotientProgram = some program') is NOT proved anywhere, so a row-level use of these lemmas
  for the program the MODEL interpreter carries must still be handed the ordering, or be moved to the
  plan face. Nothing below assumes the model face exists: both lemmas take 'PG_qvmWindowsOrdered program'
  as an ordinary hypothesis and say what follows from it.

  WHAT IT DOES NOT COVER. 'PG_qvmWindowsOrdered' orders the CONST TABLE window below the stack. The two
  token arms read through 'L_0_MPTR' (plus 'q_off'), which is not a field of 'QuotientProgram' at all -
  it is a register the prologue binds from the memory layout ('VmTypes.lean:1218'). So BINDINV's lemma
  does NOT discharge the token arms' 'hdisj', and their contracts keep it as an arm-lemma hypothesis.
  That is a different window pair, not the same gap reopened.  PRECISE SOURCE (SPILL2): 'L_0_MPTR' is one
  of the nine symbolic memory tokens of 'quotientMemTokenTable' ('VmTypes.lean:1217-1227'), bound as a
  VM register; 'QuotientProgram' has no token-MPTR field at all ('Models.lean:666-690' lists constMptr,
  evalNumerMptr, traceIdMptr, selectorPowerMptr, stackMptr, programMptr and nothing else of the kind).
  does NOT discharge the token arms' 'hdisj', and their contracts keep it as an arm-lemma hypothesis.
  That is a different window pair, not the same gap reopened. -/

/-- **THE CONST-SLOT DISJOINTNESS IS NOW A THEOREM.** One line, citing BINDINV: the ordering, the fit
    clauses, the two pointer equations and the arm's own 'b <= constMax' PRE give 'PG_spillSlotDisjoint'
    at the base pointer. No ordering is re-proved here. -/
theorem spillDisjoint_pushConst_of_ordered (program : QuotientProgram) (cb sp : U256) (b : Nat)
    (hord : Midfall.LoweringV3.MemoryPairs.PG_qvmWindowsOrdered program)
    (hfit : Midfall.LoweringV3.quotientProgramFits program)
    (hcb : cb = BitVec.ofNat 256 program.constMptr)
    (hsp : sp = BitVec.ofNat 256 program.stackMptr)
    (hb : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    PG_spillSlotDisjoint program cb sp b :=
  Midfall.LoweringV3.MemoryPairs.spillSlotDisjoint_of_ordered program cb sp b hord hfit hcb hsp hb

/-- **... AND IT SURVIVES DEPTH.** A spill at depth 'n' writes at 'stackMptr + 32 * n', which is FURTHER
    above the const table, not nearer it, so the same ordering gives the same disjointness at every depth
    the invariant reaches. The ordering is BINDINV's theorem, cited unchanged; only the pointer arithmetic
    is done here, and it is the same arithmetic, one clause longer. -/
theorem spillDisjoint_atDepth_of_ordered (program : QuotientProgram) (cb sp : U256) (b n : Nat)
    (hord : Midfall.LoweringV3.MemoryPairs.PG_qvmWindowsOrdered program)
    (hfit : Midfall.LoweringV3.quotientProgramFits program)
    (hcb : cb = BitVec.ofNat 256 program.constMptr)
    (hsp : sp = BitVec.ofNat 256 (program.stackMptr + 32 * n))
    (hwrap : program.stackMptr + 32 * n < 2 ^ 256)
    (hb : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    PG_spillSlotDisjoint program cb sp b := by
  obtain ⟨_, hfitc, hstk, hlast, _, _, _⟩ := hfit
  have hord' : program.constMptr + 32 * (program.guards.constMax + 1) ≤ program.stackMptr := hord
  have hw : 2 ^ 5 = 32 := by norm_num
  have hcmax : program.guards.constMax < 2 ^ 256 := by omega
  have hcm : (BitVec.ofNat 256 program.constMptr).toNat = program.constMptr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcmt : (BitVec.ofNat 256 program.guards.constMax).toNat = program.guards.constMax := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcmax
  have hb1 : (BitVec.ofNat 256 b).toNat ≤ program.guards.constMax := by
    rw [← hcmt]; exact hb
  have hbx : ((BitVec.ofNat 256 b) <<< 5).toNat = (BitVec.ofNat 256 b).toNat * 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hw]
    refine Nat.mod_eq_of_lt ?_
    have : (BitVec.ofNat 256 b).toNat * 32 ≤ program.guards.constMax * 32 :=
      Nat.mul_le_mul_right 32 hb1
    omega
  have hsum : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat
      = program.constMptr + (BitVec.ofNat 256 b).toNat * 32 := by
    rw [hcb, BitVec.toNat_add, hcm, hbx]
    refine Nat.mod_eq_of_lt ?_
    have : (BitVec.ofNat 256 b).toNat * 32 ≤ program.guards.constMax * 32 :=
      Nat.mul_le_mul_right 32 hb1
    omega
  have hspn : sp.toNat = program.stackMptr + 32 * n := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hwrap
  show (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 ≤ sp.toNat ∨
    sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat
  rw [hsum, hspn]
  exact Or.inl (by omega)


/-! ### 11. THE INVARIANT STEPS ACROSS THE OTHER TWO SPILL SHAPES (SPILL2, item 2)

  'qStackCorr_pushConst' is STKINV's step shape: two cases, because a push does not pop - at the empty
  reference stack the arm takes the branch the published triple already describes, and at a live cached
  top it takes the spill branch. These two instances are that shape for the two arms whose spill reads
  through a POINTER rather than the const-table slot, each built on its own landed spill contract and
  on 'qSpilled_spill_below' for the tail. Nothing new is needed from the arm layer beyond what section 9

  SPILL2 COUNT (printed, not asserted). Five instances land in this section - 'pushConstU8',
  'pushMemU16', 'pushMemToken', 'pushMemLiteral' and 'pushMemTokenOffset' - and with SPILL's
  'pushConst' that is ALL SIX push arms: every push arm now steps across its own spill inside
  'QStackCorr'. The only arms still outside are the four LIMB arms, excluded behind
  'PG_limbCountAgrees' exactly as IDSEG, STKINV and SPILL excluded them. 'pushConstU8' needs no
  named hypothesis at all; 'pushMemLiteral' and 'pushMemTokenOffset' compose the reference's u32
  address from its operand bytes inside their own statements, so no new tie lemma was needed.
  lands and what SPILL already published. -/

/-- **THE INVARIANT STEPS ACROSS A SPILL - PUSH_MEM_U16.** A DIFFERENT SPILL SHAPE from 'pushConst':
    the word the arm caches after the spill is read through the pointer decoded from the program word,
    not through the const-table slot, so the disjointness it needs is about the LITERAL window and the
    stack - which is why BINDINV's const-window ordering does not discharge it (section 10). 'hlit' is the
    reference's own literal read and 'hv' says the word is canonical: 'QuotientRefMemory' is a free cache
    list and 'QVMFr' is just 'Nat' ('VmReference.lean:253, 410-414'), so nothing in the tree forces a
    literal-domain read below the modulus. That is SPILL section 7's literal-domain member of the
    canonicity family, named here as an ARM-LEMMA hypothesis and nowhere else (RULES). -/
theorem qStackCorr_pushMemU16 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (b₀ b₁ v : Nat)
    (pc sp top : U256)
    (hbytes : (loadWord st.memory pc.toNat) >>> 240 = BitVec.ofNat 256 (b₀ * 256 + b₁))
    (hread : loadWord st.memory (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat = BitVec.ofNat 256 v)
    (hlit : (mem.literal (b₀ * 256 + b₁)).1 = (BitVec.ofNat 256 v).toNat)
    (hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus)
    (hdisj : (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat)
    (hfit : quotientProgramFits program)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemU16 ctx program tcq) V' st' o)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPushMemU16 :: b₀ :: b₁ :: rest) consts 0
      qOpPushMemU16 stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, spb, topb, hspb, htopb, heq0, hwrap0, hcase⟩ := hcorr
  have esp : sp = spb := Option.some.inj (hsp.symm.trans hspb)
  have etop : top = topb := Option.some.inj (htop.symm.trans htopb)
  subst esp; subst etop
  have hspn : 32 * n ≤ sp.toNat := by
    rw [heq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap0]
    omega
  have hstep' : Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemU16, b₀, b₁] ++ rest)
      consts 0 qOpPushMemU16 stk mem = .ok s := hstep
  rw [rtie_pushMemU16 b₀ b₁ rest consts (BitVec.ofNat 256 v) stk mem hlit] at hstep'
  obtain rfl := Except.ok.inj hstep'
  rcases hcase with ⟨h0, hnil, hn0⟩ | ⟨h1, hcan, hshape, hspill⟩
  · -- the empty reference stack: the arm takes the NO-SPILL branch published by QARMS
    subst hn0
    obtain ⟨hnormal, hst'', hV''⟩ := qArmValueAll_pushMemU16 hc hg ctx program tcq funs pc sp top (b₀ * 256 + b₁) v V st ⟨hget_pc, hsp, h0, htop, hbytes, hread⟩ V' st' o hrun
    subst hnormal; subst hV''; subst hst''
    refine ⟨rfl, ⟨0, sp, BitVec.ofNat 256 v, ?_, ?_, heq0, QStackNoWrap_zero_of_fits program hfit,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_sp" (BitVec.ofNat 256 (b₀ * 256 + b₁)) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (hsp)))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 (b₀ * 256 + b₁)) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (htop)))))
    · exact (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (0) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (0) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) (0) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 (b₀ * 256 + b₁)) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (h0)))))
    · rw [hnil]
      rfl
    · intro w hw
      have hq : ∀ (X : EvmState), qSpilled X 0 sp = [] := fun X => rfl
      rw [hq] at hw
      cases hw
  · -- the live cached top: the SPILL branch this card lands
    obtain ⟨hnormal, hst'', hV'', hspillsp⟩ := qArmValueAll_pushMemU16_spill hc hg ctx program tcq funs pc sp top (b₀ * 256 + b₁) v hroom hdisj V st ⟨hget_pc, hsp, h1, htop, hbytes, hread⟩ V' st' o hrun
    subst hnormal
    have htails : qSpilled st' (n + 1) (sp + BitVec.ofNat 256 32) = top :: qSpilled st n sp := by
      rw [qSpilled_succ, BitVec.add_sub_cancel, hspillsp]
      suffices h : qSpilled st' n sp = qSpilled st n sp by rw [h]
      rw [hst'', qSpilled_touchMemory,
          qSpilled_spill_below (touchMemory st pc.toNat 32) sp top n sp (le_refl sp.toNat) hspn,
          qSpilled_touchMemory]
    refine ⟨rfl, ⟨n + 1, sp + BitVec.ofNat 256 32, BitVec.ofNat 256 v, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32) (sp) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_sp" (BitVec.ofNat 256 (b₀ * 256 + b₁)) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (hsp))))))
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) (top) (by decide : ("q_sp" : Ident) ≠ "q_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 (b₀ * 256 + b₁)) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (htop))))))
    · rw [heq0]
      exact spill_add_word program.stackMptr n
    · exact spill_room_toNat program n sp heq0 hwrap0 hfit.2.2.2.1 hroom
    · rw [hV'']
      exact (venvGet_set_same (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (1) (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (1) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) (1) (by decide : ("q_sp" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 (b₀ * 256 + b₁))) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) (1) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 (b₀ * 256 + b₁)) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (h1))))))
    · rw [hshape, htails, List.map_cons]
    · intro w hw
      rw [htails] at hw
      cases List.mem_cons.mp hw with
      | inl heq => exact heq ▸ hcan
      | inr hw2 => exact hspill w hw2


/-- **THE INVARIANT STEPS ACROSS A SPILL - PUSH_MEM_TOKEN.** The third shape: the arm resolves its
    pointer through the nine-way 'Stmt.switch' over 'program.memUsage' and then reads through it, so the
    spill sits BETWEEN the switch and the read. 'hv' is the token-domain member of the same canonicity
    family as the literal one above, for the same reason: 'mem.token' is a cache lookup over 'Nat'. -/
theorem qStackCorr_pushMemToken {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (t p v : Nat)
    (pc sp top : U256)
    (hget_l0 : VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p))
    (hbyte : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0)
    (hread : loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
    (hlit : (mem.token t 0).1 = (BitVec.ofNat 256 v).toNat)
    (hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus)
    (hl0 : program.memUsage.l0 = true)
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat)
    (hfit : quotientProgramFits program)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemToken ctx program tcq) V' st' o)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPushMemToken :: t :: rest) consts 0
      qOpPushMemToken stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, spb, topb, hspb, htopb, heq0, hwrap0, hcase⟩ := hcorr
  have esp : sp = spb := Option.some.inj (hsp.symm.trans hspb)
  have etop : top = topb := Option.some.inj (htop.symm.trans htopb)
  subst esp; subst etop
  have hspn : 32 * n ≤ sp.toNat := by
    rw [heq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap0]
    omega
  have hstep' : Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemToken, t] ++ rest)
      consts 0 qOpPushMemToken stk mem = .ok s := hstep
  rw [rtie_pushMemToken t rest consts (BitVec.ofNat 256 v) stk mem hlit] at hstep'
  obtain rfl := Except.ok.inj hstep'
  rcases hcase with ⟨h0, hnil, hn0⟩ | ⟨h1, hcan, hshape, hspill⟩
  · -- the empty reference stack: the arm takes the NO-SPILL branch published by QARMS
    subst hn0
    obtain ⟨hnormal, hst'', hV''⟩ := qArmValueAll_pushMemToken hc hg ctx program tcq funs pc sp top p v hl0 V st ⟨hget_pc, hsp, h0, htop, hget_l0, hbyte, hread⟩ V' st' o hrun
    subst hnormal; subst hV''; subst hst''
    refine ⟨rfl, ⟨0, sp, BitVec.ofNat 256 v, ?_, ?_, heq0, QStackNoWrap_zero_of_fits program hfit,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_sp" (BitVec.ofNat 256 p) (sp) (by decide : ("q_ptr" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_sp" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (venvGet_set_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 1) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "q_token" "q_sp" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_sp")) (hsp)))))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_top" (BitVec.ofNat 256 p) (top) (by decide : ("q_ptr" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (venvGet_set_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 1) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "q_token" "q_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_top")) (htop)))))))
    · exact (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (0) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (0) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_has_top" (BitVec.ofNat 256 p) (0) (by decide : ("q_ptr" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_has_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (venvGet_set_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 1) (0) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "q_token" "q_has_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_has_top")) (h0)))))))
    · rw [hnil]
      rfl
    · intro w hw
      have hq : ∀ (X : EvmState), qSpilled X 0 sp = [] := fun X => rfl
      rw [hq] at hw
      cases hw
  · -- the live cached top: the SPILL branch this card lands
    obtain ⟨hnormal, hst'', hV'', hspillsp⟩ := qArmValueAll_pushMemToken_spill hc hg ctx program tcq funs pc sp top p v hl0 hroom hdisj V st ⟨hget_pc, hsp, h1, htop, hget_l0, hbyte, hread⟩ V' st' o hrun
    subst hnormal
    have htails : qSpilled st' (n + 1) (sp + BitVec.ofNat 256 32) = top :: qSpilled st n sp := by
      rw [qSpilled_succ, BitVec.add_sub_cancel, hspillsp]
      suffices h : qSpilled st' n sp = qSpilled st n sp by rw [h]
      rw [hst'', qSpilled_touchMemory,
          qSpilled_spill_below (touchMemory st pc.toNat 32) sp top n sp (le_refl sp.toNat) hspn,
          qSpilled_touchMemory]
    refine ⟨rfl, ⟨n + 1, sp + BitVec.ofNat 256 32, BitVec.ofNat 256 v, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32) (sp) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_sp" (BitVec.ofNat 256 p) (sp) (by decide : ("q_ptr" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_sp" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (venvGet_set_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 1) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "q_token" "q_sp" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_sp")) (hsp))))))))
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) (top) (by decide : ("q_sp" : Ident) ≠ "q_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_top" (BitVec.ofNat 256 p) (top) (by decide : ("q_ptr" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (venvGet_set_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 1) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "q_token" "q_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_top")) (htop))))))))
    · rw [heq0]
      exact spill_add_word program.stackMptr n
    · exact spill_room_toNat program n sp heq0 hwrap0 hfit.2.2.2.1 hroom
    · rw [hV'']
      exact (venvGet_set_same (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (1) (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (1) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" (BitVec.ofNat 256 p)) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) (1) (by decide : ("q_sp" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1))) "q_ptr" "q_has_top" (BitVec.ofNat 256 p) (1) (by decide : ("q_ptr" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" (pc + BitVec.ofNat 256 1)) "q_ptr" "q_has_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (venvGet_set_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 1) (1) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "q_token" "q_has_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_has_top")) (h1))))))))
    · rw [hshape, htails, List.map_cons]
    · intro w hw
      rw [htails] at hw
      cases List.mem_cons.mp hw with
      | inl heq => exact heq ▸ hcan
      | inr hw2 => exact hspill w hw2



/-- **THE INVARIANT STEPS ACROSS A SPILL - PUSH_CONST_U8.** The fourth push arm across its own spill, and
    the only one of the four that needs NO new named hypothesis: the arm has no 'constMax' guard at all
    (SPILL section 7), and 'spill_constAt_ok_lt' makes the const-table read canonical on its own, so the
    canonicity clause of 'QStackCorrWith' is discharged rather than assumed. The spill shape is the
    const-slot one, as in 'pushConst'. -/
theorem qStackCorr_pushConstU8 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (b₀ v : Nat)
    (pc cb sp top : U256)
    (hfit : quotientProgramFits program)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hbytes : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b₀)
    (hread : loadWord st.memory (cb + ((BitVec.ofNat 256 b₀) <<< 5)).toNat = BitVec.ofNat 256 v)
    (hv₀ : Midfall.Generator.constAt consts b₀ 0 = .ok v)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (cb + ((BitVec.ofNat 256 b₀) <<< 5)).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (cb + ((BitVec.ofNat 256 b₀) <<< 5)).toNat)
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushConstU8 ctx program tcq) V' st' o)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPushConstU8 :: b₀ :: rest) consts 0
      qOpPushConstU8 stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, spb, topb, hspb, htopb, heq0, hwrap0, hcase⟩ := hcorr
  have esp : sp = spb := Option.some.inj (hsp.symm.trans hspb)
  have etop : top = topb := Option.some.inj (htop.symm.trans htopb)
  subst esp; subst etop
  have hvx : v < qvmFrModulus := spill_constAt_ok_lt consts b₀ 0 v hv₀
  have hvc : (BitVec.ofNat 256 v).toNat = v := rtie_ofNat_toNat v hvx
  have hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus := by rw [hvc]; exact hvx
  have hspn : 32 * n ≤ sp.toNat := by
    rw [heq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap0]
    omega
  rw [← hvc] at hv₀
  have hstep' : Midfall.Generator.evalQuotientIdentityStep ([qOpPushConstU8, b₀] ++ rest) consts 0
      qOpPushConstU8 stk mem = .ok s := hstep
  rw [rtie_pushConstU8 b₀ rest consts (BitVec.ofNat 256 v) stk mem hv₀] at hstep'
  obtain rfl := Except.ok.inj hstep'
  rcases hcase with ⟨h0, hnil, hn0⟩ | ⟨h1, hcan, hshape, hspill⟩
  · -- the empty reference stack: the arm takes the NO-SPILL branch published by QARMS
    subst hn0
    obtain ⟨hnormal, hst'', hV''⟩ := qArmValueAll_pushConstU8 hc hg ctx program tcq funs pc cb sp top b₀ v V st ⟨hget_pc, hsp, h0, htop, hget_cb, hbytes, hread⟩ V' st' o hrun
    subst hnormal; subst hV''; subst hst''
    refine ⟨rfl, ⟨0, sp, BitVec.ofNat 256 v, ?_, ?_, heq0, QStackNoWrap_zero_of_fits program hfit,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 1) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp) (by decide : ("q_top" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_sp")) (hsp)))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_pc" : Ident) ≠ "q_top") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v) (top) (Eq.trans (venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_top")) (htop)))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 1) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (venvGet_set_same (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (0) (venvGet_set_ne (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_top" "q_has_top" (BitVec.ofNat 256 v) (0) (by decide : ("q_top" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_has_top")) (h0)))))
    · rw [hnil]
      rfl
    · intro w hw
      have hq : ∀ (X : EvmState), qSpilled X 0 sp = [] := fun X => rfl
      rw [hq] at hw
      cases hw
  · -- the live cached top: the SPILL branch this card lands
    obtain ⟨hnormal, hst'', hV'', hspillsp⟩ := qArmValueAll_pushConstU8_spill hc hg ctx program tcq funs pc cb sp top b₀ v hroom hdisj V st ⟨hget_pc, hsp, h1, htop, hget_cb, hbytes, hread⟩ V' st' o hrun
    subst hnormal
    have htails : qSpilled st' (n + 1) (sp + BitVec.ofNat 256 32) = top :: qSpilled st n sp := by
      rw [qSpilled_succ, BitVec.add_sub_cancel, hspillsp]
      suffices h : qSpilled st' n sp = qSpilled st n sp by rw [h]
      rw [hst'', qSpilled_touchMemory,
          qSpilled_spill_below (touchMemory st pc.toNat 32) sp top n sp (le_refl sp.toNat) hspn,
          qSpilled_touchMemory]
    refine ⟨rfl, ⟨n + 1, sp + BitVec.ofNat 256 32, BitVec.ofNat 256 v, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32) (by decide : ("q_pc" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32) (sp) (Eq.trans (venvGet_cons_ne V "qconst" "q_sp" (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_sp")) (hsp))))))
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_pc" : Ident) ≠ "q_top") (venvGet_set_ne (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) (top) (by decide : ("q_sp" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_top")) (htop))))))
    · rw [heq0]
      exact spill_add_word program.stackMptr n
    · exact spill_room_toNat program n sp heq0 hwrap0 hfit.2.2.2.1 hroom
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 1) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (venvGet_set_same (VEnv.set (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (1) (venvGet_set_ne (VEnv.set (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (1) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("qconst", (BitVec.ofNat 256 b₀)) :: V) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) (1) (by decide : ("q_sp" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b₀) (by decide : ("qconst" : Ident) ≠ "q_has_top")) (h1))))))
    · rw [hshape, htails, List.map_cons]
    · intro w hw
      rw [htails] at hw
      cases List.mem_cons.mp hw with
      | inl heq => exact heq ▸ hcan
      | inr hw2 => exact hspill w hw2




/-- **THE INVARIANT STEPS ACROSS A SPILL - PUSH_MEM_LITERAL.** The u32-pointer twin of 'pushMemU16': same
    spill shape, four operand bytes instead of two, and the cursor advances by 'tcq.byteU32Bytes'. The
    reference's address is the composed u32, so the instance composes the bytes once in its own statement
    and hands the same number to the published tie - no new tie is needed. -/
theorem qStackCorr_pushMemLiteral {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (b₀ b₁ b₂ b₃ v : Nat)
    (pc sp top : U256)
    (hbytes : (loadWord st.memory pc.toNat) >>> 224 = BitVec.ofNat 256 (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))))
    (hread : loadWord st.memory (BitVec.ofNat 256 (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))).toNat = BitVec.ofNat 256 v)
    (hlit : (mem.literal (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))).1 = (BitVec.ofNat 256 v).toNat)
    (hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus)
    (hdisj : (BitVec.ofNat 256 (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))).toNat)
    (hfit : quotientProgramFits program)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemLiteral ctx program tcq) V' st' o)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPushMemLiteral :: b₀ :: b₁ :: b₂ :: b₃ :: rest) consts 0
      qOpPushMemLiteral stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, spb, topb, hspb, htopb, heq0, hwrap0, hcase⟩ := hcorr
  have esp : sp = spb := Option.some.inj (hsp.symm.trans hspb)
  have etop : top = topb := Option.some.inj (htop.symm.trans htopb)
  subst esp; subst etop
  have hspn : 32 * n ≤ sp.toNat := by
    rw [heq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap0]
    omega
  have hstep' : Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemLiteral, b₀, b₁, b₂, b₃] ++ rest) consts 0
      qOpPushMemLiteral stk mem = .ok s := hstep
  rw [rtie_pushMemLiteral b₀ b₁ b₂ b₃ rest consts (BitVec.ofNat 256 v) stk mem hlit] at hstep'
  obtain rfl := Except.ok.inj hstep'
  rcases hcase with ⟨h0, hnil, hn0⟩ | ⟨h1, hcan, hshape, hspill⟩
  · -- the empty reference stack: the arm takes the NO-SPILL branch published by QARMS
    subst hn0
    obtain ⟨hnormal, hst'', hV''⟩ := qArmValueAll_pushMemLiteral hc hg ctx program tcq funs pc sp top (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) v V st ⟨hget_pc, hsp, h0, htop, hbytes, hread⟩ V' st' o hrun
    subst hnormal; subst hV''; subst hst''
    refine ⟨rfl, ⟨0, sp, BitVec.ofNat 256 v, ?_, ?_, heq0, QStackNoWrap_zero_of_fits program hfit,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_sp" (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (hsp)))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (htop)))))
    · exact (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (0) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (0) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (0) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (h0)))))
    · rw [hnil]
      rfl
    · intro w hw
      have hq : ∀ (X : EvmState), qSpilled X 0 sp = [] := fun X => rfl
      rw [hq] at hw
      cases hw
  · -- the live cached top: the SPILL branch this card lands
    obtain ⟨hnormal, hst'', hV'', hspillsp⟩ := qArmValueAll_pushMemLiteral_spill hc hg ctx program tcq funs pc sp top (((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) v hroom hdisj V st ⟨hget_pc, hsp, h1, htop, hbytes, hread⟩ V' st' o hrun
    subst hnormal
    have htails : qSpilled st' (n + 1) (sp + BitVec.ofNat 256 32) = top :: qSpilled st n sp := by
      rw [qSpilled_succ, BitVec.add_sub_cancel, hspillsp]
      suffices h : qSpilled st' n sp = qSpilled st n sp by rw [h]
      rw [hst'', qSpilled_touchMemory,
          qSpilled_spill_below (touchMemory st pc.toNat 32) sp top n sp (le_refl sp.toNat) hspn,
          qSpilled_touchMemory]
    refine ⟨rfl, ⟨n + 1, sp + BitVec.ofNat 256 32, BitVec.ofNat 256 v, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32) (sp) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" "q_sp" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_sp" (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (hsp))))))
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) (top) (by decide : ("q_sp" : Ident) ≠ "q_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (htop))))))
    · rw [heq0]
      exact spill_add_word program.stackMptr n
    · exact spill_room_toNat program n sp heq0 hwrap0 hfit.2.2.2.1 hroom
    · rw [hV'']
      exact (venvGet_set_same (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (1) (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (1) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) (1) (by decide : ("q_sp" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃)))) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (1) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 ((((b₀ * 256 + b₁) * 256 + b₂) * 256 + b₃))) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (h1))))))
    · rw [hshape, htails, List.map_cons]
    · intro w hw
      rw [htails] at hw
      cases List.mem_cons.mp hw with
      | inl heq => exact heq ▸ hcan
      | inr hw2 => exact hspill w hw2


/-- **THE INVARIANT STEPS ACROSS A SPILL - PUSH_MEM_TOKEN_OFFSET.** The last of the six push arms: the
    spill sits between the nine-way switch and a read through 'L_0_MPTR + q_off'. As in 'pushMemLiteral'
    the instance composes the four operand bytes into the u32 the published tie asks for. -/
theorem qStackCorr_pushMemTokenOffset {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V' : VEnv (Bridge.Dialect c g)) (st st' : EvmState) (o : Outcome)
    (rest : List Nat) (consts : List Word256) (mem : QuotientRefMemory)
    (stk : List QVMFr) (s : IdentityStep)
    (t o₀ o₁ o₂ o₃ p v : Nat)
    (pc sp top : U256)
    (hget_l0 : VEnv.get V "L_0_MPTR" = some (BitVec.ofNat 256 p))
    (hbyte : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0)
    (hoff : (((loadWord st.memory pc.toNat) >>> 216) &&& BitVec.ofNat 256 4294967295) = BitVec.ofNat 256 (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))))
    (hread : loadWord st.memory (BitVec.ofNat 256 p + BitVec.ofNat 256 (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))).toNat = BitVec.ofNat 256 v)
    (hlit : (mem.token t (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))).1 = (BitVec.ofNat 256 v).toNat)
    (hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus)
    (hl0 : program.memUsage.l0 = true)
    (hdisj : (BitVec.ofNat 256 p + BitVec.ofNat 256 (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (BitVec.ofNat 256 p + BitVec.ofNat 256 (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))).toNat)
    (hfit : quotientProgramFits program)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hsp : VEnv.get V "q_sp" = some sp)
    (htop : VEnv.get V "q_top" = some top)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemTokenOffset ctx program tcq) V' st' o)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (qOpPushMemTokenOffset :: t :: o₀ :: o₁ :: o₂ :: o₃ :: rest) consts 0
      qOpPushMemTokenOffset stk mem = .ok s) :
    o = .normal ∧ QStackCorr (c := c) (g := g) program V' st' s.stack := by
  obtain ⟨n, spb, topb, hspb, htopb, heq0, hwrap0, hcase⟩ := hcorr
  have esp : sp = spb := Option.some.inj (hsp.symm.trans hspb)
  have etop : top = topb := Option.some.inj (htop.symm.trans htopb)
  subst esp; subst etop
  have hspn : 32 * n ≤ sp.toNat := by
    rw [heq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwrap0]
    omega
  have hstep' : Midfall.Generator.evalQuotientIdentityStep ([qOpPushMemTokenOffset, t, o₀, o₁, o₂, o₃] ++ rest) consts 0
      qOpPushMemTokenOffset stk mem = .ok s := hstep
  rw [rtie_pushMemTokenOffset t o₀ o₁ o₂ o₃ rest consts (BitVec.ofNat 256 v) stk mem hlit] at hstep'
  obtain rfl := Except.ok.inj hstep'
  rcases hcase with ⟨h0, hnil, hn0⟩ | ⟨h1, hcan, hshape, hspill⟩
  · -- the empty reference stack: the arm takes the NO-SPILL branch published by QARMS
    subst hn0
    obtain ⟨hnormal, hst'', hV''⟩ := qArmValueAll_pushMemTokenOffset hc hg ctx program tcq funs pc sp top (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) p v hl0 V st ⟨hget_pc, hsp, h0, htop, hget_l0, hbyte, hoff, hread⟩ V' st' o hrun
    subst hnormal; subst hV''; subst hst''
    refine ⟨rfl, ⟨0, sp, BitVec.ofNat 256 v, ?_, ?_, heq0, QStackNoWrap_zero_of_fits program hfit,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_sp" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (sp) (by decide : ("q_ptr" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_sp" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (venvGet_set_ne (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" "q_sp" (pc + BitVec.ofNat 256 5) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V)) "q_off" "q_sp" (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (by decide : ("q_off" : Ident) ≠ "q_sp")) (Eq.trans (venvGet_cons_ne (("q_word", (loadWord st.memory pc.toNat)) :: V) "q_token" "q_sp" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_sp")) (Eq.trans (venvGet_cons_ne V "q_word" "q_sp" (loadWord st.memory pc.toNat) (by decide : ("q_word" : Ident) ≠ "q_sp")) (hsp)))))))))
    · exact (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_top" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (top) (by decide : ("q_ptr" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (venvGet_set_ne (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" "q_top" (pc + BitVec.ofNat 256 5) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V)) "q_off" "q_top" (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (by decide : ("q_off" : Ident) ≠ "q_top")) (Eq.trans (venvGet_cons_ne (("q_word", (loadWord st.memory pc.toNat)) :: V) "q_token" "q_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_top")) (Eq.trans (venvGet_cons_ne V "q_word" "q_top" (loadWord st.memory pc.toNat) (by decide : ("q_word" : Ident) ≠ "q_top")) (htop)))))))))
    · exact (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (0) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_top" "q_has_top" (BitVec.ofNat 256 v) (0) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_has_top" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (0) (by decide : ("q_ptr" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_has_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (venvGet_set_ne (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 5) (0) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V)) "q_off" "q_has_top" (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (by decide : ("q_off" : Ident) ≠ "q_has_top")) (Eq.trans (venvGet_cons_ne (("q_word", (loadWord st.memory pc.toNat)) :: V) "q_token" "q_has_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_has_top")) (Eq.trans (venvGet_cons_ne V "q_word" "q_has_top" (loadWord st.memory pc.toNat) (by decide : ("q_word" : Ident) ≠ "q_has_top")) (h0)))))))))
    · rw [hnil]
      rfl
    · intro w hw
      have hq : ∀ (X : EvmState), qSpilled X 0 sp = [] := fun X => rfl
      rw [hq] at hw
      cases hw
  · -- the live cached top: the SPILL branch this card lands
    obtain ⟨hnormal, hst'', hV'', hspillsp⟩ := qArmValueAll_pushMemTokenOffset_spill hc hg ctx program tcq funs pc sp top (((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) p v hl0 hroom hdisj V st ⟨hget_pc, hsp, h1, htop, hget_l0, hbyte, hoff, hread⟩ V' st' o hrun
    subst hnormal
    have htails : qSpilled st' (n + 1) (sp + BitVec.ofNat 256 32) = top :: qSpilled st n sp := by
      rw [qSpilled_succ, BitVec.add_sub_cancel, hspillsp]
      suffices h : qSpilled st' n sp = qSpilled st n sp by rw [h]
      rw [hst'', qSpilled_touchMemory,
          qSpilled_spill_below (touchMemory st pc.toNat 32) sp top n sp (le_refl sp.toNat) hspn,
          qSpilled_touchMemory]
    refine ⟨rfl, ⟨n + 1, sp + BitVec.ofNat 256 32, BitVec.ofNat 256 v, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, hv, ?_, ?_⟩⟩⟩
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) (sp + BitVec.ofNat 256 32) (by decide : ("q_has_top" : Ident) ≠ "q_sp") (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_sp" (BitVec.ofNat 256 v) (sp + BitVec.ofNat 256 32) (by decide : ("q_top" : Ident) ≠ "q_sp") (venvGet_set_same (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32) (sp) (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_sp" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (sp) (by decide : ("q_ptr" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_sp" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_sp")) (venvGet_set_ne (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" "q_sp" (pc + BitVec.ofNat 256 5) (sp) (by decide : ("q_pc" : Ident) ≠ "q_sp") (Eq.trans (venvGet_cons_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V)) "q_off" "q_sp" (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (by decide : ("q_off" : Ident) ≠ "q_sp")) (Eq.trans (venvGet_cons_ne (("q_word", (loadWord st.memory pc.toNat)) :: V) "q_token" "q_sp" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_sp")) (Eq.trans (venvGet_cons_ne V "q_word" "q_sp" (loadWord st.memory pc.toNat) (by decide : ("q_word" : Ident) ≠ "q_sp")) (hsp))))))))))
    · rw [hV'']
      exact (venvGet_set_ne (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : ("q_has_top" : Ident) ≠ "q_top") (venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v) (top) (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" "q_top" (sp + BitVec.ofNat 256 32) (top) (by decide : ("q_sp" : Ident) ≠ "q_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_top" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (top) (by decide : ("q_ptr" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_top")) (venvGet_set_ne (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" "q_top" (pc + BitVec.ofNat 256 5) (top) (by decide : ("q_pc" : Ident) ≠ "q_top") (Eq.trans (venvGet_cons_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V)) "q_off" "q_top" (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (by decide : ("q_off" : Ident) ≠ "q_top")) (Eq.trans (venvGet_cons_ne (("q_word", (loadWord st.memory pc.toNat)) :: V) "q_token" "q_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_top")) (Eq.trans (venvGet_cons_ne V "q_word" "q_top" (loadWord st.memory pc.toNat) (by decide : ("q_word" : Ident) ≠ "q_top")) (htop))))))))))
    · rw [heq0]
      exact spill_add_word program.stackMptr n
    · exact spill_room_toNat program n sp heq0 hwrap0 hfit.2.2.2.1 hroom
    · rw [hV'']
      exact (venvGet_set_same (VEnv.set (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) (1) (venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" (sp + BitVec.ofNat 256 32)) "q_top" "q_has_top" (BitVec.ofNat 256 v) (1) (by decide : ("q_top" : Ident) ≠ "q_has_top") (venvGet_set_ne (VEnv.set (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) "q_sp" "q_has_top" (sp + BitVec.ofNat 256 32) (1) (by decide : ("q_sp" : Ident) ≠ "q_has_top") (venvGet_set_ne (("q_ptr", (BitVec.ofNat 256 0)) :: (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5))) "q_ptr" "q_has_top" (BitVec.ofNat 256 p + BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (1) (by decide : ("q_ptr" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne (VEnv.set (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_ptr" "q_has_top" (BitVec.ofNat 256 0) (by decide : ("q_ptr" : Ident) ≠ "q_has_top")) (venvGet_set_ne (("q_off", (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃)))) :: (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V))) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 5) (1) (by decide : ("q_pc" : Ident) ≠ "q_has_top") (Eq.trans (venvGet_cons_ne (("q_token", (BitVec.ofNat 256 tcq.mem.l0)) :: (("q_word", (loadWord st.memory pc.toNat)) :: V)) "q_off" "q_has_top" (BitVec.ofNat 256 ((((o₀ * 256 + o₁) * 256 + o₂) * 256 + o₃))) (by decide : ("q_off" : Ident) ≠ "q_has_top")) (Eq.trans (venvGet_cons_ne (("q_word", (loadWord st.memory pc.toNat)) :: V) "q_token" "q_has_top" (BitVec.ofNat 256 tcq.mem.l0) (by decide : ("q_token" : Ident) ≠ "q_has_top")) (Eq.trans (venvGet_cons_ne V "q_word" "q_has_top" (loadWord st.memory pc.toNat) (by decide : ("q_word" : Ident) ≠ "q_has_top")) (h1))))))))))
    · rw [hshape, htails, List.map_cons]
    · intro w hw
      rw [htails] at hw
      cases List.mem_cons.mp hw with
      | inl heq => exact heq ▸ hcan
      | inr hw2 => exact hspill w hw2


/-! ### 12. TWO MORE CHAINS THROUGH A SPILL (SPILL2, item 2's prize)

  SPILL landed 'qStackCorr_neg_then_pushConst_then_add': three boundaries, the middle one a spill, with
  ADD popping the spilled word back out of memory. One chain is evidence of shape, not of generality.
  These two run the SAME three boundaries through the two OTHER spill shapes the arm layer now has: the
  literal-pointer spill ('pushMemU16', where the word re-cached after the spill is read through a pointer
  decoded from the program word) and the token spill ('pushMemToken', where it is read through the
  nine-way 'Stmt.switch'). In all three the middle step is the shared 'qSpillStmt' and the last step is
  the same 'qStackCorr_add' popping at the pointer the spill left behind - so what varies is only what the
  arm does between the spill and the next boundary, which is exactly the generality claim. -/

/-- **CHAIN TWO - NEG, then PUSH_MEM_U16 across its spill, then ADD.** -/
theorem qStackCorr_neg_then_pushMemU16_then_add {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V₁ V₂ V₃ : VEnv (Bridge.Dialect c g)) (st st₁ st₂ st₃ : EvmState) (o₁ o₂ o₃ : Outcome)
    (rest₁ : List Nat) (b₀ b₁ : Nat) (rest₂ : List Nat) (v : Nat)
    (consts : List Word256) (mem₁ mem₂ mem₃ : QuotientRefMemory)
    (stk : List QVMFr) (s₁ s₂ s₃ : IdentityStep)
    (pc sp top : U256)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hfit : quotientProgramFits program)
    (hstep₁ : Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest₁) consts 0 qOpNeg stk mem₁ = .ok s₁)
    (hrun₁ : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyNeg ctx program tcq) V₁ st₁ o₁)
    (hr : VEnv.get V "r" = some frModulusWord)
    (_hr₁ : VEnv.get V₁ "r" = some frModulusWord)
    (hstep₂ : Midfall.Generator.evalQuotientIdentityStep (qOpPushMemU16 :: b₀ :: b₁ :: rest₂) consts 0
      qOpPushMemU16 s₁.stack mem₂ = .ok s₂)
    (hrun₂ : ExecStmts (Bridge.Dialect c g) funs V₁ st₁
      (GenAst.qArmBodyPushMemU16 ctx program tcq) V₂ st₂ o₂)
    (hget_pc : VEnv.get V₁ "q_pc" = some pc)
    (hsp : VEnv.get V₁ "q_sp" = some sp)
    (htop : VEnv.get V₁ "q_top" = some top)
    (hbytes : (loadWord st₁.memory pc.toNat) >>> 240 = BitVec.ofNat 256 (b₀ * 256 + b₁))
    (hread : loadWord st₁.memory (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat = BitVec.ofNat 256 v)
    (hlit : (mem₂.literal (b₀ * 256 + b₁)).1 = (BitVec.ofNat 256 v).toNat)
    (hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat + 32 ≤ sp.toNat ∨
      sp.toNat + 32 ≤ (BitVec.ofNat 256 (b₀ * 256 + b₁)).toNat)
    (hstep₃ : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest₂) consts 0 qOpAdd s₂.stack
      mem₃ = .ok s₃)
    (hrun₃ : ExecStmts (Bridge.Dialect c g) funs V₂ st₂ (GenAst.qArmBodyAdd ctx program tcq) V₃ st₃ o₃)
    (hr₂ : VEnv.get V₂ "r" = some frModulusWord) :
    o₁ = .normal ∧ o₂ = .normal ∧ o₃ = .normal ∧
      QStackCorr (c := c) (g := g) program V₃ st₃ s₃.stack := by
  obtain ⟨hn₁, hc₁⟩ := qStackCorr_neg hc hg ctx program tcq funs V V₁ st st₁ o₁ rest₁ consts mem₁ stk s₁
    hrun₁ hr hcorr hstep₁
  obtain ⟨hn₂, hc₂⟩ := qStackCorr_pushMemU16 hc hg ctx program tcq funs V₁ V₂ st₁ st₂ o₂ rest₂ consts
    mem₂ s₁.stack s₂ b₀ b₁ v pc sp top hbytes hread hlit hv hdisj hfit hget_pc hsp htop hroom hrun₂ hc₁
    hstep₂
  obtain ⟨hn₃, hc₃⟩ := qStackCorr_add hc hg ctx program tcq funs V₂ V₃ st₂ st₃ o₃ rest₂ consts mem₃
    s₂.stack s₃ hrun₃ hr₂ hc₂ hstep₃
  exact ⟨hn₁, hn₂, hn₃, hc₃⟩

/-- **CHAIN THREE - NEG, then PUSH_MEM_TOKEN across its spill, then ADD.** -/
theorem qStackCorr_neg_then_pushMemToken_then_add {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g))
    (V V₁ V₂ V₃ : VEnv (Bridge.Dialect c g)) (st st₁ st₂ st₃ : EvmState) (o₁ o₂ o₃ : Outcome)
    (rest₁ : List Nat) (t p v : Nat) (rest₂ : List Nat)
    (consts : List Word256) (mem₁ mem₂ mem₃ : QuotientRefMemory)
    (stk : List QVMFr) (s₁ s₂ s₃ : IdentityStep)
    (pc sp top : U256)
    (hcorr : QStackCorr (c := c) (g := g) program V st stk)
    (hfit : quotientProgramFits program)
    (hstep₁ : Midfall.Generator.evalQuotientIdentityStep (qOpNeg :: rest₁) consts 0 qOpNeg stk mem₁ = .ok s₁)
    (hrun₁ : ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyNeg ctx program tcq) V₁ st₁ o₁)
    (hr : VEnv.get V "r" = some frModulusWord)
    (_hr₁ : VEnv.get V₁ "r" = some frModulusWord)
    (hstep₂ : Midfall.Generator.evalQuotientIdentityStep (qOpPushMemToken :: t :: rest₂) consts 0
      qOpPushMemToken s₁.stack mem₂ = .ok s₂)
    (hrun₂ : ExecStmts (Bridge.Dialect c g) funs V₁ st₁
      (GenAst.qArmBodyPushMemToken ctx program tcq) V₂ st₂ o₂)
    (hget_pc : VEnv.get V₁ "q_pc" = some pc)
    (hsp : VEnv.get V₁ "q_sp" = some sp)
    (htop : VEnv.get V₁ "q_top" = some top)
    (hget_l0 : VEnv.get V₁ "L_0_MPTR" = some (BitVec.ofNat 256 p))
    (hbyte : (((loadWord st₁.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 tcq.mem.l0)
    (hread : loadWord st₁.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
    (hlit : (mem₂.token t 0).1 = (BitVec.ofNat 256 v).toNat)
    (hv : (BitVec.ofNat 256 v).toNat < qvmFrModulus)
    (hl0 : program.memUsage.l0 = true)
    (hroom : ¬ (sp > BitVec.ofNat 256 program.guards.stackLast))
    (hdisj : (BitVec.ofNat 256 p).toNat + 32 ≤ sp.toNat ∨ sp.toNat + 32 ≤ (BitVec.ofNat 256 p).toNat)
    (hstep₃ : Midfall.Generator.evalQuotientIdentityStep (qOpAdd :: rest₂) consts 0 qOpAdd s₂.stack
      mem₃ = .ok s₃)
    (hrun₃ : ExecStmts (Bridge.Dialect c g) funs V₂ st₂ (GenAst.qArmBodyAdd ctx program tcq) V₃ st₃ o₃)
    (hr₂ : VEnv.get V₂ "r" = some frModulusWord) :
    o₁ = .normal ∧ o₂ = .normal ∧ o₃ = .normal ∧
      QStackCorr (c := c) (g := g) program V₃ st₃ s₃.stack := by
  obtain ⟨hn₁, hc₁⟩ := qStackCorr_neg hc hg ctx program tcq funs V V₁ st st₁ o₁ rest₁ consts mem₁ stk s₁
    hrun₁ hr hcorr hstep₁
  obtain ⟨hn₂, hc₂⟩ := qStackCorr_pushMemToken hc hg ctx program tcq funs V₁ V₂ st₁ st₂ o₂ rest₂ consts
    mem₂ s₁.stack s₂ t p v pc sp top hget_l0 hbyte hread hlit hv hl0 hdisj hfit hget_pc hsp htop hroom
    hrun₂ hc₁ hstep₂
  obtain ⟨hn₃, hc₃⟩ := qStackCorr_add hc hg ctx program tcq funs V₂ V₃ st₂ st₃ o₃ rest₂ consts mem₃
    s₂.stack s₃ hrun₃ hr₂ hc₂ hstep₃
  exact ⟨hn₁, hn₂, hn₃, hc₃⟩

/-! ### 13. SPILL2 ACCEPTANCE PRINTS -/

#print axioms Midfall.Lowering.QuotientSpill.qArmRun_pushMemToken_spill
#print axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemToken_spill
#print axioms Midfall.Lowering.QuotientSpill.qArmRun_pushMemTokenOffset_spill
#print axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemTokenOffset_spill
#print axioms Midfall.Lowering.QuotientSpill.spillDisjoint_pushConst_of_ordered
#print axioms Midfall.Lowering.QuotientSpill.spillDisjoint_atDepth_of_ordered
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushConstU8
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemLiteral
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemTokenOffset
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemU16
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemToken
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushMemU16_then_add
#print axioms Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushMemToken_then_add

#cone_sorries Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemToken_spill
#cone_sorries Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemTokenOffset_spill

#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_pushConstU8
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_pushMemLiteral
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_pushMemTokenOffset
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_pushMemU16
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_pushMemToken
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushMemU16_then_add
#cone_sorries Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushMemToken_then_add
#cone_sorries Midfall.Lowering.QuotientSpill.spillDisjoint_pushConst_of_ordered
#cone_sorries Midfall.Lowering.QuotientSpill.spillDisjoint_atDepth_of_ordered

#assert_axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemToken_spill [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qArmValueAll_pushMemTokenOffset_spill [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.spillDisjoint_pushConst_of_ordered [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.spillDisjoint_atDepth_of_ordered [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushConstU8 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemLiteral [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemTokenOffset [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemU16 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_pushMemToken [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushMemU16_then_add [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.QuotientSpill.qStackCorr_neg_then_pushMemToken_then_add [propext, Classical.choice, Quot.sound] native []

end Midfall.Lowering.QuotientSpill

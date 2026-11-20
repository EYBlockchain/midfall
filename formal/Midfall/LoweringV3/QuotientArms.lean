-- |
-- Midfall.LoweringV3.QuotientArms
--
-- QMEM - the memory-reading arm value refinements: the bulk of the 20 static arms that
-- 'QuotientFrame' section H left open. PLAN-V3 section 4 / EXECUTION-V2 section 5 as amended by D-P75.
--
-- THIS FILE IS THE EMITTED SIDE of ROW.Q.3's value clause for the arms that READ MEMORY.
-- 'QuotientFrame' sections B and H landed the reference side ('qStepValue_X') and the first six
-- register-only or single-read refinements (NEG, POW5, ADD, MUL, ADD_CONST_U8, MUL_CONST_U8). The
-- triples here follow those two templates exactly - 'qArmRun_X' (a vendored 'Step' derivation
-- EXECUTING the emitter's own 'GenAst.qArmBodyX'), 'qArmValue_X' as a 'StmtsContract', and
-- 'qArmValueAll_X' as a 'StmtsContractAll' through 'StmtsContractAll.of_det' at
-- 'Bridge.dialect_deterministic', whose only extra hypotheses are 'c.Functional' and 'g.Functional' -
-- oracle facts, not row facts.
--
-- THE STATE EQUATION IS PER ARM, AND THAT IS THE FINDING. 'mload' is 'touchMemory' and 'mstore' is a
-- memory WRITE, so NEG's 'st' = 'st' post-condition does NOT extend to any arm here. Each post names
-- the state the arm's own reads produced, in the order the vendored semantics produced it:
--
--   ADD_MEM_U16 / MUL_MEM_U16   touch(pc), then touch(ptr)          - two reads, one decode
--   ADD_CONST / MUL_CONST       touch(pc), then touch(const slot)   - decode + guard + table read
--   ADD_MUL_MEM_MEM             touch(pc), touch(lhs), touch(rhs)   - three reads
--   ADD_MUL_MEM_MEM_CONST_U8    touch(pc), touch(lhs), touch(rhs), touch(slot) - four reads
--   ADD_MUL_CONST_U8_MEM_U16    touch(pc), touch(ptr), touch(slot)
--   PUSH_MEM_U16 / PUSH_MEM_LITERAL / PUSH_CONST_U8 / PUSH_CONST
--                               touch(pc), then touch(the pushed address)
--
-- CANONICITY: none of these arms needs 'x.toNat < qvmFrModulus'. Every field operation here is an
-- 'addmod'/'mulmod' at 'frModulusWord', and 'wAddmod'/'wMulmod' reduce by 'qvmFrModulus' BEFORE the
-- 256-bit wrap, which is the same reason 'mulmod_toFr' (WpX.lean:533) carries no hypothesis. NEG's
-- 'subFr_needsCanonicity' bound is specific to subtraction. There is no uniform side-condition, and
-- none was added to a row (RULES).
--
-- THE PRECONDITIONS ARE READER EQUATIONS, NOT NEW AXIOMS. Each arm pins the registers it reads by
-- 'VEnv.get' equations (exactly what 'AtSegment'/'qinterpTop' supply) and pins each memory read at the
-- EMITTED expression - 'loadWord st.memory ...' - so the theorem is independent of how the byte got
-- there and the byte-level bridge ('loadWord_topByte' / 'loadWord_top2', Midfall/Yul/Word.lean
-- section 8) stays the composition's job. The two arms with a 'qconst > program.guards.constMax'
-- guard (ADD_CONST, MUL_CONST, PUSH_CONST) additionally need the guard not to fire, stated as the
-- word inequality '(BitVec.ofNat 256 b).toNat <= (BitVec.ofNat 256 program.guards.constMax).toNat'.
--
-- THE FOUR PUSH ARMS ARE STATED AT THE EMPTY STACK. Their emitted body begins with
-- 'if q_has_top then [spill q_top at q_sp; q_sp += 32]', and the 'then' branch is a 'Step.block', so
-- its post-environment is 'restore V Vb' (BigStep.lean:111) at a symbolic 'V'. The empty-stack branch
-- ('q_has_top = 0') is the branch a one-instruction identity segment actually takes - the reference
-- starts every segment with '[]' - and it is what is landed here. The non-empty branch is the same
-- work plus a 'restore' lemma; it is named as open, not papered over.
--
-- NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', to a bundle or to the root (RULES); no
-- statement names a fixture (D-P71); there is no 'native_decide' and no sorry in this file.
import Midfall.LoweringV3.QuotientFrame
import Midfall.Tools.ConeSorries


open YulSemantics YulSemantics.EVM Midfall Midfall.Generator Midfall.Lowering
open Midfall.Yul Midfall.Yul.Bridge Midfall.Lowering.QuotientInterp
open Midfall.Lowering.GenAst
open Midfall.Yul.WpX
open Midfall.LoweringV3.QuotientFrame

set_option autoImplicit false

namespace Midfall.LoweringV3.QuotientArms



-- the open-dialect built-in facts the derivations below use


theorem qbi_add {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.add [a, b] st (.ok [a + b] st) := rfl

theorem qbi_addmod_atFr {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.addmod [a, b, frModulusWord] st (.ok [wAddmod a b] st) := rfl

theorem qbi_and {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.and [a, b] st (.ok [a &&& b] st) := rfl

theorem qbi_byte0 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :
    (Bridge.Dialect c g).Builtin Op.byte [BitVec.ofNat 256 0, w] st (.ok [(w >>> 248) &&& 0xff] st) := rfl

theorem qbi_byte2 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :
    (Bridge.Dialect c g).Builtin Op.byte [BitVec.ofNat 256 2, w] st (.ok [(w >>> 232) &&& 0xff] st) := rfl

theorem qbi_byte4 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :
    (Bridge.Dialect c g).Builtin Op.byte [BitVec.ofNat 256 4, w] st (.ok [(w >>> 216) &&& 0xff] st) := rfl

theorem qbi_gt {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.gt [a, b] st (.ok [b2w (decide (b.toNat < a.toNat))] st) := rfl

theorem qbi_mload_at {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (m : Nat -> UInt8) (p : U256) (h : st.memory = m) :
    (Bridge.Dialect c g).Builtin Op.mload [p] st (.ok [loadWord m p.toNat] (touchMemory st p.toNat 32)) := by
  rw [<- h]
  rfl

theorem qbi_mulmod_atFr {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.mulmod [a, b, frModulusWord] st (.ok [wMulmod a b] st) := rfl

theorem qbi_shl5 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (v : U256) :
    (Bridge.Dialect c g).Builtin Op.shl [BitVec.ofNat 256 5, v] st (.ok [v <<< 5] st) := rfl

theorem qbi_shr224 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (v : U256) :
    (Bridge.Dialect c g).Builtin Op.shr [BitVec.ofNat 256 224, v] st (.ok [v >>> 224] st) := rfl

theorem qbi_shr240 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (v : U256) :
    (Bridge.Dialect c g).Builtin Op.shr [BitVec.ofNat 256 240, v] st (.ok [v >>> 240] st) := rfl



theorem qArmRun_addMemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc x v : U256) (p : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hptr : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAddMemU16 ctx program tcq)
      (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal := by
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
  have g13 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_ptr" "q_pc" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_pc")]; exact hget_pc
  have g14 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_top")]; exact hget_top
  have g15 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "q_ptr" "r" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "r")]; exact hget_r
  have g16 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_cons_eq V "q_ptr" (BitVec.ofNat 256 p)
  have a17 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x18 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a19 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [ylit 2]) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory st pc.toNat 32) a17 x18
  have x20 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g13
  have a21 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 2]) (.eres (.vals [pc, BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 2]) (restvals := [BitVec.ofNat 256 2]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a19 x20
  have x22 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 2])) (.eres (.vals [(pc + BitVec.ofNat 256 2)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a21 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 2))
  have s23 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 2]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 2)]) x22 (by rfl)
  have g24 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_ptr" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "q_ptr") g16
  have g25 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" = some x :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) x (by decide : "q_pc" ≠ "q_top") g14
  have g26 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "r" = some frModulusWord :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "r" (pc + BitVec.ofNat 256 2) frModulusWord (by decide : "q_pc" ≠ "r") g15
  have g27 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_same (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2) pc g13
  have a28 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x29 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a30 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a28 x29
  have a31 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "q_ptr")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g24
  have a33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_ptr"]) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 p) (st2 := touchMemory st pc.toNat 32) a31 x32
  have x34 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 p).toNat] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a33 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (BitVec.ofNat 256 p) w6)
  have d35 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [v] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    by rw [<- hload]; exact x34
  have w36 :
    (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) w6
  have a37 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yvar "q_ptr"], yvar "r"]) (.eres (.vals [v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := v) (st2 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) a30 d35
  have x38 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g25
  have a39 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mload [yvar "q_ptr"], yvar "r"]) (.eres (.vals [x, v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_ptr"], yvar "r"]) (restvals := [v, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (v := x) (st2 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) a37 x38
  have x40 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.addmod [yvar "q_top", yop Op.mload [yvar "q_ptr"], yvar "r"])) (.eres (.vals [wAddmod x v] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a39 (qbi_addmod_atFr (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) x v)
  have s41 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.addmod [yvar "q_top", yop Op.mload [yvar "q_ptr"], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod x v]) x40 (by rfl)
  have g42 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_pc" (wAddmod x v) (pc + BitVec.ofNat 256 2) (by decide : "q_top" ≠ "q_pc") g27
  have g43 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_ptr" (wAddmod x v) (BitVec.ofNat 256 p) (by decide : "q_top" ≠ "q_ptr") g24
  have g44 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "r" (wAddmod x v) frModulusWord (by decide : "q_top" ≠ "r") g26
  have g45 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "q_top" = some (wAddmod x v) :=
    venvGet_set_same (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v) x g25
  unfold GenAst.qArmBodyAddMemU16
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s23 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)) s41 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_addMemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc x v : U256) (p : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)))) := by
  intro V st hpre
  have hrun := qArmRun_addMemU16 ctx program tcq funs V st pc x v p hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2
  rw [wAddmod_eq_qvmFrAdd] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_addMemU16 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc x v : U256) (p : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_addMemU16 ctx program tcq funs pc x v p )

theorem qArmRun_mulMemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc x v : U256) (p : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hptr : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyMulMemU16 ctx program tcq)
      (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal := by
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
  have g13 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_ptr" "q_pc" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_pc")]; exact hget_pc
  have g14 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_ptr" "q_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_top")]; exact hget_top
  have g15 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "q_ptr" "r" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "r")]; exact hget_r
  have g16 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_cons_eq V "q_ptr" (BitVec.ofNat 256 p)
  have a17 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x18 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a19 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [ylit 2]) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory st pc.toNat 32) a17 x18
  have x20 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g13
  have a21 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 2]) (.eres (.vals [pc, BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 2]) (restvals := [BitVec.ofNat 256 2]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a19 x20
  have x22 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 2])) (.eres (.vals [(pc + BitVec.ofNat 256 2)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a21 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 2))
  have s23 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 2]))) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 2)]) x22 (by rfl)
  have g24 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_ptr" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "q_ptr") g16
  have g25 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" = some x :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) x (by decide : "q_pc" ≠ "q_top") g14
  have g26 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "r" = some frModulusWord :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "r" (pc + BitVec.ofNat 256 2) frModulusWord (by decide : "q_pc" ≠ "r") g15
  have g27 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_same (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2) pc g13
  have a28 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x29 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a30 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a28 x29
  have a31 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "q_ptr")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g24
  have a33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_ptr"]) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 p) (st2 := touchMemory st pc.toNat 32) a31 x32
  have x34 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 p).toNat] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a33 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (BitVec.ofNat 256 p) w6)
  have d35 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [v] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    by rw [<- hload]; exact x34
  have w36 :
    (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) w6
  have a37 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yvar "q_ptr"], yvar "r"]) (.eres (.vals [v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := v) (st2 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) a30 d35
  have x38 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g25
  have a39 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mload [yvar "q_ptr"], yvar "r"]) (.eres (.vals [x, v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_ptr"], yvar "r"]) (restvals := [v, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (v := x) (st2 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) a37 x38
  have x40 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mulmod [yvar "q_top", yop Op.mload [yvar "q_ptr"], yvar "r"])) (.eres (.vals [wMulmod x v] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a39 (qbi_mulmod_atFr (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) x v)
  have s41 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.mulmod [yvar "q_top", yop Op.mload [yvar "q_ptr"], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wMulmod x v]) x40 (by rfl)
  have g42 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_pc" (wMulmod x v) (pc + BitVec.ofNat 256 2) (by decide : "q_top" ≠ "q_pc") g27
  have g43 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_ptr" (wMulmod x v) (BitVec.ofNat 256 p) (by decide : "q_top" ≠ "q_ptr") g24
  have g44 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "r" (wMulmod x v) frModulusWord (by decide : "q_top" ≠ "r") g26
  have g45 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "q_top" = some (wMulmod x v) :=
    venvGet_set_same (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v) x g25
  unfold GenAst.qArmBodyMulMemU16
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s23 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)) s41 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_mulMemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc x v : U256) (p : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMulMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)))) := by
  intro V st hpre
  have hrun := qArmRun_mulMemU16 ctx program tcq funs V st pc x v p hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2
  rw [wMulmod_eq_qvmFrMul] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_mulMemU16 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc x v : U256) (p : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMulMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_mulMemU16 ctx program tcq funs pc x v p )

theorem qArmRun_addConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb x v : U256) (b : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hdec : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b)
    (hconst : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = v)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAddConst ctx program tcq)
      (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal := by
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
  have g14 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "qconst" "q_pc" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_pc")]; exact hget_pc
  have g15 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_top")]; exact hget_top
  have g16 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "qconst" "r" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "r")]; exact hget_r
  have g17 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_cons_eq V "qconst" (BitVec.ofNat 256 b)
  have a18 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x19 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a20 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [ylit 2]) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory st pc.toNat 32) a18 x19
  have x21 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g14
  have a22 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 2]) (.eres (.vals [pc, BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 2]) (restvals := [BitVec.ofNat 256 2]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a20 x21
  have x23 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 2])) (.eres (.vals [(pc + BitVec.ofNat 256 2)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a22 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 2))
  have s24 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 2]))) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 2)]) x23 (by rfl)
  have g25 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 2) cb (by decide : "q_pc" ≠ "q_const_mptr") g13
  have g26 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" = some x :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) x (by decide : "q_pc" ≠ "q_top") g15
  have g27 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "qconst" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 b) (by decide : "q_pc" ≠ "qconst") g17
  have g28 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "r" = some frModulusWord :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "r" (pc + BitVec.ofNat 256 2) frModulusWord (by decide : "q_pc" ≠ "r") g16
  have g29 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_same (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2) pc g14
  have a30 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x31 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (ylit program.guards.constMax)) (.eres (.vals [BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number program.guards.constMax)
  have a32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [ylit program.guards.constMax]) (.eres (.vals [BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 program.guards.constMax) (st2 := touchMemory st pc.toNat 32) a30 x31
  have x33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g27
  have a34 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "qconst", ylit program.guards.constMax]) (.eres (.vals [BitVec.ofNat 256 b, BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit program.guards.constMax]) (restvals := [BitVec.ofNat 256 program.guards.constMax]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a32 x33
  have x35 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.gt [yvar "qconst", ylit program.guards.constMax])) (.eres (.vals [b2w (decide ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a34 (qbi_gt (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b) (BitVec.ofNat 256 program.guards.constMax))
  have z36 :
    b2w (decide ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat)) = (Bridge.Dialect c g).zero :=
    by rw [decide_eq_false (by omega : ¬ ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat))]; rfl
  have s37 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yif (yop Op.gt [yvar "qconst", ylit program.guards.constMax]) [yexpr (ycall "q_program_fail" [])])) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x35 z36
  have a38 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x39 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g28
  have a40 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a38 x39
  have a41 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a42 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a43 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x44 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g27
  have a45 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a43 x44
  have x46 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a47 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [ylit 5, yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 5, BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [BitVec.ofNat 256 b]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a45 x46
  have x48 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.shl [ylit 5, yvar "qconst"])) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a47 (qbi_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b))
  have a49 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := ((BitVec.ofNat 256 b) <<< 5)) (st2 := touchMemory st pc.toNat 32) a42 x48
  have x50 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "q_const_mptr")) (.eres (.vals [cb] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g25
  have a51 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [cb, ((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [((BitVec.ofNat 256 b) <<< 5)]) (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32) a49 x50
  have x52 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a51 (qbi_add (touchMemory st pc.toNat 32) cb ((BitVec.ofNat 256 b) <<< 5))
  have a53 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := (cb + ((BitVec.ofNat 256 b) <<< 5))) (st2 := touchMemory st pc.toNat 32) a41 x52
  have x54 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a53 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)) w6)
  have d55 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [v] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    by rw [<- hconst]; exact x54
  have w56 :
    (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) w6
  have a57 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := v) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a40 d55
  have x58 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a59 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [x, v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (restvals := [v, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := x) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a57 x58
  have x60 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.addmod [yvar "q_top", yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"])) (.eres (.vals [wAddmod x v] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a59 (qbi_addmod_atFr (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) x v)
  have s61 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.addmod [yvar "q_top", yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod x v]) x60 (by rfl)
  have g62 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_const_mptr" (wAddmod x v) cb (by decide : "q_top" ≠ "q_const_mptr") g25
  have g63 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_pc" (wAddmod x v) (pc + BitVec.ofNat 256 2) (by decide : "q_top" ≠ "q_pc") g29
  have g64 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "qconst" (wAddmod x v) (BitVec.ofNat 256 b) (by decide : "q_top" ≠ "qconst") g27
  have g65 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "r" (wAddmod x v) frModulusWord (by decide : "q_top" ≠ "r") g28
  have g66 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v)) "q_top" = some (wAddmod x v) :=
    venvGet_set_same (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v) x g26
  unfold GenAst.qArmBodyAddConst
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s24 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s37 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wAddmod x v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s61 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_addConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x v : U256) (b : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)))) := by
  intro V st hpre
  have hrun := qArmRun_addConst ctx program tcq funs V st pc cb x v b hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2 hguard
  rw [wAddmod_eq_qvmFrAdd] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_addConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x v : U256) (b : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_addConst ctx program tcq funs pc cb x v b hguard)

theorem qArmRun_mulConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb x v : U256) (b : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hdec : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b)
    (hconst : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = v)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyMulConst ctx program tcq)
      (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal := by
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
  have g14 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "qconst" "q_pc" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_pc")]; exact hget_pc
  have g15 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "qconst" "q_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_top")]; exact hget_top
  have g16 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "qconst" "r" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "r")]; exact hget_r
  have g17 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_cons_eq V "qconst" (BitVec.ofNat 256 b)
  have a18 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x19 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a20 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [ylit 2]) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory st pc.toNat 32) a18 x19
  have x21 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g14
  have a22 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 2]) (.eres (.vals [pc, BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 2]) (restvals := [BitVec.ofNat 256 2]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a20 x21
  have x23 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 2])) (.eres (.vals [(pc + BitVec.ofNat 256 2)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a22 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 2))
  have s24 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 2]))) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 2)]) x23 (by rfl)
  have g25 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 2) cb (by decide : "q_pc" ≠ "q_const_mptr") g13
  have g26 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" = some x :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) x (by decide : "q_pc" ≠ "q_top") g15
  have g27 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "qconst" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 b) (by decide : "q_pc" ≠ "qconst") g17
  have g28 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "r" = some frModulusWord :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" "r" (pc + BitVec.ofNat 256 2) frModulusWord (by decide : "q_pc" ≠ "r") g16
  have g29 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_same (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2) pc g14
  have a30 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x31 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (ylit program.guards.constMax)) (.eres (.vals [BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number program.guards.constMax)
  have a32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [ylit program.guards.constMax]) (.eres (.vals [BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 program.guards.constMax) (st2 := touchMemory st pc.toNat 32) a30 x31
  have x33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g27
  have a34 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "qconst", ylit program.guards.constMax]) (.eres (.vals [BitVec.ofNat 256 b, BitVec.ofNat 256 program.guards.constMax] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit program.guards.constMax]) (restvals := [BitVec.ofNat 256 program.guards.constMax]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a32 x33
  have x35 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.gt [yvar "qconst", ylit program.guards.constMax])) (.eres (.vals [b2w (decide ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a34 (qbi_gt (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b) (BitVec.ofNat 256 program.guards.constMax))
  have z36 :
    b2w (decide ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat)) = (Bridge.Dialect c g).zero :=
    by rw [decide_eq_false (by omega : ¬ ((BitVec.ofNat 256 program.guards.constMax).toNat < (BitVec.ofNat 256 b).toNat))]; rfl
  have s37 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yif (yop Op.gt [yvar "qconst", ylit program.guards.constMax]) [yexpr (ycall "q_program_fail" [])])) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x35 z36
  have a38 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x39 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g28
  have a40 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a38 x39
  have a41 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a42 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a43 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x44 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g27
  have a45 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a43 x44
  have x46 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a47 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [ylit 5, yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 5, BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [BitVec.ofNat 256 b]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a45 x46
  have x48 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.shl [ylit 5, yvar "qconst"])) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a47 (qbi_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b))
  have a49 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := ((BitVec.ofNat 256 b) <<< 5)) (st2 := touchMemory st pc.toNat 32) a42 x48
  have x50 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "q_const_mptr")) (.eres (.vals [cb] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g25
  have a51 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [cb, ((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [((BitVec.ofNat 256 b) <<< 5)]) (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32) a49 x50
  have x52 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a51 (qbi_add (touchMemory st pc.toNat 32) cb ((BitVec.ofNat 256 b) <<< 5))
  have a53 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := (cb + ((BitVec.ofNat 256 b) <<< 5))) (st2 := touchMemory st pc.toNat 32) a41 x52
  have x54 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a53 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)) w6)
  have d55 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [v] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    by rw [<- hconst]; exact x54
  have w56 :
    (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) w6
  have a57 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := v) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a40 d55
  have x58 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a59 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [x, v, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (restvals := [v, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := x) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a57 x58
  have x60 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mulmod [yvar "q_top", yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"])) (.eres (.vals [wMulmod x v] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a59 (qbi_mulmod_atFr (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) x v)
  have s61 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.mulmod [yvar "q_top", yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wMulmod x v]) x60 (by rfl)
  have g62 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_const_mptr" (wMulmod x v) cb (by decide : "q_top" ≠ "q_const_mptr") g25
  have g63 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_pc" (wMulmod x v) (pc + BitVec.ofNat 256 2) (by decide : "q_top" ≠ "q_pc") g29
  have g64 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "qconst" (wMulmod x v) (BitVec.ofNat 256 b) (by decide : "q_top" ≠ "qconst") g27
  have g65 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "r" (wMulmod x v) frModulusWord (by decide : "q_top" ≠ "r") g28
  have g66 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v)) "q_top" = some (wMulmod x v) :=
    venvGet_set_same (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v) x g26
  unfold GenAst.qArmBodyMulConst
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s24 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s37 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (wMulmod x v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s61 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_mulConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x v : U256) (b : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMulConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)))) := by
  intro V st hpre
  have hrun := qArmRun_mulConst ctx program tcq funs V st pc cb x v b hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2 hguard
  rw [wMulmod_eq_qvmFrMul] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_mulConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x v : U256) (b : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyMulConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_mulConst ctx program tcq funs pc cb x v b hguard)

theorem wAddmod_wMulmod_eq_qvmFr_addMulMemMem (x lv rv : U256) :
    wAddmod x (wMulmod lv rv) = BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul lv.toNat rv.toNat)) := by rw [wAddmod_eq_qvmFrAdd, wMulmod_toNat]

theorem qArmRun_addMulMemMem {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc x lv rv : U256) (l r : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hl : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 l)
    (hr : (((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535) = BitVec.ofNat 256 r)
    (hlv : loadWord st.memory (BitVec.ofNat 256 l).toNat = lv)
    (hrv : loadWord st.memory (BitVec.ofNat 256 r).toNat = rv) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAddMulMemMem ctx program tcq)
      (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) .normal := by
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
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_word" "q_pc" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_pc")]; exact hget_pc
  have g8 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_word" "q_top" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_top")]; exact hget_top
  have g9 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "q_word" "r" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "r")]; exact hget_r
  have g10 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_cons_eq V "q_word" (loadWord st.memory pc.toNat)
  have a11 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x12 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g10
  have a13 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a11 x12
  have x14 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 240)) (.eres (.vals [BitVec.ofNat 256 240] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 240)
  have a15 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [ylit 240, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 240, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 240) (st2 := touchMemory st pc.toNat 32) a13 x14
  have x16 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 240, yvar "q_word"])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 240)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a15 (qbi_shr240 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d17 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 240, yvar "q_word"])) (.eres (.vals [BitVec.ofNat 256 l] (touchMemory st pc.toNat 32))) :=
    by rw [<- hl]; exact x16
  have s18 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.stmt (ylet "q_lhs" (yop Op.shr [ylit 240, yvar "q_word"]))) (.sres (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d17 rfl
  have g19 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_pc" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_pc")]; exact g7
  have g20 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_top" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_top")]; exact g8
  have g21 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_word" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_word")]; exact g10
  have g22 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "r" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "r")]; exact g9
  have g23 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_lhs" = some (BitVec.ofNat 256 l) :=
    venvGet_cons_eq (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" (BitVec.ofNat 256 l)
  have a24 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x25 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 65535)) (.eres (.vals [BitVec.ofNat 256 65535] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 65535)
  have a26 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 65535]) (.eres (.vals [BitVec.ofNat 256 65535] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 65535) (st2 := touchMemory st pc.toNat 32) a24 x25
  have a27 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x28 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g21
  have a29 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a27 x28
  have x30 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 224)) (.eres (.vals [BitVec.ofNat 256 224] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 224)
  have a31 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 224, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 224, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 224) (st2 := touchMemory st pc.toNat 32) a29 x30
  have x32 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 224, yvar "q_word"])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 224)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a31 (qbi_shr224 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have a33 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535]) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 224), BitVec.ofNat 256 65535] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 65535]) (restvals := [BitVec.ofNat 256 65535]) (st1 := touchMemory st pc.toNat 32) (v := ((loadWord st.memory pc.toNat) >>> 224)) (st2 := touchMemory st pc.toNat 32) a26 x32
  have x34 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.and [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a33 (qbi_and (touchMemory st pc.toNat 32) ((loadWord st.memory pc.toNat) >>> 224) (BitVec.ofNat 256 65535))
  have d35 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.and [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535])) (.eres (.vals [BitVec.ofNat 256 r] (touchMemory st pc.toNat 32))) :=
    by rw [<- hr]; exact x34
  have s36 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.stmt (ylet "q_rhs" (yop Op.and [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535]))) (.sres (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d35 rfl
  have g37 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_lhs" = some (BitVec.ofNat 256 l) :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_lhs" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_lhs")]; exact g23
  have g38 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_pc" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_pc")]; exact g19
  have g39 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_top" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_top")]; exact g20
  have g40 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_word" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_word")]; exact g21
  have g41 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "r" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "r")]; exact g22
  have g42 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_rhs" = some (BitVec.ofNat 256 r) :=
    venvGet_cons_eq (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" (BitVec.ofNat 256 r)
  have a43 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x44 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (ylit tcq.byteU32Bytes)) (.eres (.vals [BitVec.ofNat 256 tcq.byteU32Bytes] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number tcq.byteU32Bytes)
  have a45 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [ylit tcq.byteU32Bytes]) (.eres (.vals [BitVec.ofNat 256 tcq.byteU32Bytes] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 tcq.byteU32Bytes) (st2 := touchMemory st pc.toNat 32) a43 x44
  have x46 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g38
  have a47 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit tcq.byteU32Bytes]) (.eres (.vals [pc, BitVec.ofNat 256 tcq.byteU32Bytes] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit tcq.byteU32Bytes]) (restvals := [BitVec.ofNat 256 tcq.byteU32Bytes]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a45 x46
  have x48 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit tcq.byteU32Bytes])) (.eres (.vals [(pc + BitVec.ofNat 256 tcq.byteU32Bytes)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a47 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 tcq.byteU32Bytes))
  have s49 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit tcq.byteU32Bytes]))) (.sres (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 tcq.byteU32Bytes)]) x48 (by rfl)
  have g50 :
    VEnv.get (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_lhs" = some (BitVec.ofNat 256 l) :=
    venvGet_set_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_lhs" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (BitVec.ofNat 256 l) (by decide : "q_pc" ≠ "q_lhs") g37
  have g51 :
    VEnv.get (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_rhs" = some (BitVec.ofNat 256 r) :=
    venvGet_set_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_rhs" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (BitVec.ofNat 256 r) (by decide : "q_pc" ≠ "q_rhs") g42
  have g52 :
    VEnv.get (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" = some x :=
    venvGet_set_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) x (by decide : "q_pc" ≠ "q_top") g39
  have g53 :
    VEnv.get (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_word" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (loadWord st.memory pc.toNat) (by decide : "q_pc" ≠ "q_word") g40
  have g54 :
    VEnv.get (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "r" = some frModulusWord :=
    venvGet_set_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "r" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) frModulusWord (by decide : "q_pc" ≠ "r") g41
  have g55 :
    VEnv.get (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_pc" = some (pc + BitVec.ofNat 256 tcq.byteU32Bytes) :=
    venvGet_set_same (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) pc g38
  have a56 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x57 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g54
  have a58 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a56 x57
  have a59 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x60 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g54
  have a61 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a59 x60
  have a62 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x63 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yvar "q_rhs")) (.eres (.vals [BitVec.ofNat 256 r] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g51
  have a64 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yvar "q_rhs"]) (.eres (.vals [BitVec.ofNat 256 r] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 r) (st2 := touchMemory st pc.toNat 32) a62 x63
  have x65 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_rhs"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 r).toNat] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.builtinOk a64 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (BitVec.ofNat 256 r) w5)
  have d66 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_rhs"])) (.eres (.vals [rv] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    by rw [<- hrv]; exact x65
  have w67 :
    (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) w5
  have a68 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yvar "q_rhs"], yvar "r"]) (.eres (.vals [rv, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := rv) (st2 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) a61 d66
  have a69 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x70 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (.expr (yvar "q_lhs")) (.eres (.vals [BitVec.ofNat 256 l] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g50
  have a71 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (.args [yvar "q_lhs"]) (.eres (.vals [BitVec.ofNat 256 l] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (v := BitVec.ofNat 256 l) (st2 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) a69 x70
  have x72 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (.expr (yop Op.mload [yvar "q_lhs"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 l).toNat] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a71 (qbi_mload_at (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) st.memory (BitVec.ofNat 256 l) w67)
  have d73 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (.expr (yop Op.mload [yvar "q_lhs"])) (.eres (.vals [lv] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    by rw [<- hlv]; exact x72
  have w74 :
    (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) w67
  have a75 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"]) (.eres (.vals [lv, rv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_rhs"], yvar "r"]) (restvals := [rv, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (v := lv) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a68 d73
  have x76 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"])) (.eres (.vals [wMulmod lv rv] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a75 (qbi_mulmod_atFr (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) lv rv)
  have a77 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yvar "r"]) (.eres (.vals [wMulmod lv rv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := wMulmod lv rv) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a58 x76
  have x78 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g52
  have a79 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yvar "r"]) (.eres (.vals [x, wMulmod lv rv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yvar "r"]) (restvals := [wMulmod lv rv, frModulusWord]) (st1 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) (v := x) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a77 x78
  have x80 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yop Op.addmod [yvar "q_top", yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yvar "r"])) (.eres (.vals [wAddmod x (wMulmod lv rv)] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a79 (qbi_addmod_atFr (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) x (wMulmod lv rv))
  have s81 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.addmod [yvar "q_top", yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod x (wMulmod lv rv)]) x80 (by rfl)
  have g82 :
    VEnv.get (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) "q_lhs" = some (BitVec.ofNat 256 l) :=
    venvGet_set_ne (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_lhs" (wAddmod x (wMulmod lv rv)) (BitVec.ofNat 256 l) (by decide : "q_top" ≠ "q_lhs") g50
  have g83 :
    VEnv.get (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) "q_pc" = some (pc + BitVec.ofNat 256 tcq.byteU32Bytes) :=
    venvGet_set_ne (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_pc" (wAddmod x (wMulmod lv rv)) (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (by decide : "q_top" ≠ "q_pc") g55
  have g84 :
    VEnv.get (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) "q_rhs" = some (BitVec.ofNat 256 r) :=
    venvGet_set_ne (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_rhs" (wAddmod x (wMulmod lv rv)) (BitVec.ofNat 256 r) (by decide : "q_top" ≠ "q_rhs") g51
  have g85 :
    VEnv.get (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_word" (wAddmod x (wMulmod lv rv)) (loadWord st.memory pc.toNat) (by decide : "q_top" ≠ "q_word") g53
  have g86 :
    VEnv.get (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "r" (wAddmod x (wMulmod lv rv)) frModulusWord (by decide : "q_top" ≠ "r") g54
  have g87 :
    VEnv.get (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv))) "q_top" = some (wAddmod x (wMulmod lv rv)) :=
    venvGet_set_same (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv)) x g52
  unfold GenAst.qArmBodyAddMulMemMem
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_word", loadWord st.memory pc.toNat) :: V)) (st1 := (touchMemory st pc.toNat 32)) s6 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (st1 := (touchMemory st pc.toNat 32)) s18 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (st1 := (touchMemory st pc.toNat 32)) s36 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes))) (st1 := (touchMemory st pc.toNat 32)) s49 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (wAddmod x (wMulmod lv rv)))) (st1 := (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32)) s81 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_addMulMemMem {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc x lv rv : U256) (l r : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMulMemMem ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 l ∧
        (((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535) = BitVec.ofNat 256 r ∧
        loadWord st.memory (BitVec.ofNat 256 l).toNat = lv ∧
        loadWord st.memory (BitVec.ofNat 256 r).toNat = rv)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul lv.toNat rv.toNat))))) := by
  intro V st hpre
  have hrun := qArmRun_addMulMemMem ctx program tcq funs V st pc x lv rv l r hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2
  rw [wAddmod_wMulmod_eq_qvmFr_addMulMemMem] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_addMulMemMem {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc x lv rv : U256) (l r : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMulMemMem ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 l ∧
        (((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535) = BitVec.ofNat 256 r ∧
        loadWord st.memory (BitVec.ofNat 256 l).toNat = lv ∧
        loadWord st.memory (BitVec.ofNat 256 r).toNat = rv)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul lv.toNat rv.toNat))))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_addMulMemMem ctx program tcq funs pc x lv rv l r )

theorem wAddmod_wMulmod_eq_qvmFr_addMulConstU8MemU16 (x pv cv : U256) :
    wAddmod x (wMulmod pv cv) = BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul pv.toNat cv.toNat)) := by rw [wAddmod_eq_qvmFrAdd, wMulmod_toNat]

theorem qArmRun_addMulConstU8MemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb x pv cv : U256) (p b : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hp : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p)
    (hb : (((loadWord st.memory pc.toNat) >>> 232) &&& 0xff) = BitVec.ofNat 256 b)
    (hpv : loadWord st.memory (BitVec.ofNat 256 p).toNat = pv)
    (hcv : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = cv) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAddMulConstU8MemU16 ctx program tcq)
      (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal := by
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
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne V "q_word" "q_const_mptr" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_const_mptr")]; exact hget_cb
  have g8 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_word" "q_pc" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_pc")]; exact hget_pc
  have g9 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_word" "q_top" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_top")]; exact hget_top
  have g10 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "q_word" "r" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "r")]; exact hget_r
  have g11 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_cons_eq V "q_word" (loadWord st.memory pc.toNat)
  have a12 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x13 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g11
  have a14 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a12 x13
  have x15 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 240)) (.eres (.vals [BitVec.ofNat 256 240] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 240)
  have a16 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [ylit 240, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 240, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 240) (st2 := touchMemory st pc.toNat 32) a14 x15
  have x17 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 240, yvar "q_word"])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 240)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a16 (qbi_shr240 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d18 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 240, yvar "q_word"])) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    by rw [<- hp]; exact x17
  have s19 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.stmt (ylet "q_ptr" (yop Op.shr [ylit 240, yvar "q_word"]))) (.sres (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d18 rfl
  have g20 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_ptr" "q_const_mptr" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_const_mptr")]; exact g7
  have g21 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_ptr" "q_pc" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_pc")]; exact g8
  have g22 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_ptr" "q_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_top")]; exact g9
  have g23 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_ptr" "q_word" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_word")]; exact g11
  have g24 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_ptr" "r" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "r")]; exact g10
  have g25 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_cons_eq (("q_word", loadWord st.memory pc.toNat) :: V) "q_ptr" (BitVec.ofNat 256 p)
  have a26 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x27 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g23
  have a28 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a26 x27
  have x29 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a30 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 2, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 2, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory st pc.toNat 32) a28 x29
  have x31 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.byte [ylit 2, yvar "q_word"])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 232) &&& 0xff)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a30 (qbi_byte2 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d32 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.byte [ylit 2, yvar "q_word"])) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    by rw [<- hb]; exact x31
  have s33 :
    Step (D := Bridge.Dialect c g) funs (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.stmt (ylet "qconst" (yop Op.byte [ylit 2, yvar "q_word"]))) (.sres (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d32 rfl
  have g34 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" "q_const_mptr" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_const_mptr")]; exact g20
  have g35 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" "q_pc" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_pc")]; exact g21
  have g36 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_ptr" = some (BitVec.ofNat 256 p) :=
    by rw [venvGet_cons_ne (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" "q_ptr" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_ptr")]; exact g25
  have g37 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" "q_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_top")]; exact g22
  have g38 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" "q_word" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_word")]; exact g23
  have g39 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" "r" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "r")]; exact g24
  have g40 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_cons_eq (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "qconst" (BitVec.ofNat 256 b)
  have a41 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x42 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (ylit 3)) (.eres (.vals [BitVec.ofNat 256 3] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 3)
  have a43 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [ylit 3]) (.eres (.vals [BitVec.ofNat 256 3] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 3) (st2 := touchMemory st pc.toNat 32) a41 x42
  have x44 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g35
  have a45 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 3]) (.eres (.vals [pc, BitVec.ofNat 256 3] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 3]) (restvals := [BitVec.ofNat 256 3]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a43 x44
  have x46 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 3])) (.eres (.vals [(pc + BitVec.ofNat 256 3)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a45 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 3))
  have s47 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 3]))) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 3)]) x46 (by rfl)
  have g48 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 3) cb (by decide : "q_pc" ≠ "q_const_mptr") g34
  have g49 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_ptr" (pc + BitVec.ofNat 256 3) (BitVec.ofNat 256 p) (by decide : "q_pc" ≠ "q_ptr") g36
  have g50 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" = some x :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_top" (pc + BitVec.ofNat 256 3) x (by decide : "q_pc" ≠ "q_top") g37
  have g51 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "q_word" (pc + BitVec.ofNat 256 3) (loadWord st.memory pc.toNat) (by decide : "q_pc" ≠ "q_word") g38
  have g52 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "qconst" (pc + BitVec.ofNat 256 3) (BitVec.ofNat 256 b) (by decide : "q_pc" ≠ "qconst") g40
  have g53 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "r" = some frModulusWord :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" "r" (pc + BitVec.ofNat 256 3) frModulusWord (by decide : "q_pc" ≠ "r") g39
  have g54 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_pc" = some (pc + BitVec.ofNat 256 3) :=
    venvGet_set_same (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3) pc g35
  have a55 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x56 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g53
  have a57 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a55 x56
  have a58 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x59 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g53
  have a60 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a58 x59
  have a61 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a62 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a63 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x64 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g52
  have a65 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a63 x64
  have x66 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a67 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [ylit 5, yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 5, BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [BitVec.ofNat 256 b]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a65 x66
  have x68 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yop Op.shl [ylit 5, yvar "qconst"])) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a67 (qbi_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b))
  have a69 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := ((BitVec.ofNat 256 b) <<< 5)) (st2 := touchMemory st pc.toNat 32) a62 x68
  have x70 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yvar "q_const_mptr")) (.eres (.vals [cb] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g48
  have a71 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [cb, ((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [((BitVec.ofNat 256 b) <<< 5)]) (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32) a69 x70
  have x72 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a71 (qbi_add (touchMemory st pc.toNat 32) cb ((BitVec.ofNat 256 b) <<< 5))
  have a73 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := (cb + ((BitVec.ofNat 256 b) <<< 5))) (st2 := touchMemory st pc.toNat 32) a61 x72
  have x74 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a73 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)) w5)
  have d75 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [cv] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    by rw [<- hcv]; exact x74
  have w76 :
    (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) w5
  have a77 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [cv, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := cv) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a60 d75
  have a78 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x79 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "q_ptr")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g49
  have a80 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yvar "q_ptr"]) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := BitVec.ofNat 256 p) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a78 x79
  have x81 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 p).toNat] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a80 (qbi_mload_at (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) st.memory (BitVec.ofNat 256 p) w76)
  have d82 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [pv] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    by rw [<- hpv]; exact x81
  have w83 :
    (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) w76
  have a84 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [pv, cv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (restvals := [cv, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := pv) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) a77 d82
  have x85 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yop Op.mulmod [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"])) (.eres (.vals [wMulmod pv cv] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a84 (qbi_mulmod_atFr (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) pv cv)
  have a86 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yop Op.mulmod [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]) (.eres (.vals [wMulmod pv cv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := wMulmod pv cv) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) a57 x85
  have x87 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g50
  have a88 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mulmod [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]) (.eres (.vals [x, wMulmod pv cv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mulmod [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]) (restvals := [wMulmod pv cv, frModulusWord]) (st1 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) (v := x) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) a86 x87
  have x89 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.expr (yop Op.addmod [yvar "q_top", yop Op.mulmod [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"])) (.eres (.vals [wAddmod x (wMulmod pv cv)] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a88 (qbi_addmod_atFr (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) x (wMulmod pv cv))
  have s90 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.addmod [yvar "q_top", yop Op.mulmod [yop Op.mload [yvar "q_ptr"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod x (wMulmod pv cv)]) x89 (by rfl)
  have g91 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" "q_const_mptr" (wAddmod x (wMulmod pv cv)) cb (by decide : "q_top" ≠ "q_const_mptr") g48
  have g92 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "q_pc" = some (pc + BitVec.ofNat 256 3) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" "q_pc" (wAddmod x (wMulmod pv cv)) (pc + BitVec.ofNat 256 3) (by decide : "q_top" ≠ "q_pc") g54
  have g93 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" "q_ptr" (wAddmod x (wMulmod pv cv)) (BitVec.ofNat 256 p) (by decide : "q_top" ≠ "q_ptr") g49
  have g94 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" "q_word" (wAddmod x (wMulmod pv cv)) (loadWord st.memory pc.toNat) (by decide : "q_top" ≠ "q_word") g51
  have g95 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" "qconst" (wAddmod x (wMulmod pv cv)) (BitVec.ofNat 256 b) (by decide : "q_top" ≠ "qconst") g52
  have g96 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" "r" (wAddmod x (wMulmod pv cv)) frModulusWord (by decide : "q_top" ≠ "r") g53
  have g97 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv))) "q_top" = some (wAddmod x (wMulmod pv cv)) :=
    venvGet_set_same (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv)) x g50
  unfold GenAst.qArmBodyAddMulConstU8MemU16
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_word", loadWord st.memory pc.toNat) :: V)) (st1 := (touchMemory st pc.toNat 32)) s6 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (st1 := (touchMemory st pc.toNat 32)) s19 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (st1 := (touchMemory st pc.toNat 32)) s33 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3))) (st1 := (touchMemory st pc.toNat 32)) s47 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (wAddmod x (wMulmod pv cv)))) (st1 := (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32)) s90 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_addMulConstU8MemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x pv cv : U256) (p b : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMulConstU8MemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        (((loadWord st.memory pc.toNat) >>> 232) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = pv ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = cv)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul pv.toNat cv.toNat))))) := by
  intro V st hpre
  have hrun := qArmRun_addMulConstU8MemU16 ctx program tcq funs V st pc cb x pv cv p b hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2
  rw [wAddmod_wMulmod_eq_qvmFr_addMulConstU8MemU16] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_addMulConstU8MemU16 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x pv cv : U256) (p b : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMulConstU8MemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        (((loadWord st.memory pc.toNat) >>> 232) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = pv ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = cv)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_ptr", BitVec.ofNat 256 p) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" (pc + BitVec.ofNat 256 3)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul pv.toNat cv.toNat))))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_addMulConstU8MemU16 ctx program tcq funs pc cb x pv cv p b )

theorem wAddmod_wMulmod2_eq_qvmFr_addMulMemMemConstU8 (x lv rv cv : U256) :
    wAddmod x (wMulmod (wMulmod lv rv) cv) = BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul (qvmFrMul lv.toNat rv.toNat) cv.toNat)) := by rw [wAddmod_eq_qvmFrAdd, wMulmod_toNat, wMulmod_toNat]

theorem qArmRun_addMulMemMemConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb x lv rv cv : U256) (l r b : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_r : VEnv.get V "r" = some frModulusWord)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hl : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 l)
    (hr : (((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535) = BitVec.ofNat 256 r)
    (hb : (((loadWord st.memory pc.toNat) >>> 216) &&& 0xff) = BitVec.ofNat 256 b)
    (hlv : loadWord st.memory (BitVec.ofNat 256 l).toNat = lv)
    (hrv : loadWord st.memory (BitVec.ofNat 256 r).toNat = rv)
    (hcv : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = cv) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyAddMulMemMemConstU8 ctx program tcq)
      (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) .normal := by
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
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne V "q_word" "q_const_mptr" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_const_mptr")]; exact hget_cb
  have g8 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_pc" = some pc :=
    by rw [venvGet_cons_ne V "q_word" "q_pc" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_pc")]; exact hget_pc
  have g9 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_top" = some x :=
    by rw [venvGet_cons_ne V "q_word" "q_top" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "q_top")]; exact hget_top
  have g10 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne V "q_word" "r" (loadWord st.memory pc.toNat) (by decide : "q_word" ≠ "r")]; exact hget_r
  have g11 :
    VEnv.get (("q_word", loadWord st.memory pc.toNat) :: V) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_cons_eq V "q_word" (loadWord st.memory pc.toNat)
  have a12 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x13 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g11
  have a14 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a12 x13
  have x15 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 240)) (.eres (.vals [BitVec.ofNat 256 240] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 240)
  have a16 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.args [ylit 240, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 240, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 240) (st2 := touchMemory st pc.toNat 32) a14 x15
  have x17 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 240, yvar "q_word"])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 240)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a16 (qbi_shr240 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d18 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 240, yvar "q_word"])) (.eres (.vals [BitVec.ofNat 256 l] (touchMemory st pc.toNat 32))) :=
    by rw [<- hl]; exact x17
  have s19 :
    Step (D := Bridge.Dialect c g) funs (("q_word", loadWord st.memory pc.toNat) :: V) (touchMemory st pc.toNat 32) (.stmt (ylet "q_lhs" (yop Op.shr [ylit 240, yvar "q_word"]))) (.sres (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d18 rfl
  have g20 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_const_mptr" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_const_mptr")]; exact g7
  have g21 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_pc" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_pc")]; exact g8
  have g22 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_top" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_top")]; exact g9
  have g23 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "q_word" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "q_word")]; exact g11
  have g24 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" "r" (BitVec.ofNat 256 l) (by decide : "q_lhs" ≠ "r")]; exact g10
  have g25 :
    VEnv.get (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_lhs" = some (BitVec.ofNat 256 l) :=
    venvGet_cons_eq (("q_word", loadWord st.memory pc.toNat) :: V) "q_lhs" (BitVec.ofNat 256 l)
  have a26 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x27 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 65535)) (.eres (.vals [BitVec.ofNat 256 65535] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 65535)
  have a28 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 65535]) (.eres (.vals [BitVec.ofNat 256 65535] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 65535) (st2 := touchMemory st pc.toNat 32) a26 x27
  have a29 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x30 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g23
  have a31 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a29 x30
  have x32 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (ylit 224)) (.eres (.vals [BitVec.ofNat 256 224] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 224)
  have a33 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [ylit 224, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 224, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 224) (st2 := touchMemory st pc.toNat 32) a31 x32
  have x34 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.shr [ylit 224, yvar "q_word"])) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 224)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a33 (qbi_shr224 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have a35 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.args [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535]) (.eres (.vals [((loadWord st.memory pc.toNat) >>> 224), BitVec.ofNat 256 65535] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 65535]) (restvals := [BitVec.ofNat 256 65535]) (st1 := touchMemory st pc.toNat 32) (v := ((loadWord st.memory pc.toNat) >>> 224)) (st2 := touchMemory st pc.toNat 32) a28 x34
  have x36 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.and [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a35 (qbi_and (touchMemory st pc.toNat 32) ((loadWord st.memory pc.toNat) >>> 224) (BitVec.ofNat 256 65535))
  have d37 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.expr (yop Op.and [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535])) (.eres (.vals [BitVec.ofNat 256 r] (touchMemory st pc.toNat 32))) :=
    by rw [<- hr]; exact x36
  have s38 :
    Step (D := Bridge.Dialect c g) funs (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) (touchMemory st pc.toNat 32) (.stmt (ylet "q_rhs" (yop Op.and [yop Op.shr [ylit 224, yvar "q_word"], ylit 65535]))) (.sres (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d37 rfl
  have g39 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_const_mptr" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_const_mptr")]; exact g20
  have g40 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_lhs" = some (BitVec.ofNat 256 l) :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_lhs" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_lhs")]; exact g25
  have g41 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_pc" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_pc")]; exact g21
  have g42 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_top" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_top")]; exact g22
  have g43 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "q_word" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "q_word")]; exact g23
  have g44 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" "r" (BitVec.ofNat 256 r) (by decide : "q_rhs" ≠ "r")]; exact g24
  have g45 :
    VEnv.get (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "q_rhs" = some (BitVec.ofNat 256 r) :=
    venvGet_cons_eq (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)) "q_rhs" (BitVec.ofNat 256 r)
  have a46 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x47 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yvar "q_word")) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g43
  have a48 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [yvar "q_word"]) (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32) a46 x47
  have x49 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (ylit 4)) (.eres (.vals [BitVec.ofNat 256 4] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 4)
  have a50 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.args [ylit 4, yvar "q_word"]) (.eres (.vals [BitVec.ofNat 256 4, loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_word"]) (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 4) (st2 := touchMemory st pc.toNat 32) a48 x49
  have x51 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yop Op.byte [ylit 4, yvar "q_word"])) (.eres (.vals [(((loadWord st.memory pc.toNat) >>> 216) &&& 0xff)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a50 (qbi_byte4 (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have d52 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.expr (yop Op.byte [ylit 4, yvar "q_word"])) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    by rw [<- hb]; exact x51
  have s53 :
    Step (D := Bridge.Dialect c g) funs (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (touchMemory st pc.toNat 32) (.stmt (ylet "qconst" (yop Op.byte [ylit 4, yvar "q_word"]))) (.sres (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) .normal) :=
    Step.letVal d52 rfl
  have g54 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_const_mptr" = some cb :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "q_const_mptr" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_const_mptr")]; exact g39
  have g55 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_lhs" = some (BitVec.ofNat 256 l) :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "q_lhs" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_lhs")]; exact g40
  have g56 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" = some pc :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "q_pc" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_pc")]; exact g41
  have g57 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_rhs" = some (BitVec.ofNat 256 r) :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "q_rhs" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_rhs")]; exact g45
  have g58 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_top" = some x :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "q_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_top")]; exact g42
  have g59 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_word" = some (loadWord st.memory pc.toNat) :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "q_word" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_word")]; exact g43
  have g60 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "r" = some frModulusWord :=
    by rw [venvGet_cons_ne (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" "r" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "r")]; exact g44
  have g61 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_cons_eq (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) "qconst" (BitVec.ofNat 256 b)
  have a62 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x63 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a64 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.args [ylit 5]) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a62 x63
  have x65 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g56
  have a66 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 5]) (.eres (.vals [pc, BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 5]) (restvals := [BitVec.ofNat 256 5]) (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a64 x65
  have x67 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 5])) (.eres (.vals [(pc + BitVec.ofNat 256 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a66 (qbi_add (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 5))
  have s68 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 5]))) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 5)]) x67 (by rfl)
  have g69 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 5) cb (by decide : "q_pc" ≠ "q_const_mptr") g54
  have g70 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_lhs" = some (BitVec.ofNat 256 l) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "q_lhs" (pc + BitVec.ofNat 256 5) (BitVec.ofNat 256 l) (by decide : "q_pc" ≠ "q_lhs") g55
  have g71 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_rhs" = some (BitVec.ofNat 256 r) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "q_rhs" (pc + BitVec.ofNat 256 5) (BitVec.ofNat 256 r) (by decide : "q_pc" ≠ "q_rhs") g57
  have g72 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" = some x :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "q_top" (pc + BitVec.ofNat 256 5) x (by decide : "q_pc" ≠ "q_top") g58
  have g73 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "q_word" (pc + BitVec.ofNat 256 5) (loadWord st.memory pc.toNat) (by decide : "q_pc" ≠ "q_word") g59
  have g74 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "qconst" (pc + BitVec.ofNat 256 5) (BitVec.ofNat 256 b) (by decide : "q_pc" ≠ "qconst") g61
  have g75 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "r" = some frModulusWord :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" "r" (pc + BitVec.ofNat 256 5) frModulusWord (by decide : "q_pc" ≠ "r") g60
  have g76 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_pc" = some (pc + BitVec.ofNat 256 5) :=
    venvGet_set_same (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5) pc g56
  have a77 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x78 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g75
  have a79 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a77 x78
  have a80 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x81 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g75
  have a82 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := frModulusWord) (st2 := touchMemory st pc.toNat 32) a80 x81
  have a83 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a84 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a85 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x86 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g74
  have a87 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a85 x86
  have x88 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a89 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [ylit 5, yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 5, BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [BitVec.ofNat 256 b]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a87 x88
  have x90 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yop Op.shl [ylit 5, yvar "qconst"])) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a89 (qbi_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b))
  have a91 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := ((BitVec.ofNat 256 b) <<< 5)) (st2 := touchMemory st pc.toNat 32) a84 x90
  have x92 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yvar "q_const_mptr")) (.eres (.vals [cb] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g69
  have a93 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [cb, ((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [((BitVec.ofNat 256 b) <<< 5)]) (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32) a91 x92
  have x94 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a93 (qbi_add (touchMemory st pc.toNat 32) cb ((BitVec.ofNat 256 b) <<< 5))
  have a95 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := (cb + ((BitVec.ofNat 256 b) <<< 5))) (st2 := touchMemory st pc.toNat 32) a83 x94
  have x96 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a95 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)) w5)
  have d97 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [cv] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    by rw [<- hcv]; exact x96
  have w98 :
    (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) w5
  have a99 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [cv, frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := cv) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a82 d97
  have a100 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x101 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "r")) (.eres (.vals [frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g75
  have a102 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yvar "r"]) (.eres (.vals [frModulusWord] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := frModulusWord) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a100 x101
  have a103 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x104 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "q_rhs")) (.eres (.vals [BitVec.ofNat 256 r] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g71
  have a105 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yvar "q_rhs"]) (.eres (.vals [BitVec.ofNat 256 r] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := BitVec.ofNat 256 r) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a103 x104
  have x106 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.mload [yvar "q_rhs"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 r).toNat] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.builtinOk a105 (qbi_mload_at (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) st.memory (BitVec.ofNat 256 r) w98)
  have d107 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.mload [yvar "q_rhs"])) (.eres (.vals [rv] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    by rw [<- hrv]; exact x106
  have w108 :
    (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) w98
  have a109 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yop Op.mload [yvar "q_rhs"], yvar "r"]) (.eres (.vals [rv, frModulusWord] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := rv) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) a102 d107
  have a110 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x111 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (.expr (yvar "q_lhs")) (.eres (.vals [BitVec.ofNat 256 l] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g70
  have a112 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (.args [yvar "q_lhs"]) (.eres (.vals [BitVec.ofNat 256 l] (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (v := BitVec.ofNat 256 l) (st2 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) a110 x111
  have x113 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (.expr (yop Op.mload [yvar "q_lhs"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 l).toNat] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a112 (qbi_mload_at (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) st.memory (BitVec.ofNat 256 l) w108)
  have d114 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (.expr (yop Op.mload [yvar "q_lhs"])) (.eres (.vals [lv] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    by rw [<- hlv]; exact x113
  have w115 :
    (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) w108
  have a116 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"]) (.eres (.vals [lv, rv, frModulusWord] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_rhs"], yvar "r"]) (restvals := [rv, frModulusWord]) (st1 := touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (v := lv) (st2 := touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a109 d114
  have x117 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"])) (.eres (.vals [wMulmod lv rv] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a116 (qbi_mulmod_atFr (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) lv rv)
  have a118 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (.eres (.vals [wMulmod lv rv, cv, frModulusWord] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"]) (restvals := [cv, frModulusWord]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := wMulmod lv rv) (st2 := touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a99 x117
  have x119 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yop Op.mulmod [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"])) (.eres (.vals [wMulmod (wMulmod lv rv) cv] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a118 (qbi_mulmod_atFr (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) (wMulmod lv rv) cv)
  have a120 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yop Op.mulmod [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]) (.eres (.vals [wMulmod (wMulmod lv rv) cv, frModulusWord] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "r"]) (restvals := [frModulusWord]) (st1 := touchMemory st pc.toNat 32) (v := wMulmod (wMulmod lv rv) cv) (st2 := touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a79 x119
  have x121 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) (.expr (yvar "q_top")) (.eres (.vals [x] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g72
  have a122 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.args [yvar "q_top", yop Op.mulmod [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]) (.eres (.vals [x, wMulmod (wMulmod lv rv) cv, frModulusWord] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mulmod [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]) (restvals := [wMulmod (wMulmod lv rv) cv, frModulusWord]) (st1 := touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) (v := x) (st2 := touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) a120 x121
  have x123 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.expr (yop Op.addmod [yvar "q_top", yop Op.mulmod [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"])) (.eres (.vals [wAddmod x (wMulmod (wMulmod lv rv) cv)] (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32))) :=
    Step.builtinOk a122 (qbi_addmod_atFr (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) x (wMulmod (wMulmod lv rv) cv))
  have s124 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.addmod [yvar "q_top", yop Op.mulmod [yop Op.mulmod [yop Op.mload [yvar "q_lhs"], yop Op.mload [yvar "q_rhs"], yvar "r"], yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]], yvar "r"], yvar "r"]))) (.sres (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [wAddmod x (wMulmod (wMulmod lv rv) cv)]) x123 (by rfl)
  have g125 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "q_const_mptr" (wAddmod x (wMulmod (wMulmod lv rv) cv)) cb (by decide : "q_top" ≠ "q_const_mptr") g69
  have g126 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "q_lhs" = some (BitVec.ofNat 256 l) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "q_lhs" (wAddmod x (wMulmod (wMulmod lv rv) cv)) (BitVec.ofNat 256 l) (by decide : "q_top" ≠ "q_lhs") g70
  have g127 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "q_pc" = some (pc + BitVec.ofNat 256 5) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "q_pc" (wAddmod x (wMulmod (wMulmod lv rv) cv)) (pc + BitVec.ofNat 256 5) (by decide : "q_top" ≠ "q_pc") g76
  have g128 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "q_rhs" = some (BitVec.ofNat 256 r) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "q_rhs" (wAddmod x (wMulmod (wMulmod lv rv) cv)) (BitVec.ofNat 256 r) (by decide : "q_top" ≠ "q_rhs") g71
  have g129 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "q_word" = some (loadWord st.memory pc.toNat) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "q_word" (wAddmod x (wMulmod (wMulmod lv rv) cv)) (loadWord st.memory pc.toNat) (by decide : "q_top" ≠ "q_word") g73
  have g130 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "qconst" (wAddmod x (wMulmod (wMulmod lv rv) cv)) (BitVec.ofNat 256 b) (by decide : "q_top" ≠ "qconst") g74
  have g131 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "r" = some frModulusWord :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" "r" (wAddmod x (wMulmod (wMulmod lv rv) cv)) frModulusWord (by decide : "q_top" ≠ "r") g75
  have g132 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv))) "q_top" = some (wAddmod x (wMulmod (wMulmod lv rv) cv)) :=
    venvGet_set_same (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv)) x g72
  unfold GenAst.qArmBodyAddMulMemMemConstU8
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_word", loadWord st.memory pc.toNat) :: V)) (st1 := (touchMemory st pc.toNat 32)) s6 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))) (st1 := (touchMemory st pc.toNat 32)) s19 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) (st1 := (touchMemory st pc.toNat 32)) s38 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V))))) (st1 := (touchMemory st pc.toNat 32)) s53 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5))) (st1 := (touchMemory st pc.toNat 32)) s68 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (wAddmod x (wMulmod (wMulmod lv rv) cv)))) (st1 := (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32)) s124 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_addMulMemMemConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x lv rv cv : U256) (l r b : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMulMemMemConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 l ∧
        (((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535) = BitVec.ofNat 256 r ∧
        (((loadWord st.memory pc.toNat) >>> 216) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (BitVec.ofNat 256 l).toNat = lv ∧
        loadWord st.memory (BitVec.ofNat 256 r).toNat = rv ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = cv)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul (qvmFrMul lv.toNat rv.toNat) cv.toNat))))) := by
  intro V st hpre
  have hrun := qArmRun_addMulMemMemConstU8 ctx program tcq funs V st pc cb x lv rv cv l r b hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2.2.2
  rw [wAddmod_wMulmod2_eq_qvmFr_addMulMemMemConstU8] at hrun
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_addMulMemMemConstU8 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb x lv rv cv : U256) (l r b : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyAddMulMemMemConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "r" = some frModulusWord ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 l ∧
        (((loadWord st.memory pc.toNat) >>> 224) &&& BitVec.ofNat 256 65535) = BitVec.ofNat 256 r ∧
        (((loadWord st.memory pc.toNat) >>> 216) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (BitVec.ofNat 256 l).toNat = lv ∧
        loadWord st.memory (BitVec.ofNat 256 r).toNat = rv ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = cv)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (BitVec.ofNat 256 r).toNat 32) (BitVec.ofNat 256 l).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: (("q_rhs", BitVec.ofNat 256 r) :: (("q_lhs", BitVec.ofNat 256 l) :: (("q_word", loadWord st.memory pc.toNat) :: V)))) "q_pc" (pc + BitVec.ofNat 256 5)) "q_top" (BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul (qvmFrMul lv.toNat rv.toNat) cv.toNat))))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_addMulMemMemConstU8 ctx program tcq funs pc cb x lv rv cv l r b )

theorem qArmRun_pushMemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc sp x : U256) (p v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 0)
    (hget_top : VEnv.get V "q_top" = some x)
    (hptr : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemU16 ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal := by
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
  have g13 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_has_top" = some 0 :=
    by rw [venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_has_top")]; exact hget_ht
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
  have g25 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_has_top" = some 0 :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) 0 (by decide : "q_pc" ≠ "q_has_top") g13
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
  have x30 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "q_has_top")) (.eres (.vals [0] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g25
  have z31 : 0 = (Bridge.Dialect c g).zero := rfl
  have s32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yif (yvar "q_has_top") [yif (yop Op.gt [yvar "q_sp", ylit program.guards.stackLast]) [yexpr (ycall "q_program_fail" [])], yexpr (yop Op.mstore [yvar "q_sp", yvar "q_top"]), yset "q_sp" (yop Op.add [yvar "q_sp", ylit 32])])) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x30 z31
  have a33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x34 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yvar "q_ptr")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a35 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.args [yvar "q_ptr"]) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 p) (st2 := touchMemory st pc.toNat 32) a33 x34
  have x36 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 p).toNat] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a35 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (BitVec.ofNat 256 p) w6)
  have d37 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [BitVec.ofNat 256 v] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    by rw [<- hload]; exact x36
  have w38 :
    (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) w6
  have s39 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.mload [yvar "q_ptr"]))) (.sres (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [BitVec.ofNat 256 v]) d37 (by rfl)
  have g40 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" = some 0 :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_has_top" (BitVec.ofNat 256 v) 0 (by decide : "q_top" ≠ "q_has_top") g25
  have g41 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_pc" (BitVec.ofNat 256 v) (pc + BitVec.ofNat 256 2) (by decide : "q_top" ≠ "q_pc") g29
  have g42 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_ptr" (BitVec.ofNat 256 v) (BitVec.ofNat 256 p) (by decide : "q_top" ≠ "q_ptr") g26
  have g43 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" "q_sp" (BitVec.ofNat 256 v) sp (by decide : "q_top" ≠ "q_sp") g27
  have g44 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_same (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v) x g28
  have x45 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have s46 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (.stmt (yset "q_has_top" (ylit 1))) (.sres (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_has_top"]) (vals := [BitVec.ofNat 256 1]) x45 (by rfl)
  have g47 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_pc" (BitVec.ofNat 256 1) (pc + BitVec.ofNat 256 2) (by decide : "q_has_top" ≠ "q_pc") g41
  have g48 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_ptr" (BitVec.ofNat 256 1) (BitVec.ofNat 256 p) (by decide : "q_has_top" ≠ "q_ptr") g42
  have g49 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) sp (by decide : "q_has_top" ≠ "q_sp") g43
  have g50 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : "q_has_top" ≠ "q_top") g44
  have g51 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_has_top" = some (BitVec.ofNat 256 1) :=
    venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 0 g40
  unfold GenAst.qArmBodyPushMemU16
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s24 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory st pc.toNat 32)) s32 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)) s39 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)) s46 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_pushMemU16 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) := by
  intro V st hpre
  have hrun := qArmRun_pushMemU16 ctx program tcq funs V st pc sp x p v hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_pushMemU16 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushMemU16 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushMemU16 ctx program tcq funs pc sp x p v )

theorem qArmRun_pushMemLiteral {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc sp x : U256) (p v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 0)
    (hget_top : VEnv.get V "q_top" = some x)
    (hptr : ((loadWord st.memory pc.toNat) >>> 224) = BitVec.ofNat 256 p)
    (hload : loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushMemLiteral ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal := by
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
  have g13 :
    VEnv.get (("q_ptr", BitVec.ofNat 256 p) :: V) "q_has_top" = some 0 :=
    by rw [venvGet_cons_ne V "q_ptr" "q_has_top" (BitVec.ofNat 256 p) (by decide : "q_ptr" ≠ "q_has_top")]; exact hget_ht
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
  have g25 :
    VEnv.get (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_has_top" = some 0 :=
    venvGet_set_ne (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 tcq.byteU32Bytes) 0 (by decide : "q_pc" ≠ "q_has_top") g13
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
  have x30 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yvar "q_has_top")) (.eres (.vals [0] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g25
  have z31 : 0 = (Bridge.Dialect c g).zero := rfl
  have s32 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.stmt (yif (yvar "q_has_top") [yif (yop Op.gt [yvar "q_sp", ylit program.guards.stackLast]) [yexpr (ycall "q_program_fail" [])], yexpr (yop Op.mstore [yvar "q_sp", yvar "q_top"]), yset "q_sp" (yop Op.add [yvar "q_sp", ylit 32])])) (.sres (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x30 z31
  have a33 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x34 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yvar "q_ptr")) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g26
  have a35 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.args [yvar "q_ptr"]) (.eres (.vals [BitVec.ofNat 256 p] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 p) (st2 := touchMemory st pc.toNat 32) a33 x34
  have x36 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [loadWord st.memory (BitVec.ofNat 256 p).toNat] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.builtinOk a35 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (BitVec.ofNat 256 p) w6)
  have d37 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yvar "q_ptr"])) (.eres (.vals [BitVec.ofNat 256 v] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    by rw [<- hload]; exact x36
  have w38 :
    (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) w6
  have s39 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.mload [yvar "q_ptr"]))) (.sres (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [BitVec.ofNat 256 v]) d37 (by rfl)
  have g40 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" = some 0 :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_has_top" (BitVec.ofNat 256 v) 0 (by decide : "q_top" ≠ "q_has_top") g25
  have g41 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_pc" = some (pc + BitVec.ofNat 256 tcq.byteU32Bytes) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_pc" (BitVec.ofNat 256 v) (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (by decide : "q_top" ≠ "q_pc") g29
  have g42 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_ptr" (BitVec.ofNat 256 v) (BitVec.ofNat 256 p) (by decide : "q_top" ≠ "q_ptr") g26
  have g43 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" "q_sp" (BitVec.ofNat 256 v) sp (by decide : "q_top" ≠ "q_sp") g27
  have g44 :
    VEnv.get (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_same (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v) x g28
  have x45 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have s46 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) (.stmt (yset "q_has_top" (ylit 1))) (.sres (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_has_top"]) (vals := [BitVec.ofNat 256 1]) x45 (by rfl)
  have g47 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" = some (pc + BitVec.ofNat 256 tcq.byteU32Bytes) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_pc" (BitVec.ofNat 256 1) (pc + BitVec.ofNat 256 tcq.byteU32Bytes) (by decide : "q_has_top" ≠ "q_pc") g41
  have g48 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_ptr" = some (BitVec.ofNat 256 p) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_ptr" (BitVec.ofNat 256 1) (BitVec.ofNat 256 p) (by decide : "q_has_top" ≠ "q_ptr") g42
  have g49 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) sp (by decide : "q_has_top" ≠ "q_sp") g43
  have g50 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : "q_has_top" ≠ "q_top") g44
  have g51 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_has_top" = some (BitVec.ofNat 256 1) :=
    venvGet_set_same (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 0 g40
  unfold GenAst.qArmBodyPushMemLiteral
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("q_ptr", BitVec.ofNat 256 p) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes))) (st1 := (touchMemory st pc.toNat 32)) s24 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes))) (st1 := (touchMemory st pc.toNat 32)) s32 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)) s39 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)) s46 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_pushMemLiteral {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushMemLiteral ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 224) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) := by
  intro V st hpre
  have hrun := qArmRun_pushMemLiteral ctx program tcq funs V st pc sp x p v hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_pushMemLiteral {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc sp x : U256) (p v : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushMemLiteral ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        ((loadWord st.memory pc.toNat) >>> 224) = BitVec.ofNat 256 p ∧
        loadWord st.memory (BitVec.ofNat 256 p).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (BitVec.ofNat 256 p).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("q_ptr", BitVec.ofNat 256 p) :: V) "q_pc" (pc + BitVec.ofNat 256 tcq.byteU32Bytes)) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushMemLiteral ctx program tcq funs pc sp x p v )

theorem qArmRun_pushConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb sp x : U256) (b v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 0)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hdec : (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b)
    (hconst : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushConstU8 ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal := by
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
  have g14 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_has_top" = some 0 :=
    by rw [venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_has_top")]; exact hget_ht
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
  have x19 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_has_top")) (.eres (.vals [0] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g14
  have z20 : 0 = (Bridge.Dialect c g).zero := rfl
  have s21 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yif (yvar "q_has_top") [yif (yop Op.gt [yvar "q_sp", ylit program.guards.stackLast]) [yexpr (ycall "q_program_fail" [])], yexpr (yop Op.mstore [yvar "q_sp", yvar "q_top"]), yset "q_sp" (yop Op.add [yvar "q_sp", ylit 32])])) (.sres (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x19 z20
  have a22 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a23 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a24 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x25 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g18
  have a26 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a24 x25
  have x27 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a28 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [ylit 5, yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 5, BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [BitVec.ofNat 256 b]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a26 x27
  have x29 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shl [ylit 5, yvar "qconst"])) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a28 (qbi_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b))
  have a30 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := ((BitVec.ofNat 256 b) <<< 5)) (st2 := touchMemory st pc.toNat 32) a23 x29
  have x31 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_const_mptr")) (.eres (.vals [cb] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g13
  have a32 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [cb, ((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [((BitVec.ofNat 256 b) <<< 5)]) (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32) a30 x31
  have x33 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a32 (qbi_add (touchMemory st pc.toNat 32) cb ((BitVec.ofNat 256 b) <<< 5))
  have a34 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := (cb + ((BitVec.ofNat 256 b) <<< 5))) (st2 := touchMemory st pc.toNat 32) a22 x33
  have x35 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a34 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)) w6)
  have d36 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [BitVec.ofNat 256 v] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    by rw [<- hconst]; exact x35
  have w37 :
    (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) w6
  have s38 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]))) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [BitVec.ofNat 256 v]) d36 (by rfl)
  have g39 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_const_mptr" (BitVec.ofNat 256 v) cb (by decide : "q_top" ≠ "q_const_mptr") g13
  have g40 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" = some 0 :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_has_top" (BitVec.ofNat 256 v) 0 (by decide : "q_top" ≠ "q_has_top") g14
  have g41 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_pc" = some pc :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_pc" (BitVec.ofNat 256 v) pc (by decide : "q_top" ≠ "q_pc") g15
  have g42 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_sp" = some sp :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_sp" (BitVec.ofNat 256 v) sp (by decide : "q_top" ≠ "q_sp") g16
  have g43 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "qconst" (BitVec.ofNat 256 v) (BitVec.ofNat 256 b) (by decide : "q_top" ≠ "qconst") g18
  have g44 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_same (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v) x g17
  have x45 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have s46 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.stmt (yset "q_has_top" (ylit 1))) (.sres (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_has_top"]) (vals := [BitVec.ofNat 256 1]) x45 (by rfl)
  have g47 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_const_mptr" (BitVec.ofNat 256 1) cb (by decide : "q_has_top" ≠ "q_const_mptr") g39
  have g48 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" = some pc :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_pc" (BitVec.ofNat 256 1) pc (by decide : "q_has_top" ≠ "q_pc") g41
  have g49 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) sp (by decide : "q_has_top" ≠ "q_sp") g42
  have g50 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : "q_has_top" ≠ "q_top") g44
  have g51 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "qconst" (BitVec.ofNat 256 1) (BitVec.ofNat 256 b) (by decide : "q_has_top" ≠ "qconst") g43
  have g52 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_has_top" = some (BitVec.ofNat 256 1) :=
    venvGet_set_same (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 0 g40
  have a53 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x54 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have a55 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [ylit 1]) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := BitVec.ofNat 256 1) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a53 x54
  have x56 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g48
  have a57 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yvar "q_pc", ylit 1]) (.eres (.vals [pc, BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 1]) (restvals := [BitVec.ofNat 256 1]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := pc) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a55 x56
  have x58 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 1])) (.eres (.vals [(pc + BitVec.ofNat 256 1)] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a57 (qbi_add (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) pc (BitVec.ofNat 256 1))
  have s59 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 1]))) (.sres (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 1)]) x58 (by rfl)
  have g60 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 1) cb (by decide : "q_pc" ≠ "q_const_mptr") g47
  have g61 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) "q_has_top" = some (BitVec.ofNat 256 1) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 1) (by decide : "q_pc" ≠ "q_has_top") g52
  have g62 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 1) sp (by decide : "q_pc" ≠ "q_sp") g49
  have g63 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : "q_pc" ≠ "q_top") g50
  have g64 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "qconst" (pc + BitVec.ofNat 256 1) (BitVec.ofNat 256 b) (by decide : "q_pc" ≠ "qconst") g51
  have g65 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1)) "q_pc" = some (pc + BitVec.ofNat 256 1) :=
    venvGet_set_same (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1) pc g48
  unfold GenAst.qArmBodyPushConstU8
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s21 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s38 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s46 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s59 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_pushConstU8 {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1))) := by
  intro V st hpre
  have hrun := qArmRun_pushConstU8 ctx program tcq funs V st pc cb sp x b v hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_pushConstU8 {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushConstU8 ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 1))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushConstU8 ctx program tcq funs pc cb sp x b v )

theorem qArmRun_pushConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (pc cb sp x : U256) (b v : Nat)
    (hget_pc : VEnv.get V "q_pc" = some pc)
    (hget_sp : VEnv.get V "q_sp" = some sp)
    (hget_ht : VEnv.get V "q_has_top" = some 0)
    (hget_top : VEnv.get V "q_top" = some x)
    (hget_cb : VEnv.get V "q_const_mptr" = some cb)
    (hdec : ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b)
    (hconst : loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    ExecStmts (Bridge.Dialect c g) funs V st (GenAst.qArmBodyPushConst ctx program tcq)
      (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal := by
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
  have g14 :
    VEnv.get (("qconst", BitVec.ofNat 256 b) :: V) "q_has_top" = some 0 :=
    by rw [venvGet_cons_ne V "qconst" "q_has_top" (BitVec.ofNat 256 b) (by decide : "qconst" ≠ "q_has_top")]; exact hget_ht
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
  have x27 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_has_top")) (.eres (.vals [0] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g14
  have z28 : 0 = (Bridge.Dialect c g).zero := rfl
  have s29 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yif (yvar "q_has_top") [yif (yop Op.gt [yvar "q_sp", ylit program.guards.stackLast]) [yexpr (ycall "q_program_fail" [])], yexpr (yop Op.mstore [yvar "q_sp", yvar "q_top"]), yset "q_sp" (yop Op.add [yvar "q_sp", ylit 32])])) (.sres (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) .normal) :=
    Step.ifFalse x27 z28
  have a30 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a31 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have a32 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args []) (.eres (.vals [] (touchMemory st pc.toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x33 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "qconst")) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g18
  have a34 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 b) (st2 := touchMemory st pc.toNat 32) a32 x33
  have x35 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (ylit 5)) (.eres (.vals [BitVec.ofNat 256 5] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 5)
  have a36 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [ylit 5, yvar "qconst"]) (.eres (.vals [BitVec.ofNat 256 5, BitVec.ofNat 256 b] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "qconst"]) (restvals := [BitVec.ofNat 256 b]) (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 5) (st2 := touchMemory st pc.toNat 32) a34 x35
  have x37 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.shl [ylit 5, yvar "qconst"])) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a36 (qbi_shl5 (touchMemory st pc.toNat 32) (BitVec.ofNat 256 b))
  have a38 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := ((BitVec.ofNat 256 b) <<< 5)) (st2 := touchMemory st pc.toNat 32) a31 x37
  have x39 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yvar "q_const_mptr")) (.eres (.vals [cb] (touchMemory st pc.toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g13
  have a40 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]) (.eres (.vals [cb, ((BitVec.ofNat 256 b) <<< 5)] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.shl [ylit 5, yvar "qconst"]]) (restvals := [((BitVec.ofNat 256 b) <<< 5)]) (st1 := touchMemory st pc.toNat 32) (v := cb) (st2 := touchMemory st pc.toNat 32) a38 x39
  have x41 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]])) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a40 (qbi_add (touchMemory st pc.toNat 32) cb ((BitVec.ofNat 256 b) <<< 5))
  have a42 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.args [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]) (.eres (.vals [(cb + ((BitVec.ofNat 256 b) <<< 5))] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory st pc.toNat 32) (v := (cb + ((BitVec.ofNat 256 b) <<< 5))) (st2 := touchMemory st pc.toNat 32) a30 x41
  have x43 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a42 (qbi_mload_at (touchMemory st pc.toNat 32) st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)) w6)
  have d44 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.expr (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]])) (.eres (.vals [BitVec.ofNat 256 v] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    by rw [<- hconst]; exact x43
  have w45 :
    (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32).memory = st.memory :=
    Eq.trans (Midfall.Yul.Word.touchMemory_memory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) w6
  have s46 :
    Step (D := Bridge.Dialect c g) funs (("qconst", BitVec.ofNat 256 b) :: V) (touchMemory st pc.toNat 32) (.stmt (yset "q_top" (yop Op.mload [yop Op.add [yvar "q_const_mptr", yop Op.shl [ylit 5, yvar "qconst"]]]))) (.sres (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_top"]) (vals := [BitVec.ofNat 256 v]) d44 (by rfl)
  have g47 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_const_mptr" = some cb :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_const_mptr" (BitVec.ofNat 256 v) cb (by decide : "q_top" ≠ "q_const_mptr") g13
  have g48 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" = some 0 :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_has_top" (BitVec.ofNat 256 v) 0 (by decide : "q_top" ≠ "q_has_top") g14
  have g49 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_pc" = some pc :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_pc" (BitVec.ofNat 256 v) pc (by decide : "q_top" ≠ "q_pc") g15
  have g50 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_sp" = some sp :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "q_sp" (BitVec.ofNat 256 v) sp (by decide : "q_top" ≠ "q_sp") g16
  have g51 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (("qconst", BitVec.ofNat 256 b) :: V) "q_top" "qconst" (BitVec.ofNat 256 v) (BitVec.ofNat 256 b) (by decide : "q_top" ≠ "qconst") g18
  have g52 :
    VEnv.get (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_same (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v) x g17
  have x53 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (ylit 1)) (.eres (.vals [BitVec.ofNat 256 1] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have s54 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.stmt (yset "q_has_top" (ylit 1))) (.sres (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_has_top"]) (vals := [BitVec.ofNat 256 1]) x53 (by rfl)
  have g55 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_const_mptr" (BitVec.ofNat 256 1) cb (by decide : "q_has_top" ≠ "q_const_mptr") g47
  have g56 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" = some pc :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_pc" (BitVec.ofNat 256 1) pc (by decide : "q_has_top" ≠ "q_pc") g49
  have g57 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_sp" (BitVec.ofNat 256 1) sp (by decide : "q_has_top" ≠ "q_sp") g50
  have g58 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "q_top" (BitVec.ofNat 256 1) (BitVec.ofNat 256 v) (by decide : "q_has_top" ≠ "q_top") g52
  have g59 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" "qconst" (BitVec.ofNat 256 1) (BitVec.ofNat 256 b) (by decide : "q_has_top" ≠ "qconst") g51
  have g60 :
    VEnv.get (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_has_top" = some (BitVec.ofNat 256 1) :=
    venvGet_set_same (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1) 0 g48
  have a61 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args []) (.eres (.vals [] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsNil (D := Bridge.Dialect c g)
  have x62 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (ylit 2)) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 2)
  have a63 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [ylit 2]) (.eres (.vals [BitVec.ofNat 256 2] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := BitVec.ofNat 256 2) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a61 x62
  have x64 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yvar "q_pc")) (.eres (.vals [pc] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.var (D := Bridge.Dialect c g) g56
  have a65 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.args [yvar "q_pc", ylit 2]) (.eres (.vals [pc, BitVec.ofNat 256 2] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 2]) (restvals := [BitVec.ofNat 256 2]) (st1 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (v := pc) (st2 := touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) a63 x64
  have x66 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 2])) (.eres (.vals [(pc + BitVec.ofNat 256 2)] (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32))) :=
    Step.builtinOk a65 (qbi_add (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) pc (BitVec.ofNat 256 2))
  have s67 :
    Step (D := Bridge.Dialect c g) funs (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 2]))) (.sres (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"]) (vals := [(pc + BitVec.ofNat 256 2)]) x66 (by rfl)
  have g68 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) "q_const_mptr" = some cb :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_const_mptr" (pc + BitVec.ofNat 256 2) cb (by decide : "q_pc" ≠ "q_const_mptr") g55
  have g69 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) "q_has_top" = some (BitVec.ofNat 256 1) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_has_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 1) (by decide : "q_pc" ≠ "q_has_top") g60
  have g70 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) "q_sp" = some sp :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_sp" (pc + BitVec.ofNat 256 2) sp (by decide : "q_pc" ≠ "q_sp") g57
  have g71 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) "q_top" = some (BitVec.ofNat 256 v) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "q_top" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 v) (by decide : "q_pc" ≠ "q_top") g58
  have g72 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) "qconst" = some (BitVec.ofNat 256 b) :=
    venvGet_set_ne (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" "qconst" (pc + BitVec.ofNat 256 2) (BitVec.ofNat 256 b) (by decide : "q_pc" ≠ "qconst") g59
  have g73 :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) "q_pc" = some (pc + BitVec.ofNat 256 2) :=
    venvGet_set_same (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2) pc g56
  unfold GenAst.qArmBodyPushConst
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s12 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s26 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (("qconst", BitVec.ofNat 256 b) :: V)) (st1 := (touchMemory st pc.toNat 32)) s29 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s46 ?_
  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s54 ?_
  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2))) (st1 := (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)) s67 (Step.seqNil (D := Bridge.Dialect c g))

theorem qArmValue_pushConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    :
    StmtsContract (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2))) := by
  intro V st hpre
  have hrun := qArmRun_pushConst ctx program tcq funs V st pc cb sp x b v hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2 hguard
  exact ⟨_, _, _, hrun, ⟨rfl, rfl, rfl⟩⟩

theorem qArmValueAll_pushConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    :
    StmtsContractAll (D := Bridge.Dialect c g) funs (GenAst.qArmBodyPushConst ctx program tcq)
      (fun V st => VEnv.get V "q_pc" = some pc ∧
        VEnv.get V "q_sp" = some sp ∧
        VEnv.get V "q_has_top" = some 0 ∧
        VEnv.get V "q_top" = some x ∧
        VEnv.get V "q_const_mptr" = some cb ∧
        ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
        loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v)
      (fun V st V' st' o => o = .normal 
        ∧ st' = (touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32)
        ∧ V' = (VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top" (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2))) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (qArmValue_pushConst ctx program tcq funs pc cb sp x b v hguard)
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_addMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_addMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_addMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_addMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_addMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_addMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_mulMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_mulMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_mulMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_mulMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_mulMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_mulMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_addConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_addConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_addConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_addConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_addConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_addConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_mulConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_mulConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_mulConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_mulConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_mulConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_mulConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_addMulMemMem
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_addMulMemMem
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_addMulMemMem
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_addMulMemMem
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_addMulMemMem
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_addMulMemMem
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_addMulConstU8MemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_addMulConstU8MemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_addMulConstU8MemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_addMulConstU8MemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_addMulConstU8MemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_addMulConstU8MemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_addMulMemMemConstU8
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_addMulMemMemConstU8
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_addMulMemMemConstU8
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_addMulMemMemConstU8
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_addMulMemMemConstU8
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_addMulMemMemConstU8
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_pushMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_pushMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_pushMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_pushMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_pushMemU16
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_pushMemU16
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_pushMemLiteral
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_pushMemLiteral
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_pushMemLiteral
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_pushMemLiteral
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_pushMemLiteral
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_pushMemLiteral
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_pushConstU8
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_pushConstU8
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_pushConstU8
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_pushConstU8
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_pushConstU8
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_pushConstU8
#print axioms Midfall.LoweringV3.QuotientArms.qArmRun_pushConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmRun_pushConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmValue_pushConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValue_pushConst
#print axioms Midfall.LoweringV3.QuotientArms.qArmValueAll_pushConst
#cone_sorries Midfall.LoweringV3.QuotientArms.qArmValueAll_pushConst

/-! ### THE FOURTEEN ARMS THIS CARD DID NOT LAND, AND EXACTLY WHY

Of the 25 arms QARMS left open, 17 have a reference equation in 'QuotientFrame' section B and 8 do
not. All 11 arms landed here are from the 17. The remaining six OF THE SEVENTEEN, and the eight
outside it, are NOT the same work - the reason for each is named below so the next card does not
re-derive it.

**SIX ARMS WITH A REFERENCE EQUATION, NOT LANDED.**

* 'PUSH_MEM_TOKEN', 'PUSH_MEM_TOKEN_OFFSET' - **not "the same work with two reader equations" as the
  brief said, but tractable: three extra ingredients, each checked here and none of them a wall.**
  Their bodies contain
  'Stmt.switch q_token CASES (some [q_program_fail()])' where CASES is a nine-way append of
  'if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [...])] else []' terms. To execute the
  switch, 'Step.switchExec' asks for a 'Step' on '.stmt (.block (selectSwitch D cv CASES dflt))'
  (BigStep.lean:262), and 'selectSwitch' reduces through
  'CASES.find? (fun p => decide (cv = D.litValue p.1))'. Two things block that reduction:
  (i) the nine 'if program.memUsage.X' guards are undecided, so CASES is not a syntactic cons - the
  arm needs at least 'program.memUsage.l0 = true' as a per-arm hypothesis; and (ii) the labels are
  'tcq.mem.X', SYMBOLIC template values, so 'decide (cv = D.litValue p.1)' will not reduce unless the
  scrutinee is pinned to one of them, i.e. 'htok : q_token = BitVec.ofNat 256 tcq.mem.l0', discharged
  by 'decide_eq_true (Eq.refl _)'. THEN the block introduces 'restore' (see the recipe below).
  THE RECIPE, CHECKED: with 'hl0 : program.memUsage.l0 = true' and the scrutinee pinned to
  'BitVec.ofNat 256 tcq.mem.l0',

    rw [hl0]
    rw [selectSwitch]
    have h2 : decide (BitVec.ofNat 256 tcq.mem.l0 =
        (Bridge.Dialect c g).litValue ((Literal.number tcq.mem.l0, body).1)) = true :=
      decide_eq_true (Eq.refl _)
    simp only [List.find?, h2]

  reduces the switch to the single-statement body - 'find?' short-circuits, so the other eight flags
  are irrelevant. What remains is 'Step.block' and so 'restore', i.e. the recipe below.
* 'LIN7', 'BILIN7_ROW', 'BILIN7_PAIRWISE', 'MODARITH7' - **the emitted 'yfor' iterates a SYMBOLIC
  count.** 'lin7' loops while 'q_i < tcq.limbCount', and 'limbCount' is a field of
  'QuotientVmTemplateConstants' (VmTypes.lean:987), not a literal; the KAT
  'limbCounts_crossCheckAccumulatorLimbs_ok' pins the DEFAULT to 'quotientVmLimbs', but the arm is
  stated for an arbitrary 'tcq' (D-P71 forbids pinning it). No finite unrolling proves it: the arm
  needs a loop invariant and an induction over 'Step.loopStep'/'Step.loopDone' against the reference's
  'limbLinearForm' fold. That is section F's unlanded loop wall, not arm work - and it is the same
  obstacle for the three count-prefixed arms below.

**EIGHT ARMS WITH NO REFERENCE EQUATION ANYWHERE IN THE TREE.** Section B states 'qStepValue_X' for 23
arms; these eight are not among them, so the middle theorem of the triple - the one that identifies
the emitted word with what the reference PUSHES - has nothing to be stated against.

* 'RUN_ADD_MUL_MEM_MEM_CONST_U8', 'RUN_ADD_MUL_CONST_U8_MEM_U16', 'AFFINE_SUM' - count-prefixed runs;
  the reference side is a 'foldRangeIdxM' loop over a runtime count word read out of the program.
* 'FOLD_MAIN', 'FOLD_SELECTOR' - the two 'qvmFoldArms'. STATIC (no 'yfor'), so the 'qArmRun' half is
  ordinary work - but they write memory with 'mstore' (a real write: the post-state is 'storeWord',
  not 'touchMemory') and their value goes to 'program.evalNumerMptr', not to 'q_top', so there is no
  'qinterpTop' counterpart to refine.
* 'NATIVE_PERMUTATION', 'NATIVE_LOOKUP', 'NATIVE_IDENTITY' - the bodies end in
  'qGenFlat c.quotientNative*Computation': the statement list is DATA carried in the 'PartialCtx',
  not syntax the emitter spells. A value refinement for them is a theorem about 'qGenFlat' over an
  ARBITRARY computation list - a different deliverable, and 'GenAstQvm.lean' is read-only from here.

**THE ONE PAIR OF FACTS THAT UNLOCKS BOTH THE SWITCH ARMS AND THE NON-EMPTY-STACK PUSH ARMS.** This
card proved them and then did not need them, so they are NOT in the file - land them with whichever
arm uses them:

    theorem venvSet_length {D : Dialect} (V : VEnv D) (x : Ident) (v : D.Value) :
        (VEnv.set V x v).length = V.length
    theorem restore_set {D : Dialect} (V : VEnv D) (x : Ident) (v : D.Value) :
        restore V (VEnv.set V x v) = VEnv.set V x v

Both check at [propext] only. 'Step.block' concludes with '.sres (restore V Vb) stb o'
(BigStep.lean:227) and 'restore outer inner = inner.drop (inner.length - outer.length)', so any arm
that runs a 'Step.block' - the two switch arms, and the 'if q_has_top then [spill]' TRUE branch of the
four PUSH arms this card lands at the EMPTY stack - needs 'restore_set' to get its post-environment
back into the 'VEnv.set' form the contract states.

**WHY THE FOUR PUSH ARMS HERE ARE STATED AT 'q_has_top = 0'.** A one-instruction identity segment
starts with the reference stack '[]' ('evalQuotientIdentity' is called with '[]', QuotientFrame
section A), and 'q_has_top = 0' IS that empty stack - the guard's FALSE branch is the branch the
composition actually takes. The non-empty branch is the same arm plus 'Step.ifTrue', 'Step.block' and
'restore_set', and its post additionally spills the old 'q_top' with an 'mstore' at 'q_sp'. It is not
landed and it is not hidden: the precondition is in the statement.
-/
end Midfall.LoweringV3.QuotientArms

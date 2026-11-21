
import sys
sys.path.insert(0, '/private/tmp')
from gs3 import *

FUNS = "(hoist (Bridge.Dialect c g) mod7ProdBody :: hoist (Bridge.Dialect c g) (mod7Init ctr) :: funs)"
BASE = "((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m)"
ST0 = "(stw m)"
MEM = "(stw m).memory"
GETS = {"q_pc": ("(pc m)", "hpcW"), "q_acc": ("(acc m)", "haccW"),
        "q_const_mptr": ("cm", "hcmW"), "r": ("frModulusWord", "hrW")}
PROD = [
  ('let', 'q_word', OP('mload', [V('q_pc')])),
  ('let', 'qconst', OP('byte', [L(0), V('q_word')])),
  ('let', 'q_lhs', OP('and', [OP('shr', [L(232), V('q_word')]), L(65535)])),
  ('let', 'q_rhs', OP('and', [OP('shr', [L(216), V('q_word')]), L(65535)])),
  ('set', 'q_pc', OP('add', [V('q_pc'), L(5)])),
  ('set', 'q_acc', OP('addmod', [V('q_acc'),
      OP('mulmod', [OP('mulmod', [OP('mload', [V('q_lhs')]), OP('mload', [V('q_rhs')]), V('r')]),
                    OP('mload', [OP('add', [V('q_const_mptr'), OP('shl', [L(5), V('qconst')])])]),
                    V('r')]), V('r')])),
]
g = Gen(FUNS, BASE, GETS, ST0, MEM)
gen, layers, stend = g.stmts(PROD)
gen = chr(10).join(("  " + l) if l.strip() else l for l in gen.split(chr(10)))
ENVA = P(render(layers, BASE))

W = "(loadWord (stw m).memory (pc m).toNat)"
SLOT = "(((%s >>> 248) &&& 0xff))" % W
LHS = "(((%s >>> 232) &&& (BitVec.ofNat 256 65535)))" % W
RHS = "(((%s >>> 216) &&& (BitVec.ofNat 256 65535)))" % W
CPTR = "(cm + (%s <<< 5))" % SLOT
ACCN = "wAddmod (acc m) (wMulmod (wMulmod (loadWord (stw m).memory %s.toNat) (loadWord (stw m).memory %s.toNat)) (loadWord (stw m).memory %s.toNat))" % (LHS, RHS, CPTR)

BODYDEF = '''/-- **THE PRODUCT BLOCK BODY**: the six emitted statements at index 19 of 'qArmBodyModarith7'. Four
    'let's ('q_word', 'qconst', 'q_lhs', 'q_rhs'), then the cursor step of five, then the accumulator
    update. Named so the block lemma and the emitted-text certificate can both point at it. -/
def mod7ProdBody : Block EVM.Op :=
  [ylet "q_word" (yop EVM.Op.mload [yvar "q_pc"]),
   ylet "qconst" (yop EVM.Op.byte [ylit 0, yvar "q_word"]),
   ylet "q_lhs" (yop EVM.Op.and [yop EVM.Op.shr [ylit 232, yvar "q_word"], ylit 65535]),
   ylet "q_rhs" (yop EVM.Op.and [yop EVM.Op.shr [ylit 216, yvar "q_word"], ylit 65535]),
   yset "q_pc" (yop EVM.Op.add [yvar "q_pc", ylit 5]),
   yset "q_acc" (yop EVM.Op.addmod [yvar "q_acc",
     yop EVM.Op.mulmod [yop EVM.Op.mulmod [yop EVM.Op.mload [yvar "q_lhs"],
                                          yop EVM.Op.mload [yvar "q_rhs"], yvar "r"],
                        yop EVM.Op.mload [yop EVM.Op.add [yvar "q_const_mptr",
                                             yop EVM.Op.shl [ylit 5, yvar "qconst"]]],
                        yvar "r"], yvar "r"])]

/-- DROPPING THE FOUR 'let's the PRODUCT body introduces while keeping both register writes: the
    'restore_limb3' shape with one more local ('venvSet_c4' in place of 'venvSet_c3', drop 4 not 3). -/
theorem restore_prod4 {D : YulSemantics.Dialect} (V : VEnv D) (ctr : Ident)
    (iv : D.Value) (w slot lhs rhs pc' acc' : D.Value)
    (hctr_acc : ctr \u2260 "q_acc") (hctr_pc : ctr \u2260 "q_pc") :
    restore ((ctr, iv) :: V)
      (VEnv.set (VEnv.set (("q_rhs", rhs) :: ("q_lhs", lhs) :: ("qconst", slot) :: ("q_word", w) ::
          (ctr, iv) :: V) "q_pc" pc') "q_acc" acc')
      = (ctr, iv) :: VEnv.set (VEnv.set V "q_pc" pc') "q_acc" acc' := by
  have hp1 : VEnv.set (("q_rhs", rhs) :: ("q_lhs", lhs) :: ("qconst", slot) :: ("q_word", w) ::
      (ctr, iv) :: V) "q_pc" pc'
      = ("q_rhs", rhs) :: ("q_lhs", lhs) :: ("qconst", slot) :: ("q_word", w) :: (ctr, iv) ::
        VEnv.set V "q_pc" pc' := by
    rw [venvSet_c4 ((ctr, iv) :: V) "q_word" "qconst" "q_lhs" "q_rhs" w slot lhs rhs pc' "q_pc"
          (by decide : ("q_word" : Ident) \u2260 "q_pc") (by decide : ("qconst" : Ident) \u2260 "q_pc")
          (by decide : ("q_lhs" : Ident) \u2260 "q_pc") (by decide : ("q_rhs" : Ident) \u2260 "q_pc"),
        venvSet_cons_ne V ctr "q_pc" iv pc' hctr_pc]
  have hp2 : VEnv.set (("q_rhs", rhs) :: ("q_lhs", lhs) :: ("qconst", slot) :: ("q_word", w) ::
      (ctr, iv) :: VEnv.set V "q_pc" pc') "q_acc" acc'
      = ("q_rhs", rhs) :: ("q_lhs", lhs) :: ("qconst", slot) :: ("q_word", w) :: (ctr, iv) ::
        VEnv.set (VEnv.set V "q_pc" pc') "q_acc" acc' := by
    rw [venvSet_c4 ((ctr, iv) :: VEnv.set V "q_pc" pc') "q_word" "qconst" "q_lhs" "q_rhs"
          w slot lhs rhs acc' "q_acc"
          (by decide : ("q_word" : Ident) \u2260 "q_acc") (by decide : ("qconst" : Ident) \u2260 "q_acc")
          (by decide : ("q_lhs" : Ident) \u2260 "q_acc") (by decide : ("q_rhs" : Ident) \u2260 "q_acc"),
        venvSet_cons_ne (VEnv.set V "q_pc" pc') ctr "q_acc" iv acc' hctr_acc]
  rw [hp1, hp2]
  unfold restore
  have hlen : List.length (("q_rhs", rhs) :: ("q_lhs", lhs) :: ("qconst", slot) :: ("q_word", w) ::
      (ctr, iv) :: VEnv.set (VEnv.set V "q_pc" pc') "q_acc" acc')
      - List.length ((ctr, iv) :: V) = 4 := by
    simp only [List.length_cons]
    rw [venvSet_length, venvSet_length]
    omega
  rw [hlen]
  rfl

/-- One iteration of the emitted PRODUCT walk: cursor +5, and the two memory operands read in the
    REVERSE of their source order - 'cptr', then 'rhs', then 'lhs' - because 'Step.argsCons' evaluates
    the REST of an argument list before its head. This is the only MODARITH7 block with that reversal. -/
def mod7ProdStep (cm : U256) (s : U256 \u00d7 U256 \u00d7 EvmState) : U256 \u00d7 U256 \u00d7 EvmState :=
  let w := loadWord s.2.2.memory s.1.toNat
  let slot := (w >>> 248) &&& 0xff
  let lhs := (w >>> 232) &&& 65535
  let rhs := (w >>> 216) &&& 65535
  let cptr := cm + (slot <<< 5)
  (s.1 + BitVec.ofNat 256 5,
   wAddmod s.2.1 (wMulmod (wMulmod (loadWord s.2.2.memory lhs.toNat)
                                   (loadWord s.2.2.memory rhs.toNat))
                          (loadWord s.2.2.memory cptr.toNat)),
   touchMemory (touchMemory (touchMemory (touchMemory s.2.2 s.1.toNat 32) cptr.toNat 32)
     rhs.toNat 32) lhs.toNat 32)

def mod7ProdWalk (cm : U256) : Nat \u2192 U256 \u00d7 U256 \u00d7 EvmState \u2192 U256 \u00d7 U256 \u00d7 EvmState
  | 0, s => s
  | m + 1, s => mod7ProdStep cm (mod7ProdWalk cm m s)

theorem mod7ProdWalk_succ (cm : U256) (m : Nat) (s : U256 \u00d7 U256 \u00d7 EvmState) :
    mod7ProdWalk cm (m + 1) s = mod7ProdStep cm (mod7ProdWalk cm m s) := rfl

def mod7ProdFrom (cm pcv accv : U256) (st : EvmState) (m : Nat) : U256 \u00d7 U256 \u00d7 EvmState :=
  mod7ProdWalk cm m (pcv, accv, st)

/-- **ONE PRODUCT-BLOCK ITERATION**: the six-statement emitted body inside a MODARITH7 block loop at a
    symbolic counter 'ctr' and loop-head environment 'V\u2080'. -/
theorem mod7Prod_iter {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (ctr : Ident)
    (V\u2080 : VEnv (Bridge.Dialect c g)) (pcv accv cm : U256) (st : EvmState) (m : Nat)
    (hctr_acc : ctr \u2260 "q_acc") (hctr_pc : ctr \u2260 "q_pc")
    (hctr_cm : ctr \u2260 "q_const_mptr") (hctr_r : ctr \u2260 "r")
    (hget_pc : VEnv.get V\u2080 "q_pc" = some pcv)
    (hget_acc : VEnv.get V\u2080 "q_acc" = some accv)
    (hget_cm : VEnv.get V\u2080 "q_const_mptr" = some cm)
    (hget_r : VEnv.get V\u2080 "r" = some frModulusWord) :
    let pc := fun k => (mod7ProdFrom cm pcv accv st k).1
    let acc := fun k => (mod7ProdFrom cm pcv accv st k).2.1
    let stw := fun k => (mod7ProdFrom cm pcv accv st k).2.2
    Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) (mod7Init ctr) :: funs)
      ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) (stw m) (.stmt (.block mod7ProdBody))
      (.sres ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc (m + 1)) (stw (m + 1)) .normal) := by
  intro pc acc stw
  have hpcW : VEnv.get ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) "q_pc" = some (pc m) := by
    rw [venvGet_cons_ne (mod7Env V\u2080 pc acc m) ctr "q_pc" (BitVec.ofNat 256 m) hctr_pc]
    exact mod7Env_get_pc V\u2080 pc acc pcv hget_pc m
  have haccW : VEnv.get ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) "q_acc" = some (acc m) := by
    rw [venvGet_cons_ne (mod7Env V\u2080 pc acc m) ctr "q_acc" (BitVec.ofNat 256 m) hctr_acc]
    exact mod7Env_get_acc V\u2080 pc acc accv hget_acc m
  have hcmW : VEnv.get ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) "q_const_mptr" = some cm := by
    rw [venvGet_cons_ne (mod7Env V\u2080 pc acc m) ctr "q_const_mptr" (BitVec.ofNat 256 m) hctr_cm]
    exact mod7Env_get_other V\u2080 pc acc "q_const_mptr"
      (by decide : ("q_const_mptr" : Ident) \u2260 "q_acc") (by decide : ("q_const_mptr" : Ident) \u2260 "q_pc")
      cm hget_cm m
  have hrW : VEnv.get ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) "r" = some frModulusWord := by
    rw [venvGet_cons_ne (mod7Env V\u2080 pc acc m) ctr "r" (BitVec.ofNat 256 m) hctr_r]
    exact mod7Env_get_other V\u2080 pc acc "r" (by decide : ("r" : Ident) \u2260 "q_acc")
      (by decide : ("r" : Ident) \u2260 "q_pc") frModulusWord hget_r m
  have hpcS : pc (m + 1) = pc m + BitVec.ofNat 256 5 := rfl
  have haccS : acc (m + 1) = %s := rfl
  have hstS : stw (m + 1) = %s := rfl
  have h1 : Step (D := Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g) mod7ProdBody :: hoist (Bridge.Dialect c g) (mod7Init ctr) :: funs)
      ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) (stw m) (.stmts mod7ProdBody)
      (.sres %s %s .normal) := by
%s
  have hstep : Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) (mod7Init ctr) :: funs)
      ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) (stw m) (.stmt (.block mod7ProdBody))
      (.sres (restore ((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m) %s) %s .normal) :=
    Step.block (D := Bridge.Dialect c g) (body := mod7ProdBody) h1
  convert hstep using 1
  \u00b7 rw [restore_prod4 (mod7Env V\u2080 pc acc m) ctr (BitVec.ofNat 256 m) %s hctr_acc hctr_pc,
      mod7Env_step V\u2080 pc acc m \u27e8pcv, hget_pc\u27e9 \u27e8accv, hget_acc\u27e9, hpcS, haccS, hstS]
''' % (ACCN, stend, ENVA, stend, gen, ENVA, stend,
       " ".join([W, SLOT, LHS, RHS, "(pc m + BitVec.ofNat 256 5)", "(" + ACCN + ")"]))

open('/private/tmp/prod_lean.txt','w').write(BODYDEF)
print("chars", len(BODYDEF))

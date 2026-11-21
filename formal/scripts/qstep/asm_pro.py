"""MOD7C - assemble the MODARITH7 prologue Lean text from the 'gen_pro.py' parts.

Same shape as the preserved 'asm_prod.py': a Lean template with '@@NAME@@' placeholders filled from
the generator. Run 'gen_pro.py' first (or just run this, which imports it).

    python3 formal/scripts/qstep/asm_pro.py     -> writes pro_lean.txt next to it
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_pro import PARTS as P  # noqa: E402

q = chr(34)
nl = chr(10)
ne = chr(8800)   # the Lean not-equal glyph

def steps(key):
    "the generator's (name, env-after, state-after) triples, parsed back out of the parts file"
    out = []
    for line in P[key].split(nl):
        i, rest = line.split(" ", 1)
        # the name is the first token of the 'have' lines; env and state follow - recompute from SEG text
        out.append(rest)
    return out

def names(key):
    "the 'have' names the generator used, in order"
    import re
    return re.findall(r"^  have (\S+) : Step", P[key], re.M)

# ---------------------------------------------------------------- the emitted prologue block
BODY = nl.join([
    "/-- **THE MODARITH7 PROLOGUE**: emitted statements 0-14 of 'qArmBodyModarith7', spelled VERBATIM",
    "    off the emitter's own source by 'gen_pro.emitted_statements' and pinned to the emitted list by",
    "    'mod7_emitted_split' below. The flag guard, the two optional fields, the counts word with its",
    "    FIVE byte extracts, the cursor step of five, and the spill guard at the empty stack. -/",
    "def mod7PrologueBody (program : QuotientProgram) : Block EVM.Op :=",
    "  " + P["BODY_PRO"],
    "",
    "/-- **THE MODARITH7 EPILOGUE**: emitted statements 20-22 - the optional COND gate applied last,",
    "    then the two publishes. Also verbatim. -/",
    "def mod7EpilogueBody : Block EVM.Op :=",
    "  " + P["BODY_EPI"],
    "",
    "/-- **THE FIVE BLOCK LOOPS**: emitted statements 15-19, verbatim. Each is one 'Step.forLoop' fact",
    "    by MOD7/MOD7B's five block lemmas, so the arm is 23 links and not 23 proofs. -/",
    "def mod7MidBody (tcq : QuotientVmTemplateConstants) : Block EVM.Op :=",
    "  " + P["BODY_MID"],
])

# ---------------------------------------------------------------- the closed-form value abbrevs
ABB = nl.join([
    "/-- **THE PROLOGUE'S CLOSED FORM**, one 'abbrev' per derived value, so the arm statement can name",
    "    what the prologue computes instead of spelling 7 KB of nested 'loadWord's. Each body is the",
    "    exact expression the generated derivation produces, so the two meet by 'rfl'. -/",
    "abbrev mod7Flags (st : EvmState) (pcv : U256) : U256 :=",
    "    " + P["FL"],
    "abbrev mod7St1 (st : EvmState) (pcv : U256) : EvmState :=",
    "    " + P["ST1"],
    "abbrev mod7Pc1 (pcv : U256) : U256 := " + P["PC1"],
    "abbrev mod7CondPtr (st : EvmState) (pcv : U256)",
    "    (b0 : Bool) : U256 := " + P["CPV"],
    "abbrev mod7PcA (pcv : U256) (b0 : Bool) : U256 := " + P["PCA"],
    "abbrev mod7StA (st : EvmState) (pcv : U256) (b0 : Bool)",
    "    : EvmState := " + P["STA"],
    "abbrev mod7St3 (st : EvmState) (pcv : U256) (b0 : Bool)",
    "    : EvmState := " + P["ST3"],
    "abbrev mod7Qcv (st : EvmState) (pcv : U256) (b0 : Bool)",
    "    : U256 := " + P["QCV"],
    "abbrev mod7Cptr (cm : U256) (st : EvmState) (pcv : U256)",
    "    (b0 : Bool) : U256 := " + P["CPTR"],
    "abbrev mod7Acc (cm : U256) (st : EvmState) (pcv : U256)",
    "    (b0 b1 : Bool) : U256 := " + P["ACCV"],
    "abbrev mod7PcC (pcv : U256) (b0 b1 : Bool) : U256 := " + P["PCC"],
    "abbrev mod7PcB (pcv : U256) (b0 : Bool) : U256 := " + P["PCB"],
    "abbrev mod7StC (cm : U256) (st : EvmState) (pcv : U256)",
    "    (b0 b1 : Bool) : EvmState := " + P["STC"],
    "abbrev mod7Counts (cm : U256) (st : EvmState)",
    "    (pcv : U256) (b0 b1 : Bool) : U256 := " + P["CW"],
    "abbrev mod7Count0 (cm : U256) (st : EvmState)",
    "    (pcv : U256) (b0 b1 : Bool) : U256 := " + P["C0"],
    "abbrev mod7Count1 (cm : U256) (st : EvmState)",
    "    (pcv : U256) (b0 b1 : Bool) : U256 := " + P["C1"],
    "abbrev mod7Count2 (cm : U256) (st : EvmState)",
    "    (pcv : U256) (b0 b1 : Bool) : U256 := " + P["C2"],
    "abbrev mod7Count3 (cm : U256) (st : EvmState)",
    "    (pcv : U256) (b0 b1 : Bool) : U256 := " + P["C3"],
    "abbrev mod7Count4 (cm : U256) (st : EvmState)",
    "    (pcv : U256) (b0 b1 : Bool) : U256 := " + P["C4"],
    "abbrev mod7PcF (pcv : U256) (b0 b1 : Bool) : U256 := " + P["PCF"],
    "abbrev mod7StF (cm : U256) (st : EvmState) (pcv : U256)",
    "    (b0 b1 : Bool) : EvmState := " + P["ST5"],
])

# ---------------------------------------------------------------- the prologue environment def
CONS = [("q_flags", "fl"), ("q_cond_ptr", "cpv"), ("q_acc", "accv"), ("q_counts_word", "cw"),
        ("q_lin_count", "c0"), ("q_row_count", "c1"), ("q_pairwise_count", "c2"),
        ("q_mem_count", "c3"), ("q_product_count", "c4")]
PARAMS = "fl cpv accv cw c0 c1 c2 c3 c4 pcC pcF"

def env_term():
    s = "VEnv.set V " + q + "q_pc" + q + " pcC"
    for (nm, v) in CONS:
        s = "(" + q + nm + q + ", " + v + ") :: " + s
    return s

ENVDEF = nl.join([
    "/-- **THE PROLOGUE'S POST-ENVIRONMENT** in the shape the derivation leaves it: the nine 'let's the",
    "    prologue binds, on top of the start environment with 'q_pc' written at the cursor the prologue",
    "    arrived at, and with 'q_pc' written once more at its output cursor. 'cpv' is the condition",
    "    pointer (zero when the COND bit is clear), 'accv' the seeded accumulator (zero when the CONST",
    "    bit is clear) - the two optional fields are 'restore'd away by their own 'Step.block', so the",
    "    ENVIRONMENT SHAPE does not depend on the flags, only the VALUES do. -/",
    "def mod7PrologueEnv {c : ExternalCalls} {g : ExternalGas}",
    "    (V : VEnv (Bridge.Dialect c g)) (" + PARAMS + " : U256) :",
    "    VEnv (Bridge.Dialect c g) :=",
    "  VEnv.set (" + env_term() + ") " + q + "q_pc" + q + " pcF",
])

def get_term(x, val, baseproof):
    "VEnv.get (mod7PrologueEnv ...) x = some val, as a term over the def's own parameter names"
    inner_env = "VEnv.set V " + q + "q_pc" + q + " pcC"
    # inner four conses: q_flags, q_cond_ptr, q_acc, q_counts_word
    e4 = inner_env
    for (nm, v) in CONS[:4]:
        e4 = "(" + q + nm + q + ", " + v + ") :: " + e4
    p4 = "venvGet_c4 (" + inner_env + ") " + " ".join(
        [q + nm + q for (nm, v) in CONS[:4]] + [v for (nm, v) in CONS[:4]] +
        [val, q + x + q] + ["(by decide : (" + q + nm + q + " : Ident) " + ne + " " + q + x + q + ")"
                            for (nm, v) in CONS[:4]] + [baseproof])
    p5 = "venvGet_c5 (" + e4 + ") " + " ".join(
        [q + nm + q for (nm, v) in CONS[4:]] + [v for (nm, v) in CONS[4:]] +
        [val, q + x + q] + ["(by decide : (" + q + nm + q + " : Ident) " + ne + " " + q + x + q + ")"
                            for (nm, v) in CONS[4:]] + [p4])
    return p5


def cons_env(upto):
    "the cons list CONS[0..upto-1] over the prologue base"
    s = "VEnv.set V " + q + "q_pc" + q + " pcC"
    for (nm, v) in CONS[:upto]:
        s = "(" + q + nm + q + ", " + v + ") :: " + s
    return s

NE = "(by decide : (" + q + "%s" + q + " : Ident) " + ne + " " + q + "%s" + q + ")"

FMTCONS = ("Eq.trans (venvGet_cons_ne (%s) %s %s %s (by decide : (%s : Ident) " + ne + " %s)) (%s)")

def get_term2(x, val):
    "VEnv.get (mod7PrologueEnv ...) x = some val, over the def's own parameter names"
    inner = "VEnv.set V " + q + "q_pc" + q + " pcC"
    names = [c[0] for c in CONS]
    if x in names:
        k = names.index(x)
        prf = "venvGet_cons_eq (%s) %s %s" % (cons_env(k), q + x + q, val)
        start_i = k + 1
    else:
        prf = SETBASE[x]
        start_i = 0
    for i in range(start_i, len(CONS)):
        (nm, v) = CONS[i]
        prf = (FMTCONS % (cons_env(i), q + nm + q, q + x + q, v, q + nm + q, q + x + q, prf))
    full = cons_env(len(CONS))
    if x == "q_pc":
        prf = "venvGet_set_same (%s) %s pcF pcC (%s)" % (full, q + "q_pc" + q, prf)
    else:
        prf = "venvGet_set_ne (%s) %s %s pcF %s %s (%s)" % (
            full, q + "q_pc" + q, q + x + q, val, dne("q_pc", x), prf)
    return prf

def dne(a, b):
    return "(by decide : (" + q + a + q + " : Ident) " + ne + " " + q + b + q + ")"

def setbase(x, val, hyp):
    return ("venvGet_set_ne V " + q + "q_pc" + q + " " + q + x + q + " pcC " + val + " " +
            dne("q_pc", x) + " " + hyp)

SETBASE = {
    "q_pc": "venvGet_set_same V " + q + "q_pc" + q + " pcC pcv hget_pcV",
    "q_acc": setbase("q_acc", "accv", "hget_accV"),
    "q_const_mptr": setbase("q_const_mptr", "cm", "hget_cmV"),
    "q_has_top": setbase("q_has_top", "(BitVec.ofNat 256 0)", "hget_htV"),
    "q_top": setbase("q_top", "topv", "hget_topV"),
}

GETLEM = []
for (x, val, hyp) in [("q_pc", "pcF", "hget_pcV"), ("q_acc", "accv", "hget_accV"),
                      ("q_const_mptr", "cm", "hget_cmV"),
                      ("q_has_top", "(BitVec.ofNat 256 0)", "hget_htV"),
                      ("q_top", "topv", "hget_topV"),
                      ("q_lin_count", "c0", "hget_pcV"), ("q_row_count", "c1", "hget_pcV"),
                      ("q_pairwise_count", "c2", "hget_pcV"), ("q_mem_count", "c3", "hget_pcV"),
                      ("q_product_count", "c4", "hget_pcV")]:
    GETLEM.append(nl.join([
        "theorem mod7PrologueEnv_get_" + x.replace("q_", "") + " {c : ExternalCalls} {g : ExternalGas}",
        "    (V : VEnv (Bridge.Dialect c g)) (pcv cm topv : U256) (fl cpv accv cw c0 c1 c2 c3 c4 pcC pcF :",
        "    U256) (hget_pcV : VEnv.get V " + q + "q_pc" + q + " = some pcv)",
        "    (hget_accV : VEnv.get V " + q + "q_acc" + q + " = some accv)",
        "    (hget_cmV : VEnv.get V " + q + "q_const_mptr" + q + " = some cm)",
        "    (hget_htV : VEnv.get V " + q + "q_has_top" + q + " = some (BitVec.ofNat 256 0))",
        "    (hget_topV : VEnv.get V " + q + "q_top" + q + " = some topv) :",
        "    VEnv.get (mod7PrologueEnv V " + PARAMS + ") " + q + x + q + " = some " + val + " :=",
        "  by" + nl + "    show VEnv.get (VEnv.set (" + cons_env(len(CONS)) + ") " + q + "q_pc" + q +
              " pcF) " + q + x + q + " = some " + val + nl + "    exact " + get_term2(x, val)]))
GETS = (nl + nl).join(GETLEM)
# ---------------------------------------------------------------- the proof body
def stp(key, i):
    f = P[key].split(nl)[i].split("|")
    return dict(i=int(f[0]), name=f[1], env=f[2], state=f[3])

A = [stp("A_ENVS", i) for i in range(2)]
B = [stp("B_ENVS", i) for i in range(7)]
F = [stp("F_ENVS", i) for i in range(2)]
G = [stp("G_ENVS", i) for i in range(3)]

def ind(s, n):
    pad = " " * n
    return nl.join((pad + l if l.strip() else l) for l in s.split(nl))

def dne(a, b):
    return "(by decide : (" + q + a + q + " : Ident) " + ne + " " + q + b + q + ")"

E15ENV = "(" + B[6]["env"] + ")"  # MOD7D fix 6: spliced bare after funs
E15ST = B[6]["state"]

# the values the two optional branches assign, read back out of the generated environment strings
X4 = F[0]["env"].split(q + "q_cond_ptr" + q + " ", 1)[1]
Y4 = F[1]["env"].split(q + "q_pc" + q + " ", 1)[1]
Q6 = G[0]["env"].split("(\"qconst\", ", 1)[1].split(" :: ")[0][:-1]
PCB6 = G[1]["env"].split(q + "q_pc" + q + " ", 1)[1]
ACC6 = G[2]["env"].split(q + "q_acc" + q + " ", 1)[1]

BODY4 = P["YIF4B"]
BODY6 = P["YIF6B"]
SPILL = P["YIF14B"]


BYTE = nl.join([
    "/-- The two byte extracts the prologue's counts word needs that MOD7 did not: 'byte 1' and",
    "    'byte 3'. Only byte0/2/4 existed, which is why the counts word could not be decoded before. -/",
    "theorem qbi_byte1 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :",
    "    (Bridge.Dialect c g).Builtin Op.byte [BitVec.ofNat 256 1, w] st (.ok [(w >>> 240) &&& 0xff] st) := rfl",
    "",
    "theorem qbi_byte3 {c : ExternalCalls} {g : ExternalGas} (st : EvmState) (w : U256) :",
    "    (Bridge.Dialect c g).Builtin Op.byte [BitVec.ofNat 256 3, w] st (.ok [(w >>> 224) &&& 0xff] st) := rfl",
])

PRELETS = nl.join([
    "  -- the prologue's derived values and intermediate environments, named",
    "  let fl : U256 := mod7Flags st pcv",
    "  let pc1 : U256 := mod7Pc1 pcv",
    "  let st1 : EvmState := mod7St1 st pcv",
    "  let E2 : VEnv (Bridge.Dialect c g) := " + P["E2"],
    "  let E3 : VEnv (Bridge.Dialect c g) := " + P["E3"],
    "  let cpv : U256 := mod7CondPtr st pcv b0",
    "  let pcA : U256 := mod7PcA pcv b0",
    "  let stA : EvmState := mod7StA st pcv b0",
    "  let E4 : VEnv (Bridge.Dialect c g) := " + P["E4"],
    "  let E5 : VEnv (Bridge.Dialect c g) := " + P["E5"],
    "  let accv : U256 := mod7Acc cm st pcv b0 b1",
    "  let pcC : U256 := mod7PcC pcv b0 b1",
    "  let stC : EvmState := mod7StC cm st pcv b0 b1",
    "  let E6 : VEnv (Bridge.Dialect c g) := " + P["E6"],
])

def dne(a, b):
    return "(by decide : (" + q + a + q + " : Ident) " + ne + " " + q + b + q + ")"

def c3get(tail, x, accval, resval, base):
    "VEnv.get ((q_acc,accv) :: (q_cond_ptr,cpv) :: (q_flags,fl) :: VEnv.set V q_pc TAIL) x = some VAL"
    return ("venvGet_c3 (VEnv.set V " + q + "q_pc" + q + " " + tail + ") " +
            q + "q_flags" + q + " " + q + "q_cond_ptr" + q + " " + q + "q_acc" + q +
            " fl cpv " + accval + " " + resval + " " + q + x + q + " " +
            dne("q_flags", x) + " " + dne("q_cond_ptr", x) + " " + dne("q_acc", x) +
            " (" + base + ")")

BASEGETS = nl.join([
    "  -- the register reads the generated segments need at the segment boundaries",
    "  have hpcE2 : VEnv.get E2 " + q + "q_pc" + q + " = some pc1 :=",
    "    venvGet_set_same ((" + q + "q_flags" + q + ", fl) :: V) " + q + "q_pc" + q + " pc1 pcv",
    "      (Eq.trans (venvGet_cons_ne V " + q + "q_flags" + q + " " + q + "q_pc" + q + " fl " +
        dne("q_flags", "q_pc") + ") hget_pc)",
    "  have hflE2 : VEnv.get E2 " + q + "q_flags" + q + " = some fl :=",
    "    venvGet_set_ne ((" + q + "q_flags" + q + ", fl) :: V) " + q + "q_pc" + q + " " + q + "q_flags" + q +
        " pc1 fl " + dne("q_pc", "q_flags") + " (venvGet_cons_eq V " + q + "q_flags" + q + " fl)",
    "  have hpcE3 : VEnv.get E3 " + q + "q_pc" + q + " = some pc1 :=",
    "    Eq.trans (venvGet_cons_ne E2 " + q + "q_cond_ptr" + q + " " + q + "q_pc" + q +
        " (BitVec.ofNat 256 0) " + dne("q_cond_ptr", "q_pc") + ") hpcE2",
    "  have hflE3 : VEnv.get E3 " + q + "q_flags" + q + " = some fl :=",
    "    Eq.trans (venvGet_cons_ne E2 " + q + "q_cond_ptr" + q + " " + q + "q_flags" + q +
        " (BitVec.ofNat 256 0) " + dne("q_cond_ptr", "q_flags") + ") hflE2",
    "  have hpcE4 : VEnv.get E4 " + q + "q_pc" + q + " = some pcA :=",
    "    " + c3get("pcA", "q_pc", "(BitVec.ofNat 256 0)", "pcA",
    "      venvGet_set_same V " + q + "q_pc" + q + " pcA pcv hget_pc"),
    "  have hpcE5 : VEnv.get E5 " + q + "q_pc" + q + " = some pcA :=",
    "    Eq.trans (venvGet_cons_ne E4 " + q + "q_acc" + q + " " + q + "q_pc" + q +
        " (BitVec.ofNat 256 0) " + dne("q_acc", "q_pc") + ") hpcE4",
    "  have hflE5 : VEnv.get E5 " + q + "q_flags" + q + " = some fl :=",
    "    Eq.trans (venvGet_cons_ne E4 " + q + "q_acc" + q + " " + q + "q_flags" + q +
        " (BitVec.ofNat 256 0) " + dne("q_acc", "q_flags") + ") hflE2",
    "  have hcmE5 : VEnv.get E5 " + q + "q_const_mptr" + q + " = some cm :=",
    "    " + c3get("pcA", "q_const_mptr", "(BitVec.ofNat 256 0)", "cm",
    "      venvGet_set_ne V " + q + "q_pc" + q + " " + q + "q_const_mptr" + q + " pcA cm " +
        dne("q_pc", "q_const_mptr") + " hget_cm"),
    "  have hpcE6 : VEnv.get E6 " + q + "q_pc" + q + " = some pcC :=",
    "    " + c3get("pcC", "q_pc", "accv", "pcC",
    "      venvGet_set_same V " + q + "q_pc" + q + " pcC pcv hget_pc"),
    "  have hcmE6 : VEnv.get E6 " + q + "q_const_mptr" + q + " = some cm :=",
    "    " + c3get("pcC", "q_const_mptr", "accv", "cm",
    "      venvGet_set_ne V " + q + "q_pc" + q + " " + q + "q_const_mptr" + q + " pcC cm " +
        dne("q_pc", "q_const_mptr") + " hget_cm"),
    "  have hhtE6 : VEnv.get E6 " + q + "q_has_top" + q + " = some (BitVec.ofNat 256 0) :=",
    "    " + c3get("pcC", "q_has_top", "accv", "(BitVec.ofNat 256 0)",
    "      venvGet_set_ne V " + q + "q_pc" + q + " " + q + "q_has_top" + q + " pcC (BitVec.ofNat 256 0) " +
        dne("q_pc", "q_has_top") + " hget_ht"),
])

GUARD = nl.join([
    "  -- statement 2: the flag guard 'if q_flags > 3' takes its FALSE branch, by 'hflag'",
    P["COND_GT_HAVES"],
    "  have z_gt : " + P["COND_GT"] + " = (Bridge.Dialect c g).zero := by",
    "    have hnot : ¬ ((BitVec.ofNat 256 3).toNat < fl.toNat) := by",
    "      intro hh",
    "      have h3 : fl.toNat ≤ 3 := BitVec.le_def.mp hflag",
    "      have h2 : (3 : Nat) < fl.toNat := by simpa using hh",
    "      omega",
    "    rw [decide_eq_false hnot]; rfl",
    "  have s2 : Step (D := Bridge.Dialect c g) funs E2 st1",
    "      (.stmt (yif (yop EVM.Op.gt [yvar " + q + "q_flags" + q + ", ylit 3])",
    "          [yexpr (ycall " + q + "q_program_fail" + q + " [])])) (.sres E2 st1 .normal) :=",
    "    Step.ifFalse " + P["COND_GT_NAME"] + " z_gt",
    "  -- statement 3: 'let q_cond_ptr := 0', executed on every path",
    "  have s3 : Step (D := Bridge.Dialect c g) funs E2 st1",
    "      (.stmt (ylet " + q + "q_cond_ptr" + q + " (ylit 0))) (.sres E3 st1 .normal) :=",
    "    Step.letVal (D := Bridge.Dialect c g) (qlit funs E2 st1 0) rfl",
])

S4 = nl.join([
    "  -- statement 4: the optional COND field, a two-way split on flag bit 0",
    P["COND_AND0_HAVES"],
    "  have s4 : Step (D := Bridge.Dialect c g) funs E3 st1",
    "      (.stmt (yif " + P["YIF4C"] + " " + BODY4 + "))",
    "      (.sres E4 stA .normal) := by",
    "    cases b0",
    "    · exact Step.ifFalse " + P["COND_AND0_NAME"] + " hb0",
    "    · refine Step.ifTrue (D := Bridge.Dialect c g) " + P["COND_AND0_NAME"] + " ?_ ?_",
    "      · rw [hb0]; exact (by decide : (BitVec.ofNat 256 1 : U256) ≠ 0)",
    "      · " + ind(P["SEG_F"], 6).strip(),
    "        have hchain4 : Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) " + BODY4 + " :: funs) E3 st1 (.stmts " + BODY4 + ")",
    "            (.sres (" + F[1]["env"] + ") " + F[1]["state"] + " .normal) := by",
    "          refine Step.seqCons (D := Bridge.Dialect c g) (V1 := " + F[0]["env"] + ") (st1 := " +
        F[0]["state"] + ") " + F[0]["name"] + " ?_",
    "          exact Step.seqCons (D := Bridge.Dialect c g) (V1 := " + F[1]["env"] + ") (st1 := " +
        F[1]["state"] + ") " + F[1]["name"] + " (Step.seqNil (D := Bridge.Dialect c g))",
    "        have hnorm4 : restore E3 (" + F[1]["env"] + ") = E4 := by",
    "          rw [restore_same_len E3 (" + F[1]["env"] + ") (by rw [venvSet_length, venvSet_length]),",
    "              venvSet_cons_eq E2 " + q + "q_cond_ptr" + q + " (BitVec.ofNat 256 0) " + X4 + ",",
    "              venvSet_cons_ne E2 " + q + "q_cond_ptr" + q + " " + q + "q_pc" + q + " " + X4 + " " + Y4 + " " +
        dne("q_cond_ptr", "q_pc") + ",",
    "              venvSet_set_same ((\"q_flags\", fl) :: V) " + q + "q_pc" + q + " pc1 " + Y4 + ",",
    "              venvSet_cons_ne V " + q + "q_flags" + q + " " + q + "q_pc" + q + " fl " + Y4 + " " +
        dne("q_flags", "q_pc") + "]",
    "          exact rfl",
    "        rw [← hnorm4]",
    "        exact Step.block (D := Bridge.Dialect c g) (body := " + BODY4 + ") hchain4",
])

S5 = nl.join([
    "  -- statement 5: 'let q_acc := 0', executed on every path",
    "  have s5 : Step (D := Bridge.Dialect c g) funs E4 stA",
    "      (.stmt (ylet " + q + "q_acc" + q + " (ylit 0))) (.sres E5 stA .normal) :=",
    "    Step.letVal (D := Bridge.Dialect c g) (qlit funs E4 stA 0) rfl",
])

S6 = nl.join([
    "  -- statement 6: the optional CONST field, a two-way split on flag bit 1. The 'let qconst' the",
    "  -- branch binds is dropped by the branch's own 'Step.block', which is why the environment SHAPE",
    "  -- does not depend on the flags; the writes it makes to 'q_pc' and 'q_acc' survive.",
    P["COND_AND1_HAVES"],
    "  have s6 : Step (D := Bridge.Dialect c g) funs E5 stA",
    "      (.stmt (yif " + P["YIF6C"] + " " + BODY6 + "))",
    "      (.sres E6 stC .normal) := by",
    "    cases b1",
    "    · exact Step.ifFalse " + P["COND_AND1_NAME"] + " hb1",
    "    · refine Step.ifTrue (D := Bridge.Dialect c g) " + P["COND_AND1_NAME"] + " ?_ ?_",
    "      · rw [hb1]; exact (by decide : (BitVec.ofNat 256 2 : U256) ≠ 0)",
    "      · " + ind(P["SEG_G"], 6).strip(),
    "        have hchain6 : Step (D := Bridge.Dialect c g) (hoist (Bridge.Dialect c g) " + BODY6 + " :: funs) E5 stA (.stmts " + BODY6 + ")",
    "            (.sres (" + G[2]["env"] + ") " + G[2]["state"] + " .normal) := by",
    "          exact Step.seqCons (D := Bridge.Dialect c g) (V1 := " + G[0]["env"] + ") (st1 := " + G[0]["state"] + ") " + G[0]["name"] + " (",
    "            Step.seqCons (D := Bridge.Dialect c g) (V1 := " + G[1]["env"] + ") (st1 := " + G[1]["state"] + ") " + G[1]["name"] + " (",
    "              Step.seqCons (D := Bridge.Dialect c g) (V1 := " + G[2]["env"] + ") (st1 := " + G[2]["state"] + ") " + G[2]["name"] + " (Step.seqNil (D := Bridge.Dialect c g))))",
    "        have hnorm6 : restore E5 (" + G[2]["env"] + ") = E6 := by",
    "          rw [venvSet_cons_ne E5 " + q + "qconst" + q + " " + q + "q_pc" + q + " " + Q6 + " " + PCB6 + " " +
        dne("qconst", "q_pc") + ",",
    "            venvSet_cons_ne (VEnv.set E5 " + q + "q_pc" + q + " " + PCB6 + ") " + q + "qconst" + q + " " +
        q + "q_acc" + q + " " + Q6 + " " + ACC6 + " " + dne("qconst", "q_acc") + ",",
    "            restore_pw_cons_len E5 (VEnv.set (VEnv.set E5 " + q + "q_pc" + q + " " + PCB6 + ") " +
        q + "q_acc" + q + " " + ACC6 + ") " + q + "qconst" + q + " " + Q6 +
    "              (by rw [venvSet_length, venvSet_length]),",
    "            venvSet_cons_ne E4 " + q + "q_acc" + q + " " + q + "q_pc" + q + " (BitVec.ofNat 256 0) " +
        PCB6 + " " + dne("q_acc", "q_pc") + ",",
    "            venvSet_cons_eq (VEnv.set E4 " + q + "q_pc" + q + " " + PCB6 + ") " + q + "q_acc" + q +
        " (BitVec.ofNat 256 0) " + ACC6 + ",",
    "            venvSet_cons_ne ((\"q_flags\", fl) :: VEnv.set V \"q_pc\" pcA) \"q_cond_ptr\" \"q_pc\" cpv " +
        PCB6 + " " + dne("q_cond_ptr", "q_pc") + ",",
    "            venvSet_cons_ne (VEnv.set V \"q_pc\" pcA) \"q_flags\" \"q_pc\" fl " + PCB6 + " " +
        dne("q_flags", "q_pc") + ",",
    "            venvSet_set_same V \"q_pc\" pcA " + PCB6 + "]",
    "          exact rfl",
    "        rw [← hnorm6]",
    "        exact Step.block (D := Bridge.Dialect c g) (body := " + BODY6 + ") hchain6",
])

S14 = nl.join([
    "  -- statement 14: the spill guard 'if q_has_top' at the EMPTY stack, FALSE branch, exactly as in",
    "  -- every landed arm - 'Step.ifFalse' on the 'q_has_top' read, so nothing is touched.",
    P["LOOK_B"].split(nl)[0],
    "  have s14 : Step (D := Bridge.Dialect c g) funs " + E15ENV + " " + E15ST,
    "      (.stmt (yif " + P["YIF14C"] + " " + SPILL + "))",
    "      (.sres " + E15ENV + " " + E15ST + " .normal) :=",
    "    Step.ifFalse (Step.var (D := Bridge.Dialect c g) hhtE15) rfl",
])

# MOD7D fix 5 (NOT in MOD7C's list of four): segment A's 'have h1..h17' and segment B's
# 'have h1..h47' are BOTH emitted at the theorem's top level, and B comes last, so B's h10/h17
# SHADOW A's and the chain's first two links were handed segment B's derivations. Rename A's.
P["SEG_A"] = re.sub(r"\bh(\d+)\b", r"aH\1", P["SEG_A"])
for _a in A:
    _a["name"] = re.sub(r"\bh(\d+)\b", r"aH\1", _a["name"])

LINKS = [(A[0]["env"], A[0]["state"], A[0]["name"]),
         (A[1]["env"], A[1]["state"], A[1]["name"]),
         ("E2", "st1", "s2"),
         ("E3", "st1", "s3"),
         ("E4", "stA", "s4"),
         ("E5", "stA", "s5"),
         ("E6", "stC", "s6")] + [(b["env"], b["state"], b["name"]) for b in B] + \
        [(E15ENV, E15ST, "s14")]
CH = []
for i, (e, s, n) in enumerate(LINKS):
    if i + 1 < len(LINKS):
        CH.append("  refine Step.seqCons (D := Bridge.Dialect c g) (V1 := %s) (st1 := %s) %s ?_" % (e, s, n))
    else:
        CH.append("  exact Step.seqCons (D := Bridge.Dialect c g) (V1 := %s) (st1 := %s) %s (Step.seqNil (D := Bridge.Dialect c g))" % (e, s, n))
CHAIN = nl.join(CH)

TEMPLATE = open(os.path.join(HERE, "pro_template.txt")).read()
SUB = {"BYTE": BYTE, "ABB": ABB, "ENVDEF": ENVDEF, "GETS": GETS, "BODY": BODY,
       "PRELETS": PRELETS, "BASEGETS": BASEGETS, "SEGA": P["SEG_A"], "GUARD": GUARD,
       "COND4": "", "S4": S4, "S5": S5, "COND6": "", "S6": S6, "SEGB": P["SEG_B"],
       "S14": S15 if False else S14, "CHAIN": CHAIN}
T = TEMPLATE
for _pass in range(3):
    for k, v in SUB.items():
        T = T.replace("@@" + k + "@@", v)
left = sorted(set(re.findall(r"@@[A-Za-z0-9_]+@@", T)))
assert not left, left
# MOD7D fix 3c: pin the byte-mask literal. With the env ascribed the expected type is
# '(Bridge.Dialect c g).Value', which type-class search will not unfold to 'BitVec 256', so
# 'x &&& 0xff' leaves 'failed to synthesize HAnd (BitVec 256) Nat (Bridge.Dialect c g).Value'.
# '(0xff : U256)' elaborates to the same term and removes the search.
T = T.replace("&&& 0xff", "&&& (0xff : U256)")
open(os.path.join(HERE, "pro_lean.txt"), "w").write(T)
print("pro_lean.txt chars", len(T), "lines", len(T.split(nl)))

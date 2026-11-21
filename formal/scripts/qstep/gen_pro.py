"""MOD7C - the MODARITH7 PROLOGUE (emitted statements 0-14) and EPILOGUE (20-22).

Built on 'gs3.Gen', the preserved Step-derivation generator. The prologue is NOT straight-line code:
it contains the flag guard 'if q_flags > 3' (FALSE branch), two OPTIONAL branches gated on the flag
bits, and the spill guard 'if q_has_top' (FALSE branch). The generator derives every straight-line
statement and every guard CONDITION mechanically, so this script runs it over the two straight-line
SEGMENTS (0-1 and 7-13) and over the three guard expressions; the four 'yif' links are assembled
around those derivations in 'asm_pro.py'.

The additive extension this card made to gs3.py is the 'gt' builtin (the flag guard), which the
prologue needs and none of the five block bodies did.

Run:  python3 formal/scripts/qstep/gen_pro.py   (writes pro_parts.py next to it)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gs3 import *  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "pro_parts.py")

# ------------------------------------------------- the prologue's intermediate values (closed spellings)
W0 = "(loadWord st.memory pcv.toNat)"
FL = "((%s >>> 248) &&& 0xff)" % W0
ST1 = "(touchMemory st pcv.toNat 32)"
PC1 = "(pcv + BitVec.ofNat 256 1)"
E1 = '(("q_flags", %s) :: V)' % FL
E2 = "(VEnv.set %s \"q_pc\" %s)" % (E1, PC1)
E3 = '("q_cond_ptr", (BitVec.ofNat 256 0)) :: %s' % E2

W1 = "(loadWord (%s).memory (%s).toNat)" % (ST1, PC1)
ST2 = "(touchMemory %s (%s).toNat 32)" % (ST1, PC1)
CPV = "(if b0 then (%s >>> 240) else BitVec.ofNat 256 0)" % W1
PCA = "(if b0 then (%s + BitVec.ofNat 256 2) else %s)" % (PC1, PC1)
STA = "(if b0 then %s else %s)" % (ST2, ST1)
E4 = '("q_cond_ptr", %s) :: (("q_flags", %s) :: VEnv.set V "q_pc" %s)' % (CPV, FL, PCA)
E5 = '("q_acc", (BitVec.ofNat 256 0)) :: %s' % E4

W2 = "(loadWord (%s).memory (%s).toNat)" % (STA, PCA)
ST3 = "(touchMemory %s (%s).toNat 32)" % (STA, PCA)
QCV = "((%s >>> 248) &&& 0xff)" % W2
PCB = "(%s + BitVec.ofNat 256 1)" % PCA
CPTR = "(cm + (%s <<< 5))" % QCV
ACCSEED = "(loadWord (%s).memory (%s).toNat)" % (ST3, CPTR)
ST4 = "(touchMemory %s (%s).toNat 32)" % (ST3, CPTR)
ACCV = "(if b1 then %s else BitVec.ofNat 256 0)" % ACCSEED
PCC = "(if b1 then %s else %s)" % (PCB, PCA)
STC = "(if b1 then %s else %s)" % (ST4, STA)
E6 = ('("q_acc", %s) :: (("q_cond_ptr", %s) :: (("q_flags", %s) :: VEnv.set V "q_pc" %s))'
      % (ACCV, CPV, FL, PCC))

CW = "(loadWord (%s).memory (%s).toNat)" % (STC, PCC)
ST5 = "(touchMemory %s (%s).toNat 32)" % (STC, PCC)
CNT = ["((%s >>> %d) &&& 0xff)" % (CW, 248 - 8 * k) for k in range(5)]
PCF = "(%s + BitVec.ofNat 256 5)" % PCC
E15 = ("VEnv.set ((\"q_product_count\", %s) :: (\"q_mem_count\", %s) :: (\"q_pairwise_count\", %s) :: (\"q_row_count\", %s) :: (\"q_lin_count\", %s) :: (\"q_counts_word\", %s) :: (\"q_acc\", %s) :: (\"q_cond_ptr\", %s) :: (\"q_flags\", %s) :: VEnv.set V \"q_pc\" %s) \"q_pc\" %s"
    % (CNT[4], CNT[3], CNT[2], CNT[1], CNT[0], CW, ACCV, CPV, FL, PCC, PCF))

# ------------------------------------------------- segment A: emitted statements 0 and 1
BASE_GETS_A = {
    "q_pc": ("pcv", "hget_pc"),
    "q_has_top": ("BitVec.ofNat 256 0", "hget_ht"),
    "q_const_mptr": ("cm", "hget_cm"),
    "r": ("frModulusWord", "hget_r"),
}
SEGA = [
    ("let", "q_flags", OP("byte", [L(0), OP("mload", [V("q_pc")])])),
    ("set", "q_pc", OP("add", [V("q_pc"), L(1)])),
]
gA = Gen("funs", "V", BASE_GETS_A, "st", "st.memory")
txtA, layersA, stA_end = gA.stmts(SEGA)
havA = "\n".join(gA.lines)
stepsA = list(gA.steps)

# ------------------------------------------------- segment B: emitted statements 7 to 13
SEGB = [
    ("let", "q_counts_word", OP("mload", [V("q_pc")])),
    ("let", "q_lin_count", OP("byte", [L(0), V("q_counts_word")])),
    ("let", "q_row_count", OP("byte", [L(1), V("q_counts_word")])),
    ("let", "q_pairwise_count", OP("byte", [L(2), V("q_counts_word")])),
    ("let", "q_mem_count", OP("byte", [L(3), V("q_counts_word")])),
    ("let", "q_product_count", OP("byte", [L(4), V("q_counts_word")])),
    ("set", "q_pc", OP("add", [V("q_pc"), L(5)])),
]
BASE_GETS_B = {
    "q_pc": ("pcC", "hpcE6"),
    "q_const_mptr": ("cm", "hcmE6"),
    "r": ("frModulusWord", "hrE6"),
    "q_has_top": ("BitVec.ofNat 256 0", "hhtE6"),
    "q_top": ("topv", "htopE6"),
    "q_acc": ("accv", "haccE6"),
    "q_flags": ("fl", "hflE6"),
    "q_cond_ptr": ("cpv", "hcpE6"),
}
gB = Gen("funs", "E6", BASE_GETS_B, "stC", "stC.memory")
txtB, layersB, stB_end = gB.stmts(SEGB)
havB = "\n".join(gB.lines)
stepsB = list(gB.steps)

# ------------------------------------------------- the three guard conditions
gC = Gen("funs", "E2", {"q_flags": ("fl", "hflE2"), "q_pc": ("pc1", "hpcE2")}, "st1", "st1.memory")
v_gt, st_gt, n_gt = gC.ev(OP("gt", [V("q_flags"), L(3)]), [], "st1")
gD = Gen("funs", "E3", {"q_flags": ("fl", "hflE3"), "q_pc": ("pc1", "hpcE3")}, "st1", "st1.memory")
v_and0, st_and0, n_and0 = gD.ev(OP("and", [V("q_flags"), L(1)]), [], "st1")
gE = Gen("funs", "E5", {"q_flags": ("fl", "hflE5"), "q_pc": ("pcA", "hpcE5")}, "stA", "stA.memory")
v_and1, st_and1, n_and1 = gE.ev(OP("and", [V("q_flags"), L(2)]), [], "stA")

def emitted_statements():
    "the 23 top-level statements of 'GenAst.qArmBodyModarith7', verbatim from the source file"
    src = os.path.join(HERE, "..", "..", "Midfall", "Lowering", "GenAstQvm.lean")
    lines = open(src, encoding="utf-8").read().split(chr(10))
    d = [i for i, l in enumerate(lines) if l.startswith("def qArmBodyModarith7")][0]
    line = [l for l in lines[d:] if l.startswith("  [")][0]
    depth, items, cur = 0, [], ""
    i = line.index("[")
    while i < len(line):
        ch = line[i]
        if ch in "[(":
            depth += 1
            if depth == 1:
                i += 1
                continue
        elif ch in "])":
            depth -= 1
            if depth == 0:
                if cur.strip():
                    items.append(cur.strip())
                cur = ""
                i += 1
                continue
        if depth == 1 and ch == ",":
            items.append(cur.strip())
            cur = ""
        else:
            cur += ch
        i += 1
    assert len(items) == 23, len(items)
    return items

ITEMS = emitted_statements()

def block(items):
    "a Lean 'Block' literal, one emitted statement per line, spelled exactly as the emitter spells it"
    return "[" + (","+chr(10)+" ").join(items) + "]"

BODY_PRO = block(ITEMS[:15])
BODY_MID = block(ITEMS[15:20])
BODY_EPI = block(ITEMS[20:23])


def top_args(item):
    "the arguments of a '(yif COND BODY)' / '(yset X E)' item, as separate verbatim strings"
    assert item.startswith("(") and item.endswith(")"), item[:20]
    s = item[1:-1]
    out, i = [], 0
    while i < len(s):
        if s[i].isspace():
            i += 1
            continue
        if s[i] in "[(":
            close = {"[": "]", "(": ")"}[s[i]]
            depth, j = 0, i
            while True:
                if s[j] in "[(":
                    depth += 1
                elif s[j] in "])":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            out.append(s[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < len(s) and not s[j].isspace():
                j += 1
            out.append(s[i:j])
            i = j
    return out

YIF4 = top_args(ITEMS[4])
YIF6 = top_args(ITEMS[6])
YIF14 = top_args(ITEMS[14])

BODY4S = top_args(ITEMS[4])[2]
BODY6S = top_args(ITEMS[6])[2]
HOIST4 = "(hoist (Bridge.Dialect c g) " + BODY4S + " :: funs)"
HOIST6 = "(hoist (Bridge.Dialect c g) " + BODY6S + " :: funs)"
# ------------------------------------------------- the two optional-branch bodies and the epilogue body
gF = Gen(HOIST4, "E3", {"q_pc": ("pc1", "hpcE3"), "q_flags": ("fl", "hflE3"),
                        "q_cond_ptr": ("BitVec.ofNat 256 0", "hcpE3a"),
                        "q_const_mptr": ("cm", "hcmE3"), "r": ("frModulusWord", "hrE3"),
                        "q_has_top": ("BitVec.ofNat 256 0", "hhtE3")},
         "st1", "st1.memory")
havF = None
txtF, layersF, stF_end = gF.stmts([
    ("set", "q_cond_ptr", OP("shr", [L(240), OP("mload", [V("q_pc")])])),
    ("set", "q_pc", OP("add", [V("q_pc"), L(2)])),
])
stepsF = list(gF.steps)
havF = "\n".join(gF.lines)

gG = Gen(HOIST6, "E5", {"q_pc": ("pcA", "hpcE5"), "q_flags": ("fl", "hflE5"),
                        "q_cond_ptr": ("cpv", "hcpE5"), "q_acc": ("BitVec.ofNat 256 0", "haccE5a"),
                        "q_const_mptr": ("cm", "hcmE5"), "r": ("frModulusWord", "hrE5"),
                        "q_has_top": ("BitVec.ofNat 256 0", "hhtE5")},
         "stA", "stA.memory")
havG = None
txtG, layersG, stG_end = gG.stmts([
    ("let", "qconst", OP("byte", [L(0), OP("mload", [V("q_pc")])])),
    ("set", "q_pc", OP("add", [V("q_pc"), L(1)])),
    ("set", "q_acc", OP("mload", [OP("add", [V("q_const_mptr"), OP("shl", [L(5), V("qconst")])])])),
])
stepsG = list(gG.steps)
havG = "\n".join(gG.lines)

# the epilogue gate: 'if q_flags &&& 1 then q_acc := mulmod (mload q_cond_ptr) q_acc r'
# 'V20'/'stP'/'accP'/'pcP' are the block-chain output names used by asm_run.py.
gH = Gen("funs", "V20", {"q_pc": ("pcP", "hpcV20"), "q_flags": ("flP", "hflV20"),
                         "q_cond_ptr": ("cpvP", "hcpV20"), "q_acc": ("accP", "haccV20"),
                         "q_const_mptr": ("cm", "hcmV20"), "r": ("frModulusWord", "hrV20"),
                         "q_has_top": ("BitVec.ofNat 256 0", "hhtV20"),
                         "q_top": ("topP", "htopV20")},
         "stP", "stP.memory")
v_and20, st_and20, n_and20 = gH.ev(OP("and", [V("q_flags"), L(1)]), [], "stP")
txtH, layersH, stH_end = gH.stmts([
    ("set", "q_acc", OP("mulmod", [OP("mload", [V("q_cond_ptr")]), V("q_acc"), V("r")])),
])
stepsH = list(gH.steps)

# ------------------------------------------------- the 'VEnv.get' chains the assembly needs
def lk(gen, layers, x, hyp, env=None):
    vv, prf = gen.lookup(layers, x)
    e = env if env is not None else "(" + render(layers, gen.base) + ")"
    return "  have %s : VEnv.get %s %s = some %s := (%s)" % (hyp, e, q(x), vv, prf)

LOOK_B = "\n".join([
    lk(gB, layersB, "q_has_top", "hhtE15"),
    lk(gB, layersB, "q_top", "htopE15"),
    lk(gB, layersB, "q_pc", "hpcE15"),
    lk(gB, layersB, "q_acc", "haccE15"),
    lk(gB, layersB, "q_const_mptr", "hcmE15"),
    lk(gB, layersB, "r", "hrE15"),
    lk(gB, layersB, "q_lin_count", "hlinE15"),
    lk(gB, layersB, "q_row_count", "hrowE15"),
    lk(gB, layersB, "q_pairwise_count", "hpwE15"),
    lk(gB, layersB, "q_mem_count", "hmemE15"),
    lk(gB, layersB, "q_product_count", "hprodE15"),
    lk(gB, layersB, "q_flags", "hflE15"),
    lk(gB, layersB, "q_cond_ptr", "hcpE15"),
])


# ------------------------------------------------- the emitted statement lists, read off the emitter

PARTS = dict(
    W0=W0, FL=FL, ST1=ST1, PC1=PC1, E1=E1, E2=E2, E3=E3, W1=W1, ST2=ST2, CPV=CPV, PCA=PCA,
    STA=STA, E4=E4, E5=E5, W2=W2, ST3=ST3, QCV=QCV, PCB=PCB, CPTR=CPTR, ACCSEED=ACCSEED,
    ST4=ST4, ACCV=ACCV, PCC=PCC, STC=STC, E6=E6, CW=CW, ST5=ST5, PCF=PCF, E15=E15,
    C0=CNT[0], C1=CNT[1], C2=CNT[2], C3=CNT[3], C4=CNT[4],
    SEG_A=havA, SEG_B=havB, SEG_F=havF, SEG_G=havG,
    COND_GT=v_gt, COND_GT_NAME=n_gt, COND_GT_ST=st_gt, COND_GT_HAVES="\n".join(gC.lines),
    COND_AND0=v_and0, COND_AND0_NAME=n_and0, COND_AND0_HAVES="\n".join(gD.lines),
    COND_AND1=v_and1, COND_AND1_NAME=n_and1, COND_AND1_HAVES="\n".join(gE.lines),
    COND_AND20=v_and20, COND_AND20_NAME=n_and20, COND_AND20_HAVES="\n".join(gH.lines),
    F_ENVS="\n".join("%d|%s|%s|%s" % (i, n, e, s) for i, (n, e, s) in enumerate(stepsF)),
    G_ENVS="\n".join("%d|%s|%s|%s" % (i, n, e, s) for i, (n, e, s) in enumerate(stepsG)),
    H_ENVS="\n".join("%d|%s|%s|%s" % (i, n, e, s) for i, (n, e, s) in enumerate(stepsH)),
    BODY_PRO=BODY_PRO, YIF4C=YIF4[1], YIF4B=YIF4[2],
    YIF6C=YIF6[1], YIF6B=YIF6[2], YIF14C=YIF14[1], YIF14B=YIF14[2], BODY_MID=BODY_MID, BODY_EPI=BODY_EPI,
    LOOK_B=LOOK_B,
    A_ENVS="\n".join("%d|%s|%s|%s" % (i, n, e, s) for i, (n, e, s) in enumerate(stepsA)),
    B_ENVS="\n".join("%d|%s|%s|%s" % (i, n, e, s) for i, (n, e, s) in enumerate(stepsB)),
)

if __name__ == "__main__":
    with open(OUT, "w") as f:
        f.write("PARTS = %r\n" % (PARTS,))
    print("wrote", OUT)
    print("segment A haves:", len(gA.lines), "segment B haves:", len(gB.lines))
    print("cond gt   =", v_gt)
    print("cond and0 =", v_and0)
    print("cond and1 =", v_and1[:120], "...")
    print("A steps:", [(n, len(e)) for (n, e, s) in stepsA])
    print("B steps:", [(n, len(e)) for (n, e, s) in stepsB])
    print("E15 length:", len(E15))

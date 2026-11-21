
import sys
sys.path.insert(0, '/private/tmp')
from gs3 import *

E = "((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m)"
FUNS = "(hoist (Bridge.Dialect c g) (mod7RowOuterBody tcq) :: hoist (Bridge.Dialect c g) (mod7Init ctr) :: funs)"
g = Gen(FUNS, E, {"q_pc": ("(pc m)", "hpcW"), "q_acc": ("(acc m)", "haccW"),
                  "q_const_mptr": ("cm", "hcmW"), "r": ("frModulusWord", "hrW")},
         "(stw m)", "(stw m).memory")
PRE = [
  ('let', 'q_lhs', OP('shr', [L(240), OP('mload', [V('q_pc')])])),
  ('set', 'q_pc', OP('add', [V('q_pc'), L(2)])),
  ('let', 'q_lhs_value', OP('mload', [V('q_lhs')])),
]
_, layers, _ = g.stmts(PRE)
GENH = "\n".join(g.lines)
W = render(layers, E)
LHS = layers[2].val; PC2 = layers[1].val; LV = layers[0].val; ST1 = g.steps[-1][2]
def lk(x, hyp):
    vv, prf = g.lookup(layers, x)
    return "  have %s : VEnv.get %s %s = some %s := (%s)" % (hyp, P(W), '"%s"' % x, vv, prf)
LOOKUPS = "\n".join([lk("q_pc","hpcW2"), lk("q_acc","haccW2"), lk("q_lhs_value","hlvW2"),
                     lk("q_const_mptr","hcmW2"), lk("r","hrW2")])
INNER = "mod7RowLimbFrom cm %s %s (acc m) %s" % (LV, PC2, ST1)
PCIT = "(fun k => ((%s k).1))" % INNER
ACCT = "(fun k => ((%s k).2.1))" % INNER
STWT = "(fun k => ((%s k).2.2))" % INNER
steps = g.steps
chain = []
for (nm, envAfter, stAfter) in steps:
    chain.append("(Step.seqCons (D := Bridge.Dialect c g) (V1 := %s) (st1 := %s) %s" % (P(envAfter), stAfter, nm))
chain.append("(Step.seqCons (D := Bridge.Dialect c g) (V1 := (mod7Env @@W@@ @@PCIT@@ @@ACCT@@ tcq.limbCount)) (st1 := (@@STWT@@ tcq.limbCount)) hinner (Step.seqNil (D := Bridge.Dialect c g)))")
chain.append(")))")
CHAIN = "\n        ".join(chain)
# ROW limb values for mod7RowLimb_iter
W2 = "(loadWord (stw m).memory (pc m).toNat)"
SLOT2 = "((%s >>> 248) &&& 0xff)" % W2
RHS2 = "((%s >>> 232) &&& 65535)" % W2
CPTR2 = "(cm + (%s <<< 5))" % SLOT2
VB = ('(VEnv.set (VEnv.set (("q_rhs", %s) :: ("qconst", %s) :: ("q_word", %s) :: %s) "q_pc" '
      '((pc m) + BitVec.ofNat 256 3)) "q_acc" (wAddmod (acc m) (wMulmod (wMulmod lv '
      '(loadWord (stw m).memory %s.toNat)) (loadWord (stw m).memory %s.toNat))))'
      % (RHS2, SLOT2, W2, E, RHS2, CPTR2))
STB = "(touchMemory (touchMemory (touchMemory (stw m) (pc m).toNat 32) %s.toNat 32) %s.toNat 32)" % (CPTR2, RHS2)
HACC = "wAddmod (acc m) (wMulmod (wMulmod lv (loadWord (stw m).memory %s.toNat)) (loadWord (stw m).memory %s.toNat))" % (RHS2, CPTR2)
open('/private/tmp/row_parts.py','w').write(
  "PARTS = %r\n" % ({'GENH': GENH, 'W': '(' + W + ')', 'LHS': LHS, 'PC2': PC2, 'LV': LV, 'ST1': ST1,
     'LOOKUPS': LOOKUPS, 'CHAIN': CHAIN, 'INNER': INNER, 'PCIT': PCIT, 'ACCT': ACCT, 'STWT': STWT,
     'W2': W2, 'SLOT2': SLOT2, 'RHS2': RHS2, 'VB': VB, 'STB': STB, 'HACC': HACC, 'E': E}))
print("parts ok")
print("CHAIN head:", CHAIN[:200])
print("LOOKUPS:", LOOKUPS[:300])

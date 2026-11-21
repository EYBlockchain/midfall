
import sys
sys.path.insert(0, '/private/tmp')
from gs3 import *

E = "((ctr, BitVec.ofNat 256 m) :: mod7Env V\u2080 pc acc m)"
FUNS = "(hoist (Bridge.Dialect c g) (mod7PwOuterBody7 tcq) :: hoist (Bridge.Dialect c g) (mod7Init ctr) :: funs)"
g = Gen(FUNS, E, {"q_pc": ("(pc m)", "hpcW"), "q_acc": ("(acc m)", "haccW"),
                  "q_const_mptr": ("cm", "hcmW"), "r": ("frModulusWord", "hrW")},
         "(stw m)", "(stw m).memory")
PRE = [
  ('let', 'q_pair_word', OP('mload', [V('q_pc')])),
  ('let', 'q_lhs_base', OP('shr', [L(240), V('q_pair_word')])),
  ('let', 'q_rhs_base', OP('and', [OP('shr', [L(224), V('q_pair_word')]), L(65535)])),
  ('set', 'q_pc', OP('add', [V('q_pc'), TL("tcq.byteU32Bytes")])),
  ('let', 'q_coeff_pc', V('q_pc')),
  ('set', 'q_pc', OP('add', [V('q_pc'), TL("tcq.limbPairwiseCoeffs")])),
]
_, layers, stend = g.stmts(PRE)
GENH = "\n".join(g.lines)
W = "(" + render(layers, E) + ")"
PW = layers[5].val; LB = layers[4].val; RB = layers[3].val; CP = layers[1].val
X1 = layers[2].val; X2 = layers[0].val
ST6 = stend
def lk(x, hyp):
    vv, prf = g.lookup(layers, x)
    return "  have %s : VEnv.get %s %s = some %s := (%s)" % (hyp, W, '"%s"' % x, vv, prf)
LOOKUPS = "\n".join([lk("q_acc","haccW2"), lk("q_lhs_base","hlbW2"), lk("q_rhs_base","hrbW2"),
                     lk("q_coeff_pc","hcpW2"), lk("q_const_mptr","hcmW2"), lk("r","hrW2")])
steps = g.steps
chain = []
for (nm, envAfter, stAfter) in steps:
    chain.append("(Step.seqCons (D := Bridge.Dialect c g) (V1 := %s) (st1 := %s) %s" % (P(envAfter), stAfter, nm))
chain.append('(Step.seqCons (D := Bridge.Dialect c g) (V1 := (VEnv.set @@W@@ "q_acc" (@@ACCIN@@ tcq.limbCount))) (st1 := (@@STWIN@@ tcq.limbCount)) hdloop (Step.seqNil (D := Bridge.Dialect c g)))')
chain.append("))))))")
CHAIN = "\n        ".join(chain)
# double-loop acc/stw at the W level
PF = "mod7PwPairFrom cm @@LB@@ @@RB@@ @@CP@@ (acc m) @@ST6@@ tcq.limbCount"
ACCIN = "(fun k => ((%s k).1))" % PF
STWIN = "(fun k => ((%s k).2))" % PF
WRAW = render(layers, E)
open('/private/tmp/pw_parts.py','w').write("PARTS = %r\n" % ({
  'GENH': GENH, 'W': W, 'PW': PW, 'LB': LB, 'RB': RB, 'CP': CP, 'X1': X1, 'X2': X2,
  'ST6': ST6, 'LOOKUPS': LOOKUPS, 'CHAIN': CHAIN, 'E': E, 'ACCIN': ACCIN, 'STWIN': STWIN,
  'PF': PF}))
print("ok"); print("X1:", X1); print("X2:", X2); print("CP:", CP[:120]); print("ST6:", ST6[:160])

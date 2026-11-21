
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
txt, layers, stend = g.stmts(PROD)
open('/private/tmp/prod_gen.txt','w').write(txt)
print("=== ENV AFTER ==="); print(render(layers, BASE))
print("=== ST AFTER ==="); print(stend)
print("=== NLINES ===", len(txt.split(chr(10))))

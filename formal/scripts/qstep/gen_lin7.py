
import sys
sys.path.insert(0, '/private/tmp')
from gs3 import *
base_gets = {
  "q_pc": ("pcv", "hpc"),
  "q_acc": ("accv", "hacc"),
  "q_const_mptr": ("cm", "hcm"),
  "r": ("frModulusWord", "hr"),
}
body = [
  ('let', 'q_word', OP('mload', [V('q_pc')])),
  ('let', 'qconst', OP('byte', [L(0), V('q_word')])),
  ('let', 'q_ptr', OP('and', [OP('shr', [L(232), V('q_word')]), L(65535)])),
  ('set', 'q_pc', OP('add', [V('q_pc'), L(3)])),
  ('set', 'q_acc', OP('addmod', [V('q_acc'),
      OP('mulmod', [OP('mload', [OP('add', [V('q_const_mptr'), OP('shl', [L(5), V('qconst')])])]),
                    OP('mload', [V('q_ptr')]), V('r')]), V('r')])),
]
g = Gen("funs", "V", base_gets, "st", "st.memory")
txt, layers, stend = g.stmts(body)
open('/private/tmp/lin7_gen.txt','w').write(txt)
print("ENV AFTER:", render(layers, "V"))
print("ST AFTER:", stend)
print("nlines:", len(txt.split(chr(10))))

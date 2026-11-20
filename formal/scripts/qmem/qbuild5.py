# -*- coding: utf-8 -*-
"""QTOKEN build: emit the two switch-gated token arms into a standalone file for checking."""
import sys
from qgen2 import Arm
from qarms5 import ARMS
from qbuild import HEADER, FOOTER

def build(which, out):
    arms = [Arm(ARMS[w]()) for w in which]
    for a in arms:
        a.run()
    used = set()
    for a in arms:
        used |= a.g.used
    from qsem import bi_src, bi_at_src
    parts = [HEADER]
    parts.append('-- the open-dialect built-in facts the derivations below use\n')
    for nm in sorted(used):
        if nm in ('qbi_mload_at', 'qbi_mstore_at'):
            parts.append(bi_at_src(nm))
        else:
            parts.append(bi_src(nm))
    parts.append('')
    for a in arms:
        parts.append(a.emit())
    parts.append(FOOTER)
    open(out, 'w').write((chr(10) + chr(10)).join(parts))
    return out

if __name__ == '__main__':
    print(build(sys.argv[1:] or sorted(ARMS), '/tmp/qt_arms.lean'))

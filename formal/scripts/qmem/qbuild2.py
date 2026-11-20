# -*- coding: utf-8 -*-
import sys
from qgen2 import Arm
from qarms2 import ARMS
from qsem import bi_src, bi_at_src, BI

HEADER = """import Midfall.LoweringV3.QuotientFrame

open YulSemantics YulSemantics.EVM Midfall Midfall.Generator Midfall.Lowering
open Midfall.Yul Midfall.Yul.Bridge Midfall.Lowering.QuotientInterp
open Midfall.Lowering.GenAst
open Midfall.Yul.WpX
open Midfall.LoweringV3.QuotientFrame

set_option autoImplicit false

namespace Midfall.LoweringV3.QuotientArms

"""

FOOTER = """
end Midfall.LoweringV3.QuotientArms
"""

def build(which, out):
    arms = [Arm(ARMS[w]()) for w in which]
    for a in arms:
        a.run()
    used = set()
    for a in arms:
        used |= a.g.used
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
    txt = (chr(10) + chr(10)).join(parts)
    open(out, 'w').write(txt)
    return out

if __name__ == '__main__':
    out = sys.argv[1]
    which = sys.argv[2:]
    print(build(which, out))

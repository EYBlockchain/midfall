# -*- coding: utf-8 -*-
"""QARMS2 build: emit the two fold arms into a standalone file for checking."""
from qgen2 import Arm
from qarms6 import ARMS
from qbuild import HEADER, FOOTER
from qsem import bi_src, bi_at_src


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


# The 'qbi_*' facts the fold arms need that are NOT already in 'QuotientArms.lean'.
MISSING = ['qbi_eq', 'qbi_iszero', 'qbi_lt', 'qbi_mstore_at', 'qbi_shr16', 'qbi_shr232']


def block(out='/tmp/qarms6_block.lean'):
    """The text to append to 'QuotientArms.lean': the missing built-in facts plus both fold triples."""
    parts = ['-- the open-dialect built-in facts the two FOLD arms add (the rest are already above)']
    for nm in MISSING:
        parts.append(bi_at_src(nm) if nm in ('qbi_mload_at', 'qbi_mstore_at') else bi_src(nm))
    for w in ['foldMain', 'foldSelector']:
        parts.append(Arm(ARMS[w]()).emit())
    open(out, 'w').write((chr(10) + chr(10)).join(parts))
    return out


if __name__ == '__main__':
    import sys
    if sys.argv[1:2] == ['--block']:
        print(block())
    else:
        print(build(sys.argv[1:] or sorted(ARMS), '/tmp/qf6.lean'))

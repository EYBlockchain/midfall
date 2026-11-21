# -*- coding: utf-8 -*-
"""QARMS2 - the 31-arm reachability table.

Enumerates the arm list from the three emitted arm tables ('qvmOpcodeArms' 26 + 'qvmNativeArms' 3 +
'qvmFoldArms' 2 = 31, Midfall/Lowering/GenAstQvm.lean:325-374) and, for each, whether a
'qStepValue_X' reference equation exists in 'QuotientFrame' section B and whether a full arm triple
('qArmRun_X' / 'qArmValue_X' / 'qArmValueAll_X') was landed at this card's base.

The lists are read FROM THE TREE, not typed in, and the asserts fail loudly if either file drifts.
"""
import re
import subprocess

OP = ['pushConst', 'pushMemLiteral', 'pushMemToken', 'pushMemTokenOffset', 'pushMemU16', 'add', 'mul',
      'neg', 'pow5', 'pushConstU8', 'addConstU8', 'mulConstU8', 'addConst', 'mulConst', 'addMemU16',
      'mulMemU16', 'addMulMemMemConstU8', 'addMulConstU8MemU16', 'addMulMemMem',
      'runAddMulMemMemConstU8', 'runAddMulConstU8MemU16', 'affineSum', 'lin7', 'bilin7Row',
      'bilin7Pairwise', 'modarith7']
NAT = ['nativePermutation', 'nativeLookup', 'nativeIdentity']
FOLD = ['foldMain', 'foldSelector']

# reference value present INSIDE 'evalQuotientIdentityStep' but with no named 'qStepValue_X' lemma
# (VmReference.lean:813-848): a 'foldRangeIdxM' over 'affineProductTerm' / 'affineLinearTerm'.
RUN_REF = set(['runAddMulMemMemConstU8', 'runAddMulConstU8MemU16', 'affineSum'])
# arms the reference REFUSES: '.error (streamOpcodeInIdentity op idx)', VmReference.lean:861-865
NO_REF = set(['foldMain', 'foldSelector', 'nativePermutation', 'nativeLookup', 'nativeIdentity'])
# arms whose emitted body contains a 'yfor', so 'qgen2' cannot drive them at all
LOOP = set(['lin7', 'bilin7Row', 'bilin7Pairwise', 'modarith7', 'runAddMulMemMemConstU8',
            'runAddMulConstU8MemU16', 'affineSum'])


def frame_facts():
    src = subprocess.run(['git', 'show', 'HEAD:formal/Midfall/LoweringV3/QuotientFrame.lean'],
                         capture_output=True, text=True, cwd='../..').stdout
    qs = set(re.findall(r'theorem qStepValue_([A-Za-z0-9]+) ', src))
    arms = ''
    for f in ('QuotientFrame.lean', 'QuotientArms.lean'):
        arms += subprocess.run(['git', 'show', 'HEAD:formal/Midfall/LoweringV3/' + f],
                               capture_output=True, text=True, cwd='../..').stdout
    trip = set(re.findall(r'theorem qArmValue_([A-Za-z0-9]+) ', arms))
    return qs, trip


def build():
    qs, trip = frame_facts()
    rows = []
    for fam, lst in (('opcode', OP), ('native', NAT), ('fold', FOLD)):
        for a in lst:
            ref = 'yes' if a in qs else ('in-step' if a in RUN_REF else 'NONE')
            rows.append((a, fam, ref, 'landed' if a in trip else 'open',
                         'loop' if a in LOOP else 'straight'))
    assert len(rows) == 31, len(rows)
    assert len(qs) == 23, sorted(qs)
    assert len(trip) == 20, sorted(trip)
    return rows


def table():
    rows = build()
    hdr = '%-26s %-8s %-9s %-8s %s' % ('ARM', 'FAMILY', 'REF', 'TRIPLE', 'EMITTED')
    out = [hdr, '-' * len(hdr)]
    for r in rows:
        out.append('%-26s %-8s %-9s %-8s %s' % r)
    out.append('-' * len(hdr))
    out.append('31 arms | ref: %d qStepValue_X + %d in-step + %d NONE | triples landed: %d' %
               (sum(1 for r in rows if r[2] == 'yes'), sum(1 for r in rows if r[2] == 'in-step'),
                sum(1 for r in rows if r[2] == 'NONE'),
                sum(1 for r in rows if r[3] == 'landed')))
    return chr(10).join(out)


if __name__ == '__main__':
    print(table())

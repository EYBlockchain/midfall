# -*- coding: utf-8 -*-
"""QTOKEN - the two PUSH_MEM_TOKEN arms. The first arms in the file whose emitted body contains a
'Stmt.switch': the case list is a nine-way append of 'if program.memUsage.X then [(label, body)]
else []', so the arm needs (i) the flag of the entry it takes, (ii) the scrutinee pinned to that
entry's 'tcq.mem.X' label so 'decide' can fire, and (iii) 'restore_set' to get the block's
post-environment back into 'VEnv.set' form. All three are in 'QuotientFrame' now."""
import sys
from qgen2 import Arm, P
from qparse import sv
from qsem import op_info

FR = 'frModulusWord'
DEC = 'loadWord st.memory pc.toNat'

def Vshr(k, v):
    return op_info('shr', [('lit', str(k))])[1](sv(k), v)[0]
def Vbyte(i, v):
    return op_info('byte', [('lit', str(i))])[1](sv(i), v)[0]
def Vadd(x, y):
    return op_info('add', [])[1](x, y)[0]
def Vand(x, y):
    return op_info('and', [])[1](x, y)[0]
def Vload(mem, p):
    return 'loadWord ' + P(mem) + ' ' + P(p) + '.toNat'

byte0 = Vbyte(0, DEC)
shr216 = Vshr(216, DEC)
OFF = Vand(shr216, sv(4294967295))
PTR = 'BitVec.ofNat 256 p'
BO = 'BitVec.ofNat 256 ow'
PADDR = Vload('st.memory', PTR)
OPADDR = Vload('st.memory', Vadd(PTR, BO))
L0 = 'BitVec.ofNat 256 p'
LAB = 'BitVec.ofNat 256 tcq.mem.l0'

def S(name, body, binders, varargs, pins, reads, guards=None, extras=None,
      switch_entry=0, switch_flag='hl0'):
    d = dict(name=name, body=body, binders=binders, varargs=varargs, pins=pins, reads=reads,
             switch_entry=switch_entry, switch_flag=switch_flag)
    if guards: d['guards'] = guards
    if extras: d['extras'] = extras
    return d

PINS = [('q_pc', 'pc', 'hget_pc'), ('q_sp', 'sp', 'hget_sp'), ('q_has_top', '0', 'hget_ht'),
        ('q_top', 'x', 'hget_top'), ('L_0_MPTR', L0, 'hget_l0')]
FLAG = [('(hl0 : program.memUsage.l0 = true)', 'program.memUsage.l0 = true', 'hl0')]

ARMS = {}

ARMS['pushMemToken'] = lambda: S(
    'pushMemToken', 'qArmBodyPushMemToken', '(pc sp x : U256) (p v : Nat)', 'pc sp x p v ',
    PINS, [(byte0, 'hbyte', LAB), (PADDR, 'hload', 'BitVec.ofNat 256 v')],
    guards={4: 'rfl'}, extras=FLAG)

ARMS['pushMemTokenOffset'] = lambda: S(
    'pushMemTokenOffset', 'qArmBodyPushMemTokenOffset',
    '(pc sp x : U256) (ow p v : Nat)', 'pc sp x ow p v ',
    PINS, [(byte0, 'hbyte', LAB), (OFF, 'hoff', BO), (OPADDR, 'hload', 'BitVec.ofNat 256 v')],
    guards={6: 'rfl'}, extras=FLAG)

if __name__ == '__main__':
    which = sys.argv[1:] or sorted(ARMS)
    for w in which:
        a = Arm(ARMS[w]())
        print(a.emit())
        print()
        for l in a.lemmas():
            print(l)

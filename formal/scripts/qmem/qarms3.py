# -*- coding: utf-8 -*-
import sys
from qgen2 import Arm, P
from qparse import sv
from qsem import op_info

FR = 'frModulusWord'
CM = 'program.guards.constMax'
DEC = 'loadWord st.memory pc.toNat'

def Vshr(k, v):
    return op_info('shr', [('lit', str(k))])[1](sv(k), v)[0]
def Vbyte(i, v):
    return op_info('byte', [('lit', str(i))])[1](sv(i), v)[0]
def Vadd(x, y):
    return op_info('add', [])[1](x, y)[0]
def Vshl(k, v):
    return op_info('shl', [('lit', str(k))])[1](sv(k), v)[0]
def Vand(x, y):
    return op_info('and', [])[1](x, y)[0]
def Vload(mem, p):
    return 'loadWord ' + P(mem) + ' ' + P(p) + '.toNat'

shr240 = Vshr(240, DEC)
shr224 = Vshr(224, DEC)
byte0 = Vbyte(0, DEC)
byte2 = Vbyte(2, DEC)
byte4 = Vbyte(4, DEC)
rhs224 = Vand(shr224, sv(65535))
PTR = 'BitVec.ofNat 256 p'
BP = 'BitVec.ofNat 256 b'
BL = 'BitVec.ofNat 256 l'
BR = 'BitVec.ofNat 256 r'
CONSTREAD = Vload('st.memory', Vadd('cb', Vshl(5, BP)))
PADDR = Vload('st.memory', PTR)
LREAD = Vload('st.memory', BL)
RREAD = Vload('st.memory', BR)

def S(name, body, binders, varargs, pins, reads, emit_top=None, ref_top=None, tie=None,
      guards=None, extras=None, tie_lemma=None):
    d = dict(name=name, body=body, binders=binders, varargs=varargs, pins=pins, reads=reads)
    if emit_top: d['emit_top'] = emit_top; d['ref_top'] = ref_top
    if tie: d['tie'] = tie
    if guards: d['guards'] = guards
    if extras: d['extras'] = extras
    if tie_lemma: d['tie_lemma'] = tie_lemma
    return d

ARMS = {}

def memU16(nm, body, w):
    return S(nm, body, '(pc x v : U256) (p : Nat)', 'pc x v p ',
        [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r')],
        [(shr240, 'hptr', PTR), (PADDR, 'hload', 'v')],
        emit_top='w' + w + 'mod x v',
        ref_top='BitVec.ofNat 256 (qvmFr' + w[3:] + ' x.toNat v.toNat)',
        tie=['w' + w + 'mod_eq_qvmFr' + w[3:]])

ARMS['addMemU16'] = lambda: memU16('addMemU16', 'qArmBodyAddMemU16', 'wAdd')
ARMS['mulMemU16'] = lambda: memU16('mulMemU16', 'qArmBodyMulMemU16', 'wMul')

def constArm(nm, body, w):
    return S(nm, body, '(pc cb x v : U256) (b : Nat)', 'pc cb x v b ',
        [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r'),
         ('q_const_mptr', 'cb', 'hget_cb')],
        [(shr240, 'hdec', BP), (CONSTREAD, 'hconst', 'v')],
        guards={2: 'by rw [decide_eq_false (by omega : \u00ac ((BitVec.ofNat 256 '
                    + CM + ').toNat < (' + BP + ').toNat))]; rfl'},
        extras=[('(hguard : ' + BP + '.toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat)',
                 BP + '.toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat', 'hguard')],
        emit_top='w' + w + 'mod x v',
        ref_top='BitVec.ofNat 256 (qvmFr' + w[3:] + ' x.toNat v.toNat)',
        tie=['w' + w + 'mod_eq_qvmFr' + w[3:]])

ARMS['addConst'] = lambda: constArm('addConst', 'qArmBodyAddConst', 'wAdd')
ARMS['mulConst'] = lambda: constArm('mulConst', 'qArmBodyMulConst', 'wMul')

ARMS['addMulMemMem'] = lambda: S(
    'addMulMemMem', 'qArmBodyAddMulMemMem', '(pc x lv rv : U256) (l r : Nat)', 'pc x lv rv l r ',
    [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r')],
    [(shr240, 'hl', BL), (rhs224, 'hr', BR), (LREAD, 'hlv', 'lv'), (RREAD, 'hrv', 'rv')],
    emit_top='wAddmod x (wMulmod lv rv)',
    ref_top='BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul lv.toNat rv.toNat))',
    tie=['wAddmod_wMulmod_eq_qvmFr_addMulMemMem'],
    tie_lemma=('wAddmod_wMulmod_eq_qvmFr_addMulMemMem', '(x lv rv : U256)',
               'wAddmod x (wMulmod lv rv) = BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul lv.toNat rv.toNat))',
               'rw [wAddmod_eq_qvmFrAdd, wMulmod_toNat]'))

ARMS['addMulConstU8MemU16'] = lambda: S(
    'addMulConstU8MemU16', 'qArmBodyAddMulConstU8MemU16',
    '(pc cb x pv cv : U256) (p b : Nat)', 'pc cb x pv cv p b ',
    [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r'),
     ('q_const_mptr', 'cb', 'hget_cb')],
    [(shr240, 'hp', PTR), (byte2, 'hb', BP), (PADDR, 'hpv', 'pv'), (CONSTREAD, 'hcv', 'cv')],
    emit_top='wAddmod x (wMulmod pv cv)',
    ref_top='BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul pv.toNat cv.toNat))',
    tie=['wAddmod_wMulmod_eq_qvmFr_addMulConstU8MemU16'],
    tie_lemma=('wAddmod_wMulmod_eq_qvmFr_addMulConstU8MemU16', '(x pv cv : U256)',
               'wAddmod x (wMulmod pv cv) = BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul pv.toNat cv.toNat))',
               'rw [wAddmod_eq_qvmFrAdd, wMulmod_toNat]'))

ARMS['addMulMemMemConstU8'] = lambda: S(
    'addMulMemMemConstU8', 'qArmBodyAddMulMemMemConstU8',
    '(pc cb x lv rv cv : U256) (l r b : Nat)', 'pc cb x lv rv cv l r b ',
    [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r'),
     ('q_const_mptr', 'cb', 'hget_cb')],
    [(shr240, 'hl', BL), (rhs224, 'hr', BR), (byte4, 'hb', BP),
     (LREAD, 'hlv', 'lv'), (RREAD, 'hrv', 'rv'), (CONSTREAD, 'hcv', 'cv')],
    emit_top='wAddmod x (wMulmod (wMulmod lv rv) cv)',
    ref_top='BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul (qvmFrMul lv.toNat rv.toNat) cv.toNat))',
    tie=['wAddmod_wMulmod2_eq_qvmFr_addMulMemMemConstU8'],
    tie_lemma=('wAddmod_wMulmod2_eq_qvmFr_addMulMemMemConstU8', '(x lv rv cv : U256)',
               'wAddmod x (wMulmod (wMulmod lv rv) cv) = '
               'BitVec.ofNat 256 (qvmFrAdd x.toNat (qvmFrMul (qvmFrMul lv.toNat rv.toNat) cv.toNat))',
               'rw [wAddmod_eq_qvmFrAdd, wMulmod_toNat, wMulmod_toNat]'))

HT = [('q_sp', 'sp', 'hget_sp'), ('q_has_top', '0', 'hget_ht')]

ARMS['pushMemU16'] = lambda: S(
    'pushMemU16', 'qArmBodyPushMemU16', '(pc sp x v : U256) (p : Nat)', 'pc sp x v p ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top')],
    [(shr240, 'hptr', PTR), (PADDR, 'hload', 'BitVec.ofNat 256 v')],
    guards={2: 'rfl'})

ARMS['pushMemLiteral'] = lambda: S(
    'pushMemLiteral', 'qArmBodyPushMemLiteral', '(pc sp x v : U256) (p : Nat)', 'pc sp x v p ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top')],
    [(shr224, 'hptr', PTR), (PADDR, 'hload', 'BitVec.ofNat 256 v')],
    guards={2: 'rfl'})

ARMS['pushConstU8'] = lambda: S(
    'pushConstU8', 'qArmBodyPushConstU8', '(pc cb sp x v : U256) (b : Nat)', 'pc cb sp x v b ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top'), ('q_const_mptr', 'cb', 'hget_cb')],
    [(byte0, 'hdec', BP), (CONSTREAD, 'hconst', 'BitVec.ofNat 256 v')],
    guards={1: 'rfl'})

ARMS['pushConst'] = lambda: S(
    'pushConst', 'qArmBodyPushConst', '(pc cb sp x v : U256) (b : Nat)', 'pc cb sp x v b ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top'), ('q_const_mptr', 'cb', 'hget_cb')],
    [(shr240, 'hdec', BP), (CONSTREAD, 'hconst', 'BitVec.ofNat 256 v')],
    guards={1: 'by rw [decide_eq_false (by omega : \u00ac ((BitVec.ofNat 256 '
               + CM + ').toNat < (' + BP + ').toNat))]; rfl', 2: 'rfl'},
    extras=[('(hguard : ' + BP + '.toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat)',
             BP + '.toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat', 'hguard')])

if __name__ == '__main__':
    which = sys.argv[1:] or sorted(ARMS)
    for w in which:
        a = Arm(ARMS[w]())
        print(a.emit())
        print()
        for l in a.lemmas():
            print(l)

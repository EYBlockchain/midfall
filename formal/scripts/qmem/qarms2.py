# -*- coding: utf-8 -*-
import sys
from qgen2 import Arm
from qparse import sv

FR = 'frModulusWord'
CM = 'program.guards.constMax'
DEC = 'loadWord st.memory pc.toNat'

def shr(k):
    return '(' + DEC + ' >>> ' + str(k) + ')'

def bytek(k):
    return '(' + DEC + ' >>> ' + str(248 - 8 * k) + ') &&& 0xff'

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

def memU16(nm, body, add):
    w = 'Add' if add else 'Mul'
    return S(nm, body, '(pc x v : U256) (p : Nat)', 'pc x v p ',
        [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r')],
        [(shr(240), 'hptr', 'BitVec.ofNat 256 p'),
         ('loadWord st.memory (BitVec.ofNat 256 p).toNat', 'hload', 'v')],
        emit_top='w' + w.lower() + 'mod x v',
        ref_top='BitVec.ofNat 256 (qvmFr' + w + ' x.toNat v.toNat)',
        tie=['w' + w.lower() + 'mod_eq_qvmFr' + w])

ARMS['addMemU16'] = lambda: memU16('addMemU16', 'qArmBodyAddMemU16', True)
ARMS['mulMemU16'] = lambda: memU16('mulMemU16', 'qArmBodyMulMemU16', False)

def constArm(nm, body, add):
    w = 'Add' if add else 'Mul'
    return S(nm, body, '(pc cb x v : U256) (b : Nat)', 'pc cb x v b ',
        [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r'),
         ('q_const_mptr', 'cb', 'hget_cb')],
        [(shr(240), 'hdec', 'BitVec.ofNat 256 b'),
         ('loadWord st.memory (cb + (BitVec.ofNat 256 b <<< 5)).toNat', 'hconst', 'v')],
        guards={2: 'by rw [hdec]; rw [decide_eq_false (by omega : \u00ac ((BitVec.ofNat 256 ' + CM +
                    ').toNat < (BitVec.ofNat 256 b).toNat))]; rfl'},
        extras=[('(hguard : (BitVec.ofNat 256 b).toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat)',
                 '(BitVec.ofNat 256 b).toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat', 'hguard')],
        emit_top='w' + w.lower() + 'mod x v',
        ref_top='BitVec.ofNat 256 (qvmFr' + w + ' x.toNat v.toNat)',
        tie=['w' + w.lower() + 'mod_eq_qvmFr' + w])

ARMS['addConst'] = lambda: constArm('addConst', 'qArmBodyAddConst', True)
ARMS['mulConst'] = lambda: constArm('mulConst', 'qArmBodyMulConst', False)

ARMS['addMulMemMem'] = lambda: S(
    'addMulMemMem', 'qArmBodyAddMulMemMem', '(pc x lv rv : U256) (l r : Nat)', 'pc x lv rv l r ',
    [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r')],
    [(shr(240), 'hl', 'BitVec.ofNat 256 l'),
     ('(' + DEC + ' >>> 224) &&& BitVec.ofNat 256 65535', 'hr', 'BitVec.ofNat 256 r'),
     ('loadWord st.memory (BitVec.ofNat 256 l).toNat', 'hlv', 'lv'),
     ('loadWord st.memory (BitVec.ofNat 256 r).toNat', 'hrv', 'rv')],
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
    [(shr(240), 'hp', 'BitVec.ofNat 256 p'),
     (bytek(2), 'hb', 'BitVec.ofNat 256 b'),
     ('loadWord st.memory (BitVec.ofNat 256 p).toNat', 'hpv', 'pv'),
     ('loadWord st.memory (cb + (BitVec.ofNat 256 b <<< 5)).toNat', 'hcv', 'cv')],
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
    [(shr(240), 'hl', 'BitVec.ofNat 256 l'),
     ('(' + DEC + ' >>> 224) &&& BitVec.ofNat 256 65535', 'hr', 'BitVec.ofNat 256 r'),
     (bytek(4), 'hb', 'BitVec.ofNat 256 b'),
     ('loadWord st.memory (BitVec.ofNat 256 l).toNat', 'hlv', 'lv'),
     ('loadWord st.memory (BitVec.ofNat 256 r).toNat', 'hrv', 'rv'),
     ('loadWord st.memory (cb + (BitVec.ofNat 256 b <<< 5)).toNat', 'hcv', 'cv')],
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
    [(shr(240), 'hptr', 'BitVec.ofNat 256 p'),
     ('loadWord st.memory (BitVec.ofNat 256 p).toNat', 'hload', 'BitVec.ofNat 256 v')],
    guards={2: 'rfl'})

ARMS['pushMemLiteral'] = lambda: S(
    'pushMemLiteral', 'qArmBodyPushMemLiteral', '(pc sp x v : U256) (p : Nat)', 'pc sp x v p ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top')],
    [(shr(224), 'hptr', 'BitVec.ofNat 256 p'),
     ('loadWord st.memory (BitVec.ofNat 256 p).toNat', 'hload', 'BitVec.ofNat 256 v')],
    guards={2: 'rfl'})

ARMS['pushConstU8'] = lambda: S(
    'pushConstU8', 'qArmBodyPushConstU8', '(pc cb sp x v : U256) (b : Nat)', 'pc cb sp x v b ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top'), ('q_const_mptr', 'cb', 'hget_cb')],
    [(bytek(0), 'hdec', 'BitVec.ofNat 256 b'),
     ('loadWord st.memory (cb + (BitVec.ofNat 256 b <<< 5)).toNat', 'hconst', 'BitVec.ofNat 256 v')],
    guards={1: 'rfl'})

ARMS['pushConst'] = lambda: S(
    'pushConst', 'qArmBodyPushConst', '(pc cb sp x v : U256) (b : Nat)', 'pc cb sp x v b ',
    [('q_pc', 'pc', 'hget_pc')] + HT + [('q_top', 'x', 'hget_top'), ('q_const_mptr', 'cb', 'hget_cb')],
    [(shr(240), 'hdec', 'BitVec.ofNat 256 b'),
     ('loadWord st.memory (cb + (BitVec.ofNat 256 b <<< 5)).toNat', 'hconst', 'BitVec.ofNat 256 v')],
    guards={1: 'by rw [hdec]; rw [decide_eq_false (by omega : \u00ac ((BitVec.ofNat 256 ' + CM +
               ').toNat < (BitVec.ofNat 256 b).toNat))]; rfl', 2: 'rfl'},
    extras=[('(hguard : (BitVec.ofNat 256 b).toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat)',
             '(BitVec.ofNat 256 b).toNat \u2264 (BitVec.ofNat 256 ' + CM + ').toNat', 'hguard')])

if __name__ == '__main__':
    which = sys.argv[1:] or sorted(ARMS)
    for w in which:
        a = Arm(ARMS[w]())
        print(a.emit())
        print()
        for l in a.lemmas():
            print(l)

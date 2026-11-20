# -*- coding: utf-8 -*-
import sys
from qgen2 import Arm
from qparse import sv

FR = 'frModulusWord'

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

ARMS['addMemU16'] = lambda: S(
    'addMemU16', 'qArmBodyAddMemU16', '(pc x v : U256) (p : Nat)', 'pc x v p ',
    [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r')],
    [('(loadWord st.memory pc.toNat >>> 240)', 'hptr', 'BitVec.ofNat 256 p'),
     ('loadWord st.memory (BitVec.ofNat 256 p).toNat', 'hload', 'v')],
    emit_top='wAddmod x v', ref_top='BitVec.ofNat 256 (qvmFrAdd x.toNat v.toNat)',
    tie=['wAddmod_eq_qvmFrAdd'])

ARMS['mulMemU16'] = lambda: S(
    'mulMemU16', 'qArmBodyMulMemU16', '(pc x v : U256) (p : Nat)', 'pc x v p ',
    [('q_pc', 'pc', 'hget_pc'), ('q_top', 'x', 'hget_top'), ('r', FR, 'hget_r')],
    [('(loadWord st.memory pc.toNat >>> 240)', 'hptr', 'BitVec.ofNat 256 p'),
     ('loadWord st.memory (BitVec.ofNat 256 p).toNat', 'hload', 'v')],
    emit_top='wMulmod x v', ref_top='BitVec.ofNat 256 (qvmFrMul x.toNat v.toNat)',
    tie=['wMulmod_eq_qvmFrMul'])

if __name__ == '__main__':
    which = sys.argv[1:] or list(ARMS)
    for w in which:
        a = Arm(ARMS[w]())
        print(a.emit())
        print()
        for l in a.lemmas():
            print(l)
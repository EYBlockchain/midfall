# -*- coding: utf-8 -*-
"""QARMS2 - the two FOLD arms.

These are the only two of the eleven arms still open when this card started that the generator can
drive at all: both are STATIC straight-line blocks (no 'yfor'), so 'qgen2' symbolically executes them
exactly as it does the twenty landed arms.  The six loop arms (three limb, three run) need an
induction over 'Step.loopStep'/'Step.loopDone' and are out of the generator's reach; the three native
arms splice DATA out of the 'PartialCtx' and are out of any static arm's reach.

WHAT MAKES THEM DIFFERENT FROM EVERY ARM LANDED BEFORE, AND WHY THERE IS NO 'ref_top' HERE.  The
twenty landed arms are VALUE REFINEMENTS: the emitted arm pushes a word onto 'q_top' and the middle
theorem of the triple identifies that word with what 'qStepValue_X' says the reference pushes.  The
fold arms do not push.  Their whole effect is a WRITE of the identity's value into the accumulator
slot 'program.evalNumerMptr' and the clearing of the cached top, so their post-state memory is
'storeWord', not 'touchMemory'.  'Midfall/Generator/Quotient/VmReference.lean:861-865' returns
'.error (QVMFault.streamOpcodeInIdentity op idx)' for both fold opcodes: they are OUT OF THE DOMAIN of
'evalQuotientIdentityStep' by design (rust QVR:325-333), so there is NO reference equation to tie to
and none was invented.  What is landed here is the EMITTED-SIDE contract - the arm's own state and
environment equation - and the reference-side statement that would complete the triple is named in
'QuotientArms.lean'.

Two generator features these arms need and no earlier arm did:

* 'guards' for the identity-boundary test.  'iszero (and q_has_top (eq q_sp (ylit program.stackMptr)))'
  does not reduce, because 'decide (x = x)' does not reduce for a symbolic 'x'.  The pins therefore
  put 'q_has_top' at the live-top word '1' and 'q_sp' AT the program's own 'stackMptr' word, and the
  guard discharges with 'decide_eq_true (rfl : S = S)'.  That is a precondition about the VM's own
  registers, exactly like the 'q_has_top = 0' pin the four PUSH arms carry.
* 'read_proofs' for the fold's read-back.  The arm writes the accumulator and then reads it again in
  the very next statement.  The second read is 'loadWord (storeWord m p v) = v' - a LEMMA
  ('Midfall.Yul.Word.loadWord_storeWord_same'), not a precondition - so it is substituted into the
  post and discharged inline instead of being stated as a hypothesis.
"""
import sys
from qgen2 import Arm, P
from qparse import sv
from qsem import op_info

FR = 'frModulusWord'
EP = 'BitVec.ofNat 256 program.evalNumerMptr'
SP = 'BitVec.ofNat 256 program.stackMptr'
LWS = 'Midfall.Yul.Word.loadWord_storeWord_same'


def Vshr(k, v):
    return op_info('shr', [('lit', str(k))])[1](sv(k), v)[0]


def Vbyte(i, v):
    return op_info('byte', [('lit', str(i))])[1](sv(i), v)[0]


def Vadd(x, y):
    return op_info('add', [])[1](x, y)[0]


def Vand(x, y):
    return op_info('and', [])[1](x, y)[0]


def Vshl(k, v):
    return op_info('shl', [('lit', str(k))])[1](sv(k), v)[0]


def Vload(mem, p):
    return 'loadWord ' + P(mem) + ' ' + P(p) + '.toNat'


def S(name, body, binders, varargs, pins, reads, guards=None, extras=None, read_proofs=None):
    d = dict(name=name, body=body, binders=binders, varargs=varargs, pins=pins, reads=reads)
    if guards:
        d['guards'] = guards
    if extras:
        d['extras'] = extras
    if read_proofs:
        d['read_proofs'] = read_proofs
    return d


ACC = Vload('st.memory', EP)
BOUNDARY = 'by rw [decide_eq_true (rfl : (' + SP + ') = _)]; rfl'

ARMS = {}

# ------------------------------------------------------------------------ FOLD_MAIN
#   if !(has_top && sp == stackMptr) { fail }     -- pinned to the LIVE-top, balanced-stack case
#   let q_eval := q_top
#   q_has_top := 0
#   mstore(evalNumer, mulmod(mload(evalNumer), y, r))
#   mstore(evalNumer, addmod(mload(evalNumer), q_eval, r))
ARMS['foldMain'] = lambda: S(
    'foldMain', 'qArmBodyFoldMain', '(x y a : U256)', 'x y a ',
    [('q_has_top', '1', 'hget_ht'), ('q_sp', SP, 'hget_sp'), ('q_top', 'x', 'hget_top'),
     ('y', 'y', 'hget_y'), ('r', FR, 'hget_r')],
    [(ACC, 'hacc', 'a'),
     (Vload('storeWord st.memory ' + P(EP) + '.toNat (wMulmod a y)', EP), 'hrb', 'wMulmod a y')],
    guards={0: BOUNDARY},
    read_proofs={'hrb': LWS + ' st.memory ' + P(EP) + '.toNat (wMulmod a y)'})

# --------------------------------------------------------------------------- FOLD_SELECTOR
#   let q_selector_payload := shr 232 (mload q_pc);  q_pc += 3
#   let q_sel_idx := shr 16 payload;  let q_sel_gap := and payload 65535
#   three identity/bucket/gap guards, all pinned to the FALSE branch
#   let q_eval := q_top;  q_has_top := 0
#   mstore(evalNumer, mulmod(mload(evalNumer), y, r))            -- the same accumulator fold
#   let q_target_ptr := add SELECTOR_ACC_MPTR (shl 5 q_sel_idx)
#   let q_sel_acc := mload q_target_ptr
#   if q_sel_gap { ... }                                         -- pinned to gap = 0
#   mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
# The gap is pinned to zero: 'qgen2' only emits 'Step.ifFalse', so the y-power multiply of
# statement 12 is the branch that is NOT landed, and 'hgap' says so in the statement.
SHR232 = Vshr(232, 'loadWord st.memory pc.toNat')
IDX = Vshr(16, 'pl')
GAP = Vand('pl', sv(65535))
TPTR = Vadd('sa', Vshl(5, 'si'))
TPTRV = 'sa + (si <<< 5)'
MEM1 = 'storeWord st.memory ' + P(EP) + '.toNat (wMulmod a y)'

ARMS['foldSelector'] = lambda: S(
    'foldSelector', 'qArmBodyFoldSelector', '(pc x y a pl si sa sv2 : U256)',
    'pc x y a pl si sa sv2 ',
    [('q_pc', 'pc', 'hget_pc'), ('q_has_top', '1', 'hget_ht'),
     ('q_sp', SP, 'hget_sp'), ('q_top', 'x', 'hget_top'), ('y', 'y', 'hget_y'),
     ('r', FR, 'hget_r'), ('SELECTOR_ACC_MPTR', 'sa', 'hget_sa')],
    [(SHR232, 'hpl', 'pl'), (IDX, 'hidx', 'si'), (GAP, 'hgap', 'BitVec.ofNat 256 0'),
     (Vload('st.memory', EP), 'hacc', 'a'),
     (Vload(MEM1, TPTRV), 'hsacc', 'sv2'),
     (Vload('storeWord st.memory ' + P(EP) + '.toNat (wMulmod a y)', EP), 'hrb', 'wMulmod a y')],
    guards={4: 'by rw [decide_eq_true hbucket]; rfl', 5: 'rfl', 6: BOUNDARY, 12: 'rfl'},
    extras=[('(hbucket : si.toNat < (BitVec.ofNat 256 program.guards.numSelectorBuckets).toNat)',
             'si.toNat < (BitVec.ofNat 256 program.guards.numSelectorBuckets).toNat', 'hbucket')],
    read_proofs={'hrb': LWS + ' st.memory ' + P(EP) + '.toNat (wMulmod a y)'})

if __name__ == '__main__':
    which = sys.argv[1:] or sorted(ARMS)
    for w in which:
        a = Arm(ARMS[w]())
        print(a.emit())
        print()
        for l in a.lemmas():
            print(l)

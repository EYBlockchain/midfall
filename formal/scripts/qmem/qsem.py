import sys
from qparse import arm_body, sv, D

Q = chr(34)
NL = chr(10)

def syn(e):
    k = e[0]
    if k == 'var':  return 'yvar ' + Q + e[1] + Q
    if k == 'lit':  return 'ylit ' + e[1]
    if k == 'op':   return 'yop Op.' + e[1] + ' [' + ', '.join(syn(a) for a in e[2]) + ']'
    if k == 'call': return 'ycall ' + Q + e[1] + Q + ' [' + ', '.join(syn(a) for a in e[2]) + ']'
    raise Exception(k)

def syn_stmt(s):
    k = s[0]
    if k == 'let':  return 'ylet ' + Q + s[1] + Q + ' (' + syn(s[2]) + ')'
    if k == 'set':  return 'yset ' + Q + s[1] + Q + ' (' + syn(s[2]) + ')'
    if k == 'expr': return 'yexpr (' + syn(s[1]) + ')'
    if k == 'if':   return 'yif (' + syn(s[1]) + ') [' + ', '.join(syn_stmt(x) for x in s[2]) + ']'
    if k == 'switch': return 'Stmt.switch (' + syn(s[1]) + ') (' + s[2] + ') (' + s[3] + ')'
    raise Exception(k)

def syn_block(body):
    return '[' + ', '.join(syn_stmt(s) for s in body) + ']'

BI = {}
def bi(nm, op, binders, argpat, res):
    BI[nm] = (op, binders, argpat, res)

bi('qbi_add', 'add', '(st : EvmState) (a b : U256)', '[a, b]', '[a + b] st')
bi('qbi_sub', 'sub', '(st : EvmState) (a b : U256)', '[a, b]', '[a - b] st')
bi('qbi_mul', 'mul', '(st : EvmState) (a b : U256)', '[a, b]', '[a * b] st')
bi('qbi_and', 'and', '(st : EvmState) (a b : U256)', '[a, b]', '[a &&& b] st')
bi('qbi_or', 'or', '(st : EvmState) (a b : U256)', '[a, b]', '[a ||| b] st')
bi('qbi_xor', 'xor', '(st : EvmState) (a b : U256)', '[a, b]', '[a ^^^ b] st')
bi('qbi_eq', 'eq', '(st : EvmState) (a b : U256)', '[a, b]', '[b2w (decide (a = b))] st')
bi('qbi_iszero', 'iszero', '(st : EvmState) (a : U256)', '[a]', '[b2w (decide (a = 0))] st')
bi('qbi_lt', 'lt', '(st : EvmState) (a b : U256)', '[a, b]', '[b2w (decide (a.toNat < b.toNat))] st')
bi('qbi_gt', 'gt', '(st : EvmState) (a b : U256)', '[a, b]', '[b2w (decide (b.toNat < a.toNat))] st')
bi('qbi_addmod_atFr', 'addmod', '(st : EvmState) (a b : U256)', '[a, b, frModulusWord]', '[wAddmod a b] st')
bi('qbi_mulmod_atFr', 'mulmod', '(st : EvmState) (a b : U256)', '[a, b, frModulusWord]', '[wMulmod a b] st')
for _k in (1, 2, 3, 4, 5, 6, 7, 8):
    bi('qbi_shl' + str(_k), 'shl', '(st : EvmState) (v : U256)', '[' + sv(_k) + ', v]', '[v <<< ' + str(_k) + '] st')
for _k in (16, 168, 216, 224, 232, 240, 248):
    bi('qbi_shr' + str(_k), 'shr', '(st : EvmState) (v : U256)', '[' + sv(_k) + ', v]', '[v >>> ' + str(_k) + '] st')
for _i in (0, 1, 2, 3, 4):
    bi('qbi_byte' + str(_i), 'byte', '(st : EvmState) (w : U256)', '[' + sv(_i) + ', w]',
       '[(w >>> ' + str(248 - 8 * _i) + ') &&& 0xff] st')

def bi_src(nm):
    op, binders, argpat, res = BI[nm]
    return ('theorem ' + nm + ' {c : ExternalCalls} {g : ExternalGas} ' + binders + ' :' + NL +
            '    (' + D + ').Builtin Op.' + op + ' ' + argpat + ' st (.ok ' + res + ') := rfl')

bi('qbi_mload_at', 'mload', '(st : EvmState) (m : Nat -> UInt8) (p : U256) (h : st.memory = m)',
   '[p]', '[loadWord m p.toNat] (touchMemory st p.toNat 32)')
bi('qbi_mstore_at', 'mstore',
   '(st : EvmState) (m : Nat -> UInt8) (p : U256) (v : U256) (h : st.memory = m)', '[p, v]',
   '[] { touchMemory st p.toNat 32 with memory := storeWord m p.toNat v }')

def bi_at_src(nm):
    op, binders, argpat, res = BI[nm]
    return ('theorem ' + nm + ' {c : ExternalCalls} {g : ExternalGas} ' + binders + ' :' + NL +
            '    (' + D + ').Builtin Op.' + op + ' ' + argpat + ' st (.ok ' + res + ') := by' + NL +
            '  rw [<- h]' + NL + '  rfl')

def op_info(op, args):
    from qgen2 import P
    if op in ('add', 'sub', 'mul', 'and', 'or', 'xor'):
        f = {'add': lambda a, b: ['(' + a + ' + ' + b + ')'],
             'sub': lambda a, b: ['(' + a + ' - ' + b + ')'],
             'mul': lambda a, b: ['(' + a + ' * ' + b + ')'],
             'and': lambda a, b: ['(' + a + ' &&& ' + b + ')'],
             'or': lambda a, b: ['(' + a + ' ||| ' + b + ')'],
             'xor': lambda a, b: ['(' + a + ' ^^^ ' + b + ')']}
        return 'qbi_' + op, f[op], 2
    if op == 'eq':
        return 'qbi_eq', (lambda a, b: ['b2w (decide (' + P(a) + ' = ' + P(b) + '))']), 2
    if op == 'iszero':
        return 'qbi_iszero', (lambda a: ['b2w (decide (' + P(a) + ' = 0))']), 1
    if op == 'lt':
        return 'qbi_lt', (lambda a, b: ['b2w (decide (' + P(a) + '.toNat < ' + P(b) + '.toNat))']), 2
    if op == 'gt':
        return 'qbi_gt', (lambda a, b: ['b2w (decide (' + P(b) + '.toNat < ' + P(a) + '.toNat))']), 2
    if op == 'addmod':
        return 'qbi_addmod_atFr', (lambda a, b, r: ['wAddmod ' + P(a) + ' ' + P(b)]), 3
    if op == 'mulmod':
        return 'qbi_mulmod_atFr', (lambda a, b, r: ['wMulmod ' + P(a) + ' ' + P(b)]), 3
    if op == 'shl':
        k = int(args[0][1])
        return 'qbi_shl' + str(k), (lambda s_, v: ['(' + P(v) + ' <<< ' + str(k) + ')']), 2
    if op == 'shr':
        k = int(args[0][1])
        return 'qbi_shr' + str(k), (lambda s_, v: ['(' + P(v) + ' >>> ' + str(k) + ')']), 2
    if op == 'byte':
        i = int(args[0][1])
        return 'qbi_byte' + str(i), (lambda s_, v: ['((' + P(v) + ' >>> ' + str(248 - 8 * i) + ') &&& 0xff)']), 2
    raise Exception('no op ' + op)

if __name__ == '__main__':
    print(bi_src('qbi_gt'))
    print(bi_at_src('qbi_mload_at'))
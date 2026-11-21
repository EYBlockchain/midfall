# -*- coding: utf-8 -*-
import sys
from qparse import arm_body, sv, D
from qsem import syn, syn_stmt, syn_block, op_info, BI, bi_src, bi_at_src

Q = chr(34)
NL = chr(10)
NE = chr(8800)
AND = chr(8743)
LAng = chr(10216)
RAng = chr(10217)

def isatom(t):
    return all(ch.isalnum() or ch in "_'." for ch in t) and t != ''

def P(t):
    if isatom(t):
        return t
    if t.startswith('(') and t.endswith(')'):
        return t
    return '(' + t + ')'

def idq(x):
    return Q + x + Q

def T(t):
    return idq(t)

# --------------------------------------------------------------- positions
class Pos(object):
    def __init__(self, V, st, mem, memEq, env):
        self.V = V; self.st = st; self.mem = mem; self.memEq = memEq
        self.env = dict(env)
    def cp(self):
        return Pos(self.V, self.st, self.mem, self.memEq, self.env)

class Gen(object):
    def __init__(self, spec):
        self.spec = spec
        self.out = []
        self.k = 0
        self.used = set()
        self.decode = {}
        self.funs_lbl = 'funs'
        # 'read_proofs' maps a read-equation name to a PROOF TERM for it. Such a read is still
        # substituted into the post (so the post is clean) but it is NOT a hypothesis of the theorem:
        # it is discharged inline. Used by the fold arms, whose second accumulator read is
        # 'loadWord (storeWord m p v) p = v' - a lemma, not a precondition.
        self.read_proofs = spec.get('read_proofs', {})
        for (computed, hyp, repl) in spec.get('reads', []):
            self.decode[computed] = (hyp, repl)

    def have(self, name, typ, proof):
        if len(typ) + len(proof) > 92:
            self.out.append('have ' + name + ' :' + NL + '    ' + typ + ' :=' + NL + '    ' + proof)
        else:
            self.out.append('have ' + name + ' : ' + typ + ' := ' + proof)

    def fresh(self, pfx):
        self.k += 1
        return pfx + str(self.k)

    def start(self):
        env = {}
        for (reg, val, hyp) in self.spec['pins']:
            env[reg] = (val, hyp)
        return Pos('V', 'st', 'st.memory', None, env)

    def retarget(self, p, kind, x, v):
        if kind == 'cons':
            newV = '((' + T(x) + ', ' + v + ') :: ' + P(p.V) + ')'
        else:
            newV = '(VEnv.set ' + P(p.V) + ' ' + T(x) + ' ' + P(v) + ')'
        newenv = {}
        for y, (vy, py) in sorted(p.env.items()):
            if y == x:
                continue
            nm = self.fresh('g')
            dec = '(by decide : ' + T(x) + ' ' + NE + ' ' + T(y) + ')'
            if kind == 'cons':
                pr = ('by rw [venvGet_cons_ne ' + P(p.V) + ' ' + T(x) + ' ' + T(y) + ' ' + P(v) +
                      ' ' + dec + ']; exact ' + py)
            else:
                pr = ('venvGet_set_ne ' + P(p.V) + ' ' + T(x) + ' ' + T(y) + ' ' + P(v) + ' ' + P(vy) +
                      ' ' + dec + ' ' + py)
            self.have(nm, 'VEnv.get ' + newV + ' ' + T(y) + ' = some ' + P(vy), pr)
            newenv[y] = (vy, nm)
        nm = self.fresh('g')
        if kind == 'cons':
            self.have(nm, 'VEnv.get ' + newV + ' ' + T(x) + ' = some ' + P(v),
                      'venvGet_cons_eq ' + P(p.V) + ' ' + T(x) + ' ' + P(v))
        else:
            oldv, oldp = p.env[x]
            self.have(nm, 'VEnv.get ' + newV + ' ' + T(x) + ' = some ' + P(v),
                      'venvGet_set_same ' + P(p.V) + ' ' + T(x) + ' ' + P(v) + ' ' + P(oldv) + ' ' + oldp)
        newenv[x] = (v, nm)
        q = p.cp()
        q.V = newV
        q.env = newenv
        return q

    # ------------------------------------------------------------ expressions
    def step_ty(self, p, code, res):
        return 'Step (D := ' + D + ') ' + self.funs_lbl + ' ' + P(p.V) + ' ' + P(p.st) + ' (' + code + ') (' + res + ')'

    def ev_args(self, p, args):
        if not args:
            nm = self.fresh('a')
            self.have(nm, self.step_ty(p, '.args []', '.eres (.vals [] ' + P(p.st) + ')'),
                      'Step.argsNil (D := ' + D + ')')
            return p, [], nm
        head, rest = args[0], args[1:]
        p2, rvals, prest = self.ev_args(p, rest)
        p3, v, phead = self.ev_expr(p2, head)
        nm = self.fresh('a')
        allv = ([v] if v is not None else []) + rvals
        self.have(nm, self.step_ty(p, '.args [' + ', '.join(syn(a) for a in args) + ']',
                                   '.eres (.vals [' + ', '.join(allv) + '] ' + P(p3.st) + ')'),
                  'Step.argsCons (D := ' + D + ') (rest := [' + ', '.join(syn(a) for a in rest) +
                  ']) (restvals := [' + ', '.join(rvals) + ']) (st1 := ' + p2.st + ') (v := ' + v +
                  ') (st2 := ' + p3.st + ') ' + prest + ' ' + phead)
        return p3, allv, nm

    def ev_expr(self, p, e):
        k = e[0]
        if k == 'var':
            v, pr = p.env[e[1]]
            nm = self.fresh('x')
            self.have(nm, self.step_ty(p, '.expr (' + syn(e) + ')', '.eres (.vals [' + v + '] ' + P(p.st) + ')'),
                      'Step.var (D := ' + D + ') ' + pr)
            return p, v, nm
        if k == 'lit':
            v = sv(e[1])
            nm = self.fresh('x')
            self.have(nm, self.step_ty(p, '.expr (' + syn(e) + ')', '.eres (.vals [' + v + '] ' + P(p.st) + ')'),
                      'Step.lit (D := ' + D + ') (l := Literal.number ' + e[1] + ')')
            return p, v, nm
        if k == 'op':
            op, args = e[1], e[2]
            pa, vals, pargs = self.ev_args(p, args)
            if op == 'mload':
                self.used.add('qbi_mload_at')
                raw = 'loadWord ' + P(pa.mem) + ' ' + P(vals[0]) + '.toNat'
                stnew = 'touchMemory ' + P(pa.st) + ' ' + P(vals[0]) + '.toNat 32'
                newmem = pa.mem
                call = 'qbi_mload_at ' + P(pa.st) + ' ' + P(pa.mem) + ' ' + P(vals[0]) + ' ' + (pa.memEq or 'rfl')
            elif op == 'mstore':
                self.used.add('qbi_mstore_at')
                raw = None
                stnew = ('{ touchMemory ' + P(pa.st) + ' ' + P(vals[0]) + '.toNat 32 with memory := storeWord '
                         + P(pa.mem) + ' ' + P(vals[0]) + '.toNat ' + P(vals[1]) + ' }')
                newmem = 'storeWord ' + P(pa.mem) + ' ' + P(vals[0]) + '.toNat ' + P(vals[1])
                call = ('qbi_mstore_at ' + P(pa.st) + ' ' + P(pa.mem) + ' ' + P(vals[0]) + ' ' + P(vals[1])
                        + ' ' + (pa.memEq or 'rfl'))
            else:
                nm_lem, vf, arity = op_info(op, args)
                self.used.add(nm_lem)
                raw = vf(*vals)[0]
                stnew = pa.st
                newmem = pa.mem
                if op in ('shl', 'shr', 'byte'):
                    callargs = vals[1:]
                elif op in ('addmod', 'mulmod'):
                    callargs = vals[:2]
                else:
                    callargs = vals
                call = nm_lem + ' ' + P(pa.st) + ' ' + ' '.join(P(x) for x in callargs)
            resvals = '[]' if raw is None else '[' + raw + ']'
            nm = self.fresh('x')
            self.have(nm, self.step_ty(p, '.expr (' + syn(e) + ')', '.eres (.vals ' + resvals + ' ' + P(stnew) + ')'),
                      'Step.builtinOk ' + pargs + ' (' + call + ')')
            key = raw if raw is not None else None
            val = raw
            if key is not None and key in self.decode:
                hyp, repl = self.decode[key]
                nm2 = self.fresh('d')
                rp = self.read_proofs.get(hyp)
                # A read PROOF is applied to the derivation, not to the goal: rewriting the goal
                # with '<- prf' can hit an earlier syntactic occurrence of the replacement value
                # (the fold arm writes 'wMulmod a y' into memory and then reads it back, and the
                # write comes before the read in the term).  'rw [prf] at h' rewrites only the
                # 'loadWord (storeWord m p v) p' pattern, which occurs once.
                src = ('by have h9 := ' + nm + '; rw [' + rp + '] at h9; exact h9') if rp \
                    else ('by rw [<- ' + hyp + ']; exact ' + nm)
                self.have(nm2, self.step_ty(p, '.expr (' + syn(e) + ')', '.eres (.vals [' + repl + '] ' + P(stnew) + ')'),
                          src)
                nm = nm2
                val = repl
            q = pa.cp()
            q.st = stnew
            q.mem = newmem
            if op == 'mload':
                hn = self.fresh('w')
                tm = 'Midfall.Yul.Word.touchMemory_memory ' + P(pa.st) + ' ' + P(vals[0]) + '.toNat 32'
                self.have(hn, '(' + stnew + ').memory = ' + newmem,
                          tm if not pa.memEq else ('Eq.trans (' + tm + ') ' + P(pa.memEq)))
                q.memEq = hn
            elif op == 'mstore':
                q.memEq = 'rfl'
            else:
                q.memEq = pa.memEq
            return q, val, nm
        raise Exception(k)

def stmt_syn(s):
    return '.stmt (' + syn_stmt(s) + ')'

class Arm(object):
    def __init__(self, spec):
        self.spec = spec
        self.g = Gen(spec)
        self.body = arm_body(spec['body'])
        self.steps = []

    def run(self):
        if getattr(self, 'done', False):
            return self.final
        self.done = True
        g = self.g
        p = g.start()
        guards = self.spec.get('guards', {})
        for i, s in enumerate(self.body):
            p, nm = self.do_stmt(p, s, guards.get(i), self.steps)
        self.final = p
        return p

    def do_stmt(self, p, s, guard, sink):
        """one statement -> (new position, name of its Step derivation). 'sink' collects the
        (V0, st0, V1, st1, nm) records the seqCons chain at the end of the theorem needs."""
        g = self.g
        V0, st0 = p.V, p.st
        k = s[0]
        if k == 'let':
            p2, v, px = g.ev_expr(p, s[2])
            nm = g.fresh('s')
            newV = '((' + idq(s[1]) + ', ' + v + ') :: ' + P(p.V) + ')'
            g.have(nm, g.step_ty(p, stmt_syn(s), '.sres ' + P(newV) + ' ' + P(p2.st) + ' .normal'),
                   'Step.letVal ' + px + ' rfl')
            p = g.retarget(p2, 'cons', s[1], v)
        elif k == 'set':
            p2, v, px = g.ev_expr(p, s[2])
            nm = g.fresh('s')
            newV = '(VEnv.set ' + P(p.V) + ' ' + idq(s[1]) + ' ' + P(v) + ')'
            g.have(nm, g.step_ty(p, stmt_syn(s), '.sres ' + P(newV) + ' ' + P(p2.st) + ' .normal'),
                   'Step.assignVal (D := ' + D + ') (vars := [' + idq(s[1]) + ']) (vals := [' +
                   v + ']) ' + px + ' (by rfl)')
            p = g.retarget(p2, 'set', s[1], v)
        elif k == 'expr':
            p2, v, px = g.ev_expr(p, s[1])
            nm = g.fresh('s')
            g.have(nm, g.step_ty(p, stmt_syn(s), '.sres ' + P(p.V) + ' ' + P(p2.st) + ' .normal'),
                   'Step.exprStmt ' + px)
            p = p2
        elif k == 'if':
            p2, cv, pc = g.ev_expr(p, s[1])
            hz = g.fresh('z')
            g.have(hz, cv + ' = (' + D + ').zero', guard)
            nm = g.fresh('s')
            g.have(nm, g.step_ty(p, stmt_syn(s), '.sres ' + P(p.V) + ' ' + P(p2.st) + ' .normal'),
                   'Step.ifFalse ' + pc + ' ' + hz)
            p = p2
        elif k == 'switch':
            p, nm = self.do_switch(p, s)
        else:
            raise Exception('stmt ' + k)
        sink.append((V0, st0, p.V, p.st, nm))
        return p, nm

    def seq_chain(self, recs):
        """Step.seqCons ... Step.seqNil over a list of (V0, st0, V1, st1, nm) records."""
        lines = []
        n = len(recs)
        for i, (V0, st0, V1, st1, nm) in enumerate(recs):
            head = 'exact ' if i == n - 1 else 'refine '
            tail = ' (Step.seqNil (D := ' + D + '))' if i == n - 1 else ' ?_'
            lines.append(head + 'Step.seqCons (D := ' + D + ') (V1 := ' + P(V1) + ') (st1 := ' +
                         P(st1) + ') ' + nm + tail)
        return 'by ' + (chr(10) + '       ').join(lines)

    def do_switch(self, p, s):
        """'Stmt.switch cv CASES dflt' with the emitted 'if program.memUsage.X then [(label, body)]
        else []' shape. Only the flag of the entry taken has to be assumed: 'List.find?' short-circuits
        on the head, so the other eight entries and the default are irrelevant. The block that
        'Step.switchExec' asks for is a 'Step.block', so 'restore_set' is what turns its post-environment
        back into the 'VEnv.set' form the contract states."""
        g = self.g
        scrut, cases_raw, dflt_raw, ents = s[1], s[2], s[3], s[4]
        ent = ents[self.spec.get('switch_entry', 0)]
        body = ent['body']
        p2, cv, px = g.ev_expr(p, scrut)
        bsel = syn_block(body)
        sel = 'selectSwitch (' + D + ') ' + P(cv) + ' (' + cases_raw + ') (' + dflt_raw + ')'
        hsel = g.fresh('h')
        flag = self.spec['switch_flag']
        g.have(hsel, sel + ' = ' + bsel,
               'by refine selectSwitch_head (D := ' + D + ') ' + P(cv) + ' (' + cases_raw + ') ' +
               '(Literal.number tcq.mem.' + ent['label'] + ', ' + bsel + ') (' + dflt_raw + ') ?_' +
               chr(10) + '       rw [' + flag + ']' + chr(10) +
               '       exact find?_head _ _ _ (decide_litValue_number_eq_self tcq.mem.' + ent['label'] + ')')
        hoistf = '(hoist (' + D + ') ' + bsel + ' :: funs)'
        saved = g.funs_lbl
        g.funs_lbl = hoistf
        q = p2
        inner = []
        for s2 in body:
            q, nm2 = self.do_stmt(q, s2, None, inner)
        g.funs_lbl = saved
        Vb, stb = q.V, q.st
        bN = g.fresh('b')
        g.have(bN, 'Step (D := ' + D + ') ' + hoistf + ' ' + P(p2.V) + ' ' + P(p2.st) +
               ' (.stmts ' + bsel + ') (.sres ' + P(Vb) + ' ' + P(stb) + ' .normal)',
               self.seq_chain(inner))
        k0 = g.fresh('k')
        g.have(k0, g.step_ty(p2, '.stmt (.block (' + sel + '))',
               '.sres (restore ' + P(p2.V) + ' ' + P(Vb) + ') ' + P(stb) + ' .normal'),
               'by refine Step.block (D := ' + D + ') ?_' + chr(10) + '       rw [' + hsel + ']' +
               chr(10) + '       exact ' + bN)
        k1 = g.fresh('k')
        g.have(k1, g.step_ty(p2, '.stmt (.block (' + sel + '))',
               '.sres ' + P(Vb) + ' ' + P(stb) + ' .normal'),
               'by rw [restore_set] at ' + k0 + chr(10) + '       exact ' + k0)
        nm = g.fresh('s')
        g.have(nm, g.step_ty(p, '.stmt (' + syn_stmt(s) + ')', '.sres ' + P(Vb) + ' ' + P(stb) + ' .normal'),
               'Step.switchExec (D := ' + D + ') ' + px + ' ' + k1)
        return q, nm

    def pre_list(self):
        s = self.spec
        rp = s.get('read_proofs', {})
        ps = ['VEnv.get V ' + idq(reg) + ' = some ' + P(val) for (reg, val, h) in s['pins']]
        ps += [c + ' = ' + r for (c, h, r) in s.get('reads', []) if h not in rp]
        return ps

    def projections(self):
        n = len(self.pre_list())
        res = []
        cur = 'hpre'
        for i in range(n):
            if i == n - 1:
                res.append(cur)
            else:
                res.append(cur + '.1')
                cur = cur + '.2'
        return res

    def hyp_lines(self):
        s = self.spec
        out = []
        for (reg, val, hyp) in s['pins']:
            out.append('(' + hyp + ' : VEnv.get V ' + idq(reg) + ' = some ' + P(val) + ')')
        rp = s.get('read_proofs', {})
        for (computed, hyp, repl) in s.get('reads', []):
            if hyp in rp:
                continue
            out.append('(' + hyp + ' : ' + computed + ' = ' + repl + ')')
        for (b, prop, name) in s.get('extras', []):
            out.append(b)
        return out

    def print_run(self):
        s = self.spec
        L = []
        L.append('theorem qArmRun_' + s['name'] + ' {c : ExternalCalls} {g : ExternalGas}')
        L.append('    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)')
        L.append('    (funs : FunEnv (' + D + ')) (V : VEnv (' + D + ')) (st : EvmState)')
        if s.get('binders'):
            L.append('    ' + s['binders'])
        hl = self.hyp_lines()
        for i, h in enumerate(hl):
            L.append('    ' + h + (' :' if i == len(hl) - 1 else ''))
        if not hl:
            L.append('    :')
        L.append('    ExecStmts (' + D + ') funs V st (GenAst.' + s['body'] + ' ctx program tcq)')
        L.append('      ' + P(self.final.V) + ' ' + P(self.final.st) + ' .normal := by')
        for line in self.g.out:
            L.append('  ' + line)
        L.append('  unfold GenAst.' + s['body'])
        n = len(self.steps)
        for i, (V0, st0, V1, st1, nm) in enumerate(self.steps):
            last = (i == n - 1)
            head = 'exact ' if last else 'refine '
            tail = ' (Step.seqNil (D := ' + D + '))' if last else ' ?_'
            L.append('  ' + head + 'Step.seqCons (D := ' + D + ') (V1 := ' + P(V1) + ') (st1 := ' + P(st1) +
                     ') ' + nm + tail)
        return NL.join(L)

    def post_v(self):
        s = self.spec
        v = self.final.V
        if 'emit_top' in s:
            v = v.replace(s['emit_top'], s['ref_top'])
        return v

    def print_value(self):
        s = self.spec
        ps = self.pre_list()
        pre = ps[0]
        for x in ps[1:]:
            pre = pre + ' ' + AND + NL + '        ' + x
        L = []
        L.append('theorem qArmValue_' + s['name'] + ' {c : ExternalCalls} {g : ExternalGas}')
        L.append('    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)')
        L.append('    (funs : FunEnv (' + D + ')) ' + s.get('binders', ''))
        for (b, prop, name) in s.get('extras', []):
            L.append('    ' + b)
        L.append('    :')
        L.append('    StmtsContract (D := ' + D + ') funs (GenAst.' + s['body'] + ' ctx program tcq)')
        L.append('      (fun V st => ' + pre + ')')
        L.append("      (fun V st V' st' o => o = .normal " + NL + '        ' + AND + " st' = " +
                 P(self.final.st) + NL + '        ' + AND + " V' = " + P(self.post_v()) + ') := by')
        proj = ' '.join(self.projections())
        names = ' '.join([e[2] for e in s.get('extras', [])])
        L.append('  intro V st hpre')
        L.append('  have hrun := qArmRun_' + s['name'] + ' ctx program tcq funs V st ' +
                 s.get('varargs', '') + proj + (' ' + names if names else ''))
        for t in s.get('tie', []):
            L.append('  rw [' + t + '] at hrun')
        L.append('  exact ' + LAng + '_, _, _, hrun, ' + LAng + 'rfl, rfl, rfl' + RAng + RAng)
        return NL.join(L)

    def print_value_all(self):
        s = self.spec
        ps = self.pre_list()
        pre = ps[0]
        for x in ps[1:]:
            pre = pre + ' ' + AND + NL + '        ' + x
        L = []
        L.append('theorem qArmValueAll_' + s['name'] + ' {c : ExternalCalls} {g : ExternalGas}')
        L.append('    (hc : c.Functional) (hg : g.Functional)')
        L.append('    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)')
        L.append('    (funs : FunEnv (' + D + ')) ' + s.get('binders', ''))
        for (b2, prop, name) in s.get('extras', []):
            L.append('    ' + b2)
        L.append('    :')
        L.append('    StmtsContractAll (D := ' + D + ') funs (GenAst.' + s['body'] + ' ctx program tcq)')
        L.append('      (fun V st => ' + pre + ')')
        L.append("      (fun V st V' st' o => o = .normal " + NL + '        ' + AND + " st' = " +
                 P(self.final.st) + NL + '        ' + AND + " V' = " + P(self.post_v()) + ') :=')
        names = ' '.join([e[2] for e in s.get('extras', [])])
        args = 'ctx program tcq funs ' + s.get('varargs', '') + names
        L.append('  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)')
        L.append('    (qArmValue_' + s['name'] + ' ' + args + ')')
        return NL.join(L)

    def emit(self):
        self.run()
        parts = []
        s = self.spec
        if 'tie_lemma' in s:
            nm, bnd, styp, prf = s['tie_lemma']
            parts.append('theorem ' + nm + ' ' + bnd + ' :' + NL + '    ' + styp + ' := by ' + prf)
        parts.append(self.print_run())
        parts.append(self.print_value())
        parts.append(self.print_value_all())
        return (NL + NL).join(parts)

    def lemmas(self):
        return [bi_src(n) for n in sorted(self.g.used) if n in BI and 'at' not in n] + \
               [bi_at_src(n) for n in sorted(self.g.used) if 'at' in n]
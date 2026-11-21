
# /private/tmp/gs2.py
D = "Bridge.Dialect c g"
def q(s): return '"%s"' % s
def ne(a, b): return "(by decide : (%s : Ident) \u2260 %s)" % (q(a), q(b))
def P(s): return "(%s)" % s
def atomic(v): return len(v.split())==1 and not v.startswith("(")
def proj(v): return v + ".toNat" if atomic(v) else "(" + v + ").toNat"

def V(x):  return ('var', x, "(yvar %s)" % q(x))
def L(n):  return ('lit', n, "(ylit %d)" % n)
def TL(n): return ('texpr', n, "(ylit %s)" % n)
def OP(op, args): return ('op', op, list(args),
    "(yop EVM.Op.%s [%s])" % (op, ", ".join(a[-1] for a in args)))
def src(e): return e[-1]

class Layer:
    def __init__(self, kind, name, val):
        self.kind = kind; self.name = name; self.val = val

def render(layers, base):
    s = base
    for L_ in reversed(layers):
        if L_.kind == 'cons':
            s = "(%s, %s) :: %s" % (q(L_.name), L_.val, s)
        else:
            s = "VEnv.set %s %s %s" % (P(s), q(L_.name), L_.val)
    return s

class Gen:
    def __init__(self, funs, base, base_gets, st0, mem):
        self.funs = funs; self.base = base; self.base_gets = base_gets
        self.st0 = st0; self.mem = mem
        self.lines = []; self.n = 0; self.steps = []
        self.memfacts = {st0: "rfl"}
    def fresh(self, p="h"):
        self.n += 1; return "%s%d" % (p, self.n)
    def emit(self, typ, proof, name=None):
        nm = name or self.fresh()
        self.lines.append("  have %s : %s := %s" % (nm, typ, proof))
        return nm
    def envof(self, layers, i):
        return render(layers[i:], self.base)
    def lookup(self, layers, x):
        idx = None
        for i, Ly in enumerate(layers):
            if Ly.name == x: idx = i; break
        if idx is None:
            v, cur = self.base_gets[x]
            for i in range(len(layers) - 1, -1, -1):
                Ly = layers[i]; inner = self.envof(layers, i + 1)
                if Ly.kind == 'cons':
                    cur = "Eq.trans (venvGet_cons_ne %s %s %s %s %s) (%s)" % (
                        P(inner), q(Ly.name), q(x), Ly.val, ne(Ly.name, x), cur)
                else:
                    cur = "(venvGet_set_ne %s %s %s %s %s %s (%s))" % (
                        P(inner), q(Ly.name), q(x), Ly.val, v, ne(Ly.name, x), cur)
            return v, cur
        Ly = layers[idx]
        if Ly.kind == 'cons':
            cur = "venvGet_cons_eq %s %s %s" % (P(self.envof(layers, idx + 1)), q(x), Ly.val)
        else:
            w, pw = self.lookup(layers[idx + 1:], x)
            cur = "venvGet_set_same %s %s %s %s (%s)" % (
                P(self.envof(layers, idx + 1)), q(x), Ly.val, w, pw)
        v = Ly.val
        for i in range(idx - 1, -1, -1):
            Li = layers[i]; inner = self.envof(layers, i + 1)
            if Li.kind == 'cons':
                cur = "Eq.trans (venvGet_cons_ne %s %s %s %s %s) (%s)" % (
                    P(inner), q(Li.name), q(x), Li.val, ne(Li.name, x), cur)
            else:
                cur = "(venvGet_set_ne %s %s %s %s %s %s (%s))" % (
                    P(inner), q(Li.name), q(x), Li.val, v, ne(Li.name, x), cur)
        return v, cur
    def memfact(self, st):
        if st in self.memfacts: return self.memfacts[st]
        raise Exception("no memfact for " + st)
    def ev(self, e, layers, st):
        if e[0] == 'var':
            x = e[1]; envS = P(render(layers, self.base))
            v, prf = self.lookup(layers, x)
            typ = "Step (D := %s) %s %s %s (.expr (yvar %s)) (.eres (.vals [%s] %s))" % (
                D, self.funs, envS, st, q(x), v, st)
            return v, st, self.emit(typ, "Step.var (D := %s) %s" % (D, P(prf)))
        if e[0] == 'texpr':
            n = e[1]; envS = P(render(layers, self.base))
            v = "(BitVec.ofNat 256 %s)" % n
            typ = "Step (D := %s) %s %s %s (.expr (ylit %s)) (.eres (.vals [%s] %s))" % (
                D, self.funs, envS, st, n, v, st)
            proof = "qlit %s %s %s %s" % (self.funs, envS, st, n)
            return v, st, self.emit(typ, proof)
        if e[0] == 'lit':
            n = e[1]; envS = P(render(layers, self.base))
            v = "(BitVec.ofNat 256 %d)" % n
            typ = "Step (D := %s) %s %s %s (.expr (ylit %d)) (.eres (.vals [%s] %s))" % (
                D, self.funs, envS, st, n, v, st)
            proof = "qlit %s %s %s %d" % (self.funs, envS, st, n)
            return v, st, self.emit(typ, proof)
        op = e[1]; args = e[2]; k = len(args); envS = P(render(layers, self.base))
        vals = [None]*k; dnames = [None]*k; ends = [None]*k
        st_cur = st
        for i in range(k - 1, -1, -1):
            v, st_cur, dn = self.ev(args[i], layers, st_cur)
            vals[i] = v; dnames[i] = dn; ends[i] = st_cur
        final_st = st_cur
        prev = self.emit("Step (D := %s) %s %s %s (.args []) (.eres (.vals [] %s))" % (
            D, self.funs, envS, st, st), "Step.argsNil (D := %s)" % D)
        st_after_rest = st
        for i in range(k - 1, -1, -1):
            rest_src = ", ".join(src(a) for a in args[i+1:])
            all_src = src(args[i]) + (", " + rest_src if rest_src else "")
            restvals = ", ".join(vals[i+1:])
            allvals = vals[i] + (", " + ", ".join(vals[i+1:]) if i+1 < k else "")
            typ = "Step (D := %s) %s %s %s (.args [%s]) (.eres (.vals [%s] %s))" % (
                D, self.funs, envS, st, all_src, allvals, ends[i])
            proof = ("Step.argsCons (D := %s) (rest := [%s]) (restvals := [%s]) (st1 := %s) "
                     "(v := %s) (st2 := %s) %s %s") % (
                D, rest_src, restvals, st_after_rest, vals[i], ends[i], prev, dnames[i])
            prev = self.emit(typ, proof)
            st_after_rest = ends[i]
        argsname = prev
        return self.builtin(op, args, vals, envS, st, argsname, final_st)
    def builtin(self, op, args, vals, envS, st0args, argsname, st):
        if op == 'add':
            lemma = "qbi_add %s %s %s" % (st, vals[0], vals[1]); val = "(%s + %s)" % (vals[0], vals[1])
        elif op == 'and':
            lemma = "qbi_and %s %s %s" % (st, vals[0], vals[1]); val = "(%s &&& %s)" % (vals[0], vals[1])
        elif op == 'shr':
            kk = args[0][1]; lemma = "qbi_shr%d %s %s" % (kk, st, vals[1]); val = "(%s >>> %d)" % (vals[1], kk)
        elif op == 'shl':
            kk = args[0][1]; lemma = "QSHL%d %s %s" % (kk, st, vals[1]); val = "(%s <<< %d)" % (vals[1], kk)
        elif op == 'byte':
            kk = args[0][1]; lemma = "qbi_byte%d %s %s" % (kk, st, vals[1])
            val = "((%s >>> %d) &&& 0xff)" % (vals[1], 248 - 8*kk)
        elif op == 'gt':
            lemma = "qbi_gt %s %s %s" % (st, vals[0], vals[1])
            val = "(b2w (decide ((%s).toNat < (%s).toNat)))" % (vals[1], vals[0])
        elif op == 'mulmod':
            lemma = "qbi_mulmod_atFr %s %s %s" % (st, vals[0], vals[1]); val = "(wMulmod %s %s)" % (vals[0], vals[1])
        elif op == 'addmod':
            lemma = "qbi_addmod_atFr %s %s %s" % (st, vals[0], vals[1]); val = "(wAddmod %s %s)" % (vals[0], vals[1])
        elif op == 'mload':
            newst = "(touchMemory %s %s 32)" % (st, proj(vals[0]))
            mf = self.memfact(st)
            self.memfacts[newst] = ("Eq.trans (Midfall.Yul.Word.touchMemory_memory %s %s 32) (%s)" % (st, proj(vals[0]), mf))
            lemma = "qbi_mload_at %s %s %s (%s)" % (st, self.mem, vals[0], mf)
            typ = "Step (D := %s) %s %s %s (.expr %s) (.eres (.vals [(loadWord %s %s) ] %s))" % (
                D, self.funs, envS, st, src(OP('mload', [args[0]])), self.mem, proj(vals[0]), newst)
            nm = self.emit(typ, "Step.builtinOk (D := %s) %s (%s)" % (D, argsname, lemma))
            return "(loadWord %s %s)" % (self.mem, proj(vals[0])), newst, nm
        else:
            raise Exception("op " + op)
        typ = "Step (D := %s) %s %s %s (.expr %s) (.eres (.vals [%s] %s))" % (
            D, self.funs, envS, st0args, src(OP(op, args)), val, st)
        nm = self.emit(typ, "Step.builtinOk (D := %s) %s (%s)" % (D, argsname, lemma))
        return val, st, nm
    def stmts(self, body):
        layers = []; st = self.st0
        steps = []
        for s in body:
            envS = P(render(layers, self.base))
            if s[0] == 'let':
                x = s[1]; e = s[2]
                v, st2, dn = self.ev(e, layers, st)
                typ = "Step (D := %s) %s %s %s (.stmt (ylet %s %s)) (.sres ((%s, %s) :: %s) %s .normal)" % (
                    D, self.funs, envS, st, q(x), src(e), q(x), v, render(layers, self.base), st2)
                nm = self.emit(typ, "Step.letVal (D := %s) %s rfl" % (D, dn))
                layers = [Layer('cons', x, v)] + layers
            else:
                x = s[1]; e = s[2]
                v, st2, dn = self.ev(e, layers, st)
                typ = "Step (D := %s) %s %s %s (.stmt (yset %s %s)) (.sres (VEnv.set %s %s %s) %s .normal)" % (
                    D, self.funs, envS, st, q(x), src(e), envS, q(x), v, st2)
                nm = self.emit(typ, "Step.assignVal (D := %s) (vars := [%s]) (vals := [%s]) %s (by rfl)" % (
                    D, q(x), v, dn))
                layers = [Layer('set', x, v)] + layers
            steps.append((nm, render(layers, self.base), st2))
            self.steps = list(steps)
            st = st2
        out = []
        for i, (nm, envAfter, stAfter) in enumerate(steps):
            if i < len(steps) - 1:
                out.append("  refine Step.seqCons (D := %s) (V1 := %s) (st1 := %s) %s ?_" % (
                    D, envAfter, stAfter, nm))
            else:
                out.append("  exact Step.seqCons (D := %s) (V1 := %s) (st1 := %s) %s (Step.seqNil (D := %s))" % (
                    D, envAfter, stAfter, nm, D))
        return "\n".join(self.lines) + "\n" + "\n".join(out), layers, st
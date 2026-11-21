import re, sys

import os as _os
GENFILE = _os.environ.get("QARMS_GENFILE") or _os.path.join(
    _os.path.dirname(_os.path.abspath(__file__)), "..", "..",
    "Midfall", "Lowering", "GenAstQvm.lean")
D = "Bridge.Dialect c g"

def sv(n):
    return "BitVec.ofNat 256 %s" % n

PUNCT = set('[](),')
SWITCHES = {}

def tokenize(s):
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c in ' \n\t':
            i += 1; continue
        if c == '[' and s.startswith('[]', i):
            out.append('[]'); i += 2; continue
        if c in PUNCT:
            out.append(c); i += 1; continue
        if c == '"':
            j = i + 1
            while s[j] != '"':
                j += 1
            out.append(s[i:j+1]); i = j + 1; continue
        j = i
        while j < len(s) and s[j] not in ' [](),\n\t':
            j += 1
        out.append(s[i:j]); i = j
    return out

class P:
    def __init__(self, toks): self.t = toks; self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        v = self.t[self.i]; self.i += 1
        if x and v != x: raise Exception('expected %r got %r at %d' % (x, v, self.i))
        return v

def L(p):
    """parse a bracketed list (or a single paren-expr) into a python list"""
    t = p.peek()
    if t == '[':
        p.eat('[')
        items = []
        if p.peek() != ']':
            while True:
                items.append(parse_expr(p))
                if p.peek() == ',': p.eat(','); continue
                break
        p.eat(']')
        return items
    if t == '[]':
        p.eat('[]'); return []
    return [parse_expr(p)]

def parse_expr(p):
    t = p.peek()
    if t == '(':
        p.eat('(')
        e = parse_expr(p)
        while p.peek() == ')':
            p.eat(')')
            break
        return e
    if t == '[' or t == '[]':
        return ('list', L(p))
    return parse_node(p)

def parse_node(p):
    t = p.eat()
    if t == 'ylet':
        name = p.eat(); return ('let', name[1:-1], parse_expr(p))
    if t == 'yset':
        name = p.eat(); return ('set', name[1:-1], parse_expr(p))
    if t == 'yexpr':
        return ('expr', parse_expr(p))
    if t == 'yif':
        c = parse_expr(p); return ('if', c, L(p))
    if t == 'yfor':
        init = L(p); cond = parse_expr(p); post = L(p); body = L(p)
        return ('for', init, cond, post, body)
    if t == 'yop':
        op = p.eat().split('.')[-1]; return ('op', op, L(p))
    if t == 'yvar':
        return ('var', p.eat()[1:-1])
    if t == 'ylit':
        return ('lit', p.eat())
    if t == 'ycall':
        nm = p.eat()[1:-1]; return ('call', nm, L(p))
    if t.startswith('SWITCH'):
        w = SWITCHES[int(t[6:])]
        c = parse_expr(P(tokenize(w['scrut'])))
        ents = [parse_case_entry(x) for x in top_split(w['cases'], '++')]
        return ('switch', c, w['cases'].strip(), w['dflt'].strip(), ents)
    raise Exception('unknown node %r (next %r)' % (t, p.peek()))

def balanced(s, start):
    """index of the ) matching the ( at s[start]"""
    d = 0
    for i in range(start, len(s)):
        if s[i] == "(":
            d += 1
        elif s[i] == ")":
            d -= 1
            if d == 0:
                return i
    return -1

def skip_sp(s, i):
    while i < len(s) and s[i] in " \n\t":
        i += 1
    return i

def top_split(s, sep):
    """split s on occurrences of sep that sit at paren depth 0"""
    out, cur, d, i = [], "", 0, 0
    while i < len(s):
        ch = s[i]
        if ch == "(": d += 1
        elif ch == ")": d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(cur); cur = ""; i += len(sep); continue
        cur += ch; i += 1
    out.append(cur)
    return out

def strip_paren(s):
    s = s.strip()
    if s.startswith("(") and balanced(s, 0) == len(s) - 1:
        return s[1:-1]
    return s

def strip_bracket(s):
    s = s.strip()
    d = 0
    for i, ch in enumerate(s):
        if ch == "[": d += 1
        elif ch == "]":
            d -= 1
            if d == 0 and i == len(s) - 1:
                return s[1:-1]
            if d == 0:
                return s[1:i]
    return s

CASE_RE = re.compile(r"^\s*if\s+program\.memUsage\.(\w+)\s+then\s+(.*)\s+else\s*\[\]\s*$", re.S)
LABEL_RE = re.compile(r"^Literal\.number\s+tcq\.mem\.(\w+)$")

def parse_case_entry(part):
    """one (if program.memUsage.X then [(Literal.number tcq.mem.Y, BODY)] else []) group"""
    inner = strip_paren(part)
    m = CASE_RE.match(inner)
    if not m:
        raise Exception("case entry not understood: %r" % inner[:140])
    flag, mid = m.group(1), m.group(2)
    ent = strip_paren(strip_bracket(mid))
    pieces = top_split(ent, ",")
    label = pieces[0].strip()
    body_txt = ",".join(pieces[1:]).strip()
    lm = LABEL_RE.match(label)
    if not lm:
        raise Exception("label not understood: %r" % label)
    return dict(flag=flag, label=lm.group(1), body=L(P(tokenize(body_txt))))

def extract_switches(s):
    """replace every Stmt.switch (c) (cases) (dflt) by a placeholder token"""
    parts, out, i, n = {}, [], 0, 0
    while True:
        j = s.find("Stmt.switch", i)
        if j < 0:
            out.append(s[i:]); break
        out.append(s[i:j])
        a = skip_sp(s, j + len("Stmt.switch"))
        e1 = balanced(s, a)
        b = skip_sp(s, e1 + 1)
        e2 = balanced(s, b)
        cc = skip_sp(s, e2 + 1)
        e3 = balanced(s, cc)
        parts[n] = dict(scrut=s[a + 1:e1], cases=s[b + 1:e2], dflt=s[cc + 1:e3])
        out.append("SWITCH%d" % n)
        n += 1
        i = e3 + 1
    return "".join(out), parts

def arm_body(name):
    src = open(GENFILE).read()
    i = src.find('def %s ' % name)
    assert i >= 0, name
    j = src.find(': Block Op :=', i)
    assert j > 0, name
    k = src.find('\n\n', j)
    body = src[j + len(': Block Op :='):k]
    body, sw = extract_switches(body)
    global SWITCHES
    SWITCHES = sw
    p = P(tokenize(body))
    return L(p)

if __name__ == '__main__':
    for nm in sys.argv[1:]:
        print('=====', nm)
        for s in arm_body(nm):
            print('   ', s)

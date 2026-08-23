#!/usr/bin/env python3
r"""Verify every code excerpt against the artifact it cites.

A specification's excerpts are the part a reader trusts most and checks least.
This script extracts each `lstlisting` whose caption names a source file and a
line range, then checks that every non-elided line of the excerpt occurs in that
range of the real file. Whitespace is normalised (the spec re-indents); `// ...`
marks a deliberate elision and is skipped.
"""
import re, os, sys, difflib

HERE = os.path.dirname(os.path.abspath(__file__))
FIX = os.path.join(HERE, '..', '..', 'fixtures', 'moonlight-wrap')
SPEC = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'Halo2VerifierSpec.tex')

SRC = {name: open(os.path.join(FIX, name)).read().split('\n')
       for name in ('Halo2Verifier.sol', 'Halo2VerifyingKey.sol')}

LST = re.compile(r'\\begin\{lstlisting\}(\[[^\]]*\])?\n(.*?)\\end\{lstlisting\}', re.S)
# caption forms: "Halo2Verifier.sol} lines 836--954" / "lines 1446--1453" / "line 500"
CAP = re.compile(r'(Halo2Verifier\.sol|Halo2VerifyingKey\.sol)[^0-9]{0,40}?'
                 r'lines?\s+(\d+)(?:\s*-{2,3}\s*(\d+))?')
RANGE = re.compile(r'\b(\d{2,4})\s*-{2,3}\s*(\d{2,4})\b')

def norm(l):
    return re.sub(r'\s+', ' ', l).strip()

def main():
    checked = mismatched = uncited = 0
    problems = []
    files = ([os.path.join(SPEC, f) for f in sorted(os.listdir(SPEC)) if f.endswith('.tex')]
             if os.path.isdir(SPEC) else [SPEC])
    for path in files:
        fn = os.path.basename(path)
        text = open(path).read()
        for m in LST.finditer(text):
            opts, body = m.group(1) or '', m.group(2)
            caps = list(CAP.finditer(opts))
            # A caption may cite several ranges ("lines A--B ... and C--D"); a
            # bare "lines C--D" after the first cite inherits the file name.
            extra = list(RANGE.finditer(opts))
            if not caps:
                uncited += 1
                continue
            name = caps[0].group(1)
            a = int(caps[0].group(2))
            b = int(caps[0].group(3)) if caps[0].group(3) else a
            window = set()
            spans = [(int(c.group(2)), int(c.group(3) or c.group(2))) for c in caps]
            spans += [(int(e.group(1)), int(e.group(2))) for e in extra]
            for lo, hi in spans:
                # widen slightly: captions sometimes name the block, not the exact span
                lo, hi = max(1, lo - 3), min(len(SRC[name]), hi + 3)
                window |= {norm(l) for l in SRC[name][lo - 1:hi] if norm(l)}
            checked += 1
            bad = []
            for line in body.split('\n'):
                n = norm(line)
                if (not n or n.startswith('// ...') or 'elided' in n
                        or n in ('...', '// ---')):
                    continue
                if n not in window:
                    bad.append(n)
            if bad:
                mismatched += 1
                problems.append((fn, name, a, b, bad[:4], len(bad)))
    print(f"excerpts with a cited range: {checked}")
    print(f"excerpts without a cited file+range (skipped): {uncited}")
    print(f"excerpts containing a line not found in the cited range: {mismatched}")
    for fn, name, a, b, bad, n in problems[:30]:
        print(f"\n-- {fn}: {name} lines {a}--{b} ({n} unmatched)")
        for l in bad:
            print(f"     {l[:110]}")
    return 1 if mismatched else 0

sys.exit(main())

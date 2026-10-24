#!/usr/bin/env python3
"""Canonicalise Solidity/Yul source for generator comparison (D-P13 companion).

D-P13 made the generator's obligation structural, because raw byte equality is
unachievable: Halo2Verifier.sol carries 1107 comment lines and 119 blanks, and its
indentation comes from Jinja templates rather than from the Yul. Dropping to AST
equality alone would throw away a blunt-but-broad tripwire for nothing. This gets
most of that coverage back at the cost of no proof: strip comments and blanks,
collapse whitespace, compare bytes.

It is STRICTER than YulSemantics.Ast.stmtsBeq, because the AST discards tokens this
still sees. Use both: this for conformance triage and CI, stmtsBeq for the statement
of record in the theorems.

Usage:
  normalise_sol.py FILE          write canonical form to stdout
  normalise_sol.py A B           exit 0 iff canonical forms are equal
"""
import re
import sys


def normalise(src: str) -> str:
    out = []
    i, n = 0, len(src)
    in_str = None
    while i < n:
        c = src[i]
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(src[i + 1])
                i += 2
                continue
            if c == in_str:
                in_str = None
            i += 1
            continue
        if c in ('"', "'"):
            in_str = c
            out.append(c)
            i += 1
            continue
        if src.startswith("//", i):
            j = src.find(chr(10), i)
            i = n if j < 0 else j
            continue
        if src.startswith("/*", i):
            j = src.find("*/", i + 2)
            i = n if j < 0 else j + 2
            continue
        out.append(c)
        i += 1
    lines = []
    for line in "".join(out).split(chr(10)):
        line = re.sub(r"\s+", " ", line).strip()
        if line:
            lines.append(line)
    return chr(10).join(lines) + chr(10)


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    a = open(sys.argv[1]).read()
    if len(sys.argv) == 2:
        sys.stdout.write(normalise(a))
        return 0
    b = open(sys.argv[2]).read()
    na, nb = normalise(a), normalise(b)
    if na == nb:
        print("EQUAL: canonical forms match (%d lines)" % na.count(chr(10)))
        return 0
    la, lb = na.split(chr(10)), nb.split(chr(10))
    print("DIFFER: %d vs %d canonical lines" % (len(la), len(lb)))
    for k in range(max(len(la), len(lb))):
        x = la[k] if k < len(la) else "<eof>"
        y = lb[k] if k < len(lb) else "<eof>"
        if x != y:
            print("  first difference at canonical line %d:" % (k + 1))
            print("    A: %r" % x[:110])
            print("    B: %r" % y[:110])
            break
    return 1


if __name__ == "__main__":
    sys.exit(main())

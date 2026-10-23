#!/usr/bin/env python3
"""lean_grep.py PATTERN FILE...

Print "path:line" for every file whose *code* (comments removed) contains PATTERN.

The sorry register and the native_decide confinement gate both need to tell a
real occurrence from one that only appears in prose. A plain grep cannot: a
line-comment filter misses occurrences inside a /-- doc string -/ whose marker is
on another line, and that produced both a false sorry and a false native_decide
hit on the first try. So we strip comments properly: line comments, nested block
comments, and string literals (which may contain "--").

Line numbers are preserved: a stripped line yields the empty string.
"""
import re
import sys


def code_only(text: str) -> str:
    """Return text with every comment replaced by spaces (newlines kept)."""
    out = []
    i, n = 0, len(text)
    depth = 0  # nesting depth of block comments
    in_str = False
    in_char = False
    while i < n:
        c = text[i]
        if in_str:
            out.append(c)
            if c == "\\":
                out.append(text[i + 1] if i + 1 < n else "")
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if in_char:
            out.append(c)
            if c == "'":
                in_char = False
            i += 1
            continue
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append(c if c == "\n" else " ")
            i += 1
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if c == "'":
            in_char = True
            out.append(c)
            i += 1
            continue
        if text.startswith("/--", i):
            depth = 1
            out.append("   ")
            i += 3
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        out.append(c)
        i += 1
    return "".join(out)


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    pat = re.compile(sys.argv[1])
    for path in sys.argv[2:]:
        try:
            with open(path, encoding="utf-8") as fh:
                src = fh.read()
        except OSError:
            continue
        for lineno, line in enumerate(code_only(src).split("\n"), start=1):
            if pat.search(line):
                print(f"{path}:{lineno}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

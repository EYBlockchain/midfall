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

WHAT THIS SCANNER CANNOT DO, AND WHY THE GATES EXEMPT ONE FILE BY NAME. A string literal is kept
as code text (it must be tracked, or a "--" inside a string would open a phantom comment), so a
token that appears only inside a message string reads as a use of it. No regex fixes that; it is
why the sorry register and the native_decide gate now read the ENVIRONMENT (scripts/Report.lean).
While the text scan is kept as a cross-check, ONE FILE IS EXEMPT BY NAME: Midfall/Tools/Done.lean
is the tool that implements both rules and so carries the tokens `sorry` (in the messages it
prints) and `native_decide` (in the axiom-name shape it matches) as DATA - 1 and 9 occurrences.
The exemption is a filename, not a directory, so a new tool that needs it must say so where it is
granted: scripts/sorries.sh and scripts/checks.sh.

THE PRIME BUG P-CODECLAWS FIXED (docs/REVIEW.md R-66, last item). The old stripper tested
for a char literal (') BEFORE it tested for a line comment (--), and it entered a char
state on ANY quote. Lean identifiers may contain primes - obs', hshell', \u03bb' - so the
trailing prime of an identifier at block-comment depth zero opened a PHANTOM char literal,
and every line after it stopped being comment-stripped: a /-- doc string -/ below such a
proof was scanned as code. P-LOWEQ's first regenerated SORRY.md listed two FALSE proof
holes sitting in a docstring three lines below a proof, with the build green, and the only
reason the register is correct today is that that package avoided primed identifiers.

THE FIX, THREE PARTS. (1) A line comment is tested before a quote, so '--' wins wherever
both could start. (2) A quote opens a char literal only if a WELL-FORMED one matches at
that position - one character, or one backslash escape, between the quotes. A prime is
then ordinary code text and opens nothing, which is lexically correct: in Lean 'f'a'' is
one identifier, not a function applied to a char. (3) Char literals are emitted as code
rather than blanked, because the state existed to stop a quote inside a char literal from
opening a phantom STRING, and that is still achieved: the literal is consumed atomically.
A char literal cannot hold '--' or a sorry, so keeping its text costs nothing.
"""
import re
import sys

# A well-formed Lean char literal: 'c', '\\\'' , '\\n', ... . '\\x41' and '\\u{...}' do not
# match; they are then treated as ordinary text, which is harmless because they contain no
# comment marker and no quote that could open a string.
CHARLIT = re.compile(r"'(?:\\.|[^'\\])'")


def code_only(text: str) -> str:
    """Return text with every comment replaced by spaces (newlines kept)."""
    out = []
    i, n = 0, len(text)
    depth = 0  # nesting depth of block comments
    in_str = False
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
        # /-- /-! and bare /- all open a NESTED block comment in Lean 4. The
        # opener used to be tested only for "/--" and only inside the depth>0
        # branch, so a /-! note was never stripped and prose inside it was
        # scanned as code (it reported a false proof hole; see docs/REVIEW.md).
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth:
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
        # THE ORDERING FIX (R-66): a line comment is tested BEFORE any quote handling, so
        # '--' can never be swallowed by a char-literal state that a prime opened.
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if c == "'":
            m = CHARLIT.match(text, i)
            if m:
                # A real char literal: consumed atomically so a quote inside it cannot open
                # a phantom string. Its text is kept - it cannot hold '--' or a proof hole.
                out.append(m.group(0))
                i = m.end()
                continue
            # A prime (Lean identifiers may end in ') or a stray quote: ordinary code text.
            # The old code entered a char state here, which is the phantom.
            out.append(c)
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    pat = re.compile(sys.argv[1])
    rc = 0
    for path in sys.argv[2:]:
        try:
            with open(path, encoding="utf-8") as fh:
                src = fh.read()
        except (OSError, UnicodeDecodeError) as exc:
            # A file that cannot be read was NOT scanned, so its hits are unknown. That is an error,
            # not a silent pass (review J-10): exit 2, which pipefail turns into a red gate.
            print(f"lean_grep: cannot scan {path}: {exc}", file=sys.stderr)
            rc = 2
            continue
        for lineno, line in enumerate(code_only(src).split("\n"), start=1):
            if pat.search(line):
                print(f"{path}:{lineno}")
    return rc


if __name__ == "__main__":
    sys.exit(main())

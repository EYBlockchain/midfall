#!/usr/bin/env python3
"""Gate every known-answer check in the tree.

Each "#eval <expr>  -- expect <value>" line is a gate. Files are evaluated in
place so their own opens, local instances and helper definitions are in scope.
Negative controls are first-class: "-- expect false" passes by returning false.

Hardened after an adversarial review showed this script could pass while a KAT
was broken:

* The expected value used to be a non-space run, so an annotation with trailing
  prose ("-- expect true, and checks.sh asserts it") swallowed the tail into the
  expression and the check became silently UNGATED. pBaseKats_ok was in exactly
  that state, and corrupting pBase - the R-20 bug class - left the gate reporting
  success. Now the whole tail is captured and the first token is the expectation.
* The subprocess exit status was ignored, so a KAT file that does not compile
  could pass. A non-zero exit is now a hard failure for that file.
* Output lines are matched against a narrow set of shapes, so wrapped
  diagnostics cannot be harvested as values, and the count must match exactly:
  a gate that realigns its own expectations is not a gate.
* One bad file used to abort the whole run, hiding every later KAT. Failures
  are now collected and reported together.
"""
import re
import subprocess
import sys
import pathlib

# expression, then an optional "-- expect <value>" plus any prose after it.
# The expectation stops at whitespace OR a comma, so "-- expect true, and ..."
# reads as true and "-- expect [8]" reads as [8]; an expectation value itself must
# not contain a comma.
EVAL = re.compile(
    r"^#eval\s+(?P<expr>.+?)"
    r"(?:\s+--\s*expect\s+(?P<exp>[^\s,]+).*)?\s*$"
)

# only these shapes count as #eval output
VALUE = re.compile(r"^(true|false|-?\d+|\"[^\"]*\"|\[.*\])$")


def gate_lines(text):
    """Return the real `#eval` gate lines of a file.

    A gate must start the line AND be at block-comment depth zero. Lean block
    comments nest (`/--` opens, `-/-` nests, `-/` closes), and prose inside one
    can wrap so that a line begins with `#eval time.` - which the previous
    `startswith` test counted as a gate, producing a bogus "printed N values for
    N+1 #eval lines" failure. Recorded as R-53.
    """
    depth = 0
    out = []
    for line in text.splitlines():
        stripped = line.strip()
        is_gate = depth == 0 and stripped.startswith("#eval ")
        i = 0
        while i < len(line):
            if line.startswith("/-", i) and i + 2 < len(line) and line[i + 2] == "-":
                depth += 1          # `/--` open, or `-/-` nested open
                i += 3
            elif line.startswith("-/", i) and depth > 0:
                depth -= 1
                i += 2
            else:
                i += 1
        if is_gate:
            out.append(stripped)
    return out


def main() -> int:
    root = pathlib.Path("Midfall")
    if not root.is_dir():
        print("kat_gate: run from the formal/ directory", file=sys.stderr)
        return 2

    files = sorted(
        p for p in root.rglob("*.lean")
        if gate_lines(p.read_text(encoding="utf-8"))
    )
    if not files:
        print("kat_gate: no KAT files found - that is itself a failure", file=sys.stderr)
        return 2

    checked = 0
    uncommented = 0
    problems = []

    for path in files:
        specs = []
        for stripped in gate_lines(path.read_text(encoding="utf-8")):
            m = EVAL.match(stripped)
            if m is None:
                problems.append("%s: unparsable #eval line: %r" % (path, stripped[:70]))
                continue
            exp = m.group("exp")
            # An expectation is a single token, but prose may follow it with
            # no separator other than a colon or comma ("-- expect true: g1 is
            # not the identity"). Strip trailing punctuation so the value is
            # 'true' there and '[8]' in '-- expect [8]'.
            if exp is not None:
                exp = exp.rstrip(".,:;")
            specs.append((m.group("expr"), exp))
        if not specs:
            continue

        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            blob = (proc.stdout + proc.stderr).strip().splitlines()
            detail = blob[0] if blob else "no output"
            problems.append("%s: does not elaborate (exit %d): %s"
                            % (path, proc.returncode, detail[:120]))
            continue

        values = [l.strip() for l in proc.stdout.splitlines()
                  if VALUE.match(l.strip())]
        if len(values) != len(specs):
            problems.append("%s: printed %d value(s) for %d #eval line(s)"
                            % (path, len(values), len(specs)))
            continue

        for (expr, exp), actual in zip(specs, values):
            if exp is None:
                uncommented += 1
                continue
            checked += 1
            if actual != exp:
                problems.append("%s: %s expected %r, got %r"
                                % (path, expr[:60], exp, actual))

    if problems:
        print("KAT GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1

    print("ok: %d annotated known-answer checks pass across %d files"
          % (checked, len(files)))
    if uncommented:
        print("note: %d unannotated #eval line(s) are NOT gated; add" % uncommented)
        print("      \"-- expect <value>\" to gate them")
    return 0


if __name__ == "__main__":
    sys.exit(main())

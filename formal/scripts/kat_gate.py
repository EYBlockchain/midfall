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
* THE TOTAL WAS PRINTED AND NEVER ASSERTED (P-GATEINTEG, P-SCHED P6). Deleting a gate
  together with its "#eval ... -- expect ..." line simply made the report say one
  fewer check and exit 0. EXPECTED_KAT_TOTAL and EXPECTED_KAT_FILES pin both numbers
  now, and they are checked statically - before any file is run - so a deleted gate
  reddens in a second. A deliberate change has to move the pin.
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

# P-GATEINTEG (P6): THE TOTAL IS ASSERTED, NOT PRINTED.
#
# WHY. The KAT section used to end at "ok: %d annotated known-answer checks pass
# across %d files" and exit 0 whatever the number said. Deleting a gate therefore went
# unseen: P-SCHED P6 removed a "def X_ok : Bool := ..." together with its
# "#eval X_ok -- expect true" line, and the whole suite stayed green while the printed
# count quietly dropped by one. A count that is reported and never compared is a report
# wearing a gate's clothes - the same defect P-STATGATE found in the axiom probe.
#
# WHY AN EXACT PIN AND NOT A FLOOR. "at least N" would still let the count fall by one
# every package as long as it stayed above the floor, which is how a register rots. An
# exact total means an unexpected drop reddens AND a deliberate change has to move this
# line - so the diff says out loud that a gate was added or removed, which is the whole
# point of a pin. Both numbers are static properties of the tree, computed BEFORE any
# "lake env lean" runs, so a deleted gate reddens in a second instead of eight minutes.
EXPECTED_KAT_TOTAL = 1336
EXPECTED_KAT_FILES = 96

# Only these shapes count as #eval output.
#
# P-TRUNK HARDENING (a defect that cost two packages a gate run each). The bracket arm
# used to harvest ANY stdout line that begins with [ and ends with ], which is exactly
# the shape of a linter hint: Lean prints its fix-it block
#
#   Hint: Replace the deprecated name:
#     [apply] simp [foo]
#
# on the SAME stream as #eval output, so "[apply] simp [foo]" was counted as a fake
# value and checks.sh went rc=1 with "printed 6 value(s) for 5 #eval line(s)" on a
# file lake build accepted. R-53 below is the same class from the other direction
# (prose inside a block comment read as a gate). Two anchors now apply:
#
#   * a real #eval value is the WHOLE line and has nothing after its closing bracket,
#     so a line with ] followed by more text is a diagnostic, not a value;
#   * a line that opens with a bracketed word ([apply], [warning]) is a diagnostic.
#
# A genuine list value ([], [1, 2], ["a"], [pointAndScalar]) satisfies both.
VALUE = re.compile(r"^(true|false|-?\d+|\"[^\"]*\"|\[.*\])$")
DIAG = re.compile(r"^\[[A-Za-z_][A-Za-z0-9_.]*\][ \t]|\][ \t]+\S")


def is_value(line):
    """True if `line` is a #eval result rather than a linter diagnostic."""
    return bool(VALUE.match(line)) and not DIAG.search(line)


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

    # ---- PASS 1: read the tree and collect every gate line, WITHOUT running lean.
    # The total is asserted here, before anything expensive, so a deleted gate is a
    # one-second failure and not an eight-minute one (P-GATEINTEG / P-SCHED P6).
    per_file = []
    annotated = 0
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
            else:
                uncommented += 1
            if exp is not None:
                annotated += 1
            specs.append((m.group("expr"), exp))
        if not specs:
            continue
        per_file.append((path, specs))

    if len(per_file) != EXPECTED_KAT_FILES or annotated != EXPECTED_KAT_TOTAL:
        print("KAT GATE FAILED (total moved):")
        if len(per_file) != EXPECTED_KAT_FILES:
            print("  KAT FILE COUNT MOVED - %d files carry a #eval gate, pinned %d. A file"
                  % (len(per_file), EXPECTED_KAT_FILES))
            print("  whose last gate was deleted has left the suite silently.")
        if annotated != EXPECTED_KAT_TOTAL:
            print("  KAT TOTAL MOVED - %d annotated known-answer checks in the tree, pinned"
                  % annotated)
            print("  %d (%+d). Deleting a gate and its '#eval ... -- expect ...' line is"
                  % (EXPECTED_KAT_TOTAL, annotated - EXPECTED_KAT_TOTAL))
            print("  exactly what this catches (P-SCHED P6): the count used to be printed")
            print("  and never asserted. If the change is deliberate, move EXPECTED_KAT_TOTAL")
            print("  in scripts/kat_gate.py and say why in the commit.")
        return 1
    if problems:
        print("KAT GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1

    # ---- PASS 2: run each file and compare the values it prints.
    for path, specs in per_file:
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            blob = (proc.stdout + proc.stderr).strip().splitlines()
            detail = blob[0] if blob else "no output"
            problems.append("%s: does not elaborate (exit %d): %s"
                            % (path, proc.returncode, detail[:120]))
            continue

        values = [l.strip() for l in proc.stdout.splitlines() if is_value(l.strip())]
        if len(values) != len(specs):
            problems.append("%s: printed %d value(s) for %d #eval line(s)"
                            % (path, len(values), len(specs)))
            continue

        for (expr, exp), actual in zip(specs, values):
            if exp is None:
                continue          # counted in pass 1; nothing to compare against
            checked += 1
            if actual != exp:
                problems.append("%s: %s expected %r, got %r"
                                % (path, expr[:60], exp, actual))

    # Belt and braces: the total was asserted statically, so every annotated gate must
    # also have been COMPARED. A file that failed to elaborate skips its gates, and this
    # is the line that stops such a skip reading as a pass on the remaining ones.
    if checked != annotated:
        problems.append("only %d of the %d annotated gates were compared - a KAT file was"
                        " skipped, which is a failure and not a smaller pass"
                        % (checked, annotated))

    if problems:
        print("KAT GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1

    print("ok: %d annotated known-answer checks pass across %d files (both pinned:"
          " %d and %d in scripts/kat_gate.py)"
          % (checked, len(per_file), EXPECTED_KAT_TOTAL, EXPECTED_KAT_FILES))
    if uncommented:
        print("note: %d unannotated #eval line(s) are NOT gated; add" % uncommented)
        print("      \"-- expect <value>\" to gate them")
    return 0


if __name__ == "__main__":
    sys.exit(main())

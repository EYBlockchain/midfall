#!/usr/bin/env python3
"""Gate every known-answer check in the tree.

Each '#eval <expr>  -- expect <value>' line in Midfall/ is a gate, not
documentation. Before this script, checks.sh asserted six hand-picked booleans,
so the R-30 and R-32 regression tests - written precisely because those bugs
survived sign-off - would not have failed CI if they regressed: a false #eval
prints as an 'info:' line and 'lake build' still exits 0.

Files are evaluated in place so their own opens, local instances and helper
definitions are in scope; harvesting the bare expressions into one file breaks on
the unqualified ones (e.g. 'DualMSM.check dualOk expPrm').

Negative controls are first-class: '-- expect false' is a PASS. That matters -
a verifier KAT that only ever returns true proves nothing, and the exponent
model's dualBad check is exactly the control that shows the decision discriminates.
"""
import re, subprocess, sys, pathlib

EVAL = re.compile(r"^#eval\s+(?P<expr>.+?)\s*(?:--\s*expect\s+(?P<exp>\S+))?\s*$")

def main() -> int:
    root = pathlib.Path("Midfall")
    files = sorted(p for p in root.rglob("*.lean") if any(
        l.startswith("#eval ") for l in p.read_text(encoding="utf-8").splitlines()))
    total = checked = failures = uncommented = 0
    for path in files:
        specs = []
        for line in path.read_text(encoding="utf-8").splitlines():
            m = EVAL.match(line.strip())
            if m:
                specs.append((m.group("expr"), m.group("exp")))
        if not specs:
            continue
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              capture_output=True, text=True)
        got = [l.strip() for l in proc.stdout.splitlines()
               if l.strip() and not l.startswith(("info", "warning", "error", "trace"))]
        # only the value lines count; #eval prints one line per eval
        values = [g for g in got if re.fullmatch(r"[A-Za-z0-9_()+\-\s=#.,]*", g)]
        if len(values) < len(specs):
            print("KAT GATE: %s printed %d values for %d #eval lines"
                  % (path, len(values), len(specs)))
            print(proc.stdout[-800:])
            return 1
        offset = len(values) - len(specs)
        for (expr, exp), actual in zip(specs, values[offset:]):
            total += 1
            if exp is None:
                uncommented += 1
                continue
            checked += 1
            if actual.strip() != exp.strip():
                failures += 1
                print("KAT FAILURE %s:%s  expected %r, got %r"
                      % (path, expr[:60], exp, actual))
    if failures:
        print("KAT GATE: %d/%d annotated checks failed" % (failures, checked))
        return 1
    print("ok: %d annotated known-answer checks pass across %d files "
          "(%d unannotated #evals skipped)" % (checked, len(files), uncommented))
    if uncommented:
        print("note: add '-- expect <value>' to the %d unannotated #eval lines "
              "to gate them too" % uncommented)
    return 0

if __name__ == "__main__":
    sys.exit(main())

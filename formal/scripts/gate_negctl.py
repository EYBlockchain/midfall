#!/usr/bin/env python3
"""Gate self-tests: prove the two hard gates in scripts/checks.sh can fail.

Why this exists. docs/REVIEW.md R-40 states the rule: a gate must be justified by a
perturbation INSIDE its stated scope, not by a control outside it. R-41 records the
first application, to scripts/kat_gate.py, as prose. This script makes that evidence
re-runnable rather than an anecdote, and extends it to
scripts/check_golden_provenance.py.

Each control perturbs a tracked file, runs the gate, records the exit status, then
restores from git and verifies the restore is byte-identical. A control that cannot
change the file is an error, not a pass: a half-applied edit is indistinguishable
from a passing test (R-40, seventh instance of that class).

One control is deliberately inverted in shape: an edit OUTSIDE every pinned slice
must leave the provenance gate GREEN. Without it an always-red gate would pass every
other control while checking nothing.

Usage: python3 scripts/gate_negctl.py [kat|prov|all]   (default all)
The kat half elaborates 29 files standalone, so it takes minutes. The prov half is
pure file parsing and takes seconds.

Quoting note: this file builds Lean string literals with Q = chr(34) instead of
embedding double quotes, so every line here is single-quoted and the constants stay
readable.
"""
import hashlib
import pathlib
import subprocess
import sys

Q = chr(34)
NL = chr(10)
REPO = pathlib.Path(__file__).resolve().parent.parent.parent
FORMAL = REPO / "formal"

KAT_GATE = "scripts/kat_gate.py"
PROV_GATE = "scripts/check_golden_provenance.py"

# Perturbed by the kat controls: small, six annotated KATs, and hexFilter is a
# shared helper, so a defect in it propagates to three gates at once.
KAT_FILE = "formal/Midfall/Generator/Filters.lean"
KAT_LINE = "#eval Midfall.Generator.hexFilter_kats_ok -- expect true"
HEX_PAD = "  if value.length % 2 == 1 then " + Q + "0x0" + Q + " ++ value else " + Q + "0x" + Q + " ++ value"

SOL = "proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol"
YG = "formal/Midfall/Generator/YulGolden.lean"
TM = "formal/Midfall/Generator/Templates.lean"
PIN = "mstore8 ( runtime , 254 )"
ANCHOR = "(" + Q + "partials/verifier/Lagrange.yul" + Q + ", 1509)"


def sha(rel):
    return hashlib.sha256((REPO / rel).read_bytes()).hexdigest()


def run_gate(gate):
    r = subprocess.run([sys.executable, gate], cwd=FORMAL,
                       capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip().splitlines()
    bad = [l for l in out if "FAIL" in l]
    detail = bad[0] if bad else (out[-1] if out else "")
    return r.returncode, detail


def restore(rel):
    subprocess.run(["git", "checkout", "--", rel], cwd=REPO, check=True)


def control(name, gate, rel, mutate, want_red=True):
    before = sha(rel)
    path = REPO / rel
    new = mutate(path.read_text())
    if new == path.read_text():
        raise AssertionError("control " + name + " made no edit, so it proves nothing")
    path.write_text(new)
    try:
        if sha(rel) == before:
            raise AssertionError("control " + name + " wrote identical bytes back")
        rc, detail = run_gate(gate)
    finally:
        restore(rel)
    red = rc != 0
    behaved = red if want_red else not red
    verdict = "RED" if red else "GREEN"
    want = "RED" if want_red else "GREEN"
    tag = "OK" if behaved else "*** GATE MISBEHAVED ***"
    print("  %-44s exit=%d %-5s want %-5s %s" % (name, rc, verdict, want, tag))
    print("       " + detail[:140])
    if sha(rel) != before:
        print("       *** RESTORE FAILED: " + rel + " is not byte-identical ***")
        behaved = False
    return behaved


def kat_controls():
    def flip(t):
        assert t.count(KAT_LINE) == 1
        return t.replace(KAT_LINE, KAT_LINE.replace("expect true", "expect false"))

    def prose(t):
        # The historical defect: the expectation was a non-space run, so trailing
        # prose was absorbed into the EXPRESSION and the line silently stopped
        # being a gate at all.
        assert t.count(KAT_LINE) == 1
        return t.replace(KAT_LINE, KAT_LINE + ", and this prose used to swallow the tail")

    def nobuild(t):
        assert t.count(KAT_LINE) == 1
        return t.replace(KAT_LINE, "#eval thisIsNotDefined_xyz")

    def impl(t):
        # The control that matters: one token changed in hexFilter itself, inside
        # the scope the gate claims to cover, not in its annotation.
        assert t.count(HEX_PAD) == 1
        return t.replace(HEX_PAD, HEX_PAD.replace(Q + "0x0" + Q, Q + "0x" + Q))

    return [
        control("kat A  flipped annotation", KAT_GATE, KAT_FILE, flip),
        control("kat B  prose glued to expectation", KAT_GATE, KAT_FILE, prose),
        control("kat C  file does not elaborate", KAT_GATE, KAT_FILE, nobuild),
        control("kat D  implementation perturbation", KAT_GATE, KAT_FILE, impl),
    ]


def prov_controls():
    def artifact(t):
        ls = t.split(NL)
        i = 2750  # inside the pcsBasis slice 2744-2773
        old = ls[i]
        ls[i] = old.replace("rot_pt_1", "rot_pt_9", 1)
        if ls[i] == old:
            raise AssertionError("no rot_pt_1 on line 2751: " + repr(old))
        return NL.join(ls)

    def pin(t):
        assert t.count(PIN) == 1, "pin anchor not unique"
        return t.replace(PIN, "mstore8 ( runtime , 253 )")

    def anchor(t):
        assert t.count(ANCHOR) == 1, "anchor not unique"
        return t.replace(ANCHOR, ANCHOR.replace("1509", "1516"))

    def outside(t):
        # Must NOT redden: the gate is scoped to the pinned slices, it does not
        # fire on any change to the artifact.
        ls = t.split(NL)
        ls[5] = ls[5] + " // inert comment outside every pinned slice"
        return NL.join(ls)

    return [
        control("prov 1 artifact token inside a slice", PROV_GATE, SOL, artifact),
        control("prov 2 pinned string edited", PROV_GATE, YG, pin),
        control("prov 3 hand-typed fixtureAnchor moved", PROV_GATE, TM, anchor),
        control("prov 4 edit outside every slice", PROV_GATE, SOL, outside,
                want_red=False),
    ]


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which == "kat":
        res = kat_controls()
    elif which == "prov":
        res = prov_controls()
    else:
        res = kat_controls() + prov_controls()
    print("")
    print("gate self-tests passed: %d/%d" % (sum(1 for x in res if x), len(res)))
    return 0 if all(res) else 1


if __name__ == "__main__":
    sys.exit(main())

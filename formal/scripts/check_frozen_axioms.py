#!/usr/bin/env python3
"""Axiom gate for the frozen normative file, Midfall/Statements.lean.

WHY THIS IS A GATE AND NOT A PRINT. checks.sh used to end with

    lake env lean /tmp/midfall-ax.lean

which prints three axiom sets and exits 0 whatever they say. It printed sorryAx three
times and stayed green, so it was a report wearing a gate's clothes - the same class of
defect D-P31 records for the memory line, except that here the thing being reported was
the trusted base of the whole project. P-REPIN found this as the second gap after the
missing semantic coverage of Statements.lean.

THE RULE, stated precisely, because the obvious rule is wrong.

  sorryAx is EXPECTED here. These are SPEC STATEMENTS, not proofs: D-P27 kept all three
  frozen texts as 'sorry' deliberately, and the authorising decision is explicit that
  filling contractRef_noAcc - which repair3_rederived shows IS derivable - is out of
  scope because the spec surface holds statements, not proofs. A gate that failed on
  sorryAx would be red on every honest version of this file, which is worse than no
  gate: it teaches the reader to ignore it.

  So the rule is about SHAPE, not presence:

  1. Every top-level declaration in the frozen file is probed - the list is read from the
     file, not hard-coded, so a fourth statement cannot arrive unprobed. The old print
     named three declarations by hand; a statement added to the normative file would have
     been invisible to it.
  2. Each of the three PINNED statements must depend on EXACTLY the expected four: propext,
     sorryAx, Classical.choice, Quot.sound. Not 'a subset', not 'does not contain something
     worse'. An exact set is the only form that also catches a statement LOSING an axiom,
     which is what happens when someone fills a 'sorry' or re-derives a theorem here - both
     of which need a re-pin, a SORRY.md change and a human decision, and therefore must not
     be silent. A fourth declaration that is not pinned gets the weaker but still real rule:
     inside the four, and carrying sorryAx. It has no business being forced to depend on
     propext merely because the other three do, and a rule with that absurd consequence
     would be broken on purpose the first time someone added a statement here.
  3. Two axioms are named and rejected specifically, because they are the two this
     repository has actually been burned by: native_decide and Lean.ofReduceBool.
     native_decide moves a proof from the kernel-checked path to the compiler-trusted
     one; the confinement gate in checks.sh bans the TACTIC outside Midfall/Instances/,
     and this catches the AXIOM arriving by any other route - a dependency that started
     using it, a vendored lemma, or a hand-written 'axiom Lean.ofReduceBool'.
  4. A declaration that fails to elaborate, or that the probe did not report, is a
     failure. Silence is not a pass.

Usage:  python3 scripts/check_frozen_axioms.py [--root DIR] [--print-only]
        python3 scripts/check_frozen_axioms.py --input FILE   # parse captured output
"""
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_duplicate_facts import strip_comments

EXPECTED = {"propext", "sorryAx", "Classical.choice", "Quot.sound"}
# Matched as SUBSTRINGS, not keys, because Lean mangles a generated axiom after the
# declaration that produced it: a native_decide at Midfall.Statements.foo reports the axiom
# as 'Midfall.Statements.foo._native.native_decide.ax_1_1', never as 'Lean.ofReduceBool'.
# P-STATGATE found that by demonstration - the first version of this gate printed UNEXPECTED
# AXIOM and named the mangled string, which is a true report but not the point: the reader
# has to be told WHICH trusted-base line was crossed.
BANNED = [
    ("native_decide", "the native evaluator was trusted here (checks.sh confines the tactic "
                      "to Midfall/Instances/; this catches the axiom arriving by any route)"),
    ("ofReduceBool", "the Bool-to-Prop bridge native_decide needs, i.e. the kernel no longer "
                     "checked this step"),
]
STATEMENTS_FILE = "Midfall/Statements.lean"
MODULE = "Midfall.Statements"
# The three statements D-P27 repaired and this gate pins text for. Their axiom set is part of
# the pin and must stay EXACTLY the four. Any other declaration in the frozen file must stay
# INSIDE the four and must still carry sorryAx - it has no business depending on propext just
# because the other three do, and a rule that demanded that would be broken on purpose.
PINNED = {MODULE + ".verifyNative_iff_msgs", MODULE + ".verifyMsgs_iff_spec",
          MODULE + ".contractRef_noAcc"}
REPAIR_FILE = "Midfall/Instances/StatementsRepair.lean"
REPAIR_MODULE = "Midfall.Instances.StatementsRepair"
# The D-P23 halves the frozen doc strings cite: three satisfiability witnesses and three
# retained refutations, plus the exhibit that says the new law is a real restriction. These
# are PROOFS, not spec statements, so the rule INVERTS - sorryAx must be ABSENT. The
# fingerprint gate pins their TEXT, and a witness whose proof had been replaced by a hole
# would keep every text pin green while the D-P23 obligation quietly went unmet: the repair
# would still be written down and would no longer be demonstrated. native_decide axioms are
# EXPECTED here (this is the one directory the confinement gate allows them in), so only
# sorryAx is asserted about them.
# Short names only: the qualified name is resolved by reading the namespace out of the file
# (StatementsRepair.lean lives in Midfall.Instances, NOT Midfall.Instances.StatementsRepair -
# a Lean namespace is not a file, and the first version of this list got that wrong).
REPAIR_NO_SORRY = ["repair1_satisfiable", "repair1_old_false_at_degEnv",
                   "repair1_old_universal_refuted", "repair2_old_refuted",
                   "repair2_new_shape_inhabited", "repair3_rederived",
                   "repair3_hash_is_not_forced", "repair1_law_is_not_free"]

DECL = re.compile(r"^(?:private\s+|protected\s+)?(?:abstract\s+)?"
                  r"(theorem|lemma|def|abbrev|example)\b\s*([A-Za-z_][A-Za-z0-9_.']*)?")
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)")
# Lean WRAPS a long axiom list across lines with a leading space per continuation - which
# is exactly what a native_decide witness produces, since the generated axiom names are
# qualified per declaration. A line-anchored parser silently dropped every wrapped entry and
# the gate reported 'NO AXIOM REPORT' for five witnesses that were printed in full. Parsed
# across lines with DOTALL instead.
AXIOMS = re.compile(r"'(.+?)' depends on axioms: \[(.*?)\]", re.S)
NOAXIOMS = re.compile(r"'(.+?)' does not depend on any axioms")


def frozen_declarations(path):
    """Every top-level declaration in the frozen file, fully qualified. Comments are
    stripped first: a doc string that begins with the word 'theorem' has been mistaken
    for a declaration before (REVIEW.md's note on Accumulator.lean:1126)."""
    out, ns = [], []
    for ln in strip_comments(path.read_text(encoding="utf-8")).splitlines():
        if not ln or ln[0] in " \t":
            continue
        m = NAMESPACE.match(ln)
        if m:
            ns.append(m.group(1))
            continue
        m = END.match(ln)
        if m and ns and ns[-1].split(".")[-1] == m.group(1):
            ns.pop()
            continue
        m = DECL.match(ln)
        if m is None or m.group(2) is None:
            continue
        if m.group(1) == "example" or m.group(2) in ns:
            continue
        out.append(".".join(ns + [m.group(2)]))
    return out


def repair_targets(root):
    """The D-P23 witnesses, qualified by the namespace the file actually declares them in."""
    p = root / REPAIR_FILE
    if not p.exists():
        return []
    have = frozen_declarations(p)
    return [d for d in have if d.split(".")[-1] in set(REPAIR_NO_SORRY)]


def parse(text):
    """full name -> set of axioms, read from #print axioms output, wrapped lines included."""
    got = {m.group(1): {a.strip() for a in m.group(2).split(",") if a.strip()}
           for m in AXIOMS.finditer(text)}
    for m in NOAXIOMS.finditer(text):
        got.setdefault(m.group(1), set())
    return got


def main():
    argv = sys.argv[1:]
    root = Path(__file__).resolve().parent.parent
    if "--root" in argv:
        root = Path(argv[argv.index("--root") + 1]).resolve()
    st = root / STATEMENTS_FILE
    if not st.exists():
        print("check_frozen_axioms: no such file %s" % st, file=sys.stderr)
        return 2
    decls = frozen_declarations(st)
    if not decls:
        print("check_frozen_axioms: NO DECLARATIONS FOUND in %s - the probe would be "
              "vacuous" % st, file=sys.stderr)
        return 1
    problems = []
    if "--input" in argv:
        text = Path(argv[argv.index("--input") + 1]).read_text(encoding="utf-8")
    else:
        probe = Path("/tmp/midfall-ax.lean")
        # every import first: Lean rejects an import that follows a command
        imports = ["import %s\n" % MODULE]
        prints = ["#print axioms %s\n" % d for d in decls]
        if (root / REPAIR_FILE).exists():
            imports.append("import %s\n" % REPAIR_MODULE)
            prints += ["#print axioms %s\n" % d for d in repair_targets(root)]
        probe.write_text("".join(imports) + "".join(prints), encoding="utf-8")
        r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root,
                           capture_output=True, text=True)
        text = r.stdout + r.stderr
        if r.returncode != 0:
            problems.append("the probe itself failed (lake env lean exit %d):\n%s"
                            % (r.returncode, text.strip()[:2000]))
    if "--print-only" in argv:
        print(text.strip())
        return 0
    got = parse(text)
    for d in decls:
        if d not in got:
            problems.append("%s: NO AXIOM REPORT - the declaration did not elaborate or "
                            "was not probed; silence is not a pass" % d)
            continue
        ax = got[d]
        for a in sorted(ax - EXPECTED):
            why = next((w for key, w in BANNED if key in a),
                       "the axiom set is no longer the pinned four")
            problems.append("%s: UNEXPECTED AXIOM %s - %s" % (d, a, why))
        if "sorryAx" not in ax:
            problems.append("%s: sorryAx GONE - this frozen statement is no longer a "
                            "registered hole. The spec surface holds statements, not "
                            "proofs: filling it needs a re-pin, a SORRY.md change, and "
                            "this gate's EXPECTED set moved with a reason." % d)
        if d in PINNED:
            for a in sorted(EXPECTED - ax - {"sorryAx"}):
                problems.append("%s: AXIOM %s GONE - this is a PINNED frozen statement, so "
                                "its dependency shape is part of the pin; the set must stay "
                                "exactly %s" % (d, a, sorted(EXPECTED)))
    targets = repair_targets(root)
    if not (root / REPAIR_FILE).exists():
        problems.append("%s is missing, so none of the %d D-P23 witnesses the frozen file "
                        "cites can be probed" % (REPAIR_FILE, len(REPAIR_NO_SORRY)))
    for n in REPAIR_NO_SORRY:
        if not any(t.split(".")[-1] == n for t in targets):
            problems.append("%s: WITNESS NOT FOUND in %s - the frozen doc string cites it "
                            "and it is no longer a declaration of that file"
                            % (n, REPAIR_FILE))
    for d in targets:
        if d not in got:
            problems.append("%s: NO AXIOM REPORT - the witness is gone or does not "
                            "elaborate; silence is not a pass" % d)
        elif "sorryAx" in got[d]:
            problems.append("%s: D-P23 WITNESS IS A HOLE - this carries sorryAx, so the "
                            "satisfiability or refutation the frozen doc string cites is "
                            "asserted and not demonstrated (D-P23 wants both halves PROVED)"
                            % d)
    if problems:
        print("FROZEN STATEMENT AXIOMS BROKEN (%d):" % len(problems))
        for pr in problems:
            print("  " + pr)
        print("  expected exactly %s per frozen declaration, %d declarations probed"
              % (sorted(EXPECTED), len(decls)))
        return 1
    print("ok: %d frozen statements, each depending on exactly %s - no native_decide, "
          "no Lean.ofReduceBool, sorryAx present as expected for spec statements; and %d "
          "D-P23 witnesses carrying no sorryAx"
          % (len(decls), ", ".join(sorted(EXPECTED)), len(targets)))
    return 0


if __name__ == "__main__":
    sys.exit(main())

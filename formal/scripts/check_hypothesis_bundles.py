#!/usr/bin/env python3
"""Hypothesis-bundle gate: every multi-hypothesis headline conjunction is either
JOINTLY exhibited or has a named gap saying which conjunct blocks it.

WHY (docs/REVIEW.md R-60 S1). The headline fields of LoweringCorrect take several
hypotheses at once - a SupportedS, a DeploymentW, an import check, a run of the imported
object - and the repair round claimed the IR hypothesis was inhabited because
Instances/ImportedIR.lean exhibits a committed RunContractIR. It did. What nobody
checked was the CONJUNCTION: the same fields also take S.irCheck ir = true, and the
fixture's check hard-coded a runtime naming convention instead of reading
Surface.runtimeName, so it was false of exactly the object the run was about. Each half
was inhabited and the bundle was empty, and gate 6 - which checks RunContractIR alone -
could not see it. A hypothesis bundle can be individually inhabited and jointly empty.

WHAT THIS GATE CHECKS.

  1. DISCOVERY. Every field of LoweringCorrect whose statement takes two or more
     top-level hypotheses, and the headline theorem lowering_equivalence, must appear in
     the registry below. A new multi-hypothesis field with no registration is a failure:
     that is how a bundle joins the tree without anyone ever asking whether it is
     inhabited.
  2. EXHIBIT. A registered exhibit is the name of a Lean declaration in
     Midfall/Instances/ObligationsGates.lean whose statement mentions EVERY token listed
     for it, in ONE declaration. Two separate half-exhibits do not satisfy the gate -
     that is precisely the shape that hid S1.
  3. GAP. A conjunct that is not jointly exhibited must be covered by a named gap
     declaration in the same file whose body names the blocker. A gap is honest only if
     it can go stale: if the blocker token disappears or the def is deleted, the gate
     reddens.
  4. NO DRIFT. Every token the registry lists for a field must actually occur in that
     field's statement, so a registry cannot keep certifying a bundle that has been
     rewritten.

Like the other two text gates this is a STRUCTURE gate, not a meaning check: it proves
that an exhibit exists and names the right conjuncts, not that the exhibit is the right
theorem. Only a proof is a semantics check.

Usage:  python3 scripts/check_hypothesis_bundles.py [--root DIR]
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_duplicate_facts import (ARROW, definitions, mentions, split_top,
                                   strip_comments, structures)

OB = "Midfall/Lowering/Obligations.lean"
GATES = "Midfall/Instances/ObligationsGates.lean"

# The registry. "exhibit" is (declaration, tokens it must mention); "gaps" is a list of
# (declaration, tokens it must name as the blocker).
REGISTRY = [
    {
        "field": "ir_refines",
        "exhibit": ("bundle_irLeg", ["irCheck ir = true", "RunContractIR"]),
        "gaps": [],
    },
    {
        "field": "verifier_sound",
        "exhibit": ("bundle_deployment", ["SupportedS", "DeploymentW"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"]),
                 ("gap_envAgrees_unexhibited", ["EnvAgrees"]),
                 ("gap_runLeg_unexhibited", ["RunVerifier"])],
    },
    {
        "field": "verifier_complete",
        "exhibit": ("bundle_deployment", ["SupportedS", "DeploymentW"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"]),
                 ("gap_envAgrees_unexhibited", ["EnvAgrees"]),
                 ("gap_runLeg_unexhibited", ["RunShell"])],
    },
    {
        "field": "only_two_outcomes",
        "exhibit": ("bundle_deployment", ["SupportedS", "DeploymentW"]),
        "gaps": [("gap_envAgrees_unexhibited", ["EnvAgrees"]),
                 ("gap_runLeg_unexhibited", ["RunShell"])],
    },
    {
        "field": "end_to_end_noAcc",
        "exhibit": ("bundle_headlineCore",
                    ["SupportedS", "DeploymentW", "irCheck ir = true",
                     "RunContractIR"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"]),
                 ("gap_envAgrees_unexhibited", ["EnvAgrees"])],
    },
    {
        "field": "qvm_validated_noBoundsFault",
        "exhibit": None,
        "gaps": [("gap_qvmField_surface_free", ["LoweringPlan"])],
    },
    {
        "field": "lowering_equivalence",
        "kind": "theorem",
        "exhibit": ("bundle_headlineCore",
                    ["SupportedS", "DeploymentW", "irCheck ir = true",
                     "RunContractIR"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"]),
                 ("gap_envAgrees_unexhibited", ["EnvAgrees"])],
    },
]


def field_statement(text, field):
    """The statement of a LoweringCorrect field or a top-level theorem, comments gone."""
    lines = text.splitlines()
    for i, ln in enumerate(lines):
        s = ln.strip()
        if s.startswith(field + " :") or s.startswith("theorem " + field + " ") \
                or s.startswith("theorem " + field + "("):
            indent = len(ln) - len(ln.lstrip())
            buf = [ln]
            for j in range(i + 1, len(lines)):
                nxt = lines[j]
                if nxt.strip():
                    cur = len(nxt) - len(nxt.lstrip())
                    if cur <= indent and not nxt.startswith(" "):
                        break
                    if cur <= indent and indent > 0:
                        break
                buf.append(nxt)
            # bracket-aware: a binder can contain the assignment arrow, as in
            # "(Gt := Gt)" with a subscript, which is a type ascription inside a forall
            # and not the end of the statement, so the cut has to respect brackets.
            return split_top(" ".join(x.strip() for x in buf), [":="])[0].strip()
    return ""


def hypothesis_count(stmt):
    """Top-level arrows in a statement: the number of hypotheses it takes. Both the
    unicode arrow and its ASCII spelling count, so a perturbation cannot dodge the
    discovery rule by changing how the arrow is written."""
    body = stmt.split(":", 1)[-1] if ":" in stmt else stmt
    return max(0, len(split_top(body, [ARROW, "->"])) - 1)


def check(root):
    def stripped(rel):
        p = root / rel
        return strip_comments(p.read_text(encoding="utf-8")) if p.exists() else None

    ob = stripped(OB)
    if ob is None:
        return ["missing file: " + OB]
    gates = stripped(GATES)
    if gates is None:
        return ["missing file: " + GATES]
    gdefs = definitions(gates)
    problems = []

    # 1. DISCOVERY: every multi-hypothesis field of LoweringCorrect is registered
    registered = {e["field"] for e in REGISTRY}
    structs = structures(ob)
    if "LoweringCorrect" not in structs:
        problems.append("structure LoweringCorrect not found in " + OB)
    else:
        for field, (line, text) in sorted(structs["LoweringCorrect"].items()):
            n = hypothesis_count(text)
            if n >= 2 and field not in registered:
                problems.append(
                    "UNREGISTERED BUNDLE - LoweringCorrect.%s takes %d hypotheses and "
                    "appears in neither an exhibit nor a gap; individually inhabited "
                    "hypotheses can still be jointly empty (R-60 S1)" % (field, n))
            if n < 2 and field in registered:
                problems.append("registry is stale: %s no longer takes two hypotheses"
                                % field)
    for entry in REGISTRY:
        field = entry["field"]
        stmt = field_statement(ob, field)
        if not stmt:
            problems.append("registry names %s, which is not a field of Obligations.lean"
                            % field)
            continue
        tokens = []
        if entry.get("exhibit"):
            tokens += entry["exhibit"][1]
        for _, ts in entry.get("gaps", []):
            tokens += ts
        # 4. NO DRIFT
        for t in tokens:
            if t not in stmt:
                problems.append("%s: registry token %r no longer occurs in the field "
                                "statement - the bundle was rewritten and the "
                                "registration is stale" % (field, t))
        # 2. EXHIBIT
        ex = entry.get("exhibit")
        if ex:
            dname, toks = ex
            body = gdefs.get(dname)
            if body is None:
                problems.append("%s: JOINT EXHIBIT MISSING - %s is not declared in %s"
                                % (field, dname, GATES))
                continue
            missing = [t for t in toks if not mentions(body, t)]
            if missing:
                problems.append("%s: EXHIBIT IS NOT JOINT - %s never mentions %s, so the "
                                "bundle is certified by halves and not by one statement "
                                "(R-60 S1)"
                                % (field, dname, ", ".join(repr(m) for m in missing)))
        elif not entry.get("gaps"):
            problems.append("%s: registered with neither an exhibit nor a gap" % field)
        # 3. GAPS
        for dname, toks in entry.get("gaps", []):
            body = gdefs.get(dname)
            if body is None:
                problems.append("%s: NAMED GAP MISSING - %s is not declared in %s, so "
                                "this conjunct is unexhibited and undocumented"
                                % (field, dname, GATES))
                continue
            missing = [t for t in toks if t not in body]
            if missing:
                problems.append("%s: GAP BLOCKER STALE - %s no longer names %s"
                                % (field, dname, ", ".join(repr(m) for m in missing)))
    return problems


def main():
    argv = sys.argv[1:]
    root = Path(__file__).resolve().parent.parent
    if "--root" in argv:
        root = Path(argv[argv.index("--root") + 1]).resolve()
    problems = check(root)
    if problems:
        print("HYPOTHESIS-BUNDLE GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1
    exhibits = sum(1 for e in REGISTRY if e.get("exhibit"))
    gaps = len({d for e in REGISTRY for d, _ in e.get("gaps", [])})
    print("ok: %d registered headline bundles (%d jointly exhibited, %d named gap defs); "
          "every multi-hypothesis field of LoweringCorrect is accounted for"
          % (len(REGISTRY), exhibits, gaps))
    return 0


if __name__ == "__main__":
    sys.exit(main())

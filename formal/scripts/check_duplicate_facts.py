#!/usr/bin/env python3
"""Duplicate-fact gate: every copied fact must have a named pin between the copies.

WHY (docs/REVIEW.md R-58). Seven of the ten statement defects share one root cause:
PlanView, Surface, LoweringPlan and GeneratorConfig each carry a COPY of a fact the
Rust derives once - hasAccumulator, numInstances, the evaluator, encG2, the
quotient/direct pair, the shell program. A copy with no field relating it to its
source is a free variable: the reviewer showed 11 of the 13 PartialSpecs fields
discharge on a PlanView whose hasAccumulator is a one-Bool lie, because nothing
anywhere compares it to cfg.accumulator.isSome, and that S.shell.codeBlock occurs at
exactly one site, so the three run relations were about three unrelated programs.

WHAT THIS GATE CHECKS. Dependency structure, not text and not meaning. For each fact
family it asserts:

  1. every CARRIER (a record field that stores the fact) is still declared in the
     structure named, so a rename or a deletion cannot silently drop the family;
  2. if a family has two or more carriers there is a named PIN field, the pin is
     still declared, and the pin's TYPE mentions the tokens on both sides of the copy
     (e.g. plan.hasAccumulator AND cfg.accumulator). A pin whose statement names only
     one side - x = x, or shell.codeBlock = shell.codeBlock - does not connect the
     copies and fails here;
  3. a family whose copies are held together by a CONSTRUCTOR VALIDATION instead of a
     record pin (the quotient/direct pair, which lives in the ported LoweringPlan
     record and is enforced in LoweringPlan.new) names the fragments of that
     validation, and they must still be present.

WHAT THIS GATE CANNOT CATCH, stated plainly because R-58 says the last gate was
oversold. It is not a meaning check. A pin whose two sides are both wrong in the same
way passes. A pin that connects the right fields with the wrong operator passes as
long as both tokens appear. A carrier that is present, pinned, and never read by any
theorem passes. The existing fingerprint gate (check_statement_fingerprints.py) pins
TEXT FRAGMENTS of the LoweringCorrect fields and demonstrably lets F1, F7 and F8
through, because those defects are dependency vacuities rather than paraphrases. This
gate pins DEPENDENCY STRUCTURE. The two are complementary and neither is a semantics
check: only a proof is a semantics check.

Usage:  python3 scripts/check_duplicate_facts.py [--root DIR]
  --root DIR  look for Midfall/... under DIR instead of this script's parent's parent.
              Run the gate against a perturbed copy of the tree to show it reddens
              (R-41: a gate that has never been seen to fail is not a gate).
"""
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# The families. carriers are (file, structure, field) triples that STORE the fact.
# pins are (file, structure, field) triples whose type must relate them, and
# pin_tokens are the strings that pin's type has to mention to count as a link.
# enforced_at is (file, [fragments]) for a family held together by a constructor
# validation rather than by a record field.
# ---------------------------------------------------------------------------

SURFACE = "Midfall/Lowering/Surface.lean"
INV = "Midfall/Lowering/Inv.lean"
TYPES = "Midfall/Lowering/Types.lean"
API = "Midfall/Generator/Api.lean"
LPLAN = "Midfall/Generator/LoweringPlan.lean"
EIP = "Midfall/Assumptions/Eip2537.lean"

FAMILIES = [
    {
        "name": "hasAccumulator",
        "carriers": [(INV, "PlanView", "hasAccumulator"),
                     (API, "GeneratorConfig", "accumulator")],
        "pins": [(SURFACE, "Surface", "plan_hasAccumulator")],
        "pin_tokens": ["plan.hasAccumulator", "cfg.accumulator"],
    },
    {
        "name": "numInstances",
        "carriers": [(INV, "PlanView", "numInstances"),
                     (API, "GeneratorConfig", "numInstances")],
        "pins": [(SURFACE, "Surface", "plan_numInstances")],
        "pin_tokens": ["plan.numInstances", "cfg.numInstances"],
    },
    {
        "name": "evaluator",
        "carriers": [(TYPES, "Lowered", "evaluator"),
                     (SURFACE, "Surface", "evaluatorRuntime")],
        "pins": [(SURFACE, "Surface", "evaluator_agrees")],
        "pin_tokens": ["L.evaluator", "evaluatorRuntime"],
    },
    {
        "name": "encG2",
        "carriers": [(SURFACE, "Surface", "encG2"),
                     (EIP, "G2Enc", "toEip")],
        "pins": [(SURFACE, "Surface", "encG2_eip")],
        "pin_tokens": ["encG2", "encG2IsEip"],
    },
    {
        "name": "shell",
        "carriers": [(SURFACE, "Surface", "shell"),
                     (TYPES, "Lowered", "headGuard"),
                     (TYPES, "Lowered", "main"),
                     (SURFACE, "Surface", "bindLocals")],
        "pins": [(SURFACE, "Surface", "shell_unfolds")],
        "pin_tokens": ["shell.codeBlock", "L.headGuard", "bindLocals", "L.main"],
    },
    {
        "name": "vkDigest",
        "carriers": [(SURFACE, "Surface", "vkDigest"),
                     (SURFACE, "Surface", "vk")],
        "pins": [(SURFACE, "Surface", "vkDigest_spec")],
        "pin_tokens": ["vkDigest", "vk.transcriptRepr"],
    },
    {
        # The one family this package does NOT repair: LoweringPlan is a faithful port
        # of a Rust record (PL:29-45) whose invariant the Rust also does not enforce by
        # type, so the link is a constructor validation, not a record pin.
        "name": "quotient/direct",
        "carriers": [(LPLAN, "LoweringPlan", "lowering"),
                     (LPLAN, "LoweringPlan", "quotient"),
                     (LPLAN, "LoweringPlan", "direct")],
        "pins": [],
        "enforced_at": (LPLAN, ["direct plan also carries a compact VM plan",
                                "direct lowering must not reserve VM program words"]),
    },
]

# ---------------------------------------------------------------------------
# A small Lean reader: strip comments, then read 'structure NAME ... where' bodies
# and the field declarations inside them.
# ---------------------------------------------------------------------------


def strip_comments(text):
    """Blank out Lean line and block comments, keeping line structure.

    Block comments nest in Lean 4 and open on /-, /-! and /--. Comments are blanked
    rather than removed so line numbers survive, and so that a field cannot be
    'declared' inside a doc string - which is how a prose mention would otherwise
    satisfy a pin-token test.
    """
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if depth == 0:
            if text.startswith("/-", i) and i + 2 < n and text[i + 2] in "-!":
                depth = 1
                out.append("  ")
                i += 3
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                if j == -1:
                    break
                out.append(" " * (j - i))
                i = j
                continue
        else:
            if text.startswith("/-", i) and i + 2 < n and text[i + 2] in "-!":
                depth += 1
                out.append("  ")
                i += 3
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
        out.append(text[i])
        i += 1
    return "".join(out)


STRUCT_RE = re.compile(r"^structure\s+([A-Za-z0-9_.']+)")
FIELD_RE = re.compile(r"^(\s+)([A-Za-z_][A-Za-z0-9_.']*)\s*:\s*")
TOPLEVEL_RE = re.compile(r"^[A-Za-z_/-]")


def structures(text):
    """Map structure name -> {field name: (line index, declaration text)}."""
    lines = text.splitlines()
    result = {}
    i = 0
    while i < len(lines):
        m = STRUCT_RE.match(lines[i])
        if m is None:
            i += 1
            continue
        name = m.group(1)
        fields = {}
        j = i + 1
        while j < len(lines):
            ln = lines[j]
            if ln.strip() and TOPLEVEL_RE.match(ln):
                break
            fm = FIELD_RE.match(ln)
            if fm:
                indent = len(fm.group(1))
                field = fm.group(2)
                buf = [ln]
                k = j + 1
                while k < len(lines):
                    nxt = lines[k]
                    if nxt.strip():
                        cur = len(nxt) - len(nxt.lstrip())
                        if cur <= indent or TOPLEVEL_RE.match(nxt):
                            break
                    buf.append(nxt)
                    k += 1
                fields[field] = (j, " ".join(s.strip() for s in buf))
                j = k
                continue
            j += 1
        result[name] = fields
        i = j
    return result


def check(root):
    cache = {}
    raw = {}

    def read(rel):
        if rel not in cache:
            p = root / rel
            cache[rel] = (structures(strip_comments(p.read_text(encoding="utf-8")))
                          if p.exists() else None)
        return cache[rel]

    def read_raw(rel):
        if rel not in raw:
            p = root / rel
            raw[rel] = p.read_text(encoding="utf-8") if p.exists() else None
        return raw[rel]

    problems = []
    pinned = 0
    for fam in FAMILIES:
        name = fam["name"]
        present = []
        for (rel, struct, field) in fam["carriers"]:
            structs = read(rel)
            if structs is None:
                problems.append("%s: file missing: %s" % (name, rel))
                continue
            if struct not in structs:
                problems.append("%s: structure %s not found in %s" % (name, struct, rel))
                continue
            if field not in structs[struct]:
                problems.append("%s: CARRIER VANISHED - %s.%s is no longer declared in %s"
                                % (name, struct, field, rel))
                continue
            present.append(field)
        if len(present) >= 2:
            if fam.get("pins"):
                for (rel, struct, field) in fam["pins"]:
                    structs = read(rel)
                    if (structs is None or struct not in structs
                            or field not in structs[struct]):
                        problems.append("%s: NO PIN - %s.%s is missing from %s, so the "
                                        "%d copies of this fact are unrelated"
                                        % (name, struct, field, rel, len(present)))
                        continue
                    text = structs[struct][field][1]
                    missing = [t for t in fam["pin_tokens"] if t not in text]
                    if missing:
                        problems.append("%s: PIN DOES NOT CONNECT - %s.%s never mentions "
                                        "%s, so it does not relate the copies"
                                        % (name, struct, field, ", ".join(missing)))
                        continue
                    # A pin of the shape `x = x` connects nothing even when it
                    # mentions the right names, so reject a literal self-equality.
                    typ = text.split(":", 1)[1] if ":" in text else text
                    if "=" in typ:
                        lhs, rhs = typ.split("=", 1)
                        if lhs.strip() == rhs.strip():
                            problems.append("%s: PIN IS A SELF-EQUALITY - %s.%s says %s"
                                            % (name, struct, field, typ.strip()))
                            continue
                    pinned += 1
            elif fam.get("enforced_at"):
                rel, frags = fam["enforced_at"]
                body = read_raw(rel)
                if body is None:
                    problems.append("%s: enforcement file missing: %s" % (name, rel))
                    continue
                gone = [f for f in frags if f not in body]
                if gone:
                    problems.append("%s: ENFORCEMENT VANISHED - %s no longer contains %s"
                                    % (name, rel, ", ".join(repr(g) for g in gone)))
                    continue
                pinned += 1
            else:
                problems.append("%s: %d copies of this fact with no pin and no named "
                                "enforcement - the R-58 F2/F3/F6 class"
                                % (name, len(present)))
    return problems, pinned


def main():
    argv = sys.argv[1:]
    root = Path(__file__).resolve().parent.parent
    if "--root" in argv:
        root = Path(argv[argv.index("--root") + 1]).resolve()
    problems, pinned = check(root)
    if problems:
        print("DUPLICATE-FACT GATE FAILED (%d problem(s)):" % len(problems))
        for p in problems:
            print("  " + p)
        return 1
    print("ok: %d fact families, every one either single-copy or pinned "
          "(%d pins checked)" % (len(FAMILIES), pinned))
    return 0


if __name__ == "__main__":
    sys.exit(main())

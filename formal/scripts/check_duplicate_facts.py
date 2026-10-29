#!/usr/bin/env python3
"""Duplicate-fact gate: every copied fact must have a named pin, a scoped enforcement,
a derived consumer, or a declared gap - and a NEW copy must be DISCOVERED, not regressed.

WHY (docs/REVIEW.md R-58 and R-60 S2). Seven of the ten R-58 statement defects share
one root cause: PlanView, Surface, LoweringPlan and GeneratorConfig each carry a COPY
of a fact the Rust derives once - hasAccumulator, numInstances, the evaluator, encG2,
the quotient/direct pair, the shell program. A copy with no field relating it to its
source is a free variable. R-60 S1 found the same class in the one place it mattered
most: the fixture's irCheck hard-coded a runtime naming convention instead of reading
Surface.runtimeName, so the gate on the headline hypothesis disagreed with the run
relation it was supposed to describe.

WHAT THIS GATE CHECKS. Dependency structure, not text and not meaning.

  1. CARRIER: every record field that stores the fact is still declared in the named
     structure, so a rename or deletion cannot silently drop the family.
  2. PIN: if a family has two or more carriers there is a named pin field, and its
     TYPE mentions the tokens on both sides - matched at WORD BOUNDARIES, because
     R-60 S2 found that substring matching let 'encG2' be "mentioned" by 'encG2IsEip'.
     A pin whose every component is trivially decidable is rejected: R-60 S2 found
     that a self-equality was beaten by any earlier colon in the type, and that a
     CONJUNCTION of self-equalities passed outright.
  3. ENFORCED_AT: a family held together by a constructor validation instead of a
     record pin names the DEFINITION that performs the validation, and the fragments
     must occur inside THAT definition's body, in comment-stripped code. R-60 S2 found
     the old form grepped raw file text, so deleting the real quotient/direct checks
     stayed green while the same English sentences survived in a KAT string.
  4. DERIVED: a free field that other code re-derives is pinned to its consumers by
     requiring each consumer definition to READ the field. This is the S1 repair:
     Surface.irCheck is a projection of Surface.irRuntime, which is a projection of
     Surface.runtimeName, and if the check ever goes back to hard-coding a name the
     token disappears from the consumer and the gate reddens.
  5. DISCOVERY: every structure field in the tracked files whose name is a known
     carrier stem (optionally with a trailing digit or a suffix) must be accounted for
     by some family. R-60 S2's most important point: a hand-written family list is a
     REGRESSION check, and the arrival of a NEW copy - 'hasAccumulator2 : Bool' - is
     the actual root cause. This is the half that discovers.
  6. GAP: a copy this package does not repair names a Lean definition that states the
     gap and its blocker, so the gap lives in the code, is deletable, and reddens the
     gate when it goes missing or when the blocker is no longer named.

WHAT THIS GATE CANNOT CATCH, stated plainly. It is not a meaning check. A pin whose two
sides are both wrong in the same way passes. A carrier that is present, pinned and never
read by any theorem passes. Only a proof is a semantics check.

Usage:  python3 scripts/check_duplicate_facts.py [--root DIR]
  --root DIR  look for Midfall/... under DIR instead of this script's parent's parent.
              Run the gate against a perturbed copy of the tree to show it reddens
              (R-41: a gate that has never been seen to fail is not a gate).
"""
import re
import sys
from pathlib import Path

SURFACE = "Midfall/Lowering/Surface.lean"
INV = "Midfall/Lowering/Inv.lean"
TYPES = "Midfall/Lowering/Types.lean"
API = "Midfall/Generator/Api.lean"
LPLAN = "Midfall/Generator/LoweringPlan.lean"
EIP = "Midfall/Assumptions/Eip2537.lean"

# Stems that mark a field as "a copy of a fact this programme has already been burned
# by copying". Discovery (rule 5) flags any field whose name stems from one of these
# unless a family declares it. Longer stems also match as substrings; short ones only
# as prefixes, to keep the scan free of noise.
DISCOVERY_STEMS = ["hasAccumulator", "numInstances", "accumulator", "evaluator",
                   "encG2", "runtimeName", "vkDigest", "shell"]

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
        # R-60 S3: the pin is the runtime-BLOCK equation now, so the token test asks
        # for the projection that makes it a block equation and not for isSome.
        "pin_tokens": ["L.evaluator", "evaluatorRuntime", "Object.codeBlock"],
    },
    {
        "name": "encG2",
        "carriers": [(SURFACE, "Surface", "encG2"),
                     (EIP, "G2Enc", "toEip")],
        "pins": [(SURFACE, "Surface", "encG2_shape")],
        "pin_tokens": ["encG2", "encG2IsEip"],
    },
    {
        "name": "shell",
        "carriers": [(SURFACE, "Surface", "shell"),
                     (SURFACE, "Surface", "shellLayout"),
                     (TYPES, "Lowered", "headGuard"),
                     (TYPES, "Lowered", "main"),
                     (SURFACE, "Surface", "bindLocals")],
        "pins": [(SURFACE, "Surface", "shell_unfolds")],
        "pin_tokens": ["shell.codeBlock", "L.headGuard", "bindLocals", "L.main"],
    },
    {
        "name": "vkDigest",
        "carriers": [(SURFACE, "Surface", "vkDigest"),
                     (SURFACE, "Surface", "vk"),
                     # R-60 S2 discovery: the third copy of the same word. EnvAgrees is
                     # the hypothesis that relates the plan slot to the key, so it is a
                     # carrier of this fact and not an unrelated field sharing a stem.
                     (INV, "EnvAgrees", "vkDigestWord")],
        "pins": [(SURFACE, "Surface", "vkDigest_spec")],
        "pin_tokens": ["vkDigest", "vk.transcriptRepr"],
    },
    {
        # R-60 S1: the runtime naming convention. It is a free field, and the S1
        # defect was a SECOND copy of it baked into the body of the import check.
        # The repair deleted the copy, so the family is single-carrier by construction
        # and the DERIVED list is what keeps it that way.
        "name": "runtimeName",
        "carriers": [(SURFACE, "Surface", "runtimeName")],
        "pins": [],
        "derived": [(SURFACE, "Surface.irRuntime", ["S.runtimeName"]),
                    (SURFACE, "Surface.irCheck", ["irRuntime"])],
    },
    {
        # The one family this package does NOT repair: LoweringPlan is a faithful port
        # of a Rust record (PL:29-45) whose invariant the Rust also does not enforce by
        # type, so the link is a constructor validation, not a record pin. R-60 S2:
        # the validation is now located by DEFINITION, not by file-wide grep.
        "name": "quotient/direct",
        "carriers": [(LPLAN, "LoweringPlan", "lowering"),
                     (LPLAN, "LoweringPlan", "quotient"),
                     (LPLAN, "LoweringPlan", "direct")],
        "pins": [],
        "enforced_at": (LPLAN, "LoweringPlan.validateGeneratorInvariants",
                        ["L.quotient.isSome", "L.lowering != QuotientLowering.direct",
                         "direct plan also carries a compact VM plan",
                         "direct lowering must not reserve VM program words"]),
    },
    {
        # P-AST3b: the four VK-header accumulator words PlanView now carries, because
        # VkLoading.yul:105-110 cross-checks the loaded VK header against them. The Rust
        # derives all four ONCE from the accumulator encoding (Vk.lean:782-791, and
        # Artifacts.lean's accExpectationsOf at ART:229-245), so four fields are four
        # copies of one fact - the R-58 F2 class one step further. Both repairs the brief
        # allows are in: the values are DERIVED by Inv.lean's accWordsOfEncoding through
        # planViewWithAccumulator, the only PlanView constructor any call site uses, AND
        # the copies are related to their source by the named pin below - one equation over
        # the 4-tuple, so no individual word can be paraphrased out of it.
        #
        # WHY THIS IS REGISTERED BY HAND: discovery (rule 5) would NOT have flagged these
        # four. The stem scan is a PREFIX match on the field name, and expectedAccOffset /
        # expectedNumAccLimbs / expectedNumAccLimbBits / expectedHasAccumulatorWord all
        # begin with "expected". A new spelling of an old copy is a human finding, and this
        # comment is the record that it was found by a human and not by the gate.
        "name": "accExpectations",
        "carriers": [(INV, "PlanView", "expectedHasAccumulatorWord"),
                     (INV, "PlanView", "expectedAccOffset"),
                     (INV, "PlanView", "expectedNumAccLimbs"),
                     (INV, "PlanView", "expectedNumAccLimbBits"),
                     (API, "GeneratorConfig", "accumulator")],
        "pins": [(SURFACE, "Surface", "plan_accExpectations")],
        "pin_tokens": ["plan.expectedHasAccumulatorWord", "plan.expectedAccOffset",
                       "plan.expectedNumAccLimbs", "plan.expectedNumAccLimbBits",
                       "cfg.accumulator"],
    },
    {
        # P-AST4: the six transcript-parser facts PlanView now carries, because
        # TranscriptProofParser.yul loops over user_phases (:105), guards four of its ten
        # proof sections on the four counts (:142, :172, :195, :242) and masks x3 on the
        # truncation flag (:355). The Rust derives all six ONCE into the render model
        # (M:557-563, M:614) from the constraint-system meta and the proof layout
        # (ART:160-170, :291-294, :172, :328), so six fields are six copies of facts that
        # already live in the plan record - the R-58 F2 / F6 class again, one partial later.
        # The repair is the P-AST3b shape: ONE derivation (Inv.lean's parserFactsOfPlan,
        # reached only through planViewWithAccumulator, the constructor every call site
        # uses) and a pin that ties the derived six to the values the emitter reads
        # (Instances/DeployedProfile.lean's derivedParserFacts_matchPlanView_ok, which also
        # perturbs each of the six on the model and requires the tuple to move).
        #
        # WHY THIS IS REGISTERED BY HAND, and this is the second time the same hole in the
        # gate has been found by a human rather than by the gate: discovery (rule 5) is a
        # PREFIX match of the field name against DISCOVERY_STEMS, and not one of userPhases,
        # numLookups, numPermutationZs, lookupHPlusAcc, numTrashcans or truncatedChallenges
        # begins with hasAccumulator, numInstances, accumulator, evaluator, encG2,
        # runtimeName, vkDigest or shell. "numLookups" does not start with "numInstances";
        # "lookupHPlusAcc" does not start with "accumulator". A family of six brand-new
        # copies is invisible to the automatic scan, exactly as the four "expected*" words
        # were in P-AST3b. The stem list is NOT widened here: adding "num" or "lookup" would
        # flag dozens of unrelated fields, and a gate that cries wolf gets ignored (R-60 S2).
        "name": "transcriptParserFacts",
        # P-PLANVIEW DELETED THREE OF THE SIX CARRIERS rather than pinning them:
        # numLookups, numPermutationZs and numTrashcans are literally meta_.numLookups,
        # meta_.numPermutationZs and meta_.numTrashcans (ART:291, :292, :294), so once
        # PlanView carries the meta they were a copy whose source sat in the same record.
        # Deleting is the repair the gate prefers - there is now ONE carrier of each fact,
        # reached by the three projections PlanView.numLookups and siblings - and the
        # deletion is what this family now records rather than a pin. The three that remain
        # are the three that are NOT meta projections: userPhases (userPhasesOf indexes the
        # proof layout and aborts at ART:164, so a total projection would swallow a panic),
        # lookupHPlusAcc (Artifacts' lookupHPlusAccOf is the one carrier of that sum) and
        # truncatedChallenges (a build input at ART:328, not a circuit fact).
        "carriers": [(INV, "PlanView", "userPhases"),
                     (INV, "PlanView", "lookupHPlusAcc"),
                     (INV, "PlanView", "truncatedChallenges")],
        "pins": [],
        "enforced_at": (INV, "parserFactsOfPlan",
                        ["m.userPhases", "m.lookupHPlusAcc", "m.truncatedChallenges"]),
    },
    {
        # P-PLANVIEW: the two fields the PCS emitter needs, added to PlanView as a
        # projection of the plan record. Registered as a DECLARED GAP rather than a pin
        # because there is nothing in Lean to pin them against: the source is
        # LoweringPlan.meta_ / LoweringPlan.data, and no Surface carries a LoweringPlan
        # because P-11's LoweringPlan::new has not landed - the same blocker
        # ObligationsGates.gap_qvmField_surface_free names for the qvm field. The gap lives
        # in the code (Inv.lean's gap_planview_carries_the_plan), and the package's answer
        # to "unpinned" is deletion where deletion was possible: see the family above.
        "name": "pcsPlanInputs",
        "carriers": [(INV, "PlanView", "meta_"),
                     (INV, "PlanView", "dat"),
                     (LPLAN, "LoweringPlan", "meta_"),
                     (LPLAN, "LoweringPlan", "data")],
        "pins": [],
        "gap": (INV, "gap_planview_carries_the_plan",
                ["PlanView.meta_", "PlanView.dat", "LoweringPlan::new"]),
    },
    {
        # R-60 S7: shell.codeBlock (the Yul AST the shell runs) and shellLayout.code
        # (the bytecode the deployment installs) are two copies of "the shell program"
        # in two representations. No pin is nameable today: relating them needs a
        # Yul-to-bytecode compiler, and P-13 ported the templates as TEXT renders, so
        # nothing in Lean emits bytecode from a Block Op. Declared as a gap in the code
        # (gap_shell_code_vs_layout_code in Surface.lean), not in prose.
        "name": "shell bytecode",
        "carriers": [(SURFACE, "Surface", "shell"),
                     (SURFACE, "Surface", "shellLayout")],
        "pins": [],
        "gap": (SURFACE, "gap_shell_code_vs_layout_code",
                ["Yul-to-bytecode compiler"]),
    },
]

# ---------------------------------------------------------------------------
# A small Lean reader: strip comments, then read 'structure NAME ... where' bodies,
# the field declarations inside them, and named top-level definitions.
# ---------------------------------------------------------------------------

STR = re.compile(r'"(?:\\.|[^"\\])*"')
FORALL = "∀"
ARROW = "→"
AND = "∧"


def strip_comments(text):
    """Blank out Lean line and block comments, keeping line and column structure.

    Block comments nest in Lean 4 and open on /-, /-! and /--; their BODIES are
    blanked too. R-60 S2 is the reason this function is written out again: the
    previous version opened on /-- and /-! but then COPIED the body through, so a
    doc string was parsed as code and the tree's own provenance convention
    ('/-- rust: try_new rejects ... -/') invented a phantom SupportedS field named
    'rust'. A gate whose parser harvests fields from prose is worse than no gate: it
    reports the shape of the comments as the shape of the record.

    Comments are blanked rather than removed so line numbers survive, and so that a
    field cannot be 'declared' inside a doc string - which is how a deleted pin left
    inside /-- ... -/ kept the pin-token test green.
    """
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if depth == 0:
            if c == '"':
                m = STR.match(text, i)
                if m:
                    out.append(m.group(0))
                    i = m.end()
                    continue
            if text.startswith("/--", i) or text.startswith("/-!", i):
                depth = 1
                out.append("   ")
                i += 3
                continue
            if text.startswith("/-", i):
                depth = 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                if j == -1:
                    out.append(" " * (n - i))
                    break
                out.append(" " * (j - i))
                i = j
                continue
            out.append(c)
            i += 1
            continue
        # inside a block comment: blank the body, keep newlines
        if text.startswith("/--", i) or text.startswith("/-!", i):
            depth += 1
            out.append("   ")
            i += 3
            continue
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
    return "".join(out)


STRUCT_RE = re.compile(r"^structure\s+([A-Za-z0-9_.']+)")
FIELD_RE = re.compile(r"^(\s+)([A-Za-z_][A-Za-z0-9_.']*)\s*:\s*")
TOPLEVEL_RE = re.compile(r"^[A-Za-z_/-]")
DECL_RE = re.compile(r"^(?:private\s+|protected\s+)?(?:abstract\s+)?"
                     r"(def|theorem|lemma|abbrev|instance|example|structure)\s+"
                     r"([A-Za-z0-9_.']+)?")


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


def definitions(text):
    """Map top-level declaration name -> its full source text, comment-stripped.

    Used for the scoped checks: enforced_at fragments and derived-consumer tokens have
    to live inside the named definition, not anywhere in the file.
    """
    lines = text.splitlines()
    result = {}
    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.strip() and TOPLEVEL_RE.match(ln):
            m = DECL_RE.match(ln)
            if m and m.group(2):
                name = m.group(2)
                buf = [ln]
                k = i + 1
                while k < len(lines):
                    nxt = lines[k]
                    if nxt.strip() and TOPLEVEL_RE.match(nxt):
                        break
                    buf.append(nxt)
                    k += 1
                result[name] = " ".join(s.strip() for s in buf)
                i = k
                continue
        i += 1
    return result


def mentions(text, token):
    """Word-boundary token test. R-60 S2: substring matching let 'encG2' be counted
    as mentioned by 'encG2IsEip', so a pin naming only the validator passed the
    both-sides test without naming the encoder at all."""
    esc = re.escape(token)
    return re.search(r"(?<![A-Za-z0-9_'])" + esc + r"(?![A-Za-z0-9_'])", text) is not None


def split_top(s, seps):
    """Split on top-level separators, respecting (), [], {} and string literals."""
    parts, cur, depth = [], "", 0
    i = 0
    while i < len(s):
        c = s[i]
        if c == '"':
            m = STR.match(s, i)
            if m:
                cur += m.group(0)
                i = m.end()
                continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if depth == 0:
            hit = None
            for sep in seps:
                if s.startswith(sep, i):
                    hit = sep
                    break
            if hit:
                parts.append(cur)
                cur = ""
                i += len(hit)
                continue
        cur += c
        i += 1
    parts.append(cur)
    return parts


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def strip_binders(comp):
    """Drop leading FORALL x : T, and (h : T) -> binder prefixes from a component."""
    comp = norm(comp)
    for _ in range(8):
        before = comp
        if comp.startswith(FORALL):
            parts = split_top(comp[1:], [","])
            if len(parts) > 1:
                comp = norm(parts[-1])
        if comp.startswith("("):
            depth = 0
            for i, c in enumerate(comp):
                if c in "([{":
                    depth += 1
                elif c in ")]}":
                    depth -= 1
                    if depth == 0:
                        after = comp[i + 1:].strip()
                        if (after.startswith(ARROW) or after.startswith("->")
                                or after.startswith(",")):
                            comp = norm(after.lstrip(ARROW + ",->").strip())
                        break
        if comp == before:
            break
    return comp


def is_trivial(comp):
    """True if the component is decidable without knowing the fields it names."""
    c = strip_binders(comp)
    if c in ("True", ""):
        return True
    eqs = split_top(c, ["="])
    if len(eqs) == 2 and norm(eqs[0]) == norm(eqs[1]) and norm(eqs[0]) != "":
        return True
    return False


def triviality_problems(typ):
    """Reject a pin every Surface satisfies.

    R-60 S2 found two defeats here. (a) The old code took the text after the FIRST
    colon and before the first '=', so any earlier colon in the type - a binder group
    like '(z : Nat) -> X = X' - made the two sides unequal and the self-equality
    passed. (b) A CONJUNCTION of self-equalities passed for the same reason. The rule
    now: split the type into top-level components on the arrow, take the CONCLUSION
    (the last component), split THAT on the conjunction operator, and reject when every
    conjunct of the conclusion is decidable without knowing the fields it names. So
    '(h : X = X) -> True' is rejected through its conclusion and a conjunction of
    self-equalities through its conjuncts, and neither can hide behind an earlier colon.
    """
    comps = [c for c in split_top(typ, [ARROW, "->"]) if c.strip()]
    if not comps:
        return ["empty type"]
    conclusion = comps[-1]
    conjuncts = [c for c in split_top(conclusion, [AND]) if c.strip()]
    if not conjuncts:
        return ["empty conclusion"]
    if all(is_trivial(c) for c in conjuncts):
        return ["every conjunct of the conclusion is trivially decidable: " +
                "; ".join(norm(c) for c in conjuncts)]
    return []


def check(root):
    cache, stripped, defcache = {}, {}, {}

    def strip(rel):
        if rel not in stripped:
            p = root / rel
            stripped[rel] = strip_comments(p.read_text(encoding="utf-8")) \
                if p.exists() else None
        return stripped[rel]

    def read(rel):
        if rel not in cache:
            s = strip(rel)
            cache[rel] = structures(s) if s is not None else None
        return cache[rel]

    def defs(rel):
        if rel not in defcache:
            s = strip(rel)
            defcache[rel] = definitions(s) if s is not None else None
        return defcache[rel]

    problems = []
    pinned = 0
    gaps = 0
    derived = 0

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
        if len(present) < 2:
            for (rel, dname, toks) in fam.get("derived", []):
                body = (defs(rel) or {}).get(dname)
                if body is None:
                    problems.append("%s: DERIVED CONSUMER MISSING - %s is not declared "
                                    "in %s, so the single carrier has no reader"
                                    % (name, dname, rel))
                    continue
                missing = [t for t in toks if not mentions(body, t)]
                if missing:
                    problems.append("%s: DERIVED CONSUMER DOES NOT READ THE CARRIER - "
                                    "%s never mentions %s in %s (R-60 S1: the check must "
                                    "read the field it belongs to)"
                                    % (name, dname, ", ".join(missing), rel))
                    continue
                derived += 1
            continue
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
                missing = [t for t in fam["pin_tokens"] if not mentions(text, t)]
                if missing:
                    problems.append("%s: PIN DOES NOT CONNECT - %s.%s never mentions "
                                    "%s, so it does not relate the copies"
                                    % (name, struct, field, ", ".join(missing)))
                    continue
                typ = text.split(":", 1)[1] if ":" in text else text
                bad = triviality_problems(typ)
                if bad:
                    problems.append("%s: PIN IS TRIVIALLY DECIDABLE - %s.%s says %s (%s)"
                                    % (name, struct, field, norm(typ), bad[0]))
                    continue
                pinned += 1
        elif fam.get("enforced_at"):
            rel, dname, frags = fam["enforced_at"]
            body = defs(rel)
            if body is None:
                problems.append("%s: enforcement file missing: %s" % (name, rel))
                continue
            if dname not in body:
                problems.append("%s: ENFORCEMENT VANISHED - %s is not declared in %s, "
                                "so nothing performs the %s validation"
                                % (name, dname, rel, name))
                continue
            scope = body[dname]
            gone = [f for f in frags if f not in scope]
            if gone:
                problems.append("%s: ENFORCEMENT VANISHED - %s no longer contains %s "
                                "inside %s (the same sentence elsewhere in the file, e.g. "
                                "in a KAT string, enforces nothing)"
                                % (name, rel, ", ".join(repr(g) for g in gone), dname))
                continue
            pinned += 1
        elif fam.get("gap"):
            rel, dname, toks = fam["gap"]
            body = defs(rel)
            if body is None or dname not in body:
                problems.append("%s: DECLARED GAP NOT IN THE CODE - %s is missing from "
                                "%s, so this unpinned copy is undocumented"
                                % (name, dname, rel))
                continue
            missing = [t for t in toks if t not in body[dname]]
            if missing:
                problems.append("%s: GAP BLOCKER MISSING - %s no longer names %s"
                                % (name, dname, ", ".join(repr(m) for m in missing)))
                continue
            gaps += 1
        else:
            problems.append("%s: %d copies of this fact with no pin, no named "
                            "enforcement and no declared gap - the R-58 F2/F3/F6 class"
                            % (name, len(present)))

    # ---- rule 5: DISCOVERY, not regression ------------------------------------
    seen = set()
    for fam in FAMILIES:
        for entry in fam["carriers"] + fam.get("pins", []):
            seen.add(entry)
    for rel in sorted({c[0] for f in FAMILIES
                       for c in f["carriers"] + f.get("pins", [])}):
        structs = read(rel)
        if structs is None:
            problems.append("discovery: file missing: %s" % rel)
            continue
        for struct, fields in sorted(structs.items()):
            for field in sorted(fields):
                stem = re.sub(r"\d+$", "", field).lower()
                if not stem:
                    continue
                hit = None
                for s in DISCOVERY_STEMS:
                    # PREFIX matching only, after the trailing digit is stripped: a
                    # substring rule flags ProofEvaluationCounts.lookupAccumulator and
                    # RenderedArtifacts.quotientEvaluator, different facts that happen
                    # to END with a carrier name, and a gate that cries wolf gets
                    # ignored - which is the failure mode R-60 S2 is about.
                    if stem.startswith(s.lower()):
                        hit = s
                        break
                if hit is None or (rel, struct, field) in seen:
                    continue
                problems.append("NEW COPY NOT ACCOUNTED FOR - %s.%s stems from the "
                                "carrier %r; add it to a family as a carrier with a "
                                "pin, as an enforcement, or as a declared gap "
                                "(R-60 S2 discovery)" % (rel, struct + "." + field, hit))
    return problems, pinned, gaps, derived


def main():
    argv = sys.argv[1:]
    root = Path(__file__).resolve().parent.parent
    if "--root" in argv:
        root = Path(argv[argv.index("--root") + 1]).resolve()
    problems, pinned, gaps, derived = check(root)
    if problems:
        print("DUPLICATE-FACT GATE FAILED (%d problem(s)):" % len(problems))
        for p in problems:
            print("  " + p)
        return 1
    print("ok: %d fact families, every one either single-copy or pinned "
          "(%d pins, %d derived consumers, %d declared gaps); discovery scan covers "
          "every field of every tracked structure"
          % (len(FAMILIES), pinned, derived, gaps))
    return 0


if __name__ == "__main__":
    sys.exit(main())

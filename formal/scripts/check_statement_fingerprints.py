#!/usr/bin/env python3
"""Statement-fingerprint gate for Midfall/Lowering/Obligations.lean.

Why (P-SE stage 6, R-41, hardened by R-60 S2): LoweringCorrect fields are STATEMENTS,
not gated computations, so no #eval gate reads a field text. Three perturbations proved
it - replacing ZeroAbove with True in verifier_sound, paraphrasing render_eq_print's
conjunct as a length equality, and dropping the selector conjunct from only_two_outcomes
- each built clean with every gate still true. The only defence had been a hand-run
verbatim diff against section Q. This makes it a CI gate.

It does NOT claim byte equality: seven fields legitimately differ from the sketch by
recorded substitutions. It asserts each load-bearing FRAGMENT survives, so a paraphrase
that drops a conjunct or weakens a hypothesis fails even though it elaborates.

R-60 S2 closed two defeats of this gate:

  * COMMENTS WERE NOT STRIPPED. field_text read raw lines, so a deleted statement whose
    text survived inside a doc string or a trailing comment still fingerprinted green.
    The gate now parses comment-stripped code with the SAME stripper the duplicate-fact
    gate uses, so the two cannot disagree about what the file says.
  * FRAGMENTS WERE MATCHED ANYWHERE IN THE DECLARATION, value and all. So a field
    written 'render_eq_print : True := trivial' with the real text in a trailing
    comment passed: the fragments were in the comment and in the value, and the TYPE
    said nothing. The gate now cuts the declaration at the first top-level ':=' and
    matches fragments inside the TYPE only, and it rejects a field whose type is
    trivially decidable (True, or a conjunction of self-equalities) outright - the
    countdown_or_halt : True := trivial pattern attack.md names, which the old gate
    could not see at all.

Usage:  python3 scripts/check_statement_fingerprints.py [OBLIGATIONS.LEAN]
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_duplicate_facts import (ARROW, AND, norm, split_top, strip_comments,
                                   triviality_problems)

FINGERPRINTS = [
    ("verifier_sound", ["ZeroAbove mem", "SoundSide S H cd",
        "obs.returnData = abiTrue", "LeanAccepts S H cd", "SupportedS S S.o",
        "DeploymentW S W H vkAddr qAddr", "Eip2537.Holds",
        "EnvAgrees S.E S.vk S.plan S.params S.sG2gen"]),
    ("verifier_complete", ["CompleteSide S H cd", "EnvAgrees", "G1CodecLaws",
        "LeanAccepts S H cd", "returnView (callState"]),
    ("only_two_outcomes", ["fnSigVerifyProof", "obs.isRevertOrHalt",
        "obs.worldUnchanged", "returnView (callState",
        "EnvAgrees S.E S.vk S.plan S.params S.sG2gen"]),
    ("ir_refines", ["S.irCheck ir = true", "WorldLocal", "ObsEquiv",
        "RunContractIR", "RunShell"]),
    # R-60 S5: render_eq_print is a conjunction now - the astOfMain/lower equation AND
    # the trace-refusal half that stops it being one free function defined in terms of
    # another. Both halves are fingerprinted, so dropping either reddens the gate.
    ("render_eq_print", ["S.astOfMain o =", "match S.lower o with",
        "some l.main", ".error _ => none",
        "o.diagnostics.trace = true", "S.astOfMain o = none"]),
    ("end_to_end_noAcc", ["S.cfg.accumulator = none",
        "inst.size = S.cfg.numInstances", "fromRepackError", "verifyNative",
        "repackProof", "encodeCalldata", "RunContractIR"]),
    ("lowering_equivalence", ["RunContractIR", "obs.isReturn",
        "obs.returnData = abiTrue", "LeanAccepts S H cd",
        "S.irCheck ir = true", "\u2203 obs"]),
    ("qvm_validated_noBoundsFault", ["readPastEnd", "constSlotOutOfRange",
        "quotientOperandModel", ").isOk = true"]),
    ("accFixedBases_producer", [chr(34) + "-G" + chr(34), "negate = true",
        "\u2203 b \u2208 S.accFixedBases.toList", "namesAscending"]),
]

# R-58 also added pin FIELDS to the Surface record. Those are statements too, and the
# duplicate-fact gate only checks that they exist and name both sides - it does not
# notice a paraphrase that keeps the two names and drops the equation. These fragments
# pin the shape of each pin, in the file that declares them.
SURFACE_PINS = [
    ("shell_unfolds", ["shell.codeBlock =", "L.headGuard ++ bindLocals ++ L.main"]),
    ("plan_hasAccumulator", ["plan.hasAccumulator =", "cfg.accumulator.isSome"]),
    ("plan_numInstances", ["plan.numInstances =", "cfg.numInstances"]),
    # R-60 S3: the evaluator pin is the runtime-BLOCK equation, not the isSome agreement.
    ("evaluator_agrees", ["L.evaluator.map YulSemantics.Object.codeBlock =",
                          "evaluatorRuntime.map Prod.fst"]),
    # R-60 S4: renamed encG2_eip -> encG2_shape, and the name IS the claim: the shape of
    # the bytes, not a codec. The injectivity this pin does not make is a named gap in
    # scripts/check_hypothesis_bundles.py, not a satisfied claim.
    ("encG2_shape", ["\u2200 R : G\u2082", "encG2IsEip (encG2 R) = true"]),
]
# R-60 S1: the import check is a PROJECTION of the naming field, not a free field. Its
# body is fingerprinted here too, because the defect was in a definition and not in a
# statement: a check that hard-codes a name instead of reading S.runtimeName makes every
# headline hypothesis above it unsatisfiable while elaborating perfectly.
DERIVED_CHECKS = [
    ("Surface.irCheck", ["S.irRuntime", "unresolvedTop"]),
    ("Surface.irRuntime", ["S.runtimeName"]),
]

DECL = re.compile(r"^\s*(?:theorem |lemma |def |example )?")
WORD_START = re.compile(r"^[A-Za-z_]")


def field_type(lines, start, whole=False):
    """The declaration at the given line, TYPE ONLY by default. With whole=True the
    full declaration including its body, which is what a derived-check test wants."""
    indent = len(lines[start]) - len(lines[start].lstrip())
    end = len(lines)
    for j in range(start + 1, len(lines)):
        stripped = lines[j].strip()
        if not stripped:
            continue
        cur = len(lines[j]) - len(lines[j].lstrip())
        if cur <= indent and (WORD_START.match(stripped)
                              or stripped.startswith("/")
                              or stripped.startswith("--")):
            end = j
            break
    text = norm(" ".join(lines[start:end]))
    # cut at the first top-level assignment so a value or proof body cannot carry a
    # fragment: 'render_eq_print : True := trivial -- <the real text>' is the exploit
    if whole:
        return text
    # The STATEMENT is everything before the first top-level assignment. For a theorem
    # that includes the binder list, and the binders are where the hypotheses live:
    # "(hir : S.irCheck ir = true)" is a hypothesis of lowering_equivalence, so cutting
    # the statement at the first colon would throw away exactly the part a vacuity
    # attack edits. The value and any trailing comment are still excluded, which is the
    # R-60 S2 exploit this gate had.
    return norm(split_top(text, [":="])[0])


def conclusion(text):
    """The part after the first TOP-LEVEL colon: the type of a field, the conclusion of
    a theorem. Colons inside binder parens are not top-level, and a type may itself
    contain colons (forall R : G2, ...), so the remainder is rejoined."""
    parts = split_top(text, [":"])
    if len(parts) < 2:
        return norm(text)
    return norm(":".join(parts[1:]))


def field_text(body, field, whole=False):
    lines = body.splitlines()
    # The name must be FOLLOWED by a colon (a structure field) or by "("
    # (a theorem with binders), not by prose: "shell_unfolds below now states"
    # in a doc comment is not the shell_unfolds field - and after R-60 S2 the doc
    # comment is not even in the text the parser sees.
    pat = re.compile(DECL.pattern + re.escape(field) + r"\s*(?::|\()")
    for i, ln in enumerate(lines):
        if pat.match(ln):
            return field_type(lines, i, whole)
    return ""


def main():
    root = Path(__file__).resolve().parent.parent
    default = root / "Midfall/Lowering/Obligations.lean"
    ob = Path(sys.argv[1]) if len(sys.argv) > 1 else default
    if not ob.exists():
        print("check_statement_fingerprints: no such file", ob, file=sys.stderr)
        return 2
    body = strip_comments(ob.read_text(encoding="utf-8"))
    problems = []
    checked = 0
    for field, frags in FINGERPRINTS:
        text = field_text(body, field)
        if not text:
            problems.append(field + ": FIELD NOT FOUND")
            continue
        bad = triviality_problems(conclusion(text))
        if bad:
            problems.append(field + ": TYPE IS TRIVIALLY DECIDABLE - the field says "
                            + repr(conclusion(text)) + " (" + bad[0]
                            + "), so no Surface can fail it")
            continue
        for f in frags:
            checked += 1
            if norm(f) not in text:
                problems.append(field + ": missing fragment " + repr(f)
                                + " in the TYPE (comments and the value do not count)")
    surf = root / "Midfall/Lowering/Surface.lean"
    if not surf.exists():
        problems.append("Surface.lean missing: %s" % surf)
    else:
        sbody = strip_comments(surf.read_text(encoding="utf-8"))
        for field, frags in SURFACE_PINS:
            text = field_text(sbody, field)
            if not text:
                problems.append("Surface." + field + ": PIN FIELD NOT FOUND")
                continue
            bad = triviality_problems(conclusion(text))
            if bad:
                problems.append("Surface." + field + ": PIN IS TRIVIALLY DECIDABLE - "
                                + repr(conclusion(text)) + " (" + bad[0] + ")")
                continue
            for f in frags:
                checked += 1
                if norm(f) not in text:
                    problems.append("Surface." + field + ": missing fragment "
                                    + repr(f))
        for dname, frags in DERIVED_CHECKS:
            # a derived check is a DEFINITION, so its body is the claim under test
            text = field_text(sbody, dname, whole=True)
            if not text:
                problems.append("Surface: derived check " + dname + " NOT FOUND")
                continue
            for f in frags:
                checked += 1
                if f not in text:
                    problems.append("Surface: " + dname + " no longer mentions " + repr(f)
                                    + " - R-60 S1: the import check must read the naming"
                                    + " field, not hard-code a name")
    if problems:
        print("STATEMENT FINGERPRINTS BROKEN (%d):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1
    print("ok: %d statement fragments present in the TYPE across %d LoweringCorrect "
          "fields, %d Surface pins and %d derived checks (comments stripped first)"
          % (checked, len(FINGERPRINTS), len(SURFACE_PINS), len(DERIVED_CHECKS)))
    return 0


if __name__ == "__main__":
    sys.exit(main())

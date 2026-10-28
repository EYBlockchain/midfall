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

P-ENV added a third kind of target: the TYPE OF A STRUCTURE FIELD in Inv.lean. The
EnvAgrees.omegaOrder clause was strengthened from `omega ^ n = 1` to
`orderExactly omega n`, and nothing else in the repository reads a structure field's
type - the duplicate-fact gate checks that a carrier EXISTS and that a pin names both
sides, and the fingerprints above read LoweringCorrect fields - so without an entry here
weakening the clause back would build clean, keep every KAT true and leave the degenerate
`omega = omegaInv = 1` domain accepted again. Each entry is (structure, field, required
fragments, forbidden fragments); the forbidden half matters, because a field that kept
the word `orderExactly` and dropped its second conjunct would pass a presence test.

Usage:  python3 scripts/check_statement_fingerprints.py [OBLIGATIONS.LEAN]
        python3 scripts/check_statement_fingerprints.py --root DIR
  --root DIR  read every tracked file under DIR instead of this script's parent's
              parent. Run it against a perturbed copy of the tree to show the gate
              reddens (R-41: a gate that has never been seen to fail is not a gate).
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_duplicate_facts import (ARROW, AND, norm, split_top, structures,
                                   strip_comments, triviality_problems)

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

# P-AST (docs/REVIEW.md R-62). The ten *_spec theorems in Lowering/Partials.lean are
# true as stated ONLY because each carries the blk pin: without it they quantify over every
# Surface, Surface.blk is free, and a planted 'return(0, 0)' satisfies every hypothesis and
# refutes the conclusion. Nothing else in the tree reads a theorem's binder list, so
# deleting one 'hblk' line would restore the false-as-stated quantifier with every other
# gate still green. These fragments are the gate against that, and against the pin being
# paraphrased into something no Surface can fail.
SPEC_FILE = "Midfall/Lowering/Partials.lean"
GEN_FILE = "Midfall/Lowering/GenAst.lean"
PARTIAL_SPEC_PINS = [
    ("vkLoading_spec", ["hblk : BlkIsEmitter S"], False),
    ("transcriptParser_spec", ["hblk : BlkIsEmitter S"], False),
    ("lagrange_spec", ["hblk : BlkIsEmitter S"], False),
    ("lagrange_progress_spec", ["hblk : BlkIsEmitter S"], False),
    ("quotientLin_spec", ["hblk : BlkIsEmitter S"], False),
    ("pcs_spec", ["hblk : BlkIsEmitter S"], False),
    ("finalPairing_spec", ["hblk : BlkIsEmitter S"], False),
    ("finalPairing_progress_spec", ["hblk : BlkIsEmitter S"], False),
    ("finalPairing_acc_spec", ["hblk : BlkIsEmitter S"], False),
    ("traceReturn_spec", ["hblk : BlkIsEmitter S"], False),
    # The pin itself must pin blk to the EMITTER and main to the emitted whole - not to a
    # self-equality, not to True. Its body IS the statement, so whole=True.
    ("BlkIsEmitter", ["S.blk q pv =", "GenAst.emitPartial pv q",
                      "S.L.main =", "GenAst.emitMain S.plan"], True),
    # The emitter must stay a function of the plan and keep the two FinalPairing arms
    # distinct, or the pin degenerates into a constant a placeholder could satisfy.
    ("emitPartial", ["emitFinalPairing pv", "emitPlaceholder q"], True),
    ("emitFinalPairingArms", ["emitAccBatch batch", "ec_pairing",
                              "PAIRING_RHS_MPTR", "PAIRING_LHS_MPTR"], True),
]

# P-ENV: the EnvAgrees clause types in Lowering/Inv.lean. (structure, field, must, must not)
INV_FILE = "Midfall/Lowering/Inv.lean"
ENV_CLAUSES = [
    ("EnvAgrees", "omegaOrder",
     ["Midfall.Assumptions.orderExactly vk.domain.omega vk.domain.n"],
     ["vk.domain.omega ^ vk.domain.n = 1"]),
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


def env_clause_text(body, struct, field):
    """The declaration text of `field` inside `structure struct`, read with the SAME
    structure parser the duplicate-fact gate uses, so the fragment is matched against the
    field of THAT structure and not against the first line in the file that mentions the
    name (a doc string that quotes the old clause would otherwise satisfy the test)."""
    return norm((structures(body).get(struct) or {}).get(field, (0, ""))[1])


def main():
    argv = sys.argv[1:]
    root = Path(__file__).resolve().parent.parent
    if "--root" in argv:
        root = Path(argv[argv.index("--root") + 1]).resolve()
        argv = [a for i, a in enumerate(argv)
                if a != "--root" and i != argv.index("--root") + 1]
    default = root / "Midfall/Lowering/Obligations.lean"
    ob = Path(argv[0]) if argv else default
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
    # P-AST: the blk pin on the ten *_spec theorems, and the shape of the pin and the
    # emitter it pins to. A theorem binder list is invisible to every other gate in this
    # repository, so this is the only thing that notices an "hblk" being deleted.
    spec = root / SPEC_FILE
    gen = root / GEN_FILE
    pbody = strip_comments(spec.read_text(encoding="utf-8")) if spec.exists() else None
    gbody = strip_comments(gen.read_text(encoding="utf-8")) if gen.exists() else None
    if pbody is None:
        problems.append("Partials.lean missing: %s" % spec)
    if gbody is None:
        problems.append("GenAst.lean missing: %s" % gen)
    if pbody is not None and gbody is not None:
        for name, frags, whole in PARTIAL_SPEC_PINS:
            in_gen = name in ("emitPartial", "emitFinalPairingArms")
            src, where = (gbody, "GenAst.") if in_gen else (pbody, "Partials.")
            text = field_text(src, name, whole)
            if not text:
                problems.append(where + name + ": DECLARATION NOT FOUND")
                continue
            if not whole:
                bad = triviality_problems(conclusion(text))
                if bad:
                    problems.append(where + name + ": TYPE IS TRIVIALLY DECIDABLE - "
                                    + repr(conclusion(text)) + " (" + bad[0]
                                    + "), so the pin says nothing")
            for fr in frags:
                checked += 1
                if norm(fr) not in text:
                    problems.append(where + name + ": missing fragment " + repr(fr))
    # P-ENV: the EnvAgrees clause types. A weakened clause elaborates, builds, and keeps
    # every KAT true - the degenerate domain simply stops being refutable - so this is
    # the only gate that can see it.
    inv = root / INV_FILE
    if not inv.exists():
        problems.append("Inv.lean missing: %s" % inv)
    else:
        ibody = strip_comments(inv.read_text(encoding="utf-8"))
        for struct, field, must, must_not in ENV_CLAUSES:
            text = env_clause_text(ibody, struct, field)
            if not text:
                problems.append("Inv.%s.%s: CLAUSE NOT FOUND - the field is no longer "
                                "declared, so nothing pins its type" % (struct, field))
                continue
            for fr in must:
                checked += 1
                if norm(fr) not in text:
                    problems.append("Inv.%s.%s: CLAUSE WEAKENED - the type no longer "
                                    "says %s (P-ENV: omegaOrder must require the EXACT "
                                    "order, or a generator equal to 1 satisfies it)"
                                    % (struct, field, repr(fr)))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("Inv.%s.%s: CLAUSE WEAKENED - the type contains the "
                                    "pre-P-ENV text %s" % (struct, field, repr(fr)))
    if problems:
        print("STATEMENT FINGERPRINTS BROKEN (%d):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1
    print("ok: %d statement fragments present in the TYPE across %d LoweringCorrect "
          "fields, %d Surface pins, %d derived checks, %d blk-pin declarations and "
          "%d EnvAgrees clause types (comments stripped first)"
          % (checked, len(FINGERPRINTS), len(SURFACE_PINS), len(DERIVED_CHECKS),
             len(PARTIAL_SPEC_PINS), len(ENV_CLAUSES)))
    return 0


if __name__ == "__main__":
    sys.exit(main())

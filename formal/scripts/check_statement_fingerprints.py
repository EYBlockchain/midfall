#!/usr/bin/env python3
"""Statement-fingerprint gate for Midfall/Lowering/Obligations.lean.

Why (P-SE stage 6, R-41): LoweringCorrect fields are STATEMENTS, not gated computations,
so no #eval gate reads a field text. Three perturbations proved it - replacing ZeroAbove
with True in verifier_sound, paraphrasing render_eq_print conjunct as a length equality,
and dropping the selector conjunct from only_two_outcomes - each built clean with every
gate still true. The only defence had been a hand-run verbatim diff against section Q.
This makes it a CI gate.

It does NOT claim byte equality: seven fields legitimately differ from the sketch by
recorded substitutions. It asserts each load-bearing FRAGMENT survives, so a paraphrase
that drops a conjunct or weakens a hypothesis fails even though it elaborates.
"""
import re
import sys
from pathlib import Path

FINGERPRINTS = [
    ("verifier_sound", ["ZeroAbove mem", "SoundSide S H cd",
        "obs.returnData = abiTrue", "LeanAccepts S H cd", "SupportedS S S.o",
        "DeploymentW S W H vkAddr qAddr", "Eip2537.Holds"]),
    ("verifier_complete", ["CompleteSide S H cd", "EnvAgrees", "G1CodecLaws",
        "LeanAccepts S H cd", "returnView (callState"]),
    ("only_two_outcomes", ["fnSigVerifyProof", "obs.isRevertOrHalt",
        "obs.worldUnchanged", "returnView (callState"]),
    ("ir_refines", ["S.irCheck ir = true", "WorldLocal", "ObsEquiv",
        "RunContractIR", "RunShell"]),
    ("render_eq_print", ["SyntaxEq.stmtsBeq", "S.astOfMain o = some ast", "L.main"]),
    ("end_to_end_noAcc", ["S.cfg.accumulator = none",
        "inst.size = S.cfg.numInstances", "fromRepackError", "verifyNative",
        "repackProof", "encodeCalldata", "RunContractIR"]),
    ("lowering_equivalence", ["RunContractIR", "obs.isReturn",
        "obs.returnData = abiTrue", "LeanAccepts S H cd",
        "S.irCheck ir = true", "\u2203 obs"]),
    ("qvm_validated_noBoundsFault", ["readPastEnd", "constSlotOutOfRange"]),
    ("points_subgroup_checked", ["IsAlignedSubslice"]),
    ("accFixedBases_producer", [chr(34) + "-G" + chr(34), "negate = true"]),
]

WS = re.compile(r"\s+")
WORD_START = re.compile(r"^[A-Za-z_]")
DECL = re.compile(r"^\s*(?:theorem |lemma |def |example )?")


def norm(s):
    return WS.sub(" ", s)


def field_text(body, field):
    lines = body.splitlines()
    pat = re.compile(DECL.pattern + re.escape(field) + r"\b")
    start = None
    for i, ln in enumerate(lines):
        if pat.match(ln):
            start = i
            break
    if start is None:
        return ""
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
    return norm(" ".join(lines[start:end]))


def main():
    root = Path(__file__).resolve().parent.parent
    default = root / "Midfall/Lowering/Obligations.lean"
    ob = Path(sys.argv[1]) if len(sys.argv) > 1 else default
    if not ob.exists():
        print("check_statement_fingerprints: no such file", ob, file=sys.stderr)
        return 2
    body = ob.read_text(encoding="utf-8")
    problems = []
    checked = 0
    for field, frags in FINGERPRINTS:
        text = field_text(body, field)
        if not text:
            problems.append(field + ": FIELD NOT FOUND")
            continue
        for f in frags:
            checked += 1
            if norm(f) not in text:
                problems.append(field + ": missing fragment " + repr(f))
    if problems:
        print("STATEMENT FINGERPRINTS BROKEN (%d):" % len(problems))
        for p in problems:
            print("  " + p)
        return 1
    print("ok: %d statement fragments present across %d LoweringCorrect fields"
          % (checked, len(FINGERPRINTS)))
    return 0


if __name__ == "__main__":
    sys.exit(main())

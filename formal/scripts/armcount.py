#!/usr/bin/env python3
"""armcount.py - the QVM arm counts, computed from the tree rather than hand-tallied.

Why this exists: the orchestrator had been quoting '20 reference-tied arms' across several cards as if it
were a measured figure. FTIE tried to reproduce it and could not: there are 23 emitted qArmValueAll
triples and 23 arms with a qStepValue lemma, and the intersection is 21. It carried the orchestrator's
number forward and flagged it as a ledger figure rather than a count. This script makes the number
derivable so nobody has to trust prose again.

Definitions used, stated so they can be argued with:
  ARM        - a `def qArmBody<X>` in GenAstQvm.lean (the lifted switch arm, QEMIT4).
  TRIPLE     - a `theorem qArmValueAll_<x>` in QuotientFrame.lean or QuotientArms.lean (emitted-side
               contract: running the emitted body reaches the stated post-env/state).
  QSTEPVAL   - a `theorem qStepValue_<x>` in QuotientFrame.lean section B (reference-side value).
  TIED       - an arm with BOTH a triple and a qStepValue. This is 'reference-tied'. A triple alone is
               emitted-to-emitted; a qStepValue alone is a reference value with no emitted proof.

Note that TIED is an over-count in one respect and an under-count in another, and both are reported:
  over  - the limb triples are emitted-to-emitted walks (lin7From/bilin7RowFrom) whose hlimbs
          hypothesis is never used to reach the reference, so a limb arm with a qStepValue is not truly
          tied until PG_limbCountAgrees is ruled on.
  under - the two fold arms now have a genuine reference tie via QuotientFoldTie.lean without having a
          named qStepValue at all.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1] / "Midfall"
GEN = ROOT / "Lowering" / "GenAstQvm.lean"
FRAME = ROOT / "LoweringV3" / "QuotientFrame.lean"
ARMS = ROOT / "LoweringV3" / "QuotientArms.lean"
TIE = ROOT / "LoweringV3" / "QuotientFoldTie.lean"


def names(path, pattern):
    if not path.exists():
        return set()
    return set(re.findall(pattern, path.read_text(encoding="utf-8", errors="replace")))


def main():
    arms = names(GEN, r"def qArmBody([A-Za-z0-9_]+)")
    triples = names(FRAME, r"theorem qArmValueAll_([A-Za-z0-9_]+)") | names(
        ARMS, r"theorem qArmValueAll_([A-Za-z0-9_]+)")
    qstep = names(FRAME, r"theorem qStepValue_([A-Za-z0-9_]+)")
    foldtie = TIE.exists()

    lower = lambda s: {x.lower() for x in s}
    tri_l, step_l = lower(triples), lower(qstep)
    tied = tri_l & step_l

    print("arms defined (qArmBody*)        :", len(arms))
    print("emitted-side triples           :", len(tri_l))
    print("arms with a named qStepValue   :", len(step_l))
    print("REFERENCE-TIED (both)          :", len(tied))
    print("  triple but NO qStepValue     :", len(tri_l - step_l), sorted(tri_l - step_l))
    print("  qStepValue but NO triple     :", len(step_l - tri_l), sorted(step_l - tri_l))
    print("fold reference tie file present:", foldtie,
          "(adds fold arms without a named qStepValue)")
    print()
    print("CAVEAT: limb arms in REFERENCE-TIED are emitted-to-emitted until PG_limbCountAgrees is")
    print("ruled on, so the honest reference-tied count is this number MINUS any limb arm it includes.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

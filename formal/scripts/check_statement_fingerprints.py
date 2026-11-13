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
    # P-AST3b: the four accumulator words PlanView now carries. The pin is ONE equation
    # over the 4-tuple, so a paraphrase that keeps the tuple and drops the derivation - or
    # keeps the derivation and drops one of the four words - loses a fragment here.
    ("plan_accExpectations", ["plan.expectedHasAccumulatorWord",
                              "plan.expectedNumAccLimbBits",
                              "accWordsOfEncoding cfg.accumulator"]),
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
# P-PLANVIEW: the dispatch moved to its own module, because emitPartial has to see the
# pcs emitter and GenAstPcs imports GenAst. The NAME is unchanged - Midfall.Lowering.GenAst.emitPartial
# - because a Lean namespace is not a file; only the source this gate reads from moved.
DISPATCH_FILE = "Midfall/Lowering/GenAstDispatch.lean"
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
    #
    # P-PLANVIEW CHANGED THE SECOND FRAGMENT, and the change is the point rather than a
    # side effect: the old pin was "emitPlaceholder q", i.e. the dispatch had a wildcard arm
    # that fell through to a dummy. The dispatch is now exhaustive over the seven partials,
    # so that fragment is not merely absent but WRONG - a future package that reintroduced a
    # fall-through would be the regression, and this line refuses it. "emitPcsFromPlan pv" is
    # the seventh arm; the emptiness of placeholderPartials is proved in the Lean tree by
    # GenAstDispatch.placeholderPartials_nil, which no text gate has to duplicate.
    ("emitPartial", ["emitFinalPairing pv", "emitPcsFromPlan pv", "emitTraceReturn pv"],
     True),
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

# P-HOLDS (docs/REVIEW.md R-63): the six Eip2537.Holds clause types in
# Midfall/Assumptions/Eip2537.lean. P-CURVE reported that no text gate read them at all, so
# weakening g1Decodes - the defect R-63 found, and the one the repair fixes - reddened nothing
# and the build was the only defence. A hypothesis structure is a STATEMENT, and the only thing
# that notices a clause being relaxed to True or to a one-directional implication is this file.
#
# Each entry is (structure, field, must, must_not), read with the SAME structure parser the
# duplicate-fact gate uses so a fragment is matched against the field of THAT structure and not
# against a doc string that quotes it (comments are stripped first). The must_not half makes
# the g1Decodes entry a two-sided pin: the live clause must carry the frame-width condition and
# must not be the pre-repair quantifier, while g1DecodesOld must be exactly the pre-repair
# quantifier and must NOT acquire the width condition. Repair one and forget the other and the
# gate reddens.
HOLDS_FILE = "Midfall/Assumptions/Eip2537.lean"
HOLDS_CLAUSES = [
    # G1VALID: every encoding the codec produces must be a point the byte validators accept.
    # g1PointAddValid is the WEAKER validator (it skips the r-torsion check, which is why
    # EIP-2537's G1ADD accepts off-subgroup points), so naming it here would silently drop the
    # subgroup half of the clause - the distinction g1FrameCodecKats_ok line 7 pins.
    ("Eip2537.Holds", "g1Valid",
     ["\u2200 Q : G\u2081", "\u2203 pt, g1Of? (c.toEip Q) = some pt",
      "g1PointMsmValid pt = true"],
     ["g1PointAddValid", "= True"]),
    ("Eip2537.Holds", "g2Valid",
     ["\u2200 R : G\u2082", "\u2203 pt, g2Of? (c\u2082.toEip R) = some pt",
      "g2PointValid pt = true"],
     ["g2PointAddValid", "= True"]),
    # PAIRING2: an IFF, not an implication. One direction is all a soundness proof needs and
    # is the shape a package under pressure would write; the additive identity 0 and the two
    # pairs are what make it the precompile's answer.
    ("Eip2537.Holds", "pairing2",
     ["product (pairingFrame [", "= true \u2194",
      "P.e (Additive.ofMul P\u2081) (Additive.ofMul Q\u2081) +",
      "P.e (Additive.ofMul P\u2082) (Additive.ofMul Q\u2082) = 0"],
     ["msmSpecific", "pairing_iff"]),
    # G1ADD / G1MSM1: the frame the precompile runs, the codec's own bytes on both sides, and
    # the group law / scalar action it must agree with. g1AddValidInput and g1MsmValidInput are
    # the LENGTH validators - true of far more frames than the outputs - so a clause that names
    # one instead of g1AddOutput/g1MsmOutput has stopped saying anything about arithmetic.
    ("Eip2537.Holds", "g1Add",
     ["\u2200 P\u2081 P\u2082 : G\u2081",
      "g1AddOutput (g1AddFrame (c.toEip P\u2081) (c.toEip P\u2082)) =",
      "some (c.toEip (P\u2081 * P\u2082))"],
     ["g1AddValidInput", "= True"]),
    ("Eip2537.Holds", "g1Msm1",
     ["g1MsmOutput (g1MsmFrame [(c.toEip Q, frToInputBE s)]) =",
      "some (c.toEip (gsmul s Q))"],
     ["g1MsmValidInput", "= True"]),
    # G1DECODES, the repaired clause: the frame-width condition is REQUIRED and the pre-repair
    # quantifier is FORBIDDEN. R-63 proved the forbidden text unsatisfiable for every codec on
    # every prime-order group; the pinned old text below is where it lives now.
    ("Eip2537.Holds", "g1Decodes",
     ["\u2200 b : Bytes, b.size == g1Bytes \u2192",
      "(\u2203 pt, g1Of? b = some pt \u2227 g1PointMsmValid pt = true) \u2192",
      "\u2203 Q, c.ofEip? b = some Q \u2227 c.toEip Q = b"],
     ["\u2200 b : Bytes, (\u2203 pt, g1Of? b = some pt"]),
]

# The two named decode propositions and the pinned old structure, as DEFINITIONS: for a def the
# BODY is the statement, so these are matched against the whole declaration (whole=True), the
# same way Surface.irCheck is.
HOLDS_DEFS = [
    ("g1DecodesWidth",
     ["\u2200 b : Bytes, b.size == g1Bytes \u2192",
      "\u2203 Q, c.ofEip? b = some Q \u2227 c.toEip Q = b"],
     ["\u2200 b : Bytes, (\u2203 pt, g1Of? b = some pt"]),
    ("g1DecodesOld",
     ["\u2200 b : Bytes, (\u2203 pt, g1Of? b = some pt \u2227 g1PointMsmValid pt = true) \u2192",
      "\u2203 Q, c.ofEip? b = some Q \u2227 c.toEip Q = b"],
     ["b.size == g1Bytes"]),
    ("Eip2537.HoldsOld",
     ["Eip2537.Holds c c\u2082 product \u2227 g1DecodesOld c"],
     []),
]

# ---------------------------------------------------------------------------
# P-STATGATE: the frozen normative file, Midfall/Statements.lean.
#
# WHY THIS SECTION EXISTS. This gate read four files and never the one that matters most.
# Statements.lean is the surface the whole project states its theorem on, and its only
# defence was the SHA-256 - which detects any change and validates NONE of the content.
# P-REPIN proved the hole by deleting 'hc : E.g1.compressedRoundtrip' from the frozen
# statement: the build stayed green and every structural gate stayed green with it, so the
# known-false theorem it had just spent a whole package removing could have been put back by
# a future re-pin with nothing objecting. This is the fourth structural gate blind spot of
# the session after theorem-binder hypotheses, EnvAgrees clause types and the Holds clause
# texts - and the largest, because it was on the normative file.
#
# PIN BOTH DIRECTIONS. A presence-only gate passes on a statement weakened by ADDING
# hypotheses until nothing satisfies it, and passes on a statement whose shape was replaced
# by something that merely mentions the same names. So every clause here is two-sided -
# `must` is the repaired shape, `must_not` is the refuted one - and each statement is
# additionally pinned EXACTLY (STATEMENTS_EXACT). The exact pin is not the hash again: the
# hash proves the file is the file, this proves what the file means. A legitimate amendment
# under the D-P27 precedent has to move the pin in this script, which is where a reviewer
# sees the claim being signed off rather than watched for drift.
#
# Comments are stripped before any of this, which matters here more than anywhere else in
# this gate: the frozen doc strings QUOTE the refuted texts verbatim ('Spec.accepts H F
# params vk inst ms'), so a must_not read against raw text would fail on the file exactly as
# it should stand. The doc-string provenance checks are the one part that reads raw text, and
# they are matched only against the doc string ATTACHED to the named declaration.
STATEMENTS_FILE = "Midfall/Statements.lean"
REPAIR_FILE = "Midfall/Instances/StatementsRepair.lean"

# The COMPLETE set of top-level declarations the normative file is allowed to have. Without
# this the pins below only protect the three statements they name: a fourth one could be
# appended to the frozen file, unpinned and unprovenanced, and every clause here would stay
# green on it. The hash reddens on the edit; this reddens on the CLAIM.
STATEMENTS_DECLS = ["verifyNative_iff_msgs", "verifyMsgs_iff_spec", "contractRef_noAcc"]

# (theorem, must, must_not), read on the STATEMENT: binder list plus type, value cut.
STATEMENTS_PINS = [
    ("verifyNative_iff_msgs",
     # The codec law IS the repair. Naming the projection E.g1.compressedRoundtrip rather
     # than the bare word compressedRoundtrip is the point: a hypothesis about some other
     # object, or a placeholder of the same name, would pass a looser fragment.
     ["(hc : E.g1.compressedRoundtrip)",
      "verifyNative (G\u209c := G\u209c) E F params vk inst \u03c0 = .ok () \u2194",
      "\u2203 ms, decodeRust (G\u209c := G\u209c) E F vk inst \u03c0 = some ms",
      "verifyMsgs (G\u209c := G\u209c) E keccak256 F params vk inst ms = .ok ()"],
     # The refuted shape: the text as frozen at formal-baseline-v1, with no binder at all.
     # And the hypothesis pile-up the repair deliberately did NOT make - attack.md line 107
     # FIX shows p <= 2^256 decorative here, so if it comes back the statement has grown a
     # hypothesis nobody asked for and the pin has to be re-argued, not quietly widened.
     ["verifyNative_iff_msgs :", "p \u2264 2 ^ 256", "p \u2264 2^256",
      "p <= 2 ^ 256", "p <= 2^256", "\u2194 True", "\u2194 trivial"]),
    ("verifyMsgs_iff_spec",
     ["(hwf : vk.WellFormed F)",
      "(verifyMsgs (G\u209c := G\u209c) E H F params vk inst ms).isOk \u2194",
      "Spec.accepts E H F params vk inst ms"],
     # The refuted shape: an E-free right-hand side beside an E-dependent left-hand side.
     # survey.md, L0 area note: "a predicate that ignores E cannot be equivalent for every E".
     ["Spec.accepts H F params vk inst ms", "verifyMsgs_iff_spec :",
      "\u2194 True", "\u2194 trivial"]),
    ("contractRef_noAcc",
     ["Lowering.ContractRefAccepts (p := p) (G\u209c := G\u209c) E keccak256 params vk inst ms \u2194",
      "verifyMsgs (G\u209c := G\u209c) E keccak256 Features.solidity params vk inst ms = .ok ()"],
     # Its text is unchanged by D-P27 - it is marked, not amended - so the refuted drift to
     # refuse is the two edits this statement is most likely to suffer: being generalised
     # over H to look like the proved lemma it was superseded BY (that lemma lives in
     # Lowering/SemanticEquivalence.lean and is not the frozen obligation), or being emptied
     # out now that it is known to be derivable.
     ["ContractRefAccepts (p := p) (G\u209c := G\u209c) E H params", "\u2194 True",
      "\u2194 trivial", "contractRef_noAcc := trivial"]),
]

# The whole statement, exactly, modulo whitespace. See the note above: this is the pin a
# re-pin has to move deliberately, with a reason, in the file that gates it.
STATEMENTS_EXACT = {
    "verifyNative_iff_msgs":
        "theorem verifyNative_iff_msgs (hc : E.g1.compressedRoundtrip) : "
        "verifyNative (G\u209c := G\u209c) E F params vk inst \u03c0 = .ok () \u2194 "
        "\u2203 ms, decodeRust (G\u209c := G\u209c) E F vk inst \u03c0 = some ms \u2227 "
        "verifyMsgs (G\u209c := G\u209c) E keccak256 F params vk inst ms = .ok ()",
    "verifyMsgs_iff_spec":
        "theorem verifyMsgs_iff_spec (hwf : vk.WellFormed F) : "
        "(verifyMsgs (G\u209c := G\u209c) E H F params vk inst ms).isOk \u2194 "
        "Spec.accepts E H F params vk inst ms",
    "contractRef_noAcc":
        "theorem contractRef_noAcc : "
        "Lowering.ContractRefAccepts (p := p) (G\u209c := G\u209c) E keccak256 params vk inst ms \u2194 "
        "verifyMsgs (G\u209c := G\u209c) E keccak256 Features.solidity params vk inst ms = .ok ()",
}

# The four `variable` commands, in file order, normalised. A Lean theorem's statement is its
# VARIABLE CONTEXT plus its own binders plus its type. STATEMENTS_PINS and STATEMENTS_EXACT
# cover the last two; without this, the fourth line of the same attack - editing a
# `variable` line, or slipping a hypothesis in through one - is invisible to every gate.
STATEMENTS_BINDERS = [
    "variable {p : \u2115} [Fact (Nat.Prime p)] {G\u2081 G\u2082 G\u209c : Type} [Group G\u2081] [Group G\u2082] "
    "[Group G\u209c] [PrimeOrderWith G\u2081 p] [PrimeOrderWith G\u2082 p] [PrimeOrderWith G\u209c p] "
    "[Module (ZMod p) (Additive G\u2081)] [Module (ZMod p) (Additive G\u2082)] "
    "[Module (ZMod p) (Additive G\u209c)] [P : AdmissiblePairing G\u2081 G\u2082 G\u209c]",
    "variable (E : VerifierEnv p G\u2081 G\u2082 G\u209c) (F : Features) "
    "(params : ParamsVerifierKZG G\u2081 G\u2082) "
    "(vk : VerifyingKey (Fr p) G\u2081) (inst : Array (Fr p)) (\u03c0 : Bytes)",
    "variable (E : VerifierEnv p G\u2081 G\u2082 G\u209c) (H : Hash) (F : Features) "
    "(params : ParamsVerifierKZG G\u2081 G\u2082) "
    "(vk : VerifyingKey (Fr p) G\u2081) (inst : Array (Fr p)) "
    "(ms : List (Msg (Fr p) G\u2081))",
    "variable (E : VerifierEnv p G\u2081 G\u2082 G\u209c) (params : ParamsVerifierKZG G\u2081 G\u2082) "
    "(vk : VerifyingKey (Fr p) G\u2081) "
    "(inst : Array (Fr p)) (ms : List (Msg (Fr p) G\u2081))",
]

# The trusted surface, pinned exactly and in order. P-REPIN found two dead imports here
# (Security.SRS, Security.Challenges) that widen what the normative file may assume for no
# reason, and D-P27 was deliberately too narrow to remove them. This pin takes neither side
# of that decision; it makes the surface VISIBLE, so that adding an import reddens a gate
# with a reason attached and the pending removal is recorded rather than lost.
STATEMENTS_IMPORTS = [
    "import Midfall.Common.Curve",
    "import Midfall.Common.Bytes",
    "import Midfall.Common.Codec",
    "import Midfall.Common.Keccak",
    "import Midfall.Halo2.Exec.Native",
    "import Midfall.Halo2.Exec.VerifyingKey",
    "import Midfall.Halo2.Spec.Piop",
    "import Midfall.Lowering.Types",
    "import Midfall.Security.SRS",
    "import Midfall.Security.Challenges",
]

# (theorem, must, must_not) on the DOC STRING attached to the declaration, read against the
# RAW file. This is what "marked superseded" has to mean for a gate: the marker is prose, so
# pinning the prose is the only way to gate it. The must half names the decision (D-P27),
# the action taken, and the D-P23 evidence the amendment rests on; the must_not half refuses
# a premise P-REPIN PROVED false rather than merely one it dislikes.
STATEMENTS_DOCS = [
    ("verifyNative_iff_msgs",
     ["AMENDED under D-P27", "compressedRoundtrip", "repair1_satisfiable",
      "repair1_old_false_at_degEnv", "repair1_old_universal_refuted"],
     []),
    ("verifyMsgs_iff_spec",
     ["AMENDED under D-P27", "repair2_old_refuted", "repair2_new_shape_inhabited"],
     []),
    ("contractRef_noAcc",
     ["SUPERSEDED under D-P27", "contractRef_noAcc_of_semanticEquivalence",
      "repair3_rederived", "repair3_hash_is_not_forced",
      # The original note claimed the shape was frozen "before the port exists", and
      # repair3_rederived IS that port. The phrase still appears in the doc string - as a
      # QUOTATION being refuted - so what is pinned is the refutation, not the absence of
      # the words. A gate that reddens on a quoted refutation teaches people to delete the
      # quotation, which is the opposite of what D-P23 wants.
      "is refuted by the port existing"],
     []),
]

# The witnesses and retained refutations the frozen doc strings cite, pinned two-sided for
# the same reason as the statements. The OLD texts are kept as named propositions so that
# each refutation is a theorem about the text that was really there; an old text quietly
# upgraded to the new shape would make every refutation vacuous - it would refute something
# nobody claimed. Entries are (decl, whole, must, must_not); whole=True for a DEFINITION,
# whose BODY is the statement, the same convention HOLDS_DEFS uses.
REPAIR_PINS = [
    ("verifyNative_iff_msgsOld", True,
     ["def verifyNative_iff_msgsOld",
      "verifyNative (G\u209c := Exp 17) E F params vk inst pi = .ok () \u2194"],
     ["compressedRoundtrip"]),
    ("verifyMsgs_iff_specOld", True,
     ["\u2203 (S : Hash \u2192 Features \u2192"],
     # The pinned old claim is about an E-INDEPENDENT predicate. Give S an environment and
     # repair2_old_refuted stops refuting anything.
     ["VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) \u2192 Hash \u2192"]),
    ("repair1_satisfiable", False,
     ["\u2203 (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17)), E.g1.compressedRoundtrip"], []),
    ("repair1_law_is_not_free", False,
     ["\u00ac (expG1Codec (p := 17)).compressedRoundtrip"], []),
    ("repair1_old_false_at_degEnv", False,
     ["\u00ac verifyNative_iff_msgsOld degEnv Features.solidity expPrm n2Vk n2Inst (n2Proof n2Pi)"],
     []),
    ("repair2_old_refuted", False, ["\u00ac verifyMsgs_iff_specOld"], []),
    ("repair2_new_shape_inhabited", False,
     ["VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) \u2192 Hash \u2192"], []),
    ("repair3_rederived", False,
     ["ContractRefAccepts E keccak256 params vk inst ms = true \u2194"], []),
    ("repair3_hash_is_not_forced", False,
     ["\u2203 (H : Hash) (b : Bytes), H b \u2260 keccak256 b"], []),
    # The witness codec must keep the law it was built to prove, or repair1_satisfiable
    # becomes a claim about a codec that does not satisfy it.
    ("canonG1Codec_compressedRoundtrip", False,
     ["canonG1Codec.compressedRoundtrip"], []),
]


def decl_statement(lines, name, whole=False):
    """field_text for a declaration whose NAME may end the line, as it does when the
    binders are wrapped onto the next one (`theorem repair3_rederived` then `(E : ...)`).
    field_text requires a colon or a paren after the name, so it misses those; this allows
    end-of-line as well and is used only on the two files this section reads."""
    pat = re.compile(r"^\s*(?:theorem |lemma |def |example )?"
                     + re.escape(name) + r"\s*(?::|\(|\{|$)")
    for i, ln in enumerate(lines):
        if pat.match(ln):
            return field_type(lines, i, whole)
    return ""


def variable_blocks(body):
    """Every top-level `variable` command, joined across its continuation lines and
    normalised, in file order."""
    out, cur = [], None
    for ln in body.splitlines():
        s = ln.strip()
        if ln.startswith("variable"):
            if cur is not None:
                out.append(norm(cur))
            cur = s
            continue
        if cur is None:
            continue
        if not s or not ln.startswith((" ", "\t")):
            out.append(norm(cur))
            cur = None
            continue
        cur += " " + s
    if cur is not None:
        out.append(norm(cur))
    return out


DOC_NAME = re.compile(r"^\s*(?:theorem |lemma |def |example )?([A-Za-z_][A-Za-z0-9_.']*)")


def docstring_of(raw, name):
    """The doc string ATTACHED to the declaration `name` in the raw text, normalised, or ""
    if it has none. Read on raw text on purpose - this is a check ON prose - but scoped to
    the block that ends immediately above the declaration, so a doc string elsewhere in the
    file that happens to use the same words cannot satisfy it."""
    lines = raw.splitlines()
    for i, ln in enumerate(lines):
        m = DOC_NAME.match(ln)
        if m is None or m.group(1) != name:
            continue
        if not re.search(re.escape(name) + r"\s*(?::|\(|$)", ln):
            continue
        j = i - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j < 0 or not lines[j].strip().endswith("-/"):
            return ""
        k = j
        while k >= 0 and not lines[k].strip().startswith("/--"):
            k -= 1
        if k < 0:
            return ""
        return norm(" ".join(lines[k:j + 1]))
    return ""


# The definitions the frozen statements CITE. Pinning only the frozen text leaves the
# obvious way round: keep `hc : E.g1.compressedRoundtrip` word for word and hollow out
# `compressedRoundtrip` itself, or keep `Spec.accepts E H ...` and define `accepts` to a
# constant. Neither edit touches Statements.lean, so the hash stays green WITH the hollow
# statement. These are the two cited definitions a repair could be undone through without
# touching the frozen file at all. The rest of the cited surface - `verifyNative`,
# `decodeRust`, `verifyMsgs`, `ContractRefAccepts`, `VerifierEnv`, `vk.WellFormed` - is
# enumerated as remaining unprotected surface in the package report, NOT silently claimed
# as covered here.
FROZEN_CITED_DEFS = [
    ("Midfall/Common/Codec.lean", "G1Codec.compressedRoundtrip", True,
     ["\u2200 b : Bytes, \u2200 P : G\u2081, c.ofCompressed? b = some P \u2192 "
      "c.toCompressed P = b"],
     # '= True' is the hollowing; the second is the ENCODER-FIRST form that
     # Common/Codec.lean:97-105 records as deliberately rejected, because it is false of
     # any representation with redundant structure. If it came back the frozen hypothesis
     # would be a different - and unsatisfiable - law while the statement text was unchanged.
     ["= True", "\u2200 P : G\u2081, c.ofCompressed? (c.toCompressed P)"]),
    ("Midfall/Halo2/Spec/Piop.lean", "accepts", True,
     ["def accepts (E : VerifierEnv p G\u2081 G\u2082 G\u209c) (H : Hash) (F : Features)",
      ": Prop := sorry"],
     # The E-free arity D-P27 removed, and the constant that would make statement 2 say
     # nothing. It must stay the registered Phase 4 hole: that is what 'sorry' means here.
     ["def accepts (H : Hash", ": Prop := True", ":= True"]),
]

REPAIR_CITE = re.compile(r"repair\d_[A-Za-z0-9_]+")

# A hypothesis replaced by a placeholder elaborates, keeps the binder NAME the doc string
# cites, and says nothing: '(hc : True)' is exactly where a statement drifts under pressure.
# triviality_problems reads the CONCLUSION and cannot see it, and the conclusion of a frozen
# statement is an iff that is never trivially decidable - so the binder list needs its own
# rule, because that is where a frozen hypothesis actually lives.
PLACEHOLDER_BINDER = re.compile(r"\((\w+) : (?:True|trivial)\)")

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
    disp = root / DISPATCH_FILE
    dbody = strip_comments(disp.read_text(encoding="utf-8")) if disp.exists() else None
    if pbody is None:
        problems.append("Partials.lean missing: %s" % spec)
    if gbody is None:
        problems.append("GenAst.lean missing: %s" % gen)
    if dbody is None:
        problems.append("GenAstDispatch.lean missing: %s" % disp)
    if pbody is not None and gbody is not None and dbody is not None:
        for name, frags, whole in PARTIAL_SPEC_PINS:
            in_gen = name in ("emitFinalPairingArms",)
            if name == "emitPartial":
                src, where = (dbody, "GenAstDispatch.")
            elif in_gen:
                src, where = (gbody, "GenAst.")
            else:
                src, where = (pbody, "Partials.")
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
    # P-HOLDS: the six Eip2537.Holds clause types, and the named decode propositions the
    # repair pins. A weakened clause elaborates, builds, and keeps every KAT true - the
    # unsatisfiable demand simply stops being refutable - so this is the only text gate that
    # can see the R-63 regression coming back.
    holds = root / HOLDS_FILE
    if not holds.exists():
        problems.append("Eip2537.lean missing: %s" % holds)
    else:
        hbody = strip_comments(holds.read_text(encoding="utf-8"))
        for struct, field, must, must_not in HOLDS_CLAUSES:
            text = env_clause_text(hbody, struct, field)
            if not text:
                problems.append("Holds.%s.%s: CLAUSE NOT FOUND - the field is no longer "
                                "declared, so nothing pins its type" % (struct, field))
                continue
            for fr in must:
                checked += 1
                if norm(fr) not in text:
                    problems.append("Holds.%s.%s: CLAUSE WEAKENED - the type no longer "
                                    "says %s (P-HOLDS: the six Holds clauses are statements "
                                    "and no other gate reads them)"
                                    % (struct, field, repr(fr)))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("Holds.%s.%s: CLAUSE WEAKENED - the type contains %s"
                                    % (struct, field, repr(fr)))
        for dname, must, must_not in HOLDS_DEFS:
            text = field_text(hbody, dname, whole=True)
            if not text:
                problems.append("Eip2537." + dname + ": DECLARATION NOT FOUND - the "
                                "regression pin has been deleted")
                continue
            for fr in must:
                checked += 1
                if norm(fr) not in text:
                    problems.append("Eip2537." + dname + ": no longer says " + repr(fr))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("Eip2537." + dname + ": must stay the pinned OLD text "
                                    "and now contains " + repr(fr))
    # ---- P-STATGATE: the frozen normative file --------------------------------
    # Every clause below is two-sided; see the note on STATEMENTS_PINS.
    st = root / STATEMENTS_FILE
    if not st.exists():
        problems.append("Statements.lean missing: %s - the frozen normative file has no "
                        "text gate at all, which is the hole P-STATGATE closes" % st)
    else:
        sraw = st.read_text(encoding="utf-8")
        slines = strip_comments(sraw).splitlines()
        imps = [norm(l) for l in slines if l.startswith("import ")]
        if imps != list(STATEMENTS_IMPORTS):
            problems.append("Statements: TRUSTED SURFACE CHANGED - imports are %s, pinned %s. "
                            "Adding one widens what the normative file may assume; removing "
                            "one (the two dead imports P-REPIN flagged, Security.SRS and "
                            "Security.Challenges) is a statement-surface decision this gate "
                            "does not take on the human's behalf."
                            % (imps, list(STATEMENTS_IMPORTS)))
        from check_frozen_axioms import frozen_declarations
        found = [d.split(".")[-1] for d in frozen_declarations(st)]
        for extra in [d for d in found if d not in STATEMENTS_DECLS]:
            problems.append("Statements: UNPINNED FROZEN STATEMENT %s - a declaration has "
                            "entered the normative file that nothing here pins and no doc "
                            "string explains; the hash reddens on the edit, this reddens on "
                            "the claim" % extra)
        for gone in [d for d in STATEMENTS_DECLS if d not in found]:
            problems.append("Statements: %s is no longer a top-level declaration of the "
                            "normative file - deleted, renamed, or demoted below a section"
                            % gone)
        vbs = variable_blocks("\n".join(slines))
        if len(vbs) != len(STATEMENTS_BINDERS):
            problems.append("Statements: BINDER CONTEXT CHANGED - %d `variable` commands "
                            "found, %d pinned. The variable block is part of the statement "
                            "of every theorem in this file."
                            % (len(vbs), len(STATEMENTS_BINDERS)))
        for i, want in enumerate(STATEMENTS_BINDERS):
            checked += 1
            got = vbs[i] if i < len(vbs) else "(absent)"
            if got != want:
                problems.append("Statements: binder block %d WEAKENED OR MOVED - found %s, "
                                "pinned %s" % (i + 1, repr(got), repr(want)))
        for name, must, must_not in STATEMENTS_PINS:
            text = decl_statement(slines, name)
            if not text:
                problems.append("Statements." + name + ": FROZEN DECLARATION NOT FOUND - it "
                                "has been deleted, renamed, or moved out of the normative file")
                continue
            bad = triviality_problems(conclusion(text))
            if bad:
                problems.append("Statements." + name + ": CONCLUSION IS TRIVIALLY DECIDABLE - "
                                + repr(conclusion(text)) + " (" + bad[0]
                                + "), so the statement no longer constrains anything")
                continue
            for h in PLACEHOLDER_BINDER.findall(text):
                problems.append("Statements." + name + ": HYPOTHESIS PLACEHOLDER - the binder "
                                "(" + h + " : True) is decidable without the object it names, "
                                "so the D-P27 hypothesis has been hollowed out while keeping "
                                "its name")
            if norm(STATEMENTS_EXACT[name]) != text:
                problems.append("Statements." + name + ": FROZEN TEXT MOVED - the statement is " 
                                "no longer the D-P27-repaired text this gate pins. A re-pin "
                                "must move STATEMENTS_EXACT in "
                                "scripts/check_statement_fingerprints.py and say why; "
                                "re-pinning the SHA-256 alone is not a sign-off.")
            for f in must:
                checked += 1
                if norm(f) not in text:
                    problems.append("Statements." + name + ": REPAIR MISSING - the statement "
                                    "no longer says %s (D-P27: this is the hypothesis or the "
                                    "threaded argument that made the frozen text true)"
                                    % repr(f))
            for f in must_not:
                if norm(f) in text:
                    problems.append("Statements." + name + ": REFUTED SHAPE BACK - the "
                                    "statement contains %s, the form whose refutation "
                                    "StatementsRepair.lean retains" % repr(f))
        cited = set()
        for name, must, must_not in STATEMENTS_DOCS:
            d = docstring_of(sraw, name)
            if not d:
                problems.append("Statements." + name + ": NO DOC STRING - the amendment "
                                "provenance has been stripped, so the file no longer records "
                                "why it differs from the plan sketch it was frozen from")
                continue
            for f in must:
                checked += 1
                if f not in d:
                    problems.append("Statements." + name + ": DOC PROVENANCE MISSING - the "
                                    "doc string no longer says %s" % repr(f))
            for f in must_not:
                if f in d:
                    problems.append("Statements." + name + ": DOC RESTATES A REFUTED PREMISE - "
                                    "it still says %s" % repr(f))
            cited |= set(REPAIR_CITE.findall(d))
        rp = root / REPAIR_FILE
        if not rp.exists():
            problems.append("StatementsRepair.lean missing: %s - the D-P23 witnesses and "
                            "retained refutations the frozen doc strings cite are gone" % rp)
        else:
            rlines = strip_comments(rp.read_text(encoding="utf-8")).splitlines()
            for name in sorted(cited):
                checked += 1
                if not decl_statement(rlines, name):
                    problems.append("Statements.lean cites %s as its D-P23 half and "
                                    "StatementsRepair.lean no longer declares it - the "
                                    "citation in the normative file is now hollow" % name)
        for rel, dname, whole, must, must_not in FROZEN_CITED_DEFS:
            cpath = root / rel
            if not cpath.exists():
                problems.append("cited definition file missing: %s (%s)" % (cpath, dname))
                continue
            ctext = decl_statement(cpath.read_text(encoding="utf-8").split("\n"),
                                   dname, whole)
            if not ctext:
                problems.append("%s: CITED DEFINITION %s NOT FOUND - the frozen statement "
                                "still names it, so the name now resolves to something else "
                                "or to nothing" % (rel, dname))
                continue
            for f in must:
                checked += 1
                if norm(f) not in ctext:
                    problems.append("%s.%s: no longer says %s - the frozen statement cites "
                                    "this definition, so weakening it weakens the statement "
                                    "without touching the frozen file" % (rel, dname, repr(f)))
            for f in must_not:
                if norm(f) in ctext:
                    problems.append("%s.%s: contains %s - the cited definition has been "
                                    "hollowed out or reverted" % (rel, dname, repr(f)))
        for name, whole, must, must_not in REPAIR_PINS:
                text = decl_statement(rlines, name, whole)
                if not text:
                    problems.append("StatementsRepair." + name + ": DECLARATION NOT FOUND - "
                                    "this is a witness or a retained refutation that a frozen "
                                    "doc string rests on")
                    continue
                for f in must:
                    checked += 1
                    if norm(f) not in text:
                        problems.append("StatementsRepair." + name + ": no longer says "
                                        + repr(f))
                for f in must_not:
                    if norm(f) in text:
                        problems.append("StatementsRepair." + name + ": must stay the pinned "
                                        "OLD text and now contains " + repr(f)
                                        + " - upgrading a retained refutation to the repaired "
                                        "shape makes it refute nothing")
    if problems:
        print("STATEMENT FINGERPRINTS BROKEN (%d):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1
    print("ok: %d statement fragments present in the TYPE across %d LoweringCorrect "
          "fields, %d Surface pins, %d derived checks, %d blk-pin declarations, "
          "%d EnvAgrees clause types, %d Holds clause types plus %d Holds decode pins, "
          "and %d frozen statements (exact text, binders, trusted surface, doc "
          "provenance) against %d repair witnesses (comments stripped first)"
          % (checked, len(FINGERPRINTS), len(SURFACE_PINS), len(DERIVED_CHECKS),
             len(PARTIAL_SPEC_PINS), len(ENV_CLAUSES), len(HOLDS_CLAUSES),
             len(HOLDS_DEFS), len(STATEMENTS_PINS), len(REPAIR_PINS)))


if __name__ == "__main__":
    sys.exit(main())

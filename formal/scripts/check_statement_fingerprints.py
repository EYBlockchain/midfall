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

P-SPECPIN added a fifth kind of target: the CONCLUSION of a spec theorem in Lowering/
Partials.lean. P-SPEC1 proved traceReturn_spec and then measured this gate rather than
trusting it, and found that weakening the theorem's own post - the halt record
'st'.halted = some (.ret, abiTrue)' replaced by 'o = .halt and True', with the proof
repaired to match - left lake build GREEN and all three text gates at rc=0 with the sorry
register unchanged. PARTIAL_SPEC_PINS carried one fragment per theorem, the binder
'hblk : BlkIsEmitter S', and never the conclusion: the fifth blind spot of the class after
theorem-binder hypotheses, EnvAgrees clause types, Holds clause texts and the frozen
normative file. So the only thing protecting a proved spec from silent gutting was its
proof, and a package under schedule pressure edits both.

Three things close it, and each is needed because the others are defeatable alone:

  * PARTIAL_SPEC_CONCLUSIONS - the postcondition shape each of the ten specs must retain,
    matched against conclusion(...) and NOT against the declaration, because a decoy
    hypothesis '(hdecoy : (fun _ : Prop => True) (PartialSound ...) = True)' elaborates, is
    rfl, and would satisfy a presence test run over the binder list while the conclusion had
    been emptied. Every entry is two-sided: a trivialised post ('and True', 'or True', a
    wildcard payload, a bare 'o = .halt') is REJECTED, not merely missing.
  * SPEC_RELATION_DEFS - the bodies of PartialSound and PartialProgress, because pinning the
    application and not the definition leaves the obvious way round: keep 'PartialSound S
    .pcs ...' word for word and hollow the relation's post out, which guts six specs at once
    without editing a theorem. Same reasoning as FROZEN_CITED_DEFS.
  * CHECKPOINT_MAP - Partial.pre and Checkpoint.next, because eight of the ten conclusions
    name a Partial and not a Checkpoint: the target Inv checkpoint is computed by those two
    maps, so moving '.pcs => .pairing' silently moves the claim while every theorem text
    stays put.

P-GATEINTEG closed the sixth blind spot of this class, and it is the one every other entry
in this doc string assumed away: THE FIELD LIST WAS WRITTEN BY HAND. Every table here is a
list of names, and nothing compared a list to the structure it claims to cover. So
P-SCHED P8 - delete 'readScheduleAgrees' from LoweringCorrect outright - built green,
left all three text gates green, and this gate still printed "9 LoweringCorrect fields",
because that number was len(FINGERPRINTS). It was not even nine fields: eight entries were
fields and the ninth, 'lowering_equivalence', is a theorem in the same file, while
'partials' and 'readScheduleAgrees' were fields with no entry at all. And the checklist
inside 'partials' - all sixteen PartialSpecs fields - was named by nothing anywhere under
scripts/.

The gate now PARSES the structures (same parser the duplicate-fact gate uses, on
comment-stripped text) and enforces four derived rules over every tracked structure:
coverage (a field with no pin reddens), no dead names (a pin whose field is gone reddens),
count agreement (the printed number is the parsed one), and non-triviality of EVERY parsed
field's conclusion - the rule that used to guard only Surface pins, now extended to
LoweringCorrect fields, PartialSpecs fields, EnvAgrees, VkSlotsAgree, ChallengesGood and
Eip2537.Holds clauses. P7's gutting of a conclusion to 'ms.map Msg.slot = ms.map Msg.slot'
is caught by that rule and by the fragment list, and the gate says which field it saw.

All twelve perturbations in the package report redden the gate; ten of them passed the gate
as it stood at HEAD. Two of the twelve are 'or True' guttings that keep EVERY required
fragment verbatim - those are why the must_not direction is not decoration.

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
    # P-LOWEQ: the headline moved off solc's IR and onto the in-tree dispatcher model, so
    # the two fragments that pinned the OLD shape (RunContractIR, S.irCheck ir = true) are
    # GONE from this statement and their replacements are pinned instead: the run predicate
    # is ShellModel.wrap, the one new hypothesis is the WorldLocal leg the ir_refines
    # transport demands, and the selector hypothesis that survived the move is spelled. A
    # restatement that quietly dropped a conjunct or re-added the IR binders reddens here.
    ("lowering_equivalence", ["ShellModel.wrap", "obs.isReturn",
        "obs.returnData = abiTrue", "LeanAccepts S H cd",
        "hwl : (S.calls W product qAddr).WorldLocal",
        "bytesTake cd 0 4 = some fnSigVerifyProof",
        "Midfall.Assumptions.G1CodecLaws S.E.g1",
        "Midfall.Assumptions.Eip2537.Holds S.E.g1 \u27e8S.encG2\u27e9 product",
        "hdep : DeploymentW S W H vkAddr qAddr", "hc : LoweringCorrect S product",
        "SideConditions S H cd", "obs.worldUnchanged (callState W S.shellLayout H cd)",
        "returnView (callState W S.shellLayout H cd)",
        "permissive (S.calls W product qAddr)) (ExternalGas.ofFun fun _ => g\u2080) obs \u2192 obs.isReturn",
        "\u2203 obs, ShellModel.wrap S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0)",
        "\u2203 obs"]),
    ("qvm_validated_noBoundsFault", ["readPastEnd", "constSlotOutOfRange",
        "quotientOperandModel", ").isOk = true"]),
    ("accFixedBases_producer", [chr(34) + "-G" + chr(34), "negate = true",
        "\u2203 b \u2208 S.accFixedBases.toList", "namesAscending"]),
    # ---- P-GATEINTEG: the two fields this list did NOT carry, added because the new
    # structure-derived coverage check reddened on them. `partials` is the field that
    # carries the whole per-partial checklist as ONE LoweringCorrect field, and
    # `readScheduleAgrees` is the field P-SCHED deleted (P8) with every gate green: the
    # registry had nine entries, the structure has ten fields, and nothing compared the
    # two numbers. Both are pinned here now, and the gate prints the count it PARSED.
    ("partials", ["PartialSpecs S product"]),
    ("readScheduleAgrees", ["\u2200 inst \u03c0 ms",
        "decodeRust (G\u209c := G\u209c) S.E Features.solidity S.vk inst \u03c0 = some ms",
        "ms.map Msg.slot",
        "(RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout).slots"]),
]


# ---------------------------------------------------------------------------
# P-GATEINTEG: THE PER-PARTIAL CHECKLIST, FIELD BY FIELD.
#
# WHY THIS TABLE EXISTS. LoweringCorrect carries PartialSpecs as ONE field ('partials'),
# so the fingerprint gate read nine names out of a ten-field structure and never looked
# at the checklist inside it. Measured, not assumed: NOT ONE of the sixteen PartialSpecs
# field names appeared anywhere under scripts/. Deleting finalPairing_sound, gutting
# pcs_rejects to a self-equality, or renaming vkLoading_progress so the mirror of its
# theorem no longer has a twin was invisible to every text gate in the repository. The
# *_spec THEOREMS were pinned by P-SPECPIN; the checklist FIELDS the headline carries
# were not - and it is the fields a LoweringCorrect instance has to discharge.
#
# WHY FRAGMENTS AND NOT BARE NAMES. A name-only registry is defeated by keeping the name
# and hollowing the type - the R-60 S2 attack this file documents twice. Each entry is
# (field, must, must_not), matched against the field type read FROM THE STRUCTURE, so a
# paraphrase that drops the blk pin, the permissive leg, the Holds leg, the keccak leg,
# the DualMSM hypothesis or the checkpoint loses a NAMED fragment.
#
# The spine is a constant because it is the same five hypotheses in fifteen fields, and
# one constant is the only honest way to say 'every one of these keeps all five': the
# copy that drifts in one of fifteen places is exactly the defect this project measures.
# ---------------------------------------------------------------------------
_SPECS_SPINE = [
    "SupportedS S S.o\u2080",
    "EnvAgrees S.E S.vk S.plan S.params S.sG2gen",
    "Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout "
    "S.cfg.numInstances S.E.g1 cd = some (ms, instW)",
    "instOfWords? (p := p) instW = some inst",
    "snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap",
]
# The fault-implies-revert pair keys on a decode that FAILED, so it carries the
# decodeCalldata leg as '= none' and the snapshot leg as '= .error f' - not the spine,
# whose whole point is that a snapshot exists.
_SPECS_DECODE_NONE = ("Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout "
                      "S.cfg.numInstances S.E.g1 cd = none")
_SPECS_SNAPSHOT_ERROR = "snapshotOf S.E H S.vk inst ms (accOf S instW) = .error f"
_SPECS_CALDATA_PRE = "(fun st => st.env.calldata = cd.data.toList)"
_SPECS_PERMISSIVE = "PermissiveFor S W product qAddr calls"
_SPECS_HOLDS = "Midfall.Assumptions.Eip2537.Holds S.E.g1 \u27e8S.encG2\u27e9 product"
_SPECS_VKSLOTS = "VkSlotsAgree S.E S.plan S.sG2gen S.encG2 S.accFixedBases"
# The keccak agreement, spelled at each of the four places it legitimately differs: the
# checkpoint it is taken at (.vk / .pcs) and the call relation it quantifies over (the
# bundle's own 'calls' in a sound field, 'S.calls W product qAddr' in a progress twin).
# They are NOT interchangeable, which is why they are four constants and not one.
_SPECS_KECCAK_SOUND_VK = ("(\u2200 V st, Inv (calls := calls) (gas := gas) S.E S.params "
                          ".vk S.plan Snap V st \u2192 st.env.keccakOf = hashOfBytes H)")
_SPECS_KECCAK_SOUND_PCS = ("(\u2200 V st, Inv (calls := calls) (gas := gas) S.E S.params "
                           ".pcs S.plan Snap V st \u2192 st.env.keccakOf = hashOfBytes H)")
_SPECS_KECCAK_PROG_VK = ("(\u2200 V st, Inv (calls := S.calls W product qAddr) (gas := gas) "
                         "S.E S.params .vk S.plan Snap V st \u2192 "
                         "st.env.keccakOf = hashOfBytes H)")
_SPECS_KECCAK_PROG_PCS = ("(\u2200 V st, Inv (calls := S.calls W product qAddr) (gas := gas) "
                          "S.E S.params .pcs S.plan Snap V st \u2192 "
                          "st.env.keccakOf = hashOfBytes H)")
# The two shapes every field in this structure refuses: a progress claim inside a sound
# field (and vice versa), and a post widened by a conjunct that cannot fail.
_SPECS_NO_PROGRESS = ["PartialProgress", "\u2227 True", "\u2228 True"]
_SPECS_NO_SOUND = ["PartialSound", "\u2227 True", "\u2228 True"]

PARTIAL_SPECS_FINGERPRINTS = [
    # THE blk PIN, carried by the checklist and not only by the theorems (R-62). If this
    # field goes the sixteen claims below quantify over every block a Surface returns.
    ("blk_is", ["BlkIsEmitter S"], ["= True"]),
    ("vkLoading_sound",
     _SPECS_SPINE + [_SPECS_PERMISSIVE,
                     "PartialSound S .vkLoading Snap calls gas (calldataPre S cd) "
                     "(fun _ _ => True)"],
     _SPECS_NO_PROGRESS + ["PartialSound S .pcs"]),
    ("transcriptParser_sound",
     _SPECS_SPINE + [_SPECS_PERMISSIVE, _SPECS_KECCAK_SOUND_VK,
                     "PartialSound S .transcriptParser Snap calls gas "
                     "(calldataPre S cd) (fun _ _ => True)"],
     _SPECS_NO_PROGRESS),
    # lagrange is the ONE sound arm whose post is not True: a normal exit proves x^n != 1,
    # because the contract batch-inverts where Lean's lIRange yields zeros silently.
    # Replacing that post with (fun _ _ => True) is the gutting this row refuses.
    ("lagrange_sound",
     _SPECS_SPINE + [_SPECS_PERMISSIVE,
                     "PartialSound S .lagrange Snap calls gas (calldataPre S cd) "
                     "(fun _ _ => Snap.alg.x ^ S.vk.domain.n \u2260 1)"],
     _SPECS_NO_PROGRESS + ["(fun _ _ => True)"]),
    ("quotientLin_sound",
     _SPECS_SPINE + [_SPECS_PERMISSIVE,
                     "PartialSound S .quotientLin Snap calls gas (calldataPre S cd) "
                     "(fun _ _ => True)"],
     _SPECS_NO_PROGRESS),
    ("pcs_sound",
     _SPECS_SPINE + [_SPECS_PERMISSIVE, _SPECS_HOLDS,
                     "PartialSound S .pcs Snap calls gas (calldataPre S cd) "
                     "(fun _ _ => True)"],
     _SPECS_NO_PROGRESS),
    # finalPairing carries the whole bundle: Holds, the keccak leg at .pcs, AND the VK
    # slot agreement. Drop any one and the arm stops being the claim the theorem proves.
    ("finalPairing_sound",
     _SPECS_SPINE + [_SPECS_PERMISSIVE, _SPECS_HOLDS, _SPECS_KECCAK_SOUND_PCS,
                     _SPECS_VKSLOTS,
                     "PartialSound S .finalPairing Snap calls gas (calldataPre S cd) "
                     "(fun _ _ => True)"],
     _SPECS_NO_PROGRESS),
    # Stated OUTSIDE the relation wrappers: checkpoint, pre and halt record are all in the
    # field's own text, so all three are pinned. The must_not half is the gutting menu -
    # a bare 'o = .halt', a wildcard payload, a wildcard kind, an existential.
    ("traceReturn_sound",
     ["SupportedS S S.o\u2080", "EnvAgrees S.E S.vk S.plan S.params S.sG2gen",
      "Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout "
      "S.cfg.numInstances S.E.g1 cd = some (ms, instW)",
      "instOfWords? (p := p) instW = some inst",
      "snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap",
      "\u2200 outer,",
      "StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)",
      "(S.blk .traceReturn S.plan)",
      "Inv (calls := calls) (gas := gas) S.E S.params .pairing S.plan Snap V st "
      "\u2227 calldataPre S cd V st",
      "(fun _ _ _ st' o => o = .halt \u2227 st'.halted = some (.ret, abiTrue))"],
     ["o = .halt \u2227 True", "o = .halt)", "some (.ret, _)", "some (_, abiTrue)",
      "\u2203 d, st'.halted", "\u2227 True", "\u2228 True"]),
    # The two fault-implies-revert obligations (section N). Their content is the FAILED
    # decode and the absent snapshot: '= none' and '= .error f' are the whole claim.
    ("transcript_rejects",
     ["SupportedS S S.o\u2080", "EnvAgrees S.E S.vk S.plan S.params S.sG2gen",
      _SPECS_DECODE_NONE,
      "PartialRejects S .transcriptParser .vk calls gas", _SPECS_CALDATA_PRE],
     _SPECS_NO_PROGRESS + ["PartialSound", "= True"]),
    ("pcs_rejects",
     ["SupportedS S S.o\u2080", "EnvAgrees S.E S.vk S.plan S.params S.sG2gen",
      "Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout "
      "S.cfg.numInstances S.E.g1 cd = some (ms, instW)",
      "instOfWords? (p := p) instW = some inst",
      _SPECS_SNAPSHOT_ERROR,
      "PartialRejects S .pcs .quotient calls gas", _SPECS_CALDATA_PRE],
     _SPECS_NO_PROGRESS + ["PartialSound", "= True"]),
    # ---- the six progress twins. Their content is that the block does NOT revert, so
    # PartialSound and the word Reverted are the forbidden shapes, and each twin must
    # name its OWN partial: a progress field that quietly points at another checkpoint
    # stops being the twin of the sound arm above it.
    ("vkLoading_progress",
     _SPECS_SPINE + ["PartialProgress S W product qAddr .vkLoading Snap gas "
                     "(calldataPre S cd)"],
     _SPECS_NO_SOUND + ["PartialProgress S W product qAddr .pcs"]),
    ("transcriptParser_progress",
     _SPECS_SPINE + [_SPECS_KECCAK_PROG_VK,
                     "PartialProgress S W product qAddr .transcriptParser Snap gas "
                     "(calldataPre S cd)"],
     _SPECS_NO_SOUND),
    # lagrange's twin needs ChallengesGood: at x = omega^i the contract reverts and Lean
    # accepts, so without that side condition the no-revert claim is simply false.
    ("lagrange_progress",
     _SPECS_SPINE + ["ChallengesGood S.vk Snap",
                     "PartialProgress S W product qAddr .lagrange Snap gas "
                     "(calldataPre S cd)"],
     _SPECS_NO_SOUND),
    ("quotientLin_progress",
     _SPECS_SPINE + ["PartialProgress S W product qAddr .quotientLin Snap gas "
                     "(calldataPre S cd)"],
     _SPECS_NO_SOUND),
    ("pcs_progress",
     _SPECS_SPINE + [_SPECS_HOLDS,
                     "PartialProgress S W product qAddr .pcs Snap gas "
                     "(calldataPre S cd)"],
     _SPECS_NO_SOUND),
    # The pairing check has to PASS for the honest fold to return, so DualMSM.check is a
    # hypothesis of the no-revert claim and the entry condition lives on the PRE.
    ("finalPairing_progress",
     _SPECS_SPINE + [_SPECS_HOLDS, _SPECS_KECCAK_PROG_PCS,
                     "DualMSM.check Snap.c.dual S.params = true",
                     _SPECS_VKSLOTS,
                     "PartialProgress S W product qAddr .finalPairing Snap gas "
                     "(fun V st => calldataPre S cd V st \u2227 VEnv.get V "
                     "\"success\" = some 1)"],
     _SPECS_NO_SOUND + ["DualMSM.check Snap.c.dual S.params = false"]),
]

# The same three-way shape for the headline structure: a field may not be the OTHER
# field's claim, and may not carry a conjunct that cannot fail. Only readScheduleAgrees
# needs an explicit must_not today - its P7 gutting is a self-equality, and naming the
# exact text here means the gate says WHICH attack it saw rather than only that the
# conclusion is decidable.
FIELD_MUST_NOT = {
    "readScheduleAgrees": ["ms.map Msg.slot = ms.map Msg.slot", "= True"],
}

# R-58 also added pin FIELDS to the Surface record. Those are statements too, and the
# duplicate-fact gate only checks that they exist and name both sides - it does not
# notice a paraphrase that keeps the two names and drops the equation. These fragments
# pin the shape of each pin, in the file that declares them.
SURFACE_PINS = [
    # P-INLINE (D-P39): the pin was restated to the ARM form in the same commit this registry
    # entry moved (D-P27). The third fragment is the embedding itself - a paraphrase that keeps the
    # concatenation and drops the constant inlining loses a token here, which is the point: the
    # un-inlined form is the statement RunShellInversion proved FALSE.
    ("shell_unfolds", ["shell.codeBlock =", "inlineContractConstants",
                       "L.headGuard ++ bindLocals ++ L.main"]),
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
    # P-RESTORE3: hProofLayout, restored from sketch M:1676 after its drop-reason turned
    # out to belong to its two codec neighbours and not to it. The four fragments are the
    # four things the pin has to keep saying: it is an existential over the generator's own
    # producer, at the ABI proof pointer, about the plan's layout, as an equation and not a
    # predicate. Drop any one and the field stops pinning what it was restored to pin.
    ("hProofLayout", ["\u2203 protocol numEvals numPointSets",
                      "ProofCalldataLayout.fromProtocol protocol",
                      "Midfall.Generator.abiVerifyProofProofCptr",
                      "= .ok plan.proofLayout"]),
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
#
# P-SPECPIN made each entry a 4-tuple (theorem, must, must_not, whole). The must half now
# carries the CONCLUSION SHAPE as well as the binder, and the must_not half refuses the
# trivialisations a package under pressure would write - `o = .halt ∧ True`, a progress twin
# demoted to `PartialSound`, a strictness post replaced by `(fun _ _ => True)`. Presence-only is
# not enough: the hole P-SPEC1 measured was a conclusion that KEPT its outer shape and LOST its
# content, and a gate that only looks for the shape waves it through.
PARTIAL_SPEC_PINS = [
    ("vkLoading_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("transcriptParser_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("lagrange_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("lagrange_progress_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("quotientLin_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("pcs_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("finalPairing_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("finalPairing_progress_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("finalPairing_acc_spec", ["hblk : BlkIsEmitter S"], [], False),
    ("traceReturn_spec", ["hblk : BlkIsEmitter S"], [], False),
    # The pin itself must pin blk to the EMITTER and main to the emitted whole - not to a
    # self-equality, not to True. Its body IS the statement, so whole=True.
    ("BlkIsEmitter", ["S.blk q pv =", "GenAst.emitPartial pv q",
                      "S.L.main =", "GenAst.emitMain S.plan"], [], True),
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
     [], True),
    ("emitFinalPairingArms", ["emitAccBatch batch", "ec_pairing",
                              "PAIRING_RHS_MPTR", "PAIRING_LHS_MPTR"], [], True),
]

# ---------------------------------------------------------------------------
# P-SPECPIN: THE POSTCONDITION EACH SPEC MUST RETAIN, READ OFF THE CONCLUSION ALONE.
#
# WHY THIS SECTION EXISTS. P-SPEC1 proved `traceReturn_spec` and then MEASURED the gate instead
# of trusting it. Weakening that theorem's conclusion from the halt record
#
#     (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue))
#
# to
#
#     (fun _ _ _ st' o => o = .halt ∧ True)
#
# - and repairing the proof to match, which is a one-line change - leaves `lake build` GREEN and
# `check_statement_fingerprints.py`, `check_hypothesis_bundles.py` and `check_duplicate_facts.py`
# all at rc=0 with the sorry register unchanged. `PARTIAL_SPEC_PINS` carried
# `["hblk : BlkIsEmitter S"]` per theorem: the binder, never the conclusion. So the only thing
# standing between a proved spec and a silent gutting was the proof itself, and a package under
# schedule pressure edits both. This is the fifth structural blind spot of the class - theorem
# binders, EnvAgrees clause types, Holds clause texts, the frozen normative file, and now the
# CONCLUSIONS of the very theorems the project is trying to close.
#
# WHY THE CONCLUSION AND NOT THE DECLARATION. R-60 S2 learned that a fragment matched anywhere in
# a declaration can be carried by a part of it that says nothing: the original exploit was a field
# whose real text sat in a trailing comment. The same attack exists here - a decoy hypothesis
#
#     (hdecoy : (fun _ : Prop => True)
#       (PartialSound S .pcs Snap calls gas (calldataPre S cd) (fun _ _ => True)) = True)
#
# elaborates, is `rfl`, and would satisfy a presence test run over the binder list while the
# conclusion had been emptied. So every fragment below is matched against `conclusion(...)`: the
# text after the first TOP-LEVEL colon with the value cut. A hypothesis cannot reach it.
#
# BOTH DIRECTIONS, as STATEMENTS_PINS and HOLDS_CLAUSES do. `must` is the postcondition shape;
# `must_not` is the trivialisation of it. The must half alone would still pass a gutting that kept
# the outer application and hollowed the argument, and the must_not half is what makes `True` in
# a post a gate failure rather than a refactor.
PARTIAL_SPEC_CONCLUSIONS = [
    # ---- the six soundness arms: PartialSound at the partial's own checkpoint, with the calldata
    # link as the extra pre and the partial's own extra post.
    ("vkLoading_spec",
     ["PartialSound S .vkLoading", "Snap calls gas (calldataPre S cd)", "(fun _ _ => True)"],
     ["PartialProgress", "PartialRejects", "\u2227 True", "\u2228 True",
      "fun _ _ _ st' o => True", "fun _ _ V' st' o => True"]),
    ("transcriptParser_spec",
     ["PartialSound S .transcriptParser", "Snap calls gas (calldataPre S cd)",
      "(fun _ _ => True)"],
     ["PartialProgress", "PartialRejects", "\u2227 True", "\u2228 True",
      "fun _ _ _ st' o => True", "fun _ _ V' st' o => True"]),
    # lagrange is the ONE spec whose extra post is not True: a normal exit proves x^n is not 1,
    # because batch_invert rejects the zero Lean's lIRange accepts. Replacing that with
    # (fun _ _ => True) is the exact gutting this row refuses - it is IN must_not, not merely
    # absent from must.
    ("lagrange_spec",
     ["PartialSound S .lagrange", "Snap calls gas (calldataPre S cd)",
      "fun _ _ => Snap.alg.x ^ S.vk.domain.n \u2260 1"],
     ["(fun _ _ => True)", "PartialProgress", "PartialRejects", "\u2227 True", "\u2228 True"]),
    ("quotientLin_spec",
     ["PartialSound S .quotientLin", "Snap calls gas (calldataPre S cd)", "(fun _ _ => True)"],
     ["PartialProgress", "PartialRejects", "\u2227 True", "\u2228 True",
      "fun _ _ _ st' o => True", "fun _ _ V' st' o => True"]),
    ("pcs_spec",
     ["PartialSound S .pcs", "Snap calls gas (calldataPre S cd)", "(fun _ _ => True)"],
     ["PartialProgress", "PartialRejects", "\u2227 True", "\u2228 True",
      "fun _ _ _ st' o => True", "fun _ _ V' st' o => True"]),
    ("finalPairing_spec",
     ["PartialSound S .finalPairing", "Snap calls gas (calldataPre S cd)", "(fun _ _ => True)"],
     ["PartialProgress", "PartialRejects", "\u2227 True", "\u2228 True",
      "fun _ _ _ st' o => True", "fun _ _ V' st' o => True"]),
    # ---- the progress arms. Their whole content is that the block does NOT revert, so the
    # revert arm is the forbidden shape: `Reverted`, any disjunction, and any trivial post.
    ("lagrange_progress_spec",
     ["PartialProgress S W product qAddr .lagrange", "Snap gas (calldataPre S cd)"],
     ["PartialSound", "PartialRejects", "\u2227 True", "\u2228 True", "=> True", "Reverted"]),
    # P-RESTORE2 MOVED THIS PIN, and says so because a pin moved without a note is the
    # same defect as a clause dropped without one. The theorem used to take
    # (calldataPre S cd) as its whole pre, and that statement was FALSE: the emitted
    # slice reads the success local before it writes it (GenAst.lean:651-654), so a run
    # entering at .pcs with success = 0 reverts and PartialProgress's o = .normal post
    # cannot hold. The entry condition is now on the pre, and the OLD form is in must_not
    # so a package that quietly restores the sketch's weaker pre reddens this gate
    # instead of quietly being true of a program that reverts.
    ("finalPairing_progress_spec",
     ["PartialProgress S W product qAddr .finalPairing", "Snap gas",
      'calldataPre S cd V st \u2227 VEnv.get V "success" = some 1'],
     ["PartialSound", "PartialRejects", "\u2227 True", "\u2228 True", "=> True", "Reverted",
      "(calldataPre S cd)"]),
    # ---- the two arms stated OUTSIDE the relation wrappers, so the checkpoint, the pre and the
    # post are all in the theorem's own text, and all three are pinned here.
    ("finalPairing_acc_spec",
     ["StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer) "
      "(S.blk .finalPairing S.plan)",
      "Inv (calls := calls) (gas := gas) S.E S.params .pcs S.plan Snap V st",
      "calldataPre S cd V st",
      "(o = .halt \u2227 Reverted st')",
      "o = .normal \u2227 VEnv.get V' \"success\" = some 1",
      "batchedCheck S.params",
      "Snap.c.dual a (tblOf S.accFixedBases) = true"],
     # The accumulator arm's decision is batchedCheck over the batched pair. DualMSM.check is the
     # NO-accumulator decision: if it appears in this conclusion the arm has been swapped for the
     # other one and the accumulator claim is gone.
     ["\u2227 True", "\u2228 True", "DualMSM.check Snap.c.dual S.params = true",
      "fun _ _ V' st' o => True"]),
    ("traceReturn_spec",
     ["StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer) "
      "(S.blk .traceReturn S.plan)",
      "Inv (calls := calls) (gas := gas) S.E S.params .pairing S.plan Snap V st",
      "calldataPre S cd V st",
      "o = .halt \u2227 st'.halted = some (.ret, abiTrue)"],
     # Every one of these is a shape the halt record could be weakened to that still ELABORATES
     # and still builds: `o = .halt \u2227 True` (the hole P-SPEC1 measured), a bare `o = .halt`, a
     # wildcard payload `some (.ret, _)` that drops the abiTrue word, a wildcard kind
     # `some (_, abiTrue)` that drops the return, and an existential that drops both.
     ["o = .halt \u2227 True", "o = .halt)", "some (.ret, _)", "some (_, abiTrue)",
      "\u2203 d, st'.halted", "\u2227 True", "\u2228 True", "fun _ _ _ st' o => True",
      "Reverted st'"]),
]

# The two relations the eight wrapper conclusions are applications OF. Pinning the application and
# not the definition leaves the obvious way round: keep `PartialSound S .pcs ...` word for word and
# redefine PartialSound's post to True, which guts all six soundness specs at once without
# touching one theorem. Same reasoning as FROZEN_CITED_DEFS for Statements.lean. whole=True,
# because for a definition the BODY is the statement.
SPEC_RELATION_DEFS = [
    ("PartialSound",
     ["\u2200 outer,",
      "StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)",
      "(S.blk q S.plan)",
      "Inv (calls := calls) (gas := gas) S.E S.params q.pre S.plan Snap V st",
      "addl V st",
      "(o = .halt \u2227 Reverted st')",
      "o = .normal",
      "Inv (calls := calls) (gas := gas) S.E S.params q.pre.next S.plan Snap V' st'",
      "extra V' st'"],
     ["fun _ _ V' st' o => True", "\u2227 True", "\u2228 True"]),
    # The progress twin's content is the ABSENCE of the revert arm, so a disjunction anywhere in
    # its body - and the word Reverted - is the soundness shape creeping back in.
    ("PartialProgress",
     ["\u2200 outer,",
      "StmtsContractAll (D := Bridge.Dialect (S.calls W product qAddr) gas)",
      "(S.blk q S.plan)",
      "Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params q.pre S.plan Snap V st",
      "addl V st",
      "o = .normal",
      "Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params q.pre.next S.plan "
      "Snap V' st'"],
     ["\u2228", "Reverted", "=> True"]),
]

# The checkpoint each wrapper spec's post REACHES. The eight wrapper conclusions name a Partial and
# not a Checkpoint: the target Inv checkpoint is `q.pre.next`, computed by the two maps below.
# Move `.lagrange => .transcript` to `.lagrange => .start` and every lagrange post silently stops
# asserting the Lagrange slots while the theorem text is unchanged and the build is green. Each of
# the seven arms and seven successors is pinned to its OWN right-hand side, so any move reddens a
# named fragment rather than sliding past a count.
CHECKPOINT_MAP_FILE = "Midfall/Lowering/Checkpoint.lean"
CHECKPOINT_MAP = [
    ("Partial.pre",
     [".vkLoading => .start", ".transcriptParser => .vk", ".lagrange => .transcript",
      ".quotientLin => .lagrange", ".pcs => .quotient", ".finalPairing => .pcs",
      ".traceReturn => .pairing"],
     []),
    ("Checkpoint.next",
     [".start => .vk", ".vk => .transcript", ".transcript => .lagrange",
      ".lagrange => .quotient", ".quotient => .pcs", ".pcs => .pairing",
      ".pairing => .pairing"],
     []),
]

# P-ENV: the EnvAgrees clause types in Lowering/Inv.lean. (structure, field, must, must not)
INV_FILE = "Midfall/Lowering/Inv.lean"
ENV_CLAUSES = [
    ("EnvAgrees", "omegaOrder",
     ["Midfall.Assumptions.orderExactly vk.domain.omega vk.domain.n"],
     ["vk.domain.omega ^ vk.domain.n = 1"]),
    # P-RESTORE2: the four VK-header / fixed-base clauses the sketch carried inside
    # EnvAgrees. They had been dropped, the stated reason for dropping them measured FALSE
    # (the .vk clause pins the payload COPY and never mentions a codec), and they are now
    # fields of VkSlotsAgree in the same file. A hypothesis structure no theorem reads and
    # no gate pins is a hypothesis that gets hollowed out to True on the next package that
    # needs a proof, which is what happened to these four once already.
    # ---- P-GATEINTEG: the nine EnvAgrees clauses this list did NOT carry. The coverage
    # rule added by this package parses 'structure EnvAgrees' and found them: 10 fields,
    # 1 pinned. They are the hypotheses verifier_sound, verifier_complete,
    # only_two_outcomes and end_to_end_noAcc all carry, and a clause relaxed to a
    # self-equality or widened with a disjunct that cannot fail elaborates, builds, and
    # keeps every KAT true - the omegaOrder defect (P-ENV) with nine more chances to
    # recur. Each entry is the equation the clause states, and neither 'True' nor a
    # widened form is accepted.
    ("EnvAgrees", "modulus", ["p = frModulusConstant"], ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "truncWidth",
     ["divCeil (divCeil E.field.numBits 8) 2 = 16"], ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "domainN",
     ["vk.domain.n = 2 ^ vk.domain.k", "vk.domain.k = PV.k"],
     ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "baryWeight",
     ["vk.domain.barycentricWeight = ((2 ^ vk.domain.k : \u2115) : Fr p)\u207b\u00b9"],
     ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "omegaInvMul",
     ["vk.domain.omegaInv * vk.domain.omega = 1"], ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "negLagranges",
     ["PV.numNegLagranges = vk.cs.blindingFactors.toOption.getD 0 + 1"],
     ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "nG2", ["params.nG2Prepared = P.g\u2082\u207b\u00b9"],
     ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "sG2", ["params.sG2Prepared = sG2gen"], ["\u2227 True", "\u2228 True"]),
    ("EnvAgrees", "vkDigestWord",
     ['(PV.vk.constants.getD 0 ("", 0)).2 = frWord vk.transcriptRepr'],
     ["\u2227 True", "\u2228 True"]),
    # P-GATEINTEG: ChallengesGood is a one-field structure in the same file, and the
    # field is the whole claim - lagrange_sound's post and lagrange_progress's hypothesis
    # both rest on it. Unpinned until the coverage rule parsed it.
    ("ChallengesGood", "xNotRoot",
     ["S.alg.x ^ vk.domain.n \u2260 1"], ["\u2227 True", "\u2228 True"]),
    ("VkSlotsAgree", "g1BaseWords",
     ["vkG1Words PV vkG1BaseSlot = E.g1.toEip P.g\u2081"],
     ["= True", "Bytes.empty"]),
    ("VkSlotsAgree", "g2BaseWords",
     ["vkG2Words PV vkG2BaseSlot = encG2 P.g\u2082"],
     ["= True"]),
    ("VkSlotsAgree", "negSG2Words",
     ["vkG2Words PV vkNegSG2BaseSlot = encG2 sG2gen\u207b\u00b9"],
     ["= True"]),
    ("VkSlotsAgree", "accBasesInVk",
     ["\u2200 b \u2208 fb.toList, \u2203 slot, vkG1Words PV slot = E.g1.toEip b.base"],
     ["= True", "\u2200 b \u2208 fb.toList, True"]),
]

# P-RESTORE2 STEP 3: the clauses of Inv ITSELF. InvAt is a Bool-valued def and not a
# structure, so env_clause_text cannot reach it; these are read with the same whole-body
# parser the checkpoint maps use. WHY THEY NEED PINNING: P-SPECPIN dropped two post
# conjuncts from finalPairing_spec on the ground that Inv .pairing already asserts them,
# and that relocation is now load-bearing - Inv.pairing_decision in Inv.lean is the
# in-tree proof of it. If the .pairing arm were hollowed out the recovery lemma would
# still elaborate (it reads the arm by shape) and the specs would silently stop asserting
# the pairing decision. LocalsOk is here for the same reason: every Inv hypothesis
# carries it, and it is one match away from being a constant true.
INV_CLAUSES = [
    ("InvAt",
     ["if k == Checkpoint.pairing then",
      'VEnv.get V "success" == some 1',
      "PV.hasAccumulator == true || DualMSM.check S.c.dual params"],
     ["PV.hasAccumulator == true || True", "DualMSM.check S.c.dual params && True"]),
    ("LocalsOk",
     ['match VEnv.get V "r" with', "w == BitVec.ofNat 256 p"],
     ["fun _ => true"]),
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
    # D-P33 (human, round 107): filling the frozen verifyNative_iff_msgs sorry needs the
    # proof layer, so the normative file now depends on it. This is the widening the gate
    # exists to make a deliberate act rather than a silent one - the policy objection in
    # D-P27 ("the spec surface holds statements, not proofs") was answered on the merits
    # once the proof existed, and the human chose to fill it.
    "import Midfall.Lowering.Obligations",
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


# ---------------------------------------------------------------------------
# P-GATEINTEG: THE FIELD LIST IS PARSED FROM THE STRUCTURE, NOT WRITTEN BY HAND.
#
# THE DEFECT THIS CLOSES. Every table above is a list of NAMES written by a human, and
# nothing in the repository ever compared one to the structure it claims to cover. So
# P-SCHED P8 - delete 'readScheduleAgrees' from LoweringCorrect outright - left the
# build green, all three text gates green, and this gate still printing "9 LoweringCorrect
# fields": the printed count was len(FINGERPRINTS), a literal that cannot move when a
# field does. It was not even nine fields: eight of the nine entries were fields and the
# ninth, 'lowering_equivalence', is a theorem in the same file, while 'partials' and
# 'readScheduleAgrees' were fields with no entry at all.
#
# THE RULE, IN FOUR PARTS, ALL DERIVED FROM THE PARSED STRUCTURE:
#   (a) COVERAGE. Every field the parser finds must have a registry entry. A field with
#       no pin reddens - that is precisely what P8 slipped through.
#   (b) NO DEAD NAMES. Every registry entry must name a field the structure still
#       declares, unless it is a declared non-field entry (the theorem). A rename trips
#       (a) and (b) at once, which is the point: the old name stops being live and the
#       new one is unpinned.
#   (c) COUNT AGREEMENT. The parsed count must equal the number of registry entries that
#       name fields. Redundant with (a) and (b) and asserted anyway, because it is the
#       number this gate PRINTS, and a printed number that is derived rather than typed
#       is the whole deliverable.
#   (d) EVERY FIELD'S CONCLUSION MUST BE ABLE TO FAIL. The triviality rule that already
#       guarded Surface pins and the *_spec conclusions now runs over every parsed field
#       of every tracked structure, whether or not a fragment list mentions it. P7's
#       gutting - a conclusion replaced by 'ms.map Msg.slot = ms.map Msg.slot' - is a
#       self-equality, and it is now seen twice: once here and once by the fragment list.
#
# The fields are read with the SAME structure parser the duplicate-fact gate uses, on
# comment-stripped text, so a fragment is matched against the field of THAT structure and
# not against a doc string that quotes it (R-60 S2).
# ---------------------------------------------------------------------------
def _registry_from_clauses(table, struct):
    """The clause tables already carry (structure, field, must, must_not); re-cut them as
    (field, must, must_not) so the coverage rule can read the field list off the
    structure and compare."""
    return [(f, must, must_not) for (s, f, must, must_not) in table if s == struct]


# The two headline obligation structures are checked in full here - coverage, count, and
# every fragment - because nothing in the tree CONSTRUCTS a term of either, which is
# exactly why a field could vanish with the build green. The four hypothesis structures
# below are checked for COVERAGE and triviality only: their fragments are already
# enforced by the ENV_CLAUSES / HOLDS_CLAUSES loops, and re-checking them here would
# count the same fragment twice. They are also constructed at the fixture
# (Instances/SurfaceFixture.lean:2279-2312 builds EnvAgrees and VkSlotsAgree field by
# field), so deleting one of their fields reddens lake build - a gutting does not, which
# is what the triviality rule and the clause pins are for.
TRACKED_STRUCTURES = [
    # (file, structure, registry, label, non-field entries, check fragments here?)
    ("Midfall/Lowering/Obligations.lean", "LoweringCorrect",
     [(f, frags, FIELD_MUST_NOT.get(f, [])) for f, frags in FINGERPRINTS],
     "LoweringCorrect", {"lowering_equivalence"}, True),
    ("Midfall/Lowering/Partials.lean", "PartialSpecs",
     [(f, must, must_not) for f, must, must_not in PARTIAL_SPECS_FINGERPRINTS],
     "PartialSpecs", set(), True),
    ("Midfall/Lowering/Inv.lean", "EnvAgrees",
     _registry_from_clauses(ENV_CLAUSES, "EnvAgrees"), "EnvAgrees", set(), False),
    ("Midfall/Lowering/Inv.lean", "VkSlotsAgree",
     _registry_from_clauses(ENV_CLAUSES, "VkSlotsAgree"), "VkSlotsAgree", set(), False),
    ("Midfall/Lowering/Inv.lean", "ChallengesGood",
     _registry_from_clauses(ENV_CLAUSES, "ChallengesGood"), "ChallengesGood", set(), False),
    ("Midfall/Assumptions/Eip2537.lean", "Eip2537.Holds",
     _registry_from_clauses(HOLDS_CLAUSES, "Eip2537.Holds"), "Eip2537.Holds", set(), False),
]


def check_tracked_structures(root, problems):
    """Returns (derived field counts by label, set of pinned field names, fragments)."""
    counts, pinned_all, checked = {}, set(), 0
    for rel, struct, registry, label, nonfield, check_frags in TRACKED_STRUCTURES:
        path = root / rel
        if not path.exists():
            problems.append("%s: file missing: %s - the structure cannot be parsed, so "
                            "no field of it is tracked by anything" % (label, rel))
            continue
        body = strip_comments(path.read_text(encoding="utf-8"))
        fields = structures(body).get(struct)
        if not fields:
            problems.append("%s: STRUCTURE NOT FOUND in %s - deleted, renamed, or moved "
                            "below a section, so every pin that claims to read it now "
                            "reads nothing" % (label, rel))
            continue
        counts[label] = len(fields)
        reg = {}
        for f, must, must_not in registry:
            if f in reg:
                problems.append("%s.%s: DUPLICATE REGISTRY ENTRY - the registry pins the "
                                "same field twice, so a count can no longer be read off it"
                                % (label, f))
            reg[f] = (must, must_not)
        live = {f for f in reg if f in fields}
        pinned_all |= live
        # (a) COVERAGE - the check P8 slipped through.
        for f in sorted(set(fields) - live):
            problems.append(
                "%s.%s: FIELD HAS NO PIN - the structure declares %d fields and the "
                "registry covers %d, and this one is in none of them, so it can be "
                "deleted, renamed or gutted with every gate green (P-GATEINTEG P8)"
                % (label, f, len(fields), len(live)))
        # (b) NO DEAD NAMES.
        for f in sorted(set(reg) - set(fields) - nonfield):
            problems.append(
                "%s.%s: REGISTRY NAMES A DEAD FIELD - %s no longer declares it in %s. "
                "Either the field was deleted or renamed (which is the regression) or the "
                "pin was retired without deleting it (which is a lie in a table)"
                % (label, f, struct, rel))
        # (c) COUNT AGREEMENT.
        if len(fields) != len(live):
            problems.append(
                "%s: FIELD COUNT DISAGREES - %d fields parsed from 'structure %s' in %s, "
                "%d pinned by the registry. The number this gate prints used to be "
                "len(FINGERPRINTS), a literal that could not move when a field did"
                % (label, len(fields), struct, rel, len(live)))
        # (d) EVERY FIELD: able to fail, then its fragments.
        for f in sorted(fields):
            text = env_clause_text(body, struct, f)
            if not text:
                problems.append("%s.%s: FIELD TEXT EMPTY - the parser found the name but "
                                "no type, so there is nothing to pin" % (label, f))
                continue
            bad = triviality_problems(conclusion(text))
            if bad:
                problems.append(
                    "%s.%s: FIELD CONCLUSION IS TRIVIALLY DECIDABLE - it says %s (%s), so "
                    "no Surface can fail it (P-GATEINTEG P7: a gutted field is the same "
                    "defeat R-60 S2 found on a Surface pin, one level up)"
                    % (label, f, repr(conclusion(text)), bad[0]))
                continue
            if not check_frags:
                continue    # coverage + triviality only; the clause loop enforces the text
            must, must_not = reg.get(f, ([], []))
            for fr in must:
                checked += 1
                if norm(fr) not in text:
                    problems.append("%s.%s: missing fragment %r in the TYPE (comments and "
                                    "the value do not count)" % (label, f, fr))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("%s.%s: FORBIDDEN SHAPE - the field type contains %r"
                                    % (label, f, fr))
    return counts, pinned_all, checked


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
    # P-GATEINTEG: the structure-derived coverage check runs FIRST, and returns the set of
    # field names it pinned, so a fragment is never counted twice through two parsers.
    derived, pinned_fields, struct_checked = check_tracked_structures(root, problems)
    checked += struct_checked
    for field, frags in FINGERPRINTS:
        if field in pinned_fields:
            # P-GATEINTEG: a field of a tracked structure, already pinned above from the
            # PARSED structure. Only an entry that is not a field - the lowering_equivalence
            # theorem - still needs the name search below.
            continue
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
        for name, frags, must_not, whole in PARTIAL_SPEC_PINS:
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
            for fr in must_not:
                if norm(fr) in text:
                    problems.append(where + name + ": FORBIDDEN SHAPE - the declaration "
                                    "contains " + repr(fr))
        # P-SPECPIN: the postcondition each spec must retain, read off the CONCLUSION alone so a
        # decoy hypothesis in the binder list cannot satisfy it. See the note on the list.
        for name, must, must_not in PARTIAL_SPEC_CONCLUSIONS:
            text = field_text(pbody, name)
            if not text:
                problems.append("Partials." + name + ": SPEC DECLARATION NOT FOUND - the "
                                "theorem has been deleted, renamed, or demoted below a section, "
                                "so nothing pins its postcondition")
                continue
            c = conclusion(text)
            if not c:
                problems.append("Partials." + name + ": NO CONCLUSION - the theorem declares no "
                                "type, so there is no postcondition to retain")
                continue
            bad = triviality_problems(c)
            if bad:
                problems.append("Partials." + name + ": CONCLUSION IS TRIVIALLY DECIDABLE - "
                                + repr(c) + " (" + bad[0] + "), so the spec constrains nothing")
            for fr in must:
                checked += 1
                if norm(fr) not in c:
                    problems.append("Partials." + name + ": POSTCONDITION WEAKENED - the "
                                    "conclusion no longer says " + repr(fr)
                                    + " (P-SPECPIN: this is the postcondition shape the theorem "
                                    "was proved for; a repair has to move this pin and say why)")
            for fr in must_not:
                if norm(fr) in c:
                    problems.append("Partials." + name + ": POSTCONDITION TRIVIALISED - the "
                                    "conclusion contains " + repr(fr)
                                    + ", a shape that elaborates, builds, and asserts nothing")
        # The relations those conclusions are applications of: hollowing the definition guts all
        # eight wrapper specs without touching a theorem.
        for name, must, must_not in SPEC_RELATION_DEFS:
            text = field_text(pbody, name, whole=True)
            if not text:
                problems.append("Partials." + name + ": RELATION DEFINITION NOT FOUND - the "
                                "specs' conclusions are applications of it")
                continue
            for fr in must:
                checked += 1
                if norm(fr) not in text:
                    problems.append("Partials." + name + ": RELATION HOLLOWED - the body no "
                                    "longer says " + repr(fr))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("Partials." + name + ": RELATION HOLLOWED - the body "
                                    "contains " + repr(fr))
        # And the map that turns a Partial into the checkpoint its post must reach.
        cmap = root / CHECKPOINT_MAP_FILE
        if not cmap.exists():
            problems.append("Checkpoint.lean missing: %s - nothing pins which checkpoint each "
                            "spec's post reaches" % cmap)
        else:
            cbody = strip_comments(cmap.read_text(encoding="utf-8"))
            for name, must, must_not in CHECKPOINT_MAP:
                text = field_text(cbody, name, whole=True)
                if not text:
                    problems.append("Checkpoint." + name + ": MAP DEFINITION NOT FOUND - the "
                                    "specs' target checkpoints are computed by it")
                    continue
                for fr in must:
                    checked += 1
                    if norm(fr) not in text:
                        problems.append("Checkpoint." + name + ": CHECKPOINT MOVED - the map no "
                                        "longer says " + repr(fr)
                                        + " (P-SPECPIN: this is the Inv checkpoint a spec's post "
                                        "reaches; moving it silently moves the claim)")
                for fr in must_not:
                    if norm(fr) in text:
                        problems.append("Checkpoint." + name + ": CHECKPOINT MOVED - the map "
                                        "contains " + repr(fr))
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
                    # P-GATEINTEG: this loop used to recite the omegaOrder explanation for
                    # every clause it covered, which was wrong for the fourteen others once
                    # the coverage rule pulled them in. The reason now travels with the
                    # clause that needs it.
                    why = (" (P-ENV: omegaOrder must require the EXACT order, or a "
                           "generator equal to 1 satisfies it)" if field == "omegaOrder"
                           else " (P-GATEINTEG: the coverage rule found this clause unpinned"
                           " - a hypothesis no gate reads is a hypothesis that gets hollowed"
                           " to True)")
                    problems.append("Inv.%s.%s: CLAUSE WEAKENED - the type no longer "
                                    "says %s%s" % (struct, field, repr(fr), why))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("Inv.%s.%s: CLAUSE WEAKENED - the type contains the "
                                    "pre-P-ENV text %s" % (struct, field, repr(fr)))
        # P-RESTORE2: the .pairing arm of InvAt and LocalsOk, read as whole def bodies.
        for dname, must, must_not in INV_CLAUSES:
            text = field_text(ibody, dname, whole=True)
            if not text:
                problems.append("Inv." + dname + ": CLAUSE NOT FOUND - the definition that "
                                "carries the .pairing arm has been deleted or renamed, so the "
                                "conjuncts finalPairing_spec dropped have nothing to recover "
                                "from")
                continue
            for fr in must:
                checked += 1
                if norm(fr) not in text:
                    problems.append("Inv.%s: CLAUSE WEAKENED - the body no longer says %s "
                                    "(P-RESTORE2: the .pairing success and DualMSM clauses are "
                                    "what finalPairing_spec's dropped post conjuncts are "
                                    "recovered from; hollowing them hollows the specs)"
                                    % (dname, repr(fr)))
            for fr in must_not:
                if norm(fr) in text:
                    problems.append("Inv.%s: CLAUSE HOLLOWED - the body contains %s"
                                    % (dname, repr(fr)))
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
    # P-GATEINTEG: the two structure counts are the PARSED ones. Before this the line
    # printed len(FINGERPRINTS) and called it "LoweringCorrect fields", which was wrong
    # twice over: the list held a theorem among its fields, and it held no entry at all
    # for two of the structure's ten fields. A count the gate cannot lose is a count that
    # cannot be trusted.
    print("ok: %d statement fragments present in the TYPE across %d LoweringCorrect "
          "fields and %d PartialSpecs fields (both parsed from the structures), "
          "%d Surface pins, %d derived checks, %d blk-pin declarations, "
          "%d spec postconditions read off the CONCLUSION, %d spec relation definitions, "
          "%d checkpoint maps, "
          "%d EnvAgrees clause types, %d Inv clause groups, "
          "%d Holds clause types plus %d Holds decode pins, "
          "%d/%d/%d/%d fields parsed for EnvAgrees/VkSlotsAgree/ChallengesGood/"
          "Eip2537.Holds (coverage derived from the structures, not from the tables), "
          "and %d frozen statements (exact text, binders, trusted surface, doc "
          "provenance) against %d repair witnesses (comments stripped first)"
          % (checked, derived.get("LoweringCorrect", 0),
             derived.get("PartialSpecs", 0),
             len(SURFACE_PINS), len(DERIVED_CHECKS),
             len(PARTIAL_SPEC_PINS), len(PARTIAL_SPEC_CONCLUSIONS),
             len(SPEC_RELATION_DEFS), len(CHECKPOINT_MAP),
             len(ENV_CLAUSES), len(INV_CLAUSES),
             len(HOLDS_CLAUSES), len(HOLDS_DEFS),
             derived.get("EnvAgrees", 0), derived.get("VkSlotsAgree", 0),
             derived.get("ChallengesGood", 0), derived.get("Eip2537.Holds", 0),
             len(STATEMENTS_PINS), len(REPAIR_PINS)))


if __name__ == "__main__":
    sys.exit(main())

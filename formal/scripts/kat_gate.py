#!/usr/bin/env python3
"""Gate every known-answer check in the tree.

Each "#eval <expr>  -- expect <value>" line is a gate. Files are evaluated in
place so their own opens, local instances and helper definitions are in scope.
Negative controls are first-class: "-- expect false" passes by returning false.

Hardened after an adversarial review showed this script could pass while a KAT
was broken:

* The expected value used to be a non-space run, so an annotation with trailing
  prose ("-- expect true, and checks.sh asserts it") swallowed the tail into the
  expression and the check became silently UNGATED. pBaseKats_ok was in exactly
  that state, and corrupting pBase - the R-20 bug class - left the gate reporting
  success. Now the whole tail is captured and the first token is the expectation.
* The subprocess exit status was ignored, so a KAT file that does not compile
  could pass. A non-zero exit is now a hard failure for that file.
* Output lines are matched against a narrow set of shapes, so wrapped
  diagnostics cannot be harvested as values, and the count must match exactly:
  a gate that realigns its own expectations is not a gate.
* One bad file used to abort the whole run, hiding every later KAT. Failures
  are now collected and reported together.
* THE TOTAL WAS PRINTED AND NEVER ASSERTED (P-GATEINTEG, P-SCHED P6). Deleting a gate
  together with its "#eval ... -- expect ..." line simply made the report say one
  fewer check and exit 0. EXPECTED_KAT_TOTAL and EXPECTED_KAT_FILES pin both numbers
  now, and they are checked statically - before any file is run - so a deleted gate
  reddens in a second. A deliberate change has to move the pin.
"""
import re
import subprocess
import sys
import pathlib

# expression, then an optional "-- expect <value>" plus any prose after it.
# The expectation stops at whitespace OR a comma, so "-- expect true, and ..."
# reads as true and "-- expect [8]" reads as [8]; an expectation value itself must
# not contain a comma.
EVAL = re.compile(
    r"^#eval\s+(?P<expr>.+?)"
    r"(?:\s+--\s*expect\s+(?P<exp>[^\s,]+).*)?\s*$"
)

# P-GATEINTEG (P6): THE TOTAL IS ASSERTED, NOT PRINTED.
#
# WHY. The KAT section used to end at "ok: %d annotated known-answer checks pass
# across %d files" and exit 0 whatever the number said. Deleting a gate therefore went
# unseen: P-SCHED P6 removed a "def X_ok : Bool := ..." together with its
# "#eval X_ok -- expect true" line, and the whole suite stayed green while the printed
# count quietly dropped by one. A count that is reported and never compared is a report
# wearing a gate's clothes - the same defect P-STATGATE found in the axiom probe.
#
# WHY AN EXACT PIN AND NOT A FLOOR. "at least N" would still let the count fall by one
# every package as long as it stayed above the floor, which is how a register rots. An
# exact total means an unexpected drop reddens AND a deliberate change has to move this
# line - so the diff says out loud that a gate was added or removed, which is the whole
# point of a pin. Both numbers are static properties of the tree, computed BEFORE any
# "lake env lean" runs, so a deleted gate reddens in a second instead of eight minutes.
# P-INLINE (D-P39) moved both pins deliberately, in the commit that added the gates.
# Midfall/Lowering/InlineConstants.lean is a NEW file in the suite carrying THREE
# '#eval ... -- expect true' gates (contractConstantsShape_ok, inlineShadowingKats_ok,
# naiveTransformIsWrong_ok), so the file count goes 96 -> 97 and the total 1340 -> 1346: three
# gates in the new module and three in RunEmitted (inlineFuelIsEnough_ok,
# inlinedArtifactArmRuns_ok, inlineTheLocalsToo_stuck_ok). No gate was deleted; the delta is +6/+1
# and nothing else moved.
# P-DET moved both pins deliberately, in the commit that added the gates.
# Midfall/Instances/RunShellInhabited.lean carried NO '#eval ... -- expect' line before P-DET, so it
# was not in the suite at all; P-DET adds TWO (dispatcher_reverts_zero_bytes_ok,
# arm_reverts_four_bytes_ok), which are the independent interpreter measurement of the D-P42 entry-path
# difference. So the file count goes 97 -> 98 and the total 1346 -> 1348. No gate was deleted; the
# delta is +2/+1 and nothing else moved.
# P-RUNLEG moved both pins deliberately, in the commit that added the gates.
# Midfall/Instances/RunLegRouted.lean is a NEW file in the suite carrying FOUR '#eval ... -- expect
# true' gates: routed_comparison_ok (the routed comparison measured through the fuel interpreter:
# closed arm 4 bytes, dispatcher over the OPEN arm STUCK, dispatcher over the CLOSED arm 4 bytes,
# open arm STUCK), unroutable_comparison_ok (the same programs at the empty calldata: 4, 0, 0 - the
# two-mechanisms contrast), routed_calldata_is_the_routed_one_ok (the exhibit discriminates: the
# wrong-selector, truncated and empty calldata all fail the dispatcher's own tests) and
# artifact_both_inputs_ok (the real solc artifact reverts with zero bytes at BOTH inputs). So the
# file count goes 98 -> 99 and the total 1348 -> 1352. No gate was deleted; the delta is +4/+1 and
# nothing else moved.
# D.1 (GEN/PORT) adds Midfall/Instances/PoseidonInputs.lean: a NEW file in the suite carrying NINE
# '#eval ... -- expect true' gates (the pure VK/plan round-trip, the two IO-equality KATs the card
# asks for, the pure model's .ok and validate_layout, the ctx/blocks equality, the pure whole-file
# render, and the pure-vs-derived model cross-check). So the file count goes 99 -> 100 and the total
# 1352 -> 1361. No gate was deleted; the delta is +9/+1 and nothing else moved.
# D.2 (ALG/PORT) adds Midfall/Instances/PoseidonEnv.lean: a NEW file in the suite carrying FOURTEEN
# '#eval ... -- expect true' gates (the strict vk.json/params.json parse with every hex width pinned;
# the domain's k, n and extended_k; omega and omega_inv against the file's own hexes including the
# primitive-64th-root half that a degenerate omega = 1 would fail; every column count; all three query
# lists read back as the (column, rotation) pairs the exporter wrote; cs_degree with the quotient-degree
# clause of WellFormed that DOES survive the fixture; the imported transcript_repr; the 27 compressed
# commitments re-encoding to themselves; those same 27 pinned coordinate by coordinate against D.1's
# artifact words; the G2 encoder's shape and non-constancy; params.json's byte-level facts; the
# root-of-unity repair together with the clause that says the unrepaired root disagrees; the WellFormed
# gap pinned as a falsifiable obligation rather than hidden; and the three counts D.1's typed-in meta
# agrees with vk.json on). So the file count goes 100 -> 101 and the total 1361 -> 1375. No gate was
# deleted; the delta is +14/+1 and nothing else moved.
# D.3 (GEN/KAT) adds Midfall/Instances/PoseidonCoherence.lean: a NEW file in the suite carrying
# EIGHTEEN '#eval' gates. Fifteen expect true and three record a measured NEGATIVE as its own
# expectation, which kat_gate has always treated as first-class: check 1's `Valid.layout` clause
# (false, the typed-in meta's protocol is the default so fromProtocol empties every commitment
# section), check 1's `proofLen == trace.proof_len` clause (false, 4320 repacked against 2640
# compressed - the card conflated the two widths), and check 2's `Valid.circuitMeta` clause (false,
# D.2's gap A on one side and constraintSystemMetaDefault on the other). The other fifteen are the
# positive half: the derived proof length as a value (1792), the layout's slot schedule against the
# fixture's 72 reads and 2640 bytes, the two-width tiling, the meta constructor's .ok, the
# field-by-field attribution of the check-2 mismatch, the three agreeing counts, the ten
# Lean-squeezed Fiat-Shamir challenges against transcript_log, the whole 327-comparison replay with
# an empty failure list, the derived absorb prefix, three one-byte corruptions of proof.bin with
# their first-differing challenge indices (6, 0 and none), the reddened replay on a corrupt bundle,
# and two labelled DIAGNOSTICS that localise check 3's blocker to the render's G1 codec rather than
# to the layout or the decoder. No gate was deleted; the delta is +18/+1 and nothing else moved.
# DG.0 moved EXPECTED_KAT_TOTAL 1393 -> 1397 deliberately, and names the commit that added the gates.
# The four are 2041977 (F.1: Rust CAN export the constraint system), all four in
# Midfall/Instances/PoseidonEnv.lean: poseidonMeta_derived_ok (the plan's ConstraintSystemMeta comes
# out of the ported DERIVATION, not a transcription - poseidonMetaDerived?.isOk with numFixeds 19, 49
# pcsQueries, 6 commonPolys, numEvals 48); poseidonMeta_matchesTypedIn_ok (the derived counts
# reproduce all eleven counts D.2/P-13 typed in from the artifact, plus the four fields the
# observation had no source for); poseidonLookup_chunks_kat_ok (the ported LogupBatchedArgument
# .numChunks over the imported expression trees answers what Rust's num_chunks_at_cs_degree returned,
# i.e. [1], so the exported trees are load-bearing and not merely well-formed); poseidonCs_counts_ok
# (5 gates / 11 gate polys agree across the exporter's two channels, with the trashcan name "&&&&&&&"
# and gates[4] = partial_round_gate pinned as the reference produced them). F.1 also swapped
# poseidonWellFormed_open_ok for poseidonWellFormed_closed_ok, which is net zero, and the file count
# does not move: PoseidonEnv.lean was already in the suite. So the delta is +4/+0 and nothing else
# moved - the pin was simply left red for two cards rather than bumped silently.
# THE SAME COMMIT mis-spelled two annotations as "-- expect TRUE" (uppercase) while Lean prints
# `true` and this gate compares case-sensitively: DeployedProfile.lean pcs_deployedGap_measured_ok
# and PoseidonCoherence.lean check2_circuitMeta_holds. DG.0 re-spelled them to lowercase and changed
# NO expectation: both were run through `lake env lean` before this line moved and both print true.
# They were already counted as annotated gates (the regex takes any non-space token as the
# expectation), so the measured total is 1397 before and after the spelling fix - what the typo hid
# was the COMPARISON, which pass 1's total failure never let run.
# G1.2 moved EXPECTED_KAT_TOTAL 1397 -> 1400 deliberately: three NEW gates in
# Midfall/Lowering/GenAst.lean - the quotient helper region emitter the G1.2 batch splices into
# Program.mainAsmRaw - and not a re-spelling or a replacement of anything.
# emitQuotientHelpersRegion_ok (the q_program_fail + q_pow5 region against the text port's render,
# with the limb7 / wide-limb7 flags hypothesised FALSE on the gate's own face);
# emitQuotientHelpersDetectsPerturbation_ok (two one-literal mutations, one per definition, each
# reddening BOTH the token row and stmtsBeq - the teeth); emitQuotientHelpersFlagSelects_ok (the
# definition list and the token count move with the flag, so the emitter is a function of the Model
# field and not a constant). No gate was deleted or edited and the file count does not move
# (GenAst.lean was already in the suite). All three were run through `lake env lean` before this
# line moved and all three print true.
# OBJ.1 (V3 row 31, the M2 entry) adds Midfall/Instances/YulParseKats.lean: a NEW file in the suite
# carrying SEVENTEEN annotated '#eval ... -- expect' gates, plus the card's two unannotated acceptance
# prints. The seventeen: the main-block and guard-block token round trips (mainRoundTrip_ok,
# guardRoundTrip_ok); the two acceptance lines pinned as values (mainRtLine_ok, which pins
# "parsed stmts=74 roundTrip=true tokens=14054", and guardRtLine_ok, which pins
# "parsed stmts=1 roundTrip=true tokens=52"); one stmtsBeq gate per existing emitter output (helpers,
# vkLoading, transcriptParser, lagrange, quotientLin, pcs, finalPairing, traceReturn); the one-literal
# mutation falsifier for those eight (regionMutationTeeth_ok, which also asserts the mutation really
# changes the text); and FOUR negatives - an unbalanced-brace stream, the real main block with its
# closing brace dropped, an inner block that never closes, and trailing tokens after the closing brace
# (W12: a parser with no falsifier is not a gate). The two unannotated prints are the card's acceptance
# lines verbatim; they print a String containing spaces, which this script cannot annotate (an
# expectation is one token), and the same two facts ARE gated by mainRtLine_ok and guardRtLine_ok. No
# gate was deleted or edited. So the file count goes 102 -> 103 and the total 1400 -> 1417: the delta
# is +17/+1 and nothing else moved. All seventeen were run through `lake env lean` before
# this line moved.
# OBJ.5 (V3 row 39) adds Midfall/Instances/ObjectFingerprint.lean: a NEW file in the suite carrying
# FIVE annotated '#eval ... -- expect' gates - the fingerprint of the OBJECT the headline is about,
# the program `asmOf poseidonPv poseidonM 0 0`, which is COMPUTED by the emitters and so is invisible
# to `Frozen.sha256` (three files, none of them an emitter). The five: the token count of
# `EVM.print` of that program, pinned as the literal 14109; the `keccak256` of the same printed
# string, pinned as the literal 0x3149ae4f...bef176; the two halves together as one Bool
# (`objectFingerprint_ok`, the same fact as the `native_decide` theorem `object_fingerprint` in the
# file, in the shape this script can name); the IN-TREE falsifier (`objectFingerprintTeeth_ok`: one
# literal of the linearization payload offset moves the digest and NOT the token count, which is why
# both halves are pinned and not one); and the guard that the object is the INLINED program and not
# `mainAsmRaw` (`objectIsTheInlinedProgram_ok`), which is the card's own guidance. No gate was
# deleted or edited. So the file count goes 104 -> 105 and the total 1440 -> 1445: the delta is
# +5/+1 and nothing else moved. All five were run through `lake env lean` before this line moved.
# OBJ.6 (V3 row 40) adds Midfall/Instances/PlanNewKats.lean: a NEW file in the suite carrying FOURTEEN
# '#eval ... -- expect true' gates, all of them a ported quotient-glue function checked against DATA THE
# RUST EMITTED and not against a second Lean computation. frFieldCtx_matchesArtifact_ok (the R9 field
# dictionary, DELTA against curves/src/bls12_381/fq.rs:492 and powNat against a hand-written
# square-and-multiply); quotientPlan_shape_ok (inline 4 / items 9 / native 3 / perm 7 / lookup 3 / tail 1
# / maxPower 21, the four identity counts against the protocol plan cs.json yields and the max power
# against Halo2Verifier.sol); quotientBuild_matchesPayload_ok (THE HEADLINE: the emitted bytecode and
# const table equal the two quotient sections of Halo2VerifyingKey.sol, 88 bytes / 1 const / max stack 2);
# quotientProgram_matchesTypedIn_ok (all twelve template-program fields against the program read out of
# the deployed artifact); quotientNativeScratchWords_matchesStackRegion_ok (25 words, corroborated by the
# artifact's own 0x6c60 spill ceiling); compactQuotientProgramFor_matchesBuild_ok; quotientManifest_
# preservesStream_ok (the QVM:388-473 bridge); quotientOpcodeUsage_table_ok and quotientMemUsage_table_ok
# (31 and 9 singleton probes, so a transposed row is visible); quotientTemplateProgram_reservationAborts_ok
# (the four QRS:202/:204/:205/:209 aborts FIRED); templateProgramPanicSites_areTheRecordedOnes_ok (reads
# quotient.rs and pins every cited line, the panicSites pattern); quotientPlan_inlineCountFalsifier_ok (the
# card's falsifier: inline count 3 changes the program bytes, and the local copy is first checked to
# reproduce the port at 4); showSourceDebug_shapes_ok; validateExecutionManifest_rejects_ok (both Err
# messages fired). Midfall/Generator/PlanNew.lean carries NO gate of its own - it is the port, and a
# theorem-bearing Generator file may not import the fixture. So the file count goes 105 -> 106 and the
# total 1445 -> 1459. No gate was deleted; the delta is +14/+1 and nothing else moved.
# OBJ.7 (V3 row 41) adds Midfall/Instances/GeneratedKats.lean: a NEW file in the suite carrying THIRTEEN
# '#eval ... -- expect true' gates, every one of them either pinned to data the Rust emitted or labelled in
# place as having no direct Rust witness. vkReceiverRefactor_wrapperEqualsCore_ok (the card's Do 1: the four
# Vk.lean defs now take (meta, numInstances) and the &self wrappers return the same values - a Lean signature
# fact, stated as such); generateAll_planFields_matchesArtifact_ok (VK_MPTR, PROOF_LEN and the instance count
# READ OUT of Halo2Verifier.sol by the Evm.lean artifact readers, plus sorted_simple); generateAll_metaIsConverged_ok
# (REVIEW-V3 A-1 pinned to the artifact: raw meta has num_point_sets 0 and yields 4224 proof bytes, the plan's
# converged meta yields the deployed 4320); generateAll_textIsTheArtifactButForBuildId_ok (THE HEADLINE: the
# contract rendered from the generator's own model equals the tracked artifact in 3023 of 3024 lines and 175908
# of 175908 bytes, and the one differing line is named as the BUILD_ID line on both sides);
# generateAll_invariantsOk_ok (the pass, plus TWO plans that are REJECTED with the Rust's own messages, so the
# checker is shown to have teeth); generateAll_certificationOk_ok (the dual-build certification passes AND THE
# FINDING: at poseidon the limb-opcode baseline is byte-identical to the optimized build because no limb opcode
# appears in the artifact's own used_ops, so the certification is vacuous at this fixture in Rust too - and the
# gate proves the function is not a no-op by rejecting a build of a different item stream);
# newFromVk_programIsTheDeployedOne_ok (all twelve template-program fields of the CONSTRUCTOR's plan against the
# deployed program); compactBlocksOf_matchesArtifact_ok (five of six quotient block families equal to the Yul
# sliced out of Halo2Verifier.sol, the sixth equal flattened with the slicing reason given);
# generateAll_falsifierDeltaAndOmega_ok (delta := 2 reddens 3 lines and the block record; a flipped omega word
# is NOT refused - the PayloadAgrees hole, measured); generateAll_falsifierPayloadWord_ok (one flipped
# quotient_program word -> vk.rs:457, message included); generateAll_falsifierNoReservation_ok (the parsed
# payload with no reservation fields -> quotient.rs:202 and NOT the card's :204, OBJ.6's handoff re-measured);
# generatedPanicSites_areTheRecordedOnes_ok (reads plan.rs, vk.rs and artifacts.rs and pins every cited line,
# including the card's own off-by-one: compact_quotient_blocks is PL:391-406 and not :381-394);
# generateAll_layoutValidate_ok (the ART:337-339 guard passes AND rejects two drifted models with the Rust's
# messages). Midfall/LoweringV2/Generated.lean and Midfall/Generator/PlanNew.lean carry NO gate of their own -
# they are the port, and a theorem-bearing file may not import the fixture. So the file count goes 106 -> 107
# and the total 1459 -> 1472. No gate was deleted; the delta is +13/+1 and nothing else moved.
# ST.1c moved both pins deliberately, in the commit that landed the V3 staging surface on the POST-M2
# baseline. THREE NEW FILES carry the +28/+3, every one of them an annotated `#eval ... -- expect ...`:
# Midfall/LoweringV3/Statements.lean (2: calldataOfV3_witness_ok -- expect true, the repaired
# repack-then-encode reproduces the frozen composition's calldata at the p = 17 toy codec and decodes
# back; frozenCalldata_isOk -- expect false, the falsifier: the frozen repack-then-repack path never
# returns .ok at the same data), Midfall/Instances/StatementsV3Deploy.lean (19) and
# Midfall/Instances/StatementsV3Falsifiers.lean (7). ST.1b's 25 measurement wrappers are carried with
# them, so NO line in any of the three is an unannotated #eval. The only two unannotated #eval lines
# in the whole tree are OBJ.1's own acceptance prints (YulParseKats.lean:49 and :51), documented above
# at this file's OBJ.1 note and duplicated there by mainRtLine_ok / guardRtLine_ok; ST.1c does not touch
# that file. No gate was deleted, edited or re-spelled anywhere else: the delta is +28/+3 and nothing
# else moved.
# T3.1 moved both pins deliberately, in the commit that landed the wp engine. ONE NEW FILE carries
# the +6/+1 and every gate in it is an annotated `#eval ... -- expect ...`, all six in
# Midfall/Yul/WpFalsifiers.lean: addIsValued_ok (true - stepOp Op.add returns EXACTLY ONE word, the
# premise FALSIFIER 1 turns on); wpAtZero (false - FALSIFIER 2, and the #eval is decided by an
# `isFalse` instance that IS the theorem, so the print is checked against the proof and not against a
# second implementation); interpZeroFuel_ok (true - the executable mirror: Interp.run at fuel 0
# reports outOfFuel, so fuel bounds termination on both sides of honest_adequacy); wpNondetFixesResponse
# (false - THE KAT: the DEMONIC Bopen cannot fix the staticcall response at Bridge.nondetBlock, proved
# by wpS_sound against the failing run Bridge.run_staticcall_mstore exhibits); execBuiltinFixesByte_ok
# (true - the functional contrast: execBuiltin DOES fix the byte, which is why T3.2's existence half
# runs at Bfun and not at Bopen); honestRunByte_ok (true - honestExec runs nondetBlock to a normal
# outcome with byte 31 CLEAR, measured, so the program honest_adequacy quantifies over is a program
# that runs). No gate was deleted, edited or re-spelled anywhere else: the delta is +6/+1 and nothing
# else moved. The engine itself (Midfall/Yul/Wp.lean, Midfall/Yul/WpBridge.lean,
# Midfall/LoweringV2/HonestExec.lean) carries NO #eval line: it is proved code, and its axiom sets are
# pinned by `#assert_axioms` in the falsifier file, which is a build error and not a print.
# T3.11 (V3 W14 exhibit, D-P71: A TEST, NEVER A PREMISE OF A PROOF) adds Midfall/Instances/PoseidonExhibit.lean:
# a NEW file in the suite carrying FIVE annotated '#eval ... -- expect true' gates - the executable exhibit that
# runs the emitted program at the open honest dialect (Midfall/LoweringV2/HonestExec.lean, T3.1) on the F1
# bundle's real calldata, and shows a byte-flip mutant NOT reaching that outcome. The five:
# fixtureCalldata_isTheBundleBytes_ok (the card's Needs as a term: Lowering.repackThenEncode on the bundle's
# proof.bin + instances.json reproduces calldata.bin BYTE FOR BYTE, 4,484 bytes, keccak pinned - REF.14's
# question, answered equal); entryFrame_shape_ok (the frame is the theorem's EntryFrame as far as a Bool can
# say: selector, zero call value, VK runtime and codehash at the address the program reads, the free-memory
# clause, D-P64's length bound, DeploymentV2's disjointness); exhibitProg_isThePinnedObject_ok (the program run
# is structurally the object OBJ.5 fingerprints, so the exhibit is about the headline's program);
# fixture_returns_abiTrue_ok (THE FIXTURE RUN: Interp.run from the entry-like frame halts with
# return(abiTrue), measured 22.3 s at fuel 10,000,000 - stuck and outOfFuel both read as no-halt and so fail
# the gate); mutants_revert_ok (THE TEETH: eight one-bit / one-byte mutants of the same calldata - three head
# words, the instance count, a truncation, a trailing byte, two G1 x-coordinate pad bytes - each reverting with
# the four bytes the render's OWN const table assigns to ERR_BAD_CALLDATA_SHAPE or ERR_BAD_POINT_ENCODING, so
# the payloads are computed and not pasted). No gate was deleted or edited. So the file count goes 111 -> 112
# and the total 1520 -> 1525: the delta is +5/+1 and nothing else moved. All five were run through
# 'lake env lean' before this line moved, and the whole file evaluates in 28.9 s (the card's bound is 30 s; the
# single 22.3 s fixture run is what the budget buys - two further measured mutants, the ERR_PRECOMPILE_FAILED
# class at 6.99 s and the instance-word flip that still returns abiTrue under the mocked PairingProduct, are
# recorded in the file's header instead of gated, for that reason).
# OBJ.4 moved both pins deliberately: Midfall/Instances/ConstsKats.lean is a NEW file in the suite
# carrying FIFTEEN '#eval ... -- expect ...' gates — the clause at the fixture, its five conjuncts,
# the three plan-view falsifiers, the model-only non-falsifier, the eight lookups, the runtime-length
# data fact and the two residual pins. No gate was deleted; the delta is +15/+1 and nothing else moved.
EXPECTED_KAT_TOTAL = 1540
EXPECTED_KAT_FILES = 113

# Only these shapes count as #eval output.
#
# P-TRUNK HARDENING (a defect that cost two packages a gate run each). The bracket arm
# used to harvest ANY stdout line that begins with [ and ends with ], which is exactly
# the shape of a linter hint: Lean prints its fix-it block
#
#   Hint: Replace the deprecated name:
#     [apply] simp [foo]
#
# on the SAME stream as #eval output, so "[apply] simp [foo]" was counted as a fake
# value and checks.sh went rc=1 with "printed 6 value(s) for 5 #eval line(s)" on a
# file lake build accepted. R-53 below is the same class from the other direction
# (prose inside a block comment read as a gate). Two anchors now apply:
#
#   * a real #eval value is the WHOLE line and has nothing after its closing bracket,
#     so a line with ] followed by more text is a diagnostic, not a value;
#   * a line that opens with a bracketed word ([apply], [warning]) is a diagnostic.
#
# A genuine list value ([], [1, 2], ["a"], [pointAndScalar]) satisfies both.
VALUE = re.compile(r"^(true|false|-?\d+|\"[^\"]*\"|\[.*\])$")
DIAG = re.compile(r"^\[[A-Za-z_][A-Za-z0-9_.]*\][ \t]|\][ \t]+\S")


def is_value(line):
    """True if `line` is a #eval result rather than a linter diagnostic."""
    return bool(VALUE.match(line)) and not DIAG.search(line)


def gate_lines(text):
    """Return the real `#eval` gate lines of a file.

    A gate must start the line AND be at block-comment depth zero. Lean block
    comments nest (`/--` opens, `-/-` nests, `-/` closes), and prose inside one
    can wrap so that a line begins with `#eval time.` - which the previous
    `startswith` test counted as a gate, producing a bogus "printed N values for
    N+1 #eval lines" failure. Recorded as R-53.
    """
    depth = 0
    out = []
    for line in text.splitlines():
        stripped = line.strip()
        is_gate = depth == 0 and stripped.startswith("#eval ")
        i = 0
        while i < len(line):
            if line.startswith("/-", i) and i + 2 < len(line) and line[i + 2] == "-":
                depth += 1          # `/--` open, or `-/-` nested open
                i += 3
            elif line.startswith("-/", i) and depth > 0:
                depth -= 1
                i += 2
            else:
                i += 1
        if is_gate:
            out.append(stripped)
    return out


def main() -> int:
    root = pathlib.Path("Midfall")
    if not root.is_dir():
        print("kat_gate: run from the formal/ directory", file=sys.stderr)
        return 2

    files = sorted(
        p for p in root.rglob("*.lean")
        if gate_lines(p.read_text(encoding="utf-8"))
    )
    if not files:
        print("kat_gate: no KAT files found - that is itself a failure", file=sys.stderr)
        return 2

    checked = 0
    uncommented = 0
    problems = []

    # ---- PASS 1: read the tree and collect every gate line, WITHOUT running lean.
    # The total is asserted here, before anything expensive, so a deleted gate is a
    # one-second failure and not an eight-minute one (P-GATEINTEG / P-SCHED P6).
    per_file = []
    annotated = 0
    for path in files:
        specs = []
        for stripped in gate_lines(path.read_text(encoding="utf-8")):
            m = EVAL.match(stripped)
            if m is None:
                problems.append("%s: unparsable #eval line: %r" % (path, stripped[:70]))
                continue
            exp = m.group("exp")
            # An expectation is a single token, but prose may follow it with
            # no separator other than a colon or comma ("-- expect true: g1 is
            # not the identity"). Strip trailing punctuation so the value is
            # 'true' there and '[8]' in '-- expect [8]'.
            if exp is not None:
                exp = exp.rstrip(".,:;")
            else:
                uncommented += 1
            if exp is not None:
                annotated += 1
            specs.append((m.group("expr"), exp))
        if not specs:
            continue
        per_file.append((path, specs))

    if len(per_file) != EXPECTED_KAT_FILES or annotated != EXPECTED_KAT_TOTAL:
        print("KAT GATE FAILED (total moved):")
        if len(per_file) != EXPECTED_KAT_FILES:
            print("  KAT FILE COUNT MOVED - %d files carry a #eval gate, pinned %d. A file"
                  % (len(per_file), EXPECTED_KAT_FILES))
            print("  whose last gate was deleted has left the suite silently.")
        if annotated != EXPECTED_KAT_TOTAL:
            print("  KAT TOTAL MOVED - %d annotated known-answer checks in the tree, pinned"
                  % annotated)
            print("  %d (%+d). Deleting a gate and its '#eval ... -- expect ...' line is"
                  % (EXPECTED_KAT_TOTAL, annotated - EXPECTED_KAT_TOTAL))
            print("  exactly what this catches (P-SCHED P6): the count used to be printed")
            print("  and never asserted. If the change is deliberate, move EXPECTED_KAT_TOTAL")
            print("  in scripts/kat_gate.py and say why in the commit.")
        return 1
    if problems:
        print("KAT GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1

    # ---- PASS 2: run each file and compare the values it prints.
    for path, specs in per_file:
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            blob = (proc.stdout + proc.stderr).strip().splitlines()
            detail = blob[0] if blob else "no output"
            problems.append("%s: does not elaborate (exit %d): %s"
                            % (path, proc.returncode, detail[:120]))
            continue

        values = [l.strip() for l in proc.stdout.splitlines() if is_value(l.strip())]
        if len(values) != len(specs):
            problems.append("%s: printed %d value(s) for %d #eval line(s)"
                            % (path, len(values), len(specs)))
            continue

        for (expr, exp), actual in zip(specs, values):
            if exp is None:
                continue          # counted in pass 1; nothing to compare against
            checked += 1
            if actual != exp:
                problems.append("%s: %s expected %r, got %r"
                                % (path, expr[:60], exp, actual))

    # Belt and braces: the total was asserted statically, so every annotated gate must
    # also have been COMPARED. A file that failed to elaborate skips its gates, and this
    # is the line that stops such a skip reading as a pass on the remaining ones.
    if checked != annotated:
        problems.append("only %d of the %d annotated gates were compared - a KAT file was"
                        " skipped, which is a failure and not a smaller pass"
                        % (checked, annotated))

    if problems:
        print("KAT GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1

    print("ok: %d annotated known-answer checks pass across %d files (both pinned:"
          " %d and %d in scripts/kat_gate.py)"
          % (checked, len(per_file), EXPECTED_KAT_TOTAL, EXPECTED_KAT_FILES))
    if uncommented:
        print("note: %d unannotated #eval line(s) are NOT gated; add" % uncommented)
        print("      \"-- expect <value>\" to gate them")
    return 0


if __name__ == "__main__":
    sys.exit(main())

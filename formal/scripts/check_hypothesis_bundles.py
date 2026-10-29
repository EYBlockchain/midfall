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
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_duplicate_facts import (ARROW, STR, definitions, mentions, split_top,
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
        "exhibit": ("bundle_deployment",
                    ["SupportedS", "DeploymentW", "EnvAgrees"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"], ["g1Valid", "Nat.Prime pBase", "Nat.card G1Frame = r"]),
                 ("gap_runLeg_unexhibited", ["RunVerifier"])],
    },
    {
        "field": "verifier_complete",
        "exhibit": ("bundle_deployment",
                    ["SupportedS", "DeploymentW", "EnvAgrees"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"], ["g1Valid", "Nat.Prime pBase", "Nat.card G1Frame = r"]),
                 ("gap_runLeg_unexhibited", ["RunShell"])],
    },
    {
        "field": "only_two_outcomes",
        "exhibit": ("bundle_deployment",
                    ["SupportedS", "DeploymentW", "EnvAgrees"]),
        "gaps": [("gap_runLeg_unexhibited", ["RunShell"])],
    },
    {
        "field": "end_to_end_noAcc",
        "exhibit": ("bundle_headlineCore",
                    ["SupportedS", "DeploymentW", "irCheck ir = true",
                     "RunContractIR", "EnvAgrees"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"], ["g1Valid", "Nat.Prime pBase", "Nat.card G1Frame = r"])],
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
                     "RunContractIR", "EnvAgrees"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"], ["g1Valid", "Nat.Prime pBase", "Nat.card G1Frame = r"])],
    },
    # P-4a2: the three legs the field arithmetic closes, exhibited as ONE conjunction.
    # Registered separately (rather than replacing an entry) so the DeploymentW and IR
    # certifications above stay in force; the discovery rule is a set membership test,
    # so a second entry for a field it already covers is additive, not a duplicate.
    {
        "field": "lowering_equivalence",
        "kind": "theorem",
        "exhibit": ("bundle_envAgrees", ["SupportedS", "EnvAgrees"]),
        "gaps": [("gap_holds_unexhibited", ["Eip2537.Holds"], ["g1Valid", "Nat.Prime pBase", "Nat.card G1Frame = r"])],
    },
]

# A bundle that is provably EMPTY must be refuted by ONE declaration naming every conjunct,
# for the same reason an inhabited bundle must be exhibited by one: halves certify nothing.
#
# P-CURVE found the fourth headline conjunct unsatisfiable AS WRITTEN (g1Decodes needed
# infinitely many preimages of a finite group). P-HOLDS repaired that clause (R-63 level 1),
# so the refutation of the LIVE bundle had to move from the clause to the codec:
# Instances/ObligationsGates.lean:bundle_holds_empty is now proved through g1Valid, because
# the fixture's codec is the exponent model and its bytes are not curve points. The pinned
# OLD text keeps its own joint refutation, bundle_holdsOld_empty, so the regression stays
# certified: if the width condition is dropped from the live clause again the first entry goes
# stale (its proof no longer typechecks) and the fingerprint gate reddens the same edit.
#
# If a real curve codec is ever installed at the fixture, bundle_holds_empty stops being
# provable and the entry must be DELETED and replaced by an exhibit - which is the point: the
# gate reddens if the gap silently returns OR if a refutation goes stale without an exhibit
# replacing it.
REFUTATIONS = [
    ("bundle_holds_empty", ["BlkIsEmitter", "SupportedS", "EnvAgrees", "Eip2537.Holds"]),
    ("bundle_holdsOld_empty",
     ["BlkIsEmitter", "SupportedS", "EnvAgrees", "Eip2537.HoldsOld"]),
]


# ---------------------------------------------------------------------------
# SPEC-THEOREM BUNDLES (P-BUNDLE).
#
# WHY THIS IS HERE. The ten *_spec theorems in Midfall/Lowering/Partials.lean are the
# per-partial claims the lowering programme rests on, and their hypothesis bundles live in
# a THEOREM BINDER LIST - which is outside the schema of every gate that existed before
# this package: check_duplicate_facts scans STRUCTURE FIELDS in a fixed file list, and
# check_hypothesis_bundles scanned fields of LoweringCorrect plus one named theorem. A
# theorem binder is neither. P-PLANVIEW found the hole; P-BUNDLE found what fell into it:
# pcs_spec bound hblk, hsup, henv, hperm, hcd, hinst, hsnap and NO Eip2537.Holds, while
# its proof needs Holds.g1Msm1 and Holds.g1Add, because Block 5 is a G1MSM staticcall and
# Block 6 is two G1MSM-1s and two G1ADDs, and the Inv clauses at the .pcs post read those
# slots as codec images (Inv.lean:735-739). The theorem was unprovable as stated and every
# gate in the repository was green.
#
# THE RULE, AND WHY IT IS NOT A HAND-WRITTEN LIST. "A spec theorem whose conclusion
# depends on precompile behaviour must bind Holds" would be worthless as a list of ten
# names, because a list is exactly the thing that goes stale. So the requirement is DERIVED
# here from one Lean definition, partialEip2537Targets, which Partials.lean proves equal to
# what the EMITTER reaches (partialEip2537Targets_ok, a #eval gate kat_gate.py runs): for
# each partial, the EIP-2537 addresses reachable from GenAst.emitPartial for that plan
# view, closed under the helper definitions the blk pin puts in scope. The gate reads each
# spec theorem's conclusion to find WHICH partial it is about and demands Holds iff that
# partial's row is non-empty.
#
# THREE INDEPENDENT LEGS, which is the point:
#   * the Lean KAT ties the table to the emitter - change the emitter, the KAT goes red;
#   * this gate ties the binders to the table - drop a binder, the gate goes red;
#   * this gate ALSO rejects a Holds binder on a partial whose row is EMPTY, so the fix
#     cannot be laundered by binding the hypothesis everywhere. A decorative hypothesis is
#     the defect attack.md names, and neither the old form of this gate nor the fingerprint
#     gate could see it.
#
# WHAT IT STILL CANNOT DO, stated rather than hidden. It is a text gate: it checks that a
# binder names Eip2537.Holds applied to the Surface's own codec, encoder and product. It
# cannot check that Holds is the RIGHT hypothesis for the conclusion, only that a
# hypothesis about precompile behaviour is present. Only a proof is a semantics check. And
# the classifier reads LITERAL staticcall addresses: a call whose address operand is a
# variable counts as reaching (conservative), and a call into a helper the emitter does not
# define is invisible to it. Partials.lean records those unresolved helpers as data -
# batch_invert and scalar_inv (both modexp, which is arithmetic and must NEVER require
# Holds) and validate_public_accumulator (which in the reference runs G1MSM and G1ADD, so
# vkLoading_spec is a LATENT instance of exactly this hole and this gate will demand Holds
# there by itself the moment the helper is emitted).
# ---------------------------------------------------------------------------

SPEC_FILE = "Midfall/Lowering/Partials.lean"
CHECKPOINT_FILE = "Midfall/Lowering/Checkpoint.lean"
HOLDS_TOKEN = "Eip2537.Holds"
# The hypothesis has to be about THIS Surface's codec, encoder and product. A binder
# 'Holds c c2 product' for some unrelated codec would satisfy a bare token test and say
# nothing about the program the theorem speaks about - the reason
# check_statement_fingerprints matches fragments and not names.
HOLDS_ARGS = ["S.E.g1", "S.encG2", "product"]
TABLE_DEF = "partialEip2537Targets"
TABLE_KAT = "partialEip2537Targets_ok"
PERTURB_KAT = "partialEip2537Targets_detectsPerturbation_ok"
# what the Lean pin has to walk, named so deleting the walk reddens this gate
TABLE_KAT_TOKENS = ["emittedEip2537Targets", "GenAst.pcsFixturePlan",
                    "bundleAccFixturePlan", "emittedUnresolvedCalls"]
# How a spec conclusion names the partial it is about: the BLOCK position of the claim.
# Matching the block and not any '.name' is what keeps finalPairing_acc_spec honest - its
# PRE mentions the .pcs checkpoint (Inv at .pcs), so a naive scan for a partial token
# would find two and could certify the wrong one.
CONCLUSION_MARKERS = ["S.blk .", "PartialSound S .", "qAddr ."]
# The mirror of the ten theorems inside the checklist structure: a field named
# '<partial>_sound' or '<partial>_progress' is the same claim and needs the same bundle.
# LoweringCorrect carries PartialSpecs as ONE field, so the old discovery rule - which
# counts top-level arrows of a LoweringCorrect field - saw zero hypotheses and registered
# nothing. That is how a fourteen-field bundle hid from the bundle gate entirely.
SPECS_STRUCT = "PartialSpecs"
# The audit finding P-BUNDLE could NOT repair because the repair is a decision: vkLoading_spec's
# post pins the VK payload image in memory, the emitted slice fills it from extcodesize /
# extcodehash / extcodecopy, and no bound hypothesis says what the world's code is. The gate
# cannot demand the right hypothesis (three candidate homes: an Inv .start clause, an addl pre,
# or two more binders plus DeploymentW), so it demands the RECORD instead and reddens if the
# record is deleted or stops matching the measurement.
WORLD_GAP = "gap_vkLoading_world_reads"
WORLD_GAP_MEASURED = "gap_vkLoading_world_reads_measured"
WORLD_GAP_TOKENS = ["extcodesize", "extcodehash", "extcodecopy", "DeploymentW", "vkCode"]
# Audit finding 3, the same enforcement one external earlier. transcriptParser's post pins the
# squeezed challenge slots; the emitted squeeze_to hashes through the dialect keccak, which the
# Bridge answers from st.env.keccakOf; the snapshot's challenges come from H. A spec theorem about
# a squeezing partial therefore needs the keccak-agreement hypothesis (the hkec shape
# finalPairing_acc_spec already carried) or it is unprovable in exactly the way pcs_spec was.
KECCAK_TABLE = "partialKeccakSqueeze"
KECCAK_KAT = "partialKeccakSqueeze_ok"
KECCAK_TOKENS = ["st.env.keccakOf", "hashOfBytes H"]
# The exemption is read off the statement, not granted by hand: a theorem pinned to the
# no-accumulator arm does not run the arm that hashes, so it must NOT be asked for hkec and must
# NOT carry it.
NO_ACC_MARKER = "hasAccumulator = false"


def split_first(s, sep):
    """Split on the FIRST top-level occurrence of sep, returning (before, after) where
    after is None if sep never occurs at bracket depth zero. split_top drops the
    separators, which is not what a binder/conclusion cut wants."""
    depth, i = 0, 0
    while i < len(s):
        c = s[i]
        if c == '"':
            m = STR.match(s, i)
            if m:
                i = m.end()
                continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            return s[:i], s[i + len(sep):]
        i += 1
    return s, None


def partial_names(root):
    """The constructor names of 'inductive Partial' - the discovery set for the table."""
    p = root / CHECKPOINT_FILE
    if not p.exists():
        return None
    out, inside = [], False
    for ln in strip_comments(p.read_text(encoding="utf-8")).splitlines():
        if ln.startswith("inductive Partial"):
            inside = True
            continue
        if not inside:
            continue
        s = ln.strip()
        if s.startswith("|"):
            tok = s[1:].strip().split()
            if tok:
                out.append(tok[0])
        elif s:
            break
    return out


def precompile_table(root):
    """Parse 'def partialEip2537Targets : List (Partial x List Nat) := [(.pcs, [0x0b]), ...]'
    into {partial name: [addresses]}."""
    p = root / SPEC_FILE
    if not p.exists():
        return None
    text = strip_comments(p.read_text(encoding="utf-8"))
    # anchored on the WHOLE name: a plain find() on 'def partialEip2537Targets' also matches
    # 'def partialEip2537TargetsRenamed', and P-BUNDLE's own perturbation battery caught that
    # prefix bug by renaming the table and watching the gate stay green.
    m = re.search(r"(?m)^def\s+" + TABLE_DEF + r"\s*:", text)
    if m is None:
        return None
    i = m.start()
    j0 = m.end()
    j = text.find("[", j0)
    if j < 0:
        return None
    depth, k = 0, j
    while k < len(text):
        if text[k] == "[":
            depth += 1
        elif text[k] == "]":
            depth -= 1
            if depth == 0:
                break
        k += 1
    body = text[j:k + 1]
    table = {}
    for name, addrs in re.findall(r"\.([A-Za-z]+)\s*,\s*\[([^\]]*)\]", body):
        table[name] = [int(x.strip(), 0) for x in addrs.split(",") if x.strip()]
    return table


def spec_declarations(root):
    """{theorem name: (binder text, conclusion text)} for every top-level *_spec theorem."""
    p = root / SPEC_FILE
    if not p.exists():
        return {}
    text = strip_comments(p.read_text(encoding="utf-8"))
    out = {}
    for m in re.finditer(r"(?m)^theorem\s+(\w+_spec)\b", text):
        nxt = re.search(r"(?m)^(?:theorem|lemma|def|structure|abbrev|example|/-!|#eval)",
                        text[m.end():])
        end = m.end() + (nxt.start() if nxt else len(text) - m.end())
        decl = " ".join(text[m.start():end].split())
        stmt = split_first(decl, ":=")[0]
        binders, concl = split_first(stmt, ":")
        out[m.group(1)] = (binders, concl or "")
    return out


def holds_verdict(binder_text, want, where, why):
    """The one rule, applied to a theorem binder list and to a structure field alike."""
    problems = []
    present = HOLDS_TOKEN in binder_text
    if want and not present:
        problems.append(
            "%s: UNPROVABLE BUNDLE - %s, and it binds no %s. The theorem asserts something "
            "about precompile behaviour with no hypothesis about precompile behaviour, and "
            "nothing else in the bundle relates a precompile ANSWER to the codec the "
            "invariant names: PermissiveFor constrains an answer to be one the honest byte "
            "fold could give, EnvAgrees is about the domain and the digests, SupportedS is "
            "about the shape of the vk (P-BUNDLE, the R-62 class one level down)."
            % (where, why, HOLDS_TOKEN))
    if want and present:
        for a in HOLDS_ARGS:
            if a not in binder_text:
                problems.append(
                    "%s: HOLDS IS ABOUT THE WRONG OBJECT - it names %s but not %s, so the "
                    "hypothesis need not constrain the codec, encoder or pairing oracle "
                    "this Surface actually runs" % (where, HOLDS_TOKEN, a))
    if not want and present:
        problems.append(
            "%s: DECORATIVE HYPOTHESIS - binds %s but its partial reaches no EIP-2537 "
            "address per %s. Either the table is stale and the Lean pin is not running, or "
            "the hypothesis is carried for show; attack.md's decorative-field rule rejects "
            "it, and the gate refuses to be satisfied by binding Holds everywhere."
            % (where, HOLDS_TOKEN, TABLE_DEF))
    return problems


def keccak_partials(root):
    """Parse 'def partialKeccakSqueeze : List Partial := [.transcriptParser, .finalPairing]'."""
    p = root / SPEC_FILE
    if not p.exists():
        return None
    text = strip_comments(p.read_text(encoding="utf-8"))
    m = re.search(r"(?m)^def\s+" + KECCAK_TABLE + r"\s*:[^=]*=\s*\[([^\]]*)\]", text)
    if m is None:
        return None
    return [x.strip().lstrip(".") for x in m.group(1).split(",") if x.strip()]


def keccak_verdict(binder_text, want, where):
    problems = []
    present = all(t in binder_text for t in KECCAK_TOKENS)
    if want and not present:
        problems.append("%s: KECCAK AGREEMENT MISSING - its partial squeezes through the dialect "
                        "keccak (see %s) and its post pins the squeezed slots, but no hypothesis "
                        "says st.env.keccakOf is hashOfBytes H. This is audit finding 3: the "
                        "pcs_spec class, one external earlier, and finalPairing_acc_spec's hkec "
                        "is the shape." % (where, KECCAK_TABLE))
    if present and not want:
        problems.append("%s: DECORATIVE KECCAK HYPOTHESIS - it pins st.env.keccakOf to hashOfBytes "
                        "H but its partial never squeezes, so the hypothesis constrains nothing "
                        "the conclusion needs" % where)
    return problems


def spec_bundle_problems(root):
    problems = []
    names = partial_names(root)
    if names is None:
        return ["missing file: " + CHECKPOINT_FILE], 0
    spec = root / SPEC_FILE
    if not spec.exists():
        return ["missing file: " + SPEC_FILE], 0
    table = precompile_table(root)
    if table is None:
        return ["missing definition %s in %s - the spec-theorem bundle requirement has no "
                "source, so every *_spec binder list is unchecked (P-BUNDLE)"
                % (TABLE_DEF, SPEC_FILE)], 0
    raw = spec.read_text(encoding="utf-8")
    text = strip_comments(raw)
    gdefs = definitions(text)

    # 1. DISCOVERY: the table covers exactly the declared partials, no more and no less
    for n in names:
        if n not in table:
            problems.append("NEW PARTIAL WITH NO BUNDLE ROW - .%s is a constructor of "
                            "Partial and %s has no entry, so no spec theorem about it is "
                            "certified either way" % (n, TABLE_DEF))
    for n in sorted(table):
        if n not in names:
            problems.append("%s is stale: .%s is no longer a constructor of Partial"
                            % (TABLE_DEF, n))
    if not any(table.values()):
        problems.append("%s is VACUOUS - no partial reaches an EIP-2537 address, which "
                        "would make the whole spec-bundle rule silent. The emitter emits "
                        "G1MSM, G1ADD and PAIRING_CHECK calls; if that ever stops being "
                        "true the table has to be deleted on purpose and not by drift."
                        % TABLE_DEF)

    # 2. THE PIN: the Lean gate that ties the table to the emitter must exist, must walk
    #    the emitter, and must actually be evaluated by kat_gate.py
    kat = gdefs.get(TABLE_KAT)
    if kat is None:
        problems.append("SPEC-BUNDLE PIN MISSING - %s is not declared in %s, so %s is a "
                        "hand-written guess about the emitter and not a computed fact"
                        % (TABLE_KAT, SPEC_FILE, TABLE_DEF))
    else:
        for t in TABLE_KAT_TOKENS:
            if t not in kat:
                problems.append("SPEC-BUNDLE PIN WEAKENED - %s no longer mentions %s, so "
                                "the table is no longer checked against what the emitter "
                                "reaches (a plan view or the helper closure has been "
                                "dropped)" % (TABLE_KAT, t))
    for k in (TABLE_KAT, PERTURB_KAT):
        if not re.search(r"(?m)^#eval\s+" + k + r"\s+--\s*expect\s+true", raw):
            problems.append("SPEC-BUNDLE PIN NOT GATED - there is no '#eval %s -- expect "
                            "true' line in %s, so kat_gate.py never runs it and the pin is "
                            "prose" % (k, SPEC_FILE))
    if PERTURB_KAT not in gdefs:
        problems.append("SPEC-BUNDLE FALSIFICATION MISSING - %s is not declared in %s, so "
                        "the classifier has never been shown able to fail (R-41, D-P23)"
                        % (PERTURB_KAT, SPEC_FILE))

    # 3. THE TEN SPEC THEOREMS
    decls = spec_declarations(root)
    if not decls:
        problems.append("no *_spec theorem found in %s - the gate has nothing to check, "
                        "which is a failure and not a pass" % SPEC_FILE)
    certified = 0
    for name in sorted(decls):
        binders, concl = decls[name]
        hits = sorted(set(n for n in table
                          if any(mark + n in concl for mark in CONCLUSION_MARKERS)))
        if len(hits) != 1:
            problems.append("%s: CANNOT CERTIFY - its conclusion names %d of the seven "
                            "partials (%s). The gate refuses to guess which program the "
                            "theorem is about; name it in the block position (S.blk .q, "
                            "PartialSound S .q or qAddr .q)"
                            % (name, len(hits), ", ".join(hits) or "none"))
            continue
        q = hits[0]
        certified += 1
        problems += holds_verdict(binders, bool(table[q]), "%s (.%s)" % (name, q),
                                  "its partial reaches EIP-2537 %s"
                                  % ", ".join(hex(a) for a in table[q]))

    # 4. THE MIRROR IN THE CHECKLIST STRUCTURE
    structs = structures(text)
    if SPECS_STRUCT not in structs:
        problems.append("structure %s not found in %s, so the per-partial obligations the "
                        "headline field 'partials' carries are uncertified"
                        % (SPECS_STRUCT, SPEC_FILE))
    else:
        for field, (_line, ftext) in sorted(structs[SPECS_STRUCT].items()):
            stem = re.sub(r"_(sound|progress)$", "", field)
            if stem not in table:
                continue
            comps = [c for c in split_top(ftext, [ARROW]) if c.strip()]
            binders = " ".join(comps[:-1]) if len(comps) > 1 else ""
            certified += 1
            problems += holds_verdict(binders, bool(table[stem]),
                                      "%s.%s (.%s)" % (SPECS_STRUCT, field, stem),
                                      "its partial reaches EIP-2537 %s"
                                      % ", ".join(hex(a) for a in table[stem]))
    # 5. THE UNREPAIRED AUDIT FINDING, enforced as a record (see WORLD_GAP above).
    gap = gdefs.get(WORLD_GAP)
    if gap is None:
        problems.append("AUDIT GAP NOT IN THE CODE - %s is not declared in %s. vkLoading_spec "
                        "depends on world-state reads that no hypothesis of its bundle pins "
                        "(the pcs_spec class, a different external family); the repair is a "
                        "decision and the finding has to live where a gate can see it deleted"
                        % (WORLD_GAP, SPEC_FILE))
    else:
        for t in WORLD_GAP_TOKENS:
            if t not in gap:
                problems.append("AUDIT GAP UNDER-SPECIFIED - %s no longer names %s, so it "
                                "blames less than the measurement does" % (WORLD_GAP, t))
    if WORLD_GAP_MEASURED not in gdefs:
        problems.append("AUDIT GAP MEASUREMENT MISSING - %s is not declared in %s, so the gap "
                        "is prose about the emitter and not a computation over it"
                        % (WORLD_GAP_MEASURED, SPEC_FILE))
    if not re.search(r"(?m)^#eval\s+" + WORLD_GAP_MEASURED + r"\s+--\s*expect\s+true", raw):
        problems.append("AUDIT GAP MEASUREMENT NOT GATED - no '#eval %s -- expect true' line in "
                        "%s, so kat_gate.py never runs it" % (WORLD_GAP_MEASURED, SPEC_FILE))
    # 6. THE KECCAK ROWS (audit finding 3), enforced the same way as the EIP-2537 rows.
    sq = keccak_partials(root)
    if sq is None:
        problems.append("missing definition %s in %s - the keccak requirement has no source, so "
                        "audit finding 3 is recorded in prose only and hkec can be deleted in "
                        "silence" % (KECCAK_TABLE, SPEC_FILE))
    else:
        if KECCAK_KAT not in gdefs:
            problems.append("KECCAK PIN MISSING - %s is not declared in %s, so %s is a guess "
                            "about the emitter and not a computation" % (KECCAK_KAT, SPEC_FILE,
                                                                        KECCAK_TABLE))
        if not re.search(r"(?m)^#eval\s+" + KECCAK_KAT + r"\s+--\s*expect\s+true", raw):
            problems.append("KECCAK PIN NOT GATED - no '#eval %s -- expect true' line in %s"
                            % (KECCAK_KAT, SPEC_FILE))
        for name in sorted(decls):
            binders, concl = decls[name]
            hits = sorted(set(n for n in table
                              if any(mark + n in concl for mark in CONCLUSION_MARKERS)))
            if len(hits) != 1:
                continue
            want = hits[0] in sq and NO_ACC_MARKER not in binders
            problems += keccak_verdict(binders, want, "%s (.%s)" % (name, hits[0]))
        for field, (_line, ftext) in (structs.get(SPECS_STRUCT) or {}).items():
            stem = re.sub(r"_(sound|progress)$", "", field)
            if stem not in table:
                continue
            comps = [c for c in split_top(ftext, [ARROW]) if c.strip()]
            binders = " ".join(comps[:-1]) if len(comps) > 1 else ""
            want = stem in sq and NO_ACC_MARKER not in binders
            problems += keccak_verdict(binders, want,
                                       "%s.%s (.%s)" % (SPECS_STRUCT, field, stem))
    return problems, certified


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
        for g in entry.get("gaps", []):
            tokens += g[1]
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
        for g in entry.get("gaps", []):
            dname, toks = g[0], g[1]
            body_only = g[2] if len(g) > 2 else []
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
            # body-only tokens are not in the field statement (they name a blocker inside the
            # hypothesis, not a hypothesis of the field), so they are checked against the gap
            # text alone. P-CURVE added these so the gap cannot be rewritten back to the old
            # one-line "no curve model" blame while still mentioning Eip2537.Holds.
            missing_body = [t for t in body_only if t not in body]
            if missing_body:
                problems.append("%s: GAP BLOCKER UNDER-SPECIFIED - %s no longer names %s, so "
                                "the gap blames less than the measured blocker does"
                                % (field, dname, ", ".join(repr(m) for m in missing_body)))
    # 5. REFUTATIONS: a provably empty bundle needs one declaration naming every conjunct
    for dname, toks in REFUTATIONS:
        body = gdefs.get(dname)
        if body is None:
            problems.append("REFUTATION MISSING - %s is not declared in %s, so the empty "
                            "bundle is asserted in prose and not proved as one conjunction"
                            % (dname, GATES))
            continue
        missing = [t for t in toks if not mentions(body, t)]
        if missing:
            problems.append("REFUTATION IS NOT JOINT - %s never mentions %s, so the emptiness "
                            "is certified by halves and not by one statement (R-60 S1)"
                            % (dname, ", ".join(repr(m) for m in missing)))
    spec_problems, spec_certified = spec_bundle_problems(root)
    problems += spec_problems
    return problems, spec_certified


def main():
    argv = sys.argv[1:]
    root = Path(__file__).resolve().parent.parent
    if "--root" in argv:
        root = Path(argv[argv.index("--root") + 1]).resolve()
    problems, spec_certified = check(root)
    if problems:
        print("HYPOTHESIS-BUNDLE GATE FAILED (%d problem(s)):" % len(problems))
        for pr in problems:
            print("  " + pr)
        return 1
    exhibits = sum(1 for e in REGISTRY if e.get("exhibit"))
    gaps = len({g[0] for e in REGISTRY for g in e.get("gaps", [])})
    print("ok: %d registered headline bundles (%d jointly exhibited, %d named gap defs, "
          "%d joint refutations); every multi-hypothesis field of LoweringCorrect is "
          "accounted for" % (len(REGISTRY), exhibits, gaps, len(REFUTATIONS)))
    print("ok: %d spec-theorem / checklist-field bundles certified against the emitter "
          "classification in %s (P-BUNDLE: a theorem binder is outside every other gate "
          "schema)" % (spec_certified, SPEC_FILE))
    return 0


if __name__ == "__main__":
    sys.exit(main())

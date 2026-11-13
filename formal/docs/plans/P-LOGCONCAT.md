# P-LOGCONCAT - `transcript_log_concat`: the one missing lemma before the frozen statement is provable.

Status: READY, and it is **the highest-value unblocked proof work in the project.** P-BYTES
named it precisely: `transcript_log_concat` - *"the log's reprs concatenate to the consumed
transcript prefix"* - **does not exist as a declaration anywhere in the tree**, and it is the
only substantive obstacle between this codebase and a proof of `verifyNative_iff_msgs_codec`
at `Lowering/Obligations.lean:668`. The G1 half is an honest binder; the scalar half was just
proved. This is what remains.

It is **not blocked on any human decision** - unlike the pairing/torsion question, this is a
fact about the transcript, provable with what the tree already has.

## Deliverable

1. **State `transcript_log_concat`** in the right file (read the sketch hint at
   `Obligations.lean:669` and `docs/plans/P-SE-semantic-equivalence.md` section Q / line 351
   first - the statement is sketched there; **re-derive it, do not trust the sketch**).
2. **Prove it**, or report precisely why it is not provable as sketched. If the sketch's
   statement is false, **stop and report** - that is a finding, not a failure, and it has
   happened eleven times in this project.
3. **Use it to discharge `verifyNative_iff_msgs_codec`** at `Obligations.lean:668` if the
   remaining pieces allow. If they do not, say exactly which other hole blocks it.
4. **SORRY.md should go 63 -> 62** if the codec lemma closes. If only the statement of
   `transcript_log_concat` lands without the proof, that is still progress - say so plainly
   and leave the register at 63.

## What the tree already has - verify each, do not assume

* The transcript model: `Midfall/Halo2/Transcript.lean` (or wherever `squeeze_challenge`,
  `append_message`, and the log live - **locate them yourself**).
* `frOfRepr_frToRepr` and the byte lemmas from P-BYTES.
* `decodeRust`, `verifyMsgs`, `verifyNative` and the message-list structure.
* The Rust truth: `transcript/mod.rs` - the log is a `Vec` of appended bytes and `squeeze`
  reads a prefix of it. **Fact-check the Rust before porting**, as always.

## Constraints

* **D-P23 both halves for the new lemma**: a satisfiability witness AND a falsifiability
  demonstration. A concatenation lemma that nothing can violate is decoration - pin a case
  where the prefix is *not* consumed and show the lemma distinguishes it.
* **Do not edit `Statements.lean` or `Statements.sha256`.** The frozen statement's own `sorry`
  at line 68 is a deliberate D-P27 hold-out requiring a human decision and a re-pin.
* **`check_frozen_axioms.py` and the new STATEMENTS fingerprint gate are live** - if either
  reddens, investigate rather than adjusting the gate.
* **The KAT-conjunct gap P-BYTES found is real**: deleting a conjunct from a KAT def leaves
  everything green. If you add a KAT, make its falsification a separate named conjunct and
  note that the gate compares only the whole def's Bool.
* **RAM (D-P31)**: state an expected peak before VM work; use `--proc-limit 6G --limit 24G`
  for builds. A naive tree budget **kills legitimate builds** - measured at 17.91 GiB tree
  with a 2.97 GiB largest process.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place.** Numbers from `lake build` and `scripts/checks.sh` only.
* **A lesson from P-BYTES worth carrying**: the recorded blocker there was *half-wrong*, and
  the wrong half is what stopped everyone for many rounds - a precise negative about one
  lemma name is not a negative about the fact. If you find a note saying something is
  impossible, re-check it before accepting it.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5155 jobs**, 109 modules; `checks.sh` green, 13 sections: **63 tracked
sorries**, 1287 KATs across 85 files, 158 statement fragments, 12 fact families, 8 + 23
bundles, 30 baseline pins, Statements hash OK, frozen axioms exactly the expected four.

Read first: `Midfall/Lowering/Obligations.lean:640-680` (the sketch hint and the gated sorry),
`docs/plans/P-SE-semantic-equivalence.md` section Q and line 351, `docs/plans/P-SE-evidence/`
(the matching `design*.md` and `attack.md` - **FIX lines are binding**), the transcript module
you locate, and `docs/REVIEW.md` R-63/R-64.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `transcript_log_concat` stated and proved, **or** a precise report of why the sketch is
  wrong.
- **Required finding**: after this, is `verifyNative_iff_msgs_codec` discharged, and is the
  frozen `verifyNative_iff_msgs` now provable modulo the deliberate `Statements.lean:68`
  hold-out? That is the question the whole chain has been building toward.

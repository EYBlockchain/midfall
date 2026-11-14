# P-RESTORE2 - restore what the sketches required. **The unannotated drops are the headline.**

Status: **REQUIRED, human-directed.** P-SPECPIN's audit corrected my correction: of the eight
missing `EnvAgrees` fields, four are recorded with reasons and three are relocated — but **two
drops are recorded NOWHERE**, and the dangerous class is the unannotated one.

## Steps in this order. Stop at a boundary; each is independently valuable.

### Step 1 - the two UNDOCUMENTED drops (highest value)

1. **`accBasesInVk`** — sketch line ~1551. Included specifically so `finalPairing_acc_spec`
   could relate the folded point to `a.fullyCollapse (tblOf PV fb)`. **No counterpart anywhere,
   and not in `Inv.lean`'s dropped list.** Restore it, or record why it cannot hold.
2. **The `reversedEvals` clause** — sketch line ~1585: `holdsFrs st (ptrAddr M.reversedEvalsMptr)
   (reversedEvalsOf PV S)`. The parser's main output **is** the reversed-evals table
   (`GenAst.lean:1144-1154` mstores it), and `Inv .transcript` has no clause pinning that
   window. `reversedEvalsOf` exists nowhere. **This drop is recorded nowhere.**

For each: restore verbatim from the sketch, building any missing dependency (`reversedEvalsOf`,
`tblOf`), or write the reason into `Inv.lean`'s dropped list. **Do not leave either silently
absent — that is the failure being fixed.**

### Step 2 - verify the redundancy claim, do not inherit it

`Inv.lean:443-447` argues `g1BaseWords`/`g2BaseWords`/`negSG2Words` are redundant because the
base points sit in the VK payload image that `Inv`'s `.vk` clause pins byte-for-byte. P-SPECPIN
assessed it as **covering the bytes but not the LINK** — `Inv .vk` pins payload bytes to
*generator* bytes, not to `S.encG2` of anything, so "the G2 base slot holds `encG2 P.g₂`" is
stated nowhere. **Confirm or refute concretely**: do header slots 11, 15, 23 fall inside the
pinned byte range, and does anything tie them to `encG2`/`E.g1.toEip`?

### Step 3 - pin the clauses the relocations now depend on

`finalPairing_spec`'s dropped post conjuncts were proved recoverable from `Inv .pairing` +
`hacc` — **outside the tree, uncommitted.** Two consequences:
* **Land that recovery lemma in the tree** (~12 lines, sorry-free, belongs in `Inv.lean` next
  to `xNotRoot_iff_notDomainPoint`).
* **Add `ENV_CLAUSES` entries for `Inv`'s `.pairing` `success`/`DualMSM` clauses.** They are
  load-bearing for a relocation and currently unpinned — `ENV_CLAUSES` has exactly one entry.
  Same for `LocalsOk` if anything depends on it.

### Step 4 - fix the doc-vs-tree mismatches (cheap, and each is a lie a future agent will trust)

* `Partials.lean:173` — `PartialSound`'s docstring says the `alwaysReverts` soundness lemma
  "is PROVED rather than claimed". **It is a `sorry`.**
* `Partials.lean:702-703` — `finalPairing_progress_spec`'s docstring says `success = 1` "is on
  the pre". **It is not.** If the emitted block ever reads `success` before writing it, the
  implemented claim is the false one — check that and say which is wrong.
* `PartialRejects` is **defined and used by nothing** — the sketch's `transcript_rejects` and
  `pcs_rejects` obligations are absent from `PartialSpecs` because the sketch's `Fault` key does
  not typecheck. Either implement the twins with a corrected key or record the obligation as
  dropped-with-reason. Dead code that looks like coverage is the worst outcome.

### Step 5 - `delta` (recorded, but still a gap)

Find the literal the generator emits (artifact `QuotientNumeratorBlock.yul:1407` + the Rust),
define the Lean constant, restore the field. If it cannot be done, write that into the record.

### Step 6 - consolidate the deviation log and add the rule

Move/link every deviation record into `docs/plans/P-SE-statements.md` — the file whose **stated
job** is the sketch-vs-implementation record — and add: *a rename, arity change, or dropped
field on a sketched statement requires a line in that file **in the same commit**.* Then audit
`Inv`, `SupportedS`, `Snapshot`, `LoweringCorrect` for further **unannotated** drops.

## NOT in scope

* Do **not** restore the four recorded-and-reasoned fields or the three relocated ones.
* Do **not** revert `omegaOrder` to `orderExactly`'s weaker form, or remove `BlkIsEmitter`.
* Do **not** weaken any statement to make an exhibit pass. **Report instead.**
* If restoring `accBasesInVk` or `reversedEvals` makes `fxEnvAgrees` fail at the fixture,
  **that is the finding** — the fixture was built to fit the weakened hypothesis.

## Constraints

* **D-P23 both halves as theorems** for anything new. Falsification-deletion gap measured
  **sixteen** times — claim no coverage for falsifications.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts as a hole; comment edits shift
  `file:line` pins → budget a full `checks.sh` run (~8.5 min).
* **Gate changes must keep all 13 sections green and be shown to redden** (R-41).
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Full gate actual: 5.12 GiB tree / 4.45 GiB largest.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5212 jobs**,
**56 tracked sorries**, 122 modules, **221 statement fragments**, 1304 KATs across 91 files.
`EnvAgrees` at `Inv.lean:451`, its deviation note at `Inv.lean:432-450`. Sketch section L at
`docs/plans/P-SE-semantic-equivalence.md:1521-1556`. Harness left at `/tmp/specpin/perturb.py`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Steps 1–2 resolved: both unannotated drops restored or recorded with reasons.
- **Required finding**: the complete list of sketched obligations that are absent **without**
  annotation, anywhere in A–R — that is the class this package exists to eliminate.
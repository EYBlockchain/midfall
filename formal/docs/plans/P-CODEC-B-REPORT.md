# P-CODEC-B - RESULT REPORT

Status: **steps 1, 2 and 3 LANDED; step 4 NOT landed**, blocked on a **sixth obstacle**
that nobody had listed (named precisely below). Tree compiles, gate green.

## Build and gate tails

```
Build completed successfully (5156 jobs).
ram_guard: peak tree RSS 3.83 GiB (2 proc, largest 3.09 GiB at pid ... lean);
           budget 24.00 GiB; verdict OK
```
Expected peak stated before the work (D-P31): a cold parallel build is measured at
17.91 GiB tree / 2.97 GiB largest process, so `--proc-limit 6G --limit 24G` was used for
every build. `ram_guard.sh --selftest` ran first: ALL PASS. Observed peaks: 3.83 GiB
tree, 3.09 GiB largest process. Never near the budget.

`bash scripts/checks.sh` -> **EXIT=0**, 13 sections, 11 `ok:` lines:

| section | before | after |
| --- | --- | --- |
| tracked sorries | 63 | **63** (step 4 did not land) |
| KATs | 1290 across 86 files | **1291 across 86 files** (`foldLemmaKat_ok`) |
| module reachability | 110 modules | 110 modules (no new file added) |
| statement fragments | 158 | 158 |
| fact families | 12 | 12 |
| bundles | 8 + 23 | 8 + 23 |
| baseline pins | 30 | 30 |
| Statements hash | OK | OK (Statements.lean untouched) |
| frozen axioms | the expected four | the expected four |

SORRY.md was NOT regenerated: no sorry closed, so the register is unchanged and
`scripts/sorries.sh` (63), the register (63) and `checks.sh` ("ok: 63 tracked sorries")
agree three ways without any edit.

## Steps landed, in the mandated order

### Step 1 - the fold lemma (LANDED, `Midfall/Halo2/Exec/TranscriptLog.lean`)

The gap P-CODEC-A found: `transcript_log_concat` says the log tiles the consumed prefix,
`decodeRust| recovers messages by a per-record `List.mapM`, and nothing connected them.
The fact was computed at `Instances/NativeE2E.lean:347` (`n2RoundTrip_ok`) - gate evidence,
no proof, and D-P17 forbids citing that file. It is now a theorem, proved without
importing the instance file. New in a section at the end of `TranscriptLog.lean`:

* `Transcript.recorded_eq_fold` - `recorded` IS the `ByteArray.append` fold of the log's
  reprs (the two definitions are written with different folds).
* `list_mapM_roundtrip_snd` - **the fold shape**: a successful `mapM` whose per-element
  decoder round trips against a re-encoder recovers the source list's second components
  in order.
* `logDispatch` - `decodeRust`'s three-arm per-record dispatch, named so it can be a
  hypothesis; `decodeRust_eq_mapM` proves `decodeRust` IS the log's `mapM` over it.
* `msgWire_logDispatch` - the per-record round trip: Fr arm from
  `Midfall.Assumptions.frOfRepr_frToRepr_bytes`, G1 arm from `compressedRoundtrip`, dead
  third arm from `widthDispatch_exhaustive`. All three of P-CODEC-A's lemmas are consumed.
* `recorded_fold_of_mapM` - the fold lemma, abstract over `wire`/`dispatch` so the exhibits
  need no pairing model (D-P17).
* `decodeRust_recorded` - **the shape the brief asked for**: `decodeRust ... = some ms ->
  ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (msgWire E m)) =
  t.recorded`.

D-P23: `fold_lemma_witness` (satisfiability as a THEOREM: a real two-record log, both
allowed widths, tiled, with the conclusion pinned to a specific byte string),
`fold_lemma_refutesNonRoundtrip` (a non-canonical repr: `mapM` succeeds and the fold is
NOT the recorded prefix - so `compressedRoundtrip` is load-bearing), `fold_lemma_refutesOtherWidth`
(a width-4 record makes the whole `mapM` `none`, so there is no `ms` at all), and
`foldLemmaKat_ok` (computed: two REAL reads of a real buffer).

Also landed, the line P-CODEC-A verified but could not: `Transcript.initWithHash_keccak` -
`Transcript.initWithHash keccak256 bytes = Transcript.initFromBytes bytes` **is `rfl`**.

### Step 2 - `congr_of_run_eq` and the `set` warning (LANDED)

`Pres.congr_of_run_eq` and `PresWidths.congr_of_run_eq` (pointwise run equality transfers
each predicate). **The warning was honoured and is now a theorem, not a comment:**
`set_not_Pres` and `set_not_PresWidths` exhibit transcripts `x` with `¬ Pres (StateT.set x)`
and `¬ PresWidths (StateT.set x)` - `set` installs an arbitrary transcript, so no `set`
closure lemma exists for either predicate. `PresWidths.guardWhen` (the twin of
`Pres.guardWhen`) also landed here; it did not exist and the widths walk needs it.

The characterised fix was confirmed and is recorded in the file's header: `cases h : m.run s`
on a HYPOTHESIS does not abstract the scrutinee, because after `unfold` the do-block's own
`let t ← StateT.get` binder shadows `s` and the occurrence is never found; `intro s;
cases h : m.run s` on the GOAL does.

### Step 3 - the two do-block walks, Pres AND PresWidths (LANDED)

All four exist now: `pres_parseTrace`, `presWidths_parseTrace`,
`pres_verifyAlgebraicConstraints`, `presWidths_verifyAlgebraicConstraints`, plus the
compositions `pres_prepare` and `presWidths_prepare` - so `transcript_log_concat` finally
applies to the transcript `verifyNative` leaves behind, which was P-LOGCONCAT's named gap.

**COST REPORTED, as the brief asked.** `verifyAlgebraicConstraints` is ~40 lines each, as
estimated. `parseTrace` is **~95 lines each, not 5-15**. Nothing was hard - every construct
did have its closure lemma - but: `parseTrace` has 20 monadic steps over nested `for` loops
that desugar to `forIn` over BOTH `List` and `Array` (so each needs the right variant), and
the `refine` holes for `listForIn`/`listFoldlM` need `intro` WITHOUT `dsimp` while the fold
bodies need the opposite. Three no-op `dsimp`s each cost a build cycle.

**NEW OBLIGATION found in step 3:** `Pcs` is a RECORD whose `multiPrepare` field is an
arbitrary function, so `Pres (pcs.multiPrepare queries)` is not provable for a general
`pcs`. Both `verifyAlgebraicConstraints` walks carry
`hpcs : ∀ queries, Pres (pcs.multiPrepare queries)` (resp. `PresWidths`), discharged at
the call site by `pres_multiPrepare` for `Pcs.kzg` - the only instantiation `verifyNative`
uses. This is not a weakening (the frozen statement never quantifies over `pcs`), but it is
a hypothesis the plan did not list.

### Step 4 - discharge `verifyNative_iff_msgs_codec` (NOT LANDED)

Register stays **63**. The obstacle is named below.

## THE SIXTH OBSTACLE (the required finding, part 1)

Everything the codec lemma needs except one fact is now proved. The missing fact is not
the fold, not the widths, not the tiling, and not the do-blocks. It is:

> **The transcript log records a read's WIDTH and BYTES but not WHICH `Hashable` produced
> it, and `decodeRust`'s dispatch chooses a decoder by width.**

Formally, the forward direction needs `∃ ms, t.log.toList.mapM (logDispatch E) = some ms`
where `t` is the transcript `verifyNative` leaves behind. `decodeRust`'s Fr arm is
`frOfRepr? rec.2` and its G1 arm is `E.g1.ofCompressed? rec.2`; a logged record
`(w, b)` only guarantees that the reading hashable's OWN `readRepr?` accepted `b`.
`Transcript.LogWidths` (P-CODEC-A) buys "the third arm is unreachable" - it does NOT buy
"the arm that IS reached accepts the bytes". A width-32 record logged by some hypothetical
32-wide hashable whose `readRepr?` is not `frOfRepr?` would make the dispatch return
`none` while the read succeeded.

On the real pipeline this cannot happen - every read site uses `hashableFr` or
`hashableG1`, and for those two `readRepr?` IS the decoder the dispatch reaches for,
definitionally (`Exec/Transcript.lean:59`, `:69`). But that is a statement about which
hashable logged each record, which the log does not carry.

**What it costs to close.** A third pipeline predicate alongside `Pres` and `PresWidths`:
`Hashable.Dispatchable E h` (a read accepted at width `h.width` is decoded by
`logDispatch E`), `Transcript.LogDecoded E t`, its per-primitive step lemmas, and then a
third copy of the closure + transfer walks. Mechanically identical to `PresWidths` - the
same 20 read sites, the same closure lemmas, the hypotheses discharged by
`hashableFr_dispatchable` / `hashableG1_dispatchable` exactly as `hashableFr_allowed` /
`hashableG1_allowed` are now. Estimate: the closure section is a textual generation of the
`PresWidths` one; the transfers are a third copy of walks that now each fit in one screen
(`verifyAlgebraicConstraints`) or two (`parseTrace`). **Roughly one working session, no
thinking.** With it, step 4 is: chain `pres_prepare` + `presWidths_prepare` +
`transcript_log_concat` + `decodeRust_recorded` + `Transcript.initWithHash_keccak` +
`Transcript.assertEmpty`, both directions, and the register goes to 62.

**Why it was not done here:** the brief says stop at a step boundary rather than
half-finish, and a third walk is step 5, not step 4. Landing steps 1-3 in order is the
outcome the ordering was designed to protect.

## The required finding (part 2): what stands between here and the frozen statement

With the codec lemma NOT yet discharged, the chain is:

1. `Statements.verifyNative_iff_msgs` (frozen, `Statements.lean:65`), own `sorry` at
   `Statements.lean:68` - the D-P27 hold-out.
2. `Midfall.Lowering.verifyNative_iff_msgs_codec` (`Obligations.lean:664`), own `sorry` at
   `:668` - the restatement carrying `hc : E.g1.compressedRoundtrip`.
3. The sixth obstacle above (decodability of the log), then the iff assembly.

So: **no, it is not only the `Statements.lean:68` hold-out yet.** One substantive obstacle
remains, and it is ordinary work, not a decision. But the picture has changed in the way
the brief asked about:

* Before this package, `Obligations.lean:669` named `transcript_log_concat` as the only
  substantive obstacle. That is now false in two directions: the log lemma exists and
  applies to the pipeline (`pres_prepare`), and the fold gap it did not mention is closed.
* What is left is one more predicate + walk of the same shape as two that already exist.
  Nobody has to invent anything.

**Is the `Statements.lean:68` hold-out worth putting to the human?** Not yet, and the
answer sharpens: filling it would still need `verifyNative_iff_msgs_codec`, so the decision
is not reachable until the decodability walk lands. Once it does, the frozen statement
becomes PROVABLE rather than merely not-false, and at that point the D-P27 question - fill
the frozen `sorry` or keep the spec surface proof-free - is a real decision for the human,
not a technical one. Recommend the next package be the decodability walk plus step 4, and
that the D-P27 question be put only after both.

## D-P23: witness and falsification, per new lemma

Every new lemma has both halves as THEOREMS (not only KAT conjuncts), per the measured gap
that deleting a KAT conjunct leaves the gate green.

| lemma | witness | falsification |
| --- | --- | --- |
| `Transcript.recorded_eq_fold` | `foldLemmaKat_ok` (real reads) | `fold_lemma_refutesNonRoundtrip` |
| `list_mapM_roundtrip_snd` | `fold_lemma_witness` | `fold_lemma_refutesOtherWidth` |
| `msgWire_logDispatch` | `fold_lemma_witness` | `frOfRepr_bytesRefutesNonCanonical` (P-CODEC-A) + `fold_lemma_refutesNonRoundtrip` |
| `decodeRust_recorded` | `foldLemmaKat_ok` + `fold_lemma_witness` | `fold_lemma_refutesOtherWidth` |
| `Pres.congr_of_run_eq` | used by `pres_verifyAlgebraicConstraints` | `set_not_Pres` |
| `PresWidths.congr_of_run_eq` | used by `presWidths_verifyAlgebraicConstraints` | `set_not_PresWidths` |
| `pres_parseTrace` / `presWidths_parseTrace` | the walks themselves + `parseTrace_kats_ok` (pre-existing) | `transcriptLogRefutesUntiled`, `transcriptLogWidths_refutesU32Read` |
| `pres_verifyAlgebraicConstraints` (+widths) | the walks + `algR8Collapsed_ok` (pre-existing) | `set_not_Pres` / `set_not_PresWidths` |
| `Transcript.initWithHash_keccak` | `rfl` | n/a (definitional) |

**Deletion gap, recorded not hidden:** deleting any of these theorems leaves the build
green - that is the measured gap and it is not closed by anything here. What IS guarded is
FALSE versions: see the perturbation evidence.

## Perturbation evidence - all with `lake build`, never `lake env lean`

Method rule honoured: every perturbation was done in an APFS clone of the WHOLE repo at
`/tmp/clone-pcodec-b` (so Generator KATs can see `../proofs`), and measured with
`lake build`, not `lake env lean`.

| # | perturbation | result |
| --- | --- | --- |
| 1 | `Transcript.recordedList` appends a spurious byte | **REDDENED** - 5 errors, incl. `Transcript.recorded_eq_fold` (new) and `fold_lemma_witness` (new), plus the pre-existing tiling step lemma |
| 2 | `msgWire` Fr arm emits 33 bytes instead of 32 | **REDDENED** - `msgWire_logDispatch` (new) fails, and `Instances/NativeE2E.lean:596-600` (`n2RoundTrip_ok`, the `native_decide` gate) fails: the Lean proof and the computed gate agree that the round trip broke |
| 3 | `Transcript.Tiled` weakened to `True` | **REDDENED** - 8 errors incl. `transcriptLogRefutesUntiled` and `fold_lemma_witness` (new) |
| 4 | `set_not_Pres` given a TILED witness (i.e. made false) | **REDDENED** - the proof fails to elaborate at the `absurd`, so a false version of the falsification cannot be stated and proved |

**Failure to redden, reported:** corrupting `Pres` itself to `True` would NOT redden
anything - `transcript_log_concat` would become vacuous and still build. That is the
structural limit of every gate here: only a proof is a meaning check. Same for deleting a
whole falsification theorem, and for deleting a conjunct from a KAT def. Both gaps are
recorded in the file headers and here, not claimed as covered.

Note on #2: the failure surfaced partly as a heartbeat timeout inside `msgWire_logDispatch`
(the corrupted `msgWire` forced a `whnf` of the byte emitter), not a clean type error.
Reddened is reddened, but the signal was noisier than #1/#3/#4.

## Files touched

* `Midfall/Halo2/Exec/TranscriptLog.lean` - 1498 -> 2166 lines. Added `import
  Midfall.Assumptions.Codec` (needed by the Fr arm of the per-record round trip; no cycle,
  and it imports nothing from `Instances/`), a header paragraph recording what landed, and
  three new sections (steps 1, 2, 3).
* Nothing else. `Statements.lean`, `Statements.sha256`, `SORRY.md`, Rust and `vendor/`
  untouched. No `git add`, no commit.

## Scratch left in the tree (deliberately, so nothing is lost)

`formal/scratch_b.lean` (step 1 as developed), `scratch_c.lean` (the parseTrace Pres walk),
`scratch_d.lean`/`scratch_w.lean` (the widths twins), `scratch_e.lean`/`scratch_e2.lean`
(the algebraic walk), `scratch_f.lean` (the set-tail experiments), `scratch_g.lean`,
`scratch_h.lean` (the assembled step 2+3 block), `parts.json`, `block23.txt`. These are
outside `Midfall/` so `check_orphans.py` and `kat_gate.py` do not see them and the gate is
green with them present. They are the source of the landed text and the next package can
reuse the generation script.

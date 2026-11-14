# ETA ledger — estimates, actuals, and the variance between

**Purpose.** This project's estimates have been wrong often enough that a single number is
misleading. This file records every estimate **when made**, the **actual** when the work lands,
and the **variance**, so the remaining estimates are calibrated rather than hopeful. It is
updated by the orchestrator on every package completion. See standing rule **D-P37**.

**Units.** One *session* = one subagent package, roughly 1–2 hours of agent time. Wall-clock
is reported separately and is dominated by session availability, not difficulty — this project
lost 14 calendar days to a gap that cost zero work.

---

## Calibration data so far (estimate → actual)

| item | estimated | actual | variance | lesson |
|---|---|---|---|---|
| P-SE stage 2 (P2) | 4 days | ~2 days | **2× pessimistic** | first datum; caused the ~0.2 day/theorem rate |
| `verifyAlgebraicConstraints` walk | ~40 lines | ~40 lines | **accurate** | once closure lemmas exist, walks are predictable |
| `parseTrace` walk | 5–15 lines | ~95 lines | **~7× optimistic** | I extrapolated from a different shape; nested `forIn` over both `List` and `Array` |
| `pairing2` | blocked on a pairing implementation (stated 3×) | **one definition + four slice equations** | **wrong kind, not wrong size** | a free parameter was mistaken for a missing construction |
| r-torsion point count | research-grade, weeks–months | `Nat.card_zpowers` + `orderOf_eq_prime`, **elementary** | **wrong kind again** | a named lemma's absence was read as the fact's absence |
| `Array.foldl` transfer | impossible, no core lemma | `Array.foldl_toList` exists | **wrong name, right shape** | a precise negative about one name is not a negative about the fact |
| P-CODEC (4 items, one session) | 4 items | **0 durable output** | **over-scoped** | briefs must fit the budget; mandated ordering fixed it |

**Pattern, stated plainly:** of the seven items above, **four were errors of kind, not of
degree** — I recorded a blocker as large when it was a different shape entirely, usually
because a premise was inherited rather than re-verified. The standing instruction to agents to
re-verify recorded premises is the mitigation and it has paid for itself repeatedly.

## Throughput actually observed

| package | sessions | sorries closed | notes |
|---|---|---|---|
| P-BYTES | 1 | 1 | first removal; the blocker was a false premise |
| P-CODEC-C | 1 | 1 (headline) | +81 declarations; found a 6th obstacle |
| P-BRIDGE | 1 | 3 | incl. `noWritersFuel` and MF-4 — first non-vacuous run |
| P-LOGCONCAT | 1 | 0 | 825 lines, 16 transfers, general lemma proved |
| P-HOLDS2 | 1 | 0 | `pairing2` + order lemma; retired a research-grade claim |
| P-CODEC | 1 | 0 | **ran out of room, no durable output** |
| P-SPEC1 | 1 | 1 (traceReturn_spec) | first `Partials` spec proved; 13 new declarations incl. the D-P23 pair; two gate gaps measured |

**Rate: 1–3 sorries per session on hard work; 0 when the package is exploratory or over-scoped.**
At 58 remaining and a mean of ~1.3, the naive projection is **~45 sessions**, not the 17–27 I
gave earlier. I am revising upward and flagging that my previous number was optimistic because
it counted only packages that closed something.

---

## Milestones on the path to the landmark `lowering_equivalence`

### M-A — exhibit `Eip2537.Holds` — **IN PROGRESS**

| clause | status | cost |
|---|---|---|
| `g1Valid` | exhibited (P-CURVE) | done |
| `g1Decodes` | repaired + exhibited (P-HOLDS/P-CURVE) | done |
| `pairing2` | **exhibited by definition** (P-HOLDS2) | 1 session |
| `PrimeOrderWith` | **derivable**, lemma proved (D-P34) | 0 extra |
| `g1Add`, `g1Msm1` | blocked on the agreement theorem | P-MODEXP, in flight |
| `g2Valid` | needs a G2 frame codec | 1–2 sessions |

**Original estimate: 3–5 sessions. Revised: 3–4** (P-HOLDS2 landed 1 of the remaining 3–4; the
torsion item cost 0 because it was never real). **Confidence: low-medium** — the agreement
theorem is the first item here I have not already found to be mis-described.

### M-B — the 12 `Partials` specs — **1 OF 12 PROVED (P-SPEC1: `traceReturn_spec`)**

Needs M-A (`Holds`) + Bridge step lemmas (MF-4 **done**). **Estimate: 4–6 sessions** at ~2–3
specs/session, since `finalPairing_spec`'s dominant cost is already closed. **Confidence: low**
— no spec has been proved yet, so this rate is entirely extrapolated.

**UPDATED AFTER R9 (the extrapolation now has one datum).** The cheapest spec measured ~50 min
of proof work and ~40 single-file type-check iterations, ~35 min of which built machinery every
later arm inherits. Verdict: **the rate is roughly right for the four specs whose bridges exist,
and the item list is wrong** — four of the twelve bind `Eip2537.Holds` and are M8's, one
(`vkLoading_spec`) is unprovable as stated (see `gap_vkLoading_world_reads`), and three need
bridges that do not exist yet (`readScheduleAgrees`, the batch-inversion agreement). Re-cut M-B as
**2–3 sessions for the approachable arms**, with the rest charged where it actually blocks.

**RE-CUT AGAIN AFTER R10 (the item list was wrong a second time).** The twelve were never twelve specs: `Partials.lean` held twelve registered holes, ten spec theorems plus two `alwaysReverts` vacuity lemmas. Of the eleven left, **three are approachable and only one of those is a spec** (`quotientLin_spec`, and two of its intended post clauses are inert because `Snapshot.lin` is always `none`); four bind `Eip2537.Holds` and are M8's; three need bridges that do not exist (`readScheduleAgrees`, the batch-inversion agreement); one is unprovable as stated and needs a decision about where the world belongs. **M-B is now 1 session, then blocked.** Full table at R10.

### M-C — `Accumulator` 12 + `Calldata` 7 + `Qvm`/`QvmFold` 9 — **NOT STARTED**

Largely independent of M-A. `Qvm` needs `LoweringPlan::new` (circuit-as-data, uncosted).
**Estimate: 8–14 sessions.** `Calldata` is the most mechanical and should be first.

### M-D — `dialect_deterministic` + the transport — **NOT STARTED**

P-BRIDGE: hits the 200k-heartbeat limit on external-call arms; 7 external ops by hand plus ~70
local via `Option.some.inj`. **Estimate: 2–5 sessions, wide variance.** This is the item most
likely to be mis-estimated in either direction.

### M-E — `lowering_equivalence` itself — **NOT STARTED**

The theorem is a **transport** through `hc.ir_refines`; its own hint says "provable now".
**Estimate: 1–2 sessions once M-A–M-D land.** The landmark's cost is almost entirely its
prerequisites — which is the useful thing about naming it.

### Deferred, not avoided

| item | estimate | trigger |
|---|---|---|
| D-P32 reconciliation (`main` drift: 10 templates, M0 re-run, re-pin) | 3–5 sessions | before any claim about the `main` contract |
| Security track S1–S7 in ArkLib `Interaction` (D-P29) | uncosted | after the landmark |
| `Statements.lean:95` and `:123` frozen sorries | 1 session each | `verifyMsgs_iff_spec` needs `Spec.accepts` defined |

---

## Totals

| | sessions | note |
|---|---|---|
| M-A remaining | 3–4 | in flight |
| M-B | **1, then blocked** | re-cut twice: R9 found the item list wrong, R10 found 8 of the 11 remaining holes are not M-B's to prove |
| M-C | 8–14 | bulk by count |
| M-D | 2–5 | widest variance |
| M-E | 1–2 | transport |
| **Total to landmark** | **15–26** | **revised down from 18–31 by R10's M-B re-cut; M8 (8–16, R8) is still NOT in this table, so this total is optimistic by exactly M8** |

**Wall-clock:** at 1–2 sessions per active hour and this session's observed availability,
**6–12 calendar weeks**, dominated by uptime rather than difficulty. The 14-day gap earlier in
this project moved the calendar by more than every estimate error combined.


---

## Revision log

### R1 - round 116, after P-MODEXP. First recorded miss.

| claim made | before | actual | verdict |
|---|---|---|---|
| register 57 if modexpInv_correct closes | predicted close | **stayed 58** | **MISS** - needs ~8 byte-slice lemmas, not Fermat |
| the r-torsion count is not needed at all (D-P34) | retired | **needed again**, via g1Decodes + PrimeOrderWith | **error of kind, twice** |
| M-A remaining | 3-4 sessions | **5-7** | revised up |
| total to landmark | 18-31 sessions | **21-35** | revised up |
| wall-clock | 6-12 weeks | **7-13 weeks** | revised up |
| Fermat reading | asserted | **held for the math, failed on the frame width** | partial |

**The lesson is not about arithmetic.** D-P34 retired the point count because PrimeOrderWith of a
cyclic subgroup is two elementary lemmas. That is true - and the count came back through a
**different door**: g1Decodes demands toEip hit every accepted frame, PrimeOrderWith demands
Nat.card G1 = r, and together those are **equivalent to** the point count. A blocker can be
genuinely retired at one clause and silently re-imported at another. **Retiring a premise
requires checking every clause that could re-import it, not just the one it was raised under.**
New failure mode for this ledger; fifth error of kind recorded.

**Route forward, per P-MODEXP:** not SEA. Route (b) - n-torsion structure + Weil pairing +
gcd(r, p-1) = 1 - has a cheap first step: gcd(r, p-1) = 1 follows from BasePrime's existing
factorisation of p-1, since a 255-bit prime r is not among its small factors. A morning's work.

**Credibility note.** Three of the five kind-errors were the orchestrator's own, all mis-sizing a
blocker by reasoning from a recorded premise instead of re-deriving it. The mitigation is not
better estimation; it is the standing re-verify instruction, and the orchestrator's own
retirements are now included in what must be re-verified.

---
### R2 - round 117, after P-G1AGREE. First revision in the flattering direction.

| claim | before | actual | verdict |
|---|---|---|---|
| register 58 to 57 (byte plumbing closes modexpInv_correct) | predicted | **57** | **HIT** - first estimate that landed exactly |
| steps 1-3 (assembly, smul, plumbing) | ~2 h | **~1 h 45 m** | slightly pessimistic |
| step 4 gcd(r, p-1) = 1 | a morning | **5 minutes, one decide** | **~10x over-estimate** |
| M-A remaining | 5-7 sessions (R1) | **4-6** | revised down: the agreement theorem is DONE |
| total to landmark | 21-35 | **20-34** | revised down slightly |

**The pattern holds and it cuts both ways.** Step 4 was over-estimated for the same reason earlier
blockers were mis-sized: a recorded premise (route (b) first step is a morning's work) was
inherited instead of re-derived. The kernel just computes gcd(r, p-1) - no factorisation needed.
**Sixth lesson: an estimate of effort is a premise too**, and mine were wrong in both directions
roughly equally often.

**A new failure mode, distinct from the kind-errors: a correct diagnosis with a wrong cure.**
P-MODEXP recorded that rw could not move a W.Nonsingular goal - true, and the transparency note
pointed at the real cause. But both suggested cures were unnecessary; the fix was transfer lemmas
over variables proved by subst, exploiting that Point.some's third argument is a Prop and Lean 4
proof irrelevance is definitional. **A symptom recorded accurately can still carry a bad
prescription, so "the blocker is real" and "the proposed fix is right" must be verified separately.**

**What M-A now costs, itemised:** canonicity walk (1 session, blocked on an elaborator limit not
math), point count route (b) (2-3 sessions, gcd already done), G2 codec + Fp2 model (2-3
sessions, and fp2Ops has no mathlib model at all - a package, not a lemma). The agreement theorem
that P-MODEXP called THE wall is finished.

**New standing rules, added to the brief template:** lake env lean leaves autoImplicit ON so
unknown identifiers silently become free variables - pass -DautoImplicit=false; set_option X in
must precede a declaration's docstring; nsmul_nsmul does not exist in this mathlib (the lemma is
mul_nsmul, factors swapped); and **where rw cannot cross a defeq, a have with an ascribed type
can**, because elaboration uses full defeq where the matcher does not. Plus a correction to my
own rule: perturbing a KAT Bool leaves lake build green - Bool gates live in checks.sh, not the
build - so "use lake build for perturbations" applies to theorems only.
### R6 - round 126, after P-G2B. The landmark is STAGED.

| claim | before | actual | verdict |
|---|---|---|---|
| G2 codec needs maxHeartbeats 4e8 | recorded by P-G2, never tried | **18 min, unfinished, killed** - the wall was an unwanted whnf on a symbolic argument, not a budget | **error of kind, 14th** |
| checks.sh takes over 10 minutes | recorded | **491 s measured** on the untouched tree | premise did not reproduce |
| the eval gates are the expensive half of KAT | guessed | **0.4 s vs 16.2 s for the kernel decide** - exactly inverted | wrong direction |
| r•H2 costs 8.6 s | measured once | **16.2 s of per-pass elaboration** | right number, wrong unit |
| G2 mirror ~700 lines | estimated | **1091 + 510 + 68 + 147** | under-called by ~2x |
| M-A remaining | 5-7 sessions | **DONE** - holds_staged exhibits all six clauses conditionally | **closed** |

**The headline: holds_staged exists.** Given an AdmissiblePairing on the exhibited groups plus three
Gₜ instances, there EXISTS a product with Eip2537.Holds g1CodecZ g2CodecFold product - all six
fields, axioms the standard three. The FrameLaws encoder-first requirement I flagged as the one
place the landmark could stall HELD, in four lines, because injectivity makes Classical.choose pick
the unique preimage.

**So the distance to a single Holds term is now exactly one named hypothesis (D-P36a) - no Fp12, no
point count, no new mathematics.** That is the position after six sessions on the G1/G2 track,
against my original estimate of 3-5 for M-A plus a research-grade pairing. The research-grade part
did not exist; I had misread a free parameter as a missing construction, twice.

**A new sub-class of error, the 14th instance:** the first where the wrongness was in a prescribed
TACTIC rather than a diagnosis. P-G2 recorded the symptom correctly, named a plausible fix, and never
tested it - and the fix would have wasted 18 minutes per attempt. **Recorded prescriptions should be
labelled tried or guessed.**

**Revised totals.** M-A: closed. Remaining to lowering_equivalence: the pairing hypothesis (1
session), then M-B/M-C/M-D as before. **Total revised from 20-34 to 16-27 sessions**; wall-clock
**6-11 weeks**. Third revision, net downward.

### R7 - round 129, after P-HOLDS-FINAL. The model track is CLOSED; the difficulty moved.

| claim | before | actual | verdict |
|---|---|---|---|
| M-A: exhibit a single Holds term | 5-7 sessions (R2) | **6 sessions, closed** | **HIT** |
| distance to lowering_equivalence after Holds | just the LoweringCorrect fields + Bridge lemmas | **no** - M8 (ir_refines) is where the difficulty lives | **error of kind, 15th** |
| exhibiting Helps the four Holds-binding specs | implied | **advances none of their proofs** - they bind at S.E.g1 | **vacuity status only** |
| checks.sh ~476 s | recorded | 8m31s = 511 s | close |
| derivation a few lines | estimated | **one line** - but the package cost gate plumbing + 5 stale premises | right about the proof, wrong about the package |

**The headline: holds_exhibited exists.** All six Holds clauses, unconditional, resting on exactly
five named axioms, gate-enforced at three layers including an axiom-shape probe where an extra axiom
AND a missing one both redden. **No mathematical model-construction is left anywhere on the path.**

**The 15th error of kind is a reframing, not a mis-size.** I said the landmark would reduce to the
LoweringCorrect fields and the Bridge lemmas once Holds was exhibited. It does not. Two corrections:

1. **Exhibiting Holds at codecs advances four spec theorems by nothing.** They bind Holds at
   S.E.g1 - the Surface's own codec. The antecedent moved from unsatisfiable-in-principle to
   satisfiable-and-unexhibited. Real for the trusted base, **zero** for their proofs.
2. **M8 is the actual remaining difficulty**: irCheck is a decidable fragment rather than
   alpha-equivalence, shell_unfolds pins the shell model rather than the deployed entry path, and
   ir_refines - the IR-to-shell simulation - is untouched by everything on this track.

**Lesson: a milestone's difficulty can relocate rather than shrink.** Closing the model track did not
shorten the path to the landmark; it revealed the weight was mostly elsewhere. **When a blocker
closes, re-ask where the difficulty went rather than subtracting it.**

**Revised totals.** M-A **closed**. New item: build a Surface over the curve codecs (1 session,
plumbing). M8 **uncosted - the largest open estimate in the project**. Remaining to the landmark:
M-B 4-6, M-C 8-14, M-D 2-5, M-E 1-2, Surface 1, **M8 unknown**. **Total 16-27 becomes 16-27 plus
M8**, and I decline to number M8 until it is scoped rather than guess a third time. Wall-clock
unchanged at 6-11 weeks **only if M8 is small**; it is the single item that could move that
materially.

**Two new traps found by running**, both cheap to state and expensive to rediscover: the word sorry
inside a Lean **string literal** counts as a proof hole (lean_grep strips comments, not strings),
and a **comment-only** edit shifts SORRY.md's file:line pins - that cost a full 8-minute gate run.
Also: registry tokens match **source text**, so a phrase split across a string concatenation is
invisible to the gate.
### R8 - round 130, after P-CSURFACE-M8. M8 scoped: large, and its headline obligation is broken.

- curve Surface estimated 1 session: **actual 1 session** - first milestone estimate to land exactly.
- M8 size: was uncosted and refused-to-guess; now **8-16 sessions** (restate the solc hop 1-2; dispatcher model and shell_unfolds restatement 2-4; run leg as prerequisite 2-4; IR-shell bridge 3-6 - all labelled GUESSED in M8-SCOPE.md).
- Total to lowering_equivalence: **25-43 sessions** (was 16-27 plus M8). Wall-clock **9-18 weeks** (was 6-11). R7's condition that the estimate hold only if M8 is small resolved badly.
- ir_refines was assumed hard-but-valid. **It is FALSE AS STATED** - error of kind, 16th.

**The finding that justified scoping before sizing.** irCheck was probed before anyone attempted ir_refines, and it is BLIND: irRet (ret 0,32) and irRev (revert 0,0) both pass irCheck by rfl while differing in HaltKind - which ObsView explicitly carries. Five mutants pass against the real 2,898-line artifact, including deleting the first statement of every helper body and mutating the CREATION object. So the hypothesis admits counterexamples, and no amount of M8 proof work can fix a broken hypothesis.

**Had M8 been briefed as a proof attempt rather than a scoping task, 8-16 sessions would have been spent driving at a statement that cannot be true.** Strongest argument in this ledger for scoping before sizing.

**The 16th error of kind is the first belonging to the plan rather than the orchestrator:** ir_refines was written as though irCheck pinned the IR's behaviour. It pins a decidable fragment. Same class as Eip2537.Holds and the frozen verifyNative_iff_msgs - a headline statement that cannot hold as written - found by MEASURING a hypothesis rather than trying to prove it.

**One estimate landed exactly**, which is evidence the calibration converges once work is plumbing rather than unknown-shape mathematics.

**The datum that would tighten the range most: prove ONE Partials spec.** It anchors both M-B (4-6, still pure extrapolation) and M8's re-derive-preconditions-against-dispatcher-memory step - the same unknown counted twice.
### R9 - round 131, after P-SPEC1. One `Partials` spec proved: the extrapolation has a datum now.

**What landed.** `Lowering/Partials.lean:traceReturn_spec` - the terminal arm - went from a
registered hole to a kernel-checked proof. Register **57 -> 56**, agreed three ways (tree,
`scripts/sorries.sh`, `SORRY.md` regenerated by `scripts/gen_sorry.sh`, never by hand). 13 new
declarations, of which 9 are proof machinery and 4 are the D-P23 pair for the theorem itself
(`traceReturn_run_inhabited` exhibits a run; `traceReturn_post_bites` refutes the post with a
one-literal mutant).

| claim | before (recorded) | measured | verdict |
|---|---|---|---|
| M-B at 2-3 specs/session, 4-6 sessions | pure extrapolation | **the cheapest of the twelve took ~50 min of proof work and ~40 single-file type-check iterations**, of which ~35 min built machinery every later arm inherits (per-op Step inversion, the `Inv .pairing` projection, the memory lemma); the composition itself was ~15 min | **rate plausible for local-only arms, but the item list is wrong** - see below |
| `traceReturn_spec` was 'the return builtin record and nothing else' | sketch | right about the substance, stale about the line (EVMExec :840-843 -> :877-880 in the fork), and it named NONE of: the `Inv .pairing` projection, the guard inversion, or the fact that `RETURN_MPTR` is a FREE identifier of the fragment | sketch under-specified, as every package before found |
| the run leg needs `dialect_deterministic` (M-D) | assumed by association | **FALSE for this arm.** `iszero`/`mstore`/`ret` are local ops whose relation is the function `stepOp`, so per-op uniqueness falls out of inversion with no determinism hypothesis. `staticcall_failure_reverts` was not needed either | **decouples the local-only specs from M-D** |
| the spec is a claim about the emitted program | assumed | **true only for environments that bind the shell constants.** `RETURN_MPTR` unbound means NO derivation, so `StmtsContractAll` holds vacuously; the pin `hblk` cannot see it (Partials' own free-identifier gate counts 76 such names) | new finding, class 17: **vacuity-by-stuckness**, witnessed away by `traceReturn_run_inhabited` rather than assumed |
| expected RAM peak for this package | brief quoted 3.90 GiB tree / 3.15 GiB largest | **one module at a time, `lake env lean` on a 2,800-line file: largest process 0.6 GiB, tree under 1 GiB; `checks.sh` peak reported TIGHT at 15.08 GiB available** | under the quoted figures; no heavy decide added, and none was needed |

**Two gates do NOT protect this theorem, measured, not asserted.**

1. **The post is unfingerprinted.** Weakening the conclusion from
   `st'.halted = some (.ret, abiTrue)` to `o = .halt ∧ True` and trivially repairing the proof
   leaves `lake build` green AND `check_statement_fingerprints.py`, `check_hypothesis_bundles.py`
   and `check_duplicate_facts.py` all rc=0. The spec-pin list carries only
   `["hblk : BlkIsEmitter S"]` per theorem - the binder, never the conclusion. So the only thing
   standing between this package and a silent weakening is the proof itself, and a package under
   pressure could edit both. Recorded as the limit, not repaired: repairing it means adding the
   conclusion fragments to `PARTIAL_SPEC_PINS`, which is a gate change and not this package's call.
2. **The falsification-deletion gap, sixteenth measurement.** Deleting all three falsification
   theorems (`not_inv_pairing_of_success_zero`, `not_readBytes_storeWord_33`,
   `traceReturn_post_bites`) leaves the build green and every text gate passing. No gate counts
   them. Claim no coverage for them here.

**Positive controls, so the gates above are not being blamed for a hole that does not bite.**
Changing one literal in the block the proof pins to (`.lit (.number 1)` -> `2`) reddens 3 goals;
changing the mutant's return width 0x40 -> 0x20 reddens the falsification. The proof is about
the emitted AST, and the refutation is about the one literal it claims matters.

**M-B has to be re-cut, and the reason is not proof speed.** Of the twelve:

* 4 bind `Eip2537.Holds` (pcs, finalPairing, finalPairing_progress, finalPairing_acc) and are
  **M8 work**, not M-B - P-CSURFACE-M8 named the residual binders.
* 1 (`vkLoading_spec`) is recorded IN THIS FILE as unprovable as stated: its post pins the VK
  payload image and the emitted slice fills it through `extcodesize`/`extcodehash`/
  `extcodecopy`, and no hypothesis says what the world's code is (`gap_vkLoading_world_reads`).
  A statement repair has to come first, and the file says the choice of WHERE the world belongs
  is the orchestrator's.
* 3 more need bridges that do not exist: `transcriptParser_spec` the `readScheduleAgrees`
  Encoding owes, `lagrange_spec`/`lagrange_progress_spec` the batch-inversion agreement
  (P-MODEXP, in flight).
* the remaining 4 (`traceReturn` now done, `quotientLin`, `transcriptParser` modulo its bridge,
  and the two progress twins whose side conditions exist) are the ones the measured rate applies
  to.

**Verdict on 4-6 sessions: too low as a total for twelve, roughly right for the four that are
actually approachable now.** The datum says the fixed cost is the inversion machinery, not the
arithmetic - one session buys that, and after it a local-only arm is tens of minutes of
composition. So M-B should be re-scoped to 'the specs whose bridges exist' at 2-3 sessions, with
the Holds-binding four moved to M8's line (they were double-counted there already: R8 named the
same run leg) and vkLoading moved to a statement-repair item. **The same unknown counted twice
in R8 is now counted once, measured: the run leg for a local-only arm is cheap.**

### R10 - round 132, after P-SPECPIN. The gate hole is closed; M-B's item list is wrong AGAIN, in a way only a read-only audit found.

**What landed (gate only - no Lean file was touched, by instruction).** `scripts/check_statement_fingerprints.py`
gained conclusion pins for all ten specs, read off the CONCLUSION alone (the text after the first
top-level colon, value cut), each two-sided: a `must` postcondition shape and a `must_not` list of the
trivialisation shapes. Plus two supporting pin sets the conclusion pins are worthless without: the
bodies of `PartialSound`/`PartialProgress` (else the application is kept and the relation behind it
hollowed), and `Partial.pre`/`Checkpoint.next` (else the target Inv checkpoint moves under a spec
whose text names only a Partial). Fragments **158 -> 221**. `lake build` green at 5212 jobs,
`checks.sh` EXIT=0 in 13 sections, register unchanged at **56** (no Lean line shifted).

**Shown to bite, not asserted.** Twelve perturbations on an APFS clone of the whole repo, each run
against BOTH the new gate and the gate as it stood at HEAD:

| perturbation | old gate | new gate |
|---|---|---|
| traceReturn post -> `o = .halt ∧ True` (**the hole P-SPEC1 reported**) | **rc=0** | rc=1 |
| traceReturn post -> bare `o = .halt` | rc=0 | rc=1 |
| traceReturn post -> wildcard payload `some (.ret, _)` | rc=0 | rc=1 |
| lagrange strictness post -> `(fun _ _ => True)` | rc=0 | rc=1 |
| lagrange_progress demoted `PartialProgress` -> `PartialSound` | rc=0 | rc=1 |
| `PartialSound` body hollowed to a True post | rc=0 | rc=1 |
| `Checkpoint.next` moved `.pcs => .pairing` -> `.pcs => .pcs` | rc=0 | rc=1 |
| acc arm decision swapped `batchedCheck` -> `DualMSM.check` | rc=0 | rc=1 |
| traceReturn post suffixed `∨ True` - EVERY must fragment still present | rc=0 | rc=1 |
| vkLoading conclusion suffixed `∨ True` - EVERY must fragment still present | rc=0 | rc=1 |
| vkLoading conclusion -> `True` | rc=1 | rc=1 |
| decoy binder carries the fragments, conclusion -> `True` | rc=1 | rc=1 |

Ten of the twelve were invisible to the old gate; all twelve redden the new one. The two
`∨ True` rows are the ones that justify the `must_not` direction: a gutting that keeps every
required fragment verbatim and empties the post beside it passes a presence test, and only the
forbidden-shape half sees it. **No perturbation failed to redden.**

**M-B's eleven remaining holes, classified (read-only; nothing proved).** First a count
correction: the "twelve specs" of R9 were never twelve specs. `Partials.lean` held twelve
registered holes, of which **ten are spec theorems and two are the `alwaysReverts` vacuity
lemmas**. Of the eleven that remain:

| hole | class | the specific missing thing |
|---|---|---|
| `vkLoading_spec` | **unprovable as stated** (two blockers) | (a) `gap_vkLoading_world_reads`: the post pins the VK payload at `vkMptr`, the emitted slice fills it via `extcodesize`/`extcodehash`/`extcodecopy` at AUTHORIZED_VK, and no hypothesis says what the world's code there is (`DeploymentW` would; the theorem binds none). (b) NEW: the sketch's `EnvAgrees.accHeader`/`accNoHeader` - whose own comment says "without these clauses vkLoading_spec is unprovable in accumulator renders" - are not in the implemented 10-field structure. |
| `transcriptParser_spec` | **needs two bridges** | (a) `readScheduleAgrees`, the Encoding-area transcript-bytes agreement the PROOF HOLE names. (b) NEW: the parser's main output is the REVERSED_EVALS table (`GenAst.lean:1144-1154` writes it) and `Inv .transcript` has **no clause pinning that window** - the sketch's `holdsFrs st (ptrAddr M.reversedEvalsMptr) (reversedEvalsOf PV S)` was dropped and `reversedEvalsOf` exists nowhere in the tree. So the post cannot express what the partial is for. |
| `lagrange_spec` | **needs bridge** | the batch-inversion agreement (`AssemblyHelpers.yul:226-229` vs Lean `lIRange`), P-MODEXP in flight; plus Fr-word <-> `mulmod`/`addmod` agreement for the squaring walk. |
| `lagrange_progress_spec` | **needs bridge** (same) | same batch-inversion agreement. NOT blocked on its side condition: `EnvAgrees.xNotRoot_iff_notDomainPoint` (Inv.lean:511) already turns `ChallengesGood.xNotRoot` into the domain-point exclusion. |
| `quotientLin_spec` | **approachable now, but partly inert** | nothing is missing from the hypotheses - no `Holds`, no world read, no Encoding bridge - and the emitted slice writes exactly the two words the post demands (`GenAst.lean:862-863`). CAVEAT, and it is a statement finding, not a proof one: two of the intended clauses (quotient eval, selector buckets) are **inert** because `Snapshot.lin` is a named hole always `none` from `snapshotOf` (D6 limit 1, `Snapshot.lean:136`), so a proof of this spec buys strictly less than the sketch claimed. |
| `pcs_spec` | **binds `Holds`** - M8 | `hh : Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product`; no Surface in the tree exhibits `Holds` at its own codec (`curveSpecResidualBinders`). Plus the f_eval Horner fold and the `finalMsmShape` pair-count agreement. |
| `finalPairing_spec` | **binds `Holds`** - M8 | `hh` + `Holds.pairing2` to turn the precompile answer into the pairing equation, + the staticcall failure mapping. |
| `finalPairing_progress_spec` | **binds `Holds`** - M8 | `hh` + `Holds.pairing2` in the check-true -> answer-true direction. |
| `finalPairing_acc_spec` | **binds `Holds`** - M8, + a dropped clause | `hh` (`g1Msm1`/`g1Add` for the slot rewrite) + the accumulator partial ASTs; and the sketch's `EnvAgrees.accBasesInVk` - which existed precisely so this theorem could relate the folded point to `a.fullyCollapse (tblOf PV fb)` - has **no counterpart anywhere** and is not in Inv.lean's dropped list. Inv's `.vk` accumulator `holdsG1` slot clauses were also replaced by `hasAccumulator == false || S.acc.isSome` (named gap R-52). |
| `partialSound_of_alwaysReverts` | **approachable now** | no missing hypothesis; needs Step inversion at the open dialect for `revert`. NOTE: `PartialSound`'s own docstring (Partials.lean:173) says "always Reverts satisfies soundness is the lemma that says so, and it is **proved** rather than claimed" while the lemma is a `sorry` - a doc-vs-tree mismatch this item would repair. |
| `partialProgress_not_of_alwaysReverts` | **approachable now** | same inversion + `.halt ≠ .normal`; its satisfiability side condition is a binder (`hpre`), so no instance is needed. |

**THE REQUIRED FINDING - the honest size of M-B.** 3 approachable, 4 M8's, 3 bridge-blocked,
1 statement-blocked. And of the 3 approachable, only **one is a per-partial spec**
(`quotientLin_spec`), whose post is partly inert; the other two are definitional vacuity lemmas
that close nothing on the `PartialSpecs` checklist. So M-B is **not 4-6 sessions and is not 2-3
either**. It is **one session of approachable residue - three holes - and then it is blocked**,
behind M8's `Holds`-at-a-Surface exhibit (4 holes), behind `readScheduleAgrees` and the
batch-inversion agreement (3 holes), and behind a decision about where the world belongs in
`vkLoading_spec` (1 hole). Charging M-B 4-6 sessions has been carrying work that cannot start.

| claim | before (recorded) | measured | verdict |
|---|---|---|---|
| M-B = 4-6 sessions, then 2-3 for "the approachable arms" | R9 | 1 session closes 3 of 11; the other 8 need M8, two named bridges, or a statement repair | **still too high, and the item list was wrong twice**: the twelve were 10 specs + 2 vacuity lemmas, and the "four approachable" of R9 was three, one of which is partly inert |
| the spec-pin gate protects the proved specs | assumed until P-SPEC1 | it protected the BINDER only; 10 of 12 guttings passed it | **fifth gate blind spot of the class, now closed and shown to bite** |
| conclusion fragments must be read off the conclusion | not considered | a decoy binder `(hdecoy : (fun _ : Prop => True) (PartialSound ...) = True)` elaborates and is `rfl`, so a declaration-scoped presence test is defeatable | matched on `conclusion(...)` only |
| pinning the application is enough | not considered | redefining `PartialSound`'s post to `True` guts six specs at once with no theorem edited | relation bodies + `Partial.pre`/`Checkpoint.next` pinned too |
| expected RAM for a full gate run | brief quoted 5.09 GiB tree / 4.42 GiB largest | **5.11 GiB tree / 4.44 GiB largest lean**, verdict TIGHT at 17.00 GiB avail, EXIT=0 | matches; `ram_guard --selftest` ALL PASS first, `--proc-limit 6G --limit 24G` |

**Limits of this repair, stated rather than hidden.** (1) It is a TEXT gate. A package that
weakens a conclusion AND moves the pin in the same commit passes it; what makes that visible is
the diff, not the gate. (2) The fragments name shapes, not meanings: `some (.ret, abiTrue)` is
pinned as tokens, so renaming `abiTrue` reddens the gate even if the rename is sound. (3) The
falsification-deletion gap is unchanged - **sixteenth measurement, no new claim**: deleting
`not_inv_pairing_of_success_zero`, `not_readBytes_storeWord_33` or `traceReturn_post_bites`
still leaves the build green and every gate green. No gate coverage is claimed for
falsifications here either. (4) D-P23: this package adds no new Lean theorem, so there is no new
witness/falsification pair to state; the two probes written to check the audit (the
`finalPairing` post-recovery) were run OUTSIDE the tree at `/tmp` and are reported as text, not
committed.

## What would most improve this ledger

1. ~~**One `Partials` spec proved.**~~ **DELIVERED by P-SPEC1** - see R9. The datum says the rate is right for
   local-only arms and that five of the twelve are not M-B's to do.
2. **P-MODEXP's outcome.** If the Fermat reading holds, M-A's last item is cheap and the
   landmark moves up; if not, the agreement theorem is the first genuinely hard item in M-A.
3. **A sorry-per-session floor rather than a mean** — the 0-output sessions are what make the
   naive projection wrong.

---
### R3 - round 118, after P-CANON. The wall was real; its recorded mechanism was wrong.

| claim | before (recorded) | actual | verdict |
|---|---|---|---|
| the canonicity walk is "blocked on an elaborator limit, not mathematics" | blocked | **LANDED in ~50 min**, no elaborator limit hit | **right that it is not mathematics, wrong that it is a limit** |
| the cost is `fpInv`, a 381-bit `modPow`, forced by whnf of affineAdd/affineDouble | recorded mechanism | **the cost is the 255-step `affineSmul` FOLD**, forced because whnf of a PAIR `==` beta-reduces through `BEq` into `affineSmul fpOps blsR X`; `fpInv` only matters at literal POINTS (`(affineDouble fpOps genPair).1 < blsP` by `rfl` does fail) | **seventh error of kind** - symptom accurate, mechanism mis-attributed |
| cure 1: keep such facts inside `decide` | suggested | half right: `decide` proves the byte facts (16.6 s, measured) but the walk needed no `decide` at all - a walk over VARIABLES checks in milliseconds | partial |
| cure 2: give `FpFrame` a canonicity field | suggested | **not used and not needed**: it rewrites every constructor and every `Subtype.eq` in the file and still leaves the same branch walk to prove the new field for `addFrame P Q` | rejected on measurement |
| the transport across `smulFrame_val` "requires exactly the defeq check that dies" | recorded | **`▸` along a named equation never whnfs the fold and checks instantly**; what dies is `rw`/`simp`/`show`/`change` through the pair-`==`. `unfold`/`delta` cross `g1InSubgroup` for free | **the recorded impossibility was a tactic choice** |
| `blsR • emb genFrame = 0` costs about 15 s | predicted | 16.6 s, peak tree 4.64 GiB, largest process 3.99 GiB | **HIT** |
| `AddSubgroup.zsmulSet` naming task | recorded as a name problem | **worse than a name**: no `zsmulSet`, no `zsmuls` anywhere in mathlib (0 hits); the carrier is `AddSubgroup.zmultiples`, AND `Group (Additive A)` does not synthesize for an additive group `A` in this revision, so the exhibit must be `Subgroup.zpowers (Multiplicative.ofAdd x)` | naming finding + a new one |
| expected RAM peak for this package | brief quoted ~10.6 GiB tree / 3.3 GiB largest | **4.82 GiB tree / 4.09 GiB largest** (the quoted figure was a cold parallel build; this was one module) | over-estimate, 2x |

**What landed.** `affineAdd_canonic`, `affineDouble_canonic`, `addFrame_canonic`,
`doubleFrame_canonic`, `smulStep_canonic`, `smulFrame_canonic` (the walk);
`nsmul_emb_eq_zero_iff`, `g1InSubgroup_iff`, `g1PointMsmValid_iff` (the subgroup half of
`g1Valid`, DISCHARGED); `genPair_r_smul_zero`, `r_nsmul_emb_genFrame`, `g1InSubgroup_genPair`,
`g1PointMsmValid_genPair` (the witness the note said was unreachable);
`primeOrderWith_zpowers_emb_genFrame` + `natCard_zpowers_emb_genFrame` - **the first
`PrimeOrderWith` exhibit at a real curve point**, and it is `primeOrderWith_zpowers` in one line
now that `r • emb genFrame = 0` exists. Register unchanged at 57: nothing here was a sorry.

**The M-A line has to be re-cut.** P-CANON closes the canonicity item and DISCHARGES the subgroup
half of `g1Valid`, but it does NOT land `g1Add`/`g1Msm1`. What stands between them and a proof is
now named and measured, and it is byte plumbing rather than algebra or number theory:
`g1Of? (g1PointBytes P) = some P` for canonical `P`, then `bytesSlice` over the 128-byte
concatenation (`Array.extract_append`), then `g1AddValidInput` and the `where`-clause unfolding of
`g1MsmPairs?.go`. My estimate of that item ("15-20 minutes") was **optimistic**: the first three
pieces check, the `g1MsmPairs?.go` unfolding is where I stopped. So the point count is the only
remaining MATHEMATICAL G1-side item, but it is not the only remaining item: five of six `Holds`
clauses need the point count PLUS a codec on the `zpowers` carrier PLUS this byte round trip.
**Eighth lesson: "the last mechanical thing" is a claim about one mechanism.** There were three.

**Perturbation evidence.** Five code perturbations (weaken `g1InSubgroup_iff`'s RHS; drop
`g1PointMsmValid_iff`'s canonicity; drop `affineAdd_canonic`'s second hypothesis; change the
scalar in `genPair_r_smul_zero` to `blsR + 1`; change the exhibit's cardinality to `blsR + 1`) all
redden `lake build`. Deleting all four falsification/witness theorems
(`affineAdd_canonic_needs_hypothesis`, `nsmul_emb_eq_zero_iff_needs_canonical`,
`smulFrame_gen_canonical`, `g1InSubgroup_infFrame`) leaves the build **GREEN** - the
falsification-deletion gap, measured a **ninth** time across five packages. Coverage claims must
keep saying that.

**One negative result worth keeping.** The canonicity hypothesis in `g1InSubgroup_iff` is
load-bearing for the PROOF and refutable at `n = 1` (`nsmul_emb_eq_zero_iff_needs_canonical`), but
at the actual scalar `blsR` it is NOT necessary for the junk frame: `g1InSubgroup junkPair = true`
by `decide`, because `blsR` has more than one set bit and the second one flushes the accumulator
to the literal `(0,0)`. A hypothesis being used is not the same as a hypothesis being necessary.

---
### R4 - round 119, after P-G1CODEC. The plumbing landed; two NEW walls showed up where none were recorded.

| claim | before (recorded) | actual | verdict |
|---|---|---|---|
| ~ofLowDigits_append~ fires on the wrong occurrence once the RHS is in ~bytesToNatBE~ form | P-CANON | **CONFIRMED.** Cure: convert all three sides (~A~, ~B~, ~A ++ B~) to ~ofLowDigits~ as named ~have~s, rewrite at that level, convert back with ~← hB, ← hA~ | right, and the cure is new |
| ~bytesTake_whole~ needs ~@ByteArray.size_data~ to state its hypothesis | P-CANON | **WRONG IN ITS SPECIFICS.** ~bytesTake b 0 b.size = some b~ needs NO hypothesis. What fails is ~rw [Array.extract_eq_self_of_le _]~: that lemma's array AND its bound are implicit, so the matcher has nothing to match on. Cure: the ~@~-term ~@Array.extract_eq_self_of_le UInt8 (ByteArray.size b) b.data (Nat.le_refl _)~ | **tenth wrong premise** - symptom real, named cause wrong |
| slice side conditions must be stated against ~ByteArray.size A~ | P-CANON | **CONFIRMED** verbatim: ~bytesSlice_window_before / _after~ take ~Bytes~-level hypotheses and enter ~.data~ exactly once | right |
| "budget for ~g1MsmPairs?.go~, it is a ~where~-clause function and may not behave like the rest" | this brief | **it behaved exactly like the rest.** ~g1MsmPairs?.go.eq_1~ / ~.eq_2~ are ~rfl~-level equation lemmas; the one-pair frame unfolds in 12 lines | **over-estimate, and the brief told me to over-estimate it** |
| ~Point.toAffine~ + ~ZMod.val~ gives the codec map | this brief | ~Point.toAffine~ **does not exist** in this mathlib (zero hits under AlgebraicGeometry/EllipticCurve/). A two-line ~match~ on the ~Point~ inductive does the job, and ~ZMod.val_lt~ is what makes every frame canonical by construction | right idea, wrong name - **eleventh wrong premise** |
| a ~G1Codec~ on the ~zpowers~ carrier is "the missing piece" | P-CANON | **also missing: ~Module (ZMod blsR) (Additive G₁z)~ does not synthesize.** Built from ~AddCommGroup.zmodModule~, whose hypothesis ~∀ x, r • x = 0~ is exactly ~r_nsmul_emb_genFrame~. So ~g1Msm1~ was not blocked by plumbing alone - it was blocked by that instance, which P-CANON made possible but did not name | **the named blocker was real but incomplete** |
| expected RAM peak, single module | brief quoted 4.82 GiB tree / 4.09 GiB largest | **4.82 GiB tree / 4.07 GiB largest** (verdict TIGHT at ~--proc-limit 6G --limit 24G~) | **HIT** - first time the quoted figure matched |
| my own estimate: byte plumbing 40 min, exhibit 40 min | this session | plumbing **25 min** (optimistic by nothing), exhibit **~70 min** (pessimistic by 30) - the overrun was two unrecorded walls, below | wrong in both directions, as usual |

**TWO WALLS NOBODY RECORDED, both the same shape as the ~affineSmul~ fold wall.**
(1) **~g1PointMsmValid P~ for a VARIABLE ~P~ cannot be whnf'd.** ~dsimp~ of the ~match~ in
~g1MsmOutput~ forces ~List.all [(P, s)] f~, which forces ~g1InSubgroup P = affineSmul fpOps blsR P
== (0,0)~ - the 255-step fold, on a variable. Reached through a ~List.all~ over a LITERAL LIST, not
through a pair-~==~, so P-CANON's diagnosis would not have predicted it. Cure: ~g1MsmOutput_some~
takes the decoded list as a VARIABLE ~ps~ with ~g1MsmPairs? input = some ps~ as a hypothesis, so
the ~all~ stays stuck and is rewritable. (2) **~blsR • X~ for a variable ~X : W.Point~ cannot be
whnf'd either** - ~nsmul~ recurses on the 255-bit literal, so ~rfl~ on
~toAdd (ofAdd X ^ blsR) = blsR • X~ dies at the default ~maxRecDepth~. Cure: the PROPOSITIONAL
~toAdd_pow~ instead of the definitional route. **Lesson: "whnf of a fold at a literal scalar" is a
category, not a lemma - ~affineSmul~, ~List.all~-forcing, and ~nsmul~ are three doors into it.**

**What landed (84 declarations, 887 lines, ~Midfall/Instances/G1Agreement.lean~).** All four links of
the chain: ~bytesToNatBE_bytesAppend~, ~bytesTake_of_size~, ~fpCoordOf?_fpCoordBytes~,
~bytesSlice_g1PointBytes_left~ / ~_right~, **~g1Of?_g1PointBytes~ (THE ROUND TRIP)**,
~g1AddValidInput_g1PointBytes~, ~g1AddOutput_g1PointBytes~, **~g1MsmPairs?_singleton~ (the
~where~-clause)**, ~g1MsmOutput_some~, ~g1MsmOutput_singleton~. And the exhibit: ~G₁z~,
~instance PrimeOrderWith~, **~instance Module (ZMod blsR) (Additive G₁z)~**, ~ptPair~, ~frameOf~,
~emb_frameOf~, ~ptPair_emb~, ~nsmul_blsR_eq_zero~, ~g1PointMsmValid_ptPair~, **~g1CodecZ~**, and the
three clauses **~g1CodecZ_g1Valid~, ~g1CodecZ_g1Add~, ~g1CodecZ_g1Msm1~** plus
~g1CodecZ_eipRoundtrip~ and ~g1CodecZ_g1DecodesWidth_iff~. Register unchanged at 57: nothing here
was a sorry.

**THE REQUIRED FINDING, stated exactly.** On the G1 side, **three of the four G1 clauses are now
discharged at a real-curve codec** (~g1Valid~, ~g1Add~, ~g1Msm1~). The fourth, ~g1Decodes~, is
**equivalent over this codec to surjectivity of ~g1zToEip~ onto the frames the precompile accepts**
(~g1CodecZ_g1DecodesWidth_iff~), and that statement is ~|E(Fp)[r]| = r~ - so **yes, the point count
is genuinely the only thing between here and four of four on the G1 side.** It is NOT the only thing
between here and a ~Holds~ TERM: ~pairing2~ needs an ~AdmissiblePairing~ and the only one in the
tree is the exponent model (P-HOLDS2), so "five of six" is five clauses discharged across TWO
exhibits (four G1-side at the curve once the count lands, ~pairing2~ at the exponent model), not
five fields of one ~Holds~ structure. ~g2Valid~ remains the sixth and needs the G2/Fp2 package.
Stating the limit plainly, because the brief's framing invited the opposite: **no ~Holds~ term
exists yet and this package does not produce one.**

**Perturbation evidence (APFS clone of the WHOLE repo under /tmp, ~30 s per build).** TWELVE code
perturbations, **TWELVE reddened** ~lake build Midfall.Instances.G1Agreement~: drop the round trip's
~y~-canonicity; swap ~x~ and ~y~ in the round trip's conclusion; claim the double instead of the sum
in ~g1AddOutput_g1PointBytes~; wrong slice offset in ~bytesSlice_g1PointBytes_right~; wrong scalar
readback in ~g1MsmPairs?_singleton~; zero the scalar in ~g1MsmOutput_singleton~; drop the product in
~g1CodecZ_g1Add~; drop the scalar action in ~g1CodecZ_g1Msm1~; drop the width hypothesis from the
~g1Decodes~ equivalence; invert the validator transfer ~g1PointMsmValid_ptPair~; break the infinity
branch of ~emb_frameOf~; drop canonicity from ~ptPair_emb~. **No perturbation failed to redden**,
which is worth saying precisely because the last two packages each had one that did not.
**DELETING all ten falsification and witness theorems** (~g1Of?_g1PointBytes_needs_canonical~,
~g1AddValidInput_needs_the_length~, ~g1MsmPairs?_needs_whole_pairs~, ~g1zToEip_not_constant~,
~g1CodecZ_g1Msm1_scalar_matters~, ~g1zOfEip?_refuses_outside_the_image~,
~g1CodecZ_g1Valid_witness~, ~g1CodecZ_g1Add_witness~, ~g1CodecZ_g1Add_refuses_noncanonical~,
~fpCoordOf?_fpCoordBytes_none_of_too_big~) **leaves the build GREEN** - the falsification-deletion
gap, measured a **tenth** time across six packages. **No gate coverage is claimed for any
falsification here: they are true, proved, and invisible when removed.**

**A self-inflicted loss worth recording.** A splice that replaced the closing ~gap~ docstring used
~s.indexOf('end Midfall.Instances')~ for the right-hand cut, which found the file's LAST line only
after the new sections had already been appended - so the slice deleted 44 KB of fresh proofs and
the build stayed green because what remained was consistent. **Symptom to keep: the file got
SHORTER after an insertion.** Cost: one rebuild cycle plus a full re-write of both blocks, ~15 min.
The restored version built green on the first try, which is the only silver lining available.

### R5 - round 120, after P-POINTCOUNT. The point count was elementary after all - third error of kind on this item.

| claim made | before | actual | verdict |
|---|---|---|---|
| the count needs the n-torsion structure theorem + Weil pairing | route (b) | **neither**: #E(F_p) <= 2p+1 (two square roots per x) and 2p+1 < r^2 squeeze the r-torsion to exactly r | **error of kind, third time** |
| mathlib lacks the structure theorem | true | **true but irrelevant** - division polynomials exist with degree bounds and NO link to nsmul; no Weil pairing; no point-counting theorem (LFunction.lean defines the local polynomial, proves nothing) | held, did not gate |
| gcd(r, p-1) = 1 is the cheap first step of the route | predicted used | **not used at all** | dead work, recorded |
| the substitute assumption Nat.card accepted frames = r | planned fallback | **it is a theorem**; no new trusted-base entry | better than target |
| G1 side after this package | 3 of 4 + 1 assumption | **4 of 4, no assumption** (g1CodecZ_g1_four) | revised up |
| cost | ~1/3 of a session (exploration box) | ~1 session: the count is short; the decoder-to-encoder byte direction (never needed before) and three elaborator walls ate the rest | ~3x the box |

**The mechanism, for the next reader.** For prime r the r-torsion of an abelian group is an
F_r-vector space, so its size is a power of r. One point of order r gives r of them; the
affine-plane count gives at most 2p+1 points in all; and r^2 > 2p+1 for any curve with
cofactor 1 and r much larger than sqrt(p). That is BLS12-381 G1 exactly. No Hasse bound, no
structure theorem, no pairing, no point counting.

**New wall recorded (fourth of this class).** g1PointMsmValid_iff applied to a VARIABLE frame -
not decide'd, just an .mp - dies at default maxRecDepth, and unlike the decide cases raising
the depth DOES clear it (no computation is requested, only a deep unifier whnf). Two Nat.card
formulations of the count were dropped for the same class of wall: the count is proved as a
membership statement (torsion_eq_zpowers_gen), not as a Nat.card equation.


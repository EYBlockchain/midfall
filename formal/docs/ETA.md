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
| `dialect_deterministic`: true or false? | brief guessed **probably FALSE** (gas nondeterministic, arbitrary oracle) | **TRUE AS REGISTERED, proved in one session**, 3 s of elaboration, kernel-clean | **wrong kind again** | the registered statement already carries `hc : c.Functional` and `hg : g.Functional`; the guess reasoned about gas nondeterminism WITHOUT reading the hypotheses the statement assumes. Same class as the `77 constructors` figure in the hole's own docstring (real count 87) |

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
| P-DET | 1 | **1 (`dialect_deterministic`, closed AS REGISTERED)** | first sorry closed since P-SPEC1; +14 declarations (12 theorems, 2 gates); the `ir_refines` refutation became unconditional and `curveSurface_not_LoweringCorrect` came back on a better route; KAT pins moved +2/+1 |

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

### M-C — Accumulator 4 of 12 left + Calldata 3 of 7 left + Qvm/QvmFold 9 — **IN FLIGHT** (P-MC-CALLDATA 4/7, P-MC-ACC 8/12)

Largely independent of M-A. `Qvm` needs `LoweringPlan::new` (circuit-as-data, uncosted).
**Estimate: 8–14 sessions.** `Calldata` is the most mechanical and should be first.

### M-D — `dialect_deterministic` + the transport — **CLOSED by P-DET in 1 session**

P-BRIDGE: hits the 200k-heartbeat limit on external-call arms; 7 external ops by hand plus ~70
local via `Option.some.inj`. **Estimate: 2–5 sessions, wide variance.** This is the item most
likely to be mis-estimated in either direction.

**ACTUAL: 1 session, and the predicted wall did not exist.** The 200k-heartbeat claim was about a
fuel shape this proof never uses: 80 of the 87 ops fall to ONE lemma (`det_of_stepOp_graph`, whose
hypothesis is `Iff.rfl` per op) and the 7 external ones are arity splits plus `externalCall_unique`.
The whole theorem elaborates in **2.2 s** with a peak single-process RSS of 3.01 GiB. The transport
half — `Run.det`, `RunCommitted.det` — was already written and needed no change; it stopped being a
corollary of a hole and became a corollary of a theorem. Recorded at R24.

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
| M-D | **0 — closed by P-DET** | was the widest variance on the list; it cost 1 session and 2.2 s of elaboration |
| M-E | 1–2 | transport |
| **Total to landmark** | **13–24** | **revised down from 15–26 by P-DET closing M-D (2–5 → 0). Still revised down from 18–31 by R10's M-B re-cut; M8 (8–16, R8) is still NOT in this table, so this total is optimistic by exactly M8** |

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

### R11 - round 138, after P-RESTORE2. The specs were weaker than the sketches, and one was false.

**Four claims, and what measuring them showed:**

- My first audit said 8 dropped EnvAgrees fields were a weakening. **Over-flagged**: 4 were recorded
  with reasons and 3 relocated.
- My correction said 7 of 8 were fine. **Under-flagged**: `accBasesInVk` was unannotated, and the
  reversedEvals drop lived in the wrong register.
- `Inv.lean:443-447` argued the three VK header clauses were redundant against the `.vk` payload
  pin, and everyone inherited it. **REFUTED** - it pins memory to payload, never payload to codec,
  and at the old two-word fixture the slots were not even inside the pinned range.
- I planned to restore the sketch's 7-argument `EnvAgrees`. **Reverted after measuring**: it would
  have deleted three curve exhibits to gain four clauses. The clauses live in sibling `VkSlotsAgree`,
  and `EnvAgrees AND VkSlotsAgree` is the sketch's hypothesis field for field.

**The 17th error of kind is the most instructive yet: an ANNOTATED reason was still wrong.** The
redundancy argument was plausible, written down confidently, and false. **An annotated reason is
still a premise.** The standing instruction to re-verify recorded premises now has to cover
*explanations*, not just claims of impossibility.

**A second lesson about my own corrections**: over-flagged, then under-corrected - and both errors
came from checking whether a drop was *mentioned* rather than whether the *reason given* held. The
mechanical sweep of 404 sketched declarations (25 absent, 8 unannotated) is the first check that
does not depend on my reading.

**What changed in the specs.** Four clauses restored and **consumed** (`hvks` in three theorems plus
two checklist fields), so they are load-bearing. One spec's statement was strengthened because it
was **false as written** - the emitted block reads `success` before writing it. The fixture grew from
a 2-word to a 31-word header with codec-derived points. `PartialRejects` went from dead code to
backing two real obligations.

**Cost: 1 session.** Fragments 221 to 231, `ENV_CLAUSES` 1 to 5, 13/13 perturbations reddened,
sorries unchanged at 56 - **restoration costs no proofs and removes none**; it changes what the
remaining proofs must establish.

**Consequence for M-B**, already 'one session then blocked': `finalPairing_spec` and
`finalPairing_acc_spec` now carry an extra hypothesis `hvks`. That makes them harder to prove and
*worth* proving - the correct trade. M-B's one approachable spec is unaffected.
### R12 - round 139, after P-RESTORE3. An annotated reason was false a second time, and the false one was the calldata pin.

**What the package was for.** P-RESTORE2's sweep left 17 sketched obligations that were *annotated*
as absent. Annotation makes a gap visible, not correct, and these had never been checked.

| claim made | before | actual | verdict |
|---|---|---|---|
| the 17 annotated reasons hold | inherited from P-RESTORE2's sweep | **one was FALSE** (`hProofLayout` was dropped as a codec pin; it names no codec), **one was stale** (the numerator evaluator AST now exists), **one was half-false** (the `*_faithful` content had NOT moved into `end_to_end_noAcc`) | **error of kind, 18th** - and the second annotated reason found false, exactly the class R11 opened |
| re-deriving the sweep reproduces 25 absent | expected 25 | **23**, of which 1 is a parser false positive (prose matched as a field) and 9 are P-RESTORE2's own recorded renames | method holds; the count moves with the restorations |
| `hProofLayout` cannot be exhibited at the fixture | predicted, because `poseidonMeta.protocol` is the default (the circuit is not in the tree) | **exhibited by `rfl`**: the transcribed poseidon layout is EXACTLY `fromProtocol (protocolShape [8] [1] 3 1 4) 0x64 48 3`, field for field | **wrong estimate, good news** - the artifact transcription and the ported generator agree on 17 fields with no hand-holding |
| restoring an obligation breaks a fixture exhibit (as it did in P-RESTORE2) | budgeted one fixture rebuild | **nothing broke**; every new exhibit was `rfl` or `native_decide` on the first try | ~2x faster than the last restoration |
| a `fromProtocol` inversion lemma is cheap | ~10 min | **not proved**: `split at h` over the do-block's match tower survived four attempts | abandoned, and the missing coverage is stated rather than papered over |
| cost | ~1 session | ~1 session | on budget |

**The finding, in one line.** `hcd` - the hypothesis that `decodeCalldata` yields a given
message list, carried by every one of the ten specs - was satisfiable or not depending on a
layout nothing pinned. `Surface.hProofLayout` now pins it, and two new theorems prove the
converse: break either guard and no calldata decodes at all, so all ten specs become true
because nothing decodes. The `*_faithful` obligation is exhibited at the deployment's own
layout for the first time: 72 slots, a 2640-byte compressed stream, a 4484-byte calldata -
the artifact's own numbers - and the decoder reads back what the encoder wrote.

**Mechanism worth keeping.** Two of the three bad annotations were *bundling* errors: a name was
listed beside neighbours and inherited their reason without being read. A sweep that matches
names cannot see that; only re-deriving each reason per name can. The standing instruction to
re-verify recorded premises now has a second datum, and both times the false premise was in
the direction that made a spec easier, not harder.

### R13 - round 145, after P-MC-CALLDATA. Register 52, and the vacuity class is closed.

- **`hcd` satisfiability is now a THEOREM** at the deployment layout (4484 bytes, 72 slots, real
  codec). The ten specs are not true because nothing decodes. P-RESTORE3 opened the question; this
  closes it.
- **The 18th error of kind: a recorded BLOCKER was a tactic failure.** P-RESTORE3 logged
  `proofLen_eq_repackedLen` as blocked because "the do-block match tower defeated split at h after
  four attempts." It was a missing four-line lemma. Same class as R-65 and R11 - a confident
  recorded reason that did not hold. **New rule: record blockers as "I could not" rather than "it
  cannot"** - a recorded blocker stops the next agent from trying.
- **M-C's calldata tranche re-cuts**: 4 of 7 proved, and the last 3 are gated behind
  `Obligations.readScheduleAgrees` (stage 6), not behind more calldata work. The dependency ran the
  OTHER way from what the plan assumed - `Accumulator` has zero mentions of `decodeCalldata` and
  `Partials` only takes `hcd` as a hypothesis.
- **A statement had drifted weaker and was restored** (`calldata_canonical`'s extra `hend` binder).
  The authority document contradicts itself between section H and the index row. **Ruled: section H
  wins** by the standing rule, and the merits agree since `hend` is derivable.
- **Four new elaborator facts** the wall list did not name: `rw` cannot cross a match binder without
  `dsimp` first; the `rfl` TACTIC uses reducible transparency where term-mode `rfl` uses default;
  `Midfall.Bytes.empty` vs `ByteArray.empty` are defeq but block `rw`; `rcases` Option patterns are
  `(none | some)`, not source order.

**M8 is now being built per Fable's plan (D-P38), not assumed.** Revised M8: **6-12 sessions**.
**Register: 52.** M-C remaining: Accumulator 12, Qvm+QvmFold 9, calldata residue 3 (behind stage 6).
### R14 - round 147, after P-M8-IRCHECK. Fable's checker is built and sound - and its relation is too narrow.

- **`IRCheck.lean` landed: 839 lines, 19 theorems, zero sorries**, with `irCheck_sound` proving
  Fable's stated `ObsEquiv` conclusion **unchanged**. Both section 7 deliverables now exist.
- **The 19th recorded-blocker-was-wrong**: the brief asserted `ObsEquiv` needs
  `dialect_deterministic`. It does not — `ObsEquiv` is existence-to-existence in both directions, so
  a per-run matching discharges the forall. **Second time in this tree.** The agent accepted its own
  brief's premise for an hour before re-measuring it.
- **The substitution guards measured out as independent**, not one guard with a consequence: dropping
  table membership alone leaves the build GREEN, and dropping value-preservation alone also leaves it
  GREEN. Only dropping both restores the blindness.
- **`ir_refines` is NOT provable, and the reason is a limit in Fable's spec, not our implementation.**
  The artifact cannot satisfy alpha-equivalence: solc duplicates every binding through a fresh
  temporary and routes every abort through **declared helpers where the model inlines**. **An
  inlining is a simulation, not a rename.** `artifact_alpha_self = TRUE` proves the matcher is not
  broken.

**M8 re-split from measurement: 1-2 (alpha-transport) + 2-4 (run leg) + 3-6 (render-to-artifact body
equality).** D-P38's 6-12 stands, but the third item is now the dominant cost and is **bigger than
M8's own file** — it is M3's golden equality lifted to the whole contract.

**`M8-SCOPE`'s verdict refined, not overturned:** `ir_refines` is FALSE of the placeholder,
UNPROVABLE-BUT-NOT-FALSE of the sound checker, and provable-in-shape only after transport + body
equality.

**Register: 52. Both Fable-named M8 files exist.** The next question is a spec question, not a
coding question.
### R15 - round 150, after P-MC-ACC. Register 52 -> 44, and both named blockers were false.

**Eight of the twelve Accumulator holes closed: MSMKZG.eval_scale, MSMKZG.eval_addMsm,
batched_complete, batched_atMostOneRoot, dualMsm_check_iff_contract,
exists_zmod_smul_generator, contractRefAcceptsAcc_none, contractRef_acc_complete.** The four
decodeAcc round-trip holes (decodeAcc_injective, decodeAcc_encode, decodeAcc_encode_noNeg,
decodeAcc_encode_pointPair) are untouched and still registered.

**The statement audit, which is what this package was told to do first.** All twelve implemented
statements were read against their sketch in P-SE-semantic-equivalence.md section F (904-1091)
BEFORE being proved. **Zero needed restoration: eight are verbatim modulo the recorded
List.Sorted -> namesAscending substitution and the generator/Exec encoding bridge, and the four
decodeAcc ones carry the R-25/R-26 repairs that were already made and already recorded** (the
accWords projection, the .pointAndScalar restriction, and the hfb : fb.size = 0 hypothesis the
sketch lacked). So the count this package reports is **8 provable as stated, 0 restored, 4 not
attempted** - and the fourth consecutive package to find drift found none here. That is a
finding, not an absence of checking: the audit is in P-SE-statements.md under P-MC-ACC.

**Both claimed blockers were measured and both were FALSE.**

- "The decodeAcc family is blocked on the -s elaboration" (plan line 112, index line 351).
  #check @Midfall.Halo2.decodeAcc resolves and the module builds; the note predates the file ever
  being built. **The real cost is byte-level, not elaboration**: the four holes need
  loadAccPoint_flag0/1, decodeAccCoord_inj, encodeAccCoordWords_packingOk and the natToBytesBE
  16-48-16-48 frame lemmas, none of which exist. Twenty-first case of a recorded "it cannot" that
  was an "I could not".
- "dualMsm_check_iff_contract needs the run leg." **It does not.** The lift is dualMsm_check_eq
  (decideBool plus the toMul/ofMul identity transport) plus linearity in the G2 slot (map_neg)
  plus the two inverse pins; it is 14 lines and never mentions a run, an execution or a memory
  frame. The docstring's own reading (P3's, against P2's heavier one) was right and was provable
  without the prerequisite everyone inherited.

**What the eight proofs actually cost** was not the mathematics but three transport layers the
tree had never needed: (i) gsmul is Additive.toMul (s • Additive.ofMul Q) while msmSpecific folds
a multiplicative product, and Mathlib's Additive.ofMul_mul / toMul_nsmul family is NOT in the
built surface, so seven gsmul lemmas are proved from add_smul / smul_add / smul_smul plus a rfl;
(ii) MSMKZG.eval's [1] shortcut had to be proved a no-op (eval_eq_msmSpecific) before either eval
lemma could be stated in one piece; (iii) the Bool checks had to be turned into their Props
(dualMsm_check_eq, kzgAcc_check_eq, batchedCheck_eq) once instead of four times.

**Two tactic findings for the wall list.** (1) refine batched_complete ... _ with the batching
scalar as the last positional argument times out at 200k heartbeats whnf-ing batchedCheck;
apply batched_complete with the three premises as separate goals closes in milliseconds. Same
statement, same data: **positional metavariable synthesis in a deep application is the wall, not
the lemma.** (2) A section variable is auto-included only when the STATEMENT mentions it: an
exhibit whose statement does not name P cannot use P.g1 in its proof, which reads as "unknown
identifier" and cost a cycle.

**D-P23: four of the eight claims have both halves as theorems; four do not, and the limit is
stated in the file.** eval_scale, eval_addMsm, exists_zmod_smul_generator and the
contractRefAcceptsAcc_none word-gate each have a witness and a falsification
(eval_scale_witness / eval_scale_falsifies, eval_addMsm_witness / eval_addMsm_falsifies,
exists_zmod_smul_witness / exists_zmod_smul_needs_nontrivial, instOfWords_witness /
instOfWords_falsifies). **No witness/falsification pair is claimed for dualMsm_check_iff_contract,
batched_complete, batched_atMostOneRoot or contractRef_acc_complete**: the exhibits were drafted
(empty DualMSM, KzgAcc.trivial, params with one inverse pin broken) and each needs a chain of
delta+iota reductions of constructor applications that this session ran out of room to finish. The
drafts are not in the file, and the reason they are not left as comments is the standing rule that
a comment is not a proof. contractRef_acc_complete additionally cannot have its hypothesis bundle
witnessed in this file at all: a VerifierEnv exhibit lives under Instances/, which D-P17 forbids
here.

**Register: 44** (from 52), regenerated with scripts/gen_sorry.sh, three-way agreement with
scripts/sorries.sh and checks.sh verified. The four surviving Accumulator pins did not move (all
insertions were below line 339), so no comment-only line-shift was incurred.

### R18 - round 172, after P-RUNSHELL. The fourth refutation, and it hits the real artifact.

**`ir_refines` is REFUTED — not at our model, but at solc's actual imported output.**
`ir_refines_refuted_at_the_imported_artifact` refutes the exact shape `ImportedIR.lean:355` states as
an unproved `example : Prop` that stage 6 was meant to discharge. Kernel-checked, no `native_decide`,
no `sorryAx`. **M8's bridge is false for solc's output, not just for our model of it.**

| claim | believed | measured |
|---|---|---|
| the frame difference blocks ir_refines | R-66's crux | **NO** — the emitted program is frame-insensitive |
| curveSurface can discharge LoweringCorrect | assumed since P-LOWEQ | **NO** — RunShell has no runs at all |
| fix it by populating bindLocals | the obvious repair | **INSUFFICIENT** — 6 of 8 helpers read names no arm-level block can bind |
| sha256sum is missing on this host | reported by the package | **FALSE** — /sbin/sha256sum exists; a PATH artefact |
| gen_sorry.sh is reliable | assumed | **NO** — it truncates two declaration columns by one char |

**Why the refutation is strong rather than an artefact:** the package ruled out the easy explanations
instead of assuming them. The head guard is proved to PASS and a run of head-guard-then-revert from
the same frame is exhibited; a derivation of extcodesize(vk) is exhibited once vk IS bound. So the
emptiness is the binding — not the builtin, not the frame, not the program class.

**The structural fact that kills the easy fix: a Yul function is not a closure.** Step.callOk binds
params plus zeroed rets only, and six of the eight emitted helpers read names their own signature
cannot supply. Binding all 61 free names to zero is STILL STUCK — the gate passes and it dies inside
a helper. **No legal value of bindLocals closes the program.**

**Consequence for this ledger's own history.** This is the fourth headline statement found false or
vacuous as written: Holds.g1Decodes, Inv_mono, ir_refines-via-irCheck, and now ir_refines via the open
arm. **Three of the four were in Fable's plan, not in my transcription of it.** The pattern is not
carelessness — it is that a statement about a FRAGMENT treated as a PROGRAM looks fine until someone
actually runs it.

**Register: 41. `lowering_equivalence` remains proved, and is now known vacuous at every Surface in
the tree.** That is not a regression — a vacuous theorem you know is vacuous is worth more than a
proved one you believe. But the next step is a **design decision, not a proof**: whether `RunShell`
stays the right-hand side of `ir_refines` at all.

**Cost re-estimate:** the emitter change — inline contract-level constants as solc does — is a **Rust
change**, outside current confinement. The Lean alternative is a spec-level closure transform plus
restating the `shell_unfolds` pin. **Neither is inside the 10–16 session figure**, which assumed the
curve Surface could discharge the bundle.
### R19 - round 175, after P-QVM. Fifth refuted statement, one restoration, register 40.

| claim | believed | measured |
|---|---|---|
| `identityCorrespondence_of_bridge` is a proof gap | listed as a hole | **FALSE AS WRITTEN** — hypotheses pin `exprs`' first projection, conclusion needs the second |
| `qvm_validated_noBoundsFault` was as sketched | committed for 5 packages | **weaker than the sketch** — excluded `readPastEnd` at one index, not all |
| `builder_segments_total` is the most self-contained | my brief's ordering | **wrong** — an interpreter-totality claim as hard as the archetype |
| `shellConsts_matches_artifact_ok` can be a `decide` theorem | my brief | **IMPOSSIBLE** — `splitOn` is `@[extern]` C++; `FrameWalk.lean:121-137` already said so |
| the Qvm holes depend on `evaluatorRuntime` | plausible | **NO** — zero occurrences in either file; that gap blocks `qvm_yul_refines` only |

**The 5th refuted headline statement, and the restoration that took five packages.**
`qvm_validated_noBoundsFault` had been committed **weaker than its sketch** — excluding `readPastEnd`
only at `exprEnd` where the sketch excludes every `readPastEnd`, and the narrowing was **asymmetric and
silent** (the second conjunct was already universal). It survived because **each package assumed the
weakening was someone else's deliberate choice.** Restored to sketch strength, left open there, with
the missing machinery named so it cannot be re-weakened by accident.

**Third false premise in an orchestrator brief this session** — after `dialect_deterministic` and the
`Common/GSMul.lean` path. The `decide` conversion of a decorative pin is impossible, and the tree
**already recorded why**. The package reported it blocked rather than substituting `native_decide`,
which would have added compiler trust the same file header refuses.

> **My briefs are not authoritative and must not be treated as such.** Three of them carried a wrong
> premise this session; the fix each time was measurement, not deference.

**Non-vacuity done properly:** none of the nine is vacuous, and for the archetype the **smallest witness
was computed** — a 7-byte segment with zero constants that evaluates to exactly the reference's field
element. So `qvm_compile_correct_identity` is satisfiable **and true at its smallest instance**: a
proof gap, not a statement gap.

**Tooling win:** `gen_sorry.sh`'s truncation was BSD `cut -c` counting **bytes** under a non-UTF-8
`LC_CTYPE`. Fixed with a codepoint slice, verified byte-identical under three locales. A register that
rewrites itself wrongly would eventually hide a real hole.

**Rate: 1 sorry closed** — bottom of the measured 1–3 band. But 1 refutation + 1 restoration + 1
tooling fix is the real yield, and the refutation saves a package from driving at a false statement.

**Register: 40** (from 64). Six Qvm holes now share one named gap: per-opcode agreement between
`evalQuotientIdentityStep.consumed` and the validator's `quotientOpLen` across ~25 arms, plus a loop
induction over the fuel-bounded walks.
### R20 - round 177, after P-SCHED. The fixture could not decode; fixing it refuted a field.

| claim | believed | measured |
|---|---|---|
| the deployment fixture was sound | 5 packages of green gates | **`fxCs` had `numAdviceColumns := 1` with `adviceColumnPhase := []` — `decodeRust` returned `none` on all 63 buffers** |
| `readScheduleAgrees` unblocks 3 holes (my brief) | stated as fact | **FALSE** — all three take it as a binder or name it in prose |
| the field is a proof gap | assumed | **vacuous before the repair, FALSE after** — 8 decoded slots vs the layout's 72 |
| the fingerprint gate covers every `LoweringCorrect` field | its own claim | **FALSE** — deleting `readScheduleAgrees` entirely leaves all gates green |
| my cancellation of the counterexample Surface | sound call | **right for the wrong reason** — the fixture repair produced a stronger counterexample |

**The pattern that keeps repeating: a fixture tuned until a check passes, rather than a check run on
the fixture.** The deployment fixture verified when handed messages, so every gate stayed green — but
**nothing had ever decoded a proof from bytes at it.** The byte-level path was untested, and the field
that depends on it was satisfiable *only because* the decode always faulted.

**Sixth refuted headline statement** — and the first refuted **at the deployment**, not on a constructed
example. `readScheduleAgrees_refuted_at_deployment` is a theorem. `scatterIndexed_hole_is_a_fault`
carries **no axioms at all**.

**A new and serious gate blind spot.** `P8`: deleting a whole `LoweringCorrect` field leaves the build
and all three text gates green, while the fingerprint gate still prints "9 LoweringCorrect fields".
**`P7`**: gutting a field's conclusion to a self-equality also passes everything. So the claim that
all 48 obligation fields are gate-tracked is **not true**, and the count the gate prints is a literal,
not a derived fact.

**Five false premises in orchestrator briefs this session** — `dialect_deterministic`, the
`Common/GSMul.lean` path, the impossible `decide` conversion, `readScheduleAgrees` unblocking three
holes, and a register target that was impossible by construction. **The fix every single time was the
instruction to verify rather than inherit.** Briefs must keep being treated as hypotheses.

**Consequence for every later package:** the repair changes the fixture's constraint system, hence the
VK hash and every derived challenge stream. 1334 KATs and 30 pins still pass, so nothing tracked
depended on the broken value — but conformance replays at this vk now have a **live schedule** where
they previously had a fault. **That is where real byte-level decode work starts**, and where a genuine
vk/layout mismatch becomes visible for the first time.

**Register: 40, unchanged — by the nature of the finding, not a shortfall.**
### R21 - round 179, after P-GATEINTEG. 28 obligation fields had no pin.

| claim | believed | measured |
|---|---|---|
| all 48 obligation fields are gate-tracked (my brief) | asserted | **28 had no pin**; 48 is not derivable — the structures carry 26 |
| the gate printed 9 LoweringCorrect fields | 9 fields | **8 fields + 1 theorem** |
| PartialSpecs was covered | assumed | **16 of 16 fields unpinned** — no name appeared anywhere under scripts/ |
| the triviality rule's scope was the gap | my brief | **its INPUT was** — it only saw fields a human had listed |
| EnvAgrees clauses are build-guarded | assumed | **2 of 9 hollow to True and stay green** — discharged by decide, and decide proves True |

**The structural reason this mattered:** LoweringCorrect.partials carries all 16 PartialSpecs
obligations in one field, and **nothing in the tree constructs a term of either structure** — so the
build cannot guard them and only a text gate can. Seven checklist fields have **no theorem twin at
all**, existing only as a field with nothing duplicating their content into a theorem text.

**The fix derived rather than asserted**: the gate now parses the structures and enforces coverage,
no-dead-names, count-agreement and per-field non-triviality. Fragments 245 to 374. KAT totals asserted
statically, so a deleted gate reddens in about one second instead of eight minutes.

**Rule (a) reddened on 28 real fields. The package wrote content pins for them rather than weakening
the rule** — must and must_not fragments, each shown to redden on its own gutting. That is the correct
direction for a fix and the opposite of what a package under pressure would do.

**Sixth correction to my own briefs this session** — the 48-field number was never computed from
anything, which is exactly the error the standing instruction exists to catch.

**Register: 40. Gate integrity is materially better than it was an hour ago.**
### R22 - round 181, after P-QVMARMS. The shared gap was a component, and I sized it from assertion again.

| claim | believed (my brief) | measured |
|---|---|---|
| one shared gap blocks six Qvm holes | the whole blocker | **a component of five, ~5-15% each**; only `qvm_validated_noBoundsFault` is mostly it (~40%) |
| "mechanical but large, ~25 arms plus a loop induction" | the cost | **the arms are mechanical and landed in one session**; the emitter induction the same holes need is ~40 panic sites and 4 peephole cases - a separate package |
| per-opcode `consumed` vs `quotientOpLen` agreement | assumed to be where a disagreement might hide | **holds on all 26 identity arms**, 31 fixtures and all 256 opcode bytes; the only asymmetry is the five stream opcodes, which are a DOMAIN boundary, not a drift |
| the agreement is what `noBoundsFault` needs | stated by P-QVM | **incomplete**: stride agreement is one of two per-arm facts. The other is "every operand READ fits inside the stride", a second 22-arm pass nothing in section 7 gives |
| `builder_segments_total` is not self-contained | P-QVM already corrected this | confirmed: totality over EVERY fault class, not just the two bounds classes |
| the loop induction is one lemma | assumed | **two**: fuel adequacy (`evalQuotientIdentityLoop_fuelNeverBinds`, landed) and cursor correspondence (not landed) |

**Eighth correction to orchestrator briefs this session**, and the same error class as R21's 48:
a blocker's SIZE asserted without measuring it. The differential-enumeration pass cost about
forty minutes and answered the size question before any proof was attempted - see docs/REVIEW.md
R-70 for the technique writeup.

**LANDED**: `Qvm.lean` section 7 - the enumeration table, 3 arm-set defs +
`arms_enumeration_is_exhaustive` (22+4+5 = the 31 table opcodes, disjoint, by `decide`), 5
shape-helper length lemmas, the fold induction `foldRangeIdxM_ok_advance` (this is the plan's
owed `foldRangeIdxM_induction`, P8 row), `evalQuotientIdentityStep_consumed_agrees` over 22
arms in one case split, `streamArms_error`, the fuel-adequacy loop induction, 2 D-P23 witness
theorems, and 2 differential gates re-running the enumeration inside the build.

**Register: 40, unchanged. No hole closed.** KAT pins moved 1334 to 1336 deliberately, for the
two differential gates.

**NEXT, if the six are still wanted**: the emitter value-semantics induction over
`identityExpr` is the real cost of five of them and needs its own brief with the per-hole
fractions above in it. `qvm_validated_noBoundsFault` is the only one reachable without it, and
it needs the read-offset enumeration first - differentially, before inducting.

### R23 - round 185, after P-READOFF. Read bound proved; the audit rule covers 72.5% of the register.

| claim | believed | measured |
|---|---|---|
| the hole needs one more per-arm fact (my brief) | asserted | **needs a THIRD, unnamed** - const-slot correspondence. Now ~55% |
| 2 holes have no sketch | my brief | **11 of 40** - understated by 5.5x |
| the read bound is the binding constraint | my brief | **no** - the const-slot correspondence is; the read bound was the easy half |
| lake build green means the gates passed | assumed by every package | **FALSE** - a false eval-expect-true is an info line. **KAT verdicts are enforced by kat_gate.py, not the compiler** |
| the four dynamic arms differ in the property | assumed | **no** - they differ in PROOF SHAPE: stride is a function of bytes read mid-instruction |

**The audit-domain finding changes how I must brief.** The standing rule - audit every proof statement
against the sketches in A-R - has a domain of **29 of 40**. A package that runs it and reports "all
statements audited" has checked **72.5%** and said **100%**. From now on briefs must say: **audit
against A-R where a sketch exists; list the ones that have none.**

**The lake build finding is architectural and was invisible for 180 turns.** A false
`eval ... -- expect true` is an info line, not a build error, so **lake build green has never meant the
KAT gates passed.** Every perturbation in this project's history that concluded "the gate is green"
from `lake build` alone may have been reading a false verdict as a pass. The falsification-deletion
gap - 34 measurements - is partly a symptom of this.

**A near-miss that vindicates the growth rule:** the read tool silently truncated a 1967-line file and
a splice dropped **612 lines**. Assert-the-file-grew caught it - the file SHRANK. **New rule for all
packages and for the orchestrator: do not round-trip files over ~1500 lines through the read tool;**
use direct file access. This hazard applies to me as much as to agents.

**Eighth false premise in my briefs this session.** Consistent pattern: I assert a blocker's size or a
rule's coverage without deriving it. Every correction came from the instruction to measure.

**Register: 40 unchanged - the read fact landed, the hole did not close. 24 of 26 arms proved.**
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


### R24 - round 186, after P-DET. The named blocker was true, and the brief's guess about it was the only wrong thing.

| claim made | before | actual | verdict |
|---|---|---|---|
| `dialect_deterministic` is probably FALSE as registered (gas nondeterministic, `ExternalGas` arbitrary) | brief's prediction, stated as the thing to check first | **TRUE as registered, and proved.** The statement already assumes `hc : c.Functional` and `hg : g.Functional`; under those the `gas` case has one answer per state and the call family one response per (request, pre-state) pair | **error of kind - a premise about the semantics reasoned about without reading the signature that carries it** |
| the honest target is view-level determinism given fixed `c` and `g`, so the registered hole needs a deviation entry | predicted restatement | **no restatement needed.** `Run.det` / `RunCommitted.det` already were that statement; they were corollaries of a hole and are now corollaries of a theorem | premise wrong, outcome better |
| "cases on Op is 77 constructors" (the hole's own docstring) | 77 | **87** (`EVMOp.lean:41-71`); 80 discharged by one lemma, 7 need arity splits | wrong number, harmless direction |
| the hole is the single thing between the open field and a settled answer | stated in the brief | **true for the route taken** - `RunCommitted.det` really does inherit it - and the refutation became unconditional the moment it closed | held |
| third citation of this hole as a prerequisite | two prior citations had both been false | **the third was real**, which is why the honest answer is not "fake again" but "real, and provable" | held |
| cost | one package | one package: ~40 min to the first green proof of the hole, the rest to the unconditional refutation, D-P42, the gates and the register | on budget |

**The lesson, for the next brief.** Before predicting whether a registered statement is true, read what
it ASSUMES. Both errors in this package - mine and the brief's - were the same shape: a fact about the
semantics (gas is nondeterministic) applied to a statement that had already hypothesized it away. The
project's standing instruction to re-verify recorded premises cuts both ways: it also applies to
premises a brief brings with it.

**Register movement.** 40 -> 39, the first close since P-SPEC1 and the third of this class (a named
hole that turned out to be true and merely unproved). KAT pins moved 1346 -> 1348 and 97 -> 98 for the
two new interpreter gates in `RunShellInhabited.lean`.

### R25 - round 187, after P-RUNLEG. The falsifiability test fired, and it cut both ways.

| claim made | before | actual | verdict |
|---|---|---|---|
| D-P42's disagreement might be an artefact of the EMPTY calldata (the attack D-P42 itself specified) | the live falsifier, item (i) | **NO on the conclusion, YES on the mechanism.** Routed input still refutes 'ir_refines' at 'curveSurface' ('ir_refines_refuted_at_curveSurface_routed'), but not by the entry-path guard D-P42 named: 'wrap curveSurface' has NO run at all on routed input ('wrap_routed_uninhabited'), because 'armBody' is the un-inlined fragment | **conclusion survives, mechanism wrong** - the rarest outcome, and the one the falsifiability paragraph existed to produce |
| restating 'ir_refines' RHS to 'wrap' (F2) is "the only consistent reading" | recorded as unavoidable | **does not repair anything at 'curveSurface'.** It swaps a side that disagrees for a side that is empty. The repair is to close the model's arm (D-P43), not to move the RHS | **the orchestrator's own recommendation was wrong**, and the control experiment is what showed it |
| the entry path is what separates 'RunShell' from 'wrap' | D-P42's stated mechanism | **on routed input, the entry path separates nothing**: dispatcher-over-inlined-arm and bare-inlined-arm give the same four-byte revert ('control_of_arm_block_run' + 'routed_comparison_ok'). The prologue, size test, switch, callvalue guard and thirteen ABI tests contribute no halt | held only at the unroutable input |
| 'ir_refines_refuted_at_the_imported_artifact' could not be re-established without the routed run | P-INLINE's retraction: "its only route was shell emptiness" | **re-established at the UNROUTABLE input**, cheaply: 'irSt0 = stF' and 'irSurface.shell.codeBlock = armInlined' are both 'rfl', so D-P39's shell derivation transplants and 'ImportedIR.importedRuntime_runs' supplies the artifact side for every 'c' and 'g' | retraction resolved; the premise for it was stale |
| 'ShellModel.dispatcherAccepts' + 'cdWellFormed' + 'armPrefix_passes' is enough to build the routed exhibit | brief's plan | **true, and it cost no new model work**: 'cdR' is 'cdWellFormed' as 'Bytes', acceptance is thirteen 'rfl's at the deployment frame, and 'bytesTake cdR 0 4 = some fnSigVerifyProof' is 'rfl' | held |
| the wrap non-inhabitation inversion would be the expensive part | brief's estimate, implicitly | **true but tractable**: the sixteen-statement entry path comes off a run in one line via 'stmts_append_inv', because 'Bridge.dialect_deterministic' (P-DET) makes 'Step.det' available to PIN each forward step. About 200 lines, one afternoon | held, and P-DET is why |
| cost | one package | one package: ~55 min to the decisive measurement, the rest to the inversion, the artifact re-establishment, the gates and the docs | on budget |

**The lesson, for the next brief.** A recorded mechanism and a recorded conclusion are different claims, and a test that confirms the conclusion while falsifying the mechanism is worth having - it is the difference between "the field is refuted" (still true) and "restating the RHS fixes it" (false). Before recommending a repair, ask what the repaired statement is inhabited BY.

**Register movement.** None: 39 tracked sorries before and after, no statement edited, no hole closed or opened. KAT pins moved 1348 -> 1352 and 98 -> 99 for the four new interpreter gates in 'RunLegRouted.lean'. Two gap defs change status in the report rather than in the tree: 'gap_runLeg_unexhibited' is now EXHIBITED on the shell side and refuted-empty on the model side, and 'ir_refines_refuted_at_the_imported_artifact' is re-established.

## V2 ledger — cards Q0.x onward (fresh; v1 rows above are history)

**Progress measure per EXECUTION-V2:** the root's cone count and block contracts integrated. Register,
gate and KAT counts are **not** progress. Cone counts are unavailable until Q0.2 lands the tool.

| card | box | actual | cone delta | outcome | note |
|---|---|---|---|---|---|
| T0.1–T0.4 cut-over | — | ~40 min | n/a | done | v1 tagged `formal/v1-final` at `a680b5c`; D-V2 recorded as **D-P44**, not the expected D-P43, because D-P43 had been consumed by an executed v1 repair |
| Q0.1 land V2 files | 1.5 h | ~26 min subagent + orchestrator gate | n/a (no cone tool) | **DONE** | 874 insertions, 0 deletions; three files byte-identical; register 39→45 with exactly the six predicted names; **`LegacyVacuity` has zero sorries — the three v1 refutations are proved**, two on `[propext, Classical.choice, Quot.sound]` and `stuck_satisfies_every_post` on `[propext]` alone |

**False premises found in V2 so far (running total, for the C.5 calibration rule):**

- Q0.1 predicted `check_duplicate_facts.py` would redden on `Render`'s fields and pre-authorised a
  follow-up for it. It stayed green. Harmless, but it is a card premise that did not survive contact.
- PLAN-V2 §2 assumed D-P43 was free. It was not.

**Cost observation for later cards:** a KAT card costs two full KAT passes (~20 min) because the card
requires `kat_gate.py` once *and* `checks.sh` once, and `checks.sh` runs `kat_gate.py`. Worth
collapsing in a later card; **sample size 1**, so not yet a conclusion.
| Q0.2 cut V2 off retired modules + cone tool | 2 h | ~35 min subagent + orchestrator gate | **baseline set: cone_sorries 1 and 1**; V2 closure 0 of 14 AVOID modules (was 6) | **DONE** | all six NEEDS line refs exact on re-check; six copied ranges verified verbatim by the orchestrator; no false premise in the card |

**Cone baseline established at Q0.2** — the first measurable progress number V2 has had. Both roots sit
at `cone_sorries: 1` (the root alone). Later cards must move this number; a card that does not change it
has not progressed the root.

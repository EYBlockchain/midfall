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

### M-B — the 12 `Partials` specs — **NOT STARTED**

Needs M-A (`Holds`) + Bridge step lemmas (MF-4 **done**). **Estimate: 4–6 sessions** at ~2–3
specs/session, since `finalPairing_spec`'s dominant cost is already closed. **Confidence: low**
— no spec has been proved yet, so this rate is entirely extrapolated.

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
| M-B | 4–6 | extrapolated |
| M-C | 8–14 | bulk by count |
| M-D | 2–5 | widest variance |
| M-E | 1–2 | transport |
| **Total to landmark** | **18–31** | **revised up from 17–27** |

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

## What would most improve this ledger

1. **One `Partials` spec proved.** M-B's rate is pure extrapolation; one datum would tighten it
   more than anything else here.
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


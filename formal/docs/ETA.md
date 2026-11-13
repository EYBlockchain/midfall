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
## What would most improve this ledger

1. **One `Partials` spec proved.** M-B's rate is pure extrapolation; one datum would tighten it
   more than anything else here.
2. **P-MODEXP's outcome.** If the Fermat reading holds, M-A's last item is cheap and the
   landmark moves up; if not, the agreement theorem is the first genuinely hard item in M-A.
3. **A sorry-per-session floor rather than a mean** — the 0-output sessions are what make the
   naive projection wrong.

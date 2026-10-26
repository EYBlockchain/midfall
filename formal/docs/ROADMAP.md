# Midfall formal - living roadmap

Maintained by the orchestrator. Supersedes nothing: PLAN.md is normative for *what* is
claimed; this file tracks *where we are, what is next, and how long it is taking*, with
the measurements that justify the estimates.

Updated round 10, 2026-10-25.

## Velocity, measured

From commit timestamps, not from estimates:

| package | Rust lines | wall clock | lines/h |
|---|---:|---|---:|
| P-01 AST + printer + golden harness | ~1,500 | ~1.3 h | ~1,150 |
| P-02 Models + Templates | 1,505 | ~1.5 h | ~1,000 |
| P-03 Layout (a-d) | 2,852 | 4.7 h | ~610 |
| P-04 Protocol | 1,252 | ~1.0 h | ~1,250 |
| P-05 Abi + Encoding | 1,486 | ~1.6 h | ~930 |

Working number: **~1,000 Rust lines per agent-hour** for porting. Review overhead,
measured from R-38 and R-40, is **1-2 h per package** for a thorough adversarial review
plus its fixes (R-40 was 7 findings over ~2 h). A reviewed package therefore costs about
1.5x its port cost, and reviews are serial with porting because only one agent may run
at a time.

## Status board

| milestone | state | note |
|---|---|---|
| M0 baseline frozen | **open** | not tagged; see blockers |
| M1 skeleton + inventory | done | Statements.lean compiles with 4 tracked sorries |
| M0 baseline frozen | **open** | not tagged; see blockers |
| M1 skeleton + inventory | done | Statements.lean compiles with 4 tracked sorries |
| M2 L0 port | port done, **conformance not started** | the exporter does not exist |
| M3 generator port | P-01..P-05 done (~5,900 Lean lines), P-05 under review | ~24,000 Rust lines remain |
| M4 yul-semantics | D-P10 decided; dialect gap found (D-P15) | needs `memoryguard`, `setimmutable` |
| M5-M7 lowering | not started | gated on M3 |
| M8 IR validation | **decision taken** (D-P15) | gated on the dialect addition |
| M9 security | **decision taken** (D-P14) | gated on security.tex x1/x4 re-derivation |
| M10 Direct | not started | `direct/` now sits inside M3 (PLAN 14.7) |
| M11 deployment | R-44 gives a bytecode oracle | R-36 staleness still open |

| M5-M7 lowering | **new blocker found (R-47)** | Lagrange lemmas need a primitive-root hypothesis the tree does not carry |

## Generator port progress, measured

| as of | Lean lines | gates | modules | Rust ported | Rust left |
|---|---:|---:|---:|---:|---:|
| after P-04 (Protocol) | ~19,000 | ~330 | 51 | ~6,300 | ~25,200 |
| after P-06 (Api) | ~24,000 | ~400 | 55 | ~8,600 | ~22,900 |
| after P-08 (Vk) | ~38,000 | ~511 | 58 | ~10,800 | ~20,700 |
| **now (after P-09d)** | **42,691** | **597** | **60** | **~13,100** | **~17,500** |

Rust-left counts `vm/mod.rs` whole, but roughly 2,000 of its 4,336 lines are now ported
(vocabulary, builder, certifier), so the true remainder is nearer **15,000 lines plus the
4,324 Askama templates**. At the measured ~1,000 lines/agent-hour that is **~19-20 hours
of chained agent time** for the rest of M3, before any of M4-M11.

## Port ETAs, with the arithmetic shown

**Superseded by PLAN 14.8 for scope.** After the M3 cut (disasm, quotient_listing,
direct/trace, diagnostics out; direct/{mod,emit,layout,validate} deferred to M10 with
`folds.rs` staying because `quotient.rs` imports its fold types), the remaining work is
~7,500 Rust lines plus 4,324 Askama template lines.

| pkg | Rust lines | est. h |
|---|---:|---:|
| P-09e validator *(in flight)* | ~1,050 | 2 |
| P-09f shape recognizers | ~600 | 1.2 |
| P-10 `quotient.rs` + `direct/folds.rs` (split x2) | 2,644 | 4.5 |
| P-09h `yul_emit.rs` | 1,176 | 2.3 |
| P-11 `plan` + `config` + `mod` | 721 | 1.5 |
| P-12 `calldata` + `builder` + `evm` | 1,316 | 2.6 |
| P-13 templates | 4,324 Askama | 6-12 |
| | | **~21-27** |

Plus ~4 h of orchestration overhead across 9 packages. **Working number: ~25 h of
chained agent time**, down from ~38 h. The wide band on P-13 is honest: it is the only
block with no line-by-line Rust counterpart, and 6 h is judgement rather than measurement.

### Superseded table (pre-cut)
The QVM block (P-09a..e) is the part that moved fastest per line, because each package
could reuse the last one's fixtures and gates rather than build them. It is also where
the most valuable findings came from: a real zero-guard bug in committed code (F-1,
now fixed), the `v3` seed tag being unpinned in the Rust, and D-P20's discovery that
`QVM.run`'s stated granularity does not exist in the reference.

P-07 (kzg) was stopped mid-write at 01:35 with 1,493 lines, 59 decls and **zero gates**,
truncated inside `computations` - a single ~1,000-line Rust function (kzg/mod.rs:930-1927)
- at about KZ:1576. It was never registered, so the tree stayed green. Recovery is scoped
in `plans/P-07R-kzg-recover.md` and running: finish `computations`, reproduce the tests
module as gates, and **audit the inherited lines rather than trusting them**, since their
author died before evidencing any of it and its header's completeness claim is false.

R-47 is the more important item of the two. `FieldConsts` carries no hypothesis that
`rootOfUnity` has order 2^s, so the Lagrange and telescoping lemmas M5-M7 are built on
have nothing to stand on; `Spec/Lemmas.lean` already had to defer the reduced-index
`rotate_omega` form for exactly this reason. Planned as `P-4a-roots.md`.
## Package log

| pkg | commit | Rust lines | Lean lines | gates | reviewed |
|---|---|---:|---:|---:|---|
| P-01 AST + printer + harness | 2648973, d7b788e | ~1,500 | ~1,224 | 37 | yes (R-38, R-39, R-40) |
| P-02 Models + Templates | 18d7c28 | 1,505 | 2,511 | 45 | yes (R-40, 7 findings) |
| P-03 Layout a-d | 0346390..4abe3f1 | 2,852 | 1,949 | 46 | yes (3c was the fix round) |
| P-04 Protocol | 8ae201f | 1,252 | 1,580 | 18 | **owed** (deferral window) |
| P-05 Abi + Encoding | d15f1c5 | 1,486 | 3,023 | 46 | **in flight** |
| P-06 api | - | 818 | - | - | planned |
| P-07 kzg | - | 2,226 | - | - | planned |

Two patterns worth noticing in that table. Lean lines per Rust line rose from ~0.8
(P-01) to ~2.0 (P-05), because the later modules carry more gate surface per ported
line - which is the review discipline being paid for in the port rather than after it.
And P-04 is the only substantial package with **no independent review**, because it
landed inside the deferral window; it is queued behind P-05 for a review pass and that
is a real debt, not a formality - R-31's evidence is that both surviving bugs lived in
exactly that situation.

| pkg | lines | port h | +review h |
|---|---:|---:|---:|
## Review boundary, as of round 12

Per-task adversarial review is off until the generator's **semantic-equivalence results**
are finished - not merely until the port completes. So the unreviewed span now covers
P-04 through P-14 and, on the current reading, M5-M8's theorems as well.

What that actually costs, stated plainly rather than glossed: a wrong *port* is caught
eventually by a golden diff or a conformance mismatch, and the project has demonstrated
that (R-20, R-30, R-32 were all found by cross-checks). A wrong *lemma* has no such
net - `lowering_equivalence` proved against a mis-stated `Inv k` contract will sit green
forever, because nothing outside it disagrees with it. The only mitigation available
while reviews are off is the one PLAN 12 names: author-run perturbation evidence on
every gate, and `#print axioms` on every theorem, with anything that cannot be evidenced
that way flagged rather than asserted.

This raises the value of the pulled-forward `finalPairing_spec`: it is the first
semantic-equivalence result, it is small, and it is the earliest point at which the proof
architecture can be shown to be capable of failing. It should be treated as the gate
that the review batch is waiting for, not as a convenience.

## P-09 split (round 12)

The QVM block is ~10,000 Rust lines and was the weakest estimate in the port table. It
is now five packages (P-09a reference interpreter, P-09b compiler, P-09c
certify+disasm, P-09d yul_emit, P-09e direct), planned in
`plans/P-09-quotient-vm.md`. The reason for the split is a finding, not caution:
`vm/reference.rs` is a **probabilistic certifier** - it samples a deterministic
challenge and compares the emitter against the reference evaluator with a
Schwartz-Zippel argument - and its own doc says the reference-interpreter-to-Yul leg is
covered only by conformance tests and a trace differential. So PLAN 9.5's
`qvm_yul_refines` has no counterpart in the Rust to mirror: it is a theorem we originate.
Planning M6 by analogy to "what the Rust does" would plan the wrong thing.

| P-06 api | 818 | 0.8 | 2.3 |
| P-07 kzg | 2,226 | 2.2 | 3.7 |
| P-08 vk | 654 | 0.7 | 2.2 |
| P-09 vm + direct (item 9) | ~10,000 | 10 | 11.5 |
| P-10 quotient | 2,147 | 2.1 | 3.6 |
| P-11 plan + config + mod | 721 | 0.7 | 2.2 |
| P-12 calldata + builder + evm | 1,316 | 1.3 | 2.8 |
| P-13 templates | 4,324 Askama | 4-9 | 5.5-10.5 |
| P-14 Tier-2 (diagnostics, artifacts, listing, disasm) | ~5,800 | 5.8 | 7.3 |
| | **~28,000** | **~28-33** | **~41-46** |

So: **port alone ~30 h, port plus per-package review ~44 h of serial agent time.**
Elapsed calendar time depends only on how continuously agents are chained; at near-24 h
operation that is ~2 days unreviewed, ~2 days reviewed - the review cost is real but it
buys the thing R-31 says will otherwise be found late, and it does not dominate.

Two honest caveats on those numbers. Item P-09 is 10,000 lines in one package and the
velocity table has no precedent that large; it should be split into P-09a (vm) and P-09b
(direct) before firing, and the split may not be linear in lines. And P-13 (templates)
is the only block with no line-by-line Rust counterpart, so its 4-9 h range is a
judgement, not a measurement.

## Proof milestones - deliberately unestimated

The only completed proof work is Phase 4a: three small algebra lemmas in a day
(Spec/Lemmas.lean is 143 lines). M5-M9 are a different order of magnitude and no
comparable theorem has been completed, so a number here would be invented. The first
real calibration point is `finalPairing_spec`, which lands immediately after the port.
That estimate will be written here when it is measured, not before.

## Blockers and decision gates

| # | item | state |
|---|---|---|
| 1 | solc 0.8.30 | **CLOSED** (R-42) - was installed and verified all along |
| 2 | R-22 truncated batching coefficients | **DECIDED** (D-P14) - keep truncation, re-derive x1/x4; gates M9 until security.tex has the section |
| 3 | R-42 IR artifact | **DECIDED** (D-P15) - via-ir text via generated `yul%` quotes; prerequisite: dialect needs `memoryguard` + `setimmutable` |
| 4 | R-36 stale Moonlight artifact | open; regeneration now feasible (SRS assets present, solc verified, R-44 reproduces the current pair) |
| 5 | M0 tag | open; G0 has not been re-run this session |
| 6 | Phase 3 conformance exporter | open; nothing exists, and it is the only thing that validates M2 |
| 7 | uncommitted `api.rs` (+57 lines, unused) | open; excluded from P-06 by reference hygiene |


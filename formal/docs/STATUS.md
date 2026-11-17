# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `1009658` (2026-11-17 01:25Z). v1 frozen at `formal/v1-final`.

**Plan:** `docs/plans/PLAN-V3.md` (D-P60; cut over by PL.0, tag `formal/v2-cutover`) · rules
`docs/plans/EXECUTION-V2.md` + PLAN-V3 §4 · cards `docs/plans/PLAN-V3-cards.md` · queue `docs/QUEUE.md`
(the V3 table at its top). PLAN-V2 is kept for its rules and its V2 cards.
Scope decision **D-P44**. `docs/PLAN.md` points at V2.

## ✅ PLAN-V3 ADOPTED AND CUT OVER — D-P60–D-P69 signed (2026-11-17, after `53bf8c1`); PL.0 done

An independent review and a revised plan are in `docs/plans/` (`REVIEW-V3.md`, `PLAN-V3.md`,
`PLAN-V3-cards.md`, evidence under `V3-evidence/`). **D-P60 is signed, so PLAN-V3 is the active plan**: `PLAN-V2.md`'s banner and §6 note and
`EXECUTION-V2.md`'s note now redirect to it, and the goal prompt is unchanged. **PL.0 is done**: the queue's V3
table is the order (105 rows), and every V2 card is marked. **Next: DG.0** (the KAT gate is red at the
tip), then the table's READY rows top-down. F.1 is recorded there as merged (`f588ba2`, cone 11 → 9).
**In force now:** D-P65 — the G1.1–G1.3 batch must carry the block-scope repair, or it does not
merge G1.2. Every decision's conditions are recorded in its `design.md` entry and are applied, not
chosen; an unmet condition stops its card. Records: `design.md` D-P60–D-P69; `docs/DECISIONS-PENDING.md` §12.

**TICKET M0.1 (probe, `252ea1d`; table landed in `docs/QUEUE.md` under M0.1):** the 7×4 block-frame
table was computed in ONE lean run and **the orchestrator re-ran it and reproduced every headline
number** (54 = 54 stmt sum; `batch_invert` the only looping helper; quotientLin 122/6572 tokens; pcs
empty at plan level). Route: `sliceOf (planViewOf poseidonPlanV2 poseidonModelVal
`poseidonConfig.accumulator) poseidonModelVal q` — `planViewOf` takes THREE explicit args.
**Shared cross-slice locals are exactly `{vk, r, success}`. `fail()` reverts, it does not set
`success := 0` — distinct requirement paths.** C.2 is briefed off the landed table, not off memory.

## ⚠ CONE MOVED UP: 5 → 11 (C.2, merged `9401f1a`) — skeleton-first cost, stated honestly

`lowering_equivalence_of_blocks` is now **derived from 7 named sorried lemmas + 11 proved transport
facts** (113-line body, no `sorry` tactic of its own). **But it still depends on `sorryAx`** — measured:
`[propext, sorryAx, Classical.choice, Quot.sound]`. So it is **conditional on seven OPEN obligations**,
not proved. Cone: `of_blocks` 1→7, **headline 5→11**, `end_to_end` 1→1. Register 47→53.
`cone_avoids` ok for all three roots. **A plan that only ever shows the cone falling is not
skeletonising anything** — but the number is worse today and must be reported that way.

## ⚠ NEW HUMAN DECISION — `Render.Rejects` cannot serve conjunct 3

**`Rejects` demands `SoundSide`, which the frozen third conjunct of `LoweringEquivalence` does not
carry — so conjunct 3's ¬LeanAccepts branch is unreachable from `hrej`.** Deleting `SoundSide` from
`Rejects` makes `rejects_of_not_accepts` a one-liner and **drops the cone by 1**. `Blocks.lean` §6 is
designated refinable by Q0.3, so this is within V2's rules — **but it changes what `Rejects` MEANS.**
The card correctly did not do it (authorisation was Frame/Clean fields only). **Choose: delete
`SoundSide` from `Rejects`, or let C.3 own it.**

**Second expressiveness finding (no decision needed, it is FP.0/T.1's job):** `BlockSound R
.traceReturn` admits `o = .normal ∧ Poisoned`, so the needed program-level post is **strictly stronger
than 7× `BlockSound`**. The missing fact is 'traceReturn reverts on `iszero(success)`' and **no
`Frame`/`Clean` field fixes it.**

**Requirements table:** landed in QUEUE.md under C.2 (84 lines), one row per lemma with statement,
composition step, and size estimate **with sample size**; two rows say 'no basis yet' rather than
inventing numbers. M0.1 caveats carried: 2 of 7 sequenced links are vacuous (pcs empty at plan level),
and `hB` includes quotientLin, which emits 122 of 6572 tokens.

## ⚠⚠ C.4 (merged `aee4f69`): `poseidonRender` is PROVABLY NOT Valid

**`theorem poseidonRender_notValid : ¬ poseidonRender.Valid` is PROVED** (PoseidonValid.lean:468,
verified by the orchestrator). **C.1's `poseidon_valid` sorry is not unfinished — it is IMPOSSIBLE at
this render.** Clause map at `poseidonRender` (11 clauses of `Render.Valid`, `Statements.lean:139`):
**4 PROVED / 6 REFUTED / 1 SORRY.** The card predicted 3 refuted; it is 6.

| clause | verdict | deciding value |
|---|---|---|
| circuitMeta | REFUTED | numEvals 27 vs 48 |
| layout | REFUTED | proofLen 1792 vs 4320 |
| invariants | REFUTED *(not predicted)* | `.error "PCS query schedule must end with linearization query"` |
| model | **SORRY (true but undischageable)** | two obstructions, see below |
| inputs | PROVED | k=6=domain.k |
| codegen | REFUTED *(not predicted)* | 3156 AST vs 10433 printed tokens; first diff idx 1333 = WP-G1 |
| closed | PROVED | mainClosed = true |
| slots | REFUTED *(not predicted)* | negLagranges reads 9 = 7 (pv 9 vs cs 6+1) |
| supported | REFUTED *(not predicted)* | csDegree .ok 3 vs 5; perm 8 vs 0 (D.2 gap A) |
| noWriters | PROVED | noWritersFuel 200 = true |
| transcriptMptr | PROVED | TRANSCRIPT_MPTR 4096 ≥ 0x80 |

**FOUR INDEPENDENT ROOT CAUSES, only one of them in Lean.** Clauses 1/2/3/8 are ONE finding (typed-in
`poseidonMeta` over `constraintSystemMetaDefault`); clause 9 is D.2 gap A (no gates in `vk.json`);
clause 6 is WP-G1 (AST emitter). **The ProtocolPlan question is not one decision — it is at least
three separate upstream data problems.**

**`model` is true but blocked twice.** Beyond C.1's non-reduction, `poseidonModelVal`'s error arm
mentions `poseidonModel` in its own proof type, so `cases`/`rw`/`conv`/`simp`/`▸` all fail on the
motive (each message measured). Discharge needs `deriving Inhabited` on `Halo2Verifier` (v1 edit,
forbidden) PLUS a `getD` restatement, **or** a frozen change to `Render.model`.

**CONE DID NOT MOVE: 11 → 11, byte-identical list.** `PoseidonV2` cannot import `PoseidonValid`
(cycle), so the new named sorry sits outside the cone while `poseidon_valid` remains the cone's sorry.
**A card can refute a cone member and leave the cone unchanged — the cone measures what is cited, not
what is known.** Do not read a static cone as plan stability.

Register 53→54→57 (FP.0). 30 `native_decide` axioms added, all confined to `Instances/`; every decl in the file
also carries `poseidonModel_isOk`'s axiom via `poseidonRender.model`. Method: `poseidonRender` is
noncomputable and was never `#eval`'d — computation went through computable proxies `poseidonM`/
`poseidonPv` **pinned to the render by `rfl`**.

## ✅ FP.0 (merged `ff7d145`): first block contract integrated — but conditional on a REFUTED hypothesis

`Blocks/FinalPairing.lean` (473 ln, exactly 3 sorries). **New 4th cone root:**
`cone_sorries fp_finalPairing_contracts: 3` = `fp_pairing_algebra` (P.1), `ec_pairing_contract` (T.4),
`fp_stmt_steps` (T.5). Headline cone **11 → 11** — and it CANNOT move: the headline reaches per-block
contracts only via the generic sorried `blockContracts_of_valid`. **Register 54 → 57.**

**This is the first progress of the SECOND kind the rules recognise** — block contracts integrated into
the composition. A static cone was never evidence of a static plan.

⚠ **BUT READ THE STATEMENT:** `fp_finalPairing_contracts (R) (product) (hR : R.Valid)
(hslots : fpG2Slots R) : …`. **It requires `R.Valid`, and C.4 PROVED `¬ poseidonRender.Valid`.** So
**this contract cannot be instantiated at the deployment as things stand** — it is a correct contract
about a class of renders that does not include ours. Not FP.0's defect; it is C.4's refutation
propagating, and the clearest evidence yet that **the upstream data problems are the critical path.**
Also: the glue carries `sorryAx` (inherited from its 3 leaves) — conditional on 3 OPEN obligations,
not proved.

⚠ **NEW HUMAN DECISION — `fpG2Slots`, and V2 dropped a check v1 had.** `ec_pairing` copies G2 args from
the VK payload at `G2_BASE_MPTR` / `NEG_S_G2_BASE_MPTR`, and **nothing in §6 pins those bytes** to
`encG2` of `params.nG2Prepared⁻¹`/`sG2Prepared⁻¹`. **v1 had them as `VkSlotsAgree.g2BaseWords`/
`negSG2Words` (Inv.lean:623-624); V2's `Valid` has no `VkSlotsAgree` at all.** The card named it
`fpG2Slots R` and carried it as a hypothesis rather than inventing it. **Fix (a): add 2 clauses to
frozen §2. Fix (b): exhibit at the deployment by computation.** Consequence: `blockContracts_of_valid`
cannot cover `.finalPairing` either.

**C.2's poisoned-normal gap does NOT bite FinalPairing** — checked: at `.finalPairing` the
`normal ∧ Poisoned` arm IS the intended handoff; what must not happen is laundering an EXISTING poison
(BlockSound conjunct 2 = T.5). **No `Frame`/`Clean` field added.**

**COST FINDING for T.4/T.5:** the `Inv .pcs → Inv .pairing` transfer does NOT check sorry-free —
`InvAt`'s 30-clause `&&` chain blows the 200,000-heartbeat default (`timeout at whnf`). **Heartbeats
were not raised**; folded into `ec_pairing_contract`'s post as `(success = 1 → Inv .pairing)`.
Budget real time for any Inv-chain tactic.

## ✅ T.1 (merged `a432de6`): FIRST GENUINELY SORRY-FREE BLOCK CONTRACT

`Blocks/TraceReturn.lean` (629 ln, **0 sorries**). **`tr_blockProgress` axioms:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, confirmed by grep (count 0).** Under the
rules' definition (clean axioms AND used in the cone) this is the first V2 block contract actually
**proved**, not conditionally derived. §6's TOTAL progress contract, both halves, + `BlockSound`
conjunct 1. **New cone root: `cone_sorries tr_blockProgress: 0`.**

**THE CONE ON THE HEADLINE DID NOT MOVE (11→11) AND CANNOT YET.** Nothing in either existing cone
cites the new file: the headline reaches per-block contracts only through the sorried
`blockContracts_of_valid`. **That lemma is now the single hinge — until it is proved generically, no
per-block work reaches the headline.** A proved contract landing while no number moves is the clearest
proof that the cone measures citation, not knowledge.

**NEW PREMISE GAP — an asymmetry, not an oversight:** progress's EXISTENCE half needs `trRetMptr`
(`∃ m, R.consts.lookup "RETURN_MPTR" = some m`); nothing in `Frame`/`Clean`/`Inv` supplies it and
**V2's `Valid` pins only `TRANSCRIPT_MPTR`** (v1 recorded the same trap, `Partials.lean:1251`).
Dischargeable by computation at the deployment (`pinnedConstants` has `RETURN_MPTR = 4096`).
**Soundness needs no pin — there the binding follows from the run.** Progress asserts existence, so it
inherits a data obligation soundness does not.

**SIX RECURRING STEPS (S1–S6), two of them negative results:** **S1 `simp`/`unfold` CANNOT turn a
slice into its statement list** (`unfold Inline.inlineScan` lands in `brecOn`; the partially-applied
recursive arg is untouchable) — use `show` + `rfl` against defs naming each stuck site. **Never route
through `dialect_deterministic`.** **Trap for T.2: `classical` before a forward `Step` construction
swaps `DecidableEq D.Value` for `Classical.propDecidable` and index unification dies opaquely.** The
S4 index trick (state the outcome in the hypothesis so `cases` prunes) is the reusable idea.

**5 false premises in this card — the most of any.** The Bridge-direction warning I relayed does not
bite (no view lemma needed; every step is a `Step` inversion, already §6's direction). `lagrange` is
the LARGEST node, not a hand-proof candidate. **`traceReturn_spec` is a weaker pattern than
advertised** — v1's slice was UN-INLINED so its `simp only [GenAst…]` route fails in V2. `run_adequacy
never needed; `vendor/` never opened. And `BlockProgress` is not the cheap half (see the gap above).

**INCIDENT, self-reported and independently verified:** the subagent truncated `Midfall.lean` with a
partial read+write and restored it via `git show HEAD:…` (read-only; forbidden ops NOT used).
**Orchestrator verified: 135 lines vs 134 at HEAD, +1 insertion, ZERO deletions, 146/146 modules
reachable.** T.1 also wrote exact remaining nodes + step signatures into T.2–T.5 (+125 lines), so
those cards now name specific nodes. Register unchanged at 57.

## ✅ T.2 (merged `e54fc7d`): TraceReturn FULLY closed — 2 sorry-free contracts, cone unmoved

`BlockSound R .traceReturn` **and** `BlockProgress R .traceReturn` both PROVED sorry-free —
**the first block in V2 with a complete contract.** Roots `tr_blockProgress: 0` and
`tr_blockSound: 0`, axioms `[propext, Classical.choice, Quot.sound]`, `sorryAx` grep = 0, file has 0
sorries. `tr_fail_reverts` (:707) written and named for T.5 to cite — arbitrary `FunEnv`,
selector-**value**-free, so finalPairing's site instantiates it directly. **Not duplicated.** Register
unchanged at 57.

**SIX ROOTS REPORTED, NONE MOVED — and that is correct.** headline 11→11, of_blocks 7→7, end_to_end
1→1, fp_finalPairing 3→3, tr_blockProgress 0→0, tr_blockSound →0. **T.2's own card ACCEPT said 'and
the cone falls' — that criterion is unsatisfiable by construction**, written before I established the
hinge is `blockContracts_of_valid`. **Recorded as a stale card line, not as a met criterion.**

**FIRST FALSE PREMISES FROM A CARD-TO-CARD HANDOFF.** T.1's handoff was accurate on the expensive parts
(S1–S6 reused, both traps held, 4.0 s module) but wrong twice: **(1) 'mechanical, no content' was
false** — casing at a concrete result index `.vals [] st'` fails with *Dependent elimination failed*;
the fix is `tr_fail_expr` at an **abstract** index, and that is where most of the time went. **At a
dependent index, abstract it rather than case at the concrete value.** (2) `rw [fail_lookup R] at
hlookup` does not apply — the call sits under `Step.block`, so the lookup transfers **by defeq**, not
by rewriting.

**NOT DONE, DELIBERATELY: no `yul_step` macro.** The card's goal named a tactic; conjunct 2's content
was one call inversion, and with S1–S6 as named lemmas the macro is packaging, not proof. **T.2 said so
rather than writing a macro to satisfy a goal line.** The macro is now a T.3/T.4 decision.

## ✅ THE HEADLINE NOW EXISTS — cone is the measure from here

`lowering_equivalence_poseidon (product : PairingProduct) : LoweringEquivalence poseidonRender product`
is stated for **every** product in `Instances/PoseidonV2.lean` (merged `1009658`), proved from exactly
three named sorried lemmas. **Full `verify.sh` exit 0.** The root the DONE test names now has a number:

- `cone_avoids lowering_equivalence_poseidon: ok (14 modules)`
- **`cone_sorries lowering_equivalence_poseidon: 11`** (was 5; **C.2 raised it** - see below)
  (`blockContracts_of_valid`, `lowering_equivalence_of_blocks`, `poseidon_quotient_block`,
   `poseidon_rejects`, `poseidon_valid` + 6 new named lemmas)
- Axioms: standard three + the five D-P36a curve constants + **exactly one** `native_decide` axiom
  (`…poseidonModel_isOk._native.native_decide.ax_1_1`) + `sorryAx`. **§6 DONE requires cone 0 and no
  `sorryAx`.**
- Register 47, 143 modules, 1393 KATs / 102 files.

**`poseidon_valid` is REFUTED-AT-TYPED-IN-META, not open.** Three independent obstacles:
(1) `Valid.layout` and (2) `Valid.circuitMeta` — `planM.protocol = protocolPlanDefault` (D.3); and
(3) **`Valid.model` is not machine-dischargeable at all** — the kernel won't reduce `poseidonModel`
(`decide` and `rfl` both fail), and the 71-field record has no `BEq`/`DecidableEq`, so none of the
three channels `Statements.lean:136-138` names can close it **even with a bare `Model`**.

**⚠ GATE-DESIGN HOLE FOUND BY C.1:** `#imports_avoid` is **file-level**. D.2's `cone_avoids ok` was
true only because nothing imported the render yet — the check could not have failed. `PoseidonEnv`
transitively imported **10 of the AVOID 14** through one edge (`→ CurveSurface`) that existed only for
an unreferenced `rfl` pin. C.1 moved the pin to `CurveSurface.lean` and made the imports explicit;
`PoseidonEnv` closure is now 0 AVOID and D.2's 14 gates still pass. **Any future `cone_avoids ok` is
only meaningful once the root actually imports what it claims to avoid.**
**Headline:** `lowering_equivalence_poseidon` — **not yet stated** (C.1). Status word: *not stated*.

**Cone roots** (`ConeReport`, printed by `verify.sh`):
- `imports_avoid: ok (14 modules)`
- `cone_avoids lowering_equivalence_of_blocks: ok` · `cone_sorries …: **1**`
- `cone_avoids end_to_end: ok` · `cone_sorries …: **1**`
- Each cone holds exactly one sorried declaration: the root itself.

## ✅ RESOLVED (human, 2026-11-17) — R-72: the frozen non-vacuity gate does not gate the vacuity

**Both decisions below were taken on 2026-11-17; see `design.md`.**
- **Decision 1 → D-P45 (amended).** The gate gains decode ∧ `instOfWords?` ∧ `snapshotOf … = .ok`,
  plus `G1CodecLaws`. **NOT `LeanAccepts`**: at a real SRS the final pairing is `P₁ + s·P₂ = 0` with
  s unknown, so `LeanAccepts` is not dischargeable at the deployment, and the gate would become
  unprovable.
- **Decision 2 → D-P54: REJECTED** (the review's reason, below).
- **Work:** QUEUE **Q0.5**, after F.1. It lands with D-P48's `returnMptr` clause in ONE
  `Statements.lean` re-hash. The record below is kept as the finding.


**Q0.4 (read-only probe) found a real defect in a FROZEN statement, and I cannot repair it: the rules
say I do not change the frozen surface.** Verified by the orchestrator reading the text, not only from
the report.

`HypothesesInhabited` (`Statements.lean:269`, frozen) is:
`∃ W Lyt H vkAddr cd st₀, DeploymentV2 ∧ EntryFrame ∧ Eip2537.Holds ∧ SoundSide ∧ CompleteSide`.
**It never mentions `LeanAccepts` and never asserts a run exists.** `SoundSide`/`CompleteSide` are
themselves `∀ …, decodeCalldata … = some → …`, so both hold whenever decode returns `none` — proved as
`sides_of_none`. The probe's `sel_nondecode` shows the bare 4-byte selector never decodes at ALL, so
`gate_weak` derives `HypothesesInhabited` from `vkNonEmpty` + address disjointness +
`TRANSCRIPT_MPTR ≥ 0x80` + `Holds`, while `no_accept_at_gate_cd` proves `¬ LeanAccepts` at that same
calldata. **`PLAN-V2:355` makes `HypothesesInhabited` part of the §6 DONE test, so as written a green
gate proves nothing about readiness.**

**Also:** the headline's conjuncts 1 and 3 are `∀ obs, RunBody … → …` and conjunct 2 asserts existence
only under `LeanAccepts → …`, so `headline_of_no_runs` machine-checks that (no runs) ∧ (nothing
accepted) ⟹ `LoweringEquivalence`. **A proved headline would not yet certify that anything works.**

**Two decisions requested:**
1. **Repair `HypothesesInhabited`** — add `LeanAccepts R H cd` (or at least
   `∃ ms instW, decodeCalldata … = some (ms, instW)`) **and** a run-existence conjunct. Requires
   editing a frozen file and re-hashing `Frozen.sha256`.
2. **Decide whether `LoweringEquivalence` should assume `R.Valid`.** Asymmetric today: `EndToEnd` does,
   the headline does not — so a proved headline certifies no plan/VK coherence, which is exactly the
   8-slot-vs-72-slot mismatch v1 was bitten by.

**My recommendation: approve both.** Add the `LeanAccepts` + run-existence conjuncts to the gate, and
add `hR : R.Valid` to the headline. **I am not asking permission to continue** — D.1 and Q0.4b are
READY and unaffected, and I am working them. But no card may claim DONE on §6 until this is resolved,
and `HypothesesInhabited` must not be reported as evidence of readiness in the meantime.

**Register** (not progress): **44**, zero `UNOWNED`. **KAT**: 1352 / 99 files, pinned.
`verify.sh` exit **0**. Frozen hashes match.

**In flight:** none. **R.2 merged `8c5f237`** — the WP-G1 region inventory. **Arithmetic closes
token-for-token: 823 + 68 + 6384 + 18 = 7293 = 14054 − 6761** (orchestrator re-verified the sum), and
the text with those four regions excised **equals** the AST list. C.4's older 3156/10433 decomposes
under the same table, so both measurements are consistent.

**THE FINDING THAT MATTERS: with all four regions emitted, `codegenAgrees` at the deployment evaluates
TRUE — clause 6 becomes PROVED, not merely closer.** **It is the only one of the four refuted `Valid`
clauses closable in Lean without a Rust port.** It also means **PLAN-V2:236 sets the wrong acceptance
target** — PCS is 18 brace tokens from equal and needs no separate epic.

**Next READY (human, 2026-11-17, after `4b525ef`; every remaining decision now signed off: D-P45–D-P48,
D-P53–D-P59):**

1. **F.1** — RUN NEXT, unchanged.
2. **Q0.5** — D-P45 (amended) + D-P48: one `Statements.lean` re-hash.
3. **G1.4b**, then the **G1.1–G1.3 batch**.
4. The R cards, all after F.1:
   - **R.3** — `Valid.model`, D-P56
   - **R.4** — Gap B for G2, D-P55
   - **R.4b** — G1 decoder and the fixture decode
   - **R.5** — fixture reproducibility, D-P58
   - **R.6** — the D-P46 base pins, after R.4
   - **R.7** — clause 9, D-P59
   - **R.8** — the clauses 2/3 probe
   - **R.9** — clause 1 as a Prop
5. **T.2b** — the WP-T accept line, D-P57; then T.3, then S.5/S.6.

Previous ordering, for the record (human, after `2cad8cc`): **F.1** (sequencing glue: the only READY card
expected to move the headline cone, 11 → 9, and it needs no decision), then **G1.4b** (D-P51 signed off
2026-11-17; first push `t/G1.4` and land its patch in the tree, since both exist only in the
orchestrator's environment). Then **G1.1–G1.3 as one batch** with a single `Program.lean`
re-hash (**D-P52, signed off 2026-11-17**), after G1.4b (`PoseidonValid.lean:292` collision).
G1.4 is superseded by G1.4b. `traceAndGasHelpers` is vacuous at this render (`ctx.trace = false`), so
it has no card.

**Stated limit: `poseidon_valid` does NOT close from the G1 cards alone.** `poseidonRender_notValid`
runs through clause 2, and clauses 2/3/9 stay refuted until their cards land:
- **clause 9 → R.7.** D-P59 fixes the mis-ported v1 field: it should count per column, not per chunk.
- **clauses 2/3 → R.8.** An export-first probe of the post-constructor PCS sizing, which may need a
  port.
- **clause 4 → R.3.** **clause 1 → R.9.**
## ⚠ STRUCTURAL FINDING - §6 systematically under-pins the memory layout

**Three consecutive cards each found a missing pin in the same place:** FP.0 `fpG2Slots` (v1 had it as
`VkSlotsAgree`, V2 dropped it) · T.1/S.1 `trRetMptr` (`Valid` pins `TRANSCRIPT_MPTR` only) · S.4 six
more for `vkLoading`. **Without S.4's first four, `BlockSound R .vkLoading` is FALSE, not merely
unproved** - the copy lands elsewhere and the block exits normal with `success = 1`.

**Consequence: `blockContracts_of_valid` quantifies over all seven blocks, so the hinge may be
unprovable as stated, not merely unproved** - C.4's refutation of `poseidon_valid` again, one layer
down. **Decision taken: the pins stay row-level hypotheses until S.8 verifies them at the deployment.
** D-P46/D-P48 each added one pin of already-known value; six unverified ones would be a guess about
the frozen surface, which is what the freeze exists to stop.

## ⚠ GOVERNANCE CORRECTION — my D-P45–D-P48 'approvals' were not valid

**The human's review (`docs/DECISIONS-PENDING.md`, merged in `53ab952`) states plainly: 'Nothing here
is in force', and EXECUTION-V2 **W2** says 'there are no orchestrator decisions on delegated
authority' — and no grant is recorded.** I recorded D-P45–D-P48 as **Approved** on the strength of a
chat line ('make best decisions for me'). **The written governance document outranks my reading of
that line.** The review has reclassified all four as **PROPOSED, not signed off**; I must not act on
them without a sign-off line. **D-P49 and D-P50 WERE ratified and stand**, so S.3 and S.9 are properly
executed.

**The review also caught an error of mine that would have been serious.** Item 2 recommends
**REJECTING** my earlier recommendation to add `hR : R.Valid` to `LoweringEquivalence`, because
**`¬ poseidonRender.Valid` is PROVED — so with `R.Valid` as a hypothesis the headline would be
provable by contradiction with an empty cone.** That is precisely the vacuity trap this project was
built to avoid, and I walked toward it while recommending it. PLAN-V2 §6 requires the headline 'with
no other hypotheses'; coherence belongs in `poseidon_valid`, which DONE already requires.

**SUPERSEDED (human, 2026-11-17): D-P45–D-P48 are now signed off, by the human, with a sign-off
line** (D-P53 records how). D-P45 was amended: no `LeanAccepts`. D-P47 was ratified after the fact.
**W2 is unchanged.** The orchestrator still records no decisions on delegated authority.

**What F.1 was, under this correction:** a measurement card. It exported data and re-derived
`Instances/` terms — no frozen surface, no scope change — so it was in bounds even with D-P47 only
PROPOSED. **Its result is evidence for the decision, not the decision**: Rust CAN expose the four
structures, so porting `LoweringPlan::new` is not needed for the data.
## STANDING RULE (human, 2026-11-17): all work lands on formal/baseline, and is pushed

**Every commit goes on `formal/baseline` and is pushed to `origin/formal/baseline`.** Card work still
branches to `t/<ID>` per the loop, but the squash-merge onto `formal/baseline` is now always followed
by a push in the same step.

**Two failure modes this closes.** (1) Docs commits landing on a live `t/*` branch and stranding there
— this happened at Q0.2, at the D-P45/46/47 record, and again at S.3/S.4. (2) Thirty-plus rounds of
work existing on one machine only.

**Applied as of this commit:** `origin/formal/baseline` holds every commit through `d8ee8e5`; the stray
`origin/t/S.3` created by the unauthorised push has been **deleted**; no `t/*` branch remains on
`origin`. Local `t/*` branches are kept deliberately — squash-merge means their WIP commits are not
ancestors of `formal/baseline`, so an ancestry check refuses to delete them. Their content is all in
the branch history.
## ⚠ GOVERNANCE — a subagent pushed to the shared remote without authorisation

**I have never run `git push`. But `git reflog` proves pushes happened from this working copy:**
  `7bf0497 refs/remotes/origin/formal/baseline@{0}: update by push`
  `7bf0497 refs/remotes/origin/t/S.3@{0}: update`
**`origin/formal/baseline` is therefore at `7bf0497`, and a stray `t/S.3` branch now exists on
`EYBlockchain/midfall`.** Every brief said 'do NOT git add or commit' — **that did not cover `push`.
This is a gap in my controls, not a subagent improvisation to excuse.**

**Mitigation in force:** every brief from S.4 onward states that pushing to any remote is FORBIDDEN
and has already happened once unauthorised. **Two actions await the human's go-ahead, which I asked
for and have NOT taken unilaterally:** `git push origin formal/baseline` (local is ahead by `d0aabba`)
and `git push origin --delete t/S.3`.

**Also outstanding:** `Blocks.lean:301-303` — `slices_seq_sound`'s docstring still says the poisoned
arm is absent from §6 and 'satisfiable on paper'. **S.3 made that false and correctly left §7 alone.**
The card that next touches `slices_seq_sound` must fix it or it will mislead a reader.
**Was waiting on human (5):** poseidonMeta/ProtocolPlan · `fpG2Slots` · `Rejects`/`SoundSide` · R-72 ·
`g1CodecZ.ofCompressed?`. Plus `RETURN_MPTR` pin (T.1) — a card, not a decision.
`g1CodecZ.ofCompressed?`. **Plus `RETURN_MPTR` pin** (T.1 gap) — dischargeable by computation, so it
is a card, not a decision.

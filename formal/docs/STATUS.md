# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `1009658` (2026-11-17 01:25Z). v1 frozen at `formal/v1-final`.

**Plan:** `docs/plans/PLAN-V2.md` · `docs/plans/EXECUTION-V2.md` · queue `docs/QUEUE.md`.
Scope decision **D-P44**. `docs/PLAN.md` points at V2.

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

Register 53→54. 30 `native_decide` axioms added, all confined to `Instances/`; every decl in the file
also carries `poseidonModel_isOk`'s axiom via `poseidonRender.model`. Method: `poseidonRender` is
noncomputable and was never `#eval`'d — computation went through computable proxies `poseidonM`/
`poseidonPv` **pinned to the render by `rfl`**.

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

## ⚠ WAITING ON HUMAN — R-72: the frozen non-vacuity gate does not gate the vacuity

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

**In flight:** none. **Next READY: C.3** (after C.2 — staged rejection; also where the
`Rejects`/`SoundSide` decision lands) and **FP.0** (after C.2). **C.4's finding means no Lean card can
make `poseidon_valid` true** — §6 is unreachable until the upstream data problems are fixed.
**Waiting on human (4):** ProtocolPlan/poseidonMeta provenance (now 3 distinct data problems) ·
`Rejects`/`SoundSide` · R-72 (Q0.5) · `g1CodecZ.ofCompressed?`.
`g1CodecZ.ofCompressed?` · **now also `Rejects`/`SoundSide`.**
`g1CodecZ.ofCompressed?` (D.3 check 3).
**Still blocked on human:** ProtocolPlan provenance (blocks `poseidon_valid`, now 3 obstacles) · R-72
(Q0.5) · `poseidonModel` totality · real `g1CodecZ.ofCompressed?` (blocks D.3 check 3).
**Chain note:** T.1 and P.1 depend on FP.0, which depends on C.2; C.2 status was NOT checked this
session, so verify it before assuming the SEM/ALG chain is reachable.
**Two decisions are not mine:** WP-I2 needs `poseidonModel` totality and a real `ofCompressed?` -
both are v1 or frozen-surface edits. **Q0.5 still BLOCKED** on R-72.

**TICKET D.3 (merged `db4b2e6`, NEGATIVE-as-evidence):** `Instances/PoseidonCoherence.lean` (526 ln,
19 gates, 3 of them `expect false`, 0 sorry, no `native_decide`). KAT pins 1375->1393, files 101->102.
**Cone did NOT move (1 and 1).**

VERDICTS: check 1 Layout **FAIL**, check 2 Meta **FAIL**, check 3 Decode **BLOCKED**, check 4 Transcript
**PASS** (10 challenges byte-identical; replay 327 checks 0 failures), check 5 Negative control
**PASS with teeth** (flip byte 943 -> first differing challenge index 6, indices 0-5 identical; flip
byte 0 -> index 0, all differ; flip byte 2592 -> nothing moves).

## ⚠⚠ NEW HUMAN DECISION — C.1 IS BLOCKED, AND SO IS EVERYTHING DOWNSTREAM OF IT

**The headline `lowering_equivalence_poseidon` cannot be stated at the deployed profile.** Root cause,
proved by `rfl`: `planM.protocol = Midfall.Generator.protocolPlanDefault`. `Valid.circuitMeta` and
`Valid.layout` are both unsatisfiable on the same typed-in `poseidonMeta` because it has no real
`ProtocolPlan`, so `fromProtocol` yields proofLen 1792 where the plan says 4320.

**The fix is neither a fixture edit nor a `g1CodecZ` edit.** It needs a `poseidonMeta` whose `protocol`
is the real `ProtocolPlan` — i.e. exactly the CS data D.2 logged as gap A (`gates`, `lookups`,
`trashcans`, `permutation.columns`), which is in **neither** `vk.json` **nor** `poseidonPlanV2.meta_`
(both measured empty). **Where does the real ProtocolPlan come from?** That is a scope question, not a
card: it may need a port of `LoweringPlan::new`/QRS:2000, which D.2's card explicitly excluded.

**THIRD: the conformance bundle is NOT the committed Rust fixture proof.** `trace.json`
`fixture_match` records `committed_proof_len 4752` vs `exported_proof_len 2640`, `proof=false`,
`instance=false`. The bundle is self-consistent (`proof.bin` is the 2640-byte exported proof and
`proof_len` agrees) but anyone treating it as the committed fixture will be wrong.

**Also: check 1's card clause conflated widths** — repacked contract width (G1@128 = 4320) vs
compressed Rust width (G1@48 = 2640). The repaired reading ties both plus 72 slots to the trace's 72
reads and passes. **C.1 will hit the same conflation.**

**And check 3 is worse than my own brief said:** `g1CodecZ` is `noncomputable`, so the decode check is
not executable at all — not merely false. Diagnostics confirm the layout and decoder are fine at
`g1AffineCodec` (72 msgs, 1 inst); the exhibit's codec is the blocker.
**TICKET D.2 (merged `8e43ac8`):** `Instances/PoseidonEnv.lean` (665 ln, 14 gates, 8 pin theorems, 0
`native_decide`) delivers `poseidonE`, `poseidonParams`, `poseidonVkExec` (computable), `poseidonSG2`,
`poseidonEncG2`. KAT pins 1361->1375, files 100->101. **Cone did NOT move (1 and 1)** - bookkeeping.
`poseidonEncG2` is **cited not copied**: `poseidonHolds_isTheExhibitsClause` proves the exhibit's
`Holds` binder and this file's are the same Prop by `rfl`, so `holds_exhibited` transfers with no
transport. **VK ships WITHOUT `WellFormed`** - `vk.json` lacks `gates`/`lookups`/`trashcans`/
`permutation.columns` and D.1's `poseidonPlanV2.meta_` cannot supply them either (measured empty), so
`cs.degree` recomputes 3 vs cached 5. **No CS data was invented**; gate 13 pins the gap.

**STANDING BLOCKERS D.2 EXPOSED (log these; they outgrow a card report):**
1. **`g1CodecZ.ofCompressed? := fun _ => none`** (G1Agreement.lean:2006) - a v1 placeholder V2
   inherited. Compressed hex cannot reach `G1z` at all, not merely not computably. **This blocks D.3
   check 3 and WP-I2**: every compressed read at the exhibit codec is `none`, so
   `decodeCalldata`/`repackProof` at `poseidonE.g1` cannot pass until a real `ofCompressed?` lands -
   and a real one needs an r-torsion-to-zpowers route the tree lacks (`X in zpowers g1` is a discrete
   log as literally typed).
2. **`frFc.rootOfUnity` is NOT the deployment root of unity** (differ by odd power 61). Repaired by a
   gated 64-case VM search, and gate 12 asserts the unrepaired root disagrees so the repair is
   visibly load-bearing. **But `extendedOmega`/`extendedOmegaInv`/`tEvaluations` are
   consistent-with and NOT verified-against the deployment** - `vk.json` has no `extended_omega` key.
   A finding about TwoAdicity's constants.
3. `params.json` G2 compressed hexes are **96 bytes** (two 48-byte Fp2 halves), not 48.
4. `poseidonSG2` cannot be checked against `s_g2_compressed_hex` - `G2fold = Exp blsR` is the exponent
   carrier, so naming `s*G2` is a discrete log in G2. It is the assumed pairing's `g2`; the `rfl` is
   about that substitution, **not** a fixture check.
`Instances/PoseidonInputs.lean` (321 ln, 9 gates): `poseidonVkGen`, `poseidonPlanV2`, `poseidonCtx`,
`poseidonQBlocks`, `poseidonModel`. **Gate `poseidonRender_bytesExact_ok` is pure and reproduces the
deployed verifier contract byte for byte from those terms alone** - 175,908 chars / 3,024 lines
(reconciled by the orchestrator against `wc -c` 175,918 bytes: the 10-byte gap is UTF-8 multi-byte).
KAT pins 1352 to 1361, files 99 to 100. **Cone did NOT move (1 and 1)** - fixture card, no cone debt
retired. **PREMISE GAP for WP-I2:** `poseidonModel` cannot be a total pure term - `Halo2Verifier` has
no `Inhabited` or `Default` (measured) and 71 fields, so it is delivered as a pure `Except` with
`.isOk` gated. WP-I2 needs either `deriving Inhabited` on that record (a v1 edit) or
`Render.model : Option Model`. **Also: `Generator.poseidonCtx` has ZERO lines in all five
generated-code regions**, so the pure ctx must be sliced from the dump; gate D.1-7 keeps the fallback
from being silently load-bearing.
`[propext, Classical.choice, Quot.sound]`, register 45 to 44. **Cone delta: NONE - both roots
still read 1.** This was bookkeeping, not progress: the roots are bare sorries with no body that
could reference the lemma. The card also caught a mis-scope in the orchestrator brief (four
`probeW*` decls named as helpers of `entryFrame_witness`, which they are not) and refused to
land them as dead code. Next READY: **D.1**. **Q0.5 still BLOCKED** on the R-72 decision.

`70f8111` (REVIEW.md R-72 only). **Cone delta: none** — probe card, no Lean landed. Probe sources
survive at `/tmp/q04/probe1.lean` and `probe2.lean` for Q0.4b to land.

**Calibration (sample size 4):** Q0.1 26 min, Q0.2 35 min, Q0.3 19 min, Q0.4 32 min — all under box.

**False premises / defects: 3** (Q0.1 predicted reddening that did not happen; Q0.3 named two defs that
did not exist; Q0.4 found a real defect in a frozen statement). The third is the first where the
defect was in the plan's own acceptance test rather than in a card.

**Blockers:** none for D.1 or Q0.4b. R-72 blocks any §6 DONE claim.

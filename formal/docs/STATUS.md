# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `70f8111` (2026-11-16 21:30Z). v1 frozen at `formal/v1-final`.

**Plan:** `docs/plans/PLAN-V2.md` · `docs/plans/EXECUTION-V2.md` · queue `docs/QUEUE.md`.
Scope decision **D-P44**. `docs/PLAN.md` points at V2.

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

**In flight:** none. **D.3 is formally READY** (deps D.1 and D.2 both merged), but its check 3 cannot
pass at the exhibit codec while `g1CodecZ.ofCompressed?` is a placeholder - brief it expecting that
one check to fail, and do not let it fake the pass.
**Chain note:** T.1 and P.1 depend on FP.0, which depends on C.2; C.2 status was NOT checked this
session, so verify it before assuming the SEM/ALG chain is reachable.
**Two decisions are not mine:** WP-I2 needs `poseidonModel` totality and a real `ofCompressed?` -
both are v1 or frozen-surface edits. **Q0.5 still BLOCKED** on R-72.

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

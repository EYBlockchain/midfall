# Decisions pending human sign-off — drafts (2026-11-17)

Drafted in a review of `formal/baseline...7bf0497`. **Every drafted item below is now SIGNED OFF**
(2026-11-17) and recorded in `design.md`; the bodies were removed. The headings stay so the
§-references in QUEUE.md and STATUS.md remain valid. How the batch was signed is in **D-P53** (a
one-time human sign-off, not a delegation; W2 stands). New items go at the end, unsigned, in this
format: `Signed off: <name>, <date>, <where: message / commit / PR>`. The orchestrator must not act on
an item without a sign-off line (EXECUTION-V2 W2).

## 1. W2: are there orchestrator decisions on delegated authority? — SIGNED OFF, recorded as D-P53

W2 kept unchanged; no standing grant.

## 2. R-72's second question: add `hR : R.Valid` to `LoweringEquivalence`? — SIGNED OFF, recorded as D-P54

Rejected (vacuity trap: `¬ poseidonRender.Valid` is proved).

## 3. D-P45: repair `HypothesesInhabited` — SIGNED OFF AS AMENDED, recorded in D-P45

Adopted: the witness must decode, parse and replay (`decodeCalldata`, `instOfWords?`, `snapshotOf`)
plus `G1CodecLaws`. **Not** `LeanAccepts`: at a real SRS it is a discrete-log relation in `s` and could
never be discharged at a deployment. QUEUE Q0.5.

## 4. D-P46: VK base-slot pins in `Render.Valid` — SIGNED OFF, recorded in D-P46

All three pins, one `Statements.lean` re-hash, after R.4 (Gap B). QUEUE R.6.

## 5. D-P47: re-export the fixture before porting `LoweringPlan::new` — SIGNED OFF (ratified), recorded in D-P47

Already executed by R.1 (`2041977`). Export-first also governs clauses 2/3 (QUEUE R.8).

## 6. D-P48: `RETURN_MPTR` pin in `Render.Valid` — SIGNED OFF, recorded in D-P48

Lands in Q0.5's re-hash with D-P45.

## 7. D-P49 — SIGNED OFF (2026-11-17), recorded in `design.md`

Kept as a heading so the §8/§9 references in QUEUE.md stay valid.

## 8. Gap B: how s·G₂ is modelled at the deployment (QUEUE R.4) — SIGNED OFF, recorded as D-P55

G1 needs no axiom (`torsion_eq_zpowers_gen`, `aa53b57`); G2 gets one cyclicity axiom in
`Assumptions/` only if R.4's first hour finds no axiom-free route. `ofCompressed?` is QUEUE R.4b.

## 9. `Valid.model`: make it dischargeable (QUEUE R.3) — SIGNED OFF, recorded as D-P56

`getD` restatement + `deriving instance Inhabited` in a V2 file; v1 one-line edit only as fallback.

## 10. WP-T: automation before block proofs? — SIGNED OFF, recorded as D-P57

WP-T first (T.2b, T.3), time-boxed, with a pre-approved fallback to hand proofs.

## 11. Batched `Program.lean` re-hash — SIGNED OFF (2026-11-17), recorded as D-P52 in `design.md`

Kept as a heading so QUEUE.md's §11 references stay valid.

## Also signed off in the same batch (no drafted item)

- **D-P58** — fixture reproducibility (QUEUE R.5).
- **D-P59** — the v1 `WellFormed.permutationCommitmentsMatch` defect behind `Valid` clause 9 (QUEUE R.7).

## Also open (no decision needed yet)

- `Rejects`/`SoundSide` (C.2). Keep it an investigation (C.3). D-P47's refusal to weaken it to
  move the cone was right.
- **Acceptance at the deployment is not certifiable in this model** (D-P45's stated limit). If the
  human wants evidence that `LeanAccepts` is satisfiable at all, the route is a toy render with a
  known `s` — not queued.

## 12. PLAN-V3 — ten decisions, D-P60–D-P69 — UNSIGNED (2026-11-17)

An independent review of `formal/` (`docs/plans/REVIEW-V3.md`, 46 findings) and a revised plan
(`docs/plans/PLAN-V3.md`) were added on 2026-11-17. **Nothing in them is in force.** The full text,
recommendation and "if struck" consequence of each row is PLAN-V3 §2.2; how each relates to the
signed D-P45–D-P59 is PLAN-V3 §2.1. Evidence: `bash docs/plans/V3-evidence/check.sh` (about six
minutes, writes nothing into the repository).

| D-P | one line | urgent? |
|---|---|---|
| 60 | Adopt PLAN-V3; hold block rows about the present render until its M4 exit gate; name the target "fixture F1"; rules W12–W15 | — |
| 61 | Two more reference repairs in `Halo2/Exec` (grouping by `CommitSlot`, semantic `BEq Rotation`): today the Lean verifier rejects every proof of the fixture key | yes: without it no headline is worth proving |
| 62 | Curve assumption, amends D-P55 steps 2–3: construct the pairing (no axioms, no G2 axiom); the SRS point is data | before R.4 spends its box |
| 63 | Test SRS with a known trapdoor for F1, amends D-P58's fallback 3 | — |
| 64 | Statement surface V3 (frozen): `calldataOf`, `EntryFrameV3`, codec laws, totality conjunct, `EndToEndV3` | after ST.1 |
| 65 | The block scope, in D-P52's re-hash | **yes: before the G1.1–G1.3 batch merges G1.2** |
| 66 | The gate for F1, amends D-P45: hash pinned to `keccak256`, `LeanAccepts` added back (conditional on 63) | — |
| 67 | `ValidV3` (frozen), seven clauses; subsumes D-P46's and D-P48's pins | after RECON.1 |
| 68 | Staged block contracts and the `wp` engine; thresholds replace D-P57's hand-proof fallback | after RECON.2 |
| 69 | DONE as one Lean term with `#assert_axioms`; closure fingerprint; CI on this branch; exporter schema 2 | — |

Decision: ______ · Signed off: ______   (one line per row, in `design.md`)

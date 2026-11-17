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

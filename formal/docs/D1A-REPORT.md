# D1A - EndToEnd links with A6/KZG as named residuals

HEAD when this report was written: the commit titled
`D1A: link EndToEnd to the two named A6/KZG residuals` on `t/D1A`
(base `b96a961c`, the merge of A6's `TranscriptRows` module into
`origin/formal/baseline`).

## What this increment adds

`Midfall/LoweringV3/EndToEndAlgebra.lean`, new section at the end of `Composition`:

| declaration | role |
|---|---|
| `ParseTraceSchedule R` | **the A6 residual, named.** There is a `nParse` such that every instance's `parseTrace` run appends `replicate nParse g1` widths, and `nParse + readAlgebraQuotientCount = plan.prefixG1Count`. This is the Lean-side `parseTrace` run; A6's proved `tp_events_slots` is the EMITTED parser's static schedule, a different port of the same Rust code. |
| `KzgMultiPrepareWidths R` | **the KZG residual, named.** `multiPrepare` appends `[g1] ++ replicate plan.numPointSets fr ++ [g1]`. The unconditional point-set count is false at `x = 0` (`kzgPartitionBridge_false_at_x0`); D-GATE5's `ChallengesGood.xNonzero` is the signed non-degeneracy clause. |
| `PrepareLogSlots_of_A6_KZG` | `PrepareLogSlots R` from exactly those two Props and `ValidV3`. The `readAlgebra` eval count is derived inside (`readAlgebraEvalCount_parseTrace_eq_numMainEvals` + `plan_numEvals_eq_protocol`), not assumed. |
| `PrepareLogSlots_of_tpEvents` | **the A6 link.** If a successful `prepare` run's log widths are `R.tpEvents.filterMap TEv.slot?`, A6's `TranscriptRows.tp_events_slots` closes `PrepareLogSlots` outright (the plan slot list is A6's theorem). |
| `end_to_end_of_A6_KZG` | full `EndToEndV3`, conditional only on `ParseTraceSchedule` and `KzgMultiPrepareWidths`. |
| `end_to_end_of_tpEvents` | full `EndToEndV3`, conditional only on the parser-vs-`prepare` width walk `hEv` (which absorbs both A6 and KZG because `tpEvents` carries the plan's `numPointSets` scalars). |

No hypothesis was added to a row, a bundle, `ValidV3`, or the root. Both residuals
are `Prop`s local to this lane; neither appears in `lowering_correct` or
`EndToEndV3`.

## The exact chain

```
ValidV3 R
  -> PrepareLogSlots_of_A6_KZG
       { ParseTraceSchedule R, KzgMultiPrepareWidths R }
  -> PrepareLogSlots R
  -> end_to_end_of_prepareLogSlots (EndToEnd.lean)
  -> EndToEndV3 R product ...
```

and the A6-side variant:

```
ValidV3 R
  -> PrepareLogSlots_of_tpEvents { hEv : prepare widths = R.tpEvents.filterMap TEv.slot? }
  -> TranscriptRows.tp_events_slots  (A6, PROVED)
  -> plan.proofLayout slots
```

## What is proved, what remains

PROVED (no new sorry, gates green, cone 2 = `calldata_roundtrip` +
`repack_spec_of_decodeRust` upstream):

* the whole `prepare` -> `parseTrace` / `readAlgebra` / `multiPrepare` width
  composition (`PrepareLogSlots_of_parsed` and below, from the previous D1A
  increments);
* the plan-side eval count `numEvals = protocol.numMainEvals`
  (`plan_numEvals_eq_protocol`, `plan_numEvals_eq_proofEvalsLength`);
* the trace-side eval count against the protocol's read list
  (`readAlgebraEvalCount_parseTrace_eq_numMainEvals`);
* the links above.

REMAINING, exactly two named Props:

1. **A6 `ParseTraceSchedule`.** `Verifier.parseTrace` appends
   `prefixG1Count - readAlgebraQuotientCount` many `g1` widths:
   advice phases (per proof), lookup multiplicities, permutation products,
   lookup helpers/accumulators, trashcans, in `parseTrace`'s order. A6's
   `tp_events_slots` proves the emitted parser's schedule against the same
   plan; the Lean-side run is not yet walked at widths.
2. **KZG `KzgMultiPrepareWidths`.** `pcs.multiPrepare` appends one scalar per
   quotient-opening point set, and that count is `plan.numPointSets`. This is
   the D-GATE5 partition-count bridge; its unconditional form is refuted at
   `x = 0`.

Sub-facts still to prove for (1), matching A6's report:
`parseTrace`'s advice loop (`tmReadN`), the lookup-multiplicity reads, the
`Permutation.readProductCommitments` reads, the lookup commitment reads, and the
trashcan reads all append `replicate n g1` in that order; their total is the
plan's `prefixG1Count` minus `readAlgebraQuotientCount`. For (2): the
`constructIntermediateSets` point-set count at the linearized query vector is
the protocol's `numPointSets` under `ChallengesGood.xNonzero`.

## Gates

```
#cone_sorries Midfall.LoweringV3.end_to_end_of_A6_KZG     -- 2 (calldata upstream)
#cone_sorries Midfall.LoweringV3.end_to_end_of_tpEvents   -- 2 (calldata upstream)
#assert_axioms ... [propext, Classical.choice, Quot.sound, sorryAx] native []  -- ok
```

Targeted build used: `lake build Midfall.LoweringV3.EndToEndAlgebra`.

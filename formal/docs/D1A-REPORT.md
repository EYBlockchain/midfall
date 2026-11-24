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

## KZG increment: the width half closed, the count residual pinned

This increment closes the *width* half of `KzgMultiPrepareWidths` and pins the
remaining count obligation exactly.

PROVED (targeted `lake build Midfall.LoweringV3.EndToEndAlgebra`, no new sorry):

* `PresWidthSeq.multiPrepare_width` (already present): every `multiPrepare` run
  with `constructIntermediateSets … queries = .ok (cm, pointSets)` appends
  `[g1] ++ replicate pointSets.size fr ++ [g1]`.
* `KzgMultiPrepareWidths_of_pointSets`: `KzgMultiPrepareWidths R` follows from the
  point-set count equality at every query vector.
* `KzgMultiPrepareWidths_of_kzgPartitionBridge`: the same, consuming the existing
  named `KzgPartitionBridge` and the generator's `pointSets.length = plan.numPointSets`.
* `multiPrepare_width_at`: the per-query form — for a query vector whose
  `constructIntermediateSets` result has the plan's count, the width block is exact.
* `multiPrepare_constructIntermediateSets_ok`: a successful `multiPrepare` run implies
  `constructIntermediateSets` succeeded.

W12 FINDING (in the tree): `MultiPrepareBlockWidth`'s `∀ queries` form is FALSE at
the EMPTY query vector, independently of `x = 0`:

* `constructIntermediateSets_empty`: the empty construction gives `#[]` point sets;
* `multiPrepare_width_empty`: the empty run appends only the two `g1` widths;
* `MultiPrepareBlockWidth.eq_zero_of_empty_run`: a successful empty run forces
  `n = 0`;
* `pointSetsCount_forces_zero`: any uniform count premise is `0`.

So `KzgMultiPrepareWidths R` cannot be closed in its current `∀ queries` shape for
a deployed plan (`numPointSets > 0`). The true residual is the count equality at
`Verifier.linearize`'s query vector, under `ChallengesGood.xNonzero` + `omega`
order `n` + D-GATE6 rotation-distinctness.

EXACT RESIDUAL (not duplicated here):

1. the port-audit query-map bridge: `KzgPartitionBridge`
   (`LoweringV3/EndToEnd.lean:880`) is STATED but has no proof, and no theorem
   identifies `linearize`'s queries with the generator's `Generator.Query` list
   (the per-index slot/rotation correspondence);
2. the generator-side count identity
   `Generator.constructIntermediateSetsImpl queriesG.pointSets.length =
   plan.numPointSets` for the plan's query list;
3. the value→shape count lemma for `constructIntermediateSets` (equality pattern
   determines the point-set count), which with (1) turns the concrete count into
   `CircuitIndex.numPointSets`.

The consumer-side repair, when (1)–(3) land, is to replace the `hMulti` argument of
`verifyAlgebraicConstraints_width`/`PrepareLogSlots_of_parsed` with the per-query
form `multiPrepare_width_at` at the linearized queries.

## D-GATE10 repair: the KZG residual is now per-`linearize`

The `∀ queries` shape described above is SUPERSEDED. The consumer chain is
repaired to the query vector `Verifier.linearize` actually produces:

* `MultiPrepareBlockWidthAt g1 pcs n queries` — the per-query width obligation
  (exactly `PresWidthSeq ([g1] ++ replicate n fr ++ [g1]) (pcs.multiPrepare queries)`).
* `MultiPrepareWidthsLinearize …` — the same at every output of
  `linearize` (quantified over the algebra-read state and the linearize equation).
* `KzgMultiPrepareWidths R` is now THAT form (per `inst`/`trace`), not `∀ queries`.
* `verifyAlgebraicConstraints_width`, `PrepareLogSlots_of_parts`,
  `PrepareLogSlots_of_counts`, `PrepareLogSlots_of_counts'`,
  `PrepareLogSlots_of_parsed` and `PrepareLogSlots_of_A6_KZG` all take the
  per-linearize hypothesis; `readAlgebra_multiPrepare_widths` is also per-query.
* `MultiPrepareBlockWidthAt_of_pointSets` proves the per-query obligation from the
  point-set count, and `KzgMultiPrepareWidths_of_pointSets` /
  `KzgMultiPrepareWidths_of_kzgPartitionBridge` reduce `KzgMultiPrepareWidths` to
  the count at `linearize` / to the existing named `KzgPartitionBridge`.

The old `MultiPrepareBlockWidth` (`∀ queries`) is kept ONLY as the W12 object:
`MultiPrepareBlockWidth.eq_zero_of_empty_run` and `pointSetsCount_forces_zero`
show it cannot hold for `numPointSets > 0`.

EXACT remaining input (unchanged, and not duplicated here):

1. the query-map bridge `linearize`'s queries ↔ `Generator.Query` per index
   (slot + rotation correspondence); `KzgPartitionBridge` is stated in
   `LoweringV3/EndToEnd.lean` but has no proof;
2. the generator-side `Generator.constructIntermediateSetsImpl queriesG.pointSets.length
   = plan.numPointSets`;
3. the value→shape count lemma for `constructIntermediateSets` (under
   `ChallengesGood.xNonzero`, `omega` order `n`; D-GATE6 rotation-distinctness).

## D-GATE10 follow-up: the query-map bridge is proved at the KZG level

`Midfall/LoweringV3/KzgQueryMap.lean` now contains the verifier↔generator
query-map bridge; `Midfall/LoweringV3/EndToEndAlgebra.lean` consumes it.

PROVED (targeted builds `Midfall.LoweringV3.KzgQueryMap`,
`Midfall.LoweringV3.EndToEndAlgebra`, `Midfall.LoweringV3.EndToEnd`; no `sorryAx`
in any new declaration):

* `KzgQueryMapData` — the per-index correspondence: a common commitment key
  `K`, a point-to-rotation map `fk`, and the equality-reflection facts
  `eqC a b = (ck a == ck b)`, `ecPointBeq a b = (gk a == gk b)`,
  `(a == b) = (fk a == fk b)`, plus `L` whose two projections are the two query
  lists.
* `pass1_step1_sim` — the two step-1 folds of `constructIntermediateSets` and
  `constructIntermediateSetsImpl` run in lockstep: the first-occurrence point
  lists agree under `fk`, the commitment groups agree under `ck`/`gk`, and the
  per-group point-index lists are equal and duplicate-free.
* `natSort_eq_btreeSetFromList_of_nodup` — the verifier's insertion sort and the
  generator's BTreeSet fold are the same canonical form on duplicate-free lists
  (with `natSort_mem`, `btreeSetFromList_mem` and the sortedness/nodup lemmas).
* `foldl_addKeyFind_length_eq_btreeMap` — the two set-deduplicating folds have
  the same length (the `pointsV`/`pointsG` grouping), so the point-set counts
  agree.
* `constructIntermediateSets_pointSets_size_eq_of_queryMap` — the direct count
  equality `pointSets.size = setsG.pointSets.length` from `KzgQueryMapData`.
* `KzgPartitionBridge_of_queryMap` — the named `KzgPartitionBridge` from the
  same datum; `KzgMultiPrepareWidths_of_queryMap` — `KzgMultiPrepareWidths R`
  from a per-`linearize` datum plus the generator count.
* Generator side: `constructIntermediateSetsImpl_pointSets_length` (the
  `pointSets` fold over `pointIdxSets` preserves length),
  `sortSets_pointSets_length`, and
  `numPointSets_eq_of_queries_pointSets_length`
  (`numPointSets meta data = .ok sets.pointSets.length` from a successful
  `queries`/`constructIntermediateSetsImpl`/`sortSets` chain).

EXACT remaining input (unchanged in kind, now isolated to one datum):

1. Construct `KzgQueryMapData` at `Verifier.linearize`'s output against
   `Generator.queries R.plan.meta_ R.plan.data`: the per-index slot/rotation
   correspondence, including the `.linear` linearization commitment
   (`data.computedQuotientComm`) vs the verifier's `CommitmentReference.linear`,
   and the `.onePiece` slots. D-GATE5 `ChallengesGood.xNonzero` and D-GATE6
   rotation-distinctness supply the injectivity of `fk` (`x·ω^r = x·ω^s ⇒ r=s`)
   that makes the point equality reflection provable.
2. The plan-side count: from `PlanMeta`/`PlanMetaStable` (CertProbes) and
   `metaDataForVk`'s `setNumPointSets`, identify
   `R.plan.meta_.numPointSets` with the generator count above, and
   `(RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets`
   with `R.plan.proofLayout.qEvals.itemCount` (`fromProtocol_qEvals_itemCount`).
3. The linearize query list itself: proving `Verifier.linearize` produces
   exactly the `collectQueries` shape (already the real function, so this is a
   definitional unfolding plus the fixed/linearization order), and the
   generator `queries` list's order from `ProtocolPlan.fromConstraintSystem`.

W12 remains the falsifier of the old unconditional form:
`kzgPartitionBridge_false_at_x0` stays green, and the `∀ queries` statement is
kept only as the refuted object (`MultiPrepareBlockWidth.eq_zero_of_empty_run`).

## D-GATE10 datum increment: rotation injectivity, linearization entry, plan count

This increment lands the three named sub-lemmas requested for the datum, and
records the one interface obstruction that prevents the full merged
`KzgQueryMapData` from being constructed as stated.

PROVED (targeted `lake build Midfall.LoweringV3.RotationInjectivity
Midfall.LoweringV3.LinearizeEntry Midfall.LoweringV3.KzgQueryMap
Midfall.LoweringV3.EndToEndAlgebra Midfall.LoweringV3.EndToEnd`; new
declarations have no `sorryAx`):

* `Midfall/LoweringV3/RotationInjectivity.lean`
  - `rotateOmega_eq_mul_zpow`: `rotateOmega x (Rotation.value z) = x * omega^z`
    (using `powVartime_eq_pow`; `omegaInv * omega = 1` gives the negative-exponent
    case).
  - `rotateOmega_injective_on_rotations`: for `x ≠ 0` (D-GATE5
    `ChallengesGood.xNonzero`), `omega` of exact order `n` (D-GATE6's
    `EnvAgrees.omegaOrder`), and rotation-distinctness
    `r ≡ s [ZMOD n] → r = s` (D-GATE6), equal rotation-image points force
    `r = s`. The proof goes through `Units.mk0 omega`, Mathlib's
    `zpow_eq_zpow_iff_modEq`, and `orderOf_eq_iff`.
  - `rotationKey`/`rotationKey_injective`/`exists_pointKey`: the global
    extension of the rotation key. On the rotation image it returns the
    rotation; off the image it returns `N + ZMod.val q`, with `N` above every
    `|rotation|`. The two ranges are disjoint, so the key is injective and
    satisfies the global `(a == b) = (fk a == fk b)` obligation of
    `KzgQueryMapData`, while still sending each rotation-image point to its
    rotation. This closes the `fk` half of the datum.
* `Midfall/LoweringV3/LinearizeEntry.lean`
  - `collectQueries_back?`: the last query `collectQueries` emits is exactly the
    supplied `linCom`.
  - `VerifierQuery.newLinear_point` and
    `computeLinearizationCommitment_point`: `computeLinearizationCommitment`
    builds its query at point `x` (with label `custom "linearization_poly"` and
    a `.linear` commitment).
  - `linearize_back?_point`: the last query `linearize` emits has point
    `alg.x`.
* Plan count:
  - `plan_numPointSets_eq_meta`: the repacked layout's `numPointSets`
    (`proofLayout.qEvals.itemCount`) equals `R.plan.meta_.numPointSets`
    (`newFromVk_meta_layout` + `fromProtocol_qEvals_itemCount`).
  - `intermediateSets_parts` / `numPointSets_parts`: inversion of
    `intermediateSets`/`numPointSets` into `queries` →
    `constructIntermediateSetsImpl` → `sortSets`.
  - `planMeta_numPointSets_generator`: from `PlanMeta R` and the `Data.new`
    initialiser (`dummyEvalWords = []`), the generator's
    `queries`/`constructIntermediateSetsImpl`/`sortSets` chain exists and
    `R.plan.meta_.numPointSets` is its `sortSets` point-set count.
  - `numPointSets_eq_of_queries_pointSets_length` (previous increment) closes
    the reverse direction.

EXACT RESIDUAL AND INTERFACE OBSTRUCTION:

1. **The merged `KzgQueryMapData.hCommEq` is a global allocation-map
   obligation, not a consequence of the per-index correspondence.**
   `kzgCommitBeq` compares `.onePiece` by `CommitSlot` alone (`onePiece s _`)
   and `.linear` by `(points, scalars)` (labels ignored); the generator's
   `ecPointBeq` compares memory pointers. A global `ck` must therefore be a
   tagged key: `.onePiece s _ ↦ inl s`, `.linear p sc _ ↦ inr (p, sc)`, and
   `gk` must assign each paired generator pointer the same key. This is
   constructible only after proving the allocation map: no generator pointer is
   paired to two distinct slot keys at once (the committed-instance columns all
   share `G1_IDENTITY_MPTR`, so aliasing must be ruled out on the actual query
   list), and the linearization `.linear` key is assigned to `computedQuotientComm`.
   The counting simulation needs equality reflection only on the commitments
   that occur in the two query tails, so the natural next step is the
   **local/relational** form of `hCommEq`/`hGCommEq`, or this tagged global
   map plus the no-alias proof.
2. **The linearization entry is `.linear` on the verifier side but `.onePiece`
   on the generator side.** `linearize_back?_point` lands the point/order half;
   the remaining half is that the `.linear` points/scalars/labels equal the
   generator's `data.computedQuotientComm` entry (and its eval). Under (1), this
   is naturally a per-entry relation, not a global `ck` equality.
3. **`fk` instantiation.** The global key is proved (`exists_pointKey`). What
   remains is to choose the finite `rots` list from `linearize`'s query vector
   and supply D-GATE6's rotation-distinctness for that list; the field-algebra
   core and the off-image injection are both landed.
4. **Plan-side `hdummy`.** `planMeta_numPointSets_generator` takes
   `R.plan.data.dummyEvalWords = []`; `Data.new` initialises it empty, but the
   projection from `PlanMeta`'s `Data.new` equation to that fact is not yet a
   named lemma. `PlanMeta` itself is not a field of `ValidV3` (it is a measured
   candidate in `CertProbes`), so the final plan count remains conditional on
   `PlanMeta`/`PlanMetaStable`.

W12 remains green (`kzgPartitionBridge_false_at_x0`); no statement was weakened
and no row/bundle/root gained a hypothesis.

## Local/relational `KzgQueryMapData` (supersedes the global key fields)

The global `hCommEq`/`hGCommEq` fields of the merged datum were the wrong
interface for the real verifier (`kzgCommitBeq` compares `.onePiece` by slot,
`ecPointBeq` by pointer). The datum is now **tail-local**:

* `KzgQueryMapData.hCommEq`, `hGCommEq`, `hPointEq` quantify only over pairs in
  the datum's paired list `L` (not over all `CommitmentReference`s/`EcPoint`s).
* `pass1_step1_sim` takes the same local hypotheses plus an explicit
  `pre`/`suffix` split (`L = pre ++ suffix`) and provenance of the verifier's
  `cms`/`gs`/`pts` state in `L`. The provenance is maintained per step; the
  counting theorem starts at `pre = []`, `suffix = L`, empty state.
* The counting theorem `constructIntermediateSets_pointSets_size_eq_of_queryMap`
  and the consumers `KzgPartitionBridge_of_queryMap` /
  `KzgMultiPrepareWidths_of_queryMap` are unchanged in statement but now consume
  the local fields.

CONSTRUCTORS LANDED:

* `findIdx?_eq_of_equiv`: the first-index characterization of an equivalence
  relation on a list (`r a b = (idx a == idx b)`), used to turn per-tail
  equivalence classes into keys.
* `KzgQueryMapData.ofList`: builds the local datum with `K := Option Nat`,
  `ck a := L.findIdx? (eqC a ·.commitment)`, `gk c := L.findIdx? (ecPointBeq c ·.comm)`.
  It proves `hpairC` from `hclass` by pointwise predicate equality, and
  `hCommEq`/`hGCommEq` from the restricted reflexivity/symmetry/transitivity
  facts. `hPointEq` is the global point-key equality.
* `KzgQueryMapData.ofRotations`: instantiates `ofList` with the global
  `exists_pointKey` rotation key. Inputs are the actual point/rotation relation
  (`hpairPoint`), the rotation-list membership (`hrot`), and the per-tail
  `hclass`/equivalence data. `Data.new_dummyEvalWords` is proved, and
  `planMeta_numPointSets_generator` no longer takes `hdummy`.

EXACT remaining datum inputs for one `linearize` output:

1. the paired list `L` and its two projections: the `linearize` query vector
   and `Generator.queries R.plan.meta_ R.plan.data` in the same order
   (`collectQueries` order vs `ProtocolPlan.fromConstraintSystem` order);
2. `hpairPoint`: `qV.point = x·ω^qG.rotation` for every pair;
3. `hclass` and the equivalence facts for `kzgCommitBeq`/`ecPointBeq` over `L`.
   The `.linear`-vs-`computedQuotientComm` entry is the remaining per-entry
   identity: `kzgCommitBeq` on the verifier's `.linear` query must match
   `ecPointBeq` on the generator's `computedQuotientComm`, and the
   committed-instance aliasing (`G1_IDENTITY_MPTR`) must be absent from the
   actual query list. `ofList` consumes exactly these facts; it does not assume
   them globally.

## Concrete pairing increment

Landed (targeted builds; `#assert_axioms` green):

* `pairQueries` = `queriesV.toList.zip queriesG`; `pairQueries_fst` /
  `pairQueries_snd` prove the two projections are the actual lists once
  `queriesV.size = queriesG.length`. This is the mechanical `L` construction.
* `QueryTail.mapM_getLast?_some`, `queries_mapM_ok`, `queries_getLast?_some`:
  on success, `Generator.queries`'s last output is the last source's
  `queryFromPlan` result. `queries_last_rotation` then gives rotation `0` for
  the tail when `meta_.protocol.pcsQueries.getLast? = some .linearization`.
* `VerifierQuery.newLinear_commitment` and
  `computeLinearizationCommitment_commitment`: the last `linearize` query is a
  `.linear` commitment. Together with `linearize_back?_point` (point `alg.x`),
  the tail pair satisfies the point/linearization half of `hpairPoint` and the
  `.linear` half of the last per-entry identity.

Exact residual for the concrete pairing:

1. Same-order/count correspondence: `queriesV.size = queriesG.length` and the
   per-index order theorem from `collectQueries` to
   `ProtocolPlan.fromConstraintSystem` (`pcsQueries`). The `pairQueries`
   projections only need the length; the actual `hpairPoint` needs the order.
2. `hpairPoint` for every pair: the verifier point is
   `vk.domain.rotateOmega x rotation` from `collectQueries`; the generator
   rotation is `PcsQuerySource.rotation`. `LinearizeEntry` supplies the last
   entry; the per-entry shape lemma (advice, committed instance, permutation,
   lookup, trash, fixed, sigma, linearization) is the main remaining piece.
3. `hclass` and the restricted equivalence facts; the `.linear`-vs-
   `computedQuotientComm` entry and the absence of `G1_IDENTITY_MPTR` aliasing
   on the actual query list. `KzgQueryMapData.ofList`/`ofRotations` consume
   exactly these facts; they are not assumed globally.
4. `fromConstraintSystem_pcsQueries_last` is not yet a theorem: the plan's
   `pcsQueries` literal ends in `[.linearization]`, but extracting it from the
   successful `validate` match requires inverting the long
   `fromConstraintSystem` do-block. `queries_last_rotation` takes the source-end
   fact as a hypothesis until that projection is landed.
5. `PlanMeta` remains a named conditional. It is **not** a `ValidV3` field:
   `ValidV3.generated` gives `GeneratedBy`, not the `PlanMeta` data/meta
   equation. The closest landed pieces are `CertProbes.PlanMetaStable` and its
   `planMeta_of_stable`; the `v3_planMeta` target in
   `Generator/Certified.lean` is still a `sorry` (`CERT.1`), and the missing
   clause is the data equation on the final memory (the intermediate-vs-final
   layout stability).

## Per-source generator rotation lemmas

Landed in `QueryTail` (all `#assert_axioms` green):

* `queryFromPlan_advice_rotation`, `queryFromPlan_committedInstance_rotation`,
  `queryFromPlan_fixed_rotation`: the generator rotation is the source
  `QueryKey.rotation`.
* `queryFromPlan_lookupMultiplicity_rotation`,
  `queryFromPlan_lookupHelper_rotation`, `queryFromPlan_trash_rotation`,
  `queryFromPlan_permutationCommon_rotation`: the generator rotation is `0`.
* `queryFromPlan_linearization` + `PcsQuerySource.rotation_linearization`:
  the linearization source is rotation `0` at `computedQuotientComm`.

These are the generator half of the per-entry `hpairPoint` shape. The remaining
generator sources are `permutationZ` (rotation `0`/`1`/`rotationLast`) and
`lookupAccumulator` (rotation `0`/`1`/panic); both need the inner
`PermutationZEval`/`Int` match in the `queryFromPlan` do-block.

The verifier half is the same-order shape theorem: `collectQueries`'s advice,
instance, permutation, lookup, trash, fixed, common and linearization blocks
against `pcsQueries`'s source order. `pairQueries`/`pairQueries_fst/_snd` already
build the zipped list once the sizes agree; the per-index block theorem is the
remaining priority-2 input. `hclass`/`G1_IDENTITY_MPTR` freshness remains
priority 3, and `fromConstraintSystem_pcsQueries_last` remains the single named
`match`-wrapper residual.

## Generator rotation half closed; verifier decomposition and tail shape

Landed and green:

* `queryFromPlan_permutationZ_rotation` — `0` for `Cur`, `1` for `Next`,
  `rotationLast` for `Last` (the `some` branch; the `none` branch is a panic).
* `queryFromPlan_lookupAccumulator_rotation` — `rotation` for `0`/`1`, panic
  otherwise.
  With the seven prior source lemmas, all ten `PcsQuerySource` constructors now
  have their generator rotation identified with
  `PcsQuerySource.rotation rotationLast`.
* `collectQueries_parts` — a successful `collectQueries` list is
  `perProof.flatten ++ fixed ++ common ++ [linCom]`. This names the verifier-side
  block decomposition for the same-order theorem.
* `rotateOmega_zero` and `linearize_back?_point_rotateOmega` — the last
  `linearize` query point is `vk.domain.rotateOmega alg.x (Rotation.value 0)`.

Remaining for the full same-order theorem: the per-block equality of
`perProof`/`fixed`/`common` against `pcsQueries`'s advice/instance/permutation/
lookup/trash/fixed/common sources, plus the per-index `rotateOmega` point shape
inside each block. `pairQueries` supplies the zipped `L` once the sizes agree.
`hclass`/`.linear`-vs-`computedQuotientComm`/`G1_IDENTITY_MPTR` freshness remains
the priority-3 input. `fromConstraintSystem_pcsQueries_last` remains the single
named `match`-wrapper residual; `PlanMeta`/`v3_planMeta` remains CERT.1 and is
not assumed.

## Same-order block point shapes

Landed in `QueryBlockShape` (green, `#assert_axioms`):

* `Trash.Evaluated.queries_point` — every trash query opens at `x`.
* `Permutation.CommonEvaluated.queries_point` — every common sigma opening
  opens at `x`.
* `Logup.Evaluated.queries_point` — every logup query opens at `x` or at
  `domain.rotateOmega x Rotation.next`.

These are the verifier-side `rotateOmega` shapes for the trash, common and
lookup blocks. The remaining block shapes are advice, committed instance,
permutationZ and fixed; each needs the `mapM`/zip membership inversion from
`collectQueries`. The same-order list equality itself (perProof/fixed/common
against `pcsQueries`) then follows block by block once those four shapes and
the `pcsQueries` block decomposition are available.

`pairQueries` already builds the zipped list once the sizes agree.
`hclass`/`.linear`-vs-`computedQuotientComm`/`G1_IDENTITY_MPTR` freshness remains
priority 3; `fromConstraintSystem_pcsQueries_last` and `PlanMeta` remain the
named residuals.

## Fixed-block verifier shape; PlanMeta discharged on main

Merged `origin/formal/baseline` (PlanMeta/CERT.1 closure; `v3_planMeta` is now
`MemoryPairs.planMeta_of_generated`). Added:

* `planMeta_numPointSets_generator_of_validV3` — the KZG plan-count chain at
  `ValidV3`, consuming `MemoryPairs.planMeta_of_generated hR.generated` (the
  main lane also provides `planMeta_numPointSets_of_validV3`).
* `mem_mapM` — membership extraction for a successful `List.mapM`.
* `fixedQueryFn_point` — every query built by the fixed block has point
  `vk.domain.rotateOmega x q.2.2`.
* `collectQueries_fixed_point` — the fixed block's queries all have point
  `vk.domain.rotateOmega x r`, and the fixed block sits in the
  `perProof.flatten ++ fixed ++ common ++ [linCom]` decomposition.

Remaining verifier block shapes: advice, committed instance, permutationZ. Each
needs the per-proof `perProof`/inner-`mapM` decomposition (`adv.flatten`,
`inst.flatten`, `perm.toList`); `fixed` is the first complete block because it
is a direct `mapM`. The same-order list equality against `pcsQueries` is then a
block-by-block comparison. `hclass`/`.linear`-vs-`computedQuotientComm`/
`G1_IDENTITY_MPTR` freshness remains priority 3.

## Advice and committed-instance block point shapes

Landed in `QueryBlockShape`:

* `adviceQueryFn_point` / `instanceQueryFn_point` — a single advice/instance
  query block entry has point `vk.domain.rotateOmega x q.2.2`.
* `adviceQueryFn_mem` / `instanceQueryFn_mem` — the same for any member of the
  returned singleton block (instance's non-committed branch is `[]`).
* `adviceBlock_point` / `instanceBlock_point` — using `mem_mapM` and
  `List.mem_flatten`, every query in `adv.flatten` / `inst.flatten` has point
  `vk.domain.rotateOmega x r` for some rotation.

With `collectQueries_fixed_point`, `Trash.Evaluated.queries_point`,
`Permutation.CommonEvaluated.queries_point` and `Logup.Evaluated.queries_point`,
the verifier point shapes now cover advice, committed instance, fixed, trash,
common and lookup. Remaining: the `permutationZ` block point lemma (head
`x`/`xNext`, tail `xLast`) and the `perProof` append decomposition
(`adv.flatten ++ inst.flatten ++ perm.toList ++ lk ++ tr`) that lifts the inner
block lemmas to `perProof.flatten`. The same-order equality against `pcsQueries`
then follows block by block; `hclass`/`.linear`/`G1_IDENTITY_MPTR` freshness
remains priority 3.

## pcsQueries exposed; permutationZ order is the same-order blocker

`PcsOrder.pcsBlockList` / `pcsBlocks` transcribe the literal
`ProtocolPlan.fromConstraintSystem` PCS schedule as eight blocks
(advice, committed instance, permutationZ, lookup, trash, fixed, permutation
common, linearization). `fromConstraintSystem_pcsQueries` proves the plan field
is exactly that list; the final `match plan.validate` is split, not inverted.
So the old `fromConstraintSystem_pcsQueries_last` residual is closed as a
special case (the generic `pcsQueries_append_linearization_last` is now
redundant but harmless).

On the verifier side, `collectQueries_single_blocks` gives the one-proof
eight-block spine
`adv.flatten ++ inst.flatten ++ perm.toList ++ lookup ++ trash ++ fixed ++ common ++ [linCom]`,
matching `pcsBlocks` in block order. `queries_pcsBlocks` splits a successful
`Generator.queries` into one query list per PCS block, in `pcsQueries` order.

**The remaining same-order obstacle is permutationZ, and it is not a proof
gap but an order difference.** `Permutation.Evaluated.queries`
(`Halo2/Exec/Permutation.lean:265-290`) emits the `cur/next` openings for every
set first, then `.enumerate().rev().skip(1)` last-row openings in DESCENDING
set order. `pcsPermutationZ` (`Generator/Protocol.lean:733-738`) interleaves
per set: `[cur, next, last]`, `[cur, next, last]`, ..., `[cur, next]`. The
deployment has `numPermutationZs = 3` (`Instances/DeployedProfile.lean:87`), so
the two lists are literally different. The generator already knows this:
`assertPermutationQueryOrderIsUpstreamEquivalent` (`Generator/Kzg.lean:628-665`)
rebuilds the sources in upstream order
(`(filter curOrNext) ++ reverse (filter last)`, KZ:159-186), maps
`queryFromPlan` over them, and checks that the point sets and commitments agree
with the generator order.

The order algebra is now PROVED: `permZBlock`/`permZUpstream` pin the two
three-set lists (`permZBlock_three`, `permZUpstream_three`,
`permZBlock_three_beq_upstream`), and `upstreamBlock_permZBlock` proves that
filtering the generator block to `cur/next`, reversing its `last` openings, and
concatenating gives exactly `permZUpstream` - the verifier's
`head.flatten ++ tail.flatten` order. `upstreamBlock` is the `KZ:159-186`
reordering.

The upstream-check inversion is now landed as well:
`assertPermutationQueryOrderIsUpstreamEquivalent_parts` (in `UpstreamSets`)
exposes, from a successful check with nonempty z positions, the upstream source
list, its `queryFromPlan` map, both `constructIntermediateSetsImpl` successes,
and `generatorSets.pointSets = upstreamSets.pointSets`.

The remaining same-order step is to identify the z slice of
`upstreamSources` with `permZUpstream` (the source list is built by
`listSetMut` at the consecutive `zPositions`; `upstreamBlock_permZBlock`
already gives the order equality), then pair the verifier list with that
upstream list (not with raw `Generator.queries`).
`KzgQueryMapData`'s `hVlist`/`hGlist` force this: `L.map Prod.fst` and
`L.map Prod.snd` cannot simultaneously be two different orders. A literal
same-order theorem against raw `pcsQueries` is false for this deployment.

## hclass / linearization residual

Not started. `kzgCommitBeq` compares `.onePiece` by `CommitSlot` and `.linear`
by points/scalars (`Halo2/Exec/Kzg/MultiOpen.lean:46-53`), while generator
equality is `ecPointBeq` on `EcPoint` pointers
(`Generator/Kzg.lean:281`). For the linearization pair, verifier-side
self-equality is true and generator-side self-equality is true, so `hclass`
holds on the diagonal; the off-diagonal `linearization` vs any one-piece query
needs `computedQuotientComm`'s pointer to be distinct from every other
commitment pointer (`G1_IDENTITY_MPTR` freshness). This is a concrete freshness
obligation on `Data`, not a list-order one.

## KZG datum: upstream slice and quotient freshness

The upstream permutationZ slice is now PROVED.  `upstreamSources_zslice` and
`upstreamSources_filter_pcsBlockList` compose the generic list plumbing
(`filterMap_zip_range_append_block`, `mapM_get_consecutive`,
`foldlM_set_consecutive`, `permZBlock_ztrue`, the z-free block facts, and
`pcsBlockList_eq_permZ`) with the upstream-check inversion.  On a successful
`assertPermutationQueryOrderIsUpstreamEquivalent` with a literal `pcsQueries`
and nonempty z positions, the exposed `upstreamSources` satisfies

`upstreamSources.filter isPermutationZSource = permZUpstream numPermutationZs`.

`KzgQueryMapData.ofPairQueries` is the paired-list constructor: it sets
`L = pairQueries queriesV queriesG` and uses `pairQueries_fst/_snd` to supply
`hVlist`/`hGlist` from the length equality.  The remaining per-pair point and
commitment facts are still inputs; the list-projection obligation is closed.

For the linearization `hclass` case, `QuotientFresh` proves the concrete
freshness data.  `Data.new_computedQuotientComm` pins the quotient commitment
to the symbolic `QUOTIENT_MPTR`; `Data.new_commsNumericOrIdentity` proves every
other commitment array of `Data.new` is numeric, except
`committedInstanceComms`, which is the shared `G1_IDENTITY_MPTR` sentinel.
`VerifierMemoryLayout.new_numericBases` supplies the layout half from
`vkMptr.Numeric`.  `ecPointBeq_quotient_of_numeric` and
`ecPointBeq_quotient_g1` prove the quotient pointer is distinct from those
commitments, and `queryFromPlan_comm_classification` classifies every queried
generator commitment as quotient, numeric, or G1 identity.

The linearization hclass cases are formal:
`kzgCommitBeq_linear_self_eq` covers the diagonal (verifier `.linear`
self-equality equals generator quotient-pointer self-equality), and
`kzgCommitBeq_linear_offdiag` covers the off-diagonal case from the
classification and freshness.  The remaining assembly is to instantiate these
at the actual `linearize`/`Generator.queries` pair and connect the
`queryFromPlan` source to the verifier `.linear` linearization query.

## Final-datum assembly progress

Landed on top of the upstream slice:

* `upstreamSources_zslice`/`upstreamSources_filter_pcsBlockList` now return the
  whole source-list equation
  `upstreamSources = pre ++ permZUpstream numPermutationZs ++ post`, not only
  its z filter.  This is the block alignment the final pairing consumes.
* `exists_pairQueries`: with equal lengths, `pairQueries` is the list whose two
  projections are the two query lists.  `KzgQueryMapData.ofPairQueries` is the
  corresponding datum constructor.
* `queryFromPlan_comm_numericOrG1_of_ne_linearization` and
  `queryFromPlan_comm_ne_quotient`: a non-linearization source never yields the
  quotient pointer.  Together with the Data predicate this is the source-level
  freshness fact.
* `RenderFresh.plan_data_commsNumericOrIdentity`: from `GeneratedBy`,
  `plan_memory_eq_new`/`vkMptr_shape_of_generated` supply `vkMptr.Numeric`, then
  `VerifierMemoryLayout.new_numericBases` and
  `Data.new_commsNumericOrIdentity` give `R.plan.data.CommsNumericOrIdentity`.
* `KzgMultiPrepareWidths_of_upstreamDatum`: the named consumer for the final
  assembly, taking the upstream source list, its `queryFromPlan` map, the
  generator sets, and a `KzgQueryMapData` at the verifier/upstream list.

Remaining exact work:

1. Instantiate `KzgQueryMapData.ofPairQueries` at the actual `linearize`
   output and the upstream query list; this needs the query-list length
   equality and the per-index `hpairP`/`hpairC`/`hclass` facts.
2. Discharge `hpairP` block by block: the verifier block shapes and the
   `queryFromPlan_*_rotation` lemmas are available; the missing piece is the
   query-level block alignment between `collectQueries_single_blocks` and the
   upstream source-list equality.
3. Discharge `hpairC`/`hclass` block by block: this is the allocation
   correspondence `CommitSlot` ↔ `EcPoint` pointer.  The linearization
   diagonal/off-diagonal cases are proved in `QuotientFresh`; the advice,
   instance, permZ, lookup, trash, fixed and common one-piece cases still need
   the slot/pointer map.
4. Feed the resulting datum to `KzgMultiPrepareWidths_of_upstreamDatum` and the
   existing `EndToEnd` consumer.

## Complements landed (D1 assembly)

The plan/count and mapM halves of `LinearizeQueryMap` are now proved:

* `pointSets_length_eq_plan_of_queryMap`: from the per-query `KzgQueryMapData`,
  the Halo2 point-set count, and the generator's `queries` result, the
  generator's upstream point-set count is the plan's `numPointSets`.
  `setsG_pointSets_length_eq_plan_of_generator` is the Halo2-free form the
  assembly consumes.
* `upstreamDatum_of_validV3`: `ValidV3` + the minimal key-side clause
  `PermutationColumnsNonempty` gives the A5 upstream source block, the
  `queryFromPlan` map to `upstreamQueries`, the generator `queries` result, both
  set constructions, and the set equality. The z-position list, its nonemptiness
  and the `dg`/`lc` decomposition are derived (`pcsZPositions`,
  `pcsNumPermutationZs_pos_of_columns`, `plan_meta_pcsBlockList`). The
  `queries_assert_ok` bridge turns a successful `Generator.queries` into the I-6
  upstream check. The clause is not implied by `ValidV3`/`SupportedV2` (the
  empty permutation argument satisfies `permutationCommitmentsMatch`); the
  deployed poseidon profile observes eight columns.
* `LinearizeQueryMap_of_upstreamDatum` assembles `LinearizeQueryMap` once the
  per-pair datum supplies the upstream list, both set constructions, the
  point-set equality and the `KzgQueryMapData`;
  `end_to_end_of_validV3_of_upstreamDatum` is the final consumer.

The remaining per-pair inputs are exactly the `hpairP`/`hpairC`/`hclass` facts
of `KzgQueryMapData`, plus the generic key-side clause
`PermutationColumnsNonempty`; neither is a row, bundle or root hypothesis.

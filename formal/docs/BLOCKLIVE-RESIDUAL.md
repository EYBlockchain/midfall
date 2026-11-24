# BlockLive case residuals (measured)

**Ticket:** close `block_live_case_{transcriptParser,lagrange,quotientLin,pcs}` in
`Midfall/LoweringV3/BlockLive.lean` without weakening `block_live` or adding
`hacc`/`hcomp`. **Result:** all four remain open; no statement was weakened and no new
`sorry` was added. This file records the three routes that were checked and the exact
residual for each case.

The four declarations are, in `BlockLive.lean`:

```lean
block_live_case_transcriptParser (R) (product) (hR) (H) (vkAddr) (cd) :
  BlockLive R .transcriptParser H vkAddr product cd
block_live_case_lagrange (R) (product) (hR) (H) (vkAddr) (cd) :
  BlockLive R .lagrange H vkAddr product cd
block_live_case_quotientLin (R) (product) (hR) (H) (vkAddr) (cd) :
  BlockLive R .quotientLin H vkAddr product cd
block_live_case_pcs (R) (product) (hR) (H) (vkAddr) (cd) :
  BlockLive R .pcs H vkAddr product cd
```

## Route 1 - derive `hacc`/`hcomp` from `StageInv`

**Fails at the pre-checkpoint of every one of the four blocks, and the reason is
definitional, not a missing lemma.**

`BlockLive R q` starts at `LivePre R H vkAddr cd q.pre`:

| q | `q.pre` | `LivePre q.pre` | `LeanRaw` at that checkpoint |
|---|---|---|---|
| transcriptParser | .vk | `StageInv .vk` | `envelopeOk … = true` |
| lagrange | .transcript | `StageInv .transcript` | `rawDecode … |>.isSome = true` |
| quotientLin | .lagrange | `StageInv .lagrange` | `rawDecode … |>.isSome = true` |
| pcs | .quotient | `StageInv .quotient` | `rawDecode … |>.isSome = true` |

`LeanAccepts` needs a concrete `Decoded R cd ms instW inst` **and**
`verifyMsgs … = .ok ()`. `Agree` at the pre is conditional: it only says *for every
`Decoded`* the Lean stage exists. It does not produce a `Decoded`. For `.vk` even
`rawDecode` need not have succeeded. From `.transcript`/`.lagrange`/`.quotient`,
`rawDecode.isSome` still allows `decodeCalldata` to fail at `liftRaw`/`ofEip?`
(`Lowering/Stage.lean:134`); `PcsRows.decode_exists` needs exactly the missing premise
`hpts : ∀ b, RawG1 b ∈ raw → (ofEip? b).isSome = true` (`PcsRows.lean:220`), which no
`StageInv` clause supplies. `CompleteSide` is independent of all of them: it quantifies
the challenge values of a successful `snapshotOf`, and no `StageInv` clause pins those.

The suggested incomplete-case fallback also needs a run: `BlockSim` is forall-runs-only
(no existence), and `BlockProgS` is precisely the missing existence-plus-classification
row. There is therefore no case split that closes the four from `StageInv` alone.

## Route 2 - `BlockSim` + an existence run

`BlockSimAt`/`BlockSim` (`LoweringV2/Stages.lean:203,222`) are two `StmtsContractAll`
fields. They do not contain a `StmtsContract` existence field.

For **transcriptParser, lagrange, quotientLin**, the first `BlockSim` field also permits
the arm

```lean
q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'
```

(`Stages.lean`, `exitSimAt`/`BlockSimAt`). `BlockLive`'s post at `.transcript`,
`.lagrange` and `.quotient` is `StageInv`, which requires `success = 1`; a normal
poisoned exit does **not** satisfy it. So `BlockSim` alone is insufficient even if an
existence run is supplied, unless the block's poison arm is separately proved
unreachable under the honest `callsOf` relation.

For **pcs only**, the post is `LivePre .pcs = Mid .pcs = StageInv .pcs ∨ Poisoned`, so
the poisoned-normal arm *does* land in the allowed post. `block_live_pcs` uses the
stronger `BlockProgS`; a `BlockSim`-based variant would work for the classification
half, but it needs:

* `pcs_blockSim`, which lives in `Rows.lean` **above** `BlockLive` (`Rows` imports
  `Composition`, `Composition` imports `BlockLive`), so importing it here is a cycle;
* the existence half for `R.slice .pcs` from `StageInv .quotient`, which no module
  below `BlockLive` proves.

## Route 3 - the low-level PCS/lagrange contracts

* `PcsBlock4.pcsBlock_contract` (and its `pcsSetBlock_*` siblings) are **forall-only**
  `StmtContractAll`/`StmtsContractAll` contracts for a per-set `Stmt.block`; there is no
  whole-`R.slice .pcs` contract and no existential form.
* `LagrangeBlock.LagBlockContract` / `LagBlockPoisonContract` are **definitions**
  (`LagrangeBlock.lean:629,641`), not proved theorems. `LagInnerContract` /
  `LagInnerContractZero` are forall-only, and the module header records the remaining
  blockers: the whole-block composition needs A5 `batch_invert_summary` and the
  `lag_poison` arm.
* The whole-slice lagrange/pcs rows (`lag_blockSim`, `lag_blockProgS`,
  `pcs_blockSim`, `pcs_blockProgS`) are in `Rows.lean`, above `BlockLive`.

## Exact residual (what must land, and where)

| case | exact remaining obligation | owner / location |
|---|---|---|
| transcriptParser | an unconditional `BlockProgS R .transcriptParser …` (or the equivalent `StmtsTotal`/existence + all-runs classification) over `StageInv .vk`; `hacc`/`hcomp` are extra premises in the current rows | ROW.TP: `TranscriptRows.tp_blockProgS`, `Rows.tp_blockProgS` |
| lagrange | an unconditional progress/totality row over `StageInv .transcript`; `LagBlockContract` must be proved first, which needs A5 `batch_invert_summary` + the T3.9.f whole-block composition + `lag_poison` | A4: `Rows.lag_blockProgS`/`lag_blockSim` |
| quotientLin | an unconditional `BlockProgS R .quotientLin …` over `StageInv .lagrange`; the QVM existence through the numerator is the named `qvm_validated_noBoundsFault` / `builder_segments_total` lane, and `q_blockSim` additionally needs `SoundSide` | ROW.Q/QVM: `QuotientRows.q_blockProgS`/`q_blockSim` |
| pcs | an existence run for `R.slice .pcs` from `StageInv .quotient` plus `pcs_blockSim` (or the full `BlockProgS`); the PCS SEM blocks 1/3/4/5/6, PG-PCS-EMIT and the coverage invariant are still open | ROW.PCS: `Rows.pcs_blockProgS`/`pcs_blockSim`, `PcsRows` |

No root statement was weakened to obtain these conclusions: `block_live` is unchanged,
the four case rows remain the only open leaves in its cone, and `SORRY.md` is unchanged
by this investigation.

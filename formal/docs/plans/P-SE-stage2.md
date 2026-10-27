# P-SE stage 2 - `Lowering/{AccEncoding,Accumulator,VkDigest,Calldata}`

Status: READY - stage 1 confirmed stage 2 can start and is blocked by none of stage 1's
holes. It needs `Assumptions/Codec.lean`'s `G1CodecLaws`, which now exists.

**Tree**: 3405 jobs, 999 KATs across 56 files, 79 modules, 14 tracked sorries (all
owned). Stage 1 landed `83313c9` with Y-3 resolved and `Contracts.lean` at zero holes.

## Files

| file | content |
|---|---|
| `Lowering/AccEncoding.lean` | `toExec` + the D-P16 reconciliation (a)-(d) between the two `AccumulatorEncoding` types |
| `Lowering/Accumulator.lean` | `accWords`, `decodeAcc_*`, S5, the pairing lift, `ContractRefAcceptsAcc`, `contractRef_acc_complete` |
| `Lowering/VkDigest.lean` | `feToU256_frToRepr` - **imports `Encoding`, never `Generator.Vk`** |
| `Lowering/Calldata.lean` | `encodeContractProof`/`repackProof`/`decodeWire`/`encodeCalldata`/`calldataOf`/`decodeCalldata` + their specs |

## Two statements that are already known FALSE as written - do not restate them naively

1. **`decodeAcc_injective` is false** (R-25, review F4, annotated in PLAN 9.5 at the
   `decodeAcc_injective` line). The accumulator decoder IGNORES the coordinate words of
   an identity-flagged point, so distinct instance tails decode to the same accumulator.
   What is true is injectivity of **normalised** accumulator words. State it over
   `accWords` and say what normalisation is doing.
2. **`decodeAcc_encode` holds only for the collapsed `.pointAndScalar` shape.** The
   `.pointPair` round trip is FALSE - `encodeAccInstances` always emits carried scalars.
   Restrict the statement and record the restriction.

If you find a third statement in PLAN 9.5 or the P-SE sketch that is false as written,
**stop and report** (PLAN 12). Stage 1 found one such defect in `countdown_or_halt` and
corrected it by strengthening rather than weakening - that is the standard.

## One statement that got STRONGER, so take the win

P-12 measured that the contract calldata decoder is **EXACT** - trailing bytes revert,
instance words >= r revert, proof and q_eval words >= r revert, G1 words must be
canonical and self-re-encoding. That corrected PLAN 13's stale risk note and means
**`calldata_canonical` can be stated exactly as written**; P-SE decision D7 was right.
Do not carry the old `≈` fallback forward.

## Carry-over from stage 1

`frOfRepr_frToRepr` (`Assumptions/Codec.lean:100`) is a registered hole whose proof needs
two byte lemmas - `natToBytesLowFirst_size` and `bytesToNatLE_natToBytesLE` - that
`design1` M5-2 assigns to **this stage**. Land them here and close that hole, or say
precisely why not.

## Rules from the human - binding

1. Before each file read `P-SE-evidence/attack.md` and the matching `design*.md`.
   **attack FIX lines are binding** - FIX 40 concerns exactly this layer:
   `S.repackProof π |>.mapError GeneratorError.fromRepackError >>= (S.encodeCalldata L.plan · inst)`,
   plus hypotheses `hn : inst.size = S.cfg.numInstances` and `hp : p = Midfall.Assumptions.r`.
2. **Verify every `-- SKETCH` name** against `P-SE-evidence/survey.md` or `#check`. Stage
   1 found three that do not resolve (`ZMod.pow_card_sub_two_eq_inv`, the
   `Multiplicative (ZMod 17)` decide-by toy codec, and design0's `P.g₁` non-vacuity).
   Report any more rather than inventing them.
3. **Doc comments in the style of `Exec/Accumulator.lean`.**
4. **Register every hole in `SORRY.md` via `scripts/gen_sorry.sh`.** Owner arms exist.
5. **NEVER edit `Statements.lean`** - frozen, hash-checked.
6. **False as written: stop and report.**

## Hazards

1. **D-P16**: there are TWO `AccumulatorEncoding` types; PLAN 9.5 means the **Generator
   one**, not the Exec stand-in. The reconciliation needs the `n < 2^64 - 1` bound
   (saturating vs unbounded add). Get the direction of the bridge right or every
   accumulator statement below it is about the wrong type.
2. **D-P17**: no theorem-bearing file may import `Midfall/Instances/`. `VkDigest.lean`
   must import `Encoding`, never `Generator.Vk` - that is stated in the plan and it is a
   real constraint, not a style preference.
3. **`Register your modules`** in `Midfall.lean`; the orphan gate is a hard failure.
4. **`lake env lean` does not apply lakefile options** - numbers from `lake build` and
   `scripts/checks.sh` only.
5. **Re-measure inherited claims in both directions.** This session produced a false
   'live defect' claim, a false blocker claim, a missed-file planning error, and a
   half-applied edit that left a file uncompiled and unregistered.
6. **Multi-line anchored edits are dangerous here.** Stage 1's own file was left broken by
   one. Re-read the full region after each edit; rebuild before moving on.

**No idle builds.** If you run short on room, leave files compiling or unregistered -
never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, or another package's Lean file. Do NOT git add
or commit. `SORRY.md` only via `gen_sorry.sh`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 999 across 56 files.
- All four files registered, holes registered with owners.
- `frOfRepr_frToRepr` closed, or a precise reason it cannot be.
- **Required finding**: the list of PLAN 9.5 statements you found false as written
  (beyond the two already known), and whether stage 3 can start - noting that stage 3
  ALSO needs the D6 Exec refactor, which has not been done.

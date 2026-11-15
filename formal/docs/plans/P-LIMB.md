# P-LIMB - the single step that unblocks three of the four `decodeAcc_*` holes.

Status: READY. P-BYTES landed the byte mathematics and **named the next step precisely**. Use it.

## Step 1 (highest value): `loadAccCoordShifted_encode`

Prove, under `enc.limbShapeOk = true` and `c < accFpModulus`:

```
loadAccCoordShifted enc (encodeAccCoordWords enc c) 0 = (c + accFpModulus - 1) % accFpModulus
```

P-BYTES: **"the single step that unblocks three of the four."** Ingredients it left you:
- `ofLowDigits_digit` (`Exec/Accumulator.lean:1407`) — identifies the limb extracted from the
  j-th emitted word with the source limb. **This is why the next package is not stuck.**
- `natToBytesBE_split` / `natToBytesLowFirst_split` (`Common/Bytes.lean:479`, `:429`).
- `eipCoordFrame` / `eipFrame` (`:1531`, `:1562`) — the 16-48-16-48 identity.

Still owed: a **`foldl` → `ofLowDigits` bridge** for the outer sum, and the
**`min 4 (7 - 4*j)` case split** for `j ∈ {0,1}`. Then `decodeAccCoord_encode` is ~3 lines and
`encodeAccCoordWords_packingOk` falls out of the same limb bound.

## Step 2: the `accMapInsert` fold lemmas — absent from every prior table

P-BYTES found the diagnosis was **wrong in detail**: nothing named these, and three of the four
round trips need them.

- `accMapInsert_fold_sorted_id` → needed by `decodeAcc_encode` and `decodeAcc_encode_noNeg`.
- A **`Nodup` fold-injectivity** lemma → needed by `decodeAcc_injective`.
- `decodeAccCoord_inj` → needed by `decodeAcc_injective` only, **not** by the encode family.

## Step 3: close what you can

`decodeAcc_injective` (:141), `decodeAcc_encode` (:249), `decodeAcc_encode_noNeg` (:275),
`decodeAcc_encode_pointPair` (:339). **Read each against sketch section F first**
(`P-SE-semantic-equivalence.md:904-1090`); P-BYTES confirmed all four match binder-for-binder,
so no restoration should be needed — but verify rather than inherit.

## Step 4 (cheap, do it): the `GSMul` transport module

Move the seven hand-proved `gsmul` lemmas out of `Lowering/Accumulator.lean` section 8 into
`Midfall/Common/GSMul.lean`. P-BYTES deliberately deferred this (~20 min) because it shifts
four `SORRY.md` pins and costs a gate run — **you are spending that gate run anyway.** They are
stated at `gsmul`, a Midfall definition Mathlib has no name for, so they are misfiled rather
than redundant.

## The method rule this package must apply

**Before claiming a name is missing from the built surface, `#check` it against `import Midfall`
AND try the unprefixed spelling.** P-BYTES found ~70 min of hand-proving had been paid because
a blocker cited the Mathlib-docs spelling `Additive.ofMul_mul` when the declaration is at root
namespace as `ofMul_mul`. **Orchestrator independently confirmed it.** If you find yourself
re-proving a Mathlib transport fact, stop and check the spelling first.

## Constraints

* **Never weaken a statement to make it provable.** Report instead.
* **D-P23 both halves as theorems** for every claim you close. P-BYTES claimed nothing for the
  four round trips because they were still `sorry` — same standard. Gap measured **22 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`; three-way agreement.
* **New walls from P-BYTES, all measured**: reducing a power above 2^256 needs
  `set_option exponentiation.threshold 512 in` or it times out; applying `natToBytesBE_split`
  with a zero high part times out in unification (use `natToBytesBE_zero_prefix`); `congrArg`
  over a goal with free variables makes `decide` fail with "Expected type must not contain
  free variables"; positional `_` synthesis in a deep `refine` times out where `apply` is
  instant.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`. **Note** a
  cascade build peaked **22.40 GiB tree** with only 3.12 GiB largest — a clone's 2-process
  incremental build does NOT predict a cascade's tree total, so state the higher figure.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5214 jobs**, 124
modules; `checks.sh` green: **44 tracked sorries**, 1317 KATs across 93 files, 235 fragments,
30 pins, Statements hash OK.

Read first: `Midfall/Halo2/Exec/Accumulator.lean` (**the new lemmas from :1347 onward,
especially `ofLowDigits_digit` at :1407 and `eipFrame` at :1562**), `Midfall/Common/Bytes.lean`
(the frame lemmas from :378), `Midfall/Lowering/Accumulator.lean` (the four open holes and the
seven `gsmul` lemmas in section 8), sketch section F from line 904, `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 44**.
- `loadAccCoordShifted_encode` landed — the named unblocking step.
- `GSMul.lean` created and the seven lemmas relocated.
- **Required finding**: how many of the four closed, and whether P-BYTES's "single step
  unblocks three" claim held or was itself optimistic — this project has measured 23 recorded
  blockers that were not, so a precise-sounding pointer deserves the same scepticism.
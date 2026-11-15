# P-ACCENC - `loadAccPoint_encode`, the link no table ever named. Plus a layering fix.

Status: READY. P-LIMB closed 3 of the 5 links in the accumulator byte chain and **named the
next one precisely**: `loadAccPoint_encode`, which **no prior table mentioned**.

## Step 0 (10 min, do first) - fix the layering inversion I caused

`Midfall/Common/GSMul.lean` is the **only** file under `Common/` that imports `Halo2/` —
confirmed by grep. `gsmul` is defined at `Halo2/Exec/Kzg/Msm.lean:35`, so a `Common/` module
must import upward into `Halo2/`. **That is my brief's error, not the agent's** — it followed
the literal path and flagged the inversion.

**Move it to `Midfall/Halo2/Exec/Kzg/GSMul.lean`**, update the one import in
`Lowering/Accumulator.lean`, and regenerate `SORRY.md` (pins will shift). Do this **first** so
the rest of the package is not built on a layout that will move under it.

## Step 1 - `loadAccPoint_encode` (the highest-value remaining link)

The encoder direction of the point loader. P-LIMB: it needs **`eipFrame` + `eipShape` +
`ofEip_toEip` + the flag word** — all four already exist in the tree (`eipFrame` at
`Exec/Accumulator.lean:1562`, `loadAccPoint_flag0/1` at `:1586`/`:1574`).

This is the link that gates `decodeAcc_encode` and `decodeAcc_encode_noNeg`.

## Step 2 - `decodeAccCoord_encode`, with the wall workaround already found

P-LIMB got to ~80% and stopped at a **specific** wall: `Nat.div_le_div_right`'s implicit
`2^256` divisor blows the kernel recursion limit in this elaboration context. **Its recorded
workaround: state the `inField` comparison as concrete `decide`-proved numerals rather than
routing through the generic div lemmas.** `plimb_split` and `plimb_hi_eq` already prove fine
by `decide`. Expect ~80 lines, not the 3 a previous pointer claimed.

## Step 3 - the two `accMapInsert`/`find?` interaction lemmas

P-LIMB proved the brief's "Nodup fold-injectivity" **cannot exist as stated** — the fold
SORTS, so a duplicate-free descending list folds to a permutation of itself
(`accMapInsert_fold_sorted_needs_ascending` exhibits it with `[(b,1),(a,2)]`).
`decodeAcc_injective` needs **`find?`-readback injectivity** instead: one lemma for the
inserted key, one for a different key.

## Step 4 - close what fits

**`decodeAcc_encode_pointPair` (:503) is probably the cheapest of the four** — `hfb :
fb.size = 0` makes the fold trivial — once Steps 1–2 exist. Then `decodeAcc_encode` (:413),
`decodeAcc_encode_noNeg` (:439), `decodeAcc_injective` (:142).

## Constraints

* **Never weaken a statement to make it provable, and do not close a hole to meet an
  acceptance number.** P-LIMB stated plainly that the register target was not met rather than
  gaming it. Same standard here.
* **Verify inherited claims about statements.** P-BYTES reported all four `decodeAcc_*`
  matched the sketch binder-for-binder; P-LIMB found that is **false** for
  `decodeAcc_encode` (`namesAscending` vs the sketch's `List.Sorted`). Read section F yourself.
* **D-P23 both halves as theorems** for every claim you close. Nothing claimed for a `sorry`.
  Falsification-deletion gap measured **24 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Step 0 alone will move pins — regenerate and verify three-way agreement.
* **Walls already paid for, do not re-pay**: a packing/`decide` defeq on 2^336-scale numerals
  blows kernel recursion when operands are let-bound — extract it as a standalone lemma with
  OPAQUE arguments rather than raising `maxRecDepth`; `Nat.div_le_div_right`'s implicit 2^256
  divisor hits the recursion limit here, use concrete numerals; reducing a power above 2^256
  needs `set_option exponentiation.threshold 512 in`; `natToBytesBE_split` with a zero high
  part times out in unification (use `natToBytesBE_zero_prefix`); positional `_` in a deep
  `refine` times out where `apply` is instant.
* **Method rule**: before claiming a name is missing from the built surface, `#check` it
  against `import Midfall` AND try the **unprefixed** spelling. Three packages have now paid
  for a namespace error. `List.Sorted` genuinely IS absent; `Additive.ofMul_mul` is not.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`. Warm gate
  ~5.09 GiB tree / 4.42 GiB largest; **cold cascade has peaked at 22.40 GiB tree** — budget
  the tree total, not the largest process.
* **Durability**: land incrementally, keep the tree green after each step, send an interim
  report after Step 1, and never leave a file non-compiling at a point you might stop.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `ShellModel.lean` or
  `IRCheck.lean`. Do NOT git add or commit. Leave no scratch.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5215 jobs**, 125
modules; `checks.sh` green: **44 tracked sorries**, 1317 KATs across 93 files, 235 fragments.
The four open holes are at `Lowering/Accumulator.lean:142, 413, 439, 503`.

Read first: `Midfall/Halo2/Exec/Accumulator.lean` (the byte lemmas from :1347, especially
`eipFrame` :1562, `loadAccPoint_flag0/1` :1586/:1574, `ofLowDigits_digit` :1407),
`Midfall/Lowering/Accumulator.lean` (the four holes, the fold lemmas, `namesAscending`),
`Midfall/Common/GSMul.lean`, sketch section F from line 904, `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Step 0 landed (no `Common/` file imports `Halo2/`).
- `loadAccPoint_encode` landed.
- Register **below 44** if any round trip closes — **but not by weakening anything.**
- **Required finding**: the true remaining chain to each of the four, corrected for whatever
  this package learns. P-LIMB's five-link chain was itself the first accurate one, and it
  arrived only after two optimistic pointers.
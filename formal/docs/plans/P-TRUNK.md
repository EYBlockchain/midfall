# P-TRUNK - the four shared trunk links no table ever named. Small, and three of four holes need them.

Status: READY. P-ACCENC closed 2 of the 4 trunk links and **named the remaining four precisely**
with line estimates. These are plumbing, not walls — the package explicitly says "none of them
is the kind of wall that eats a day."

## The four links (in order, all shared by `decodeAcc_encode`)

| # | link | est. | what it must say |
|---|---|---|---|
| a | **array-offset getD transfer** | ~10 lines | `getD` across `pre ++ inst` at index `enc.offset + j`, using `hpre : pre.size = enc.offset`. The pieces exist **privately** in `Exec` (`getD_append_left/right`, `getD_snoc`) — there is no public `getD_append_pre`. **Make them public rather than re-proving.** |
| b | **`fixedScalarCount_exact`** | ~20 lines | `fixedScalarCount (toExec enc) (offset + fixedPayloadWords + n) = some n` for the 12 + n word payload |
| c | **scalar readback** | ~15 lines | `(frWord s).toNat = s.val` and `Nat.cast s.val = s` in `Fr p`, needing `hp : p < 2^256`. **Never previously named.** |
| d | **fold alignment** | ~40 lines | `foldl accMapInsert` over `zip fb.toList tailWords` equals the `negateByTable`-shaped tail. Needs `namesAscending_nodup` (strictly ascending names are distinct) and the `fb.any ↔ b.negate` bridge under distinctness. **`accMapInsert_fold_sorted_id` alone does NOT do it** — the fold's per-entry value is `if b.negate then -s else s` while `negateByTable` computes `fb.any (name == n && negate)`. |

**Then `decodeAcc_encode` (:413) should be ~150 lines total, and
`decodeAcc_encode_noNeg` (:439) falls out of it essentially free** (plus
`negateByTable_eq_of_noNeg`, ~10 lines).

## Explicitly NOT recommended for this package

* **`decodeAcc_encode_pointPair` (:503)** — P-ACCENC found the brief's "cheapest of the four"
  claim **false**. Its wall is `getD` through `Array.extract`, and `List.getD_take`,
  `List.getD_drop`, `Array.getD_extract` are all absent (probed). ~150–200 lines of plumbing.
  Skip unless a–d finish early.
* **`decodeAcc_injective` (:142)** — needs the **reverse direction**: `decodeAccCoord_inj`,
  recovering words from a decoded `(hi,lo)` pair. Most expensive of the four, gated on a link
  never written down. Leave it.

## Step 2: harden `kat_gate` against the fake-value defect

P-ACCENC found a real gate defect: **`kat_gate`'s VALUE regex harvests any stdout line
matching a bare `true`/`false`/number/string/bracket pattern — so a linter hint line like
`[apply] simp [...]` is counted as a fake `#eval` result.** `checks.sh` went rc=1 with
"printed 6 value(s) for 5 #eval line(s)" on a file `lake build` accepted. The R-53 comment in
`kat_gate.py` shows this class has bitten before.

**Fix: anchor the value regex to actual `#eval` output** (e.g. require the line to be the
value alone, and skip lines starting with `[` which are linter diagnostics), then **show it
bites** by reintroducing an unused `simp` arg in a clone and confirming the gate stays green.
Cheap, and it removes a class of false failures that has now cost two packages a gate run each.

## Constraints

* **Never weaken a statement to close a hole to meet a number.** P-ACCENC closed zero and said
  so; that is the standard.
* **Verify inherited claims.** Three packages in a row have now corrected the one before —
  P-BYTES's "all four match the sketch" was false; P-ACCENC's "pointPair is cheapest" was
  false; the brief's `ofEip_toEip` ingredient was misplaced. Read section F yourself.
* **Method rule, now with a corollary**: before claiming a name is missing, (a) try the
  **unprefixed** spelling, and (b) check whether it is a **project** definition shadowing a
  Mathlib one — `divCeil` is `Exec/Arith.lean:53`, not `Nat.divCeil`, so Mathlib's `divCeil`
  lemmas do not apply. Also `Array.find?` is NOT `List.find?` on `toList` here.
* **D-P23 both halves as theorems** for every claim closed. Gap measured **25 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`; three-way agreement.
* **NEW OPERATIONAL RULE: never run `checks.sh` while a file is being edited** — stale oleans
  produced 11 bogus KAT failures in P-ACCENC. Gate runs are ~9–10 min, not 8.5.
* **Walls already paid for**: `simp` EVALUATES `2^256` so a hypothesis with the unevaluated
  power stops matching (`simp only [decide_eq_true_eq]` instead); `0 + j` is NOT defeq to `j`;
  `#[0]` vs `#[BitVec.ofNat 256 0]` defeq but not `rw`-matchable; powers above 2^256 need
  `set_option exponentiation.threshold 512 in`; deep positional `_` in `refine` times out where
  `apply` is instant; let-bound huge numerals blow kernel recursion — use opaque args.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`. Warm build
  peaked 9.50 GiB tree, gate 5.11 GiB; cold cascade has hit 22.40 GiB. Budget the tree total.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `ShellModel.lean`, `IRCheck.lean`.
  Do NOT git add or commit. Leave no scratch.
* **Durability**: land incrementally, keep the tree green, interim report after links a–b.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5215 jobs**, 125
modules; `checks.sh` green: **44 tracked sorries**, 1317 KATs across 93 files, 235 fragments.
Holes: `Lowering/Accumulator.lean:142, 413, 439, 503`. The private getD lemmas are in
`Midfall/Halo2/Exec/Accumulator.lean`; readback lemmas at `Lowering/Accumulator.lean:1445,:1455`.

Read first: `Midfall/Halo2/Exec/Accumulator.lean` (the byte lemmas and the private getD
helpers), `Midfall/Lowering/Accumulator.lean` (the four holes, `namesAscending`, the fold and
find? lemmas), sketch section F from line 904, `scripts/kat_gate.py` (the R-53 note),
`docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Links a–d landed.
- **`decodeAcc_encode` and `decodeAcc_encode_noNeg` closed** → register **42**. Not by
  weakening: if a–d are not enough, report what else the trunk needs.
- `kat_gate` hardened and shown to no longer false-redden on a linter hint.
- **Required finding**: the corrected trunk depth after this package. Every prior estimate of
  this chain has been too shallow — two links, then four. Say what the real number is.
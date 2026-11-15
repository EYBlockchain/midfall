# P-CODECLAWS - `G1CodecLaws` has no witness at any codec. One byte bridge stands between that and inhabited.

Status: **HIGHEST VALUE PER LINE IN THE TREE** (P-LOWEQ's own verdict). `lowering_equivalence` is
**proved** — axioms the standard three, no `sorryAx` — but **one of its hypotheses is not known
satisfiable.** Same class as `Eip2537.Holds` before P-HOLDS-FINAL.

## The exact gap

`G1CodecLaws` had **zero terms in the whole tree** before P-LOWEQ. It now has five of seven fields
at `g1CodecZ` (`g1CodecZ_five_of_seven`). The two that fail:

- **`eipShape`** and **`toEip_one`** speak `natToBytesBE` bytes; `g1CodecZ.toEip` is
  `bytesNatBE` bytes. **`bytesNatBE v n = natToBytesBE v n` is proved nowhere.**
- `Externals.lean:188` records that the two encoders are kept independent **on purpose** — so
  this is not an oversight to paper over. **Establish the bridge where the two meet, or explain
  why they cannot be equal and what that means for the codec choice.**

## Deliverable

1. **Prove the byte bridge** `bytesNatBE v n = natToBytesBE v n` (under whatever side condition
   makes it true — likely `v < 256^n` or a width relation). **Check it is actually true before
   building on it**: if the two differ on some input, that is the finding and it may mean
   `g1CodecZ` is the wrong codec for `G1CodecLaws`.
2. **Land `eipShape` and `toEip_one`** at `g1CodecZ` → `g1CodecZ_laws` (7/7).
3. **Retire `gap_g1codecLaws_unexhibited`** with the bundle-gate tokens moved **in the same
   commit** — a mismatch reddens, and both directions have bitten before.
4. **Then re-check the bundle**: `loweqBundleCore` should gain the 7th leg and become a full
   `lowering_equivalence` hypothesis bundle at one real Surface.

## Also in scope — two gate defects P-LOWEQ found and left

* **`scripts/lean_grep.py` tests `'` before `--`**, so a primed identifier (`obs'`, `hshell'`) at
  depth zero opens a phantom char literal and everything after stops being comment-stripped.
  P-LOWEQ's first register listed **two false proof holes in a docstring with the build green**.
  **Fix the stripper** (test `--` before the char-literal case) and show it by putting a `sorry`
  inside a docstring after a primed identifier and confirming the register does NOT list it.
* **A joint exhibit can have a conjunct gutted to `True` and stay green** — the `mentions` test
  finds the token in the binder list. Assess whether `loweqBundleCore` can be pinned per-conjunct
  (e.g. `And`-component count, or each leg named in a `must` list that the conclusion must
  actually contain). If it cannot be fixed cheaply, record the limit — do not claim coverage.

## Explicitly NOT this package

**`ir_refines` at `modelIr S`** — P-LOWEQ named it as the new crux of the programme: it needs the
real `armBody` shown insensitive to the prologue write (no `msize`, no load-bearing read of
word `0x40` beyond `headGuard`'s bound test), or an explicit frame hypothesis. `L.main` is
opaque, so this cannot be checked today. **Do not start it here** — it needs the run leg and is a
separate, larger package. But **report what it would need** if you learn anything.

## Constraints

* **Never weaken a statement to make it provable.** If `bytesNatBE` and `natToBytesBE` genuinely
  differ, say so — do not adjust `G1CodecLaws` to fit the codec you have.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **27 times**; a gutted
  conjunct of a joint exhibit also measured as invisible. Claim no persistence coverage.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **NEW RULE, earned this session: never restore a perturbed file with `git checkout` if it
  holds uncommitted work** — a `git checkout` silently reverted 241 lines of proof. Use content
  saves. Verify with `git status` after every restore.
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line` pins.
  Regenerate with `scripts/gen_sorry.sh`; three-way agreement.
* **Method rule**: before claiming a name is missing, try the unprefixed spelling, check whether
  it is a project definition shadowing a Mathlib one, and remember that resolving against
  `import Midfall` is NOT the same as being in a given file's import closure.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~9–10 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5215 jobs**, 125 modules; `checks.sh` green: **41 tracked sorries**, 1317 KATs,
245 fragments, 6 named gap defs, 30 pins, Statements hash OK.

Read first: `Midfall/Assumptions/Codec.lean` (`G1CodecLaws` — all seven fields),
`Midfall/Instances/G1Agreement.lean` (`g1CodecZ`, `g1CodecZ_five_of_seven`),
`Midfall/Yul/Externals.lean:188` (**the note that the two encoders are independent on purpose**),
`Midfall/Common/Bytes.lean` (`natToBytesBE`, `bytesNatBE`), `Midfall/Instances/CurveSurface.lean`
(`loweqBundleCore`), `Midfall/Instances/ObligationsGates.lean` (`gap_g1codecLaws_unexhibited`),
`scripts/lean_grep.py`, `docs/REVIEW.md` R-66.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `G1CodecLaws` exhibited at a real codec, **or** a precise statement of why it cannot be.
- `lean_grep.py` fixed and shown not to false-positive on primed identifiers.
- **Required finding**: with the 7th leg landed or refuted, is `lowering_equivalence`'s
  hypothesis bundle now known inhabited? And what does `ir_refines` at `modelIr S` actually need?
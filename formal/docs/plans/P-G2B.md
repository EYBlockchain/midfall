# P-G2B - finish the G2 codec, restore gate speed, and set up the landmark.

Status: READY. P-G2 landed Fp2 and the G2 agreement and left **one plumbing item** between here and
a single `Holds` term. Its next-agent list is followed here, plus one cost the project should fix.

## Steps, in this order. Stop at a boundary.

### Step 1 - the G2 codec round trip (design already written into `gap_g2_codec_plumbing`)

1. Re-derive `bytesAppend_size` **locally** (~3 lines — it is `private` in `G1Agreement.lean`).
2. `set_option maxHeartbeats 400000000` on the four slice-window lemmas — P-G2 identified this as
   the fix and ran out of budget before trying it.
3. `g2Of?_g2PointBytes`.
4. The **exponent-fold carrier** `G2fold` with `g2foldToEip` — designed precisely to dodge the
   quotient problem: an AdjoinRoot element has no computable representative extraction, so the
   encoder writes the fold's bytes and canonicity is `smulFrame2_canonic`. No quotient is read
   back.
5. `g2fold_g2Valid`.

### Step 2 - correct the over-stated gap wording (P-G2 flagged it, declined to edit it)

`gap_g2_no_fp2_model` says the clause has "nothing to quantify over". **That is too strong:**
`g2Valid` is satisfied by the constant all-zero encoder, since `g2PointValid` short-circuits on the
infinity branch and `g2Of?` accepts the `0x100` zero frame. What was missing is a **non-degenerate
codec**, not a field. Re-word accordingly — **and update the registry tokens in
`scripts/check_hypothesis_bundles.py` and the Lean-side `gapHoldsBlockers_ok` in the same commit**,
or the bundle gate reddens. Show it reddens if a token is dropped.

### Step 3 - restore `checks.sh` speed (a real regression, recorded not hidden)

P-G2 measured: `checks.sh` went from **~450–480 s to over 10 minutes**, because `kat_gate.py`
re-elaborates every `#eval`-bearing file with `lake env lean`, so the heavy decides (8.6 s `r•H2`
+ ~4 s decode) are paid on **every** gate pass even with the `.olean` cached.

**Fix: move the heavy decides into a file with no `#eval` lines**, keeping the `Bool` gates in a
cheap file that cites them. Verify the wall-clock returns to ~450–500 s and report the number.
This matters beyond tidiness: a 10-minute gate discourages running it, and the gate suite is the
only thing catching the defects this project keeps finding.

### Step 4 - only if 1–3 land: stage the landmark

State the **conditional** `Holds`: given `[AdmissiblePairing G₁z G2carrier Gₜ]` plus the required
instances, exhibit `∃ product, Eip2537.Holds g1CodecZ ⟨g2fold⟩ product`.

**P-G2 named the one nontrivial bit:** `pairingProductOf` needs `FrameLaws`, and `FrameLaws` needs
the **encoder-first** codec law `ofEip? (toEip Q) = some Q`, which for `g1CodecZ` needs
`Classical.choose` plus injectivity of `g1zToEip`. **Check that specifically** — it is the one
place the landmark could still stall.

## Constraints

* **`Instances/` confinement (D-P17)**: all of this is concrete model work, so it stays in
  `Instances/`.
* **Elaborator walls**: the pair-`==` whnf wall (cross with `unfold`, never `rw` through it), the
  200k-heartbeat default (raise it **locally with the reason documented**, which is the one case
  P-POINTCOUNT showed raising a limit is legitimate), and `rw [ZMod.card]` costing ~4 GiB —
  pre-prove cardinalities as `have`s.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.** P-G2 caught **two** silent splices this way
  (589→294 lines; ~450 lines). The rule is proven, not theoretical.
* **`kat_gate` traps**: no unused `simp` args or unused-variable bindings in `#eval`-bearing files
  — the `[apply]` linter hint matches the value regex and P-G2 hit it.
* **D-P23 both halves as theorems.** The falsification-deletion gap has been measured **twelve
  times** — claim no gate coverage for falsifications.
* **RAM (D-P31)**: `ram_guard.sh --selftest` **first, and read it**. State expected peak;
  `--proc-limit 6G --limit 24G`. Recent: 4.86 GiB tree / 4.13 GiB largest.
* **Perturbations**: `lake build` for theorems, `checks.sh` for Bools, code not comments.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5205 jobs**, 115 modules; `checks.sh` green: **57 tracked sorries**, **1302 KATs
across 90 files**, 158 fragments, 12 fact families, 8 bundles with 4 gap defs, 30 pins, Statements
hash OK. **D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Instances/G2Agreement.lean` (**`gap_g2_codec_plumbing`** — the design and
both causes), `Midfall/Instances/Fp2.lean`, `Midfall/Instances/G1Agreement.lean` (`bytesAppend_size`
is private; `g1CodecZ` as the codec template), `Midfall/Instances/ObligationsGates.lean
` (`gap_g2_no_fp2_model`, `gapHoldsBlockers_ok`), `scripts/check_hypothesis_bundles.py`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green, **with `checks.sh` back to ~450–500 s**.
- The G2 codec lands and `g2Valid` is discharged at a non-degenerate codec.
- **Required finding**: with G2 done, is the **only** thing between here and a single `Holds` term
  the D-P36a pairing hypothesis — and did the `FrameLaws` encoder-first requirement hold?

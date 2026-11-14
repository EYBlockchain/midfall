# P-G2 - the Fp2 model and G2 codec. The last construction wall before a single `Holds` term.

Status: READY. P-GAPFIX established the path precisely: **a single `Holds` term does not need
Fp12.** Two walls remain — this package (G2) and one named hypothesis (D-P36a, the pairing).

## Why the hard-looking part is not hard

**The failed `2p+1 < r²` transfer does NOT block `g2Valid`.** It closed the *count* route for G2,
but `Holds` has **no `g2Decodes` clause**, so the cyclic-subgroup route (D-P34,
`primeOrderWith_zpowers`) gives `PrimeOrderWith G₂ r` with **no point count at all**. Do not
re-derive the wall and do not over-read it — it is recorded in `gap_g2_no_fp2_model`.

## Steps, in this order. Stop at a boundary rather than half-finishing all four.

### Step 1 - Fp2, and `p ≡ 3 [MOD 4]` as a THEOREM

* **P-GAPFIX's recorded trap:** `pBase % 4 = 3` is pinned only as a **Bool gate**
  (`basePrimeKats_ok`, `pBaseKats_ok`), **not as a theorem**. Expect to state and prove that one
  `decide` yourself — it is what makes `X² + 1` irreducible.
* Build `Fp2 := Fp[u]/(u²+1)`. Check what mathlib already has first — `ZMod` is a field here, so
  `AdjoinRoot` over `ZMod pBase` with the irreducible polynomial is the likely route.
* **Verify the arithmetic model matches `fp2Ops` in `Yul/Externals.lean`** before building
  anything on top — the whole point is agreement with the byte-level implementation.

### Step 2 - the G2 curve and a frame codec

* G2 curve `y² = x³ + 4(v+1)` over Fp2 (per P-GAPFIX).
* A `G2Enc` at the **0x100 width** the precompile reads.
* `g2Of?` / validity predicates from `Externals.lean` (`g2PointValid`).

### Step 3 - the agreement over Fp2, and `r • H2 = 0`

* `fp2Ops`-vs-mathlib group-law agreement — **`G1Agreement.lean` is the template**, including the
  infinity handling and the canonicity walk.
* `r • H2 = 0` for a published H2. **This is the expensive kernel computation — roughly 4× the G1
  fold.** Budget it explicitly and measure it before wiring it into a gate; the G1 equivalent cost
  16.6 s and P-GAPFIX warns that a `#eval` re-running it on every gate pass is a mistake.
* Then `PrimeOrderWith G₂ r` via `primeOrderWith_zpowers` — **no count needed.**

### Step 4 - only if 1–3 land: discharge `g2Valid`

Exhibit `Holds`'s `g2Valid` clause at the G2 codec, and record how many of six clauses now hold
at **one** codec+carrier combination.

## Constraints

* **`Instances/` confinement (D-P17)**: everything here is a concrete model, so it lives in
  `Instances/`. The *clause statements* stay in `Assumptions/`.
* **Elaborator walls, four known doors** — `affineSmul` pair-`==`, `List.all` over a literal list,
  `nsmul` at a 255-bit literal, and `rw [ZMod.card]` costing ~4 GiB. **Generalise over the thing
  the literal sits in; never raise `maxRecDepth`** (except where P-POINTCOUNT showed a deep
  unifier whnf genuinely needs it, with the reason documented). Pre-prove cardinality equations
  as `have`s rather than rewriting with the lemma.
* **D-P23 both halves as theorems.** The falsification-deletion gap has been measured **eleven
  times** — do not claim gate coverage for falsifications.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.** A splice deleted 44 KB of proofs while the
  build stayed green; the only symptom was a file getting shorter.
* **Comment edits are not free:** a comment-only change to a widely-imported module made a
  parallel fan-out peak at 13.38 GiB against a 4.0 GiB estimate.
* **RAM (D-P31)**: `ram_guard.sh --selftest` **first, and read it**. State expected peak;
  `--proc-limit 6G --limit 24G`. Recent actuals: 3.79–4.97 GiB tree, 3.10–4.35 GiB largest.
* **`kat_gate` traps**: no unused `simp` args in `#eval` files; a redundant `simpa` emits an
  `[apply]` hint that matches the value regex; and a `Bool` gate without `#eval -- expect` is
  invisible.
* **Perturbations**: `lake build` for theorems, `checks.sh` for Bools, code not comments.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck or out of room.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5202 jobs**, 113 modules; `checks.sh` green: **57 tracked sorries**, 1299 KATs
across 88 files, 158 fragments, 12 fact families, 8 bundles with **4 named gap defs**, 30 pins,
Statements hash OK. **D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Instances/ObligationsGates.lean` (`gap_g2_no_fp2_model`,
`gap_holds_unexhibited`, `gapHoldsBlockers_ok`), `Midfall/Instances/G1Agreement.lean` (the
template — `emb`, `FpFrame`, the canonicity walk, `g1CodecZ`), `Midfall/Instances/G1PointCount.lean`
(what the count route needed and why it does not transfer), `Midfall/Yul/Externals.lean`
(`fp2Ops`, `g2Of?`, `g2PointValid`), `Midfall/Assumptions/Eip2537.lean` (`G2Enc`, `g2Valid`).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Steps landed in order; each stall recorded with a **specific cause**, not "hard".
- **Required finding**: with G2 landed (or blocked), how close is a **single** `Holds` term — and
  is the only remaining item genuinely the D-P36a pairing hypothesis, i.e. is the landmark within
  reach with one named assumption and no new mathematics?

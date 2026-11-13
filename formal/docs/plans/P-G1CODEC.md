# P-G1CODEC - the byte codec round trip. Fully scoped by P-CANON; execute it.

Status: READY, narrow, and **the blockers are already named with their causes.** P-CANON landed
canonicity and said plainly: `g1Add`/`g1Msm1` are no longer blocked by mathematics but by byte
plumbing, and it wrote `gap_g1_codec_roundtrip` recording exactly which lemmas stall and why.

## The chain to discharge

1. **`g1Of? (g1PointBytes P) = some P`** for canonical `P` — the round trip itself.
2. **The two `bytesSlice` equations** over the 128-byte concatenation.
3. **`g1AddValidInput` / `g1AddOutput`** unfolding.
4. **`g1MsmPairs?.go`** — the where-clause function. **P-CANON did not attempt this.** Budget for
   it rather than assuming it is like the rest.

## The three named matcher obstacles, with P-CANON's recorded causes

* `ofLowDigits_append` **fires on the wrong occurrence** once the RHS is in `bytesToNatBE` form.
* `bytesTake_whole` needs **`@ByteArray.size_data`** to state the hypothesis.
* The slice side conditions **must be stated against `ByteArray.size A`**, because
  `Array.extract_append` inserts its own `min`.

**Re-verify these rather than trusting them** — the ledger now has **nine** recorded premises
that were wrong in their specifics, and the last one's *cure* was wrong even though its symptom
was real. P-CANON also recorded a trick that generalises: **where `rw` cannot cross a defeq, a
`have` with an ascribed type can** (elaboration uses full defeq where the matcher does not).

## Then — the second missing piece, which P-CANON named explicitly

**A `G1Codec` on the `zpowers` carrier**: a `Point → canonical-bytes` map via `Point.toAffine` +
`ZMod.val`. Without it the exhibit cannot be *plugged into* `Holds`, so the round trip alone does
not give five of six clauses. P-CANON: "canonicity + point count ⇒ five of six" is **not right**;
it is canonicity (done) + point count + codec round trip + codec exhibit.

## Out of scope

* **The point count** `|E(Fp)[r]| = r` — separate package, route (b), `gcd(r, p−1) = 1` already
  proved.
* **`g2Valid`** — needs a G2 frame codec and an Fp2 model; `fp2Ops` has **no mathlib model at
  all**. A package, not a lemma.
* `Statements.lean`, `Statements.sha256`, Rust, `vendor/`.

## Constraints

* **D-P23 both halves as theorems.** The falsification-deletion gap has been measured **nine
  times** — deleting falsifications leaves the build green. **Do not claim gate coverage for
  them**, and state coverage limits plainly, as P-CANON did.
* **`Instances/` confinement (D-P17)**: `G1Agreement.lean` stays in `Instances/`.
* **Elaborator limits, newly measured:** `whnf` of a **pair `==`** on `affineSmul` unrolls the
  255-step fold and dies at the default `maxRecDepth` even with variables. Work over variables,
  cross definitions with `unfold`/`delta` rather than `rw`/`simp`, and transport with `▸` along
  **named** equations.
* **`Group (Additive A)` does not synthesize** in this mathlib; the carrier is
  `AddSubgroup.zmultiples` (`zsmulSet`/`zsmuls` do not exist). Wrap in `Multiplicative`.
* **Perturbations:** `lake build` for theorems, `checks.sh` for KAT Bools; scope edits to code,
  not comments (a comment hit produced a false negative; a deletion that cut an intervening
  `set_option` produced a false positive).
* **`lake env lean`**: pass `-DautoImplicit=false` or unknown identifiers silently become free
  variables. `set_option X in` must precede a declaration's docstring.
* **RAM (D-P31)**: **run `ram_guard.sh --selftest` FIRST** — P-CANON ran it last, which it
  self-reported as a process miss. State expected peak; `--proc-limit 6G --limit 24G`. Recent
  actual: 4.82 GiB tree / 4.09 GiB largest (my earlier ~10.6 GiB figure was 2× over for
  single-module work).
* **`kat_gate` trap**: an unused `simp` argument in a `#eval`-bearing file fails the gate on a
  green build. And do **not** add a `#eval` that re-runs the 16 s `decide` on every gate run.
* Do NOT git add or commit. **Leave no scratch in the repo.** Report back even if stuck.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5198 jobs**, 112 modules; `checks.sh` green: **57 tracked sorries**, 1297 KATs
across 87 files, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements hash OK.
**D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Instances/G1Agreement.lean` (**`gap_g1_codec_roundtrip` and the closing
section** — the named obstacles and their causes), `Midfall/Yul/Externals.lean` (`g1Of?`,
`g1PointBytes`, `g1AddValidInput`, `g1AddOutput`, `g1MsmPairs?`), `Midfall/Assumptions/Eip2537.lean
` (`G1Codec`, the `g1Add`/`g1Msm1` clause texts).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- The round trip lands, **or** each remaining stall is recorded with a specific cause rather than
  left as "hard".
- **Required finding**: with the round trip and the `zpowers` `G1Codec` exhibit, how many of the
  six `Holds` clauses are dischargeable on the G1 side — and is the point count then genuinely
  the only thing between here and five of six?

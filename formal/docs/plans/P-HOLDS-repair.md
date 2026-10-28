# P-HOLDS - repair `g1Decodes`, and get the 381-bit primality certificate. Bounded work.

Status: READY. **Items 1 and 2 of R-63's three-level blocker.** Item 3 - the r-torsion
point count - is a human decision and is **explicitly out of scope here**. Do not attempt it.

## 1. Repair `g1Decodes` with the width condition (one line, already proved satisfiable)

`g1Of?` is a coordinate reader: `bytesSlice` clamps and never checks frame width, so every
all-zero frame of length `0x80 + k` decodes. `g1Decodes` then demands each such string be
`toEip Q`, which is unsatisfiable for cardinality reasons - proved as `holds_unsatisfiable`.

* **Apply the repair P-CURVE already proved satisfiable at real curve points**: add
  `b.size == g1Bytes` to the quantifier, i.e. adopt `g1DecodesWidth` as the clause.
* **Keep the refutation theorems.** `g1Decodes_unsatisfiable`, `holds_unsatisfiable` and
  `not_exists_holds` are currently true **of the old text**. After the repair they must be
  restated against the old clause explicitly (e.g. `g1DecodesOld_unsatisfiable`) so the
  regression is pinned rather than deleted - same principle as keeping
  `s1_defect_refutes_the_conjunction` after R-60 S1.
* **`bundle_holds_empty` becomes false after the repair** - it is a refutation of the old
  structure. Replace it with the real joint exhibit if the remaining clauses allow it; if
  they do not (item 3), replace it with a refutation naming the *new* blocker, and update
  the gap tokens the bundle gate enforces. **Do not leave a refutation of a statement that
  no longer exists.**
* Add fingerprint entries for the six `Holds` clause types. P-CURVE reported that
  `check_statement_fingerprints.py` never reads them, so a text-level weakening currently
  reddens no gate and the build is the only defence. Close that.

## 2. `Fact (Nat.Prime pBase)` - the 381-bit primality certificate

`g1Add` and `g1Msm1` need mathlib's affine group law, which needs a `Field` instance on
`ZMod pBase`, i.e. `Fact (Nat.Prime pBase)`. CompPoly has a Pratt certificate for `r` only
(`Basic.lean:27`), so the pattern exists - follow it for `pBase`.

* Bounded work: 1-3 days per R-63. If the Pratt certificate turns out not to scale to 381
  bits in Lean's kernel, **report the wall** rather than assuming `native_decide` -
  `native_decide` is confined to `Instances/` and cannot discharge a hypothesis used by
  theorem-bearing files.
* Once available, connect `affineAdd`/`affineSmul` to mathlib's
  `AlgebraicGeometry/EllipticCurve/Affine/Point.lean:805` - P-CURVE confirmed the formulas
  already match the chord-and-tangent in `Externals.lean` exactly, so this should be
  bookkeeping, not discovery.

## Out of scope - do not attempt

**`PrimeOrderWith G1 r` / the r-torsion point count.** That is research-grade (SEA or the
n-torsion structure theorem plus `gcd(r, p-1) = 1`), does not exist in Lean, and is a human
decision about whether to assume it. Leave `gap_g1_prime_order` in place and gate-enforced.

## Constraints

* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50). Numbers from `lake build` and
  `scripts/checks.sh`.
* **D-P23 / R-41**: every repair needs a witness AND a demonstrated failure mode.
* Keep all four gates green and accurate (fingerprint, duplicate-facts, bundles, orphans).

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5150 jobs**;
`checks.sh` green: 64 tracked sorries, **1196 KATs across 79 files**, 103 modules, 8 bundles
(7 exhibited, 3 gaps, 1 joint refutation), Statements hash OK.

Read first: `docs/REVIEW.md` R-63, `Midfall/Assumptions/Eip2537.lean` (the clause and the
refutations), `Midfall/Instances/Bls12_381G1.lean` (the real-curve codec where the repair is
already proved), and CompPoly's `Basic.lean:27` for the Pratt-certificate pattern.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `g1Decodes` repaired, with the old-clause refutation retained and renamed.
- `Holds` clause types covered by the fingerprint gate.
- Either the primality certificate lands and `g1Add`/`g1Msm1` are discharged, or the wall is
  reported precisely.
- **Required finding**: after items 1 and 2, which `Holds` clauses remain undischarged, and
  is `P5` still blocked solely by the r-torsion decision?

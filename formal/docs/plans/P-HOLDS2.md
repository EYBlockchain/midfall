# P-HOLDS2 - exhibit `Holds` clause by clause. Start with `pairing2`, which needs no assumption.

Status: READY, and **two of its steps need no human decision at all.** I was wrong that the
pairing blocked this: `PairingProduct := Bytes -> Bool` is a **free parameter** of `Holds`, and
`pairing2` compares it against `P.e` from the assumed `AdmissiblePairing`. So `product` can be
**defined from `P.e`** and the clause holds by construction.

## Steps, in this order. Stop at a boundary rather than half-finishing all.

### Step 1 - define `product` from `P.e`; discharge `pairing2`

* Define a `PairingProduct` for a given `E : VerifierEnv` and codecs: on a `pairingFrame`,
  decode the two pairs back through the codecs and return whether the sum of the two `P.e`
  applications is zero.
* Prove `pairing2` for it. **This should be short** - a definition plus rewrites through
  `g1Of?`/`toEip` round-trip laws.
* **D-P23 both halves**: witness that the definition is not vacuous, and a falsification -
  e.g. a frame encoding pairs whose pairing sum is nonzero must give `product = false`.
* **Check the frame orientation carefully.** `Eip2537.lean:29-32` records that `ec_pairing`
  lays out `[lhs_g1 | G2_BASE | rhs_g1 | NEG_S_G2_BASE]` but `FinalPairing.yul:88` calls it
  with `(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)` - **the pairs the precompile sees are
  swapped** relative to the naive reading (the R-11 trap). If `pairing2`'s `pairingFrame` and
  the emitter disagree on order, a definition that looks right will be wrong.

### Step 2 - `Group` instance on the real G1 frame type

`BasePrime.lean` (P-HOLDS) gave us `Field (ZMod pBase)`, so mathlib's affine group law is now
reachable. P-CURVE confirmed mathlib's formulas at
`AlgebraicGeometry/EllipticCurve/Affine/Point.lean:805` **match `Externals.lean`'s
chord-and-tangent exactly**. P-HOLDS listed the four sub-problems:

1. the short-form embedding `a1=a2=a3=a4=0, a6=g1B=4` with equation agreement;
2. a `Nonsingular` proof per point - **the all-zero infinity frame is NOT an `AffineCurve`
   point and must map to `Point.zero`**;
3. reconciling `fpOps.inv` (Nat-level modular inverse) with field division;
4. closure under r-torsion.

**Re-verify P-HOLDS's cost claim rather than trusting it** - three packages running, a recorded
premise in this chain has been half-wrong, and in one case the wrong half blocked progress for
many rounds.

### Step 3 - only if 1 and 2 land cleanly: `g1Add` / `g1Msm1`

With a `Group` instance these become statements about the codec commuting with the operation.
If they do not close, report which side fails.

## Explicitly OUT of scope

* **`PrimeOrderWith G₁ p` - the r-torsion point count.** That is the one item needing a human
  decision (I have recommended assuming it as a named hypothesis; not yet confirmed). Do not
  attempt it and do not fake it with a toy group.
* **`g2Valid`** - needs a G2 frame codec, a separate package.
* **`Statements.lean`, `Statements.sha256`** - just filled and re-pinned under D-P33.

## Constraints

* **`Instances/` confinement (D-P17)**: a real curve model lives in `Instances/`; theorem-
  bearing files must not import it. `Holds` is in `Assumptions/`, so the *exhibit* goes in
  `Instances/` and the *statement* stays portable.
* **`decide` reduces for exponentiation at 255-bit `r` but NOT for inversion** (P-4a2).
  `pBase` primality is proved by Pratt certificate, not `decide` - `decide` on `Nat.Prime` was
  killed at 100 s for a 29-bit prime.
* **D-P23**: witness AND falsification, as **theorems**. Known gaps to respect, not claim
  past: deleting a falsification theorem leaves the build green (measured again by P-BRIDGE -
  deleting both left it green at 797 jobs); deleting a KAT conjunct is invisible.
* **Perturbation tests must use `lake build`, never `lake env lean`** (stale `.olean`).
* **RAM (D-P31)**: state expected peak; `--proc-limit 6G --limit 24G`; `--selftest` first.
  P-BRIDGE measured a peak of 9.00 GiB tree / 2.22 GiB largest on similar work.
* **`kat_gate` trap**: an unused `simp` argument in a `#eval`-bearing file makes the gate fail
  on a green build. Keep new proofs warning-free.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit. Leave **no scratch in the repo**.
* Regenerate `SORRY.md` only if a sorry closes; verify three-way agreement.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5156 jobs**, 110 modules; `checks.sh` green: **58 tracked sorries**, **1294
KATs across 86 files**, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK, frozen axioms 1 PROVED + 2 still-sorry.

**D-P32**: Rust reference pinned to `2d52f24`; `origin/main` has moved and all ten `.yul`
templates changed. Work against the pinned templates.

Read first: `Midfall/Assumptions/Eip2537.lean` (`Holds`, `PairingProduct`, `pairingFrame`, the
orientation note at lines 24-32), `Midfall/Instances/Bls12_381G1.lean` (the real G1 frame
codec and what P-CURVE proved), `Midfall/Assumptions/BasePrime.lean`, `Midfall/Common/Curve.lean
(`AdmissiblePairing`), and `docs/REVIEW.md` R-63/R-64.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `pairing2` discharged by a defined `product` - **this is the item that must land.**
- `Group` on the G1 frame type, or a precise report of which of the four sub-problems resists.
- **Required finding**: with `pairing2` (and ideally `g1Add`/`g1Msm1`) discharged, which
  `Holds` clauses remain unexhibited, and is the r-torsion count now the ONLY thing between
  here and a non-vacuous `lowering_equivalence`?

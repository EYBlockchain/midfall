# P-MODEXP - modexpInv at pBase, then the agreement theorem.

Status: READY. P-HOLDS2 named this as THE wall: the agreement theorem between byte-level
`affineAdd`/`affineSmul` and mathlib's group law gates `g1Add`, `g1Msm1`, **and the subgroup
half of `g1Valid`**. Its missing ingredient is modPow-as-modular-inverse correctness.

## Why I think it is cheaper than recorded - VERIFY THIS FIRST

`fpOps.inv` uses Fermat's method, `x^(p-2) mod p`. So the required fact is
`x^(p-2) * x = 1 mod p` for `0 < x < p`, **which is just Fermat's little theorem**. And
`BasePrime.lean` already provides `Fact (Nat.Prime pBase)`. So this should be a `ZMod` or
`Nat.ModEq` argument, not a new technique. P-HOLDS2 noted the fact is proved at 255-bit `r` but
"at pBase it is not even stated" - so step 1 is likely to state and prove the pBase version
reusing the existing primality instance. **Re-verify that reading before accepting it.** Three
packages running, a recorded premise in this chain has been half-wrong, and twice the wrong
half blocked progress for many rounds. If it is harder than Fermat, say so with the obstruction.

## Steps, in order. Stop at a boundary rather than half-finishing all three.

**Step 1 - modPow correctness at `pBase`.** For `0 < x < pBase`, the `modexpInvFrame` output
equals `x^(pBase-2) mod pBase` and is the inverse of `x` in `ZMod pBase`. If
`modexpInv_correct` (at `r`) closes by the same argument, close it too - register 58 to 57.

**Step 2 - the agreement theorem.** `affineAdd fpOps P Q` agrees with mathlib `W.Point`
addition under the short-form embedding `{a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 4} :
WeierstrassCurve (ZMod pBase)` - P-HOLDS2 confirmed that literal elaborates and that
`Nonsingular` is nearly free (singular forces `x = y = 0`, then `0 = 4 != 0`). Same for
`affineSmul` and `n • P`. **The infinity case is the trap:** `g1PointMsmValid P` unfolds to
`affineSmul fpOps blsR P = (0,0)`, and the all-zero frame is NOT an `AffineCurve` point - it
must map to `Point.zero`. Get that wrong and the statement is FALSE, not unprovable.

**Step 3 - only if 1 and 2 land: `g1Add` / `g1Msm1`**, using the already-proved
`primeOrderWith_zpowers`.

## Out of scope

`g2Valid` (needs a G2 frame codec, separate package); constructing Fp12 or a real pairing
(ruled out by D-P36 - the pairing is assumed); `Statements.lean` and `Statements.sha256`
(filled and re-pinned under D-P33).

## Constraints

* **D-P23 both halves as theorems.** Gaps to respect, not claim past - each measured by a
  different package: deleting falsification theorems leaves the build green; deleting a KAT
  conjunct is invisible to `kat_gate`; corrupting a predicate to `True` reddens only what cites it.
* **`Instances/` confinement (D-P17)**: real curve model in `Instances/`; `Assumptions/` and
  `Lowering/` must not import it. Statement portable, exhibit in `Instances/`.
* **`decide` reduces for exponentiation at 255-bit `r` but NOT for inversion**; `Nat.Prime` by
  `decide` is hopeless even at 29 bits. Expect the same at 381-bit `pBase`.
* **Heartbeat limits have bitten four packages.** A timeout is a signal about the approach, not
  a reason to reach for `native_decide` - confined to `Instances/` by D-P20.
* **Perturbations via `lake build`, never `lake env lean`** (stale `.olean`). Whole-repo APFS clone.
* **`kat_gate` trap**: an unused `simp` argument in a `#eval`-bearing file fails the gate on a
  green build.
* **RAM (D-P31)**: state expected peak; `--proc-limit 6G --limit 24G`; `--selftest` first.
  Recent: 10.27 GiB tree / 3.13 GiB largest (P-HOLDS2), 9.00 / 2.22 (P-BRIDGE).
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit. **Leave no scratch in the repo.**
* If a sorry closes, regenerate `SORRY.md` with `scripts/gen_sorry.sh`; verify register,
  `scripts/sorries.sh` and `checks.sh` agree three ways.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5157 jobs**, 111 modules; `checks.sh` green: **58 tracked sorries**, **1296
KATs across 87 files**, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK, frozen axioms 1 PROVED + 2 still-sorry. **D-P32**: Rust pinned to `2d52f24`; `main`
has moved and all ten `.yul` templates changed - work against the pinned templates.

Read first: `Midfall/Assumptions/Eip2537.lean` (`modexpInv_correct` :168, `pairingProductOf`
:590, `primeOrderWith_zpowers` :714, `FrameLaws`), `Midfall/Yul/Externals.lean` (`affineAdd`,
`affineSmul`, `fpOps`, `g1PointMsmValid`), `Midfall/Assumptions/BasePrime.lean`,
`Midfall/Instances/Bls12_381G1.lean`, `docs/REVIEW.md` R-63/R-64, `docs/plans/README.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **57** if `modexpInv_correct` closes.
- **Required finding**: with the agreement theorem landed or blocked, what is the shortest path
  to a **single type triple exhibiting all six `Holds` clauses** - and is `g2Valid` now the only
  clause without a route?

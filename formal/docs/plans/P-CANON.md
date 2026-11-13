# P-CANON - the canonicity walk. The last mechanical blocker on the G1 side.

Status: READY, narrow, and **blocked on an elaborator limitation rather than mathematics.**
P-G1AGREE wrote the walk, it does not check, and it documented two candidate cures. This package
executes them.

## The wall, precisely

`emb_add` and `emb_smul` are proved. What is missing is turning **coordinate equality in `K`**
into **canonical bytes**, needed for:
* `g1Add` — `toEip (P + Q) = g1PointBytes (affineAdd fpOps p q)`
* `g1Msm1` — same for scalar multiplication
* the **subgroup half of `g1Valid`** — `g1InSubgroup P = true <-> blsR • emb P = 0`

**Why it fails:** any defeq that forces `whnf` of `affineAdd`/`affineDouble` at real 381-bit
literals must evaluate `fpInv` — a 381-bit `modPow` — **inside the elaborator**, and it dies on
`maximum recursion depth` at every depth tried (1024, 100000, 1000000; the last flips to a C++
stack limit, not a budget). **`decide` proves the same facts happily.**

## Two candidate cures, both written into `G1Agreement.lean`'s closing section

1. **Keep such facts inside `decide`** and never let a defeq touch a reduced coordinate.
2. **Give `FpFrame` a canonicity field**, so the walk is over the *type* rather than the term.

**Re-verify both before spending time** — P-G1AGREE's record shows a correct diagnosis can still
carry a wrong cure (the `Nonsingular` obstruction was real; both suggested fixes were
unnecessary). If a third approach is cheaper, take it and say why.

**Useful known trick from P-G1AGREE:** where `rw` cannot cross a defeq, a `have` with an
ascribed type **can** — elaboration uses full defeq where the matcher does not.

## Then, if the walk lands

* **`blsR • emb genFrame = 0`** — provable and already measured: `affineSmul fpOps blsR genPair
  = (0,0)` by `decide` (~15 s, same cost `Bls12_381G1.lean` already pays), transported in one
  line by `emb_smul`. It is **not in the file** because of this wall.
* **`g1Add` / `g1Msm1` as standalone theorems** over the exhibit
  `{ P : W.Point // P in zsmulSet blsR (emb genFrame) }`. Note P-G1AGREE's finding:
  `AddSubgroup.zsmulSet` **does not exist under that name** in this mathlib revision — a naming
  task, not a blocker. `PrimeOrderWith` comes free from `primeOrderWith_zpowers`.

## Out of scope

* **The point count** `|E(Fp)[r]| = r` — separate package, route (b), `gcd(r, p-1) = 1` already
  proved.
* **`g2Valid`** — needs a G2 frame codec and an Fp2 model; `fp2Ops` has **no mathlib model at
  all**, so that is a package, not a lemma.
* `Statements.lean`, `Statements.sha256`, Rust, `vendor/`.

## Constraints

* **D-P23 both halves as theorems.** The falsification-deletion gap has been measured **eight
  times** across five packages — deleting falsifications leaves the build green. Respect it.
* **`Instances/` confinement (D-P17)**: `G1Agreement.lean` stays in `Instances/`.
* **Perturbations:** `lake build` for theorems; **`checks.sh` for KAT Bools** — perturbing a
  `Bool` gate leaves the build green, since `kat_gate.py` runs in the gate, not the build.
  Scope perturbations to **code, not comments** (a comment hit produced a false negative).
* **`lake env lean` gotchas:** it does not apply lakefile options, so `autoImplicit` is ON and
  unknown identifiers silently become free variables — pass `-DautoImplicit=false`.
* **RAM (D-P31)**: state expected peak; `--proc-limit 6G --limit 24G`; `--selftest` first.
* **`kat_gate` trap**: an unused `simp` argument in a `#eval`-bearing file fails the gate on a
  green build.
* Do NOT git add or commit. **Leave no scratch in the repo.** Report back even if stuck.
* If a sorry closes, regenerate `SORRY.md` with `scripts/gen_sorry.sh`; verify three-way agreement.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5198 jobs**, 112 modules; `checks.sh` green: **57 tracked sorries**, 1297 KATs
across 87 files, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements hash OK.
**D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Instances/G1Agreement.lean` (**closing section — the wall and both cures
are written there**), `Midfall/Yul/Externals.lean` (`affineAdd`, `affineDouble`, `fpInv`,
`g1PointBytes`, `g1InSubgroup`), `Midfall/Assumptions/Eip2537.lean` (`primeOrderWith_zpowers`,
`g1Valid`), `Midfall/Instances/Bls12_381G1.lean`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- The canonicity walk lands, **or** both recorded cures are shown to fail with the reason.
- **Required finding**: with canonicity resolved, are `g1Add`, `g1Msm1` and the subgroup half of
  `g1Valid` discharged — and is the point count then the **only** G1-side item left before a
  single triple satisfies five of six `Holds` clauses (all six needing the G2 package)?

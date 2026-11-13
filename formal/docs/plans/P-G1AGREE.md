# P-G1AGREE - finish what P-MODEXP started. Four mechanical items, in this order.

Status: READY. P-MODEXP proved the **mathematics** of the agreement theorem at coordinate level
and stopped one mechanical rewrite short of the point-level assembly. It also left a precise
punch-list with time estimates. This package executes that list.

## Steps, in this order. Stop at a boundary rather than half-finishing all four.

### Step 1 - the point-level assembly `emb_add` (~30 min, per P-MODEXP)

Prove `emb P + emb Q = emb (affineAdd fpOps P Q)` from the two coordinate agreements already
proved (`affineAdd_coord_secant`, `affineDouble_coord`).

**The recorded obstruction, and the suggested fix — use theirs, don't rediscover it:** given
`hc1 : ((affineAdd ...).1 : K) = W.addX ...`, the goal
`W.Nonsingular ((affineAdd ...).1 : K) ((affineAdd ...).2 : K)` refuses to rewrite along `hc1`
in every spelling tried (`rw` both ways, `rw at h`, `convert ... using 2`, `heq > heq > e`,
`refine <?_,?_>`). Lean's note: *"target is not type-correct under the implicit transparency
level"* — pointing at the subtype coercion `P : FpFrame |-> P.1` interacting with the
`(· : K)` ascription inside the projection. **Suggested fix: make `FpFrame` a structure with
named fields `x y` instead of a subtype of a pair**, or carry `x3 := (affineAdd ...).1` as
separate haves. Written up in `G1Agreement.lean`'s last section.

**Re-verify that diagnosis rather than trusting it** — it is a recorded premise, and five of
this project's kind-errors came from exactly that.

### Step 2 - `affineSmul` / `n • emb` agreement (~45–60 min)

Fold invariant over `List.range`, using the add/double agreements. **`modPow_fold` is the
template** — same shape, already proved. Needed for `g1Msm1` **and** for the subgroup half of
`g1Valid` (`g1PointMsmValid P` unfolds to `affineSmul fpOps blsR P = (0,0)`).

### Step 3 - `modexpInv_correct`: the byte plumbing (~30–45 min). **Register 58 → 57**

P-MODEXP: the gap is *not* Fermat (that is proved — `modPow_inv` holds at any prime) but
`modexpOutput` parsing via `modexpParse?` over a 6-word concatenation. Needs ~8
`ByteArray`/`Array.extract` slice lemmas: `bytesSlice_append_left/right`, `bytesSlice_full`,
`bytesPad_left/right`, then `modexpParse?` of the frame.

**Named trap: `bs.size` and `bs.data.size` are defeq but not syntactically equal, so `rw`'s
matcher will not cross between them — pick one spelling per step.**

### Step 4 - only if 1–3 land: `gcd(r, p−1) = 1`

The cheap first step of route (b) to the point count, and **the item that re-opens D-P34**.
Provable from `BasePrime`'s existing factorisation of `p−1` — a 255-bit prime `r` is not among
its small factors. A morning's work, not SEA. Land it as a standalone theorem; the full
structure-theorem route is a separate package.

## Constraints

* **D-P23 both halves as theorems.** The falsification-deletion gap has now been measured **four
  times** — deleting falsification theorems leaves the build green. Respect it, don't claim past it.
* **Premise corrections already learned, do not re-earn them:** the short-form literal needs
  **unicode subscripts** `a\u2081 := 0` (ASCII `a1` does not elaborate); ascribe the curve def to
  `Affine K`, not `WeierstrassCurve K`, or dot-projection fails; and `Fact (Nat.Prime pBase)`
  does **not** reach `blsP` by instance search even though `blsP = pBase` is a theorem — restate it.
* **Perturbations by text search can produce false negatives** — P-MODEXP's first `a\u2086`
  perturbation hit the same string inside a header comment and left the build green. Scope edits
  to code, not comments.
* **`Instances/` confinement (D-P17)**: `G1Agreement.lean` is in `Instances/`; keep it there.
* **Perturbations via `lake build`, never `lake env lean`** (stale `.olean`). Whole-repo APFS clone.
* **RAM (D-P31)**: state expected peak; `--proc-limit 6G --limit 24G`; `--selftest` first.
  Recent: 10.57 GiB tree / 3.31 GiB largest.
* **`kat_gate` trap**: an unused `simp` argument in a `#eval`-bearing file fails the gate on a
  green build.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. **Leave no scratch in the repo.**
* If step 3 closes a sorry, regenerate `SORRY.md` with `scripts/gen_sorry.sh` and verify
  three-way agreement (register, `scripts/sorries.sh`, `checks.sh`).

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5198 jobs**, 112 modules; `checks.sh` green: **58 tracked sorries**, **1297
KATs across 87 files**, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK. **D-P32**: Rust pinned to `2d52f24`; work against the pinned templates.

Read first: `Midfall/Instances/G1Agreement.lean` (**especially its last section** — the
recorded obstruction and suggested fix), `Midfall/Assumptions/Eip2537.lean` (`modPow_eq` :264,
`modPow_inv` :319, `fpInv_correct` :364, the surviving `modexpInv_correct` sorry),
`Midfall/Yul/Externals.lean` (`affineAdd`, `affineSmul`, `fpOps`), `Midfall/Assumptions/BasePrime.lean`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Steps landed in order; register **57** if step 3 completes.
- **Required finding**: with `emb_add` and the smul agreement landed, are `g1Add` and `g1Msm1`
  now dischargeable as standalone theorems over the `zpowers` exhibit — and is the point count
  then the **only** thing between here and a single triple satisfying all six `Holds` clauses?

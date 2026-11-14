# P-POINTCOUNT - the last mathematics on the G1 side. **Time-boxed: report tractability either way.**

Status: READY, and **this is the item most likely to be a dead end.** P-G1CODEC proved
`g1CodecZ_g1DecodesWidth_iff`: `g1Decodes` for the real-curve codec is **equivalent to**
surjectivity of `g1zToEip` onto precompile-accepted frames — i.e. `|E(Fp)[r]| = r`. Everything
else on the G1 side is discharged.

**Time-box the exploration to roughly one third of the session.** If the route is not viable,
**stop and report that with specifics** — a well-evidenced "this needs an assumption" is a
successful outcome here, and it is exactly what D-P34 said to produce before falling back.

## What is already proved — do not redo it

* **`gcd(r, p−1) = 1`** (`gcd_r_pBase_sub_one`, one `decide`, ~4 s, **no axioms**).
* `r ∤ p−1` (`r_not_dvd_pBase_sub_one`), `gcd(3, p−1) = 3` (so 3 *does* divide `p−1`).
* `Fact (Nat.Prime pBase)` and `Fact (Nat.Prime r)` both exist.
* `primeOrderWith_zpowers` — `PrimeOrderWith (zpowers x) r` from `x^r = 1` and `x ≠ 1`.
* `r_nsmul_emb_genFrame` and `zpowers_emb_gen_nontrivial`.

## Route (b), and why it is bounded rather than open-ended

The standard argument: `E(Fp)[r]` embeds in `(Z/r)²`; the structure theorem gives
`E(Fp)[r] ≅ Z/d × Z/d'` with `d | d'`; the Weil pairing forces `μ_r ⊆ Fp` for the
two-dimensional case, i.e. `r | p−1`, which **`gcd(r, p−1) = 1` refutes**. So the r-torsion is
cyclic, and since `H1` has order `r`, `E(Fp)[r] = ⟨H1⟩`.

**The gap:** P-G1CODEC checked and mathlib has **neither the n-torsion structure theorem nor the
Weil pairing**. So this is not a one-liner. But it is *fixed-shape number theory*, not SEA —
which is why it is worth one time-boxed attempt.

## Cheaper angles to try FIRST, before any structure theorem

1. **Do we need the full statement?** `g1Decodes` needs surjectivity onto *accepted* frames.
   Accepted = on-curve ∧ `affineSmul fpOps r P = (0,0)`. If a direct injection
   `accepted → ZMod r` can be built by mapping a point to its discrete index **noncomputably**
   (via `Nat.card` comparison or `Exists.choose`), the cardinality may follow without naming the
   group structure. Explore this — it may be the short path.
2. **Count via the Frobenius trace.** `#E(Fp) = p + 1 − t`. For BLS12-381 `t = 2u⁶ − 2u⁵ − u`
   with parameter `u = −0xd201000000010000`, and `#E(Fp) = r`. If the trace formula is
   available or cheap to state, `#E(Fp)[r] = r` follows from `r | #E(Fp)` plus cyclicity — still
   needs cyclicity. **Check whether mathlib has any point-counting at all before investing.**
3. **Reformulate the codec's carrier.** Taking `G₁ := { accepted frames }` makes `g1Decodes`
   trivial but moves the burden to `PrimeOrderWith`, which is the same count. **Verify that
   circularity rather than assuming it** — if the accepted-frame subtype has an easier order
   proof, that is the win.

## If it does not land

**Produce the documented failure D-P34 requires**: which specific mathlib facts are missing, what
each would take, and a precise statement of the assumption that would substitute —
`Nat.card { P // accepted P } = r` as a named hypothesis in `Assumptions/`, gate-enforced. Then
`g1Decodes` and the whole G1 side close, and the trusted base gains exactly one entry.

## Constraints

* **D-P23 both halves as theorems.** The falsification-deletion gap has been measured **ten
  times** — do not claim gate coverage for falsifications.
* **`Instances/` confinement (D-P17)**.
* **Elaborator walls, three known doors** (`affineSmul` pair-`==`, `List.all` over a literal
  list, `nsmul` at a 255-bit literal): **generalise over the thing the literal sits in; never
  raise `maxRecDepth`.**
* **`Point.toAffine` does not exist** in this mathlib; `Group (Additive A)` does not synthesize
  — wrap in `Multiplicative`; the additive carrier is `AddSubgroup.zmultiples`.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.** P-G1CODEC lost 44 KB of fresh proofs to a
  splice whose only symptom was that the file got *shorter* while the build stayed green.
* **Perturbations:** `lake build` for theorems, `checks.sh` for KAT Bools, code not comments.
* **RAM (D-P31)**: `ram_guard.sh --selftest` **FIRST**; state expected peak; `--proc-limit 6G
  --limit 24G`. Recent actual: 4.82 GiB tree / 4.07 GiB largest.
* **`lake env lean`**: pass `-DautoImplicit=false`. No unused `simp` args in `#eval` files.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. Report back even if stuck.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5201 jobs**, 112 modules; `checks.sh` green: **57 tracked sorries**, 1297 KATs
across 87 files, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements hash OK.
**D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Instances/G1Agreement.lean` (`g1CodecZ_g1DecodesWidth_iff`, `g1zToEip`,
`G₁z`, `ptPair`, `frameOf`, `emb`), `Midfall/Assumptions/BasePrime.lean` (the gcd facts and the
factorisation), `Midfall/Yul/Externals.lean` (`g1PointMsmValid`, `affineSmul`),
`Midfall/Assumptions/Eip2537.lean` (`g1Decodes`, `primeOrderWith_zpowers`).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Either `g1Decodes` discharged at the real-curve codec, **or** the documented failure with the
  precise substitute assumption.
- **Required finding**: is the G1 side now four-of-four (or four-of-four-plus-one-named-
  assumption)? And what does that leave between here and a **single** `Holds` term — given
  `pairing2` is only discharged at the exponent model and `g2Valid` needs an Fp2 model?

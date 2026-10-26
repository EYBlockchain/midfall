# P-4a - Phase 4a algebra lemmas, batch 1: the missing primitive-root assumption

Status: READY. Independent of the port chain (needs only Exec/Domain, Exec/Arith and
mathlib), so it can be fired in any gap. It is a **hard prerequisite for M5-M7**: the
per-partial contracts and the Lagrange/telescoping lemmas cannot be stated without it.

## The blocker, verified against the tree

`Midfall/Halo2/Exec/Arith.lean:64-72` defines

    structure FieldConsts (F : Type) where
      numBits : Nat;  s : Nat;  rootOfUnity : F;  zeta : F

Four bare data fields. **There is no hypothesis that `rootOfUnity` has order exactly
2^s, nor that `zeta` has order 3.** `grep -rn orderOf Midfall/` returns nothing, and
`Midfall/Assumptions/` contains only `Pairing.lean`. That file already names the gap in
its own header - "nothing checks that `rootOfUnity` is a primitive 2^S-th root" - but
the gap was reported and never closed with a hypothesis structure, which is what the
plan's gap policy requires ("a missing proof becomes a named hypothesis structure in
Assumptions/; a bare sorry is never allowed").

This is not a defect in the port: the Rust does not check it either, and rule R1 forbids
inventing a check the reference does not have. It is a defect in what the **proofs** are
allowed to assume. The evidence that it bites: `Spec/Lemmas.lean` currently states
`zH_vanishes` with an ad-hoc `(h : omega ^ n = 1)` hypothesis on every call, and its
`rotate_omega_eq` entry says outright that the reduced-index form
`omega^((i+rot) % n) = omega^i * omega^rot` was **deferred rather than approximated**
because it needs order exactly n, not merely dividing n. That deferred lemma is on the
critical path for `lagrange_spec`.

## Deliverable

1. `formal/Midfall/Assumptions/TwoAdicity.lean` defining a named hypothesis structure,
   roughly:

       structure FieldConsts.IsWellFormed {F} [Field F] (fc : FieldConsts F) : Prop where
         root_order : orderOf fc.rootOfUnity = 2 ^ fc.s
         zeta_order : orderOf fc.zeta = 3
         numBits_gt_s : fc.s < fc.numBits

   Exact fields are the implementer's call, but every field must be (a) needed by at
   least one lemma in this batch and (b) discharged for the concrete instances the port
   actually uses. Do not add decorative fields - a hypothesis nobody uses is the R-30
   pattern in `Prop` clothing.

2. **Discharge it for `fc17`** (`Exec/Domain.lean:317`, `ZMod 17`, rootOfUnity = 3,
   s = 4, zeta = 2). This is the only instance in the tree with a decidable field, so it
   is where the definition is shown to be satisfiable and not an inconsistent wish.
   `decide`/`native_decide` is banned outside `Midfall/Instances/`, so do the proof by
   computation there or in a `#eval` gate, and say which.

3. Then the lemmas that were blocked, each stated over an explicit
   `(h : fc.IsWellFormed)`:
   - `omega_order`: `omega ^ n = 1` and `omega ^ i <> 1` for `0 < i < n`, for the
     `omega` that `EvaluationDomain.new` computes (note it is
     `rootOfUnity^(2^(s-extendedK))^(2^(extendedK-k))`, so the proof goes through both
     squaring steps - do not hand-wave the two-level exponent).
   - `zH_vanishes_iff`: `x^n = 1 <-> x in {omega^i | i < n}` - the fact every
     vanishing-argument step silently uses.
   - **the deferred `rotate_omega` mod form**: `omega ^ ((i + rot) % n) =
     omega ^ i * omega ^ rot`. `Spec/Lemmas.lean` explicitly defers this; closing the
     deferral is the point of the batch.
   - `lIRange_closed_form`: `EvaluationDomain.lIRange d x xn r` equals the barycentric
     Lagrange form `omega^r * (x^n - 1) / (n * (x - omega^r))`, given `x <> omega^r`.
     Read the port first: it is `rotateOmega ((x - rotateOmega 1 r)⁻¹ * ((xn - 1) *
     barycentricWeight)) r`, so the lemma is about associativity/commutative folding
     plus what `barycentricWeight` actually is - confirm it is `1/n` before writing the
     statement.
   - `lIRange_delta`: at `x = omega^j` with `j < n`, the r-th entry is `if r = j then 1
     else 0`. **This is the lemma M5's `lagrange_spec` will be stated against.**

4. Update `Spec/Lemmas.lean` to route its existing `zH_vanishes` and `rotate_omega_eq`
   through the new hypothesis, and delete the now-false deferral note. Leave the
   DualMSM/pairing-reorder entries alone - they need no roots.

## Rules

- Gap policy: named hypothesis structures in `Assumptions/`, never a bare `sorry`.
  `SORRY.md` must stay at 4 tracked sorries; if you add one, the gate fails.
- Proof style: proofs live in `*/Lemmas.lean` or `Assumptions/`, not in Exec files
  (R10). Exec files stay computable and proof-free.
- **Every lemma must ship with non-vacuity evidence.** `Spec/Lemmas.lean` already models
  this: it carries explicit counterexamples showing the `hc : c <> 0` hypothesis in
  `dualMsm_scale_check` is necessary, and concrete `ZMod 17` instances showing the
  relations hold for some inputs and fail for others. Do the same: for each new lemma,
  show an instance where it holds and, where the hypothesis is doing work, a field or
  root choice where it fails. A lemma whose hypothesis is decorative is worthless and a
  lemma with no hypothesis at all is usually false.
- `#print axioms` on each new theorem, reported in the output. It must stay within
  `propext, Classical.choice, Quot.sound` plus mathlib - and if `orderOf` drags in
  anything surprising, say so.
- Do NOT edit any Rust file or `Statements.lean`. Do NOT git add or commit.

## Acceptance

`lake build` and `bash scripts/checks.sh` green; `fc17.IsWellFormed` proved; the five
lemmas above stated and proved or, for any you cannot prove, replaced by a named
sub-assumption in `Assumptions/` with a note on exactly what is missing - **do not
weaken a statement silently** (PLAN 12). Report which of the M5-M7 lemmas are now
statable that were not before; that is the point of the package.

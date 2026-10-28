# P-4a - a real root of unity in Fr r. The cheaper of P5's two blockers.

Status: READY, and **cheaper than it looks**. P-AST measured that `EnvAgrees` is
undischargable at the only Surface because the fixture domain is a placeholder:
`fxDom` has `omega := 1`, `omegaInv := 1`, `barycentricWeight := 4`
(`SurfaceFixture.lean:116-119`). So `baryWeight` evaluates **false** and `omegaOrder`
passes only **vacuously** - a domain where the generator is 1 is not a domain.

**This is not a curve problem.** It is arithmetic inside `ZMod r`, and it also unblocks the
Lagrange closed forms, `rotate_omega` mod-arithmetic, and `lIRange` - all of which were
previously flagged as waiting on exactly this.

## Deliverable

`Midfall/Assumptions/TwoAdicity.lean` plus a real fixture domain:

1. **A `FieldConsts.IsWellFormed` predicate**: the root has order exactly `2^s`, and `zeta`
   has order 3 (needed by the `div3` helper). State it as a structure of propositions.
2. **Discharge it for a real field.** The existing precedent is `fc17` (a small field where
   it was proved). **Note the trap already recorded**: `ZMod 17` has no order-3 element, so
   `zeta_order` cannot be discharged there - check which small field actually supports both
   requirements, or state the two conditions separately and discharge what you can.
3. **Exhibit a domain for the fixture**: `omega` of order exactly `2^k` in `Fr r` for the
   real scalar modulus `r`, with `omegaInv` its inverse and `barycentricWeight` its
   inverse of `2^k`. Then `EnvAgrees.omegaOrder` and `EnvAgrees.baryWeight` become
   **dischargeable rather than vacuous** at the fixture.
4. **Replace `fxDom`'s placeholders** and show `EnvAgrees` holds for the fields that were
   previously vacuous.

## Hazards

* **`omega := 1` is the bug class, not just a placeholder.** Any gate that checks
  `omega^(2^k) = 1` passes trivially at 1. **Every new lemma needs a non-vacuity check that
  the order is EXACTLY `2^k`, not a divisor of it** - otherwise you have rebuilt the same
  vacuity in a better-dressed form. D-P23 applies: witness AND falsifiability.
* **`decide`/`native_decide` at the real 255-bit `r` will not reduce.** R-58 and stage 5 both
  hit this. Plan for proofs by `Nat`/`ZMod` reasoning, or exhibit at a small field that
  genuinely has the structure and keep the real-`r` case as a named gap. **Say which you
  did.** Do not silently downgrade to a toy field and call the gap closed.
* **`Fr r` may not have a `2^k` root of unity for arbitrary `k`.** It exists iff `2^k`
  divides `r - 1`. Check the actual two-adicity of BLS12-381's scalar field and state what
  `k` range is legitimate.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50). Numbers from `lake build` and
  `scripts/checks.sh` only.
* **R-41**: every new lemma needs a demonstrated failure mode.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Lean project `formal/`. Build green
at **5144 jobs**; `checks.sh` green: 64 tracked sorries all owned, **1164 KATs across 77
files**, 83 statement fragments, 9 fact families, 7 bundles (6 jointly exhibited), 101
modules reachable, Statements hash OK.

Read first: `docs/plans/P-4a-roots.md` (the earlier draft of this package - **re-derive its
claims, do not trust it**; briefs have been wrong in every package), `Midfall/Assumptions/Pairing.lean`,
`Midfall/Common/Field.lean` (`FieldConsts`), `Midfall/Instances/SurfaceFixture.lean:110-125`
(the placeholder domain), `Midfall/Lowering/Inv.lean` (`EnvAgrees` fields), and
`docs/REVIEW.md` R-47 (the missing root-of-unity hypothesis) and R-62.

**No idle builds.** Re-read what you changed after every edit; multi-line anchored edits have
broken files repeatedly this session.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `EnvAgrees.omegaOrder` and `EnvAgrees.baryWeight` discharged at the fixture, or a named
  gap with the precise arithmetic blocker.
- **Required finding**: which of P5's two blockers is now closed, and does the joint bundle
  `BlkIsEmitter /\ SupportedS /\ EnvAgrees /\ Eip2537.Holds` have any witness yet? P-AST
  warned it is exhibited for only the first two - if you close `EnvAgrees`, say whether a
  **single** declaration naming all four is now possible or whether the curve still blocks it.

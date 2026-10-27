# P-D6 - the Exec refactor (P-SE decision D6), with a gate that does not exist yet

Status: READY and independent of the remaining port. It blocks **P-SE stage 3**, so proof
step P4 cannot start until it lands.

## HEADLINE: the specified safety gate is vacuous for two of its three files

The agreed gate is that "every existing `#eval ... -- expect` token in `Verifier.lean`,
`MultiOpen.lean` and `Native.lean` stays identical". Measured just now:

| file | `#eval` lines |
|---|---:|
| `Exec/Verifier.lean` | 17 |
| `Exec/Kzg/MultiOpen.lean` | **0** |
| `Exec/Native.lean` | **0** |

So for `MultiOpen.lean` - the file whose refactor moves **four transcript squeezes**
(`x1`, `x2`, `x3raw` then the truncation to `x3`, `x4`) - there is no KAT at all to stay
identical. A refactor that silently reorders two of those squeezes, or drops the
`truncatedChallenges` branch, would pass the stated gate while changing the challenge
stream and therefore the whole protocol. **This is the R-41 defect class applied to the
refactor's own acceptance criterion.**

**Therefore stage 0 of this package is: write the gates first.** Do not start the split
until a perturbation of squeeze order in `multiPrepare` reddens something.

## Scope (unchanged from D6)

Two monolithic do-blocks become named phase functions whose composition is
*definitionally* the old function. Bodies move verbatim, statement order unchanged (R1),
~200 lines relocated, no new computation.

* `Exec/Verifier.lean` `verifyAlgebraicConstraints` (lines 796-956): shape checks ->
  `readAlgebra` (returns an `AlgebraRead` record: quotient limb commitments, `x`,
  `splittingFactor`, `xn`, the evaluation arrays) -> `lagrangeTriple` (lifted out of
  `partiallyEvaluateIdentities`, returns `(lLast, lBlind, l0)`) -> `linearize` (tagged
  expressions, linearization query, multi-open queries) -> the existing R-8 error
  collapse.
* `Exec/Kzg/MultiOpen.lean` `multiPrepare` (from line 201): `phaseA` (x1, x2, point
  sets) -> `phaseB` (f_com, truncated x3, q_evals, fEval) -> `phaseC` (x4, final_com,
  v, pi, the DualMSM).

Why: every value the contract writes to memory (`x`, the Lagrange values, x1..x4,
`fEval`, `v`, `PAIRING_LHS/RHS`) is currently a `let` inside those blocks, so `Inv`,
`Snapshot` and the `x not in H` side condition cannot name them. The rejected
alternative - replaying a transcript prefix in the theorem file - is a second copy of
the Fiat-Shamir schedule, which is the R-30/R-32 drift hazard already paid for twice.

## Staging

1. **Gates first, no refactor.** Add KATs to `MultiOpen.lean` and `Native.lean` that pin
   the challenge stream: for a fixed transcript, the sequence of squeezed challenges and
   the resulting `DualMSM` components. Then *prove the gates can fail* by perturbing
   squeeze order (`x1`/`x2` swapped), by dropping the `truncatedChallenges` branch on
   `x3`, and by reordering `phaseB`'s reads. Every one must redden. Report any that does
   not - a gate that cannot see its own scope is not a gate.
2. Add a `Verifier.lean` gate pinning the values the refactor must preserve: `x`,
   `splittingFactor`, `xn`, the `rotations` window, `lIS`, and the linearization query
   list. Same perturbation discipline.
3. Refactor `multiPrepare` into `phaseA`/`phaseB`/`phaseC`; `multiPrepare` becomes their
   composition by definition. Re-run everything.
4. Refactor `verifyAlgebraicConstraints` into `readAlgebra`/`lagrangeTriple`/`linearize`.
   Re-run everything.
5. Add the `AlgebraRead` / `Snapshot` accessors P-SE stage 3 needs, and confirm each
   named value is now reachable from outside the do-block.

Each stage ends with `lake build` + `bash scripts/checks.sh` green.

## Hazards

1. **`StateT Transcript (Except Fault)` composition is not free.** Splitting a do-block
   into three functions means threading the transcript state through each. The
   composition must be *definitional*, not merely extensionally equal - otherwise the
   refactor proves nothing and P-SE still cannot name the intermediate values.
2. **The `x3` truncation is a feature branch inside the sequence** (`MultiOpen.lean`:
   `let x3 := if feat.truncatedChallenges then truncate fc.numBits x3raw else x3raw`).
   It must stay in `phaseB` exactly where it is. R-22/D-P14 make this the deployed
   profile, so a silent change here is not hypothetical.
3. **`rotBounds` uses if / ELSE IF with a (0,0) seed** (`Verifier.lean:845-851`), so an
   all-positive query set gets `min = 0`, not the smallest positive rotation. The
   existing comment says "Kept". Do not "fix" it during the move - that is a behaviour
   change smuggled as a refactor.
4. **`i32Abs` and `wrapI32` are panic and wrap sites** (lines 864-866, R-5/R-9). They
   must move verbatim with their sites.
5. **The empty-`rotations` case is reachable** (line 862-863 says the empty range is what
   makes the slice check reachable rather than theoretical). Gate it after the split.
6. **Do not touch `Statements.lean`** (frozen) and do not edit `Lowering/Types.lean`
   placeholders - P-SE keeps the real versions in `Surface.lean` under new names.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options - every number from `lake build` and `scripts/checks.sh`; line numbers
from `git show HEAD:<path>`), `docs/plans/P-SE-semantic-equivalence.md` decisions D1-D14
(D6 is this package), and `P-SE-evidence/attack.md` - its FIX lines are binding.

**R-41** binds absolutely here: the whole point of staging 1 is that the existing gate
cannot fail. **R1**: bodies move verbatim. **R10**: nothing becomes `partial`.

Binding: PLAN section 4. This is Exec, so `Vec` -> `Array` per PLAN R6's literal text
(the Generator row's `List` convention does not apply here).

**No idle builds.** Do NOT edit Rust files, `Statements.lean`, or `SORRY.md`. Do NOT git
add or commit. Register nothing new unless you add a file.

## Acceptance

- Stages 1 and 2 land **before** any refactor, and their gates are shown to fail by
  named perturbations.
- After stages 3-5: `lake build` and `bash scripts/checks.sh` green; the 17 existing
  `Verifier.lean` KAT tokens unchanged; every named value (`x`, `xn`, `lLast`, `lBlind`,
  `l0`, `x1`..`x4`, `fEval`, `v`, DualMSM left/right) reachable from outside the blocks.
- A finding stating whether P-SE stage 3 can now start, and what `Snapshot`/`Inv` still
  cannot name.

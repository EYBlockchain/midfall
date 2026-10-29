# P-CHALMASS - execute D-P21: split `chalMass` per round. The uniform x3 mass is UNSOUND.

Status: **ADOPTED round 51, still not executed.** This is the standing failure mode I keep
recording - *a decision recorded is not a decision executed*. It is a soundness bug in a
stated budget, it is bounded Lean work, and it needs no human decision.

## The bug

`Security/Challenges.lean:31` applies `s / 2^128` **uniformly** to every round under
`truncatedChallenges`. That is wrong in **different directions for different rounds**, and
one function cannot be both:

* **Six untruncated rounds** (`theta`, `beta`, `gamma`, `trash`, `y`, `x`): the digest is
  reduced into the field and NOT truncated, so the true mass is `3s / 2^256`. Using
  `s/2^128` there is **pessimistic but sound** - it throws away ~127 bits of budget for free.
* **`x3`**: Rust does `squeeze_challenge()` (reduce into the field) and THEN `truncate`
  (`kzg/mod.rs`, `arithmetic.rs:247-252`, `nb_bytes = 16`). The image is `[0, 2^128)` but
  **not uniform**: each truncated value is hit by about `r/2^128 ~ 2^127` field elements,
  so the per-value mass is about `3*ceil(r/2^128)/2^256 ~ 1.5/2^128`.
  **`s/2^128` is too small there - that is the unsoundness.**

## Deliverable

1. **`chalMass F round s`** - takes the round. Return the truncated mass only for rounds
   Rust actually truncates, with the **`ceil(r/2^128)` factor made explicit** rather than
   folded into a constant. Keep the `ENNReal` type - that is ArkLib's error type.
2. **Correct `Spec/Degrees.lean`'s `x3` row** in the same change. R-23 recorded that its
   comment describes truncation as happening *before* field reduction, which is the wrong
   order. The row value `maxSetSize * n` and the comment must agree with the actual order.
3. **Show the unsoundness is real, not rhetorical.** D-P23 requires both halves:
   * a **witness**: the per-round function is satisfiable and gives a *larger* (sound) bound
     for `x3` than the uniform one - i.e. exhibit a parameter set where the old uniform mass
     admits a budget the new one correctly refuses; and
   * a **falsification**: a concrete `s` where `s/2^128 < 1.5/2^128 * s'` style comparison
     makes the old bound provably insufficient. If you cannot exhibit the gap numerically,
     say so - an unsoundness claim with no witness is itself a vacuity.
4. **Update every consumer** of the old `chalMass` arity, and re-check the union-bound sums
   that consume it (the `Q*max + Sum` shape in the security budget).

## Constraint that does NOT change

**Truncation is preserved for output compatibility (D-P14). We do not alter the deployment to
make the proof easier.** This is a *statement* fix, not a code-generation fix.

## Constraints

* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp, verify `git diff --numstat`.
* Register modules (R-50). Numbers from `lake build` and `scripts/checks.sh` only.
* **`decide` reduces for exponentiation at 255-bit `r` but not for inversion** (P-4a2).
* **D-P23 / R-41**: witness AND failure mode for everything; report failures to redden.
* Keep all **12** gate sections green (the baseline pin checker was just wired in).

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5154 jobs**; `checks.sh` green: 64 tracked sorries, **1257 KATs across 83
files**, 111 statement fragments, 12 fact families, 23 spec-theorem bundles, 30 tracked
baseline pins matching, Statements hash OK.

Read first: `docs/design.md` D-P21 (the decision) and D-P14 (the constraint),
`docs/REVIEW.md` R-51/F5 and R-23, `Midfall/Security/Challenges.lean`,
`Midfall/Halo2/Spec/Degrees.lean`, and the Rust truth it must match:
`arithmetic.rs:247-252` and the `squeeze_challenge` then `truncate` order in `kzg/mod.rs`.

**Fact-check the Rust before you port it.** The decision text is from round 51; if the code
has moved, **report the divergence rather than porting a stale claim** - briefs in this
project have been wrong in every single package.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1257.
- `chalMass` is per-round with the `ceil(r/2^128)` factor explicit; `x3` row and comment agree.
- The unsoundness is **exhibited numerically**, or the failure to exhibit it is reported.
- **Required finding**: does the corrected budget change any headline security number - the
  116-bit claim, or the per-round error sums? If a claimed security level moves, say by how
  much and in which direction, since that is the number the human signs off on.

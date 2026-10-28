# P-ENV - strengthen `EnvAgrees.omegaOrder`, and fix the `fc1009` defect in landed code

Status: READY. Two related items from P-4a2, both about field-const well-formedness.

## 1. `EnvAgrees` cannot detect a degenerate generator (statement change - authorised here)

P-4a2 measured it and correctly declined to change it unilaterally: setting `omega := 1`
**and** `omegaInv := 1` with the correct `barycentricWeight` still satisfies all ten
`EnvAgrees` clauses, because `omegaOrder` checks `1^4 = 1` and `omegaInvMul` checks `1*1 = 1`.
Non-vacuity currently lives in a **separate** `fxOmegaOrderExactly` hypothesis plus a KAT,
not in the structure the theorems actually carry.

**Authorised change:** make `EnvAgrees.omegaOrder` require `orderExactly omega n` instead
of `omega ^ n = 1`. This is exactly the vacuity class D-P23 exists to catch - a hypothesis
that a degenerate object satisfies.

* Ripples into `Lowering/Inv.lean`, `Partials.lean`, `Obligations.lean`, and the fingerprint
  gate fragments. Update all of them; **do not weaken the change to avoid the ripple.**
* `fxEnvAgrees` must still discharge - it should, since `fxDom` now carries a genuine
  order-4 generator. If it does not, report which clause fails rather than reverting.
* **D-P23 both halves:** show a witness (the repaired fixture) *and* a falsifiability
  demonstration - the degenerate `omega = omegaInv = 1` pair must now be **rejected** where
  it previously typechecked. That is the whole point of the change; make it a theorem or a
  gate, not a claim.
* Once the structure itself is strong, the separate `fxOmegaOrderExactly` hypothesis may
  become redundant - delete it if so, and say that you did.

## 2. `fc1009` in the tree fails both halves of `IsWellFormed` (defect in landed code)

Confirmed by the orchestrator at **`Exec/Kzg/MultiOpen.lean:374`** and
**`Instances/ChallengeStream.lean:243`**: both use `{ numBits := 5, s := 4, rootOfUnity := 3,
zeta := 2 }`, and P-4a2 **proved** those values fail both `IsWellFormed` conditions.

* Find values that genuinely satisfy `IsWellFormed` at that size (P-4a2 exhibited ZMod 1009
  with `root 62, zeta 374` at `s = 4`), or explain why the existing values are correct for
  the narrower purpose these two sites need.
* **Careful:** these are `#eval`-time fixtures for KAT gates. Changing them may change
  expected values in existing gates. If a gate expectation moves, verify the new value is
  right rather than pasting whatever the code now produces - that is circular.
* If the two sites genuinely do not need well-formedness, record that at the site instead of
  changing values for appearances.

## Constraints

* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54) - use copies, or verify `git diff --numstat`.
* Register modules (R-50). Numbers from `lake build` and `scripts/checks.sh` only.
* **R-41**: every change needs a demonstrated failure mode; report failures to redden.
* Keep all three structural gates green and **accurate** - `check_duplicate_facts.py`,
  `check_statement_fingerprints.py`, `check_hypothesis_bundles.py`. Note P-AST found the
  first two cannot see theorem-binder hypotheses; if your change needs that, say so rather
  than claiming coverage.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5149 jobs**;
`checks.sh` green: 64 tracked sorries all owned, **1172 KATs across 78 files**, 83 statement
fragments, 9 fact families, 8 bundles (7 jointly exhibited), 102 modules, Statements hash OK.

Read first: `Midfall/Assumptions/TwoAdicity.lean` (`orderExactly`, `IsWellFormed`, the
exhibits), `Midfall/Lowering/Inv.lean` (`EnvAgrees`), `Midfall/Instances/SurfaceFixture.lean`
(the repaired domain and `fxEnvAgrees`), and `docs/REVIEW.md` R-62.

**No idle builds.** Re-read what you changed after every edit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count not lower than 1172.
- `EnvAgrees.omegaOrder` requires exact order, with the degenerate pair **proved rejected**.
- The `fc1009` sites either fixed or documented with a reason.
- **Required finding**: does any existing theorem's hypothesis get *stronger* in a way that
  could make it vacuous again? Check the ten `*_spec` theorems and `LoweringCorrect` fields
  that carry `EnvAgrees`.

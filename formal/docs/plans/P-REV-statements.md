# P-REV - statement-only adversarial review of P-SE stages 1-6

Status: APPROVED by the human (round 51, decision 9). **Statements only - not ports.**

## Why this review and not a code review

Per-task adversarial reviews were deferred until the generator's semantic-equivalence
results landed. Six stages later, the evidence is that the deferral cost little on ports -
implementation packages auditing what they inherited found the port defects - but
**statement** defects were caught by luck of sequencing or by outside review, never by a
scheduled pass. Five false-as-written statements were found this session:
`end_to_end_noAcc`'s vacuous RHS, `countdown_or_halt`, `decodeAcc_encode_pointPair`,
`Inv_mono`, and `main_concat`. Plus `supportedQvmBool`, a vacuity **I introduced myself**
while fixing one of those. That is the failure mode a statement review exists to catch.

## Scope - read these in this order

1. `Midfall/Lowering/Obligations.lean` - `LoweringCorrect` and the five derived theorems.
2. `Midfall/Lowering/Surface.lean` - `SupportedS`, `DeploymentW`, `RunVerifier
   /RunContractIR/RunShell`, `LeanAccepts`, `ObsEquiv`.
3. `Midfall/Lowering/Partials.lean` - `blk` and the seven `*_spec` theorems.
4. `Midfall/Lowering/Inv.lean` + `Snapshot.lean` - the invariant and prefix chain.
5. `Midfall/Yul/Bridge.lean` + `Contracts.lean` - the run relation and determinism.
6. `Midfall/Assumptions/{Codec,Eip2537}.lean` - the hypothesis bundles.

## What to hunt - in priority order

* **Vacuity.** Can the RHS of an iff hold for no witness? Does a `forall` range over an
  empty set? Is any hypothesis unsatisfiable? `end_to_end_noAcc` and `Inv_mono` were both
  this class. Check every `LoweringCorrect` field for a way to satisfy it trivially.
* **Wrong direction.** Is a claimed equivalence really one-way? Are the accumulator
  statements exact or conditional? `decodeAcc_injective` was false as written.
* **Statements true for the wrong reason.** Does a hypothesis pin the thing the theorem
  needs, or something adjacent? `supportedQvmBool` returned `true` for a Direct plan
  without consulting the quotient field - the Lean type does not carry the Rust invariant
  that exactly one of `quotient`/`direct` is `Some`. **Look for other places the Lean
  record admits states the Rust cannot.**
* **Quantifier and arity drift.** `EnvAgrees` landed with 5 args where the plan sketched
  7; `Bridge.Dialect` is `@[reducible]` so `calls`/`gas` are erased from `VEnv` and cannot
  be recovered from an `Inv` argument. Check every theorem that takes a `VEnv`.
* **Decorative fields.** A structure field no proof ever consumes. Three
  `LoweringCorrect` fields were deferred rather than faked - check the 12 that were stated.
* **Hypothesis bundles that could be discharged but are not**, and vice versa: hypotheses
  stated as assumptions where the tree can already prove them (stage 5 found
  `IdentityCorrespondence` was in this state).

## Constraints

* **READ-ONLY on Lean files.** Report findings; do not edit statements. If you find a
  false-as-written statement, say so with a concrete counterexample or a witness showing
  the vacuity - that is what made the previous five actionable.
* You MAY add a scratch file under `/tmp` to test whether a hypothesis is satisfiable.
* Do NOT edit `Statements.lean`, Rust, `vendor/`, or any Lean file. Do NOT git add or commit.
* Verify existence claims with `#check`, not grep piped through `head` - that exact error
  produced a false defect claim this session.

## Acceptance

A findings list, each with: the statement, the defect class, a concrete witness or
counterexample, and a suggested repair. **Ordered by severity.** A short list of real
findings beats a long one of style notes; an explicit 'found nothing further in X' is
worth more than a padded list.

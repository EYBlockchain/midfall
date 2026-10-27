# P-09h - `yul_emit.rs`: this IS the Evaluator, and it unblocks a cluster

Status: READY. All three of its dependencies are already ported - `ConstraintSystem`
(Exec/Circuit.lean), `ConstraintSystemMeta` and `Data` (Encoding.lean:364, :551).

**Reframe before you start.** The filename suggests an emitter; the file is
`pub(crate) struct Evaluator<'a>` (yul_emit.rs:49) and 15 items. Two prior packages
named "the Evaluator" as their blocker: P-10 listed 21 unportable `quotient.rs` items
headed by `quotient_identity_parts` (QRS:804), `compact_quotient_computation_blocks
(QRS:2000) and the three `structured_*_loop_block` emitters, and P-11 named the same
things as the reason no Lean term can produce a `LoweringPlan`. **So this package is not
cosmetic - it is the unblock for the pipeline constructors.** Expect follow-on work to
become possible; say in your report which of those 21 items you have unblocked.

Reference: `lowering/quotient_numerator/yul_emit.rs` (1,176 lines, 15 items). Lean
target: `formal/Midfall/Generator/Quotient/Evaluator.lean`.

## What it does

It walks the gate / permutation / lookup / trash arguments of the constraint system and
emits the Yul lines computing each identity's contribution to `quotient_eval_numer` at
the challenge `x`. The module doc is explicit that the name is historical: it
reconstructs the batched numerator `nu_y(x)`, and the verifier stores `-nu_y(x)` as the
expected opening scalar - **that negation is the thing D-P20 called "Yul-side and
modelled nowhere"**. If this file is where it lives, say so; it would close a named gap.

## Hazards

1. **Interior mutability is the porting hazard, not the Yul.** The struct carries
   `Cell<bool>` (`pow5_used`) and two `RefCell`s (`var_counter`, `var_cache`). Lean has
   no mutable borrow, so model these as explicit state threaded through - and note that
   `reset_locals(&self)` and `evaluate_expression(&self, ...)` take `&self` while
   mutating through the `RefCell`s. A port that makes them pure and drops the cache
   changes observable behaviour: the cache means two structurally equal expressions
   reuse one variable name. **Gate that reuse**, and gate that `pow5_used` flips exactly
   when a `q_pow5` call is emitted.
2. **`var_cache` is a `HashMap<String,String>`.** Per R6 you must argue whether its
   iteration order is observable. If it is only ever `get`/`insert`, say so and cite the
   read sites; if anything iterates it, that is a finding.
3. **The emitted strings are the product.** Every line is Yul text destined for the
   contract. Gate concrete small expressions end to end (expression in, exact line list
   out) rather than checking only that something was produced. P-09f's `rowSpellingMatters_ok`
   is the model: it pins that a differently-spelled but semantically similar tree
   produces a different shape.
4. **Cross-check against the QVM.** `VmReference` evaluates `QuotientExpr` trees and
   `VmBuilder` emits QVM bytecode from them. This Evaluator emits *Yul text* for the same
   identities by a different route. Where both exist for the same identity, gate that
   they agree - that is a genuine second-implementation check and the closest thing in
   the tree to what `qvm_yul_refines` will eventually need. If they cannot be compared
   yet, name what is missing.
5. **`Expression<Fq>` handling.** `evaluate_expression` consumes halo2 `Expression`s.
   Exec/Circuit.lean already ports `Expression` and its evaluator, including the
   virtual-selector panic (R4). Reuse it; do not re-derive. If the Rust matches on
   `Expression` variants in an order that matters, mirror the order.
6. **Do not pull in `direct/{mod,emit,layout,validate}.rs`** (M10) or the halo2
   `ConstraintSystem` internals that are not in Exec/Circuit. If an item here needs one,
   report it as a scope error rather than importing around it.
7. **Retire by report.** P-10 and P-11 both wrote headers saying items are blocked on the
   Evaluator. Anything you unblock makes those notes stale - list them precisely
   (file:line) rather than editing them.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`; **register your module** -
R-50), the six `Quotient/` files, and `docs/plans/P-SE-evidence/attack.md` - its FIX
lines are binding and several concern exactly this fold/numerator layer.

**R-41** (perturbations actually run inside each gate's scope; report failures to redden),
**R-48** (own fixture or assert distinctness), **D-P19** (read artifacts at `#eval` time),
**D-P17** (no theorems in a file importing Instances/ - note `LoweringPlan.lean`
deliberately avoids `Generator.Vk` for this reason; do not reintroduce the dependency).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file compiling or
unregistered - never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 732 across 44 files.
- At least 14 gates, including the cache-reuse gate (hazard 1), a `pow5_used` gate, and
  the QVM cross-check (hazard 4) or an explicit statement of why it cannot be done yet.
- **Required finding**: which of P-10's 21 blocked items and P-11's blocker list this
  package actually unblocks, named item by item.

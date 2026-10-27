# P-11 - `plan.rs` + `config.rs` + `mod.rs`: `LoweringPlan`, the thing every §9.5 statement needs

Status: READY. ~721 lines plus a carve-out. **This is the highest-value remaining port
package**, because two named gaps in D-P20 and P-09e both resolve here:
`L.plan.qprog` and the one-argument `Supported.qvm` bridge (`plan.rs:626-643`,
`quotient_operand_model`). Until `LoweringPlan` exists, `Supported` cannot be a field of
a Lean structure and §9.5 stays a sketch.

Reference: `lowering/plan.rs` (643), `lowering/config.rs` (27), `lowering/mod.rs` (51,
`VerifierBuildInputs` already ported in Vk.lean - reconcile, do not duplicate).

**Carve-out from the M10 deferral:** `plan.rs:17` imports
`quotient_direct::{DirectQuotientPlanned, DirectQuotientRendering}` (defined at
`quotient_direct.rs:35` and `:57`). Those two records must port with this package - same
reason `direct/folds.rs` did. Port the records only, not the Direct emitter.

## Hazards

1. **`VerifierBuildInputs` already exists** (Vk.lean, ported early per P-08). `plan.rs`
   is built on it. Do not re-declare it; import it and report if Vk.lean's projection is
   insufficient. P-08 noted `VkQuotientBuild` was a two-field view standing in for the
   real record - if `LoweringPlan` now makes that an alias, say so (P-09a F-4, P-09f
   hazard 5 both flagged it) but do not edit Vk.lean.
2. **`QuotientRendering` has three arms** (`External`, `Compact`, `Direct`) and
   `helper_flags` routes External and Direct through `QuotientComputationBlocks::default()
   .helper_flags()`. P-10 pinned that default field-by-field precisely because this
   package is its consumer - verify the pin is actually used here, and gate all three arms.
3. **The `Supported.qvm` bridge.** `plan.rs:626-643` (`quotient_operand_model`) builds
   the `QuotientOperandModel` from the converged plan. P-09e named this as the missing
   one-argument form. Port it and state explicitly whether `Supported.qvm` can now be
   written as `validateQuotientProgramOperands g.plan = .ok ()`, i.e. whether the
   predicate is now constructible end to end. **This is a required finding.**
4. **`L.plan.qprog`** - name the projection from `LoweringPlan` to the quotient program
   and state whether it is now total, partial (`Option`), or faulting. D-P20's whole-stream
   statement depends on the answer.
5. **`plan.rs` calls `validate().unwrap_or_else(panic)`** on the protocol plan (P-04
   hazard 4) and has its own `assert!`s. R4: each becomes a `Fault.panic` with its site.
   Note P-04 finding F2 - `Fault.panic` carries no payload - so any message these
   `format!` is lost; record which ones.
6. **Do not pull in the Evaluator or `direct/emit.rs`.** P-10 listed 21 `quotient.rs`
   items blocked on them; if `plan.rs` needs one, report it as a scope error rather than
   importing around it.
7. **Retire by report, not edit.** P-10 left a list (VmReference:53-56, VmCertify:208,
   VmTypes:826-867, plus the five unowned `vm/mod.rs` helpers now ruled to stay). Add
   anything this package makes stale.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`; **register your module** -
R-50), and `docs/plans/P-SE-semantic-equivalence.md` sections "Findings that change what
gets written" and "Decisions" - this package feeds stage 2/3 of that plan, so read
`P-SE-evidence/attack.md` FIX lines first; they are binding.

**R-41** (perturbations actually run; report failures to redden), **R-48** (own fixture
or assert distinctness), **D-P19** (read artifacts at `#eval` time), **D-P17** (no
theorems in a file importing Instances/), **D-P16** (two `AccumulatorEncoding` types -
§9.5 means the Generator one), **D-P18** (`Supported.layout` = `WellFormed ∧ validate = .ok ()`).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file compiling or
unregistered - never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 702 across 43 files.
- At least 12 gates, including all three `QuotientRendering` arms (hazard 2).
- **Required findings**: (a) is `Supported.qvm` now constructible end to end? (b) is
  `L.plan.qprog` total/partial/faulting? (c) what still stands between this and the
  per-stream fold-agreement statement D-P20 now calls for?

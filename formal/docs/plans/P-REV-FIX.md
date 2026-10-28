# P-REV-FIX - repair the ten statement defects R-58 found. Highest priority.

Status: READY. Read **docs/REVIEW.md entry R-58** first - the full finding list, with the
two claims the orchestrator verified independently (S.shell.codeBlock occurs at exactly one
site; hasAccumulator is never compared to cfg.accumulator).

## The repairs, in the order I want them

| # | repair | file |
|---|---|---|
| F3 | Add the pin `shell_unfolds : S.shell.codeBlock = S.L.headGuard ++ S.bindLocals ++ S.L.main`. The review notes this is statable TODAY - every side is already a record field - and the fixture satisfies it by rfl. Without it, no field links shell to verifier, and the lowering_equivalence sketch proof hint is false as written. | Surface.lean |
| F2 | Add `plan_hasAccumulator : S.plan.hasAccumulator = S.cfg.accumulator.isSome`. In Rust expected_has_accumulator IS accEncoding.isSome; the Lean copy is unconstrained, so 11 of 13 PartialSpecs fields discharge on a one-Bool lie. | Surface.lean / Inv.lean |
| F6 | Same class: pin `plan.numInstances = cfg.numInstances`; and either delete the dead `Lowered.evaluator` or derive `evaluatorRuntime` from it. | Surface.lean |
| G2 | Pin `encG2` against the G2_BASE / NEG_S_G2 bytes the render embeds. The fixture currently sets encG2 to empty bytes, so NO Eip2537.Holds is satisfiable at that Surface and every field carrying Holds is unexhibited. | Surface.lean / fixture |
| F7 | Add `exists b in S.accFixedBases.toList, b.name = ` + chr(34) + `-G` + chr(34) + ` so the field can fail - it currently holds for the empty table. | Obligations.lean |
| F1 | DEFER `points_subgroup_checked` with the call-trace blocker, like the deferred trio. The review proved its conclusion holds unconditionally; the interim fix is still not a trace. Do not ship a field that cannot fail. | Obligations.lean |
| F4 | Delete `qvmValidated` + `SupportedS.qvm`, or make it decidable about the Surface own quotient program. Both trivially satisfiable and unconsumed. | Surface.lean |
| F5 | Drop `vkDigest_slot0` (derivable from two other pins) or restate what it meant. | Obligations.lean |
| F8 | Make `render_eq_print` the pin the fixture actually satisfies: `astOfMain o = (lower o).map (fun l => l.main)`. | Obligations.lean |
| F10 | Add `EnvAgrees` to `verifier_sound` / `only_two_outcomes`, OR record as a deliberate decision that Eip2537.Holds.g1Msm1 carries it. The sketch had the same asymmetry, so this may be plan-inherited rather than drift - decide and write it down. | Obligations.lean |
| F9 | Decorative bits: `memoryZeroAbove`, `PlanView.consts`, one `finalPairing_sound` extra conjunct, the `model` binder that appears only in its own hypothesis. Clean up or justify. | various |

## Also required: a gate against the root cause

The generalisation is that PlanView, Surface and LoweringPlan each carry a COPY of a fact
the Rust derives once - hasAccumulator, numInstances, evaluator, encG2, the quotient/direct
pair. Every copy without a pin is a vacuity. Add a check asserting each such fact appears
exactly once in the Lean records, or appears twice with a named pin field between them.
Cover at minimum: hasAccumulator, numInstances, evaluator/evaluatorRuntime, encG2,
quotient/direct, shell. Wire it into scripts/checks.sh and DEMONSTRATE it reddens on at
least one defect it targets.

**Be honest in the gate doc about what it cannot catch.** The existing fingerprint gate pins
42 text fragments and lets F1, F7 and F8 through; this new gate pins dependency structure;
neither is a meaning check.

## Constraints

* **Adding a pin may make the fixture unsatisfiable - that is the point.** But you must
  then update `Instances/SurfaceFixture.lean` so `supportedInhabited` still proves, or
  report precisely which pin the fixture cannot meet. **Do NOT weaken a pin to make the
  fixture pass.** If a pin is genuinely wrong, say so and stop.
* `scripts/check_statement_fingerprints.py` needs updating as fields change - keep it green
  AND keep its fragments accurate.
* Do NOT edit `Statements.lean`, Rust files, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50).
* **R-41**: every new pin needs a perturbation showing it can fail. A pin nothing can
  violate is how we got here.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; fingerprint gate green and updated.
- Each of F1-F10 and G2 either repaired or explicitly declined with a reason in the file.
- The duplicate-fact gate exists, is wired into checks.sh, and is shown to redden.
- **Required finding**: after the pins land, is `lowering_equivalence` still only statable,
  or does the shell pin make it provable in principle? Name the remaining gap.

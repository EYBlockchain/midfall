# P-REV2 - second statement review pass, after the repairs. D-P23 requires this.

Status: READY. `P-REV-FIX` landed (`8ed429d`) applying all ten R-58 repairs plus a new
duplicate-fact gate. **D-P23 says statement reviews repeat after every repair round,
because a repair can introduce a new vacuity** - and that is not hypothetical here: the
`supportedQvmBool` bug was introduced while fixing a different vacuity.

## What to check, in priority order

1. **Do the five new pins actually close what they claim?**
   `shell_unfolds`, `plan_hasAccumulator`, `plan_numInstances`, `evaluator_agrees`,
   `encG2_eip`. For each: is there still a way to satisfy the pin while the underlying
   defect survives? `evaluator_agrees` pins only `isSome` agreement, not the object - is
   that enough for what F6 claimed? `shell_unfolds` pins the shell **model** with no
   dispatcher - the agent flagged that M8 must restate it per-arm; check whether anything
   currently reads it as if it were the deployed entry path.
2. **New vacuities introduced by the repairs.** `render_eq_print` was restated as a pin
   `astOfMain o = (lower o).main` for every option. Is that now **too easy** - can a
   Surface set both fields to the same constant and satisfy it while saying nothing about
   rendering fidelity? The first version was criticised for reducing to
   `stmtsBeq fxMain fxMain`; check the replacement is not the same problem wearing a
   different hat.
3. **Orphans from the deletions.** F4 deleted `qvmValidated` + `SupportedS.qvm`; F5 dropped
   `vkDigest_slot0`; F9 removed four decorative items. Check nothing still cites them,
   and that no `SupportedS` field count or gate fragment went stale.
4. **Is the duplicate-fact gate gameable?** `scripts/check_duplicate_facts.py` requires a
   pin whose TYPE names both sides and rejects self-equality. Try to defeat it: a pin that
   names both sides in the type but is trivially true; a family declared with one carrier
   that is actually two; a comment-stripping gap. **It is a text-parsing gate over Lean**
   - those are usually beatable. Report how.
5. **The remaining IR-to-shell gap.** The repair report says `verifier_sound + shell_unfolds`
   is now a derivation and the gap is entirely IR-side: `ObsEquiv` view transport,
   `dialect_deterministic`/`noWritersFuel`, `irCheck` not being alpha-equivalence. Check
   that claim - especially whether `ObsEquiv` really cannot carry `returnData` today, since
   R-58 found the view *does* carry `halted`.

## Constraints

* **READ-ONLY on Lean, Rust and vendor.** Scratch files under `/tmp` are encouraged - a
  vacuity you can demonstrate is worth ten you suspect.
* Verify existence with `#check`, not grep piped through `head`.
* Do NOT git add or commit.

## Acceptance

A findings list ordered by severity. For each: the statement, the defect class, a concrete
witness or counterexample, and a suggested repair. **Explicitly state which of the five new
pins you checked and could not defeat** - a clean bill of health on a specific pin is worth
more than silence about it. If you find nothing new, say so plainly rather than padding.

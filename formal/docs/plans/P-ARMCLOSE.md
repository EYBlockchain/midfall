# P-ARMCLOSE - implement D-P43: make armBody the closed program, then re-run the routed comparison.

Status: CRITICAL PATH. P-RUNLEG proved wrap curveSurface has NO OBSERVATION AT ALL on routed calldata
because ShellModel.armBody S is the un-inlined fragment. D-P43 closes it.

## The change

    ShellModel.armBody S := armProgram S
    -- was: S.L.headGuard ++ S.bindLocals ++ S.L.main

Nothing new is invented - the contract constants are already inlined by D-P39 transform and the two
locals are already bound by bindLocals. This applies the same embedding ONE PLACE FURTHER OUT.

## Then restate the pins - same commit

Every pin citing armBody moves together, with the fingerprint AND duplicate-fact registries updated in
the same commit (D-P27). shell_unfolds already carries inlineContractConstants from D-P39.
ShellModel.armBody_eq_shell_codeBlock, and armBlk_is_the_shell_codeBlock / armBlk_is_the_arm_body in
FrameWalkWitness, all reference the old form. ENUMERATE them before editing, and expect the walk-based
theorems to need re-checking - the block they walked changes, so mainFrameClean,
armDirtyIsTheHeadGuardOnly and the 75-site count may all move.

## THE TEST - re-run the routed comparison

Use RunLegRouted existing setup: cdR, stR, cdR_accepts, arm_derivationR, control_of_arm_block_run and
the [4, STUCK, 4, STUCK] gate. The control already shows the closed arm under the dispatcher gives the
shell own four-byte revert - this change makes that the DEFINITION rather than a control.

- If they agree: M2 is gone. Report that ir_refines is no longer refuted that way and that F2 is now a
  live question on its merits.
- If they still disagree: name the abort-encoding mechanism precisely (revert_error is zero bytes versus
  the emitted fail with selector is four) and STOP. That is D-P44 decision, not yours.

## Also fix: stale prose

RunShellInversion.lean lines 27-32 still say curveSurface.bindLocals is empty and list vk as free.
Since D-P39 it is shellLocalLets and the free names are the 59 contract constants. Correct it and note
what changed - stale prose is a false premise waiting for the next agent.

## Constraints

* Do NOT edit ir_refines or restate its right-hand side. That is F2 and needs its own decision.
* Never weaken a statement to make it provable. If closing armBody breaks a theorem that counted on the
  open form, REPORT IT - do not adjust the theorem.
* lake build green does NOT mean the KAT gates passed - always run python3 scripts/kat_gate.py. (R-71)
* Do NOT round-trip files over about 1500 lines through the read tool - Bridge.lean is 1592, Qvm.lean
  3545, ShellModel.lean about 2400. USE DIRECT FILE ACCESS.
* Fuel per NESTING LEVEL, never per list element - per-element cost 18+ min and 8.7 GB on one rfl.
* D-P23 both halves as theorems. Falsification-deletion gap measured 37 times; gates never call the
  lemmas.
* AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW - AND READ THE BOUNDARY.
* NEVER restore with git checkout on a file holding uncommitted work - use hash-verified copies.
* KAT pins asserted (EXPECTED_KAT_TOTAL = 1352, EXPECTED_KAT_FILES = 99). Move deliberately with a
  reason written into the script.
* gen_sorry.sh is locale-fixed. sha256sum is at /sbin - no shim.
* RAM (D-P31): ram_guard.sh --selftest first; --proc-limit 6G --limit 24G. Never run checks.sh during an
  edit; gate about 14 min.
* Do NOT edit Statements.lean, .sha256, Rust, vendor/, Qvm.lean or InlineConstants.lean. Do NOT git add
  or commit. Leave no scratch. REPORT BACK EVEN IF STUCK.

## Environment

Repo /Users/julian/midfall, branch formal/baseline. Build green at 5221 jobs, 131 modules; checks.sh
green: 39 tracked sorries, 1352 KATs across 99 files, 375 fragments.

Read first: docs/design.md D-P43, Midfall/Yul/ShellModel.lean (armBody, wrap, modelIr, dispatcherCode),
Midfall/Instances/RunLegRouted.lean (the comparison to re-run), Midfall/Lowering/Surface.lean
(armProgram, RunShell, shell_unfolds), Midfall/Instances/FrameWalkWitness.lean and
Midfall/Lowering/FrameWalk.lean (the walks), Midfall/Instances/RunShellInversion.lean (stale header).

## Acceptance

- lake build, checks.sh AND kat_gate.py green.
- armBody closed, all citing pins restated with registries moved in the same commit.
- REQUIRED FINDING: do the two sides now agree on routed calldata? Either answer is a good outcome -
  agree means M2 is gone; disagree means the abort encoding is named and D-P44 is scoped precisely.
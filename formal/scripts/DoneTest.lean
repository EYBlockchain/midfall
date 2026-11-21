import Midfall.Tools.Done
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.Instances.PoseidonV2
import Midfall.Instances.PoseidonValid

set_option autoImplicit false

/-
  scripts/DoneTest.lean - the SELF-TEST of the axiom gate (DG.1, PLAN-V3 section 5).

  Deliberately NOT under Midfall/: this file declares forged axioms (`Forged`, `Forged2`,
  `poseidon_valid_ax`) that `#axiom_sweep` would rightly flag in a library module, and it must not
  be reachable from `Midfall.lean` (`check_orphans.py` walks only `Midfall/`, so a file here is not
  an orphan; `kat_gate.py` walks only `Midfall/`, so the gates below are not counted in
  EXPECTED_KAT_TOTAL). It is run as `lake env lean scripts/DoneTest.lean` by verify.sh --quick, by
  full verify.sh, and by CI. Exit 0 means every `#guard_msgs` expectation below matched: the gate
  REJECTS each counterexample the review found (J-1 a user axiom in place of a sorry, J-14 a
  hand-written axiom with a generated name, the allow-list typo) and ACCEPTS the honest cases.

  PROVENANCE. Imports are `$D/t1.imports` (T1.lean:1-6) with `import Lean` replaced by
  `import Midfall.Tools.Done`, as the card directs; the body is `$D/t1.body` = T1.lean:680-774
  VERBATIM (11 `#guard_msgs` cases). The memo's third part, `$D/donetest.tail` (tooling.md:606),
  is NOT in the evidence tree and its text is not reproduced in tooling.md, so it is NOT here: the
  card counts 18 guarded messages, this file has the 11 that exist. Nothing was invented to fill the
  gap - see the DG.1 report.
-/
open Midfall.Tools.Done

/-! ### (a) PASS: a proved block contract on the three standard axioms. -/
/-- info: assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound: ok (3 named, 0 native) -/
#guard_msgs in
#assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound [propext, Classical.choice, Quot.sound]

/-! ### (b) FAIL: a conditional deployment block contract, with the full PLAN-V2 section 6
    allow-list. The only offender is sorryAx. (The unconditional deployment headline was deleted by
    PL.1/W13, so its `poseidon_valid` cone no longer exists to test here.) -/
/--
error: assert_axioms Midfall.Instances.PoseidonV2.poseidon_block_contracts: 1 axiom(s) outside the allow-list
  sorryAx: an unproved obligation is in the cone
-/
#guard_msgs in
#assert_axioms Midfall.Instances.PoseidonV2.poseidon_block_contracts
  [propext, Classical.choice, Quot.sound, Midfall.Assumptions.blsGT, Midfall.Assumptions.blsGT_group,
   Midfall.Assumptions.blsGT_primeOrder, Midfall.Assumptions.blsGT_module,
   Midfall.Assumptions.bls12_381Pairing]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]

/-! ### (c) A native axiom is rejected unless its owner is listed; accepted when it is. -/
/--
error: assert_axioms Midfall.Instances.PoseidonV2.poseidonModel_isOk: 1 axiom(s) outside the allow-list
  Midfall.Instances.PoseidonV2.poseidonModel_isOk._native.native_decide.ax_1_1: native_decide axiom of `Midfall.Instances.PoseidonV2.poseidonModel_isOk`, which is not in the native list
-/
#guard_msgs in
#assert_axioms Midfall.Instances.PoseidonV2.poseidonModel_isOk [propext, Classical.choice, Quot.sound]

#assert_axioms Midfall.Instances.PoseidonV2.poseidonModel_isOk [propext, Classical.choice, Quot.sound]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]

/-! ### (d) J-1's counterexample: a user axiom in place of the sorry. Every script is green; this is red. -/
axiom poseidon_valid_ax : Midfall.Instances.PoseidonV2.poseidonRender.Valid
theorem uses_user_axiom : Midfall.Instances.PoseidonV2.poseidonRender.Valid := poseidon_valid_ax
/--
error: assert_axioms uses_user_axiom: 1 axiom(s) outside the allow-list
  poseidon_valid_ax: not in the allow-list
-/
#guard_msgs in
#assert_axioms uses_user_axiom
  [propext, Classical.choice, Quot.sound, Midfall.Assumptions.blsGT, Midfall.Assumptions.blsGT_group,
   Midfall.Assumptions.blsGT_primeOrder, Midfall.Assumptions.blsGT_module,
   Midfall.Assumptions.bls12_381Pairing]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]

/-! ### (e) J-14's counterexample: a hand-written axiom with a generated NAME. -/
axiom Forged._native.native_decide.ax_1_1 : False
theorem Forged : False := Forged._native.native_decide.ax_1_1
/--
error: assert_axioms Forged: 1 axiom(s) outside the allow-list
  Forged._native.native_decide.ax_1_1: has the generated NAME but not the generated STATEMENT (closed Bool = true)
-/
#guard_msgs in
#assert_axioms Forged [] native [Forged]

/-! ### (f) the same with the generated STATEMENT shape too: caught by the declaration-range test,
    and independently by the replay. -/
axiom Forged2._native.native_decide.ax_1_1 : decide (1 = 2) = true
theorem Forged2 : False := by have := Forged2._native.native_decide.ax_1_1; simp at this
/--
error: assert_axioms Forged2: 1 axiom(s) outside the allow-list
  Forged2._native.native_decide.ax_1_1: was not generated inside `Forged2` (a hand-written `axiom` with a generated name)
-/
#guard_msgs in
#assert_axioms Forged2 [propext] native [Forged2]

/--
error: replay_native Forged2: 1 failure(s)
  Forged2._native.native_decide.ax_1_1: its Bool evaluates to FALSE (forged or stale)
-/
#guard_msgs in
#replay_native Forged2

/-! ### (g) an honest native_decide: accepted by both. -/
theorem Honest : 2 ^ 10 = 1024 := by native_decide
/-- info: assert_axioms Honest: ok (1 named, 1 native) -/
#guard_msgs in
#assert_axioms Honest [propext] native [Honest]
/-- info: replay_native Honest: ok (1 native axiom(s) re-evaluated to true) -/
#guard_msgs in
#replay_native Honest

/-! ### (h) an allow-list entry that is not an axiom is an error (the list cannot rot by typo). -/
/-- error: assert_axioms Honest: `Honest` is in the allow-list but is not an axiom -/
#guard_msgs in
#assert_axioms Honest [Honest]

/-! ### (i) THE OPEN-PHASE GATE, exactly as it sits in ConeReport.lean after PL.1's re-point:
    `sorryAx` is allowed BY NAME, everything else is already pinned, and the empty native list is
    the D-P71 half of the gate. DONE is the commit that deletes that one token (then (b) is the gate). -/
/-- info: assert_axioms Midfall.LoweringV2.lowering_equivalence_of_blocks: ok (4 named, 0 native) -/
#guard_msgs in
#assert_axioms Midfall.LoweringV2.lowering_equivalence_of_blocks
  [propext, Classical.choice, Quot.sound, sorryAx] native []

/-! ### (j) DG.6: a registered sorry with a proved negation is a RED GATE. The probe below is local to
    this file and is the falsifier the card asks for: on the clean tree the scan finds only this
    deliberate one, so `assert_no_refuted_sorry` reports it instead of printing `ok`. If another
    refuted registered sorry ever appears in `Midfall`, this case reports two hits and fails too. -/
namespace Midfall.Tools.DoneTest

theorem refuted_sorry_probe : (1 : Nat) = 2 := by sorry

theorem refuted_sorry_probe_refuted : ¬ ((1 : Nat) = 2) := by decide

end Midfall.Tools.DoneTest

/--
error: assert_no_refuted_sorry: 1 registered sorry statement(s) are provably false
  Midfall.Tools.DoneTest.refuted_sorry_probe is refuted by Midfall.Tools.DoneTest.refuted_sorry_probe_refuted
-/
#guard_msgs in
#assert_no_refuted_sorry [Midfall]

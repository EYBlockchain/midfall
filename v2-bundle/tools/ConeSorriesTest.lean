import Midfall.Tools.ConeSorries
theorem a : 1 = 1 := sorry
theorem b : 2 = 2 := rfl
theorem c : 1 = 1 ∧ 2 = 2 := ⟨a, b⟩
theorem d : True := sorry
def f : Nat := sorry
theorem e : f = f := rfl
theorem g : (1 = 1 ∧ 2 = 2) ∧ f = f := ⟨c, e⟩
theorem h : True := True.intro
/-- info: cone_sorries c: 1
a -/
#guard_msgs in #cone_sorries c
/-- info: cone_sorries b: 0 -/
#guard_msgs in #cone_sorries b
/-- info: cone_sorries g: 2
a
f -/
#guard_msgs in #cone_sorries g
/-- info: cone_avoids h: ok (1 modules) -/
#guard_msgs in #cone_avoids h [Lean.Elab.Command]
/-- error: cone_avoids h: touches Init.Prelude -/
#guard_msgs in #cone_avoids h [Init.Prelude, Lean.Elab.Command]
/-- info: cone_in h Init.Prelude: 2
True
True.intro -/
#guard_msgs in #cone_in h Init.Prelude
/-- info: imports_avoid: ok (1 modules) -/
#guard_msgs in #imports_avoid [Mathlib.Tactic]
/-- error: imports_avoid: imports Lean.Elab.Command -/
#guard_msgs in #imports_avoid [Mathlib.Tactic, Lean.Elab.Command]

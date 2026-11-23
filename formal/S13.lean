import Midfall.LoweringV3.EndToEndAlgebra
example (a x : Nat) : (true = (a == x)) ↔ (true = (x == a)) := by
  rw [show (true = (a == x)) ↔ ((a == x) = true) from eq_comm,
      show (true = (x == a)) ↔ ((x == a) = true) from eq_comm,
      beq_iff_eq, beq_iff_eq, eq_comm]

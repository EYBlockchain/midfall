import Midfall.LoweringV3.EndToEndAlgebra
set_option maxRecDepth 100000
open Midfall Midfall.Halo2 Midfall.Lowering
example (xl hi lo : Nat) (hxlw : xl < 2^256)
    (hxl : xl ≤ lo)
    (hkey : hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase) :
    hi * 2^256 + xl < Midfall.Assumptions.pBase := by omega
example (xh xl hi lo : Nat) (hxlw : xl < 2^256)
    (hx : xh < hi ∨ (xh = hi ∧ xl ≤ lo))
    (hkey : hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase) :
    xh * 2^256 + xl < Midfall.Assumptions.pBase := by
  rcases hx with hx | ⟨hx, hxl⟩ <;> omega

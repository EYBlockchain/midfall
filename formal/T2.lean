import Midfall.LoweringV3.EndToEndAlgebra
set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Lowering
namespace Midfall.LoweringV3

set_option maxRecDepth 100000
theorem coordLt_pBase (xh xl hi lo : Nat) (hxlw : xl < 2 ^ 256)
    (hkey : hi * 2 ^ 256 + lo + 1 = Midfall.Assumptions.pBase)
    (hx : xh < hi ∨ (xh = hi ∧ xl ≤ lo)) :
    xh * 2 ^ 256 + xl < Midfall.Assumptions.pBase := by
  rcases hx with hx | ⟨hx, hxl⟩ <;> omega

set_option exponentiation.threshold 512
theorem g1WordsOk_of_checks (cd : Bytes) (cptr : Nat) (xh xl yh yl hi lo : Nat)
    (h1 : (cdWord cd cptr).toNat = xh) (h2 : (cdWord cd (cptr + 32)).toNat = xl)
    (h3 : (cdWord cd (cptr + 64)).toNat = yh) (h4 : (cdWord cd (cptr + 96)).toNat = yl)
    (hxh : xh < 2 ^ 128) (hyh : yh < 2 ^ 128)
    (hxlw : xl < 2 ^ 256) (hylw : yl < 2 ^ 256)
    (hkey : hi * 2 ^ 256 + lo + 1 = Midfall.Assumptions.pBase)
    (hx : xh < hi ∨ (xh = hi ∧ xl ≤ lo))
    (hy : yh < hi ∨ (yh = hi ∧ yl ≤ lo)) :
    g1WordsOk cd cptr = true := by
  have hxp := coordLt_pBase xh xl hi lo hxlw hkey hx
  have hyp := coordLt_pBase yh yl hi lo hylw hkey hy
  unfold g1WordsOk
  dsimp only
  rw [h1, h2, h3, h4]
  all_goals
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hxh, hyh⟩, hxp⟩, hyp⟩

end Midfall.LoweringV3

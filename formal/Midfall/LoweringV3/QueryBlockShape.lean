-- |
-- Midfall.LoweringV3.QueryBlockShape
--
-- The verifier-side `rotateOmega` point shape for the easy query blocks:
-- trashcan queries open at `x`, and the common sigma openings all open at `x`.
-- The remaining blocks (advice/instance/permutationZ/lookup/fixed) need their
-- mapM/zip membership inversion; these two are the first entries of the
-- same-order block theorem.
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Logup
import Midfall.Halo2.Exec.Trash

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}

theorem Trash.Evaluated.queries_point (ev : Trash.Evaluated (Fr p) G₁) (x : Fr p)
    (proof idx : Nat) :
    ∀ q ∈ (Trash.Evaluated.queries ev x proof idx).toList, q.point = x := by
  intro q hq
  unfold Trash.Evaluated.queries at hq
  simp only [List.mem_singleton] at hq
  subst hq
  rfl

theorem Permutation.CommonEvaluated.queries_point
    (common : Permutation.CommonEvaluated (Fr p))
    (vkey : Permutation.VerifyingKey G₁) (x : Fr p) :
    ∀ q ∈ (Permutation.CommonEvaluated.queries common vkey x).toList, q.point = x := by
  intro q hq
  unfold Permutation.CommonEvaluated.queries at hq
  simp only [List.mem_toArray, List.mem_map] at hq
  obtain ⟨a, _ha, rfl⟩ := hq
  rfl

end Midfall.LoweringV3

-- |
-- Midfall.Halo2.Exec.VerifyingKey
--
-- Well-formedness of a verifying key: the side conditions the soundness
-- statements need (single-phase, instance shape, commitments in the right
-- group). Phase 2/4 replace the placeholder with the real predicate.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Types
import Midfall.Halo2.Exec.Features

namespace Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
  [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]

/-- Placeholder for the constraint-system well-formedness hypotheses the
    statements quantify over (plan 9.2 `vk.WellFormed F`). -/
def VerifyingKey.WellFormed (_ : VerifyingKey (Fr p) G₁) (_ : Features) : Prop := True

end Midfall.Halo2

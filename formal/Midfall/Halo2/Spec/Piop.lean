-- |
-- Midfall.Halo2.Spec.Piop
--
-- The mathematical verifier (plan Section 6). Phase 4 fills this in from the
-- relation: challenges taken from the hash chain, the vanishing / linearized
-- identity at x, the permutation, logUp and trash identities, and the
-- multi-open checks.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Native

namespace Midfall.Halo2.Spec

open Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- Acceptance of a decoded message stream by the mathematical verifier. -/
def accepts (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Prop := sorry

end Midfall.Halo2.Spec

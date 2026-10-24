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

/-! ## Acceptance by the mathematical verifier - STILL A SORRY, AND IT SHOULD BE

    This is not a fill-in-the-blank: it is Phase 4's main body, and writing it badly
    would be worse than leaving it open. What plan Section 6 asks for is a
    DECLARATIVE predicate - the vanishing/linearized identity at x, the permutation,
    logUp and trash identities, and the multi-open checks - so that
    `verifyMsgs_iff_spec` is a refinement theorem (operational program equivalent to
    a mathematical predicate) rather than a tautology. Defining `accepts` by calling
    the Exec pipeline would make the theorem trivial and the spec worthless.

    Three things it needs that do not exist yet:

    1. A polynomial object. The identities quantify over the advice, fixed and
       permutation *polynomials*; the Exec layer only ever sees their commitments and
       their claimed openings. The spec must either quantify over polynomials and
       relate them to commitments (which is where the AGM representation from
       Security/SRS enters) or state the identities at the opening level, which is
       what the linearization already does.
    2. The challenge derivation as an equation, not a fold. `accepts` must say
       "theta is H applied to the encoding of (repr, instances, advice commitments)"
       for an ARBITRARY H (rule R9), which the transcript now supports but the spec
       has to spell out independently of the Exec fold.
    3. The `inst` shape question flagged at `evalRow`: plan 9.3 types the instance as
       one flat `Array Fr` while plan 9.5's `Supported.instShape` requires two
       instance columns. The spec cannot be written until that is settled, because
       the gate identities quantify over instance columns.

    Owner: Phase 4, after the `inst` shape decision and together with `Spec/Keygen`
    and the ArkLib `ProtocolSpec` instantiation that S2 needs. -/

/-- Acceptance of a decoded message stream by the mathematical verifier. -/
def accepts (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Prop := sorry

end Midfall.Halo2.Spec

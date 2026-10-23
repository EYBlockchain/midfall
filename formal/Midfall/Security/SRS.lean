-- |
-- Midfall.Security.SRS
--
-- The structured-reference-string and algebraic-group-model scaffolding of
-- plan Section 9.4. Everything here is DEFINED, not assumed: the AGM
-- restriction (adversaries must output representations) is a statement about a
-- concrete data type, and q-DLOG hardness is stated over it.
--
-- As elsewhere in Midfall this is abstract over an AdmissiblePairing (D-P1), so
-- `SRS G₁ G₂ N` is a vector of group elements, not a parsed file; importing the
-- concrete SRS from Rust is a Phase 2 concern (plan Section 1 puts keygen out of
-- scope - the VK is imported and transcript_repr is taken as given).
--
-- Notation note: the plan's pseudo-Lean writes `τ • G1.gen` on multiplicative
-- groups. The module structure lives on `Additive G₁`, so the action is spelled
-- out here; `g ^ a` is the same thing in group notation.

import Midfall.Common.Curve

namespace Midfall.Security

open Midfall

variable {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- A size-`N` structured reference string: the powers of tau in G1 plus the G2
    side (rust: ParamsKZG { g, s_g2, g2, ... }). -/
structure SRS (G₁ G₂ : Type) (N : Nat) where
  /-- `g1Pow i` = tau^i • g₁. -/
  g1Pow : Fin N → G₁
  /-- The G2 generator. -/
  g2 : G₂
  /-- `[tau]₂`. -/
  sg2 : G₂

/-- The honest setup: sample tau and derive every power. This is the
    mathematical spec of keygen, not the ceremony. -/
def SRS.gen (N : Nat) (τ : ZMod p) : SRS G₁ G₂ N where
  g1Pow := fun i => Additive.toMul ((τ ^ i.val) • Additive.ofMul P.g₁)
  g2 := P.g₂
  sg2 := Additive.toMul (τ • Additive.ofMul P.g₂)

/-- An AGM representation of a group element: the element together with the
    coefficients expressing it in the SRS basis (plan 9.4 Rep). -/
structure Rep (p : Nat) (G₁ : Type) (N : Nat) where
  pt : G₁
  coeff : Fin N → ZMod p

/-- The representation really denotes the element: the claimed point equals the
    SRS-basis combination of its coefficients. -/
def Rep.Valid {N : Nat} (s : SRS G₁ G₂ N) (r : Rep p G₁ N) : Prop :=
  Additive.toMul (∑ i : Fin N, (r.coeff i) • Additive.ofMul (s.g1Pow i)) = r.pt

end Midfall.Security
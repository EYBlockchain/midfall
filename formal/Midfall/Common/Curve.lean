-- |
-- Midfall.Common.Curve
--
-- The algebraic surface every Midfall statement is abstract over.
--
-- Design decision D-P1 (docs/design.md): the Lean ecosystem has no BLS12-381
-- (no base field, no Fp2/Fp12, no G1/G2/GT, no pairing -- see
-- docs/ecosystem.md), and Section 1 of the plan already allows an unproven
-- pairing to become a named hypothesis. Rather than construct a curve the
-- proofs do not need, everything is stated over an `AdmissiblePairing` shaped
-- exactly like the parameters ArkLib's KZG takes
-- (ArkLib/Commitments/Functional/KZG/Basic.lean:47-52), so ArkLib's theorems
-- apply to it verbatim. The concrete BLS12-381 instance is discharged once, in
-- Midfall/Assumptions/Pairing.lean.
--
-- Bilinearity is carried by the *type*: a curried `LinearMap` between the
-- additive forms of the three groups is precisely a `ZMod p`-bilinear pairing.
-- Non-degeneracy is the field `hNonDeg`, stated on the distinguished
-- generators -- which is all KZG needs (ArkLib's own hypothesis is
-- `hpair : pairing g₁ g₂ ≠ 0`).

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import ArkLib.Data.GroupTheory.PrimeOrder

namespace Midfall

/-- The scalar field of an admissible pairing of characteristic `p`.
    For BLS12-381 this is CompPoly's `BLS12_381.ScalarField = ZMod r`. -/
abbrev Fr (p : ℕ) := ZMod p

/-- An asymmetric pairing with exactly the structure ArkLib's KZG theorems
    assume: three prime-order groups over `ZMod p`, a bilinear (by type) map,
    and non-degeneracy on the chosen generators. -/
class AdmissiblePairing {p : outParam ℕ} [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type*)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] where
  /-- The pairing: bilinear by type. -/
  e : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ)
  /-- Distinguished generator of `G₁` (the SRS base). -/
  g₁ : G₁
  /-- Distinguished generator of `G₂` (the SRS base). -/
  g₂ : G₂
  /-- `g₁` is not the identity. -/
  hG₁ : g₁ ≠ 1
  /-- `g₂` is not the identity. -/
  hG₂ : g₂ ≠ 1
  /-- Non-degeneracy on the generators: `e(g₁, g₂) ≠ 1` (written `≠ 0` in the
      additive form of `Gₜ`). -/
  hNonDeg : e (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0

namespace AdmissiblePairing

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type*}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  {P : AdmissiblePairing G₁ G₂ Gₜ}

end AdmissiblePairing

end Midfall

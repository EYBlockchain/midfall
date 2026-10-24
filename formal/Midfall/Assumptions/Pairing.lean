-- |
-- Midfall.Assumptions.Pairing
--
-- The single place a curve-specific fact enters Midfall.
--
-- Plan Section 1 allows an unproven pairing to become a named hypothesis here,
-- and D-P1 (docs/design.md) decided to formalise generically over an
-- `AdmissiblePairing` because no Lean library has BLS12-381 at all
-- (docs/ecosystem.md §1a: CompPoly has only the scalar field; ArkLib has zero
-- hits for bls; mathlib has no elliptic-curve Weil pairing). D-P6 moved the
-- point codecs into `G1Codec` fields. R-3 recorded that `FieldConsts` is a
-- trust boundary: nothing checks that `rootOfUnity` is a primitive 2^S-th root
-- or that `zeta` has order 3, and a wrong value silently changes the extended
-- domain and the coset.
--
-- This file therefore does two things: it pins the two moduli and the
-- two-adicity as *data* (with the scalar field tied to CompPoly's, proved
-- below), and it states `BLS12_381Data`, the hypothesis structure that a real
-- instantiation must discharge. Per the gap policy there is no `sorry` here: a
-- hypothesis is a binder, not a hole.

import CompPoly.Fields.BLS12_381.Basic
import Midfall.Common.Curve
import Midfall.Common.Codec
import Midfall.Halo2.Exec.Arith

namespace Midfall.Assumptions

open Midfall
open Midfall.Halo2

/-- rust: curves/src/bls12_381/scalar.rs, and CompPoly's own definition.
    Taken from CompPoly rather than restated, so the two cannot drift
    (CompPoly/Fields/BLS12_381/Basic.lean:22). -/
abbrev r : ℕ := BLS12_381.scalarFieldSize

-- CompPoly already provides `Fact (Nat.Prime scalarFieldSize)`

/-- Midfall's generic scalar field at the BLS12-381 modulus is *definitionally*
    CompPoly's `BLS12_381.ScalarField`. This is the "proof that it equals the
    ecosystem definition" the plan's gap policy asks for when we implement a
    piece ourselves rather than importing it. -/
theorem fr_eq_compPoly : (Fr r) = (BLS12_381.ScalarField) := rfl

/-- The BLS12-381 base field modulus p (the field EIP-2537 points' coordinates
    live in). CompPoly does not have it (docs/ecosystem.md §1a: "base field Fq
    not found"), so it is a literal here. It is *checked* against the EIP-2537
    precompile behaviour on revm in Phase 5, not assumed: a wrong p would make
    the padded-coordinate validity tests disagree with the node.

    Not used by any proof below - it is here so the number lives in one place. -/
def pBase : ℕ :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- BUG FIXED 2026-10-24 (docs/REVIEW.md R-20, found by cross-agent review while
    porting Yul/Externals): this literal was the BLS12-**377** base modulus - 385
    bits and congruent to 1 mod 4 - not BLS12-381's, which is 381 bits and
    congruent to 3 mod 4 (the value EIP-2537 states, and which the EIP relies on
    for square roots). The generator agrees with the EIP: Constants.sol renders
    p-1 as BLS_P_HI || BLS_P_MINUS_ONE_LO, ending in ...ffffffffaaaa.

    The check below is what should have caught it at the time and is now a CI gate:
    a modulus is not just a big number, and the two BLS curves' moduli share a
    50-digit prefix, so a transcription slip is invisible to the eye. -/
-- A decidable check rather than a theorem: native_decide is confined to
-- Midfall/Instances/ by the CI gate, and `decide` cannot reduce a 381-bit
-- comparison economically in the kernel. scripts/checks.sh evaluates this.
def pBaseKats_ok : Bool :=
  pBase < 2 ^ 381 && pBase ≥ 2 ^ 380 && pBase % 4 = 3 &&
  -- the two BLS moduli share a 50-digit prefix; only the tails differ
  pBase % 0x100000000 = 0xffffaaab &&
  r < 2 ^ 255 && r ≥ 2 ^ 254 && r % 4 = 1

#eval pBaseKats_ok   -- expect true, and scripts/checks.sh asserts it
end Midfall.Assumptions

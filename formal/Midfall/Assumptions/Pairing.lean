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
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a06eb9650edc43970ae792c8d1bfa739f9e3d100cb9

/-- The two-adicity of r - 1. CompPoly documents 32
    (CompPoly/Fields/BLS12_381/Basic.lean:14) and its Pratt certificate factors
    out 2^32, so this is checkable rather than folklore; halo2 reads it as
    `F::S`, and domain.rs:53 asserts `extended_k <= F::S`. -/
def sTwoAdicity : Nat := 32

/-- NUM_BITS for the scalar field: 255 (r is a 255-bit prime). halo2 reads it
    as `F::NUM_BITS`; Exec/Arith.truncate halves it to decide how many bytes of
    a challenge to keep under truncated-challenges. -/
def numBitsScalar : Nat := 255

/-- The BLS12-381 data Midfall needs and cannot construct (D-P1, D-P6, R-3).

    A class rather than a structure so that the group and module instances can
    be parent parameters: `AdmissiblePairing`'s own `p` is an outParam (D-P7),
    and it is pinned here by the `Module (ZMod r)` binders.

    What is deliberately NOT claimed: that `ofCompressed?` really is
    "on-curve and torsion-free" in the sense of curves/src/bls12_381/g1.rs:369-371.
    Stating that needs Fp, which no Lean library has, so the semantic tie between
    the codec and the curve is validated externally - by the EIP-2537 relations
    and the revm differential (plan Section 7) - rather than proved. What IS
    claimed below is everything the port actually relies on: widths, round-trips,
    surjectivity of the encoding, and the algebraic properties of the roots of
    unity that Exec/Domain silently assumes. -/
class BLS12_381Data (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ r] [PrimeOrderWith G₂ r] [PrimeOrderWith Gₜ r]
    [Module (ZMod r) (Additive G₁)] [Module (ZMod r) (Additive G₂)]
    [Module (ZMod r) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ] where
  /-- The point codecs (D-P6). -/
  g1Codec : G1Codec G₁
  /-- The ff::PrimeField / WithSmallOrderMulGroup<3> constants Exec/Domain and
      Exec/Arith read off the type (rule R9). -/
  fieldConsts : FieldConsts (Fr r)

namespace BLS12_381Data

variable {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ r] [PrimeOrderWith G₂ r] [PrimeOrderWith Gₜ r]
  [Module (ZMod r) (Additive G₁)] [Module (ZMod r) (Additive G₂)]
  [Module (ZMod r) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]
  (D : BLS12_381Data G₁ G₂ Gₜ)

-- The hypotheses below are *fields of a second layer* rather than of the class
-- itself, so that a partial instantiation (codecs without the algebraic facts)
-- still typechecks while a proof can demand the facts it needs. This is the
-- plan's "named hypothesis structure" idiom applied twice: data first, then the
-- properties a given theorem depends on.

/-- The algebraic properties Exec/Domain needs and never checks (R-3).

  * `hzeta` - domain.rs:82 sets `g_coset_inv = g_coset.square()`, which is an
    inverse only because zeta has order 3. Nothing in the Rust verifies this.
  * `hroot` - domain.rs:55-63 takes extended_omega to
    root_of_unity^(2^(S - extended_k)) and domain.rs:91-98 loops until the coset
    step returns to its start. With a non-primitive root the Rust loop can spin
    forever; the ported `EvaluationDomain.new` fails at the domain.rs:98 point
    instead, which is the one place the two can differ (see Exec/Domain).
  * `hnumBits`, `hs` - the two constants truncate and the extended_k bound read. -/
structure Hypotheses (fc : FieldConsts (Fr r)) where
  hzeta : fc.zeta ^ 3 = 1 ∧ fc.zeta ≠ 1
  hroot : fc.rootOfUnity ^ (2 ^ fc.s) = 1 ∧
          ∀ m : Nat, 0 < m → m < 2 ^ fc.s → fc.rootOfUnity ^ m ≠ 1
  hnumBits : fc.numBits = numBitsScalar
  hs : fc.s = sTwoAdicity

/-- What the codecs must satisfy for the port to mean anything: the padded
    encoding round-trips, the compressed encoding is canonical, every point has
    a compressed encoding (so a proof can name any r-torsion point), and the
    widths are the EIP-2537 ones the transcript and the contract both assume. -/
structure CodecHypotheses (c : G1Codec G₁) where
  eipRoundtrip : c.eipRoundtrip
  compressedRoundtrip : c.compressedRoundtrip
  surjective : ∀ Q : G₁, ∃ b : Bytes, c.ofCompressed? b = some Q
  compressedWidth : ∀ b : Bytes, b.size ≠ g1CompressedWidth -> c.ofCompressed? b = none
  eipWidth : ∀ b : Bytes, b.size ≠ g1EipWidth -> c.ofEip? b = none
  identityEncodesToZero : c.toEip 1 = ByteArray.mk ((List.replicate 128 0).toArray)

end BLS12_381Data

end Midfall.Assumptions

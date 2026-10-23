-- |
-- Midfall.Common.Codec
--
-- Point and scalar encodings (plan Section 9.1). The EIP-2537 forms matter
-- twice over: the transcript absorbs 128-byte padded coordinates, and the
-- subgroup question (G1ADD does not check membership, plan Section 13) is
-- stated here.

import Midfall.Common.Curve
import Midfall.Common.Bytes

namespace Midfall

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
  [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]

/-- Challenge derivation: the big-endian digest reduced into the scalar field
    (rust: proofs/src/transcript/implementors.rs:29-39). -/
def frOfDigest (d : H256) : Fr p := Nat.cast d.toNat

/-- The curve equation's point type, i.e. *all* Fp-points, not only the
    r-torsion: EIP-2537 G1ADD performs no subgroup check, so the arithmetic the
    precompile does lives here. Placeholder until the curve instance lands
    (design decision D-P1). -/
abbrev E1 (Fp : Type) : Type := Fp × Fp

/-- Compressed G1 decoding: on-curve and torsion-free
    (rust: curves/src/bls12_381/g1.rs:369-371). -/
def G1OfCompressed? (_ : Bytes) : Option G₁ := sorry

/-- EIP-2537 padded decoding: 16 zero bytes || x || 16 zero bytes || y, each
    coordinate < p, on-curve; the all-zero word pair is the identity. -/
def E1OfEip? (_ : Bytes) : Option (E1 (Fr p)) := sorry

/-- EIP-2537 decoding into the r-torsion: the padded decode followed by the
    subgroup test. This is where a point that passed G1ADD can still be
    rejected, and the reason L4 (plan 9.5) has to argue every proof point
    reaches a subgroup-checking call. -/
-- The intended definition is (E1OfEip? b).bind toSubgroup?, once the curve
-- instance supplies the subgroup projection; see Assumptions/Pairing.lean.
def G1OfEip? (_ : Bytes) : Option G₁ := sorry

end Midfall

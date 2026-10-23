-- |
-- Midfall.Common.Codec
--
-- Point and scalar encodings (plan Section 9.1). The EIP-2537 forms matter
-- twice over: the transcript absorbs 128-byte padded coordinates, and the
-- subgroup question (G1ADD does not check membership, plan Section 13) is
-- stated here.
--
-- Design decision D-P6 (docs/design.md): the plan writes these as plain defs
-- over a concrete BLS12-381 (`G1.ofCompressed?`, `E1.ofEip?`, `G1.ofEip?`,
-- `E1.toEip`). Under D-P1 there is no concrete curve in the Lean ecosystem, so
-- the curve-dependent half becomes the *fields* of `G1Codec` (rule R9: a trait
-- becomes a structure of functions) and is discharged once, in
-- Assumptions/Pairing.lean, when the curve instance lands. The field-level
-- codecs below are fully concrete: `Fr p = ZMod p` is computable, and
-- canonicity is a decidable bound, so nothing here is a `sorry`.

import Midfall.Common.Curve
import Midfall.Common.Bytes

namespace Midfall

/-- Challenge derivation: the big-endian digest reduced into the scalar field
    (rust: proofs/src/transcript/implementors.rs:20-39,
    sample_keccak_digest_be_mod_r: BigUint::from_bytes_be(&h) % r, then
    from_repr, which is always canonical after the reduction). -/
def frOfDigest {p : ℕ} [Fact (Nat.Prime p)] (d : H256) : Fr p := Nat.cast d.toNat

/-- rust: ff::PrimeField::to_repr for the BLS12-381 scalar field: the canonical
    value in 32 little-endian bytes. This is the *wire* order
    (proofs/src/transcript/implementors.rs:322-324, `to_bytes`). -/
def frToRepr {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) : Bytes :=
  natToBytesLE x.val 32

/-- rust: proofs/src/transcript/implementors.rs:327-334 (`read` for Fq):
    `PrimeField::from_repr`, which is none unless the little-endian value is
    strictly below the modulus. Plan rule R7: from_repr checks canonicity. -/
def frOfRepr? {p : ℕ} [Fact (Nat.Prime p)] (b : Bytes) : Option (Fr p) :=
  if b.size == 32 && bytesToNatLE b < p then some (Nat.cast (bytesToNatLE b)) else none

/-- rust: proofs/src/transcript/implementors.rs:316-320 (`to_input` for Fq):
    the repr reversed, i.e. big-endian. The transcript absorbs big-endian and
    transmits little-endian; the two must not be confused. -/
def frToInputBE {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) : Bytes :=
  natToBytesBE x.val 32

/-- The curve equation's point type, i.e. *all* Fp-points, not only the
    r-torsion: EIP-2537 G1ADD performs no subgroup check, so the arithmetic the
    precompile does lives here. Placeholder until the curve instance lands
    (design decision D-P1). -/
abbrev E1 (Fp : Type) : Type := Fp × Fp

/-- The point codecs the transcript and the lowering need (plan 9.1
    `G1.ofCompressed?` / `G1.ofEip?` / `E1.toEip`, plan Section 4 module map
    "G1 `to_input` 128B EIP-2537, wire 48B").

    Each field is one Rust impl:

    * `ofCompressed?` — rust: proofs/src/transcript/implementors.rs:304-311
      (`read` for G1Projective) calling `GroupEncoding::from_bytes`, which for
      BLS12-381 is on-curve AND torsion-free
      (curves/src/bls12_381/g1.rs:369-371). A point that is on the curve but not
      in the r-torsion is rejected *here*, at transcript level.
    * `toCompressed` — rust: implementors.rs:300-302 (`to_bytes`), the 48-byte
      wire encoding.
    * `toEip` — rust: implementors.rs:283-299 (`to_input`): 16 zero bytes ‖
      x_BE(48) ‖ 16 zero bytes ‖ y_BE(48), and 128 zero bytes for the identity
      (the EIP-2537 convention, not the BLS-spec 0x40-leading-byte form).
    * `ofEip?` — the decode of `toEip`, used by the contract side and by L4
      (plan 9.5). It is the *subgroup-checked* decode: the plan's
      `G1.ofEip? b = (E1.ofEip? b).bind toSubgroup?`. -/
structure G1Codec (G₁ : Type) where
  ofCompressed? : Bytes → Option G₁
  toCompressed : G₁ → Bytes
  toEip : G₁ → Bytes
  ofEip? : Bytes → Option G₁

/-- The 48-byte compressed width and the 128-byte EIP-2537 padded width, pinned
    so a wrong-length repr is a shape error rather than a silent decode failure. -/
def g1CompressedWidth : Nat := 48
def g1EipWidth : Nat := 128

/-- `toEip` round-trips through `ofEip?` on the nose: the padded encoding is
    injective and the decode is total on its image. Stated as a decidable
    property of a `G1Codec`; the concrete instance proves it in
    Assumptions/Pairing.lean. -/
def G1Codec.eipRoundtrip {G₁ : Type} (c : G1Codec G₁) : Prop :=
  ∀ P : G₁, c.ofEip? (c.toEip P) = some P

/-- `ofCompressed?` only ever returns points whose compressed encoding is the
    one it was given, i.e. the 48-byte encoding is canonical. Without this the
    transcript would be malleable: two byte strings absorbing to the same
    `to_input` but decoding to different points is exactly the gap L4 closes. -/
def G1Codec.compressedRoundtrip {G₁ : Type} (c : G1Codec G₁) : Prop :=
  ∀ b : Bytes, ∀ P : G₁, c.ofCompressed? b = some P → c.toCompressed P = b

end Midfall

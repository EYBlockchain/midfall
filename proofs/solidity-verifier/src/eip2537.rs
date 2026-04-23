//! Helpers for converting midnight-curves types to/from the wire formats
//! required by the EIP-2537 BLS12-381 precompiles (Prague EVM):
//!
//! * G1 point: 128 bytes = `pad16 || x(48, BE) || pad16 || y(48, BE)`.
//! * G2 point: 256 bytes = `pad16 || x_c0(48, BE) || pad16 || x_c1(48, BE)
//!                        || pad16 || y_c0(48, BE) || pad16 || y_c1(48, BE)`.
//! * Fr scalar: 32 bytes BE.

use ff::PrimeField;
use group::{prime::PrimeCurveAffine, UncompressedEncoding};
use midnight_curves::{Fq, G1Affine, G1Projective, G2Affine};

/// Encode a G1Affine point using the EIP-2537 128-byte format.
pub fn g1_to_eip2537(p: &G1Affine) -> [u8; 128] {
    let mut out = [0u8; 128];
    if bool::from(p.is_identity()) {
        return out;
    }
    // midnight_curves `to_uncompressed` is 96 bytes: x(48) || y(48), big-endian.
    let uncompressed = p.to_uncompressed();
    let u = uncompressed.as_ref();
    out[16..64].copy_from_slice(&u[0..48]);
    out[80..128].copy_from_slice(&u[48..96]);
    out
}

pub fn g1_projective_to_eip2537(p: &G1Projective) -> [u8; 128] {
    g1_to_eip2537(&G1Affine::from(*p))
}

/// Encode a G2Affine point using the EIP-2537 256-byte format.
/// Note: BLS12-381 G2 uses Fp2 = c0 + c1*u, and EIP-2537 serialises x as
/// `x.c0 || x.c1` (each as 64 padded bytes), same for y.
pub fn g2_to_eip2537(p: &G2Affine) -> [u8; 256] {
    let mut out = [0u8; 256];
    if bool::from(p.is_identity()) {
        return out;
    }
    // midnight_curves `to_uncompressed` for G2 is 192 bytes and uses the
    // canonical BLS ordering: x.c1 || x.c0 || y.c1 || y.c0 (each 48 BE).
    // EIP-2537 expects x.c0 || x.c1 || y.c0 || y.c1, so we swap per pair.
    let ub = p.to_uncompressed();
    let u = ub.as_ref();
    let x_c1 = &u[0..48];
    let x_c0 = &u[48..96];
    let y_c1 = &u[96..144];
    let y_c0 = &u[144..192];
    out[16..64].copy_from_slice(x_c0);
    out[80..128].copy_from_slice(x_c1);
    out[144..192].copy_from_slice(y_c0);
    out[208..256].copy_from_slice(y_c1);
    out
}

/// Encode an Fq scalar (the BLS12-381 scalar field element used by
/// midnight-proofs) as a 32-byte big-endian value. The field's canonical
/// `to_repr` is little-endian, so we reverse.
pub fn fq_to_be(f: &Fq) -> [u8; 32] {
    let mut le = f.to_repr();
    le.reverse();
    le
}

pub fn fq_to_be_hex(f: &Fq) -> String {
    hex::encode(fq_to_be(f))
}

// SPDX-License-Identifier: CC0-1.0
//! Proof repacking for the Solidity-facing ABI.
//!
//! Midnight proof bytes keep compressed G1 commitments and little-endian
//! scalars; generated Solidity expects EIP-2537 padded G1 words and
//! big-endian scalar words. This module performs that deterministic boundary
//! conversion.

use ff::PrimeField;
use group::GroupEncoding;
use midnight_curves::{Fq, G1Affine};

use crate::{
    api::{GeneratorError, RepackError},
    lowering::{
        layout,
        quotient_numerator::vm::{scalar_le_to_be_word, RepackedProofLayoutPlan},
        VerifierBuildInputs,
    },
};

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Repack a midnight-proofs proof from the on-the-wire compressed
    /// form (each G1 = 48 bytes ZCash compressed) into the EIP-2537
    /// padded form (each G1 = 4 × 32-byte BE words) and rewrites scalar
    /// proof elements from midnight-proofs' canonical LE bytes into
    /// canonical BE calldata words. This is the Solidity-facing proof
    /// shim; the native proof bytes remain unchanged.
    ///
    /// This is the off-chain repack step the verifier expects: the
    /// EVM does **not** run the modexp-based BLS12-381 decompression
    /// at every G1 site (which would cost ~80 kg / commitment); the
    /// caller pays that cost off-chain once.
    ///
    /// The walk is driven entirely by the bound `&self.vk` /
    /// `&self.meta` (so it correctly handles the non-trivial proof
    /// shapes the codegen produces: per-phase advices, lookup
    /// multiplicities + chunked helpers + accumulators, perm Z
    /// products, trashcans, quotient limbs, eval block, dummy evals
    /// from `outer-fewer-point-sets`, f_com, q_evals per point set, pi).
    pub(crate) fn repack_proof(
        &self,
        plan: &RepackedProofLayoutPlan,
        compressed: &[u8],
    ) -> Result<Vec<u8>, RepackError> {
        use group::prime::PrimeCurveAffine;

        let prefix_g1_count = plan.prefix_g1_count();
        let expected_compressed_len = plan.compressed_len();
        if compressed.len() != expected_compressed_len {
            return Err(RepackError::LengthMismatch {
                expected: expected_compressed_len,
                actual: compressed.len(),
                prefix_g1: prefix_g1_count,
                num_evals: plan.num_evals,
                num_point_sets: plan.num_point_sets,
                feature_profile: crate::feature_profile(),
            });
        }

        let mut out: Vec<u8> = Vec::with_capacity(plan.repacked_len());
        let mut cursor = 0usize;
        let push_g1 = |cursor: &mut usize, out: &mut Vec<u8>| -> Result<(), RepackError> {
            let mut comp = <G1Affine as GroupEncoding>::Repr::default();
            comp.as_mut()
                .copy_from_slice(&compressed[*cursor..*cursor + layout::G1_COMPRESSED_BYTES]);
            let cur = *cursor;
            *cursor += layout::G1_COMPRESSED_BYTES;
            let Some(pt) = Option::<G1Affine>::from(<G1Affine as GroupEncoding>::from_bytes(&comp))
            else {
                return Err(RepackError::InvalidCompressedG1 {
                    offset: cur,
                    bytes_hex: hex::encode(comp.as_ref()),
                });
            };
            if bool::from(pt.is_identity()) {
                out.extend_from_slice(&[0u8; 128]);
                return Ok(());
            }
            let x_be = pt.x().to_bytes_be();
            let y_be = pt.y().to_bytes_be();
            out.extend_from_slice(&[0u8; 16]);
            out.extend_from_slice(&x_be[0..16]);
            out.extend_from_slice(&x_be[16..48]);
            out.extend_from_slice(&[0u8; 16]);
            out.extend_from_slice(&y_be[0..16]);
            out.extend_from_slice(&y_be[16..48]);
            Ok(())
        };
        let push_scalar_be = |cursor: &mut usize, out: &mut Vec<u8>| -> Result<(), RepackError> {
            let le = &compressed[*cursor..*cursor + layout::WORD_BYTES];
            // The generated verifier reverts on any eval or q_eval word that
            // is not a canonical Fr element, so reject it here rather than
            // handing the caller calldata that is guaranteed to revert
            // on-chain. Mirrors the G1 validation in `push_g1`.
            let mut arr = [0u8; layout::WORD_BYTES];
            arr.copy_from_slice(le);
            let repr = <Fq as PrimeField>::Repr::from(arr);
            if Option::<Fq>::from(Fq::from_repr(repr)).is_none() {
                let mut be = arr;
                be.reverse();
                return Err(RepackError::NonCanonicalScalar {
                    offset: *cursor,
                    bytes_hex: hex::encode(be),
                });
            }
            out.extend_from_slice(&scalar_le_to_be_word(le));
            *cursor += layout::WORD_BYTES;
            Ok(())
        };
        for &n in &plan.g1_groups {
            for _ in 0..n {
                push_g1(&mut cursor, &mut out)?;
            }
        }
        // evals (Fr 32-byte LE in native proof) -> BE calldata words
        // (incl. dummy slots).
        for _ in 0..plan.num_evals {
            push_scalar_be(&mut cursor, &mut out)?;
        }
        // f_com
        push_g1(&mut cursor, &mut out)?;
        // q_evals (Fr 32-byte LE in native proof) -> BE calldata words.
        for _ in 0..plan.num_point_sets {
            push_scalar_be(&mut cursor, &mut out)?;
        }
        // pi
        push_g1(&mut cursor, &mut out)?;
        debug_assert_eq!(cursor, compressed.len());
        Ok(out)
    }

    /// Repack a native proof and encode verifier calldata for `verifyProof`.
    pub(crate) fn encode_calldata(
        &self,
        plan: &RepackedProofLayoutPlan,
        compressed_proof: &[u8],
        instances: &[Fq],
    ) -> Result<Vec<u8>, GeneratorError> {
        if instances.len() != self.num_instances {
            return Err(GeneratorError::Planning {
                stage: "calldata",
                message: format!(
                    "instance length mismatch: expected {}, got {}",
                    self.num_instances,
                    instances.len()
                ),
            });
        }
        let proof = self.repack_proof(plan, compressed_proof)?;
        Ok(crate::evm::encode_calldata(&proof, instances))
    }
}

// SPDX-License-Identifier: CC0-1.0
//! Public calldata helpers for `SolidityGenerator`.

use super::*;

impl<'a> SolidityGenerator<'a> {
    /// Repack a midnight-proofs proof into the generated verifier ABI.
    pub fn repack_proof(&self, compressed: &[u8]) -> Result<Vec<u8>, RepackError> {
        self.inputs().repack_proof(compressed)
    }

    /// Repack a native proof and encode verifier calldata for `verifyProof`.
    pub fn encode_calldata(
        &self,
        compressed_proof: &[u8],
        instances: &[Fq],
    ) -> Result<Vec<u8>, GeneratorError> {
        self.inputs().encode_calldata(compressed_proof, instances)
    }

    #[cfg(all(test, feature = "evm"))]
    pub(crate) fn repacked_proof_scalar_layout_for_test(
        &self,
    ) -> crate::lowering::quotient_numerator::vm::RepackedProofScalarLayout {
        self.inputs().repacked_proof_scalar_layout_for_test()
    }
}

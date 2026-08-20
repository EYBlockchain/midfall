// SPDX-License-Identifier: CC0-1.0
//! Public calldata helpers for `SolidityGenerator`.

use super::*;

impl<'a> SolidityGenerator<'a> {
    /// Repack a midnight-proofs proof into the generated verifier ABI.
    pub fn repack_proof(&self, compressed: &[u8]) -> Result<Vec<u8>, RepackError> {
        let plan = self.plan().map_err(|err| RepackError::Planning {
            message: err.to_string(),
        })?;
        self.inputs().repack_proof(&plan.repacked_proof_layout_plan(), compressed)
    }

    /// Repack a native proof and encode verifier calldata for `verifyProof`.
    pub fn encode_calldata(
        &self,
        compressed_proof: &[u8],
        instances: &[Fq],
    ) -> Result<Vec<u8>, GeneratorError> {
        let plan = self.plan()?;
        self.inputs().encode_calldata(
            &plan.repacked_proof_layout_plan(),
            compressed_proof,
            instances,
        )
    }

    #[cfg(all(test, feature = "evm"))]
    pub(crate) fn repacked_proof_scalar_layout_for_test(
        &self,
    ) -> crate::lowering::quotient_numerator::vm::RepackedProofScalarLayout {
        self.plan().expect("lowering plan").repacked_proof_layout_plan().scalar_layout()
    }
}

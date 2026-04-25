// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import { Test } from "./forge-std-min.sol";
import { PlonkVerifier } from "../contracts/PlonkVerifier.sol";
import { IvcVerifyingKey } from
    "../contracts/circuits/ivc/IvcVerifyingKey.sol";

/// @notice End-to-end smoke test for the IVC single-circuit
/// aggregation example
/// (`aggregation/examples/single_circuit_aggregation.rs`).
///
/// Deploys the generic `PlonkVerifier` wired to the IVC VK blob and
/// calls `verify(publicInputs, proof)` on the fixture produced by
/// `cargo run --bin generate_ivc`.
///
/// The IVC chain aggregates 3 SHA-256 preimage proofs; the first two
/// outer transcript steps run under Poseidon (matching the in-circuit
/// verifier), and the FINAL step is emitted under `sha3::Keccak256`
/// via `IvcProver::prove_step_with::<Keccak256>` so that the resulting
/// proof can be consumed by this Keccak-transcript Solidity verifier.
///
/// The IVC circuit's structure is materially different from
/// poseidon / RSA:
///   * `k = 19` (524 288 rows; vs poseidon `k = 6`, RSA `k = 12`),
///   * 110-element flat public-input vector
///     `[ vk_repr, statements_hash, inner_acc_pi..., ivc_acc_pi... ]`,
///   * 2 lookups (poseidon + bls12_381 chips),
///   * 27 fixed columns, 18 permutation columns, 15 advice columns,
///   * 6 permutation chunks, 4 quotient limbs.
contract IvcVerifierTest is Test {
    PlonkVerifier v;
    address vkAddr;

    function setUp() public {
        vkAddr = address(new IvcVerifyingKey());
        v = new PlonkVerifier(vkAddr);
    }

    function test_verify_ivc_proof() public {
        bytes memory proof = vm.readFileBinary("fixtures/ivc/proof.bin");
        bytes memory instBlob = vm.readFileBinary("fixtures/ivc/instance.bin");

        // instBlob layout (produced by `bin/generate_ivc.rs`):
        //   [0..8]  u64 BE count of Fq limbs
        //   [8..]   count * 32 bytes BE (each limb)
        require(instBlob.length >= 8, "instance blob too short");
        uint256 n = _readU64(instBlob, 0);
        require(instBlob.length == 8 + 32 * n, "instance blob size mismatch");

        bytes32[] memory publicInputs = new bytes32[](n);
        for (uint256 i = 0; i < n; i++) {
            bytes32 word;
            assembly {
                word := mload(add(instBlob, add(40, mul(32, i))))
            }
            publicInputs[i] = word;
        }

        bool ok;
        try v.verify(publicInputs, proof) returns (bool r) {
            ok = r;
        } catch Error(string memory reason) {
            revert(reason);
        } catch (bytes memory) {
            revert("IVC verify reverted with low-level data");
        }
        assertTrue(ok, "IVC proof rejected");
    }

    function _readU64(bytes memory buf, uint256 off) private pure returns (uint256 out) {
        for (uint256 i = 0; i < 8; i++) {
            out = (out << 8) | uint256(uint8(buf[off + i]));
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import { Test } from "./forge-std-min.sol";
import { PlonkVerifier } from "../contracts/PlonkVerifier.sol";
import { RsaSignatureVerifyingKey } from
    "../contracts/circuits/rsa_signature/RsaSignatureVerifyingKey.sol";

/// @notice Phase 3 end-to-end smoke test for the RSA-signature
/// example from `zk_stdlib/examples/rsa_signature.rs`.
///
/// Deploys the generic `PlonkVerifier` wired to the RSA VK blob and
/// calls `verify(publicInputs, proof)` on the fixture produced by
/// `cargo run --bin generate_rsa`.  The goal is to exercise the
/// entire on-chain pipeline on a circuit that materially differs from
/// poseidon (22-element public-input column, 14 non-sequential fixed
/// queries, mod_exp-heavy gate bytecode) so that any remaining §7.2
/// assumption we haven't lifted shows up as either a revert or a
/// false rejection.
contract RsaSignatureVerifierTest is Test {
    PlonkVerifier v;
    address vkAddr;

    function setUp() public {
        vkAddr = address(new RsaSignatureVerifyingKey());
        v = new PlonkVerifier(vkAddr);
    }

    function test_verify_rsa_proof() public {
        bytes memory proof = vm.readFileBinary("fixtures/rsa_signature/proof.bin");
        bytes memory instBlob = vm.readFileBinary("fixtures/rsa_signature/instance.bin");

        // instBlob layout (produced by `bin/generate_rsa.rs`):
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

        // Phase 3 note: we only assert the call doesn't revert.  Phase
        // 4 will upgrade this to `require(ok, "rejected")` once we've
        // debugged whatever mismatches emerge.
        bool ok;
        try v.verify(publicInputs, proof) returns (bool r) {
            ok = r;
        } catch Error(string memory reason) {
            revert(reason);
        } catch (bytes memory) {
            revert("RSA verify reverted with low-level data");
        }
        assertTrue(ok, "RSA proof rejected");
    }

    function _readU64(bytes memory buf, uint256 off) private pure returns (uint256 out) {
        for (uint256 i = 0; i < 8; i++) {
            out = (out << 8) | uint256(uint8(buf[off + i]));
        }
    }
}

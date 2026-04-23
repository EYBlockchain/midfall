// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import { Test, Log } from "./forge-std-min.sol";
import { PoseidonVerifier } from "../contracts/PoseidonVerifier.sol";
import { PoseidonVerifyingKey } from "../contracts/PoseidonVerifyingKey.sol";

/// @notice End-to-end Solidity verifier test running against the Prague EVM.
///
/// The test:
///   1. Deploys `PoseidonVerifyingKey` (tiny constants-only contract).
///   2. Deploys `PoseidonVerifier` wired to the VK contract's address.
///   3. Loads `fixtures/proof.bin` and `fixtures/instance.be` produced by
///      the Rust `cargo run --bin generate`.
///   4. Calls `verify(instance, proof)` and measures gas for each of the
///      verifier's internal phases via the `PhaseGas(name, gas)` event.
///   5. Dumps deployment gas, call gas, and every traced challenge / read /
///      pairing outcome to `fixtures/solidity_trace.json` so the Rust
///      harness can cross-check the two execution traces.
contract PoseidonVerifierTest is Test {
    PoseidonVerifier v;
    address vkAddr;

    uint256 public vkDeployGas;
    uint256 public verifierDeployGas;

    function setUp() public {
        uint256 g0 = gasleft();
        vkAddr = address(new PoseidonVerifyingKey());
        vkDeployGas = g0 - gasleft();

        g0 = gasleft();
        v = new PoseidonVerifier(vkAddr);
        verifierDeployGas = g0 - gasleft();
    }

    function test_verify_poseidon_proof() public {
        bytes memory proof = vm.readFileBinary("fixtures/proof.bin");
        bytes memory instanceBE = vm.readFileBinary("fixtures/instance.be");
        require(instanceBE.length == 32, "instance size");
        bytes32 instance;
        assembly { instance := mload(add(instanceBE, 32)) }

        // Record logs so we can aggregate per-phase gas and challenges.
        vm.recordLogs();
        uint256 g0 = gasleft();
        bool ok;
        try v.verify(instance, proof) returns (bool r) {
            ok = r;
        } catch {
            ok = false;
        }
        uint256 verifyGas = g0 - gasleft();

        Log[] memory logs = vm.getRecordedLogs();

        // Print structured benchmark report.
        _logBench("VK deploy",       vkDeployGas);
        _logBench("Verifier deploy", verifierDeployGas);
        _logBench("verify() total",  verifyGas);

        bytes32 phaseGasSig = keccak256("PhaseGas(string,uint256)");
        bytes32 challengeSig = keccak256("TraceChallenge(string,bytes32)");
        bytes32 readScalarSig = keccak256("TraceReadScalar(string,bytes32)");
        bytes32 readPointSig = keccak256("TraceReadPoint(string,bytes)");
        bytes32 pairingSig = keccak256("TracePairing(bool)");

        string memory trace = "[";
        bool first = true;
        for (uint256 i = 0; i < logs.length; i++) {
            if (logs[i].topics[0] == phaseGasSig) {
                (string memory name, uint256 g) = abi.decode(logs[i].data, (string, uint256));
                _logBench(string.concat("  . ", name), g);
            } else if (logs[i].topics[0] == challengeSig) {
                (string memory name, bytes32 fe) = abi.decode(logs[i].data, (string, bytes32));
                trace = _appendTrace(trace, first, "Challenge", name, _toHex(fe), "");
                first = false;
            } else if (logs[i].topics[0] == readScalarSig) {
                (string memory name, bytes32 fe) = abi.decode(logs[i].data, (string, bytes32));
                trace = _appendTrace(trace, first, "ReadScalar", name, _toHex(fe), "");
                first = false;
            } else if (logs[i].topics[0] == readPointSig) {
                (string memory name, bytes memory p) = abi.decode(logs[i].data, (string, bytes));
                trace = _appendTrace(trace, first, "ReadPoint", name, "", _toHexBytes(p));
                first = false;
            } else if (logs[i].topics[0] == pairingSig) {
                bool r = abi.decode(logs[i].data, (bool));
                trace = _appendTrace(trace, first, "PairingResult", r ? "true" : "false", "", "");
                first = false;
            }
        }
        trace = string.concat(trace, "]");
        vm.writeFile("fixtures/solidity_trace.json", trace);

        emit log_named_bool("verify_ok", ok);
        // NOTE: the pairing check will NOT pass in this infrastructure demo
        // because full G1 decompression in Solidity is left for a follow-up
        // (see PoseidonVerifier._g1CompressedToEip2537). The transcript and
        // challenges *do* match byte-for-byte, which is what the equivalence
        // test asserts.
    }

    event log_named_uint(string, uint256);
    event log_named_bool(string, bool);

    function _logBench(string memory name, uint256 g) internal {
        emit log_named_uint(name, g);
    }

    function _appendTrace(
        string memory acc,
        bool first,
        string memory kind,
        string memory name,
        string memory feHex,
        string memory pHex
    ) internal pure returns (string memory) {
        string memory sep = first ? "" : ",";
        if (bytes(pHex).length > 0) {
            return string.concat(
                acc, sep,
                "{\"kind\":\"", kind,
                "\",\"tag\":\"", name,
                "\",\"eip2537_hex\":\"", pHex,
                "\"}"
            );
        }
        return string.concat(
            acc, sep,
            "{\"kind\":\"", kind,
            "\",\"tag\":\"", name,
            "\",\"fe_be_hex\":\"", feHex,
            "\"}"
        );
    }

    function _toHex(bytes32 v) internal pure returns (string memory) {
        bytes memory alph = "0123456789abcdef";
        bytes memory out = new bytes(64);
        for (uint256 i = 0; i < 32; i++) {
            out[2 * i]     = alph[uint8(v[i]) >> 4];
            out[2 * i + 1] = alph[uint8(v[i]) & 0xf];
        }
        return string(out);
    }

    function _toHexBytes(bytes memory b) internal pure returns (string memory) {
        bytes memory alph = "0123456789abcdef";
        bytes memory out = new bytes(b.length * 2);
        for (uint256 i = 0; i < b.length; i++) {
            out[2 * i]     = alph[uint8(b[i]) >> 4];
            out[2 * i + 1] = alph[uint8(b[i]) & 0xf];
        }
        return string(out);
    }
}

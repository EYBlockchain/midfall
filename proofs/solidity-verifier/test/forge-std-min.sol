// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// Ultra-minimal `forge-std` substitute. The full dependency is not
/// strictly required for this self-contained test suite, but we reproduce
/// the tiny subset we use (`Test`, `vm`, `assertEq`, `assertTrue`).

interface Vm {
    function readFileBinary(string calldata path) external view returns (bytes memory);
    function parseBytes32(string calldata) external pure returns (bytes32);
    function parseUint(string calldata) external pure returns (uint256);
    function startPrank(address) external;
    function stopPrank() external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
    function warp(uint256) external;
    function writeFile(string calldata path, string calldata data) external;
}

struct Log {
    bytes32[] topics;
    bytes data;
    address emitter;
}

address constant VM_ADDRESS = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;

abstract contract Test {
    Vm constant vm = Vm(VM_ADDRESS);

    function assertEq(uint256 a, uint256 b) internal pure {
        require(a == b, "assertEq uint fail");
    }

    function assertEq(bytes32 a, bytes32 b) internal pure {
        require(a == b, "assertEq b32 fail");
    }

    function assertEq(bytes memory a, bytes memory b) internal pure {
        require(keccak256(a) == keccak256(b), "assertEq bytes fail");
    }

    function assertTrue(bool v, string memory reason) internal pure {
        require(v, reason);
    }

    function assertTrue(bool v) internal pure {
        require(v, "assertTrue fail");
    }
}

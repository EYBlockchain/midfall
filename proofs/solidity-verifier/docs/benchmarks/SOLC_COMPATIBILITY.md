# Solidity Compiler Compatibility Smoke Results

These runs are ad-hoc compatibility checks. The reproducible gate remains the
repo-pinned compiler:

```text
solc 0.8.30+commit.73712a01
```

Alternate compiler runs use `HALO2_SOLIDITY_ALLOW_UNPINNED_SOLC=1`, so bytecode
and gas are not treated as reproducible benchmark artifacts.

## 2026-05-22

Host: macOS, `Darwin.appleclang` solc binaries from
`binaries.soliditylang.org`.

### solc 0.8.29+commit.ab55807c

```text
PASS rsa_signature_fixture
  proof: 2288 bytes compressed, 3648 bytes repacked
  instances: 22 field elements
  on-chain verify: 593451 gas

PASS sha_preimage_fixture
  proof: 3408 bytes compressed, 5248 bytes repacked
  instances: 32 field elements
  on-chain verify: 829381 gas

PASS Poseidon property/negative suite
  command filter: pbt_
  cases: POSEIDON_PBT_CASES=10
  result: 7 passed, 0 failed

PASS IVC final Keccak Solidity E2E
  proof: 5056 bytes compressed, 7776 bytes repacked
  calldata: 8356 bytes
  on-chain verify: 1281427 gas
  verifier/VK/quotient runtime: 11916 / 17025 / 9531 bytes
```

### solc 0.8.35+commit.47b9dedd

```text
PASS rsa_signature_fixture
  proof: 2288 bytes compressed, 3648 bytes repacked
  instances: 22 field elements
  on-chain verify: 593547 gas

PASS sha_preimage_fixture
  proof: 3408 bytes compressed, 5248 bytes repacked
  instances: 32 field elements
  on-chain verify: 829393 gas

PASS Poseidon property/negative suite
  command filter: pbt_
  cases: POSEIDON_PBT_CASES=10
  result: 7 passed, 0 failed

PASS IVC final Keccak Solidity E2E
  proof: 5056 bytes compressed, 7776 bytes repacked
  calldata: 8356 bytes
  on-chain verify: 1281487 gas
  verifier/VK/quotient runtime: 11916 / 17025 / 9531 bytes
```

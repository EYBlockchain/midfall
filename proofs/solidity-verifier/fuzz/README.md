# Solidity Verifier Fuzzing

This directory contains `cargo-fuzz` targets for coverage-guided fuzzing.

Install a nightly Rust toolchain and the runner once:

```sh
rustup toolchain install nightly
cargo install cargo-fuzz
```

Run the current repacker target from `proofs/solidity-verifier`:

```sh
cargo +nightly fuzz run proof_repack
```

For a short local smoke run:

```sh
cargo +nightly fuzz run proof_repack -- -max_total_time=60
```

`proof_repack` fuzzes compressed proof bytes through `SolidityGenerator::repack_proof`.
Inputs that successfully repack are also ABI-encoded with one public instance to
check the Solidity calldata shape.

To fuzz the generated Solidity verifier through `revm`, run:

```sh
cargo +nightly fuzz run solidity_calldata -- -max_total_time=60
```

`solidity_calldata` builds a tiny valid proof, compiles the generated embedded
Solidity verifier once during target initialization, deploys it once per fuzzing
thread, then mutates one calldata field at a time: selector, dynamic ABI heads,
proof length, proof G1s, proof eval scalars, q evals, instance length,
instances, trailing bytes, truncation, and proof-offset drift. Any mutated input
that makes `verifyProof(bytes,uint256[])` return `true` is a fuzzer failure.

This target needs the configured `solc` to match the pinned verifier compiler
(`0.8.30+commit.73712a01`). For local experiments with another compiler, set
`HALO2_SOLIDITY_ALLOW_UNPINNED_SOLC=1`.

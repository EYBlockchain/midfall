# Halo2 Solidity Verifier

> ⚠️ This repo has NOT been audited and is NOT intended for a production environment yet.

Solidity verifier generator for `midnight-proofs` / Midfall verifier proofs with
the KZG polynomial commitment scheme on BLS12-381. Generated verifiers use
Solidity `^0.8.24` source pragmas, and reproducible test/bench bytecode is
compiled with pinned `solc 0.8.30+commit.73712a01`.

For audited solidity verifier generator and proof aggregation toolkits, please refer to [`snark-verifier`](http://github.com/axiom-crypto/snark-verifier).

## Usage

### Generate verifier and verifying key separately as 2 Solidity contracts

```rust
let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(num_instances, 1));
let artifacts = generator
    .render(RenderOptions {
        vk: RenderVk::Separate,
        ..RenderOptions::default()
    })
    .unwrap();
let verifier_solidity = artifacts.verifier;
let vk_solidity = artifacts.verifying_key.unwrap();
```

### Generate verifier and verifying key in a single solidity contract

```rust
let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(num_instances, 1));
let verifier_solidity = generator.render(RenderOptions::default()).unwrap().verifier;
```

### Encode proof into calldata to invoke `verifyProof`

```rust
let calldata = generator.encode_calldata(&native_proof, &instances)?;
```

Note that function selector is already included.

## Test

### Current status

As of this revision,
`cargo test -p halo2_solidity_verifier --all-features --all-targets -- --list`
reports 167 library tests and 4 integration tests.

The implemented suite is narrower than the full assurance roadmap in
[`TESTING_STRATEGY.md`](./TESTING_STRATEGY.md). Today it covers transcript
compatibility, protocol planning, memory layout, VK payload encoding, proof
layout/canonicality checks, Solidity render invariants, Prague EIP-2537 smoke
coverage, Poseidon verifier property/adversarial tests, a Poseidon end-to-end
fixture, the Keccak IVC Poseidon-chain Solidity bench, and two ignored diagnostic
decompression probes.

| Area | Current status | Default behavior |
| ---- | -------------- | ---------------- |
| Library/codegen tests under `src/` | Implemented and part of the normal Cargo suite. | Run by `cargo test -p halo2_solidity_verifier`. |
| Solidity/EVM tests in `src/test.rs` | Implemented behind the `evm` feature. Heavy Poseidon cases self-skip unless `HALO2_SOLIDITY_RUN_EVM_TESTS=1`, `solc`, and SRS assets are available. | Listed by Cargo; skipped cleanly without the gate. |
| `tests/poseidon_fixture.rs` | Implemented end-to-end Poseidon proof -> Solidity render -> `solc` -> Prague `revm` verification. | Self-skips unless `HALO2_SOLIDITY_RUN_EVM_TESTS=1`. |
| `tests/ivc_keccak_solidity.rs` | Implemented slow Keccak IVC final-proof Solidity bench over Poseidon hash-chain leaves. | Self-skips unless `HALO2_SOLIDITY_RUN_IVC_BENCH=1`. |
| `tests/fcom_decompress.rs` | Implemented diagnostic probes only. | Marked `#[ignore]`. |

### Requirements

The workspace is pinned to the toolchain in
[`rust-toolchain.toml`](./rust-toolchain.toml). The verifier now builds against
the surrounding Midfall workspace crates through local path dependencies.
Solidity-touching tests require `solc 0.8.30+commit.73712a01` on `PATH` or via
the `SOLC` environment variable.

The heavy proof/EVM tests also need Filecoin/Midnight SRS assets. Set
`SRS_DIR` when they are not available at the default in-tree Midfall asset path:

```bash
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets
```

Unless noted otherwise, run the commands below from the current Midfall
repository root. Package-scoped commands use `-p halo2_solidity_verifier` so
they exercise this verifier crate without accidentally selecting unrelated
workspace members.

### Common commands

List the currently implemented tests without running them:

```bash
cargo test -p halo2_solidity_verifier --all-features --all-targets -- --list
```

Run the normal verifier suite. Without opt-in environment gates, heavy EVM and
IVC tests are still compiled/listed but skip at runtime:

```bash
cargo test -p halo2_solidity_verifier --all-features --all-targets -- --nocapture
```

> [!NOTE]
> CI and reproducible benches compile Solidity with
> `solc 0.8.30+commit.73712a01`.

The pinned Midfall revision, solc version, canonical IVC bench command, and
published verifier/VK/quotient runtime hashes are recorded in
[`docs/reference/REPRODUCIBLE_BUILDS.md`](./docs/reference/REPRODUCIBLE_BUILDS.md).
The bounded correctness and security claim, artifact manifest, threat model,
and release gates are in
[`docs/audit/CODEGEN_ASSURANCE_DOSSIER.md`](./docs/audit/CODEGEN_ASSURANCE_DOSSIER.md).
The compact reviewer handoff packet is in
[`docs/audit/REVIEW_PACKET.md`](./docs/audit/REVIEW_PACKET.md).
For a high-level architecture and lowering pipeline specification, see
[`docs/architecture/LOWERING_ARCHITECTURE_SPEC.md`](./docs/architecture/LOWERING_ARCHITECTURE_SPEC.md).
The map between the Askama templates, generated Solidity/Yul, Midfall Rust
verifier, and optimization choices is documented in
[`docs/reference/ASKAMA_TEMPLATE_RUST_MAPPING.md`](./docs/reference/ASKAMA_TEMPLATE_RUST_MAPPING.md).

Run one test by name:

```bash
cargo test -p halo2_solidity_verifier --all-features \
  lowering::layout::memory::tests::overlapping_permanent_regions_fail -- --nocapture
```

The maintained example is `examples/ivc_replay.rs`; obsolete legacy diagnostic
examples have been removed so default example discovery stays green.

Run the `src/test.rs` Solidity/EVM verifier tests with the opt-in gate:

```bash
HALO2_SOLIDITY_RUN_EVM_TESTS=1 \
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
cargo test -p halo2_solidity_verifier --release \
  --features evm,rust-verifier-trace --lib test:: -- --nocapture
```

Run a single Solidity/EVM test:

```bash
HALO2_SOLIDITY_RUN_EVM_TESTS=1 \
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
cargo test -p halo2_solidity_verifier --release \
  --features evm,rust-verifier-trace \
  pbt_solidity_rejects_malleated_proofs -- --nocapture
```

Run the Poseidon integration fixture:

```bash
HALO2_SOLIDITY_RUN_EVM_TESTS=1 \
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
cargo test -p halo2_solidity_verifier --release \
  --features evm,truncated-challenges --test poseidon_fixture -- --nocapture
```

Run the ignored diagnostic decompression probes:

```bash
cargo test -p halo2_solidity_verifier --features evm \
  --test fcom_decompress -- --ignored --nocapture
```

### IVC detailed bench

Run the Keccak IVC Solidity verifier bench over Poseidon hash-chain leaves with per-section gas checkpoints:

```bash
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
proofs/solidity-verifier/scripts/run_ivc_bench.sh
```

This prints the detailed checkpoint table, deployed runtime sizes, total
transaction gas, and real checkpointed section work. The default path uses the
multi-limb quotient commitment layout for the Solidity-facing decider proof, so
`SRS_DIR` must contain `midnight-srs-2p19` and `midnight-srs-2p20`.

To benchmark the outer single-H quotient commitment layout, opt in explicitly:

```bash
proofs/solidity-verifier/scripts/run_ivc_bench.sh --outer-single-h-commitment
```

That profile also needs `midnight-srs-2p22`. If `--skip-srs-download` is passed
and `2p22` is missing, the script fails before compiling; run without
`--skip-srs-download` once, or fetch it with:

```bash
mkdir -p zk_stdlib/examples/assets
curl -fL --retry 3 --retry-delay 2 \
  -o zk_stdlib/examples/assets/midnight-srs-2p22 \
  https://srs.midnight.network/midnight-srs-2p22
```

Single-H is outer-only in this repo: the recursive leaf proofs verified inside
the decider circuit stay on Midfall's multi-limb quotient layout. The opt-in
single-H bench therefore performs a two-phase run: first it generates a
multi-limb leaf bundle without `outer-single-h-commitment`, then it proves and
verifies the final decider proof with `outer-single-h-commitment`.

The gas effect is intentionally modest. For the current IVC decider shape,
single-H removes three quotient commitment terms from the fused PCS final MSM:
`78 -> 75` terms. The exact gas delta depends on whether trace logs and
checkpoint logs are enabled; compare a local default run against
`--outer-single-h-commitment` for the current profile. The larger structural
effect is proof layout size: three fewer G1 commitments means `144` fewer
compressed proof bytes and `384` fewer EIP-2537-padded proof bytes.

The runner keeps the recursive verifier on fewer point sets, but the outer
Solidity-facing decider proof does not enable `outer-fewer-point-sets`.

Native Rust/Solidity trace equivalence is enabled by the trace-only bench path:
`proofs/solidity-verifier/scripts/run_ivc_bench.sh --trace --no-gas-checkpoints`.
Custom Midfall overrides must expose the
`midnight-proofs/solidity-verifier-trace` feature for that leg.
The IVC bench renders a pinned `Halo2QuotientEvaluator` alongside
`Halo2Verifier`, so the trace comparison includes quotient identity trace ids
`30_000..40_000` along with proof scalar reads, `q_evals`, and the reconstructed
quotient numerator.

Generated IVC contracts and calldata are written inside the current Midfall
repository. Each IVC bench run overwrites this directory with the artifacts for
the most recent variant:

```text
proofs/solidity-verifier/target/ivc-keccak-solidity-dump/
  Halo2Verifier.sol
  Halo2VerifyingKey.sol
  Halo2QuotientEvaluator.sol
  calldata.bin
  proof.bin
  instance.le
  contract-sizes.txt
```

Compile-check the IVC bench without running the full proof:

```bash
proofs/solidity-verifier/scripts/run_ivc_bench.sh --check-only
```

For local, non-reproducible bench runs with whatever `solc` and Rust toolchain
are already available, opt out of the pins explicitly:

```bash
proofs/solidity-verifier/scripts/run_ivc_bench.sh \
  --allow-unpinned-solc \
  --rust-toolchain stable
```

This keeps the SRS/download and bench flow the same, but generated bytecode and
gas numbers should be treated as ad hoc measurements rather than release
numbers.

### Moonlight IVC wrap proof

With a compatible `../Moonlight` checkout, run the Moonlight wrap-recursion
Solidity verifier example from the Midfall root. The dump directory is set
explicitly so the generated contracts stay in this Midfall repository:

```bash
MOONLIGHT_RUN_WRAP_SOLIDITY_BENCH=1 \
MOONLIGHT_RUN_WRAP_SOLIDITY_TRACE=1 \
MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR="$PWD/proofs/solidity-verifier/target/moonlight-wrap-solidity-dump" \
SRS_DIR="$PWD/zk_stdlib/examples/assets" \
cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml \
  wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs \
  --release -- --ignored --nocapture
```

To run the same Moonlight bench with unpinned local tooling:

```bash
HALO2_SOLIDITY_ALLOW_UNPINNED_SOLC=1 \
RUSTUP_TOOLCHAIN=stable \
MOONLIGHT_RUN_WRAP_SOLIDITY_BENCH=1 \
MOONLIGHT_RUN_WRAP_SOLIDITY_TRACE=1 \
MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR="$PWD/proofs/solidity-verifier/target/moonlight-wrap-solidity-dump" \
SRS_DIR="$PWD/zk_stdlib/examples/assets" \
cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml \
  wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs \
  --release --lib -- --ignored --nocapture
```

Compile-check the same Moonlight target without producing the proof:

```bash
MOONLIGHT_RUN_WRAP_SOLIDITY_BENCH=1 \
MOONLIGHT_RUN_WRAP_SOLIDITY_TRACE=1 \
MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR="$PWD/proofs/solidity-verifier/target/moonlight-wrap-solidity-dump" \
SRS_DIR="$PWD/zk_stdlib/examples/assets" \
cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml \
  wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs \
  --release --no-run
```

Generated Moonlight wrap contracts and calldata are written inside the current
Midfall repository. Each Moonlight wrap run overwrites this directory:

```text
proofs/solidity-verifier/target/moonlight-wrap-solidity-dump/
  Halo2Verifier.sol
  Halo2VerifyingKey.sol
  calldata.bin
  proof.bin
  instance.le
```

Moonlight wrap can look slightly cheaper than the local IVC Keccak bench even
when both runs have the same verifier proof scale. In one representative run,
both had `102` proof eval scalars, `0` dummy PCS evals, `4` PCS point sets, and
a `5056` byte compressed proof, but Moonlight used `1,295,166` gas versus
`1,301,504` gas for the IVC bench. The main difference is topology: Moonlight
renders the quotient numerator inside the verifier, while the IVC bench uses a
pinned external `Halo2QuotientEvaluator`. That split keeps the main verifier
smaller, but checkpoint 12 pays the external-call/copy/return framing; in that
run, numerator reconstruction was `302,064` gas for Moonlight and `313,374` gas
for IVC. Moonlight gives some of that back through a larger public-input shape
(`19` wrap instance fields versus `14` IVC fields), which shows up in
`Lagrange + instance evaluation`.

There is intentionally no single "all features plus all gated benches" command:
`outer-single-h-commitment` changes the final-proof SRS requirements and can be
covered with
`proofs/solidity-verifier/scripts/run_ivc_bench.sh --outer-single-h-commitment`.
To run the full package suite, the gated EVM tests, ignored diagnostics, and the
IVC bench, use the targeted commands above. The closest single Cargo sweep is:

```bash
cargo test -p halo2_solidity_verifier --release --all-features --all-targets \
  -- --include-ignored --nocapture
```

That sweep compiles the all-features layout and runs ignored diagnostics, while
the heavy EVM and IVC proof paths remain covered by their explicit opt-in
commands.

### Implemented test inventory

The authoritative inventory is generated by:

```bash
cargo test -p halo2_solidity_verifier --all-features --all-targets -- --list
```

The current output contains:

- 177 library tests covering codegen planning, memory layout, PCS/query
  planning, proof layout, quotient VM lowering, Solidity template invariants,
  transcript compatibility, and gated Solidity/EVM verifier behavior.
- `tests/fcom_decompress.rs`: `fcom_decompress` and
  `quotient_limb_decompress` (`#[ignore]` diagnostics).
- `tests/ivc_keccak_solidity.rs`: `ivc_final_keccak_solidity_e2e`.
- `tests/poseidon_fixture.rs`: `poseidon_renders_compiles_and_verifies`.

## Limitations & Caveats

- It currently supports the Midfall verifier shape used by this repo: exactly
  one committed identity instance column and one non-committed public-input
  column, no rotated instance queries, and KZG on BLS12-381.
- Verifying-key generation must be reproducible for the circuit shape being
  rendered. If selector assignments can differ between proving and verifier
  generation, disable selector compression or use the Midfall keygen path that
  preserves the same selector layout.

## Compatibility

The generated transcript parser in
[`TranscriptProofParser.yul`](./templates/partials/verifier/TranscriptProofParser.yul)
follows the Midfall Keccak transcript shape used by the generated Solidity
verifier.

## Design Rationale

The current solidity verifier generator within `snark-verifier` faces a couple of issues:

- The generator receives only unoptimized, low-level operations, such as add or mul. As a result, it currently unrolls all assembly codes, making it susceptible to exceeding the contract size limit, even with a moderately sized circuit.
- The existing solution involves complex abstractions and APIs for consumers.

This repository is a ground-up rebuild, addressing these concerns while maintaining a focus on code size and readability. Remarkably, the gas cost is comparable, if not slightly lower, than the one generated by `snark-verifier`.

See [`docs/reference/PR17_BORROWED_IDEAS.md`](./docs/reference/PR17_BORROWED_IDEAS.md) for the
small artifact-layout and packed-program ideas borrowed from
`privacy-ethereum/halo2-solidity-verifier` PR #17, and why this repo keeps a
static pinned verifier instead of adopting a fully reusable runtime artifact.

See [`docs/architecture/MEMORY_LAYOUT.md`](./docs/architecture/MEMORY_LAYOUT.md) for the generated
verifier memory planner, including the fixed theta-relative offsets,
precompile-frame constants, scratch lifetimes, and update rules.

See [`docs/reference/HALO2_MIDNIGHT_VERIFIER_SPEC.md`](./docs/reference/HALO2_MIDNIGHT_VERIFIER_SPEC.md)
for a consolidated specification and architecture guide covering the ABI,
proof layout, transcript, quotient reconstruction, KZG PCS check, VK payload,
and split verifier contracts.

## Acknowledgement

The template is heavily inspired by Aztec's [`BaseUltraVerifier.sol`](https://github.com/AztecProtocol/barretenberg/blob/4c456a2b196282160fd69bead6a1cea85289af37/sol/src/ultra/BaseUltraVerifier.sol).

# Solidity Verifier Review Packet

This packet is meant to make review tractable for cryptography researchers and
Solidity/security engineers. It turns the task from "read the whole codebase"
into "validate these bounded claims with these artifacts and checkpoints."

## 1. Review Goal

Primary claim to review:

```text
For the supported Midfall profile and pinned generated artifacts, if the
generated Solidity verifier accepts, then the pinned Rust verifier would accept
the same mathematical proof for the same verifying key and public inputs.
```

This review is not a generic Halo2 verifier audit. The generator is specialized
to the Midfall/Midnight proof profile documented in
`CODEGEN_ASSURANCE_DOSSIER.md`.

## 2. Scope

In scope:

- Rust lowering and artifact generation under `proofs/solidity-verifier/src`.
- Generated Solidity/Yul templates under `proofs/solidity-verifier/templates`.
- Solidity calldata repacking and proof/public-input encoding.
- VK, quotient evaluator, and verifier bytecode binding.
- BLS12-381 EIP-2537 precompile usage and failure handling.
- Existing fixtures, trace comparison machinery, and EVM tests.

Out of scope unless explicitly added:

- Generic Halo2 circuit support.
- Application wrapper security, replay protection, nullifier policy, or state
  transition semantics.
- Chains or L2s without Prague-compatible EIP-2537 semantics.
- Arbitrary committed-instance commitments beyond the supported identity
  committed instance profile.

## 3. Supported Protocol Envelope

The intended production profile is:

- BLS12-381 KZG over `midnight_curves::Bls12`.
- Scalar field `midnight_curves::Fq`.
- Midfall Keccak transcript.
- One proof.
- Exactly one identity-committed instance column.
- Exactly one direct public instance column.
- No rotated non-committed instance queries.
- Matching Rust/Solidity features for truncated challenges, fewer point sets,
  and outer single-H quotient commitments.
- Optional split VK and quotient evaluator contracts pinned by runtime length
  and codehash.

Any artifact outside this envelope should be treated as unsupported unless the
scope is updated.

## 4. Artifact Manifest

Fill this table for the exact artifact under review. Use
`docs/reference/REPRODUCIBLE_BUILDS.md` for the recorded IVC benchmark hashes.

| Item | Value |
| --- | --- |
| Repository commit | `a096e71746e401404f250817ca4e857bac1eef56` (**this repository** at packet creation; the Midfall dependency revision is a separate stamp — see the provenance-identities table in `docs/reference/REPRODUCIBLE_BUILDS.md`) |
| Working tree status at packet creation | clean before this packet was added |
| Rust toolchain | `rust-toolchain.toml` |
| Solidity compiler | `solc 0.8.30+commit.73712a01`, SHA-256-pinned by `scripts/install_pinned_solc.sh` |
| Solidity flags | `--bin --optimize --optimize-runs <N> --via-ir --evm-version cancun --no-cbor-metadata` — record `<N>` per artifact; it changes both bytecode and deployability (0.8.30 at `runs=100000` exceeds EIP-170) |
| Cargo features | fill per artifact |
| Generated verifier source hash | fill per artifact |
| Generated VK source hash | fill per artifact, if split |
| Generated quotient evaluator source hash | fill per artifact, if split |
| Verifier runtime length/hash | fill per artifact |
| VK runtime length/hash | fill per artifact, if split |
| Quotient evaluator runtime length/hash | fill per artifact, if split |
| Proof fixture hash | fill per artifact |
| Public input fixture hash | fill per artifact |
| Calldata hash | fill per artifact |

Generate the per-artifact rows with `scripts/generate_artifact_manifest.sh
<artifact-dump-dir>`; it emits this table for each rendered fixture dump under
`target/`. The currently recorded IVC benchmark manifests live in
`docs/reference/REPRODUCIBLE_BUILDS.md`.

## 5. Reading Order

Start here:

1. `docs/audit/CODEGEN_ASSURANCE_DOSSIER.md`
2. `docs/reference/STATUS.md`
3. `docs/architecture/LOWERING_ARCHITECTURE_SPEC.md`
4. The generated Solidity artifact(s) under review.
5. The source files for the specific checkpoint being reviewed.

Avoid starting with the large Yul templates. First understand the semantic
claim, supported profile, and checkpoint map.

## 6. Crypto Researcher Checklist

The crypto review should answer these questions:

- Does the Solidity transcript absorb the same mathematical objects as the Rust
  verifier, in the same order, before each dependent challenge?
- Are the VK digest, instance length, committed identity instance, public
  inputs, commitments, evaluations, `f_com`, `q_evals`, and `pi` absorbed at
  the correct points?
- Is the quotient numerator algebra equivalent to the Rust Halo2 identities for
  gates, permutation, lookup/logup, and trash constraints?
- Are selector folds and lookup/permutation chunk boundaries batched with the
  intended powers?
- Is the linearization commitment relation equivalent to
  `plonk/linearization/verifier.rs`?
- Is the KZG `multi_prepare` batching equivalent, including dummy queries,
  point-set order, `x1`, `x2`, `x3`, `x4`, `f_com`, `q_evals`, and `pi`?
- Do truncated-challenge and fewer-point-set feature choices match the native
  proof being checked?
- Is the final pairing equation algebraically equivalent to the Rust
  `DualMSM::check` equation?
- If accumulator support is enabled, is the carried accumulator batching sound
  and bound to the same public inputs?

The target answer is not "the code looks reasonable." The target answer is:

```text
For this artifact and feature profile, Solidity acceptance implies Rust verifier
acceptance for the same mathematical statement.
```

## 7. Solidity And Systems Checklist

The implementation review should answer these questions:

- Does the ABI parser reject wrong selectors, malformed dynamic heads, truncated
  proof bytes, trailing bytes, and wrong instance lengths?
- Are all `Fr` words checked canonical before use?
- Are all BLS12-381 G1 inputs range-checked and validated through EIP-2537
  before they can influence acceptance?
- Are padded EIP-2537 G1 encodings handled consistently as 128-byte values?
- Can any Yul memory region overlap live verifier state?
- Do scratch regions have generated capacity checks for the circuit dimensions?
- Do precompile wrappers check call success, exact return size, and semantic
  result words?
- Can trace or gas-checkpoint logic perturb production acceptance?
- Are VK and quotient evaluator bytecode length/codehash pinned before use?
- Does any unsupported circuit shape fail before rendering?

## 8. Semantic Checkpoint Map

Use this table as the shared bridge between researchers and implementers.

| Checkpoint | Rust source of truth | Solidity/codegen owner | Evidence to request |
| --- | --- | --- | --- |
| Proof parser and transcript schedule | `proofs/src/plonk/verifier.rs` | `src/lowering/protocol`, `src/lowering/abi`, `TranscriptProofParser.yul` | Proof offset table and transcript trace |
| VK digest | `proofs/src/plonk/mod.rs` | `src/lowering/vk.rs`, `VkLoading.yul` | VK digest equality and runtime pinning |
| Quotient identities | `proofs/src/plonk/mod.rs` | `src/lowering/quotient.rs`, `src/lowering/quotient_numerator`, `QuotientNumeratorBlock.yul` | Per-identity numerator trace |
| Linearization | `proofs/src/plonk/linearization/verifier.rs` | `QuotientAndLinearization.yul`, `src/lowering/kzg` | Linearization scalar and commitment terms |
| KZG multi-open | `proofs/src/poly/kzg/mod.rs` | `src/lowering/kzg/mod.rs`, `Pcs.yul` | Query schedule and final MSM terms |
| Pairing check | `proofs/src/poly/kzg/msm.rs` | `FinalPairing.yul` | Pairing inputs and precompile result |
| Accumulator, if enabled | wrapper logic outside Rust PLONK verifier | `AccumulatorHelpers.yul`, `src/lowering/encoding` | Public-input decoding and batched pairing terms |

## 9. Trace Evidence Template

For each reviewed artifact, provide a trace table with Rust and Solidity values.

| Step | Rust value | Solidity value | Source/checkpoint |
| --- | --- | --- | --- |
| VK digest | fill | fill | transcript start |
| public input length | fill | fill | transcript instances |
| beta | fill | fill | after first commitment phase |
| gamma | fill | fill | after beta |
| y | fill | fill | quotient challenge |
| x | fill | fill | evaluation challenge |
| quotient numerator | fill | fill | quotient evaluator |
| linearization scalar(s) | fill | fill | linearization |
| `f_com` | fill | fill | KZG multi-open |
| `q_evals` | fill | fill | KZG multi-open |
| final MSM lhs | fill | fill | pairing input |
| final MSM rhs | fill | fill | pairing input |
| pairing result | fill | fill | final return |

This table is the fastest way for cryptographers to review the implementation
without mentally executing every Yul block.

## 10. Negative Test Matrix

The review packet should include logs or fixtures showing rejection for:

- Every proof scalar mutated to `Fr`, `Fr + 1`, high-bit, and random
  non-canonical values.
- Every proof G1 mutated with nonzero top padding, coordinate `p`, off-curve
  coordinates, and malformed infinity encodings.
- Public input mutations at every slot.
- Wrong proof length, truncated proof, trailing proof bytes, wrong ABI selector,
  shifted ABI heads, and wrong array length.
- VK runtime mutation or wrong VK codehash.
- Quotient evaluator runtime mutation or wrong evaluator codehash.
- Precompile failure, short returndata, and false pairing result.
- Accumulator limb, scalar, coordinate, and point-pair mutations when the
  accumulator path is enabled.

## 11. Reproduction Commands

List tests without running:

```bash
cargo test -p halo2_solidity_verifier --all-features --all-targets -- --list
```

Run the normal verifier suite:

```bash
cargo test -p halo2_solidity_verifier --all-features --all-targets -- --nocapture
```

Run Solidity/EVM tests:

```bash
HALO2_SOLIDITY_RUN_EVM_TESTS=1 \
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
cargo test -p halo2_solidity_verifier --release \
  --features evm,rust-verifier-trace --lib test:: -- --nocapture
```

Run the Poseidon integration fixture:

```bash
HALO2_SOLIDITY_RUN_EVM_TESTS=1 \
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
cargo test -p halo2_solidity_verifier --release \
  --features evm,truncated-challenges --test poseidon_fixture -- --nocapture
```

Run the IVC Solidity benchmark and trace path:

```bash
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
proofs/solidity-verifier/scripts/run_ivc_bench.sh --trace --no-gas-checkpoints
```

## 12. Expected Review Outputs

Ask reviewers to produce:

- A short statement of the exact artifact and feature profile reviewed.
- A list of accepted assumptions and exclusions.
- Answers to the crypto checklist and systems checklist.
- Any finding with severity, affected checkpoint, reproduction steps, and
  whether it can cause false acceptance.
- A final statement of whether the primary claim is supported, unsupported, or
  supported only after fixes.


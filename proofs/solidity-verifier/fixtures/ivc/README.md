# IVC Public-Accumulator Replay Fixture

Pre-rendered artifacts for `tests/ivc_accumulator_replay.rs`, which replays a
real IVC final proof and then mutates the accumulator public inputs to check the
decoder in `templates/partials/verifier/AccumulatorHelpers.yul` rejects them.

These are *rendered* contracts plus matching calldata rather than a verifying
key and proof, so the replay needs only solc and revm -- no SRS, no proving run,
and no `midnight-aggregation`. A verifier cannot be rendered from a VK without
the full SRS, because `SolidityGenerator` consumes `params.g_lagrange()`; that
is what makes a vk.bin-based replay unusable in CI.

## Provenance

| Field | Value |
| --- | --- |
| Source commit | `f787a77c` |
| Rendered by | `tests/ivc_keccak_solidity.rs` (`ivc_final_keccak_solidity_e2e`) |
| Circuit | IVC k=19 leaves, k=20 decider |
| Accumulator | `AccumulatorEncoding::new(offset=4, num_limbs=7, num_limb_bits=56)` |
| Verified on-chain | yes, 1,346,886 gas under revm Prague (2026-08-20 render: MF-1..MF-4 fixes, EIP-7883 modexp bound + constructor probe, fallible cached lowering plan, pinned-external quotient render type, `__phase:` section markers) |

## Regenerating

Requires `midnight-srs-2p19` and `midnight-srs-2p20` in `SRS_DIR`
(~300 MB, from <https://srs.midnight.network>):

```bash
HALO2_SOLIDITY_RUN_IVC_BENCH=1 \
  SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
  cargo test --release \
    --features evm,truncated-challenges,in-circuit-fewer-point-sets \
    --test ivc_keccak_solidity -- --nocapture

cp target/ivc-keccak-solidity-dump/{Halo2Verifier.sol,Halo2VerifyingKey.sol,\
Halo2QuotientEvaluator.sol,calldata.bin} fixtures/ivc/
```

Then update the source commit above.

## Staleness

This is a snapshot of the codegen that produced it. The artifacts are
self-consistent, so the replay keeps passing after a codegen change -- it just
stops exercising current output. Detecting that automatically would mean
re-rendering, which needs the SRS again, so it is tracked by the commit stamp
above rather than by an assertion. Regenerate after changes to the accumulator
templates or the memory layout.

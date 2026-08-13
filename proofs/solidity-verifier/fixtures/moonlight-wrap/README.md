# Moonlight Wrap point_pair Replay Fixture

Pre-rendered artifacts for the `point_pair` accumulator arm of
`tests/ivc_accumulator_replay.rs`. The IVC fixture next door covers
`AccumulatorEncoding::new` (explicit lhs/rhs scalars); this one covers
`AccumulatorEncoding::point_pair`, whose
`expected_acc_has_carried_scalars = false` template arms were otherwise only
ever compiled, never executed against a real proof.

This is a single-contract render, so there is no `Halo2QuotientEvaluator.sol`;
the replay deploys the verifier with the verifying key alone.

## Provenance

| Field | Value |
| --- | --- |
| Source commit | `f894f75` (**this repository**, solidity-verifier, at fixture-render time; not the Midfall dependency revision — see the provenance-identities table in `docs/reference/REPRODUCIBLE_BUILDS.md`) |
| Rendered by | Moonlight `wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs` |
| Moonlight revision | `origin/codex/wrap-bench-cherry-picks` (`1940ea9`), rendered from a scratch worktree with the local-path Cargo unification below |
| Accumulator | `AccumulatorEncoding::point_pair(offset=11, num_limbs=7, num_limb_bits=56)` |
| Public inputs | 19 (accumulator occupies the trailing 8 words) |
| Verified on-chain | yes, 1,338,272 gas under revm Prague (2026-08-13 render: exact precompile gas bounds, typed errors, VM operand clamps, BUILD_ID, alpha vk-binding) |
| Native/Solidity trace | 244 trace points matched |

## Regenerating

Needs a Moonlight checkout on `origin/codex/wrap-bench-cherry-picks` placed as
a **sibling of this repository** -- its `aggregation/Cargo.toml` refers to
`../../midfall/proofs/solidity-verifier` by relative path, so the bench renders
with local codegen.

That branch pins the Midfall crates to a fixed git revision, which would link a
second copy of `midnight-proofs` alongside the path-dependency one. Add a patch
to the Moonlight workspace `Cargo.toml` to unify them (do not commit it):

```toml
[patch."https://github.com/EYBlockchain/midfall.git"]
midnight-circuits = { path = "/path/to/midfall/circuits" }
midnight-curves = { path = "/path/to/midfall/curves" }
midnight-proofs = { path = "/path/to/midfall/proofs" }
midnight-zk-stdlib = { path = "/path/to/midfall/zk_stdlib" }
blake2b_halo2 = { path = "/path/to/midfall/third_party/blake2b_halo2" }
```

Then, from the Moonlight checkout (needs `midnight-srs-2p19`/`2p20` in
`SRS_DIR`; takes several minutes):

```bash
MOONLIGHT_RUN_WRAP_SOLIDITY_BENCH=1 \
MOONLIGHT_RUN_WRAP_SOLIDITY_TRACE=1 \
MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR=/path/to/midfall/proofs/solidity-verifier/target/moonlight-wrap-solidity-dump \
SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
  cargo test --release --lib \
    wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs \
    -- --ignored --nocapture

cp target/moonlight-wrap-solidity-dump/{Halo2Verifier.sol,Halo2VerifyingKey.sol,\
calldata.bin} fixtures/moonlight-wrap/
```

Then update the source commit above.

## Staleness

A snapshot of the codegen that produced it. The artifacts are self-consistent,
so the replay keeps passing after a codegen change -- it just stops exercising
current output. Tracked by the commit stamp rather than an assertion, because
detecting drift means re-rendering, which needs the SRS and the Moonlight
checkout again.

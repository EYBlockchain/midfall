# conformance bundles

Written by the Rust exporter, read by the Lean runner. **Not hand-edited.**

There are two bundles because there are two SRSs (REF.11, D-P63):

| bundle | directory | SRS | trapdoor |
|---|---|---|---|
| **F0** | `poseidon/` | Filecoin ceremony, loaded from `$SRS_DIR` | unknown |
| **F1** | `poseidon-testsrs/` | `ParamsKZG::unsafe_setup(6, ChaCha8Rng::seed_from_u64(0x5eed))` | exported in `params.json` |

F1 is the bundle the M1-M4 gates read: with a public trapdoor, acceptance, the
`-s*G2` pin and the generator's own SRS check become computations. **Its trapdoor
is public, so no soundness of the proof system is claimed for it** (D-P63). F0 is
kept unchanged as a second instance of the reference gate.

## Files in a bundle

`vk.json` `cs.json` `params.json` `instances.json` `proof.bin` `trace.json`
`calldata.bin` `evm.json` `mutations.json` `manifest.sha256`

Schema and every key: `formal/docs/conformance-schema.md`.

## Regenerate

F0 - the Filecoin bundle. **This writes into `poseidon/`; only run it deliberately.**

    cd <repo>
    cargo test -p halo2_solidity_verifier --features rust-verifier-trace \
      --test conformance_export -- --nocapture

F1 - the test-SRS bundle. Add the `evm` feature and the pinned solc for the EVM leg;
without them `evm.json` records `evm_executed: false` and everything else is identical.

    cd <repo>
    MIDFALL_CONFORMANCE_SRS=unsafe:0x5eed \
    SOLC="$PWD/proofs/solidity-verifier/.solc/solc" \
    cargo test -p halo2_solidity_verifier --features rust-verifier-trace,evm \
      --test conformance_export -- --nocapture

Output directory: `MIDFALL_CONFORMANCE_OUT`, defaulting to the mode's own directory
above. `MIDFALL_CONFORMANCE_FIXTURE=committed` replays the committed
`proofs/solidity-verifier/fixtures/poseidon` bytes instead; that mode currently
reports a finding and writes nothing, because the committed proof is rejected
under the feature profile the trace hooks require (see the header of
`proofs/solidity-verifier/tests/conformance_export.rs`).

### Reproducibility - read this before trusting a hash

`proof.bin` is **not** reproducible across runs: the prover blinds the quotient
limbs with `F::random(OsRng)` (`proofs/src/plonk/prover.rs:121-131`), which the
seeded prover RNG does not reach. `trace.json`, `calldata.bin`, `evm.json` and
`mutations.json` inherit that. What does reproduce byte for byte is the
circuit-and-SRS half - `vk.json`, `cs.json`, `params.json`, `instances.json`,
including the exported trapdoor and SRS digest.

So `manifest.sha256` **pins one run**; it is not a regeneration check. Seeding the
blinding is a `proofs/src` change and out of scope (D-P58). Details:
`formal/docs/conformance-schema.md`, "Reproducibility".

## Verify a bundle

    cd formal/fixtures/conformance/<bundle> && sha256sum -c manifest.sha256

## Replay

    cd formal
    lake build midfall-conformance
    lake exe midfall-conformance fixtures/conformance/poseidon

Exit codes: 0 every compared value agreed and at least one value was compared;
1 any mismatch (each one printed with both sides); 2 the bundle could not be read
or did not parse. Schema: formal/docs/conformance-schema.md.

# conformance bundles

Written by the Rust exporter, read by the Lean runner. Not hand-edited.

## Regenerate (poseidon)

    cd <repo>
    cargo test -p halo2_solidity_verifier --features rust-verifier-trace \
      --test conformance_export -- --nocapture

Output directory: MIDFALL_CONFORMANCE_OUT, default
formal/fixtures/conformance/poseidon. Set MIDFALL_CONFORMANCE_FIXTURE=committed
to replay the committed proofs/solidity-verifier/fixtures/poseidon bytes instead;
that mode currently reports a finding and writes nothing, because the committed
proof is rejected under the feature profile the trace hooks require (see the header
of proofs/solidity-verifier/tests/conformance_export.rs).

## Replay

    cd formal
    lake build midfall-conformance
    lake exe midfall-conformance fixtures/conformance/poseidon

Exit codes: 0 every compared value agreed and at least one value was compared;
1 any mismatch (each one printed with both sides); 2 the bundle could not be read
or did not parse. Schema: formal/docs/conformance-schema.md.

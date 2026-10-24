# Conformance exporter schema (D-P12)

`conformance-rs` is a **new workspace member** depending on `proofs` and
`zk_stdlib`. It modifies neither, so no baseline bump is required and the frozen
`Statements.lean` hash discipline is untouched. This file is the contract between
the exporter and the Lean runner; it exists before either because the shape was
derived from experiments, not guessed at.

## Why this schema and not plan Section 5's

Plan Section 5 asks `vk.json` for the "full cs". Two findings made that both
expensive and insufficient:

* **Expensive**: `ConstraintSystem` has no serde derives, so "full cs" means
  hand-writing a serializer for ~20 fields plus `Expression` trees **inside
  `proofs/src`** - a baseline bump for data the verifier never needs re-derived.
* **Insufficient**: `rust_trace.json` records each squeeze's **challenge**
  (`digest mod r`), but the transcript reseeds with the **raw digest**. Reduction
  is not invertible, so a recorded challenge cannot seed the next step. Proven on
  poseidon: all 10 challenges are `< r` where a raw digest would be below `r` with
  probability ~0.34. See `docs/ecosystem.md` section 11.

So the schema below carries the **minimal** VK data needed to reproduce the
transcript, and requires the exporter to emit **raw digests**, not just
challenges. If `solidity_trace` cannot emit raw digests without touching
`proofs/src`, the fallback is to emit the complete absorb stream instead - the
Lean side can then compute the digests itself, which is preferable to a baseline
bump.

## `vk.json`

```json
{
  "schema": 1,
  "k": 22,
  "n": 4194304,
  "omega_be_hex": "...32 bytes big-endian...",
  "omega_inv_be_hex": "...",
  "cs_degree": 5,
  "quotient_poly_degree": 4,
  "transcript_repr_be_hex": "...32 bytes...",
  "num_advice_columns": 33,
  "num_fixed_columns": 13,
  "num_instance_columns": 2,
  "num_challenges": 0,
  "nb_public_inputs": 1,
  "num_committed_instances": 1,
  "fixed_commitments_compressed_hex": ["...48 bytes...", "..."],
  "permutation_commitments_compressed_hex": ["..."],
  "advice_column_phase": [0, 0, 0],
  "selector_flags": [{"is_simple": true, "col_idx": 0}],
  "instance_queries": [[0, 0], [1, 0]],
  "blinding_factors": 9
}
```

Field notes:

* `transcript_repr_be_hex` is the imported scalar of D-P1/R-1. The runner must
  **assert** it equals what the Rust computes, not trust it - the VK binding is an
  assumption about the importer (plan Section 1).
* `instance_queries` entries are `[column_index, rotation_int]`. The column order
  is what resolves D-P11's open question: whether `format_instance` emits
  `[committed..., public...]` in that order. Emit it explicitly rather than
  letting the Lean side assume it.
* `blinding_factors` is exported because `Spec/Relation.usable` depends on it and
  it can fault in the reference (circuit.rs:2510). A fault must be an exporter
  error, not a missing field.
* Commitments are 48-byte **compressed** hex, matching the wire format the
  transcript reads. The 128-byte EIP form is derived on the Lean side by the
  codec, never duplicated here.

## `trace.json` - the change that makes a replay possible

Same event list as the existing `rust_trace.json`, plus one field per squeeze:

```json
{
  "kind": "Challenge",
  "name": "theta",
  "fe_be_hex": "...challenge = digest mod r...",
  "digest_be_hex": "...RAW digest, the reseed value...",
  "absorbed_before_hex": ["...each absorb since the previous squeeze..."]
}
```

* `digest_be_hex` is the field the current trace lacks. With it the chain is
  replayable link by link and each squeeze is independently checkable.
* `absorbed_before_hex` is the alternative if raw digests cannot be emitted: the
  byte strings absorbed since the previous squeeze, in order. Either field is
  sufficient; both is best, because then the runner can verify the exporter
  against itself.
* Reads keep `eip2537_hex` for compatibility, **but note the name is a misnomer**:
  it holds the 48-byte compressed encoding, not EIP-2537's 128-byte uncompressed
  form. Established empirically (21/21 poseidon points land on the curve reading it
  as big-endian x with the top three bits of byte 0 as flags). A field rename to
  `compressed_hex` is recommended for schema 2; keeping the old name is kept here
  for compatibility with the existing fixtures.

## `params.json`, `instances.json`, `proof.bin`

* `params.json`: `g1`, `g2`, `s_g2`, `n_g2` as compressed/uncompressed hex with an
  explicit `format` tag, since `n_g2` is the negated generator and that hazard is
  already recorded at `Exec/Kzg/Params.lean`.
* `instances.json`: the per-proof, per-column instance values, so the runner does
  not have to reconstruct `pi`.
* `proof.bin`: unchanged, the compressed proof bytes.

## Acceptance for the first slice

1. Export poseidon. The Lean runner reproduces **all 10 challenges byte for
   byte** from `vk.json` + `instances.json` + `proof.bin`.
2. `verifyNative` accepts the poseidon proof and rejects each single-bit mutation
   the mutation corpus produces, with the error class matching.
3. Only then widen to ivc and rsa_signature.

Step 1 is the first genuine Rust-vs-Lean conformance result in the project, and
the reason the whole exporter exists. Note the honest limit: byte-identity over a
corpus is conformance evidence, not proof of equivalence for every Rust input.
The formal claim is the lowering work (M5-M8), not this.


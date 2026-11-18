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

## Schema 2 - REF.11: the test SRS, the trapdoor, calldata, mutations, manifest

Schema 2 is **additive**. The `schema` integer stays 1 - the committed Lean
importer parses it, and the card's acceptance is that the Filecoin bundle's
existing fields stay byte-identical apart from added keys. The extension is named
by `params.json:schema_extension = 2`.

### Two bundles, one exporter

`MIDFALL_CONFORMANCE_SRS` selects the SRS, and each mode owns its own directory so
neither export can overwrite the other:

| value | bundle | directory | trapdoor |
|---|---|---|---|
| unset, or `filecoin` | **F0** | `formal/fixtures/conformance/poseidon/` | unknown (ceremony secret) |
| `unsafe:<seed>` | **F1** | `formal/fixtures/conformance/poseidon-testsrs/` | exported (D-P63) |

F1 is built by `ParamsKZG::unsafe_setup(K, ChaCha8Rng::seed_from_u64(seed))`
(`proofs/src/poly/kzg/params.rs:98-135`). That call draws the toxic scalar as the
first thing it takes from the rng, so a second stream from the same seed
reproduces it; the exporter asserts `g2 * s == s_g2` before writing anything, so a
wrong re-derivation is a panic and not a silent pin.

**The trapdoor is public.** D-P63: F1 exists so that acceptance, the `-s*G2` pin and
the generator's own SRS check become computations. No soundness of the proof
system is claimed for this SRS, and `SrsEncodes` is not a hypothesis of `Done`.

### New `params.json` keys

| key | meaning |
|---|---|
| `schema_extension` | `2`, naming this additive extension |
| `srs_kind` | `"filecoin"` or `"unsafe-seeded"` |
| `srs_seed` / `srs_seed_hex` | the seed passed to `ChaCha8Rng::seed_from_u64`; `null` for F0 |
| `trapdoor_s_be_hex` | the 32-byte big-endian trapdoor `s`; `null` for F0 |
| `trapdoor_note` | what the trapdoor is and is not, stated in the bundle |
| `g2_eip_hex`, `s_g2_eip_hex`, `neg_s_g2_eip_hex` | the 256-byte EIP-2537 padded forms, eight 32-byte words `x.c0_hi, x.c0_lo, x.c1_hi, x.c1_lo, y.c0_hi, y.c0_lo, y.c1_hi, y.c1_lo` |
| `srs_sha256` | sha256 of the whole serialized SRS (`write_custom`, `SerdeFormat::Processed`: k, all monomial G1 powers, all Lagrange G1 powers, g2, s_g2) |

The EIP forms come from the verifier's own encoder
(`lowering::encoding::g2_to_u256s`, re-exported as `__test_only_g2_to_u256s`), not a
second copy: the pin the Lean side checks is the pin the Solidity constructor
embeds. `neg_s_g2_eip_hex` is `-s*G2`, the second pairing argument; the pre-existing
`n_g2_compressed_hex` is `-G2`, the first one. `srs_sha256` hashes the whole SRS
rather than only the two G2 points, because pinning g2 and s_g2 alone would not
pin the G1 powers the commitments are made from.

### New `trace.json` keys

`proof_hex` (proof.bin as hex, so a JSON-only reader can pin the exact bytes),
`srs_kind`, `srs_seed`, and the `reproducibility` block below.

### `calldata.bin`, `evm.json`, `mutations.json`, `manifest.sha256`

* `calldata.bin` - the bytes of one `Halo2Verifier.verifyProof` call, produced by
  `SolidityGenerator::encode_calldata` on the same proof, instances and SRS the
  native run accepted.
* `evm.json` - that calldata rendered, compiled with the pinned solc, deployed and
  called on revm 19 (Prague, EIP-2537 precompiles): status, `accepted`, gas, output
  word, solc version. Requires the `evm` feature; without it the file is still
  written with `evm_executed: false` and the calldata digest, so the bundle's shape
  does not silently depend on the feature set.
* `mutations.json` - the corpus. `reads[]` tiles proof.bin into the 72 transcript
  reads (offsets and widths taken from the accepted run and asserted to tile it
  exactly). Then one single-bit mutation per read - the low bit of that read's
  first byte - plus four structural shapes (last byte truncated, half truncated,
  empty, a zero byte appended) and one control (the unmutated proof). Every
  mutant is scored by the real verifier (`prepare` plus the KZG pairing check), so
  `verdict` and `error` are the verifier's own answer and REF.12 replays classes
  rather than re-deriving them. An accepting mutant is printed as a FINDING, not
  hidden; at the current tip only the control accepts.
* `manifest.sha256` - `sha256sum -c` input over the nine bundle files in a fixed
  order.

### Reproducibility: what a run pins and what it does not

**Read this before concluding anything from a hash.** The prover's inter-limb
quotient blinding draws from `OsRng` (`proofs/src/plonk/prover.rs:121-131`,
`blind_quotient_limbs` under `cfg(not(feature = "single-h-commitment"))`). The seeded
`prover_rng` does not reach it. So:

* **reproduces byte for byte across runs**: `vk.json`, `cs.json`, `params.json`,
  `instances.json` - the circuit-and-SRS half, including `trapdoor_s_be_hex` and
  `srs_sha256`.
* **does not reproduce**: `proof.bin` and everything derived from it - `trace.json`,
  `calldata.bin`, `evm.json` (including its gas figure), `mutations.json`. The
  divergence starts where the H-limb commitments begin (byte 720 of 2640 at the
  poseidon fixture) and propagates through every later challenge.

Therefore **`manifest.sha256` pins one run; it is not a regeneration check.** Two
independent export runs produce different manifests. Fixing that means seeding
`blind_quotient_limbs`, which is a `proofs/src` change and out of scope for D-P58.
The exporter records this in `trace.json:reproducibility` so the bundle carries its
own caveat.

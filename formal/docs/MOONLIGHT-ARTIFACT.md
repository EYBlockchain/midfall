# Moonlight artifact conformance — measured state

## What “the deployed ones” are

The only on-chain verifier deployment recorded in this repository is

| contract | address | runtime bytes | runtime code hash |
| --- | --- | ---: | --- |
| `Halo2VerifyingKey` | `0x80b32f68A333dF55Da60BEc44C498477a8311eDe` | 17025 | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `0x5CfEd44D16F994fc17f681A83FEdFEB9c3348c17` | 21161 | `0x2e1e46a83888a8989698b1f3ad87387db52408e015b11d7cff24a930b0baa776` |

Sources and the fetched runtime bytecode are under
`proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/`.

The checked-in sources **are** the sources of the fetched runtime bytecode.  This
is checked by `proofs/solidity-verifier/scripts/check_moonlight_artifacts.py`:

```text
[VK] mstore words=532 built=17025 fetched=17025 exact=True
[verifier] compiled=21173 fetched=21161 trailer=a164736f6c634300081e000a prefix-exact=True
[moonlight-artifacts] vk=True verifier=True
```

The VK constructor's 532 payload `mstore`s rebuild the fetched runtime exactly.
The verifier compiles with the pinned solc 0.8.30 (`--via-ir --optimize
--optimize-runs 200 --evm-version cancun --metadata-hash none`) to 21,173 bytes;
after filling the two `AUTHORIZED_VK` immutable slots and stripping solc's
12-byte CBOR trailer, the first 21,161 bytes are byte-identical to the fetched
runtime.  So the deployed artifact is internally consistent; the mismatch with
the current Lean render is a **generator-version** mismatch, not corrupted
deployment data.

The deployment is a **Moonlight wrap** circuit: 19 instances, `k = 20`,
`has_accumulator = 1` (`acc_offset = 11`, 7 × 56-bit limbs), separate VK,
embedded quotient VM (no `AUTHORIZED_QUOTIENT`), solc 0.8.30, via-IR, optimizer
200, no metadata, no gas checkpoints.

## The Lean-generated contract does NOT match this deployment

This is measured, not inferred:

| item | deployed Moonlight source | current generator (tracked IVC artifact) |
| --- | --- | --- |
| pragma | `^0.8.24` | `0.8.30` |
| `TRANSCRIPT_MPTR` | `0x80` | `0x1000` |
| `RETURN_MPTR` | `0x80` | `0x1000` |
| `BUILD_ID` | absent | present |
| accumulator validation | `validate_public_accumulator(success, r) -> out` | `-> out, precompile_failed` |
| batch pointer | `0x0100` | `0x1000` |
| batch hash length | `0x0220` | `0x0240` |

The deployed source predates the current generator and uses a different layout
and accumulator call shape. It is also a different circuit (Moonlight wrap) from
the tracked Poseidon/F1 and IVC fixtures. Byte equality with the current Lean
render is therefore **false**, and cannot be recovered by a proof-only change.

## What does match: the current accumulator / batched-pairing artifact

The current generator’s accumulator and batched-pairing path is byte-exact
against the tracked current-generator IVC decider artifact
(`proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol`,
also tracked under `formal/fixtures/conformance/ivc/`). The Lean gates in
`formal/Midfall/Generator/IvcPartialKats.lean` were run at this tree:

```text
f2_assemblyHelpers_bytesExact_ok            true
f2_accumulatorHelpers_bytesExact_ok          true
f2_vkLoading_bytesExact_ok                   true
f2_transcriptProofParser_bytesExact_ok       true
f2_lagrange_bytesExact_ok                    true
f2_quotientAndLinearization_external_ok      true
f2_finalPairing_bytesExact_ok                true   -- the accumulator-batched FinalPairing
```

The batched `FinalPairing` block is the same alpha-randomised accumulator/KZG
batch in both artifacts. The deployed Moonlight block differs only by the stale
spellings above (`gas()` vs `G1MSM_GAS_1PAIR`/`G1ADD_GAS`, bare `revert(0,0)` vs
`fail(ERR_PRECOMPILE_FAILED)`, and the old batch pointer/offset).

The current generator’s batched-pairing source is
`Gamma.Generator.VerifierPartials.emitAccBatch`; the current-generator
batched-pairing reference contract is
`formal/fixtures/conformance/ivc/Halo2Verifier.sol`.

## Blocker for generating a fresh Moonlight contract

To render Moonlight with the current generator we need the Moonlight key’s

- `vk.json` (the `Halo2VerifyingKey`/domain/commitments used by the generator),
- `cs.json` (the constraint system: queries, phases, lookups, fixed columns,
  permutation columns), and
- the wrap circuit’s `num_instances`/accumulator configuration (19 / 11 / 7).

Neither `formal/fixtures/conformance/` nor the local Moonlight checkout contains
those exports. `/Users/julian/Moonlight` is at `fbd0f4f` and has **no**
`MOONLIGHT_WRAP_SOLIDITY_*` dump hooks, so it cannot emit `Halo2Verifier.sol`.
The checked-in Moonlight artifacts are fetched-back Sepolia runtime bytecode, so
refreshing them additionally needs a funded deployment. `formal/BASELINE.md`
already records this as **BLOCKED, environment, not code**.

## Recommended path

1. Pin or update a Moonlight checkout that contains the wrap Solidity dump hooks
   (or add a hook that writes `vk.json`, `cs.json`, and the generated
   `Halo2Verifier.sol` from the wrap key).
2. Run the wrap conformance export once to produce the Moonlight bundle.
3. Feed that bundle to the current Lean `generate` path with
   `cfg.accumulator := some (pointAndScalar 11 7 56)` and an embedded quotient
   VM, then compare the generated `Halo2Verifier.sol` to the exported source.
4. Regenerate the Sepolia artifacts only if an on-chain match is required;
   otherwise the comparison target is the fresh local export.

Until step 1 supplies the key, “Lean matches the deployed Moonlight contract” is
not a true statement: the deployed file is a stale-generator artifact. The
current generator’s batched pairing is nevertheless verified against the
current IVC accumulator artifact, as listed above.

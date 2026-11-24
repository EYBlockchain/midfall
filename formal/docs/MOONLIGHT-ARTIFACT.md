# Moonlight artifact conformance — measured state

## What “the deployed ones” are

The only on-chain verifier deployment recorded in this repository is

| contract | address | runtime bytes | runtime code hash |
| --- | --- | ---: | --- |
| `Halo2VerifyingKey` | `0x80b32f68A333dF55Da60BEc44C498477a8311eDe` | 17025 | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `0x5CfEd44D16F994fc17f681A83FEdFEB9c3348c17` | 21161 | `0x2e1e46a83888a8989698b1f3ad87387db52408e015b11d7cff24a930b0baa776` |

Sources and the fetched runtime bytecode are under
`proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/`.

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
batch in both artifacts, but the deployed Moonlight block is the **pre-I-7**
batch: it has no `vk_digest` word, uses offsets `0x20/0xa0/0x120/0x1a0` and a
`0x0220` hash length, while the current generator inserts `vk_digest` at
`0x20`, shifts the four points to `0x40/0xc0/0x140/0x1c0`, and hashes `0x0240`
bytes. The deployed block also uses bare `gas()` and `revert(0,0)` where the
current generator uses `G1MSM_GAS_1PAIR`/`G1ADD_GAS` and `fail(...)`. The
alpha-randomised equation itself is the same.

The current generator’s batched-pairing source is
`Midfall.Generator.VerifierPartials.renderFinalPairing`; the current-generator
batched-pairing reference contract is
`formal/fixtures/conformance/ivc/Halo2Verifier.sol`.

## Seven-partial probe at the deployed Moonlight context

`formal/Midfall/Generator/MoonlightPartialKats.lean` defines
`MoonlightPartialCtx`: 19 instances, `k = 20`, accumulator offset 11 with 7 ×
56-bit limbs, no carried scalars, no fixed-base tail, separate VK, embedded
quotient VM, `TRANSCRIPT_MPTR = RETURN_MPTR = 0x80`, and the proof layout read
from the deployed parser (`0x1e60` bytes; 15 advice G1, 2 multiplicity G1, 6
permutation-Z G1, two lookups of 1 helper + 1 accumulator, 1 trashcan, 4
quotient limbs, 102 eval words, 5 q_evals, 1 pi). The deployed VK runtime header
is cross-checked independently from `Halo2VerifyingKey.runtime.bytecode.hex`, and
the 21161-byte verifier runtime is tied to the deployed VK address, VK codehash
word, and batch domain tag.

The measured status against the deployed source is:

| partial | current bytes | raw `occ` | raw `includeBoundary` | measured difference |
| --- | ---: | ---: | :---: | --- |
| `AssemblyHelpers` | 16226 | 0 | false | current adds the `fail` helper, scalar canonicality checks, the batch-invert canonicality/MF-4 paths and the pairing `== 1` check; deployed uses bare `revert`/`gas()` |
| `AccumulatorHelpers` | 17009 | 0 | false | public-input codec differs: deployed carries the identity flag in x's first packed word (`load_acc_coord_shifted(..., first_adjust)`), current expects a separate identity-flag word; current also returns `precompile_failed` and uses gas constants |
| `VkLoading` | 5821 | 0 | false | four failure boundaries (`fail(...)`) replace bare reverts: VK codehash, VK header, calldata shape, and the accumulator decode/precompile split |
| `TranscriptProofParser` | 17968 | 0 | false | five `fail(...)` selectors replace bare `revert(0,0)`; the cursor/layout/loop structure is otherwise identical |
| `Lagrange` | 4745 | 0 | false | `LAGRANGE_DENOMS_MPTR` is the deployed `X_N_MPTR` (same address 0x6cc0), and the current block adds the MF-4 return/fail path; the arithmetic and loop bounds match |
| `QuotientAndLinearization` (linearization tail) | 1901 | 1 | false | **byte-identical** linearization tail (deployed lines 2822-2861); it is an interior sub-block of the larger quotient include, not a standalone include, so the boundary is false |
| `FinalPairing` | 4221 | 0 | false | pre-I-7 batch (no `vk_digest`, `0x0220`) vs current `vk_digest`/`0x0240`, gas constants, and `fail` selector; same alpha-randomised equation |

Every exact changed line, with absolute deployed and current line numbers, is in
`formal/docs/MOONLIGHT-PARTIAL-DIFFS.md`. The KAT pins the raw occurrence,
boundary and byte counts in `moonlight_recordedStatus_ok`; no partial except the
quotient linearization tail is a byte match, and no current render is a
standalone include of the deployed contract.

## Blocker for generating a fresh Moonlight contract

To render Moonlight with the current generator we need the Moonlight key’s

- `vk.json` (the `Halo2VerifyingKey`/domain/commitments used by the generator),
- `cs.json` (the constraint system: queries, phases, lookups, fixed columns,
  permutation columns), and
- the wrap circuit’s `num_instances`/accumulator configuration (19 / 11 / 7).

The deployed VK runtime is present and parseable (`INVALID` prefix plus 17024
payload bytes; the header words match 19/20/1/11/7/56), but it contains only the
header, base points, quotient program/constant table, and fixed/permutation
commitments. It does not contain the constraint-system query/phase/lookup/
fixed-column/permutation description the generator needs, and the emitted source
is not a substitute for that input. Neither `formal/fixtures/conformance/` nor
the local Moonlight checkout contains the `vk.json`/`cs.json` exports.
`/Users/julian/Moonlight` is at `fbd0f4f` and has **no**
`MOONLIGHT_WRAP_SOLIDITY_*` dump hooks, so it cannot emit `Halo2Verifier.sol`.
The checked-in Moonlight artifacts are fetched-back Sepolia runtime bytecode, so
refreshing them additionally needs a funded deployment. `formal/BASELINE.md`
already records this as **BLOCKED, environment, not code**.

There is also a codec mismatch independent of the missing files: the deployed
accumulator helper encodes the point-at-infinity identity flag inside x's first
packed public-input word, while the current generator's `load_acc_point` expects
a separate identity-flag word after y. Re-rendering the deployed Moonlight
circuit with the current generator would therefore require either the old codec
as a compatibility arm or a re-generated Moonlight wrap key whose public inputs
use the current codec; the deployed proof/public-input ABI cannot be matched by
changing only the VK/CS inputs.

## Recommended path

1. Pin or update a Moonlight checkout that contains the wrap Solidity dump hooks
   (or add a hook that writes `vk.json`, `cs.json`, and the generated
   `Halo2Verifier.sol` from the wrap key).
2. Run the wrap conformance export once to produce the Moonlight bundle.
3. Feed that bundle to the current Lean `generate` path with
   `cfg.accumulator := some (pointAndScalar 11 7 56)` and an embedded quotient
   VM, then compare the generated `Halo2Verifier.sol` to the exported source.
   For the existing deployed artifact, also resolve the separate-identity-flag
   vs embedded-x-flag codec mismatch recorded above.
4. Regenerate the Sepolia artifacts only if an on-chain match is required;
   otherwise the comparison target is the fresh local export.

Until step 1 supplies the key, “Lean matches the deployed Moonlight contract” is
not a true statement: the deployed file is a stale-generator artifact. The
current generator’s batched pairing is nevertheless verified against the
current IVC accumulator artifact, as listed above.

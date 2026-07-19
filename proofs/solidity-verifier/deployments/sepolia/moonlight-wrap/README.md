# Moonlight Wrap Sepolia Deployment

This directory contains the generated Moonlight wrap verifier contracts that
were deployed to Sepolia, plus the exact runtime bytecode fetched back from the
chain.

## Status: deployed code predates current codegen

**The contracts at the addresses below are still the ones described here, but
the generator has since moved on. They are not reproducible from current
`main`.** Nothing in this directory has been regenerated -- the sources and
bytecode remain exactly what was deployed, because they are the record of what
is on chain.

Re-rendering the same circuit at `e5300d4` produces a different verifier:

| | Deployed | Current codegen |
| --- | ---: | ---: |
| `Halo2Verifier.sol` | 206,619 bytes | 212,419 bytes |
| Verifier runtime | 21,161 bytes | 21,203 bytes |
| `TRANSCRIPT_MPTR` | `0x80` | `0x1000` |

The verifying key also differs, in its `quotient_program` section; the circuit
itself is unchanged (`acc_offset = 11`, 19 public inputs, `point_pair`).

Fixes made after this deployment that it therefore does **not** carry:

- **Memory layout rebase.** The deployed verifier bases its layout at `0x80`,
  inside the `[0x80, 0x8e0)` window solc reserves for via-IR stack-to-memory
  spill slots -- see AUDIT.md TA-5. It has not misbehaved, but the separation
  rests on spill placement rather than on anything enforced.
- **Accumulator identity guard.** `load_acc_coord_shifted` used a bitwise `and`
  against a radix base, making the guard false on every call; the identity
  branch was dead and the canonicality barrier ineffective. Fail-closed, not a
  forgery path.
- **Pairing result check.** `ec_pairing` folded the precompile result with a
  bitwise `and`, accepting any odd return word rather than exactly `1`.
- **Constructor smoke test.** Probes used identity-only EIP-2537 vectors, which
  a non-conformant precompile can satisfy without doing curve arithmetic.

Redeploying is a deliberate on-chain action requiring a funded keystore and an
RPC endpoint; see "Recreate The Deployment" below. Until then this record stays
as-is and accurate.

## Verifying the deployed bytecode

The tracked source reproduces the on-chain runtime exactly, apart from the
immutable address slots that are substituted at deployment:

```bash
solc --bin-runtime --optimize --optimize-runs 200 --via-ir \
  --evm-version cancun --no-cbor-metadata Halo2Verifier.sol
```

That yields 21,161 bytes -- matching `runtimeBytes` -- with codehash
`0x79432a36a98570db8c04b9c5cc23994477089eabd2501cfe0b0a78ae5f3c38f8`.

It does **not** equal the recorded `runtimeCodeHash`, and should not: comparing
compiled output byte-for-byte against on-chain code shows exactly 40 differing
bytes, in two 20-byte runs at offsets `0x51` and `0x125`. Those are the two
placeholder slots for `address public immutable AUTHORIZED_VK`, filled in by the
constructor. Every other byte is identical. Verified at `e5300d4` with
`solc 0.8.30+commit.73712a01`.

## Addresses

| Contract | Address |
| --- | --- |
| `Halo2VerifyingKey` | [`0x80b32f68A333dF55Da60BEc44C498477a8311eDe`](https://sepolia.etherscan.io/address/0x80b32f68A333dF55Da60BEc44C498477a8311eDe) |
| `Halo2Verifier` | [`0x5CfEd44D16F994fc17f681A83FEdFEB9c3348c17`](https://sepolia.etherscan.io/address/0x5CfEd44D16F994fc17f681A83FEdFEB9c3348c17) |

## Transactions

| Action | Transaction |
| --- | --- |
| Deploy VK | [`0xf96f25bd4f44b815a93b5d3a8f3c59d8f62afd4d6a10adf60139c73c5b7243dc`](https://sepolia.etherscan.io/tx/0xf96f25bd4f44b815a93b5d3a8f3c59d8f62afd4d6a10adf60139c73c5b7243dc) |
| Deploy verifier | [`0x5b34c4f25cdd6a641150488b0dc5edb130d0e8fd160408789f8ecd09f99bf417`](https://sepolia.etherscan.io/tx/0x5b34c4f25cdd6a641150488b0dc5edb130d0e8fd160408789f8ecd09f99bf417) |
| Verify fresh proof | [`0x013fb1a6323d51574c0c5b1c2e79ec4fb84706474c1c06601fa6e61737eb15a4`](https://sepolia.etherscan.io/tx/0x013fb1a6323d51574c0c5b1c2e79ec4fb84706474c1c06601fa6e61737eb15a4) |

## Gas

| Action | Gas used |
| --- | ---: |
| Deploy VK | `3,723,458` |
| Deploy verifier | `5,295,315` |
| Verify fresh proof | `1,291,730` |

The verifier was rendered without gas checkpoints. The proof verification
transaction emitted zero logs.

## Runtime Metadata

| Contract | Runtime bytes | Runtime code hash |
| --- | ---: | --- |
| `Halo2VerifyingKey` | `17025` | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `21161` | `0x2e1e46a83888a8989698b1f3ad87387db52408e015b11d7cff24a930b0baa776` |

## Files

- `Halo2VerifyingKey.sol`: generated VK source.
- `Halo2Verifier.sol`: generated verifier source.
- `Halo2VerifyingKey.runtime.bytecode.hex`: exact deployed VK runtime bytecode from Sepolia.
- `Halo2Verifier.runtime.bytecode.hex`: exact deployed verifier runtime bytecode from Sepolia.
- `deployment.json`: address, transaction, gas, and bytecode metadata.

## Recreate The Deployment

From `proofs/solidity-verifier`:

```bash
scripts/install_pinned_solc.sh

cast wallet new ~/.foundry/keystores sepolia-moonlight
cast wallet address --account sepolia-moonlight
```

Fund that address with native Sepolia ETH, then deploy. Foundry can prompt for
the keystore password interactively:

```bash
SEPOLIA_RPC_URL=https://... \
scripts/deploy_moonlight_sepolia.sh \
  --account sepolia-moonlight \
  --skip-verify
```

For non-interactive runs, put the keystore password in a local file outside the
repo, `chmod 600` it, and add `--password-file /path/to/password-file`.

The deploy script writes:

```text
target/moonlight-wrap-sepolia-deployment.env
target/moonlight-wrap-sepolia-deployment.json
```

## Generate And Verify A Fresh Proof

Generate fresh Moonlight calldata, run a free `eth_call`, then broadcast a
verification transaction:

```bash
SEPOLIA_RPC_URL=https://... \
scripts/prove_and_verify_moonlight_sepolia.sh \
  --moonlight-dir /path/to/Moonlight \
  --deployment-env target/moonlight-wrap-sepolia-deployment.env \
  --account sepolia-moonlight \
  --no-trace \
  --send
```

Add `--password-file /path/to/password-file` for non-interactive keystore use.
Without `--send`, the script only runs `eth_call` and does not spend gas.

## Requirements

- Foundry: `forge` and `cast`.
- Pinned `solc` installed at `.solc/solc` or supplied via `SOLC`.
- Sepolia RPC URL.
- A funded Sepolia account.
- A Moonlight checkout with the wrap Solidity dump hook enabled.
- A Sepolia fork that supports EIP-2537 BLS12-381 precompiles.

# Moonlight Wrap Sepolia Deployment

This directory contains the generated Moonlight wrap verifier contracts that
were deployed to Sepolia, plus the exact runtime bytecode fetched back from the
chain.

## Addresses

| Contract | Address |
| --- | --- |
| `Halo2VerifyingKey` | [`0x8C70F334Be6ba4Bd13Bb0a4F7A88FA640A9a0910`](https://sepolia.etherscan.io/address/0x8C70F334Be6ba4Bd13Bb0a4F7A88FA640A9a0910) |
| `Halo2Verifier` | [`0x0AF93fb982cfBe7f8Cc12E58123497Ba68dCb021`](https://sepolia.etherscan.io/address/0x0AF93fb982cfBe7f8Cc12E58123497Ba68dCb021) |

## Transactions

| Action | Transaction |
| --- | --- |
| Deploy VK | [`0x8be21d8a313620dd040128f88ef01aac7e5c4e44e1f2ff2302f10c9cf28869a9`](https://sepolia.etherscan.io/tx/0x8be21d8a313620dd040128f88ef01aac7e5c4e44e1f2ff2302f10c9cf28869a9) |
| Deploy verifier | [`0xb3cf7ce86434d640a72a0286c8af7fb3974b69073ea3a9356a31368de4a461fb`](https://sepolia.etherscan.io/tx/0xb3cf7ce86434d640a72a0286c8af7fb3974b69073ea3a9356a31368de4a461fb) |
| Verify fresh proof | [`0x993e2357241a4ee87330e66fbd940c900255528cb66eb05634287a46cc27761c`](https://sepolia.etherscan.io/tx/0x993e2357241a4ee87330e66fbd940c900255528cb66eb05634287a46cc27761c) |

## Gas

| Action | Gas used |
| --- | ---: |
| Deploy VK | `3,723,458` |
| Deploy verifier | `5,295,315` |
| Verify fresh proof | `1,291,766` |

The verifier was rendered without gas checkpoints. The proof verification
transaction emitted zero logs.

## Runtime Metadata

| Contract | Runtime bytes | Runtime code hash |
| --- | ---: | --- |
| `Halo2VerifyingKey` | `17025` | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `21161` | `0xa85c3e8df15a46a685e405f57cfc85993228550db803d34a001b73d6c55bf61a` |

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

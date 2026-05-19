# Moonlight Wrap Sepolia Deployment

This directory contains the generated Moonlight wrap verifier contracts that
were deployed to Sepolia, plus the exact runtime bytecode fetched back from the
chain.

## Addresses

| Contract | Address |
| --- | --- |
| `Halo2VerifyingKey` | `0x2fE3dB07Cc00f6dFF002C37d5A17ebfAd7aA88D0` |
| `Halo2Verifier` | `0x049510AfEC69eD54409dabB57195FfD38400F4D0` |

## Transactions

| Action | Transaction |
| --- | --- |
| Deploy VK | `0xd6e7c6180a57c424327df03fe5b4ed0a274c73a4e8f681913582db5cf9e809cf` |
| Deploy verifier | `0x2236dc333064a88e7f23fc669570f72bf52163ca1cf637c29a6e77b743bfa60e` |
| Verify fresh proof | `0xd536e9162bab92c71b7b9f1bb94f00def8b50e441144c6aebd7708a51400abfb` |

## Runtime Metadata

| Contract | Runtime bytes | Runtime code hash |
| --- | ---: | --- |
| `Halo2VerifyingKey` | `17025` | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `21119` | `0x1422a1464cc070cd2d88cc9468edf6d88d99ead6cacbd942bfb0257e209f3b10` |

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

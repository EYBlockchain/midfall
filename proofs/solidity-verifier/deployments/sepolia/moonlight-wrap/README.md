# Moonlight Wrap Sepolia Deployment

This directory contains the generated Moonlight wrap verifier contracts that
were deployed to Sepolia, plus the exact runtime bytecode fetched back from the
chain.

## Addresses

| Contract | Address |
| --- | --- |
| `Halo2VerifyingKey` | `0x2132E1C5f2aFE710E0F3fE01ec70E95000F99882` |
| `Halo2Verifier` | `0x3d7f4A7BF9EB60EC7909880A68eaf41e4fB4B3b5` |

## Transactions

| Action | Transaction |
| --- | --- |
| Deploy VK | `0x5283e8cfd54be98b752cfee8fda8c0f02b196f8b0053af33850e4b2cd20df80a` |
| Deploy verifier | `0x69c4f9d0ac9098357346b3986c3fd48d062738124df91a73a89e314ecf044e0a` |
| Verify fresh proof | `0x91bac90773f107016103be132b543af5ea4457527e3866484e62cbb6e01fdb97` |

## Runtime Metadata

| Contract | Runtime bytes | Runtime code hash |
| --- | ---: | --- |
| `Halo2VerifyingKey` | `17025` | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `21368` | `0x21eafc97654cfecd897cd8957217254ce0570813e59a36bc835e8bc459ee9b55` |

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

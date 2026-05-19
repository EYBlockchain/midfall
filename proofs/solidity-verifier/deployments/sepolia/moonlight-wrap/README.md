# Moonlight Wrap Sepolia Deployment

This directory contains the generated Moonlight wrap verifier contracts that
were deployed to Sepolia, plus the exact runtime bytecode fetched back from the
chain.

## Addresses

| Contract | Address |
| --- | --- |
| `Halo2VerifyingKey` | [`0x0D2789bcDF4A0406Dc7383BD7D4b73A7f08CaC16`](https://sepolia.etherscan.io/address/0x0D2789bcDF4A0406Dc7383BD7D4b73A7f08CaC16) |
| `Halo2Verifier` | [`0xA826f6e66567EAFCd618175041a8F9E79f4661a2`](https://sepolia.etherscan.io/address/0xA826f6e66567EAFCd618175041a8F9E79f4661a2) |

## Transactions

| Action | Transaction |
| --- | --- |
| Deploy VK | [`0x22db64c0b4a15460d93b3091359f7988123be59b945cec4bcb91b3498587f588`](https://sepolia.etherscan.io/tx/0x22db64c0b4a15460d93b3091359f7988123be59b945cec4bcb91b3498587f588) |
| Deploy verifier | [`0x5bb4769deb461e2ca68a8ebaf1fbf44a0dbe9c526e4d7795b394a0292a853882`](https://sepolia.etherscan.io/tx/0x5bb4769deb461e2ca68a8ebaf1fbf44a0dbe9c526e4d7795b394a0292a853882) |
| Verify fresh proof | [`0x696e5b99fbdfc31adc71046d2afd01897a20f05202a46c2f0e70614853e9ac90`](https://sepolia.etherscan.io/tx/0x696e5b99fbdfc31adc71046d2afd01897a20f05202a46c2f0e70614853e9ac90) |

## Gas

| Action | Gas used |
| --- | ---: |
| Deploy VK | `3,723,458` |
| Deploy verifier | `5,349,137` |
| Verify fresh proof | `1,310,991` |

## Runtime Metadata

| Contract | Runtime bytes | Runtime code hash |
| --- | ---: | --- |
| `Halo2VerifyingKey` | `17025` | `0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009` |
| `Halo2Verifier` | `21410` | `0x2bebc2f2ae0446f93f97cda1a72c5b6b58b9aead3a3eaf3b12927ae1bd92d981` |

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

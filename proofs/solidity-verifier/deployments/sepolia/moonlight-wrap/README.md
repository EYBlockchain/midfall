# Moonlight Wrap Sepolia Deployment

This directory contains the generated Moonlight wrap verifier contracts that
were deployed to Sepolia, plus the exact runtime bytecode fetched back from the
chain.

> **Status: historical demo deployment, not regularly updated.** These
> contracts were deployed once, on 2026-05-19, and have not been redeployed
> since. They were rendered from a synthetic Moonlight wrap benchmark (dummy
> fold-leaf proofs, a `k = 20` wrap circuit, and a seeded `unsafe_setup` SRS
> whose secret is public, so proofs can be forged against them). They predate
> later changes to the Moonlight wrap circuit and to the generator's
> accumulator public-input layout, so they neither match current generator
> output nor accept current Moonlight wrap proofs. The files below are kept as
> an exact record of what is on-chain.

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

## Provenance

The contracts were generated from Moonlight's `codex/wrap-bench-cherry-picks`
wrap bench. The `deploy_moonlight_sepolia.sh` and
`prove_and_verify_moonlight_sepolia.sh` scripts that produced them have been
removed. They remain available in git history:

```bash
git log --diff-filter=D -- proofs/solidity-verifier/scripts/deploy_moonlight_sepolia.sh
```

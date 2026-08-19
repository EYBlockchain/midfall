# Reproducible Builds

This repository pins the generated Solidity verifier build inputs that affect
bytecode:

- Rust toolchain: `rust-toolchain.toml`
- Midfall dependency revision:
  `53dc872f495104046d96bdac0a690f903dc0c537`
- Solidity compiler: `solc 0.8.30+commit.73712a01`, installed and
  SHA-256-verified by `scripts/install_pinned_solc.sh`. Official binary
  hashes from `binaries.soliditylang.org/<platform>/list.json`:
  - `linux-amd64`:
    `f3e987dc6ecebd4bd350c48edcbc320b46cf9e3109bd3fc3d88f1acaf4c428f7`
  - `macosx-amd64` (also used on Apple Silicon via Rosetta 2):
    `738dcdc6afddeb505ee4e4ef24f1c1fdba2b8c924e614cbbf5801a5b062dd683`
- Solidity compile flags: `--bin --optimize --optimize-runs <N> --via-ir
  --evm-version cancun --no-cbor-metadata`, where `<N>` defaults to `200`
  (`DEFAULT_OPTIMIZE_RUNS` in `src/evm.rs`, override with
  `SOLC_OPTIMIZE_RUNS`); the IVC bench profiles below use `runs: 1`.

  **`--optimize-runs` is bytecode-affecting and must be recorded with every
  artifact hash.** It is also deployability-affecting: solc 0.8.30 at
  `runs=100000` emits a verifier over the EIP-170 24,576-byte runtime limit,
  i.e. an undeployable contract that compiles without complaint.

Repository-local `.cargo/config.toml` path overrides are intentionally not used.
All Midfall crates are resolved from the pinned git revision in `Cargo.toml`.

## Provenance Identities

Three different commit stamps appear across the audit and fixture documents.
They index different things; every recorded stamp should say which of these
it is:

| Stamp | Identifies |
| --- | --- |
| `53dc872f495104046d96bdac0a690f903dc0c537` | The **Midfall dependency** revision pinned in `Cargo.toml` (also the source of the comment corpus). |
| `a096e71746e401404f250817ca4e857bac1eef56` | **This repository** at the time the review packet (`docs/audit/REVIEW_PACKET.md`) was assembled. |
| `3fb6d84` | **This repository** at the time the moonlight-wrap replay fixture (`fixtures/moonlight-wrap/`) was rendered. |

## SRS Provenance

`NEG_S_G2_BASE` — the element every soundness guarantee of a deployed
verifier rests on — is derived from the SRS at build time. Build-time code
(`src/lowering/vk.rs`) proves the SRS is internally consistent (G1/G2 bases
canonical, `s_g2` pairing-bound to the tau underlying `g_lagrange`), and the
gated test `midnight_srs_assets_bind_s_g2_to_lagrange_tau` runs the same
check directly against the asset files. What internal consistency cannot
prove is *which ceremony* an asset came from; that link is this record.

Ceremony reference: the Midnight trusted-setup ceremony, published at
<https://github.com/midnightntwrk/midnight-trusted-setup>. Its
`MIDNIGHT_SRS_CATALOG.md` is the authoritative checksum table and also
documents a cargo tool for verifying an asset against the ceremony's
powers-of-tau transcript. *(Citation added 2026-08-12 from the reference in
`zk_stdlib/src/utils/plonk_api.rs`; deployment owners should confirm this is
the ceremony they intend to trust.)*

Recorded asset hashes (`scripts/record_srs_provenance.sh`, 2026-08-12;
Midnight rows verified byte-identical against the official catalog above):

| Asset | Bytes | SHA-256 | Matches official catalog |
| --- | ---: | --- | --- |
| `midnight-srs-2p19` | 100,663,684 | `8e8dc15c4362f05c912f1e770559a3945db3e58a374def416ed5d3e65ad5b10e` | yes (2026-08-12) |
| `midnight-srs-2p20` | 201,326,980 | `1cc62978558fdc1e445cd70cfd9a86ec3c2e2151b6d74811232d37faf9133ff1` | yes (2026-08-12) |
| `bls_filecoin_2p19` | 100,663,684 | `0574a536c128142e89c0f28198d048145e2bb2bf645c8b81c8697cba445a1fb1` | n/a (Filecoin SRS, test fixtures only) |

Re-run the script before any deployment build and compare against this
table; then run the tau-binding test:

```bash
HALO2_SOLIDITY_RUN_EVM_TESTS=1 cargo test --release --features evm midnight_srs_assets_bind_s_g2_to_lagrange_tau
```

## Canonical IVC Bench Command

The current default IVC Solidity bench uses the multi-limb outer decider proof
layout:

```bash
scripts/run_ivc_bench.sh --skip-srs-download
```

That command assumes `.srs/` already contains:

- `midnight-srs-2p19` for the leaf IVC proofs;
- `midnight-srs-2p20` for the decider base SRS.

Without `--skip-srs-download`, the script downloads missing Midnight SRS assets
it needs. With `--skip-srs-download`, it fails before compiling if any required
asset is missing.

The default run compiles and runs the final Solidity decider bench directly.

The final decider invocation uses:

- features:
  `evm,truncated-challenges,in-circuit-fewer-point-sets,solidity-gas-checkpoints`
- `SRS_DIR=./.srs` via the bench script default
- `solc optimize runs: 1`
- CBOR metadata omitted

Opt into the single-H outer proof shape with:

```bash
scripts/run_ivc_bench.sh --skip-srs-download --outer-single-h-commitment
```

That profile also needs `midnight-srs-2p22` for the extended monomial SRS and
runs a preliminary multi-limb leaf-bundle generator phase.

## Recorded Optional Outer Single-H Runtime Hashes

The concrete hashes below were generated with the fixed default quotient codegen shape:

```bash
scripts/run_ivc_bench.sh \
  --outer-single-h-commitment \
  --skip-srs-download
```

That command uses:

- features:
  `evm,truncated-challenges,in-circuit-fewer-point-sets,outer-single-h-commitment,solidity-gas-checkpoints`
- `SRS_DIR=./.srs` via the bench script default
- `solc optimize runs: 1`
- CBOR metadata omitted

Published deployed-runtime hashes:

| Artifact | Runtime bytes | Runtime `keccak256` |
| --- | ---: | --- |
| `Halo2Verifier` | 11,962 | `0x8772fd9c1c75fbc2bbf6699778e3a19004b05c386536d1026b157a1b254802a5` |
| `Halo2VerifyingKey` | 14,016 | `0xd081cc83b30d045cb208f3045bd3d8ed6eb3ba582f44bc8358128319fc535363` |
| `Halo2QuotientEvaluator` | 23,221 | `0x4f4ea4e626f795dece8a739204772e0a25f91a6ea8ff0524656d079a84167b6f` |

Total deployed runtime bytes: `49,199`.

The same run accepted the final IVC Keccak proof on-chain in `1,374,697` gas.
The proof repacked from `4,912` compressed bytes to `7,392` padded bytes, with
`7,972` bytes of calldata.

## Recorded Legacy Multi-Limb Runtime Hashes

The concrete hashes below are the latest recorded default multi-limb profile
in this repository (recorded 2026-08-13, after the exact precompile gas
bounds, quotient-VM operand clamps (P12), typed errors (P4), BUILD_ID (P10),
and the alpha vk-binding (I-7); the tracked
`target/ivc-keccak-solidity-dump/` sources match this run). They were
generated with the fixed default quotient codegen shape:

```bash
scripts/run_ivc_bench.sh \
  --skip-srs-download
```

That command uses:

- features:
  `evm,truncated-challenges,in-circuit-fewer-point-sets,solidity-gas-checkpoints`
- `SRS_DIR=./.srs` via the bench script default
- `solc optimize runs: 1`
- CBOR metadata omitted

Published deployed-runtime hashes:

| Artifact | Runtime bytes | Runtime `keccak256` |
| --- | ---: | --- |
| `Halo2Verifier` | 12,637 | `0x6df65ec939553efef2dadffdab078bfb424d10307a32dddd84866cf94d29b215` |
| `Halo2VerifyingKey` | 17,025 | `0x67bac137fa7e479c25b63324812752e4b6e13d9841d5bf83c322170bf91c0f88` |
| `Halo2QuotientEvaluator` | 9,790 | `0x7e72c7c5d6fe845370d9431aaa590ab2cd62ca703c3d5b2a862bdb9937195814` |

Total deployed runtime bytes: `39,452`.

The same run accepted the final IVC Keccak proof on-chain in `1,365,883` gas
(gas-checkpoint diagnostic profile). The proof repacked from `5,056`
compressed bytes to `7,776` padded bytes, with `8,356` bytes of calldata.

Measured cost of the P12 runtime operand clamps: the quotient-VM section
("batched identity numerator reconstruction") went from `314,530` to
`374,481` gas (+59,951, +19.1% of that section, ~+4.6% of the transaction);
every other section is unchanged (PCS block 5 stays at `533,488`).

Previous recordings, for comparison: 2026-08-13 pre-hardening — verifier
12,454 / VK 17,025 / evaluator 9,552 bytes (39,031 total), accepted in
`1,306,084` gas; 2026-07-era artifact set — verifier 12,061 / VK 14,016 /
evaluator 23,221 bytes (49,298 total), accepted in `1,399,268` gas.

Compared with this multi-limb profile, outer single-H removes three quotient G1
commitments: proof size drops by `144` compressed bytes and `384` padded bytes,
PCS block 5 drops from `533,202` to `515,290` gas, and total transaction gas
drops by `24,571`.

# BASELINE (DRAFT - Phase 0 not yet frozen)

Written on the `formal/baseline` branch. This file is finalized at the
`formal-baseline-v1` tag (Phase 0 step 8). Until then the misc-fixes
re-application (Phase 0 step 5) is outstanding; see the status table below.

## Rust baseline commits

| step | ref | commit |
|---|---|---|
| start | main | `2d52f24426ceafed7c663b3ef6372d38a0128fec` |
| merge | origin/quotient-vm-bounds (1b30071, contains 6b3d209) | conflict-free |
| merge | origin/quotient-vm-listing (f1ceae6) | conflict-free |
| merge | origin/quotient-hybrid (d5a7e30) | 8 conflicted files, resolved |
| pending | misc-fixes (4f03428) re-applied as curated commits | not started |

### How the quotient-hybrid conflicts were resolved

Per the plan: keep both sides' meaning.

* `QuotientLowering::{Vm, Direct}` kept, `Vm` the default.
* QVM-01 operand validation (bounds) and the VM runtime guards kept; they now
  read the VM plan through `LoweringPlan::vm_quotient()\
  (hybrid made `LoweringPlan.quotient` an `Option` because the direct
  lowering has no VM program) and `sorted_simple` moved to the top-level plan.
* The listing manifest and disasm are kept and are VM-only. A direct-lowering
  render now emits an `uncertified` listing plus its own identity manifest
  entries (`quotient_listing::VerifierBuildInputs::uncertified_direct_listing\)
  instead of panicking on the absent VM program.
* `diagnostics::quotient_identity_manifest` keeps hybrid's `*_for_meta`
  refactor, which is the version that works for both lowerings; the
  certificate-based view stays available as `quotient_certificate`.
* The transcript buffer sizing and const-table fix (6b3d209) is an ancestor of
  all three branches, so it survives on both paths by construction.
* `tests/common/mod.rs` (add/add) keeps both helper sets:
  `check_quotient_listing` (listing branch) and `direct_trace` +
  `quotient_probe` (hybrid).

## Toolchain and build profile

| item | value |
|---|---|
| rust | `1.90.0` (rust-toolchain.toml channel) |
| solc | `0.8.30+commit.73712a01` (pinned; installed by `scripts/install_pinned_solc.sh` to `proofs/solidity-verifier/.solc/solc`, selected with `SOLC=`) |
| revm | `19`, `default-features = false, features = [std, blst]` (Prague handler: EIP-2537 G1ADD 0x0b, G1MSM 0x0c, PAIRING 0x0f) |
| SRS assets | `zk_stdlib/examples/assets/{bls_filecoin_2p19, midnight-srs-2p19, midnight-srs-2p20}` |
| test gates | `HALO2_SOLIDITY_RUN_EVM_TESTS=1`, `SRS_DIR`, `SOLC` |
| overflow-checks / debug-assertions | to be recorded from the release profile at freeze |

## G0 status

| gate | command | result |
|---|---|---|
| proofs suite | `cargo test -p midnight-proofs` | PASS: 32 lib + 1 integration + 8 doc-tests, 0 failures |
| verifier suite (all features) | `cargo test -p halo2_solidity_verifier --all-features --all-targets` | PASS: 230 lib + all fixture binaries, 0 failures |
| verifier suite, EVM gate on | `cargo test --release -p halo2_solidity_verifier --features evm,rust-verifier-trace --all-targets` with `HALO2_SOLIDITY_RUN_EVM_TESTS=1` | PASS: 230 lib tests (34s) + ivc / poseidon / rsa / sha / hybrid-mt / foreign-field fixtures, 0 failures |
| both quotient lowerings | `foreign_field_renders_and_verifies_in_both_lowerings`, `supported_shape_circuit_fuzz_e2e_direct_quotient`, `direct_trace_matches_native_including_intermediates` | PASS |
| Moonlight wrap end to end | `cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs --release -- --ignored` | PASS (210s) -- CAVEAT: Moonlight pins midfall at `2d52f24` via git deps, so this ran the pre-merge verifier; re-run with a path patch onto `formal/baseline` before the freeze. The `MOONLIGHT_WRAP_SOLIDITY_DUMP_DIR` render did not produce a dump and needs a look. |
| misc-fixes re-application | Phase 0 step 5 | NOT STARTED |
| fixture / gas-snapshot regeneration review | Phase 0 step 6 | NOT STARTED |
| tag + this file finalized | Phase 0 step 8 | NOT STARTED |

## Fixture SHA-256s

(filled in at the freeze)

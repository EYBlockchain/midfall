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

## Phase 0 step 5: misc-fixes curation status

misc-fixes (4f03428) is NOT merged (it is stale and lacks id_point_fix and
affa8a6). Its changes are re-applied as curated commits, each with its tests.

| # | item | source commit(s) | status |
|---|---|---|---|
| 1 | typed errors + MemoryLayoutViolated guard | 86b262e, 580a912 (MF-2, MF-4) | DONE (16333b9). MF-3 was already in the baseline via quotient-vm-bounds. The two MemoryLayoutViolated guard sites were deferred to item 2, where they become true, and landed there. |
| 2 | memory above solc's via-IR spill window | 6333673, 60f842b | DONE (2058d8e). LOW_MEMORY_SCRATCH_START 0x80 -> 0x1000, accumulator batch frame moved with it, compiled_memoryguard_does_not_overlap_generated_layout gate added. Three tests from those commits that depend on later findings were left out. |
| 3 | Lagrange scratch owned by the planner | 6753679 | DONE (960f51c), hand-ported: the two lineages had grown the memory planner apart (441 diff lines in layout/memory.rs), so the patch conflicted in 11 hunks and the *substance* was re-implemented instead - a lagrange_denoms phase-scratch region from the same allocator as batch_invert_scratch, LAGRANGE_DENOMS_MPTR rendered into the constants, Lagrange.yul rebased onto it, and the commit's 4 tests ported. The deletions that commit also made (capacity check, LAGRANGE_RUN_CAP_WORDS, TooManyInstances) were never in this lineage, so they do not apply. |
| 4 | exact precompile gas + SRS tau binding | f1840bd | BLOCKED ON 9, probed and reverted (not attempted half-way). 6 of 13 files conflicted; the cleanly-applied test hunk calls vm::certify::derive_certify_seed, which only arrives with item 9, and the H-1 tau-binding hunk needs a g_lagrange binding that does not exist in this lineage's vk.rs. Plan: land item 9 first, then split item 4 into (4a) the gas model and (4b) the tau binding. |
| 5 | EIP-7883 modexp | 8e65c96 | TODO - touches tests/template_digest.rs, which does not exist here yet (item 10) |
| 6 | PrecompileSmoke | 896fd04 (+460a666) | TODO |
| 7 | reject non-canonical scalars / off-curve points | b4319da, aa62d19, d870dd1, b24be9e, 68adb90 | TODO - partially present already from main (the every_proof_* rejection tests pass on the baseline) |
| 8 | vk_digest in the alpha preimage | 86b262e (FinalPairing.yul part) | TODO - needs pairing_batch_vk_digest_offset and PAIRING_BATCH_HASH_BYTES 0x220 -> 0x240 |
| 9 | vm/certify.rs, vm/reference.rs | 0b27485, 0cd1bdb | TODO |
| 10 | BUILD_ID and template digest | ed9f455 | TODO - adds tests/template_digest.rs |

Skipped per the plan: a01b1ea (duplicate of 6b3d209) and _to_delete/.

Each curated commit was verified with: cargo test -p halo2_solidity_verifier
--features evm,rust-verifier-trace --all-targets under HALO2_SOLIDITY_RUN_EVM_TESTS=1,
pinned solc 0.8.30 and the real SRS, plus cargo fmt --check and clippy.

## Features.solidity (plan rule R8)

Recorded production profile from docs/reference/REPRODUCIBLE_BUILDS.md and
scripts/run_ivc_bench.sh:225-243: evm,truncated-challenges,in-circuit-fewer-point-sets
(the Moonlight Sepolia artifact was rendered without gas checkpoints). Mapped to
the four flags the verifier branches on:

| flag | value |
|---|---|
| committedInstances | true (always forwarded) |
| truncatedChallenges | true |
| outerFewerPointSets | false |
| outerSingleHCommitment | false |

in-circuit-fewer-point-sets affects the recursive circuits, not the
Solidity-facing layout, so it is not one of the four. The optional
outer-single-h-commitment profile is a different Features value; the
per-deployment statement (plan 9.6) must name which one it pins.
TODO: confirm against the frozen deploy command line at the freeze.

## Milestone status

* **M1 (skeleton + inventory)**: Statements.lean compiles with sorry (2 theorems,
  Section 9.2), ecosystem.md written, CI gates in .github/workflows/formal.yml
  and formal/scripts/checks.sh all pass locally (hash, sorry register with 11
  tracked entries, native_decide confinement, Keccak KATs, #print axioms).
  Sections 9.1 (partly), 9.3-9.6 are still to be added to Statements.lean.
* **M0 (baseline frozen)**: not yet - items 4-10 of step 5 remain, then step 6
  (regenerate fixtures/gas/deployments), step 7 (re-run G0, including the
  Moonlight wrap against the baseline rather than the git-pinned 2d52f24) and
  step 8 (tag + finalize this file).

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
| misc-fixes re-application | Phase 0 step 5 | 2 of 10 curated commits landed; see the item table below |
| fixture / gas-snapshot regeneration review | Phase 0 step 6 | NOT STARTED |
| tag + this file finalized | Phase 0 step 8 | NOT STARTED |

## Fixture SHA-256s

(filled in at the freeze)

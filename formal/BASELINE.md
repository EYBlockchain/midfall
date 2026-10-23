# BASELINE (DRAFT - Phase 0 step 5 complete)

Written on the `formal/baseline` branch. This file is finalized at the
`formal-baseline-v1` tag (Phase 0 step 8). Until then the misc-fixes
re-application (Phase 0 step 5) is COMPLETE; steps 6-8 remain. See the status
tables below.
## Rust baseline commits

| step | ref | commit |
|---|---|---|
| start | main | `2d52f24426ceafed7c663b3ef6372d38a0128fec` |
| merge | origin/quotient-vm-bounds (1b30071, contains 6b3d209) | conflict-free |
| merge | origin/quotient-vm-listing (f1ceae6) | conflict-free |
| merge | origin/quotient-hybrid (d5a7e30) | 8 conflicted files, resolved |
| done | misc-fixes (4f03428) re-applied as curated commits | 10/10 items in 12 commits (item 4 split 4a/4b; fc42518 added as a prerequisite, sign-off D-P5) |

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
| 4a | exact precompile gas bounds | f1840bd (M-2/P1 half) | DONE (e0e77f0), after item 9 as planned. layout::gas model, G1ADD_GAS / G1MSM_GAS_1PAIR / G1MSM_GAS_SMOKE / PAIRING_GAS_2PAIR / MODEXP_GAS / ACC_RHS_MSM_GAS rendered as constants and forwarded at every precompile call site (the two pinned quotientEvaluator calls keep gas() deliberately: a contract call refunds unused gas). The constructor-probe needle in verifier_constructor_rejects_... had to be retargeted at the smoke call. |
| 4b | SRS tau binding (H-1) | f1840bd (H-1 half) | DONE (4ec6baa) after the fc42518 prerequisite (54b82ba) approved as D-P5. srs_tau_is_consistent reconstructs [tau]G1 by Pippenger MSM over the Lagrange basis and asserts e([tau]G1,G2) == e(G1,s_g2); the real midnight-srs-2p19/2p20 assets pass. |
| 5 | EIP-7883 modexp | 8e65c96 | DONE (d61a99a). Applied cleanly once 4a/6 had landed (the earlier probe overstated the conflicts). MODEXP_GAS is now the max over both live schedules and the constructor probes 0x05. Fixture-README hunks skipped (those dirs do not exist here). |
| 6 | PrecompileSmoke | 896fd04 (+460a666) | DONE (93e7004). Five known-answer probes (G1ADD double, G1MSM double, G1MSM subgroup rejection, pairing accept, pairing reject-constant-1), pragma pinned to 0.8.30 in all three contracts, stale 0x80 NatSpec corrected. Its P2 bare-revert guards were superseded by the typed MF-2 form; the four new probes had to be bound to the scheduled gas constants so the item-4a pinning test still holds. |
| 7 | reject non-canonical scalars / off-curve points | b4319da, b24be9e, aa62d19, d870dd1, 68adb90 | DONE (13ef643). All five applied near-cleanly; the only conflict was scalar_inv, where this lineage already had the canonical-range check. The batch_invert harness needed adapting to MF-4's second return value and the gas model. |
| 8 | vk_digest in the alpha preimage | 86b262e (audit I-7 half) | DONE (192f136). Offsets shift a word, PAIRING_BATCH_HASH_BYTES 0x220 -> 0x240, scratch start derived from the frame end. Its P12/L-6 operand-clamp half was NOT taken: QVM-01 is the stronger version of the same idea in this lineage. |
| 9 | vm/certify.rs, vm/reference.rs | 0b27485, 0cd1bdb | DONE (decaf9f), pulled ahead of items 4 and 5 because they depend on it. reference.rs is the Rust reference interpreter the plan's QVM.run statement ports, so it feeds M6 directly. |
| 10 | BUILD_ID and template digest | ed9f455 | DONE (5312cb7). bytes32 BUILD_ID per artifact over feature profile + vk_digest + VK codehash + SRS fingerprint + optional provenance tag; build.rs exports the feature profile; tests/template_digest.rs pins a keccak of the templates/ tree (feature-ungated). Fixture dumps regenerated and the digest re-pinned as that gate demands. |

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
* **Phase 0 step 5: COMPLETE.** All ten curated items landed. Item 4 was split
  into 4a (gas model) and 4b (SRS tau binding), and one unlisted prerequisite
  (fc42518, SRS G1-base validation) was added with sign-off as D-P5 because both
  4b and 10 need g_lagrange in scope in generate_base_vk. Order actually taken:
  1, 2, 3, 9, 4a, 7, 8, 6, 5, fc42518, 4b, 10 - reordered where the dependency
  graph demanded it (the plan's numeric order put vm/certify after the items
  that call it). Lib tests went 230 -> 248 across the curation, all green under
  the EVM gate with pinned solc 0.8.30 and real SRS assets.
* **M0 (baseline frozen)**: still to do - step 6 (regenerate the committed
  fixtures, gas snapshots and deployments/sepolia/moonlight-wrap and review the
  diffs; the four tracked target/*-fixture-dump files were already regenerated
  by the test runs and the template-tree digest re-pinned for them), step 7
  (re-run G0 end to end, including the Moonlight wrap against THIS baseline
  rather than the git-pinned 2d52f24), step 8 (record fixture SHA-256s and the
  build profile here, then tag formal-baseline-v1).

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
| misc-fixes re-application | Phase 0 step 5 | COMPLETE: 10/10 curated items landed |
| fixture / gas-snapshot regeneration review | Phase 0 step 6 | NOT STARTED |
| tag + this file finalized | Phase 0 step 8 | NOT STARTED |

## Fixture SHA-256s

(filled in at the freeze)

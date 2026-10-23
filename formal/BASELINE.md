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

* **M1 (skeleton + inventory)**: DONE. Statements.lean compiles with sorry
  (3 theorems, Sections 9.2 and 9.5-L6), ecosystem.md written, CI gates in
  .github/workflows/formal.yml and formal/scripts/checks.sh all pass locally
  (frozen hash, sorry register, native_decide confinement, Keccak + ABI-selector
  + transcript KATs, #print axioms). Sections 9.1 (partly), 9.3-9.6 are still to
  be added to Statements.lean as the declarations they name come into being.
* **M2 (L0 port)**: IN PROGRESS. Landed so far: Exec/Transcript (the whole
  Keccak transcript: init_from_bytes, common, read, read_n, squeeze with the
  reseed, challenge = BE digest mod r, assert_empty), Exec/Kzg/Params,
  Exec/Kzg/Msm (MSMKZG, msm_specific, DualMSM and DualMSM.check - so the final
  pairing equation is now a definition, not a placeholder), Exec/Query
  (CommitmentLabel), Exec/Arith and Exec/Domain, plus the byte and point codecs
  in Common/{Bytes,Codec}. Still to port: Exec/Poly, Exec/Pcs, Exec/Verifier,
  Exec/Permutation, Exec/Logup, Exec/Trash, Exec/Linearization, Exec/Kzg/Utils,
  Exec/Kzg/MultiOpen, Exec/Native (prepare, decodeRust, prepareMsgs,
  verifyMsgs), Exec/Accumulator and Exec/Msgs. Sorry register: 12 entries, all
  in Native/Spec/Statements.
* **Plan location**: the normative plan is now in the repository as
  docs/PLAN.md, so a work package or review can cite it by section number.
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
| cargo profiles | no [profile.dev]/[profile.release]/[profile.test] overrides anywhere, so cargo defaults apply: dev/test have debug-assertions ON and overflow-checks ON; release has both OFF |
| **reference profile for the port** | **release** - it is what produces the deployed artifacts and what the heavy fixture benches run under. Consequences for the port rules: R4 arithmetic overflow is NOT a panic site in the reference profile, so R5 applies (emulate wrapping only where it can actually occur, prove noOverflow elsewhere), and debug_assert! is compiled out |
| secondary profile exercised | debug (cargo test default) - the 248-test lib suite runs here, so the checked path is exercised too; any Lean def whose behaviour differs between the two must say so in its R1 comment |

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

## Phase 0 steps 6 and 7 status

| item | command | result |
|---|---|---|
| regenerate tracked dumps | the fixture tests write target/*-fixture-dump/ | DONE. Four dumps regenerated with the curated items (commit 33a3b20 area), reviewed hunk by hunk: every change traces to a curated item (pinned pragma, typed taxonomy, scheduled gas, vk_digest in alpha, BUILD_ID, lagrange denominator region). |
| regenerate the IVC bench dump | HALO2_SOLIDITY_RUN_IVC_BENCH=1 cargo test --release --features evm,truncated-challenges,in-circuit-fewer-point-sets,rust-verifier-trace --test ivc_keccak_solidity | DONE. Two runs. (a) With rust-verifier-trace (602 s): 244 shared trace ids + 227 direct intermediates compared, 0 mismatches; quotient probe differential over 10 frames x BOTH lowerings matched the Rust reference (m = 49 identities, 29 re-evaluated via Expression::evaluate). (b) Without trace/checkpoint instrumentation, i.e. the production render: **Vm lowering 1,284,605 gas**, **direct lowering 1,058,322 gas**. The trace render costs 2,286,614 - the extra ~1.0M is the per-value LOGs, so it is NOT comparable to the recorded figures. Pre-curation recorded figures were 1,374,697 (outer-single-H) and 1,399,268 (legacy multi-limb), so the curated baseline is ~115k gas cheaper on the same shape. Gas is out of scope for the proofs (plan Section 1); recorded only as drift evidence. |
| gas snapshots | - | N/A on this lineage: no gas-snapshot files are tracked; gas numbers live as prose in docs/reference/REPRODUCIBLE_BUILDS.md and docs/benchmarks/BENCH.md, and the plan lists exact gas as out of scope. The template-tree digest is the drift gate that stands in for them. |
| regenerate deployments/sepolia/moonlight-wrap | scripts/prove_and_verify_moonlight_sepolia.sh | **BLOCKED, environment, not code.** Two independent blockers: (a) the local ../Moonlight checkout (fbd0f4f) has no MOONLIGHT_WRAP_SOLIDITY_* hooks, so it cannot emit the wrap verifier sources the midfall README documents; (b) the committed artifacts are fetched-back Sepolia runtime bytecode, so refreshing them needs a funded deployment. Consequence to accept explicitly: the plan's M3 golden test ("byte-identical to the deployed Moonlight artifacts") would compare against artifacts rendered by the PRE-curated generator. Either a compatible Moonlight checkout is pinned before M3, or the Moonlight comparison must be restated against a dump regenerated from this baseline. Flagged for sign-off. |
| Moonlight wrap end to end | cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs --release -- --ignored | PASS (210 s) in round 1, but against the git-pinned 2d52f24. Re-running against THIS baseline needs a path patch of Moonlight's five midfall git deps; the wrap test itself does not depend on halo2_solidity_verifier, so this validates the proof pipeline, not the generator. |
| cargo test -p midnight-proofs | default features | PASS (round 1: 32 lib + 1 integration + 8 doc tests). proofs/ is untouched by the curated items. |
| cargo test -p halo2_solidity_verifier feature matrix | --all-features --all-targets, and evm,rust-verifier-trace with the EVM gate | PASS: 248 lib tests + 11 test binaries, fmt and clippy clean. |

## Fixture SHA-256s

Generated with shasum -a 256 over the tracked fixture inputs and the tracked
regenerated dumps on this branch (commit 33a3b20).

| sha256 | path |
|---|---|
| f86e8f03ce02214a7747729cf3c075d221eff2c3e51c78f8dea7e3a0da844ca4 | fixtures/ivc/instance.bin |
| 055bbfd22468b1d9803371cc765b664e359ec61d7be5537fcdfe69635adb7be2 | fixtures/ivc/proof.bin |
| 7945056172df44c07be8aa39b2f50594597d12076ae598b47ad03173479a7def | fixtures/ivc/rust_trace.json |
| 2c714487a2831d2380aa45bbca3883451b1676d50d0f02fb175eee8f33dd0a01 | fixtures/ivc/solidity_trace.json |
| 6126880f264a05da16fefa18a69ff26f7be3a30c1bd5bf66d543493ea3a16508 | fixtures/ivc/vk.bin |
| 112063ccc09c75d07e1945b932617422d936e63e4523a3b8266e2679f6ca1505 | fixtures/poseidon/adversarial_fixtures.bin |
| a8280b1280b61a78a3f33f67062601f7733441a76d1b25f4b99c34fdf8e54737 | fixtures/poseidon/algebra_fixtures.bin |
| b6e9250a6834e1d4146797ea858a3302eb3174a1276d804aac482cd272d8cdc0 | fixtures/poseidon/decomp_pairs.bin |
| 2c33c99e8faaa6d2308fc369a68faa71efae107458359eb1921ddf1b83fbd924 | fixtures/poseidon/evals_signature_fixture.bin |
| 376b300edd8afe5bb6b468f864aadf7dc7e88526593cbb884ef4b78eb751f83e | fixtures/poseidon/gate_eval_fixture.bin |
| 5f0657f37554c781402a22917dee2f75def7ab966d7b770905398eba3c444014 | fixtures/poseidon/identity_g1_compressed.bin |
| 2aa07bf0b2683897898562308b7f44414a8d7fd434b5f666e701a79bfc60b304 | fixtures/poseidon/instance.be |
| b8bc913b6eab153c2fa6c53563f9bdc9872e6e7b5961d897cddc376829083696 | fixtures/poseidon/lagrange_aux_fixture.bin |
| 52deadb1eaa1016ec01ce727997da01a3bc6c2cb51a50007bdcd726acd7de548 | fixtures/poseidon/pairing_fixture.bin |
| 818a766a5d59e1e72d16b290793f87175ef6aebc6a5500329710678024777cc6 | fixtures/poseidon/proof.bin |
| a2a80f8f637d90cd2062f299e4dd873756faea71795e872bef6376cce22fb0b6 | fixtures/poseidon/query_schedule_fixture.bin |
| 7b5d2859147c2ddc7a484f6fdd07684bc9877d1111a79eb6fe0cf2dcc64f9cd1 | fixtures/poseidon/right_g1_fixture.bin |
| 9cdf71381122c880caa6b182c4d0c3ae681cb02c54b8c0390ca2cc4cd647e171 | fixtures/poseidon/right_msm_inputs_digest_fixture.bin |
| 27cc2b0bc74b60004e7fbb46808055c1f848da73f6111a2e68e75bfc69ff3077 | fixtures/poseidon/right_msm_terms_fixture.bin |
| 3546b5d001a62cd9e1e48382464b5b9f8c23c8bc051bff50cf26dbd8564fb5ec | fixtures/poseidon/rust_trace.json |
| 040a48e7ef77bf01e88c5edaeac19193705a38d3e15415b2a0f9cd2588e9e5bb | fixtures/poseidon/solidity_trace.json |
| ddec2344a12eafad9ee15bd6f7982163bbb8b886087c7fec4ae27006532e8bf3 | fixtures/poseidon/verifier_trace.bin |
| 31f55168f1ecafade297ecccfee38db1ba45b4b7f149aaedf3c842f4f2d188d9 | fixtures/poseidon/vk.bin |
| 52bfc1b1a7b053d8b63916c81ab6e845125cae277b74ddaa5ae7b6d0c5a62e45 | fixtures/rsa_signature/instance.bin |
| b5212b21b686686749699702ba696f41a800f43ff7c83289a47ab01bd8dc8a6a | fixtures/rsa_signature/proof.bin |
| 94ff3fbf1934e6c72360307b7dfc38ebb7e41fcfe28ff97fab9c5cf10850ba20 | fixtures/rsa_signature/vk.bin |
| 36b2547aeb19919944ddce0c1ed4c1b706505cc07f4ea915b412dcbdfb647952 | target/hybrid-mt-fixture-dump/Halo2Verifier.direct.sol |
| db5a581f2b081afb08470dbc65e12eaff8eb43e2aebffbea59310de12d53b4e1 | target/hybrid-mt-fixture-dump/Halo2Verifier.sol |
| 2efd93795dc725f4aeb2b5b8a930c7ca976034eff47858e922170af109530675 | target/hybrid-mt-fixture-dump/Halo2VerifyingKey.direct.sol |
| a7307f9a890b903af2b504817792921573a880c1d66fca0755e3a6e220464091 | target/hybrid-mt-fixture-dump/Halo2VerifyingKey.sol |
| bf60d852d691a69edcdb1b1a6594bf2a266cf6bd33f0beb55ab3ec1442e479f4 | target/hybrid-mt-fixture-dump/calldata.bin |
| b4cc25f849f2cd6cfccf9f48c2e6772acdfb0065b89f7a10cf9263aa0a5e0f62 | target/hybrid-mt-fixture-dump/instances.be |
| 5038318eea2b89bf6057b9d67e77b535951ae3d3f80c82e5a665eb3ca65e34d6 | target/hybrid-mt-fixture-dump/proof.bin |
| 650286cab970e06e5b89693c3c15465a5a3945417babd3ae9652b18e062d5edc | target/ivc-keccak-solidity-dump/Halo2QuotientEvaluator.creation.bin |
| 27a60d2922cfcf1dca6fae553f52586229aa6b6058533b6c963a5d754ed22c3f | target/ivc-keccak-solidity-dump/Halo2QuotientEvaluator.sol |
| 9eb2ebf20b84109db5f91b653b267d9e4e0a12bb07964753ca85979502a8ea10 | target/ivc-keccak-solidity-dump/Halo2Verifier.creation.bin |
| a4746bf835275231564b6321211c753edb314fd1480cd772937ef68debcdaa74 | target/ivc-keccak-solidity-dump/Halo2Verifier.direct.sol |
| c4a04c1b8825ba9bc5804df204a4d345a5d3a078c08ea23584485be6c8e0edbd | target/ivc-keccak-solidity-dump/Halo2Verifier.sol |
| c84a2e752e034333e8ca3ff739c3f780a3370badd0ca503742078327c0f6a232 | target/ivc-keccak-solidity-dump/Halo2VerifyingKey.creation.bin |
| b9b2402aa4944dc7ab2a3543fd0a1c015d9004bfafb5f31a395528ca8d66da76 | target/ivc-keccak-solidity-dump/Halo2VerifyingKey.direct.sol |
| f758587480759d1fc694da6e4d1d6d52352a8d3e530e053feed73c078e2934a2 | target/ivc-keccak-solidity-dump/Halo2VerifyingKey.sol |
| d4bfd29110a4bbfc8b4c11c04afd24cf79e79fa7b00999051d0aa1dc1a4e0bf8 | target/ivc-keccak-solidity-dump/calldata.bin |
| fd83143d2116573b575741f48b2625627843440ba229bf78fdfe602fbddafaae | target/ivc-keccak-solidity-dump/contract-sizes.txt |
| fef09061a36968b52479eb88f67f1e2aa3644392955f8bc2410de27639bf3688 | target/ivc-keccak-solidity-dump/instance.le |
| bb819789684b0054514e6dc1d1fe6953d12c79ec59ad4077c5e3d1d3146ca1ac | target/ivc-keccak-solidity-dump/proof-evaluation-counts.txt |
| 6e5c780561a5323b0d93a5f7b632b12755ff2158813abc3c62c1c4366090d03c | target/ivc-keccak-solidity-dump/proof.bin |
| b3917f0fd49f138a9d7a9ea63ce00852aea64d175b530a6ebbe12372bfaf9257 | target/poseidon-fixture-dump/Halo2Verifier.direct.sol |
| 0ebebe97beaf2e105faa5be2356de2adf8ed8643c98180603a38215d8215f050 | target/poseidon-fixture-dump/Halo2Verifier.sol |
| 745779220e757f0d1e5cee903598fa3abbcb0d3c217efd3a5f8fd8929181a48a | target/poseidon-fixture-dump/Halo2VerifyingKey.direct.sol |
| e4a7d45cd2526ad3efa38cc19cfa7b88d505e060f1feac0db48082fb61f0ce55 | target/poseidon-fixture-dump/Halo2VerifyingKey.sol |
| 6af78ce3e2fcbe7d363a3999e5714869336eb8ec54210ff4f5013eff5b734ecf | target/poseidon-fixture-dump/calldata.bin |
| 276b414838d9478519646bd0e8036a00c67994d73f370f00cd5c58ba8cafa0cd | target/poseidon-fixture-dump/instance.be |
| 2f7ddc435479950f2f49a024dbc62b154664095cfae86291b07f39c3b6e2c3e0 | target/poseidon-fixture-dump/proof.bin |
| cde1a54117f54903b54aa9d51df769f527135f7cb7ec8c7d9a86a298888bd476 | target/rsa-signature-fixture-dump/Halo2Verifier.direct.sol |
| 3d1f037f725ee2f149cf472889b3ef9330d3ffdab82a999c13d1fe1b54517429 | target/rsa-signature-fixture-dump/Halo2Verifier.sol |
| a51b5d176be3d63d25525a92c59442199a196362c3952fea766fc10c4c51fe10 | target/rsa-signature-fixture-dump/Halo2VerifyingKey.direct.sol |
| 1261c6b1f695a136c70fe6800d59f2823c75d76c60af8df92f1206bfe11f3236 | target/rsa-signature-fixture-dump/Halo2VerifyingKey.sol |
| 69513007bb8eb73d126322a8e737cf03c10704a5ac03b895a08180a92aa00145 | target/rsa-signature-fixture-dump/calldata.bin |
| f8cdb21c1143e137aee4f6c4c9cdd274990c66e2160f92c027be88c2024e171f | target/rsa-signature-fixture-dump/instances.be |
| 47050f4f2cb8657df0950ee4994c967d8ac3abcff4beb8e68953dae35f587973 | target/rsa-signature-fixture-dump/proof.bin |
| 25810bc294f466828e925b6028aca076bcc9e6720d93d327062c43bfd8b95576 | target/sha-preimage-fixture-dump/Halo2Verifier.direct.sol |
| d6c6331f2672ec242890232d9e7537eed43c832f33406cbe4328bacd2c4ac6cf | target/sha-preimage-fixture-dump/Halo2Verifier.sol |
| cea0e0caee99fe979bab45593112e7d41f96c3a6de66b71c90b06c8d7e7c6304 | target/sha-preimage-fixture-dump/Halo2VerifyingKey.direct.sol |
| 1a99f410c6b8f536c480d4d90b105e2189ef4cdef0235653963e4afe9127d596 | target/sha-preimage-fixture-dump/Halo2VerifyingKey.sol |
| fe1ebeb5aa810cd0dbf44d2774c5764c25b0fcbbdffef08115656cbe65c80c78 | target/sha-preimage-fixture-dump/calldata.bin |
| cf9ea60bfee9769886ff15d846388a42bd8682a206c4119298c649a3f4636a92 | target/sha-preimage-fixture-dump/instances.be |
| 4823c266d0ed0037dba49d37bc3648968b1f434f14e378a041aefddce6d25be2 | target/sha-preimage-fixture-dump/proof.bin |

Total tracked fixture/dump files: 67.



(filled in at the freeze)

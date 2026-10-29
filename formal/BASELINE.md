# BASELINE (Phase 0 steps 5-8 complete - ready for `formal-baseline-v1`)

Written on the `formal/baseline` branch. The misc-fixes re-application
(step 5), the fixture regeneration and re-pinning (step 6), the G0 re-run
(step 7) and this finalisation (step 8) are all COMPLETE. The tag itself is
cut by the orchestrator, not by a work package. See the status tables below.
D-P28 / R-57 is the poseidon-fixture regeneration; its record is the section
"Poseidon fixture regeneration (D-P28)" further down.
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

**Resolved at the freeze (D-P28).** The four flags above are the profile the
committed poseidon fixture is rendered under, and R-57's shape arithmetic ties
`outerFewerPointSets = false` to the 2,640-byte / 72-read proof, which is what
the current tree actually produces. The cargo feature string that realises this
profile for the fixture generator is `evm,rust-verifier-trace`
(`rust-verifier-trace` implies `truncated-challenges` and
`midnight-proofs/solidity-verifier-trace`); `outer-fewer-point-sets` and
`outer-single-h-commitment` are NOT passed. The deploy command line still has
to be confirmed against a real deployment when plan 9.6 is signed off - that is
an M-item, not a Phase 0 blocker.

## Milestone status

* **M1 (skeleton + inventory)**: DONE. Statements.lean compiles with sorry
  (3 theorems, Sections 9.2 and 9.5-L6), ecosystem.md written, CI gates in
  .github/workflows/formal.yml and formal/scripts/checks.sh all pass locally
  (frozen hash, sorry register, native_decide confinement, Keccak + ABI-selector
  + transcript KATs, #print axioms). Sections 9.1 (partly), 9.3-9.6 are still to
  be added to Statements.lean as the declarations they name come into being.
* **M2 (L0 port)**: IN PROGRESS, most leaves done. Landed: Exec/Transcript (the
  whole Keccak transcript), Exec/Kzg/{Params,Msm,Utils,MultiOpen} (MSMKZG,
  msm_specific, msmInnerProduct, DualMSM, DualMSM.check,
  construct_intermediate_sets, compute_dummy_queries and the whole
  multi_prepare), Exec/Query (CommitmentLabel, CommitmentReference,
  VerifierQuery), Exec/Pcs (the R9 Pcs and Guard records), Exec/Arith,
  Exec/Domain, Exec/Circuit (2171 lines: all 20 ConstraintSystem fields,
  Expression.degree and evaluate with the caller-side callbacks, degree,
  blinding_factors, the selector-conversion path), Exec/Poly (whose finding is
  that poly/mod.rs is prover code, so Polynomial is NOT part of L0), and
  Exec/{Permutation,Logup,Trash} verifier paths (read_product_commitments, the
  three evaluate/queries triples, and the permutation/logUp/trash identity
  expressions - i.e. everything Exec/Verifier needs except the linearization).
  Plus Assumptions/Pairing (the named BLS12-381 hypothesis, no sorry) and the
  byte and point codecs in Common/{Bytes,Codec}. Still to port:
  Exec/Verifier, Exec/Native (prepare,
  decodeRust, prepareMsgs, verifyMsgs), Exec/Accumulator and Exec/Msgs.
  Sorry register: 12 entries, all in Native/Spec/Statements.
  Reviews and cross-module findings R-1..R-17: docs/REVIEW.md. Two need a
  decision from you: R-8 (does Fault gain a poly variant - candidate D-P8) and
  the M0 freeze. One blocks M4: Y-3 in docs/ecosystem.md section 10 -
  RunCommitted is fixed to the closed EVM.evm dialect, so RunVerifier and
  RunContractIR as written do not typecheck.
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
* **M0 (baseline frozen)**: **DONE for steps 6-8 on 2026-10-29**, with two
  accepted exceptions. Step 6: the six live poseidon artefacts were regenerated
  under the recorded profile, verified to pass the real verifier, and re-pinned
  here; the twelve unread poseidon files were deleted (D-P28, R-57). Step 7: G0
  re-run end to end - results in the G0 table below, including the finding that
  the `--all-features` leg cannot pass on this host. Step 8: this file is
  finalised; the tag is cut by the orchestrator. Two exceptions carried into
  the tag, both environment rather than code: `deployments/sepolia/moonlight-wrap`
  cannot be refreshed here (no `MOONLIGHT_WRAP_SOLIDITY_*` hooks in the local
  Moonlight checkout, and the committed artefacts are fetched-back Sepolia
  runtime bytecode), and the `--all-features` matrix leg needs larger Filecoin
  SRS assets than this host holds.

## Toolchain and build profile

| item | value |
|---|---|
| rust | `1.90.0` (rust-toolchain.toml channel) |
| solc | `0.8.30+commit.73712a01` (pinned; installed by `scripts/install_pinned_solc.sh` to `proofs/solidity-verifier/.solc/solc`, selected with `SOLC=`) |
| revm | `19`, `default-features = false, features = [std, blst]` (Prague handler: EIP-2537 G1ADD 0x0b, G1MSM 0x0c, PAIRING 0x0f) |
| SRS assets | `zk_stdlib/examples/assets/{bls_filecoin_2p19, midnight-srs-2p19, midnight-srs-2p20}`; the poseidon fixture additionally needs `bls_filecoin_2p6`, which `srs_for_test(_, Some(6))` loads for k = 6 (added to this row at the freeze - it was always required and was not recorded) |
| test gates | `HALO2_SOLIDITY_RUN_EVM_TESTS=1`, `SRS_DIR`, `SOLC` |
| cargo profiles | no [profile.dev]/[profile.release]/[profile.test] overrides anywhere, so cargo defaults apply: dev/test have debug-assertions ON and overflow-checks ON; release has both OFF |
| **reference profile for the port** | **release** - it is what produces the deployed artifacts and what the heavy fixture benches run under. Consequences for the port rules: R4 arithmetic overflow is NOT a panic site in the reference profile, so R5 applies (emulate wrapping only where it can actually occur, prove noOverflow elsewhere), and debug_assert! is compiled out |
| secondary profile exercised | debug (cargo test default) - the 248-test lib suite runs here, so the checked path is exercised too; any Lean def whose behaviour differs between the two must say so in its R1 comment |

### solc 0.8.30: measured behaviour of the pinned compiler (round 9)

The pinned compiler is present and verified: `proofs/solidity-verifier/.solc/solc`,
sha256 `738dcdc6afddeb505ee4e4ef24f1c1fdba2b8c924e614cbbf5801a5b062dd683`, byte-identical
to the official `solc-macosx-amd64-v0.8.30+commit.73712a01`, produced by the committed
`proofs/solidity-verifier/scripts/install_pinned_solc.sh`. `solc` on PATH is 0.8.35 and
must not be used: every gate names the pinned path or sets `SOLC=`. This closes the item
recorded at docs/PLAN.md 14.6 as an unresolvable environment blocker - it was resolvable,
and had in fact been resolved on 2026-10-23, three days before it was reported as open.

Measured against `target/poseidon-fixture-dump/Halo2Verifier.sol` (175,918 bytes):

| invocation | result |
|---|---|
| `--bin` (legacy pipeline) | **fails**: `Stack too deep ... Variable r is 3 slot(s) too deep inside the stack` |
| `--via-ir --optimize --bin-runtime` | ok, 26,533 hex chars of runtime code |
| `--via-ir --bin-runtime` (no optimizer) | ok, 52,129 hex chars |
| `--ir` / `--ir-ast-json` | ok, and **identical with and without `--via-ir`** (sha `d899f215d775bdb8` both ways) |
| `--ir-ast-json --optimize` | different (sha `12750f5f54cfd0eb`): the artifact tracks the optimizer setting, not the pipeline |
| `--standard-json` with `viaIR:false` | no `contracts` entry at all - the legacy pipeline cannot build this file |
| `--standard-json` with `viaIR:true`, `ir` | 140,439 chars; differs between `optimizer.enabled` false/true (`e3f04cfc1c05d699` vs `e9465b3433265c3f`) |
| `--standard-json` with `viaIR:true`, `ir-ast-json` | **not produced** - the JSON IR AST is a source-level CLI artifact only |

The consequence for plan Section 7 is recorded as docs/REVIEW.md R-42 and needs a
decision: the JSON AST that `ImportSolcIR.lean` is told to import comes from the legacy
pipeline, which cannot compile the generated contract to bytecode at all. The via-ir IR
exists only as text. Options are in that entry.

## G0 status

| gate | command | result |
|---|---|---|
| proofs suite | `cargo test -p midnight-proofs` | **PASS** (re-measured 2026-10-29): 32 lib + 1 integration + 8 doc-tests, 0 failures |
| verifier suite, default features | `cargo test -p halo2_solidity_verifier` | **PASS**: 203 lib + 4 in the fixture binaries, 0 failures - the standing gate figure |
| verifier suite (all features) | `cargo test -p halo2_solidity_verifier --all-features --all-targets` | **FAIL - 210 passed / 39 failed, environment not code.** Every failure is a proof-generation site in `src/test.rs` dying with `SrsError(32, 62)` / `SrsError(64, 252)`: `--all-features` turns on `outer-single-h-commitment`, and under `single-h-commitment` `load_srs` must also fetch `bls_filecoin_2p{extended_k}` (`zk_stdlib/src/utils/plonk_api.rs:282-288`), which this host does not hold (assets present: 2p6, 2p10, 2p12, 2p13, 2p19). R-57 recorded the same wall ("single-h ... cannot even prove at k=6"). None of these tests read `fixtures/poseidon/`, so the fixture regeneration is not implicated. What it would take: fetch the extended-domain Filecoin assets (`scripts/ensure_srs_assets.sh` only guarantees 2p19) or drop `outer-single-h-commitment` from the matrix and state which profile G0 means. |
| verifier suite, EVM gate on | `cargo test --release -p halo2_solidity_verifier --features evm,rust-verifier-trace --all-targets` with `HALO2_SOLIDITY_RUN_EVM_TESTS=1` | **PASS**: 249 lib tests + ivc / poseidon / rsa / sha / hybrid-mt / foreign-field / conformance-export binaries, 0 failures. This is the profile the regenerated fixture was rendered under. |
| CI matrix: poseidon fixture | `cargo test --release --features evm,truncated-challenges --test poseidon_fixture` | **PASS** |
| CI matrix: native/Solidity trace equivalence | `cargo test --release --features evm,truncated-challenges,rust-verifier-trace,solidity-trace --lib native_midfall_verifier_trace_matches_solidity_trace` | **PASS** |
| CI matrix: real-EVM PBT | `cargo test --release --all-features pbt_` | **FAIL - 8 / 8**, same `SrsError` cause as the all-features row above |
| both quotient lowerings | `foreign_field_renders_and_verifies_in_both_lowerings` (`tests/foreign_field_fixture.rs`), `supported_shape_circuit_fuzz_e2e_direct_quotient`, `direct_trace_matches_native_including_intermediates` | **PASS** under the recorded profile (1 + 1 + 1 tests, 0 failures). Note the third is a lib test and is among the 39 that fail only under `--all-features`. |
| regenerated fixture acceptance | replay of the committed `fixtures/poseidon/proof.bin` through `midnight_zk_stdlib::verify` and through the generated Solidity verifier on both lowerings | **PASS - ACCEPT on all three legs** (native ACCEPT; Vm ACCEPT 638,069 gas; Direct ACCEPT 624,166 gas). The stale fixture it replaced replayed as native REJECT `Error::Opening` and could not even be repacked (`LengthMismatch { expected: 2640, actual: 4752 }`). |
| poseidon regen harness (P-FREEZE) | `HALO2_SOLIDITY_RUN_EVM_TESTS=1 M0_OUT=<dir> cargo test --release -p halo2_solidity_verifier --features evm,rust-verifier-trace --test m0_poseidon_regen` | **PASS, and inert by default.** With `M0_OUT` unset both tests return immediately (2 passed / 0 failed in 0.00 s inside the `--all-targets` EVM gate) and nothing is written. With `M0_OUT` set it re-emits all six artefacts and asserts structure, not bytes: 2,640 B, 21 point + 51 scalar = 72 transcript reads, native ACCEPT, Solidity ACCEPT on Vm (638,117 gas), Direct (624,214) and the traced render (1,233,414). `vk.bin` and `instance.be` come back byte-identical to the committed files; `proof.bin` and the three traces come back structurally identical only. See "Poseidon fixture regeneration". |
| Moonlight wrap end to end | `cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs --release -- --ignored` | **PASS** (176.4 s, 1 passed / 0 failed, exit code 0 taken without a pipe) - CAVEAT unchanged: Moonlight pins midfall at `2d52f24` via git deps, so this exercises the proof pipeline, not this baseline's generator. A path patch onto `formal/baseline` is still owed before M3. |
| Lean build (unchanged by this package) | `cd formal && lake build` | **PASS**: Build completed successfully (5154 jobs), exit 0 - re-run after the fixture replacement and after the G0 dump-dir restore |
| Lean gate suite (unchanged by this package) | `cd formal && bash scripts/checks.sh` | **PASS**, every stage ok: Statements hash OK, 64 tracked sorries all owned, native_decide confined, all 107 modules reachable, 9 golden pins re-derived from the tracked .sol artifacts, **1257 annotated KATs across 83 files**, 111 statement fingerprints, 12 fact families, 23 spec-theorem bundles certified, axioms probe clean |
| misc-fixes re-application | Phase 0 step 5 | COMPLETE: 10/10 curated items landed |
| fixture regeneration and re-pin | Phase 0 step 6 | COMPLETE 2026-10-29 under D-P28 - see "Poseidon fixture regeneration (D-P28)" |
| G0 re-run end to end | Phase 0 step 7 | COMPLETE 2026-10-29, with the two `--all-features` legs red for the SRS-asset reason above |
| tag + this file finalized | Phase 0 step 8 | COMPLETE - this file is final. **Verdict on the tag: safe to cut, with one named exception to accept in the tag message.** Everything defined over the recorded profile is green, including the regenerated fixture acceptance and both Lean gate suites. The exception is that G0 as literally written in PLAN.md 2.7 includes the CI feature matrix, and its two `--all-features` legs are red on this host for a missing-SRS-asset reason that predates and is independent of this package. Either (a) cut the tag and record that exception, or (b) fetch the extended-domain Filecoin assets (or drop `outer-single-h-commitment` from the matrix and re-measure) and cut on a fully green G0. |

## Phase 0 steps 6 and 7 status

| item | command | result |
|---|---|---|
| regenerate tracked dumps | the fixture tests write target/*-fixture-dump/ | DONE. Four dumps regenerated with the curated items (commit 33a3b20 area), reviewed hunk by hunk: every change traces to a curated item (pinned pragma, typed taxonomy, scheduled gas, vk_digest in alpha, BUILD_ID, lagrange denominator region). |
| regenerate the IVC bench dump | HALO2_SOLIDITY_RUN_IVC_BENCH=1 cargo test --release --features evm,truncated-challenges,in-circuit-fewer-point-sets,rust-verifier-trace --test ivc_keccak_solidity | DONE. Two runs. (a) With rust-verifier-trace (602 s): 244 shared trace ids + 227 direct intermediates compared, 0 mismatches; quotient probe differential over 10 frames x BOTH lowerings matched the Rust reference (m = 49 identities, 29 re-evaluated via Expression::evaluate). (b) Without trace/checkpoint instrumentation, i.e. the production render: **Vm lowering 1,284,605 gas**, **direct lowering 1,058,322 gas**. The trace render costs 2,286,614 - the extra ~1.0M is the per-value LOGs, so it is NOT comparable to the recorded figures. Pre-curation recorded figures were 1,374,697 (outer-single-H) and 1,399,268 (legacy multi-limb), so the curated baseline is ~115k gas cheaper on the same shape. Gas is out of scope for the proofs (plan Section 1); recorded only as drift evidence. |
| gas snapshots | - | N/A on this lineage: no gas-snapshot files are tracked; gas numbers live as prose in docs/reference/REPRODUCIBLE_BUILDS.md and docs/benchmarks/BENCH.md, and the plan lists exact gas as out of scope. The template-tree digest is the drift gate that stands in for them. |
| regenerate deployments/sepolia/moonlight-wrap | scripts/prove_and_verify_moonlight_sepolia.sh | **BLOCKED, environment, not code.** Two independent blockers: (a) the local ../Moonlight checkout (fbd0f4f) has no MOONLIGHT_WRAP_SOLIDITY_* hooks, so it cannot emit the wrap verifier sources the midfall README documents; (b) the committed artifacts are fetched-back Sepolia runtime bytecode, so refreshing them needs a funded deployment. Consequence to accept explicitly: the plan's M3 golden test ("byte-identical to the deployed Moonlight artifacts") would compare against artifacts rendered by the PRE-curated generator. Either a compatible Moonlight checkout is pinned before M3, or the Moonlight comparison must be restated against a dump regenerated from this baseline. Flagged for sign-off. |
| Moonlight wrap end to end | cargo test --manifest-path ../Moonlight/aggregation/Cargo.toml wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs --release -- --ignored | PASS (210 s) in round 1, but against the git-pinned 2d52f24. Re-running against THIS baseline needs a path patch of Moonlight's five midfall git deps; the wrap test itself does not depend on halo2_solidity_verifier, so this validates the proof pipeline, not the generator. |
| cargo test -p midnight-proofs | default features | PASS (round 1: 32 lib + 1 integration + 8 doc tests). proofs/ is untouched by the curated items. |
| cargo test -p halo2_solidity_verifier feature matrix | --all-features --all-targets, and evm,rust-verifier-trace with the EVM gate | SPLIT RESULT (re-measured 2026-10-29): the recorded-profile leg is green - 249 lib tests + every fixture binary, 0 failures. The `--all-features` leg is RED: 210 passed / 39 failed, every failure at a proof-generation site with `SrsError(32, 62)` or `SrsError(64, 252)`. See the G0 table for the cause. The earlier "PASS: 248 lib tests" claim in this row could not be reproduced on this host and is superseded. |
| regenerate the six live poseidon artefacts (D-P28) | `tests/poseidon_fixture.rs` circuit path at k=6, witness seed 42, prover rng `0xdebd`, features `evm,rust-verifier-trace`, release | **DONE 2026-10-29.** Proof is 2,640 B / 72 reads as R-57 predicted; native + Solidity (Vm and Direct) all ACCEPT; SHA-256s re-pinned; 12 unread files deleted. Full record in "Poseidon fixture regeneration (D-P28)". |
| side effects of the gate runs on generated artefacts | `cargo test --all-targets` | **Trap, recorded so nobody is surprised.** Two test binaries write into the tree: `tests/poseidon_fixture.rs` rewrites `proofs/solidity-verifier/target/poseidon-fixture-dump/` (four of which are tracked and are what the Lean render gates read), and `tests/conformance_export.rs` rewrites `formal/fixtures/conformance/poseidon/` unless `MIDFALL_CONFORMANCE_OUT` is set. Both were restored byte-identical after the G0 runs (`git status` clean for both paths). Under the recorded profile the tracked `.sol` dumps reproduce byte-for-byte; only the untracked `proof.bin`/`calldata.bin` move, because of the OsRng quotient-limb blinding. A third poseidon binary, `tests/m0_poseidon_regen.rs`, is NOT a side effect: it is inert unless `M0_OUT` is set and then writes only into that directory. |

## Poseidon fixture regeneration (D-P28, 2026-10-29)

R-57 established that the committed poseidon fixture was **stale on arrival**
(published 2026-04-29, two days before the Keccak transcript changes of
05-01/05-02) and that the current verifier rejects it. D-P28 authorised
regenerating the six live artefacts under the profile this file already records,
re-pinning them, and deleting the twelve files in the directory that nothing
reads. Executed by P-M0 on 2026-10-29.

**Profile used** (the same one recorded under "Features.solidity" above):
cargo features `evm,rust-verifier-trace` on `halo2_solidity_verifier`, which
implies `truncated-challenges` and `midnight-proofs/solidity-verifier-trace`;
`outer-fewer-point-sets` and `outer-single-h-commitment` NOT passed, i.e.
`outerFewerPointSets = false`. Release profile. Circuit path identical to
`proofs/solidity-verifier/tests/poseidon_fixture.rs`: `PoseidonExample` at
k = 6, witness from `ChaCha8Rng::seed_from_u64(42)`, prover rng seeded
`0xdebd`, SRS `zk_stdlib/examples/assets/bls_filecoin_2p6`, pinned solc
0.8.30, revm Prague.

**Resulting proof shape**: 2,640 bytes = 21 x 48 + 51 x 32, i.e. **72 transcript
reads** - exactly the shape R-57 predicted for `outerFewerPointSets = false`.
`transcript_repr` is unchanged at `4cc2e5ac...0494`, so the circuit and VK
identity are the same as the stale fixture's.

**Acceptance** (the step this package exists for). The regenerated `proof.bin`
was replayed through the real verifier from the bytes on disk:

| leg | verdict |
|---|---|
| native `midnight_zk_stdlib::verify::<PoseidonExample, Keccak256>` | **ACCEPT** |
| generated Solidity verifier, Vm quotient lowering | **ACCEPT**, 638,069 gas |
| generated Solidity verifier, Direct quotient lowering | **ACCEPT**, 624,166 gas |

For contrast, the stale committed fixture replayed as: native **REJECT
`Error::Opening`**, and the current generator cannot even lay it out as
calldata (`repack_proof` -> `LengthMismatch { expected: 2640, actual: 4752,
prefix_g1: 19, num_evals: 48, num_point_sets: 3 }`).

**Files replaced** (six): `proof.bin`, `vk.bin`, `instance.be`,
`rust_trace.json`, `solidity_trace.json`, `verifier_trace.bin` under
`proofs/solidity-verifier/fixtures/poseidon/`.

**Files deleted** (twelve, zero code references - they appeared only in this
file's SHA table and in plan prose): `adversarial_fixtures.bin`,
`algebra_fixtures.bin`, `decomp_pairs.bin`, `evals_signature_fixture.bin`,
`gate_eval_fixture.bin`, `identity_g1_compressed.bin`,
`lagrange_aux_fixture.bin`, `pairing_fixture.bin`,
`query_schedule_fixture.bin`, `right_g1_fixture.bin`,
`right_msm_inputs_digest_fixture.bin`, `right_msm_terms_fixture.bin`.

**Container notes - what is faithful and what changed format.**

* `proof.bin`: current-code proof, compressed G1 + scalar reads, unchanged
  wire format.
* `instance.be`: 32 bytes, **big-endian canonical `Fq`** - the convention the
  committed file used (R-57: "the committed file is genuinely big-endian"). The
  *value* changed because the committed instance was not the seed-42 instance.
* `vk.bin`: **format change.** The committed 4,128-byte blob is a legacy
  container with no writer and no reader anywhere in this tree (it does not even
  start with the halo2 `VerifyingKey` version byte). The regenerated file is
  1,302 bytes of `VerifyingKey::to_bytes(SerdeFormat::Processed)`, which
  `VerifyingKey::from_bytes` round-trips. The VK identity it records is the
  same: `transcript_repr` matches the first 32 bytes of the old blob.
* `rust_trace.json`: same container (`{"entries":[{"kind","data":{...}}]}`,
  kinds `Intermediate` / `ReadPoint` / `ReadScalar` / `Challenge`), emitted
  from the live `solidity_trace` hooks of the accepted native run. The
  **vocabulary necessarily differs**: the committed tags (`advice[i]`,
  `dummy_eval`, `perm_product`, `q_eval`) came from
  `trace_replay.rs::replay_trace_from_vk`, a hand-written reconstruction
  deleted at `cf89e5f` that was never a verifier run (R-56 correction). Point
  payloads are now the 128-byte EIP-2537 padded form the hooks emit, not the
  old 48-byte compressed form.
* `solidity_trace.json` and `verifier_trace.bin`: same containers (flat
  `{kind, tag, *_hex}` array; `MTR1` + u32 BE count + length-prefixed
  name/data records), regenerated from the LOG stream of a traced render of the
  accepted proof. The old files recorded a Yul tracer whose emitter is not in
  this tree (`evals_signature`, `partial_eval.*`, `right_g1_digest`), so the
  tags are the current tracer's ids 1..=36 plus the proof-read, quotient-identity,
  PCS and selector-fold ranges.

**The regenerated proof is a recorded run, not a reproducible build.**
`blind_quotient_limbs` (`proofs/src/plonk/prover.rs:126`) draws its blinding
challenge from `OsRng`, so two runs of the same generator with the same seeds
produce the same first 720 bytes (the 15 pre-quotient point reads) and different
bytes from 721 on. Both runs verify. The SHA-256 table below therefore pins a
recorded accepted run; a future "regenerate and diff" check must expect the
quotient-limb tail to move.

**What the landed harness reproduces, measured 2026-10-29 (P-FREEZE).** Two of
the six artefacts reproduce byte-for-byte; four reproduce only structurally.
Running `tests/m0_poseidon_regen.rs` against the committed set:

| artefact | reproduces | measured |
|---|---|---|
| `vk.bin` | **byte-for-byte** | 1,302 B identical - `VerifyingKey::to_bytes(SerdeFormat::Processed)` is a pure function of circuit + SRS |
| `instance.be` | **byte-for-byte** | 32 B identical - the seed-42 witness hash |
| `proof.bin` | structural only | same 2,640 B; first 720 B identical, the tail differs |
| `rust_trace.json` | structural only | same 32,914 B, same 139 entries in the same order, same kinds / tags / payload widths; 105 of 139 carry different values |
| `solidity_trace.json` | structural only | same 29,106 B, same 138 records in the same order; 105 differ |
| `verifier_trace.bin` | structural only | same 12,783 B, same 138 `yul_trace.<tag>#<id>` names and payload lengths; 105 payloads differ |

The divergence starts exactly where the blinding starts: the first differing
native trace entry is `proof_quotient_commitment[0]`. The 34 entries that do
reproduce are everything upstream of it - `vk_repr`, `vk_digest`,
`num_instances`, the 15 pre-quotient point reads, the four challenges squeezed
before `y`, `k`, `n_inv`, `omega`, `omega_inv`,
`proof_committed_instance_eval[0]`, five fixed-column evals that are zero in
both runs, and `final_result`. Everything from `x` onward is downstream of the
blinded limbs. Gas moves with it: two harness runs measured Vm 638,129 and
638,117 (Direct 624,226 and 624,214) against the 638,069 / 624,166 recorded
above - the figures drift by tens of gas from run to run, caused only by the
different blinded bytes, which is a second reason the gas numbers in this file
are observations and not pins.

**Consequence for the pins.** The `vk.bin` and `instance.be` rows pin a
deterministic derivation, so a mismatch there means the circuit, the SRS or a
seed moved and is a real regression. The `proof.bin` row and the three trace
rows pin **one recorded accepted run**: what is reproducible about them is the
container, the read schedule and the tag vocabulary, not the bytes. A
"regenerate and diff" gate over those four is therefore meaningless; the
meaningful check is the structural one the harness performs - length, read
counts, and ACCEPT on all three legs.

**Generator status - the harness is landed (P-FREEZE).** The harness that
produced these six files was a temporary integration test in P-M0, run against
`M0_OUT` in a scratch directory and then deleted, which left the recipe as
prose. It is now committed as `proofs/solidity-verifier/tests/m0_poseidon_regen.rs`,
**env-gated on `M0_OUT`** (plus `HALO2_SOLIDITY_RUN_EVM_TESTS=1` and `SOLC=` at
the pinned 0.8.30) and inert without them: with `M0_OUT` unset both tests return
immediately and write nothing, so a plain `cargo test` and a plain
`--all-targets` run stay green - which matters because `--all-targets` is
already red on 39 unrelated tests for the missing extended-domain SRS assets.
The file re-emits all six artefacts into the directory named by `M0_OUT` and
asserts **structure, never bytes**: proof length 2,640, 21 point reads + 51
scalar reads = 72 transcript reads, and ACCEPT from the native verifier and
from the generated Solidity verifier on the Vm lowering, the Direct lowering
and the traced render. A second test, `m0_replay_directory`, is gated on
`M0_REPLAY_DIR` and replays recorded bytes through the real verifier; pointed at
`fixtures/poseidon/` it reports ACCEPT. That test is also where the
`instance.be` byte-order trap surfaces: both byte orders of that file decode as
canonical `Fq`, so a replay must read it big-endian, as recorded, or it rejects
a good proof with `Error::Opening`.

**Cross-cutting check - no Lean gate reads a byte that changed.** Nothing under
`formal/` opens `proofs/solidity-verifier/fixtures/poseidon/*`: the only Lean
mentions are doc comments (`Midfall/Instances/Bls12_381.lean:71,183`,
`Conformance.lean:79`, `Midfall/Conformance/Bundle.lean:153`). The Lean
conformance runner reads `formal/fixtures/conformance/poseidon/`, which is a
separate regenerated bundle and was NOT touched here; the Lean render gates read
`proofs/solidity-verifier/target/poseidon-fixture-dump/`, which was also not
touched (restored byte-identical after the G0 runs and re-verified against
`scripts/check_golden_provenance.py`). One consequence to note: the conformance
bundle's `proof.bin` is a *different recorded run* of the same circuit and
instance (same first 720 bytes, different quotient-limb tail). Both verify; they
are not byte-equal. Re-syncing them is a follow-up package, not a Phase 0 item.

## Fixture SHA-256s

Generated with `shasum -a 256` over the files named, from
`proofs/solidity-verifier/`. The poseidon rows were re-pinned on 2026-10-29
under D-P28 (see "Poseidon fixture regeneration"); the twelve unread poseidon
fixture files that used to appear here were deleted and are no longer pinned.

**The table is split in two, because only one half can be a pin.** Until
P-FREEZE it was a single 55-row list that half-checked: 25 of those rows named
files that are not in git at all, and 2 tracked rows had gone stale before the
freeze without anything noticing. The split below makes the difference
load-bearing, and `proofs/solidity-verifier/scripts/check_baseline_pins.py`
enforces it.

### Tracked pins - 30 rows

Every file here is **tracked in git**, so its bytes are fixed by the commit and
the hash is a real pin. This is the complete set: `git ls-files
proofs/solidity-verifier/fixtures proofs/solidity-verifier/target` returns
exactly these 30 paths. All 30 match the working tree as of 2026-10-29, after
the two stale rows listed under "Resolution of the two stale rows" were
re-pinned.

| sha256 | path |
|---|---|
| f86e8f03ce02214a7747729cf3c075d221eff2c3e51c78f8dea7e3a0da844ca4 | fixtures/ivc/instance.bin |
| 055bbfd22468b1d9803371cc765b664e359ec61d7be5537fcdfe69635adb7be2 | fixtures/ivc/proof.bin |
| 7945056172df44c07be8aa39b2f50594597d12076ae598b47ad03173479a7def | fixtures/ivc/rust_trace.json |
| 2c714487a2831d2380aa45bbca3883451b1676d50d0f02fb175eee8f33dd0a01 | fixtures/ivc/solidity_trace.json |
| 6126880f264a05da16fefa18a69ff26f7be3a30c1bd5bf66d543493ea3a16508 | fixtures/ivc/vk.bin |
| cebaf4594d605689a4e7f5d187d7fee743c34a0299b40c6dea0b3119df03178e | fixtures/poseidon/instance.be |
| 2120545041f640500771e7e285fed08ce07500794e6004f097984a053b44f289 | fixtures/poseidon/proof.bin |
| 8abfae7c773f43e985209f7431e85403dc2bb1d98c379b441ef16d22b7cbc540 | fixtures/poseidon/rust_trace.json |
| 67ed29fdde15d97fdc05397605795e794e6d256589059db37cd0bccb24f362b1 | fixtures/poseidon/solidity_trace.json |
| 7199576773869c25df0c8b513c24360572d69f77c493cf604b104c981030c745 | fixtures/poseidon/verifier_trace.bin |
| bffa79eaeca55dade10076e28d53a316a798eece9621313f13938de156307725 | fixtures/poseidon/vk.bin |
| 52bfc1b1a7b053d8b63916c81ab6e845125cae277b74ddaa5ae7b6d0c5a62e45 | fixtures/rsa_signature/instance.bin |
| b5212b21b686686749699702ba696f41a800f43ff7c83289a47ab01bd8dc8a6a | fixtures/rsa_signature/proof.bin |
| 94ff3fbf1934e6c72360307b7dfc38ebb7e41fcfe28ff97fab9c5cf10850ba20 | fixtures/rsa_signature/vk.bin |
| db5a581f2b081afb08470dbc65e12eaff8eb43e2aebffbea59310de12d53b4e1 | target/hybrid-mt-fixture-dump/Halo2Verifier.sol |
| a7307f9a890b903af2b504817792921573a880c1d66fca0755e3a6e220464091 | target/hybrid-mt-fixture-dump/Halo2VerifyingKey.sol |
| b4cc25f849f2cd6cfccf9f48c2e6772acdfb0065b89f7a10cf9263aa0a5e0f62 | target/hybrid-mt-fixture-dump/instances.be |
| 4086ef353eb00d62c9b803ff494d6f272ef32e2d1244fe4eed042b924b83d52e | target/ivc-keccak-solidity-dump/Halo2QuotientEvaluator.sol |
| c9347fde1dfeed43fd1dcc53cf9b6d165b02123e25497cf47001c7b3a6bd93b9 | target/ivc-keccak-solidity-dump/Halo2Verifier.sol |
| f758587480759d1fc694da6e4d1d6d52352a8d3e530e053feed73c078e2934a2 | target/ivc-keccak-solidity-dump/Halo2VerifyingKey.sol |
| b3917f0fd49f138a9d7a9ea63ce00852aea64d175b530a6ebbe12372bfaf9257 | target/poseidon-fixture-dump/Halo2Verifier.direct.sol |
| 0ebebe97beaf2e105faa5be2356de2adf8ed8643c98180603a38215d8215f050 | target/poseidon-fixture-dump/Halo2Verifier.sol |
| 745779220e757f0d1e5cee903598fa3abbcb0d3c217efd3a5f8fd8929181a48a | target/poseidon-fixture-dump/Halo2VerifyingKey.direct.sol |
| e4a7d45cd2526ad3efa38cc19cfa7b88d505e060f1feac0db48082fb61f0ce55 | target/poseidon-fixture-dump/Halo2VerifyingKey.sol |
| 3d1f037f725ee2f149cf472889b3ef9330d3ffdab82a999c13d1fe1b54517429 | target/rsa-signature-fixture-dump/Halo2Verifier.sol |
| 1261c6b1f695a136c70fe6800d59f2823c75d76c60af8df92f1206bfe11f3236 | target/rsa-signature-fixture-dump/Halo2VerifyingKey.sol |
| f8cdb21c1143e137aee4f6c4c9cdd274990c66e2160f92c027be88c2024e171f | target/rsa-signature-fixture-dump/instances.be |
| d6c6331f2672ec242890232d9e7537eed43c832f33406cbe4328bacd2c4ac6cf | target/sha-preimage-fixture-dump/Halo2Verifier.sol |
| 1a99f410c6b8f536c480d4d90b105e2189ef4cdef0235653963e4afe9127d596 | target/sha-preimage-fixture-dump/Halo2VerifyingKey.sol |
| cf9ea60bfee9769886ff15d846388a42bd8682a206c4119298c649a3f4636a92 | target/sha-preimage-fixture-dump/instances.be |

### Untracked, last-observed - 25 rows (**not pins**)

Every file here is **not tracked**: it exists only as whatever the last test run
wrote, under whatever feature profile that run used. Nothing fixes these bytes,
so a hash here is an observation and cannot be a pin. Two independent reasons:

* every `proof.bin` / `calldata.bin` moves with the `OsRng` quotient-limb
  blinding described in "Poseidon fixture regeneration", and
* the `target/ivc-keccak-solidity-dump/` render depends on the bench feature
  string, not on the recorded profile.

That is not hypothetical: the gate runs of 2026-10-29 that produced this table
moved 15 of these 25 rows - including
`target/poseidon-fixture-dump/proof.bin` and `calldata.bin`, which the mixed
table had recorded as matching. The values below were re-derived after those
runs and will move again on the next one. `check_baseline_pins.py` prints a note
when one has moved and does not fail.

| sha256 | path |
|---|---|
| 36b2547aeb19919944ddce0c1ed4c1b706505cc07f4ea915b412dcbdfb647952 | target/hybrid-mt-fixture-dump/Halo2Verifier.direct.sol |
| 2efd93795dc725f4aeb2b5b8a930c7ca976034eff47858e922170af109530675 | target/hybrid-mt-fixture-dump/Halo2VerifyingKey.direct.sol |
| 515fcaf6464b47df366c750ddd4ab9eb2b32087d9d79118bf3b30b12139be5ec | target/hybrid-mt-fixture-dump/calldata.bin |
| 8ee41908564bc833d3fc690c64268576fc8dcdde2d8b8193fb3676d486f28495 | target/hybrid-mt-fixture-dump/proof.bin |
| ee50b82009d7d8d569448404bdbc9027f02d9926c7ed12a085c8eb4f0fe95863 | target/ivc-keccak-solidity-dump/Halo2QuotientEvaluator.creation.bin |
| 9e41f6b7080e9182ffd061bb1e46592dbe349002fca7890ba91623ae764225f2 | target/ivc-keccak-solidity-dump/Halo2Verifier.creation.bin |
| cfbb66095666c4b779887da8a41c4076730e03b08b4afdd371b672b85db38adf | target/ivc-keccak-solidity-dump/Halo2Verifier.direct.sol |
| c84a2e752e034333e8ca3ff739c3f780a3370badd0ca503742078327c0f6a232 | target/ivc-keccak-solidity-dump/Halo2VerifyingKey.creation.bin |
| b9b2402aa4944dc7ab2a3543fd0a1c015d9004bfafb5f31a395528ca8d66da76 | target/ivc-keccak-solidity-dump/Halo2VerifyingKey.direct.sol |
| 7c3dcee39f38a0429c4b7cedf9faf88d7ed6638d543eba5a9e478836f1369f5e | target/ivc-keccak-solidity-dump/calldata.bin |
| ee7f60ec51c1bc12812f12a6f3920f7f6aaae5744ebf07357a22d57ed6d911c3 | target/ivc-keccak-solidity-dump/contract-sizes.txt |
| a72b86151973a3fef14b11e4815951d3e8e55d6287fc3b82069cd06a93e812c3 | target/ivc-keccak-solidity-dump/instance.le |
| bb819789684b0054514e6dc1d1fe6953d12c79ec59ad4077c5e3d1d3146ca1ac | target/ivc-keccak-solidity-dump/proof-evaluation-counts.txt |
| 1bac941ce0c8478ea4f1837239eaff4ddb153beb6ad681c51296a850ae735878 | target/ivc-keccak-solidity-dump/proof.bin |
| da85800aa34387d3159c1f813fe6ea5846a65c5e7e64b514b9219d06cf36da7a | target/poseidon-fixture-dump/calldata.bin |
| 276b414838d9478519646bd0e8036a00c67994d73f370f00cd5c58ba8cafa0cd | target/poseidon-fixture-dump/instance.be |
| 83acb2796f4e4aaf0a95b757a60a3c5f6668dd93beab7d1e0a97b1e71dfa338e | target/poseidon-fixture-dump/proof.bin |
| cde1a54117f54903b54aa9d51df769f527135f7cb7ec8c7d9a86a298888bd476 | target/rsa-signature-fixture-dump/Halo2Verifier.direct.sol |
| a51b5d176be3d63d25525a92c59442199a196362c3952fea766fc10c4c51fe10 | target/rsa-signature-fixture-dump/Halo2VerifyingKey.direct.sol |
| 07e93d3f3f3f19b32362845e20e8451adb4d0dbe78673a10ae10cb0ad8437525 | target/rsa-signature-fixture-dump/calldata.bin |
| 7ce34530518c6fc1de126d5e21c867fc166692f35022ea7c46ee5b9dfbe9557c | target/rsa-signature-fixture-dump/proof.bin |
| 25810bc294f466828e925b6028aca076bcc9e6720d93d327062c43bfd8b95576 | target/sha-preimage-fixture-dump/Halo2Verifier.direct.sol |
| cea0e0caee99fe979bab45593112e7d41f96c3a6de66b71c90b06c8d7e7c6304 | target/sha-preimage-fixture-dump/Halo2VerifyingKey.direct.sol |
| d95f2b3856d66f1a4b3daf7a9a131d5c167ec682f473041842c94d93a278e86f | target/sha-preimage-fixture-dump/calldata.bin |
| 6c79e1bfc176c3852a0184d13170bc7f063fe06ba7f11d52aca5f03af45fbe78 | target/sha-preimage-fixture-dump/proof.bin |

### Checking this table

```text
python3 proofs/solidity-verifier/scripts/check_baseline_pins.py
```

It parses both tables, classifies every row against `git ls-files`, and fails
if a pin does not match its file, if a pin row is not tracked, if a
last-observed row has become tracked (it then belongs in the pin table), or if
a path appears in both tables. It deliberately does not fail when a
last-observed row has moved.

### Resolution of the two stale rows (P-FREEZE, 2026-10-29)

Two **tracked** rows were already stale before D-P28 ran. P-M0 found them and
deliberately recorded rather than touched them:

| path | table said | HEAD and working tree |
|---|---|---|
| `target/ivc-keccak-solidity-dump/Halo2Verifier.sol` | `c4a04c1b8825ba9b...` | `c9347fde1dfeed43...` |
| `target/ivc-keccak-solidity-dump/Halo2QuotientEvaluator.sol` | `27a60d2922cfcf1d...` | `4086ef353eb00d62...` |

They are now **re-pinned to HEAD** rather than excluded from the pinned set,
which was the right resolution: the defect was in the table, not in the
artefacts. The step-6 IVC bench regeneration changed the two files and the
table was not re-derived afterwards. Both are tracked, both are byte-stable
under the recorded profile (they are renders, not proofs, so the `OsRng`
blinding does not touch them), and `Halo2Verifier.sol` is the artifact the Lean
golden chain cites (`formal/Midfall/Yul/Externals.lean:733`), so the pin now
agrees with the bytes a Lean gate reads. Nothing was regenerated to produce the
new values: they are the hashes of the committed blobs, re-derived with
`shasum -a 256`.

The 25 untracked rows were **not** re-pinned into the pin set and were not
deleted: they are kept, relabelled, and re-derived as of this package, because
they are still useful for drift diagnosis - they show what a given run emitted.
Their status is "last-observed", stated in the heading and enforced by the
checker.

Total rows: 55 = 30 tracked pins + 25 untracked last-observed. (67 rows before
D-P28; 12 unread poseidon orphans deleted, 6 live poseidon artefacts
re-pinned.) The earlier line "Total tracked fixture/dump files: 55" was wrong
in a way that mattered: 55 was the row count, and only 30 of those files are
tracked.

### M2 status update (round 7)

The **port is complete**: every Rust line on the verifier path now has a Lean
counterpart or a documented skip with grep evidence (Exec/{Verifier,Native} at
`389a0c4` closes the last of it: verify_algebraic_constraints, prepare, and the
query-vector assembly).

M2's **acceptance criterion cannot be met yet**, for two reasons that need decisions
rather than work:

* R-27 - the frozen §9.2 interface in `Statements.lean` is not implementable (it
  omits `G1Codec`, `FieldConsts` and `delta`), so the four `Exec/Native` sorries are
  blocked and there is no `verifyNative` for the conformance harness to run.
  Candidate D-P9 in docs/design.md proposes the re-pin.
* ~~R-28~~ **resolved** - `Instances/ExponentModel.lean` (`2d9a3b0`) supplies an executable
  model, and `Verifier.prepare` now runs end to end on a hand-built proof, accepting exactly
  one of 17 candidate values (independently re-verified). See R-33.
  the pairing path is executable even once the arity is fixed.

Until both are resolved, `conformance-rs` has no Lean side to compare against.

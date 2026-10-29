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
| side effects of the gate runs on generated artefacts | `cargo test --all-targets` | **Trap, recorded so nobody is surprised.** Two test binaries write into the tree: `tests/poseidon_fixture.rs` rewrites `proofs/solidity-verifier/target/poseidon-fixture-dump/` (four of which are tracked and are what the Lean render gates read), and `tests/conformance_export.rs` rewrites `formal/fixtures/conformance/poseidon/` unless `MIDFALL_CONFORMANCE_OUT` is set. Both were restored byte-identical after the G0 runs (`git status` clean for both paths). Under the recorded profile the tracked `.sol` dumps reproduce byte-for-byte; only the untracked `proof.bin`/`calldata.bin` move, because of the OsRng quotient-limb blinding. |

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

**Generator status.** The harness that produced these six files was a
temporary integration test (`tests/m0_poseidon_regen.rs`), run against
`M0_OUT` in a scratch directory and then **deleted**: it is not committed, so
nothing in the tree can currently re-emit this fixture set. The recipe it
encoded is the one stated above (same circuit, seeds and profile as
`tests/poseidon_fixture.rs`, plus the native trace events and the traced-render
LOG stream written into the three containers). If the project wants the fixture
re-generatable on demand, land that harness as an env-gated test - it must stay
inert under a plain `--all-targets` run, because an ungated version fails when
`M0_OUT` is unset.

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

Generated with shasum -a 256 over the tracked fixture inputs and the tracked
regenerated dumps on this branch. The poseidon rows were re-pinned on 2026-10-29
under D-P28 (see "Poseidon fixture regeneration"); the twelve unread poseidon
fixture files that used to appear here were deleted and are no longer pinned.

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

### Which rows of this table are stable pins (found while re-pinning, 2026-10-29)

The table mixes two kinds of row and only one of them can be a freeze pin.

* **Tracked - 30 rows.** 14 `fixtures/...` rows (5 ivc, 6 poseidon,
  3 rsa_signature) and 16 `target/...` rows name files that are **tracked in
  git**, so their bytes are fixed by the commit. 28 of the 30 verify against the
  working tree today; the 2 that do not are the stale ivc `.sol` rows in point 1
  below.
* **Untracked - 25 rows.** The remaining `target/*-fixture-dump/...` rows name
  files that are **not tracked**: they exist only as whatever the last test run
  wrote, under whatever feature profile that run used. They cannot be
  reproduced on demand - the ivc render depends on the bench feature string, and
  every `proof.bin`/`calldata.bin` moves with the OsRng quotient-limb blinding
  described above.

Two consequences, both recorded rather than papered over:

1. Two **tracked** rows were already stale before this package ran:
   `target/ivc-keccak-solidity-dump/Halo2Verifier.sol` and
   `Halo2QuotientEvaluator.sol`. The table pins
   `c4a04c1b8825...` / `27a60d2922cf...`; HEAD and the working tree both hold
   `c9347fde1dfe...` / `4086ef353eb0...`. The step-6 IVC bench regeneration
   changed them and the table was not re-pinned. This is a defect in the table,
   not in the artefacts.
2. The G0 runs on 2026-10-29 rewrote 13 further untracked rows (ivc, rsa, sha
   and hybrid-mt `proof.bin`/`calldata.bin`/`creation.bin`/`contract-sizes.txt`/`instance.le`),
   as any run of those fixtures necessarily does.

**Recommendation for the freeze:** keep the 30 tracked rows as the pins (after re-pinning the 2 stale ones), re-pin
the two stale ivc `.sol` rows to HEAD, and either drop the 25 untracked rows or
relabel them "last-observed, not a pin". Deciding this changes what the tag
claims, so it is left to the orchestrator rather than done unilaterally here.

Total tracked fixture/dump files: 55 (67 before D-P28; 12 unread poseidon
orphans deleted, 6 live poseidon artefacts re-pinned).



(filled in at the freeze)

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

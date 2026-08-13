# Fixes applied — August 2026 verifier review

Companion to `HALO2_VERIFIER_REVIEW.md`. This file records exactly what was changed, what was verified, and — importantly — **what the review found that these changes do not fix.**

## 2026-08-12 follow-up: generator-side closures

A second pass (with the workspace compilable) closed most of what the first
pass could only specify. Newly applied and validated:

- **P1 / M-2 — exact precompile gas bounds.** Gas model in
  `src/lowering/layout/mod.rs::gas` (EIP-2537 discount table + pairing
  formula, EIP-2565 modexp), threaded through `GasTemplateConstants` and
  emitted as `G1ADD_GAS` / `G1MSM_GAS_1PAIR` / `G1MSM_GAS_SMOKE` /
  `PAIRING_GAS_2PAIR` / `MODEXP_GAS` / `ACC_RHS_MSM_GAS` constants. Every
  precompile call site — templates, PCS emitter, and constructor probes —
  now forwards the exact scheduled cost instead of `gas()`; the two
  `quotientEvaluator` calls keep `gas()` deliberately (regular-call refund
  semantics, codehash-pinned callee) with a comment. Decision on cap style:
  exact schedule, no margin, per EIP-2537's DDoS-protection guarantee;
  liveness caveat (upward repricing ⇒ regenerate + redeploy) documented at
  the constants and in the spec §15. This deliberately reverses commit
  `2b2bf49` ("Forward gas to EIP-2537 precompiles", old finding M-04): those
  were hand-tuned literals, these are generated spec formulas, and the
  constructor probes now fail-fast on repriced chains, which is what M-04
  actually needed. Verified: `eip2537_gas_schedule_matches_spec_vectors`,
  `eip2537_calls_forward_exact_schedule_gas`, and the revm test
  `malformed_proof_point_rejects_with_bounded_gas` — a malformed point now
  costs no more than an honest verification (was 29.5M of a 30M limit).
- **P11 / H-1 (code half) — applied and repaired.** The patch as shipped
  could not compile: it shadowed the `omega: U256` binding with an `Fq` and
  referenced an undefined `srs_tau_is_consistent`. Landed in
  `src/lowering/vk.rs` with the helper implemented as a Pippenger-MSM
  Lagrange commitment of f(X)=X plus the pairing check
  `e([τ]G1, G2) == e(G1, s_g2)`. Verified:
  `srs_tau_binding_accepts_honest_params_and_rejects_foreign_s_g2` (honest
  SRS passes; s=1, s'=2s, and wrong-domain omega all fail).
- **H-1 (non-code half) — SRS provenance recorded.** Ceremony citation
  (github.com/midnightntwrk/midnight-trusted-setup), asset SHA-256s hashed
  by the new `scripts/record_srs_provenance.sh` and verified byte-identical
  against the ceremony's official `MIDNIGHT_SRS_CATALOG.md`; the gated test
  `midnight_srs_assets_bind_s_g2_to_lagrange_tau` pairing-checks the real
  2p19/2p20 assets. All recorded in `REPRODUCIBLE_BUILDS.md` §"SRS
  Provenance".
- **P7 / L-2 — q_eval_set comments.** Emitter now reports
  "{m} evaluation term(s), {n} commitment term(s)" (identity commitments
  excluded from n), so the comment matches the MSM pair count below it. The
  structural asserts (`pair_idx == non_identity_terms` /
  `== final_msm_terms`) plus a new whole-pairs assert guard the counts.
- **P13 / M-5 — solc hashes filled and script fixed.** Official sha256 for
  linux-amd64 and macosx-amd64 recorded (see `REPRODUCIBLE_BUILDS.md`);
  found and fixed a latent portability bug (`declare -A` fails on stock
  macOS bash 3.2); end-to-end verified by a real download+hash+version run.
  Rosetta mapping for Darwin-arm64 now documented in the script.
- **M-5 (remainder) — manifest + flags + provenance stamps.** New
  `scripts/generate_artifact_manifest.sh` produces the §4 manifest rows per
  fixture dump; `--optimize-runs` added to every recorded flag list
  (REVIEW_PACKET, dossier, REPRODUCIBLE_BUILDS) with the
  `runs=100000`-undeployable warning; the three provenance stamps were not
  contradictory but unlabeled — each is now labeled, with the canonical
  table in `REPRODUCIBLE_BUILDS.md` §"Provenance Identities". Still open
  from the original M-5 list: removing the `SOLC_OPTIMIZE_RUNS` env
  override from the reproducible path (kept, as the bench profiles rely on
  it; the manifest records the effective value instead).
- **I-4 — stale `src/codegen/*` anchors.** All 58 references across 13
  files fixed or covered: living reviewer docs (dossier §2 semantic map,
  plans, benchmarks, template comment) rewritten to the current
  `src/lowering/*` tree; the historical audit records (`AUDIT.md`,
  `AUDIT_FINDINGS.md`) carry a path-migration map at the top instead of
  rewritten history. `AUDIT_FINDINGS.md` 2026-05-11 #4's evidence cell now
  cites validators/tests that actually exist
  (`validate_quotient_program` / `quotient_vm_safety_validator_rejects_malformed_programs`);
  the previously cited names never landed. One review-side correction: I-4
  overreached on `QuotientNumeratorBlock.yul`, which does exist.
- **TA-1…TA-8 triaged.** Every TA item in `AUDIT.md` now carries a
  `Status:` line (TA-1 Fixed — the quoted scalar-0 skip no longer exists;
  TA-4 resolved/diagnostic-only; TA-5/TA-6 fixed by `460a666`; TA-2/TA-3
  open, cross-referenced to the deferred M-4 digest decision; TA-7
  fail-closed semantics now specified in the spec §12.7; TA-8 integration
  guidance).
- **I-2 (partial).** The generated opcode-summary comment is now rendered
  from the same `program.op_usage` predicates that gate the interpreter's
  case arms, so each artifact documents exactly its own opcodes; the
  `G1_IDENTITY_MPTR` comment no longer references nonexistent `mload`s.

**New finding discovered and fixed during this pass — feature-unification
challenge-truncation mismatch.** The `midnight-aggregation` dependency in
`Cargo.toml` unconditionally enabled `truncated-challenges`, which Cargo
feature unification forced onto `midnight-proofs` in EVERY build of this
crate. Consequence: the prover always truncated challenges, but a verifier
generated with `--features evm` (without this crate's own
`truncated-challenges` feature) did not mirror it — exactly the "wrong
setting on either side silently produces invalid pairings" hazard the
feature's own doc comment warns about. Every `evm`-only fixture test
(`rsa_signature`, `sha_preimage`, `hybrid_mt`) had been failing with valid
proofs reverting mid-PCS; bisect showed the breakage entered with the
workspace merge that introduced the aggregation dependency, long before the
2026-08 review. Fixed by removing the dependency-level feature so truncation
flows only through this crate's `truncated-challenges` feature; both
`--features evm` and `--features evm,truncated-challenges` now agree
end-to-end and all fixture tests pass in both modes. The committed
`target/*-dump` artifacts are canonically rendered with
`evm,truncated-challenges` (they contain the truncation code paths).

Deliberately not addressed, by explicit decision: **M-4** (`vk_digest`
coverage — protocol change affecting the prover) and anything outside
`proofs/solidity-verifier/`. Remaining open from the tables below: P4, P8,
P9, P10, P12, P14, L-4, L-9, L-10, I-6, I-7.

## 2026-08-13 follow-up: Low/Informational batch closed

The remaining P-series patches and L/I findings were applied in a third pass
(commits: planner asserts, runtime hardening, provenance/digest, docs):

- **P9 (L-7)** — planner asserts tie the batch_invert scratch capacity and
  the Lagrange run length to the template's own expression; overflow (which
  corrupted silently) now refuses to plan. Region-shape tests included.
- **P8 (L-5)** — the user-challenge window is asserted to cover the phase
  sum of squeezed challenges and to end at or before THETA_MPTR; an
  undersized window refuses to plan (positive + should-panic tests).
- **L-2 (assert half)** — `queries()` asserts every identity-pinned
  commitment originates from the committed-instance column, the exact
  justification for the MSM omission.
- **I-6** — both latent divergences are now plan-time assertions: the
  permutation z ordering is re-derived under the upstream (Cur/Next then
  reversed Last) order and the intermediate-set structures compared; the
  column-based vs query-based fixed-eval counts are asserted equal.
- **P12 (L-6)** — the runtime quotient VM clamps every decoded
  memory-pointer operand against the coarse union of the planned read
  windows (shared source of truth with the build-time validator), clamps
  FOLD_SELECTOR's bucket index and y-power gap, and guards stack pops
  against balanced underflow.
- **P4 (L-3)** — seven declared custom errors cover the verify path
  (constructor probes keep bare reverts by scoped decision); selectors
  pinned against keccak of the signatures and decoded end-to-end in revm.
- **L-4** — decision: keep the exact `calldatasize` pin; the ERC-2771 /
  calldata-appending incompatibility is now documented in `verifyProof`'s
  NatSpec (typed BadCalldataShape revert).
- **I-7** — `vk_digest` joined the accumulator batching randomizer's
  preimage (verifier-local; no prover interaction).
- **P10 (L-8)** — every render carries `BUILD_ID` (feature profile,
  vk_digest, VK codehash, SRS fingerprint keccak(n||G2||s_g2||[tau]G1),
  optional deployment provenance tag via `RenderOptions::provenance`).
- **P14 (L-1)** — `tests/template_digest.rs` pins a keccak of the sorted
  `templates/` tree in default CI, closing the committed-fixture drift gap.
  The deeper L-1 legs (expression front-end certification, native-kernel
  differential) remain future work.
- **L-9 / L-10 / I-5** — `docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md`
  states the wrapper obligations as requirements, adds the incident/migration
  playbook keyed on BUILD_ID, records the truncated-challenge ≈2^-107.6
  bound as an accepted risk with a 2^100 target level and a sign-off line,
  and records the transcript domain-separation gap (I-5) as accepted —
  it cannot be fixed verifier-side without breaking prover compatibility.
- **I-2 leftovers / I-3** — smoke-window comment corrected (creation-frame
  memory cannot pre-expand the runtime frame), `validate_public_accumulator`'s
  shape-dependent `r` parameter documented, the unreachable identity-flag
  branch labeled unreachable-by-construction.

Still open after this batch: the deeper L-1 certification legs, M-4
(excluded by owner decision), and the outer single-H recorded-hash refresh.

## Short answer: no, this does not address all the findings

Of the 23 findings, **4 are closed or substantially closed by the changes below.** The rest fall into three groups:

- **8 need generator logic** (Rust changes plus values computed at codegen time). They are fully specified in Part V of the review with exact insertion points, but were not written, because the generator cannot be compiled from this session — `solidity-verifier/Cargo.toml` depends on `../../curves`, `../../circuits` and `../../zk_stdlib`, which are outside the connected folder. Writing Rust into a workspace that cannot be `cargo check`ed would risk breaking your build to no benefit.
- **1 is patch-ready but unverified** (`patches/P11_srs_binding.patch`) for the same reason.
- **9 are not code problems.** They need data or decisions only you hold: the ceremony reference, the SRS hash, the artifact manifest, the incident-response policy, an accepted-risk sign-off on the truncated-challenge security level. No patch can close those.

---

## Applied and validated

Verified by compiling the rendered output with the pinned toolchain (solc 0.8.30, `--via-ir --optimize --optimize-runs=1 --evm-version cancun`, CBOR off) and running it under `revm 19` / `SpecId::PRAGUE` against the `moonlight-wrap` fixture plus 40 adversarial mutations.

| Patch | Finding | File |
| --- | --- | --- |
| **P2** | M-1 | `templates/contracts/Halo2Verifier.sol`, `templates/partials/verifier/PrecompileSmoke.sol` |
| **P3** | M-1 | all three `templates/contracts/*.sol` |
| **P5** | M-3 | `templates/partials/verifier/PrecompileSmoke.sol` |
| **P6** | I-1 | `templates/contracts/Halo2Verifier.sol` |

**P2 — free-memory-pointer guard.** `if gt(mload(0x40), TRANSCRIPT_MPTR) { revert(0, 0) }` at the top of the main assembly block, and the equivalent in `require_eip2537_precompiles` (which runs in the *creation* frame that `compiled_memoryguard_does_not_overlap_generated_layout` does not inspect). The invariant is now enforced by the deployed bytecode rather than by a test in this repository that an integrator recompiling the `.sol` will never run.

**P3 — pragma pinned to `0.8.30`.** Not cosmetic. Measured:

```
solc 0.8.24 runs=1       -> 29,567 B runtime -> HALT CreateContractSizeLimit
solc 0.8.30 runs=100000  -> 29,836 B runtime -> HALT CreateContractSizeLimit
solc 0.8.30 runs=1       -> 21,286 B runtime -> deploys
```

`^0.8.24` advertised a compiler that cannot produce a deployable contract. The spill reservation also moves with the version (`0x8c0` on 0.8.24, `0x8e0` on 0.8.26+), which is the concrete reason the P2 guard is not theoretical.

**P5 — four known-answer precompile probes.** The existing smoke test hardened `G1ADD` with a known-answer vector and gave a good explanation of why identity inputs prove nothing — then tested `G1MSM` and `PAIRING_CHECK` with identity inputs only. Those are the two precompiles the verifier's security actually rests on: `G1MSM` is the curve/subgroup validator for every absorbed proof commitment, and `PAIRING_CHECK` is the sole accept gate. Added:

- **(a)** `G1MSM([2]·G) == 2G` — a stub that echoes zeros fails this.
- **(b)** `G1MSM` **must reject** `(4, y)` — a point satisfying `y² = x³ + 4` over `Fp` that is provably *not* in the r-order subgroup (verified off-chain: `r·P ≠ O`). This is the one property the entire deferred-validation strategy depends on and the one no other probe exercised. Gas is deliberately bounded to 200,000: a rejecting precompile consumes everything forwarded to it, so an unbounded `gas()` here would burn 63/64 of the deployment gas.
- **(c)** `e(G, G₂)·e(−G, G₂) == 1`.
- **(d)** `e(G, G₂)·e(G, G₂) != 1` — catches a `0x0f` that always returns 1, which would otherwise accept every proof.

This closes **M-3** and addresses `AUDIT.md` TA-6, which was still un-triaged (no `Status:` line). TA-6 should now be marked resolved and its severity reconsidered — with the accept path resting entirely on `0x0f`, Low was too low.

**P6 — comments that contradicted the code.** The NatSpec claimed "generated scratch starts at `0x80`" while `TRANSCRIPT_MPTR = 0x1000`. That was the exact stale belief TA-5 identified as the hazard, hardcoded in the template so every render shipped it. Also corrected the `docs/MEMORY_LAYOUT.md` path to `docs/architecture/MEMORY_LAYOUT.md`.

### Measured cost

| | baseline | patched | delta |
| --- | --- | --- | --- |
| verifier runtime | 21,286 B | 21,299 B | **+13 B** |
| deployment gas | 5,330,806 | 5,766,768 | +435,962 (one-time) |
| valid-proof gas | 1,279,482 | 1,279,513 | **+31** |
| 40-case test suite | 1 accept / 39 reject | identical | — |
| non-Prague deploy (CANCUN/SHANGHAI/MERGE) | reverts | reverts | — |
| mutated-VK / EOA-VK deploy | reverts | reverts | — |

The strengthened probes cost **nothing** at verify time — they run only in the constructor. That deployment succeeds is itself the validation: all four new known-answer probes pass against a correct EIP-2537 implementation, so the constants are right.

---

## Applied, syntax-checked only

**P13 — `scripts/install_pinned_solc.sh`** now verifies the downloaded compiler by SHA-256 and fails closed. `bash -n` passes.

⚠️ **Action required:** the hashes are `TODO-fill-from-list.json`. Fetch them from `https://binaries.soliditylang.org/{linux-amd64,macosx-amd64}/list.json` and fill them in — until then the script refuses to install, which is the intended fail-closed behaviour but will block a fresh checkout. Also still open: `Darwin-arm64` maps to `macosx-amd64`, so Apple Silicon runs an x86 binary under Rosetta, which is a different binary from CI.

---

## Patch supplied, not applied

**`patches/P11_srs_binding.patch`** — the highest-severity finding (**H-1**). Adds two assertions to `src/lowering/vk.rs`:

1. `params.g2() == G2Affine::generator()` — the G1 side is already defended this way; the G2 side was not.
2. A pairing consistency check that `s_g2` corresponds to the same τ that produced `g_lagrange`, by committing `f(X) = X` in the Lagrange basis to obtain `[τ]G1` and checking `e([τ]G1, G₂) == e(G1, s_g2)`.

**Not applied because it cannot be compiled from here.** It will likely need small adjustments — the pairing helper's import path, and the exact `Fq`/domain accessor names. Please `cargo check` before committing. The `srs_tau_is_consistent` call in the patch is a placeholder for whatever pairing helper your curve crate exposes.

This patch closes the *checkable* half of H-1. The other half is not code: name the ceremony, record the SRS SHA-256, and publish `NEG_S_G2_BASE` next to the ceremony's published τ point so a third party can verify the negation independently. `CODEGEN_ASSURANCE_DOSSIER.md:46` already lists the SRS record as required; nothing currently produces it.

---

## Specified but not written — needs generator work

Each is fully specified in Part V of the review, with the insertion point named.

| Patch | Finding | Why it needs the generator |
| --- | --- | --- |
| **P1** | M-2 | Needs an EIP-2537 gas model in `plan.rs` to emit per-call-site caps. **This is the one with real operational impact** — a single off-curve byte currently burns ~98.5% of whatever gas limit you supply (29.5M of 30M). |
| **P4** | L-3 | Custom errors touch ~41 revert sites, some template-resident and some emitted from `src/lowering/kzg/mod.rs`; a partial application would leave the taxonomy inconsistent. |
| **P7** | L-2 | Codegen assertion that MSM `x1` exponents omit exactly the identity commitments, plus fixing the emitted comment that says "43 commitment(s)" and emits 42. |
| **P8** | L-5 | `CHALLENGE_MPTR` must get its own window in the memory planner. |
| **P9** | L-7 | Planner assertion on `batch_invert` scratch capacity. Note this one currently fails **silently** — the modexp still succeeds, so nothing reverts. |
| **P10** | L-8 | `BUILD_ID` needs generator commit, feature list and SRS hash plumbed into the render context. |
| **P12** | L-6 | Quotient-VM operand clamps need new template variables for the window bounds. |
| **P14** | L-1 | A `templates/` tree digest test. Cheapest closure of the codegen-trust gap, and needs no SRS, so it runs in default CI. |

---

## Not fixable by patch — needs your data or a decision

| Finding | What is needed |
| --- | --- |
| **H-1** (remainder) | Ceremony name and transcript URL; SRS file SHA-256; publish `NEG_S_G2_BASE` against the ceremony's τ. |
| **M-4** | Redefining `vk_digest` to cover the SRS points, quotient program, accumulator schema and feature profile is a protocol change affecting the prover — a design decision, not a patch. |
| **M-5** (remainder) | Fill the `REVIEW_PACKET.md` §4 manifest (currently `fill per artifact` in all 11 rows); reconcile the three conflicting provenance stamps (`3fb6d84` / `a096e71…` / `53dc872…`); add `--optimize-runs` to the recorded flag set and remove the `SOLC_OPTIMIZE_RUNS` env override from the reproducible path; ship `REPRODUCIBLE_BUILDS.md`. |
| **L-4** | Decide: relax the `calldatasize` pin to `>=`, or document that ERC-2771 forwarders cannot call this verifier. Both are defensible; the other four pins already carry the security property. |
| **L-9** | Write the incident-response and migration section, and state the wrapper obligations as requirements: replaceable verifier address, wrapper-held pause, and binding `block.chainid` + wrapper address into the statement. |
| **L-10** | Sign off on ~2⁻¹⁰⁸ PCS soundness from `truncated-challenges`, or disable the feature. Record the target security level in the deployment record. |
| **I-4** | Rewrite the `src/codegen/*` anchors in `CODEGEN_ASSURANCE_DOSSIER.md` and `AUDIT_FINDINGS.md` to the current `src/lowering/*` tree. Until then the ~20 findings marked "Fixed with named tests" in the 2026-05-11 addendum cannot be re-verified by a reviewer. |
| **I-2, I-3, I-6, I-7** | Cleanup and assertions; low value, no urgency. |

---

## Re-render required

The changes are to **templates**, so the committed fixtures under `fixtures/` and `deployments/` are now stale relative to them. Before relying on any of this:

1. Re-render the fixtures (see each `fixtures/*/README.md` — needs the SRS and a Moonlight checkout).
2. Update the source-commit stamps in those READMEs.
3. Re-run the replay tests. Note that `tests/ivc_accumulator_replay.rs` compiles the **committed** `.sol`, not fresh template output, so it will keep passing either way — which is finding **L-1**, and the reason P14 matters.

## Suggested next steps

1. `cargo check` and commit `patches/P11_srs_binding.patch` — highest severity, build-time only, no on-chain change.
2. Fill the solc SHA-256 values so P13 stops blocking fresh checkouts.
3. P1 — the gas cap. It is the finding with day-one operational impact for any relayer or batching wrapper.
4. P14 — one test, no SRS needed, closes the widest assurance gap for the least work.
5. Fill the artifact manifest and reconcile the provenance stamps (M-5).

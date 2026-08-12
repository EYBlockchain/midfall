# Fixes applied — August 2026 verifier review

Companion to `HALO2_VERIFIER_REVIEW.md`. This file records exactly what was changed, what was verified, and — importantly — **what the review found that these changes do not fix.**

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

# Robustness & Quality Assessment and Redesign Proposals

> Companion to
> [`../architecture/ARCHITECTURE_REVIEW_2026-08.md`](../architecture/ARCHITECTURE_REVIEW_2026-08.md).
> Produced 2026-08-08 against the `misc-fixes` branch by an independent
> multi-reviewer pass: nine subsystem mapping reviews, four assessment lenses
> (soundness, library robustness, on-chain security, architecture quality),
> and a second adversarial pass in which every finding cited below was
> re-verified against the source by a reviewer instructed to refute it.
> Findings are labeled **Confirmed** (every element checked in code) or
> **Partial** (core claim holds; stated corrections apply). Line numbers are
> as of this snapshot. As with any review, verify accuracy and completeness
> against the current sources before acting on it.

## 1. Overall verdict

| Lens | Score | Summary |
| --- | :-: | --- |
| Soundness of generated verifiers | 8/10 | No accept-invalid path or calldata malleability found. Calldata parsing is injective and fully pinned; every scalar/coordinate ingress is canonicality-checked; subgroup checking is delegated under a machine-checked coverage invariant; the quotient-VM certification chain is genuine defense-in-depth. Residual risk sits in what is assumed rather than proven (§3.2) and in assurance-process gaps (F1). |
| Robustness as a library | 7/10 | Two well-executed tiers — typed errors at the boundary, fail-closed asserts inside — that contradict each other's contracts: legal-but-unusual circuits pass `try_new` and then panic inside `render()`/`encode_calldata()` (F2), and per-proof encoding rebuilds the whole pipeline (F4). |
| Security of generated on-chain code | 8/10 | Precompile discipline, pinning, and fail-closed parsing are unusually strong. Must-fix hardening: the false `memory-safe` annotation + floating pragma with no runtime guard (F3), and dead unpinned-quotient template branches (F13). |
| Architecture quality & maintainability | 7/10 | Clean, verified macro-architecture (facade → snapshot → converged plan → declarative render). Liabilities are consistent in kind: strings and conventions doing work types should do (F7, F8, F10, F11), two oversized modules (F14), and measurable docs rot in the audit chain (F6, F15). |

The failure direction is consistently **crash-or-reject** — the right default
for this domain. Nothing found blocks the bounded correctness claim in
`docs/audit/CODEGEN_ASSURANCE_DOSSIER.md`; most of what follows lowers the
cost and raises the credibility of the external audit this repo is explicitly
preparing for.

## 2. What is strong — and should not be redesigned

Explicit non-goals for any redesign; these choices are earning their keep:

- **The narrow supported envelope** and fail-fast `try_new` validation.
- **The static absolute memory layout** with the lifetime-aware overlap
  validator. (Harden its seams — F5, F9 — do not replace it with FMP-based
  allocation.)
- **The compact quotient VM in the codehash-pinned VK payload**, and the
  render-time certification chain: 3-stage validators, pointer whitelist,
  reference-interpreter certification at an artifact-seeded challenge,
  dual-build (recognizers on/off) agreement, and word-for-word re-comparison
  of VK-embedded program bytes. Keep `vm/reference.rs` deliberately
  independent of the emitter — the N-version leg is the point.
- **Single converged `LoweringPlan` per `render()` call** (extend it with
  caching, F4 — don't weaken it).
- **Pinning by runtime length + codehash, re-checked per call.**
- **Templates-consume-facts** and `QUOTIENT_VM_SPEC` as the single VM ABI
  source.
- **Loud-failure test prerequisites, gas-based stage attribution in replay
  tests, and self-describing fixtures.**

## 3. Findings register

### 3.1 High severity (all Confirmed)

**F1 — The adversarial EVM suite is excluded from every CI workflow by the
`pbt_` name filter; the CI comment claims otherwise.**
`.github/workflows/ci.yaml` (EVM job) runs
`cargo test -p halo2_solidity_verifier --release --all-features pbt_` plus the
Poseidon fixture; the default job leaves `HALO2_SOLIDITY_RUN_EVM_TESTS` unset
so EVM tests self-skip; the bench workflow runs only the IVC bench scripts.
Tests that therefore run in **no** workflow include the strongest
security-relevant negatives: `every_proof_g1_rejects_noncanonical_coordinates`
(`src/test.rs:2868`), `..._base_modulus_coordinates` (:2914),
`..._off_curve_coordinates` (:2948),
`compiled_memoryguard_does_not_overlap_generated_layout` (:1441),
`compiled_verifier_runtime_fits_the_eip170_limit` (:1495),
`batch_invert_fails_closed_on_noncanonical_words_in_all_paths` (:1584),
`malformed_embedded_calldata_variants_are_rejected` (:1284),
`vk_payload_section_mutations_are_rejected` (:1349),
`supported_shape_circuit_fuzz_e2e` (:501), and
`same_srs_distinct_shape_matrix_rejects_cross_wiring` (:629). The CI step
comment explicitly claims "non-canonical scalar and G1 rejection, EIP-170
runtime size, and the memoryguard overlap check" run in that step — they do
not. A regression in any of these merges green. → Proposal P0.1.

**F2 — Extensive panic surface behind the Result-typed public API.**
`render()`, `render_quotient_evaluator()`, `repack_proof()`,
`encode_calldata()`, and both diagnostics route through `LoweringPlan::new`,
which converts every post-constructor failure into a panic
(`src/lowering/plan.rs:167,183`; convergence panics at
`src/lowering/vk.rs:231-234,367`; model validation at
`src/lowering/artifacts.rs:66,296`; plan validation `.expect` at
`src/lowering/quotient.rs:469`). Legal shapes that pass `try_new` and then
panic include: >28 distinct PCS rotation points, rotation spans >4096,
circuits whose VK payload exceeds EIP-170, and VKs with unremoved virtual
selectors — while `try_new`'s docs promise "a typed error when the supplied
constraint system is outside the currently supported shape" and
`GeneratorConfig`'s docs claim the constructor validates the entire shape up
front. `vm/reference.rs:129-130` even documents that a malformed stream "must
surface as a `GeneratorError`, not a process abort," yet its only production
call site converts the `Result` to a panic. → Proposal P1.1.

**F3 — False `("memory-safe")` annotation + floating `pragma ^0.8.24`, with
no per-PR or on-chain enforcement of spill-window disjointness.**
The terminal assembly block writes absolute addresses from 0x1000 up and
never allocates via the free-memory pointer; the annotation is documented
in-repo as "a false promise" that is load-bearing (the block does not compile
without it). Disjointness of solc's via-IR spill reservation (observed up to
0x8e0 of the 0xF80 headroom) from the generated layout is checked only by
`compiled_memoryguard_does_not_overlap_generated_layout` — env-gated and, per
F1, not run in CI. The floating pragma permits deployers to compile with any
0.8.x ≥ 24, unbinding the artifact from the pinned compiler the check was
measured against. Nothing at deploy or run time detects an overlap; a live
spill slot sharing bytes with the transcript buffer would corrupt verifier
state silently. → Proposal P0.2.

**F4 — Every per-proof `repack_proof`/`encode_calldata` call rebuilds the
entire lowering pipeline, including an O(2^k) SRS fold and two certification
passes.** `src/lowering/calldata.rs:157-159` calls
`self.lowering_plan().repacked_proof_layout_plan()` per proof;
`LoweringPlan::new` runs `generate_vk` — whose `generate_base_vk` folds every
`g_lagrange` point to assert the SRS base (`src/lowering/vk.rs:81-92`; k=20
for the IVC shape) — plus both convergence loops, full VM compilation, and
both certifications. `render()`, `proof_evaluation_counts()`, and
`quotient_identity_manifest()` each independently rebuild the same plan;
nothing on `SolidityGenerator` caches it, and the doc comment states each
path builds its own plan. Cross-call consistency rests on determinism by
convention (pinned by one repeated-plan test). This is seconds of latency and
a realistic DoS surface for a service encoding many proofs. → Proposal P1.2.

**F5 — Cross-phase memory-overlap soundness hangs on `MemoryPhase`
declaration order matching template include order, enforced only by a
comment.** `MemoryLifetime::intersects` treats distinct `Phase` lifetimes as
never co-live and compares `PhaseSpan`s with the derived `Ord`
(`src/lowering/layout/memory.rs:192`); the sync requirement with
`Halo2Verifier.sol` include order exists only as a doc comment
(memory.rs:121-127). A mis-ordered variant silently disables overlap
detection for the affected pair. The model's acknowledged blind spot — the
0x1000-band `AccumulatorPairingBatch`/`FinalPairing` frames — is asserted
disjoint only under `cfg(test)` (memory.rs:1522-1539), not in
`VerifierMemoryLayout::validate()`. (Correction from verification: that
specific pair is currently disjoint *by construction* —
`FINAL_PAIRING_SCRATCH_START = PAIRING_BATCH_PTR + PAIRING_BATCH_HASH_BYTES`
— so the exposure is to future edits, not the current layout.) → Proposal
P0.3 / P2.2.

**F6 — `REPRODUCIBLE_BUILDS.md`'s dependency-pinning claim contradicts
`Cargo.toml`.** The doc claims "All Midfall crates are resolved from the
pinned git revision in Cargo.toml"; `Cargo.toml` declares only workspace path
dependencies (`midnight-proofs = { path = ".." }`, etc.), so published
runtime hashes are a function of the enclosing workspace checkout. Mitigating
nuance: the doc records the Midfall revision in prose, so a careful reader
can still reproduce — but the stated mechanism is false in the document that
underwrites the hashes. → Proposal P0.4.

### 3.2 Residual assurance boundary (documented, not a defect)

The certification chain proves the **emitter → reference-interpreter** leg
per render. The **reference-interpreter → Yul** leg rests on opcode-table
conformance tests (a `case` exists per opcode — not that the case body is
correct) plus native/Solidity trace differentials on fixture circuits; an
opcode no fixture emits has unverified runtime semantics. Identities executed
as inline Yul, native callbacks, or the structured tail are never lowered to
bytecode and are covered only by the trace differentials. This is honestly
documented (`LOWERING_ARCHITECTURE_SPEC.md` §12.1, `vm/reference.rs:20-27`)
— listed here because Proposal P2.5 can close most of it, and because the
trace differential that covers it is itself env-gated (F1).

### 3.3 Medium severity

**F7 — Yul text is an internal IR** *(Partial — corrected)*. The evaluator
emits Yul strings; permutation/lookup/trash identities are re-parsed from
those strings into `QuotientExpr` trees by a shallow parser
(`src/lowering/quotient.rs:939-945` → `vm/mod.rs:1236-1279`); limb7 fusion is
textual pattern-matching (`quotient.rs:1172-1311`); helper inclusion is
substring scanning (`quotient.rs:93-118`). Correction from verification: in
actual builds the parsed families become native callbacks/structured tail,
which `certify_quotient_program` **skips** (certify.rs:176-180) — interpreted
gate identities are certified against trees from typed `Expression<Fq>`
lowering, not the parse. Net effect stands: no check compares the parsed
trees against an independent source, so a parser bug on those families is
invisible to certification and caught only by the env-gated EVM trace
differential. → Proposal P2.6.

**F8 — MODARITH7/AFFINE_SUM operand layouts hand-decoded in five Rust sites
plus the template** *(Confirmed, sites enumerated)*:
`validate_quotient_const_slots` (vm/mod.rs:2134-2192), the pointer walker
`quotient_read_pointers` (:2424-2506), the checked length walkers
(:2578-2680), the separate trusted length walkers (:3073-3105), the reference
interpreter (reference.rs:280-376, 436+), and
`QuotientNumeratorBlock.yul:715-757, 896-1052`. Certification cannot catch a
validator walker diverging from the emitter/reference pair. → Proposal P2.1.

**F9 — Panicking "trusted" bytecode walkers are safe only under a
validate-first convention** *(Confirmed)*. `quotient_op_len` panics on
unknown opcodes and reads without bounds checks; the run-after-validation
convention lives in doc comments only, and one call site
(`compact_quotient_runs`, vm/mod.rs:1931-1983) walks builder-emitted bytes
*before* validation runs in `finish()`. → Proposal P2.1.

**F10 — Injected code blocks couple to template scope by naming convention**
*(Confirmed)*. `Vec<Vec<String>>` Yul lines (models.rs:519-526, 635-640) are
spliced verbatim and reference template locals (`r`, `y`, `delta`,
`quotient_eval_numer`, …) with no identifier validation; only solc would
catch a mismatch. Related *(Partial)*: models validate at construction inside
`generate_*_from_plan` (panicking), but `render()` itself does not enforce
`validate_layout()` — a future direct-construction call site could render an
unvalidated model. → Proposals P1.3, P2.6.

**F11 — Template security behavior pinned by raw-text `contains()`
assertions** *(Partial — incident nuance)*. Guard tests assert substrings of
the **unrendered** template corpus (`src/lowering/tests.rs:1624-1690`).
Verification surfaced a concrete prior incident: commit `72bc1b2`
(2026-07-19) fixed an always-false Yul guard in `AccumulatorHelpers.yul`
that left `load_acc_point`'s `if is_id` branch dead while the adjacent
`contains()` test stayed green (the decoder remained fail-closed; no forgery
was possible — the incident shows the test style's blindness, not a
vulnerability). → Proposal P2.5.

**F12 — Feature profile recorded nowhere machine-readable in artifacts**
*(Partial)*. `truncated-challenges`, `outer-fewer-point-sets`, and
`outer-single-h-commitment` change the proof schema the rendered verifier
expects; a mismatch fails as bare `revert(0,0)` (hardcoded proof-length check
or failed pairing) with no diagnostic. Correction: truncated-challenges is
human-discernible via a rendered comment; the other two leave no named trace.
Also *(Confirmed)*: `RenderDiagnostics::default()` is intentionally
feature-gated, so default render shape depends on compile features.
→ Proposal P1.4.

**F13 — Dead unpinned external-quotient template branches** *(Partial —
guards stronger than claimed)*. `Constructors.sol:63-82` (and the two-arg
variant) render a constructor without a codehash `require` when
`expected_quotient_codehash` is `None`, and `QuotientAndLinearization.yul`
omits the pre-call codehash re-check in the same case. Corrections: the
configuration is unrepresentable through the public API (`RenderQuotient` has
only `Inline` and `ExternalPinned`), and the "deprecated panicking APIs"
mentioned in the spec no longer exist in source — the guards are the enum
shape plus an `artifacts.rs` assert. The hole-shaped template text is still
dead weight that an auditor must reason away. → Proposal P1.3.

**F14 — Module hygiene: two monoliths** *(Confirmed)*. `vm/mod.rs` is 4,382
lines mixing the opcode ABI, builder, three validators, shape recognizers,
the Yul parser, and proof-repack layout types that belong to the calldata
boundary (`RepackedProofLayoutPlan`). `kzg::computations` is one 1,014-line
function (kzg/mod.rs:834-1847) whose trace-only q_com walk (:1226-1334)
structurally duplicates Block 5's final-MSM term enumeration (:1673-1731).
→ Proposal P2.3.

**F15 — Audit-chain docs rot** *(Confirmed)*.
`CODEGEN_ASSURANCE_DOSSIER.md:59-64`, `AUDIT.md`, and `AUDIT_FINDINGS.md`
cite the vanished `src/codegen/` tree (REVIEW_PACKET.md is current — the
audit docs disagree with each other); README carries two stale,
self-contradictory test counts (167+4 at line 49, 177 at line 389; actual at
snapshot: 202 lib + 9 integration) and a broken `./TESTING_STRATEGY.md` link;
`ROADMAP.md` links a nonexistent `./AUDIT.md` and presents fixed blockers as
open; STATUS/dossier are a dated snapshot ("suite was not rerun") with no
re-assessment trigger. → Proposal P0.4.

**F16 — Diagnostics re-derivation** *(Partial)*. Public
`quotient_identity_manifest` re-derives gates/targets from `vk.cs()` without
consulting the executed plan; the plan-derived manifest exists but is
`cfg(test)`-only (vm/mod.rs:258-282). Correction: the selector-detection
method is identical to the plan's, not divergent as originally claimed;
`ProofEvaluationCounts` hand-duplicates protocol formulas with a total-sum
assert as the only cross-check. → Proposal P1.5.

**F17 — Test-hygiene trio** *(Confirmed)*. (a) The bit-flip malleation PBT
reaches only the first 512 proof bytes (`bit_idx ∈ 0..4096`, byte 511 max;
the repacked proof is several thousand bytes — the tail G1s/q_evals/π are
never flipped by this test; scalar-sweep tests do cover deeper offsets
structurally). (b) Nine adversarial tests pass vacuously (stderr notice only)
when the accept baseline breaks, via `solidity_output_is_true_or_skip`
(test.rs:3411-3429); a loud variant exists and is used by the malleation
baseline. (c) The PBT runner defaults to 3 cases with
`failure_persistence: None` (test.rs:4295-4306); the two libFuzzer targets
are wired to no workflow. → Proposal P0.1.

### 3.4 Low severity (verified; batch as hygiene)

- **L1** `scalar_inv` scratch registers 0xc0 of the historical 0x100 window;
  the 0x40 gap is unused padding but unregistered/unvalidated
  (memory.rs:700-705).
- **L2** `num_instances` has no sanity bound on the non-accumulator path (an
  absurd value renders a verifier demanding `num_instances*32` bytes of
  calldata); accumulator configs do bound it via the fixed-base tail check.
- **L3** `evm.rs` harness: pervasive documented panics, substring parsing of
  solc's human-readable output (single-contract, trailing-newline
  assumptions), publicly re-exported behind the `evm` feature;
  `Evm::code_size` doc/impl mismatch.
- **L4** Several consistency checks are `debug_assert!`-only and compile out
  in release (diagnostics.rs:18, calldata.rs:127, memory.rs:97-103/277,
  encoding/mod.rs:881/970, protocol/mod.rs:676, kzg/mod.rs:1117-1119);
  `Constants.sol:24` unwraps `expected_quotient_len` inside the
  `expected_quotient_codehash` match arm — safe only via the artifacts.rs
  pairing invariant.
- **L5** The constructor precompile smoke cannot detect a G1MSM
  implementation that omits subgroup checks (its MSM probe is identity-only;
  acknowledged in the file's own comments) — the exact property the
  verifier's soundness delegates to the precompile.
- **L6** Stale NatSpec in the template and every rendered fixture/deployment
  claims generated scratch starts at 0x80; the actual base is 0x1000.
- **L7** Trace renders switch the evaluator staticcall to CALL and drop
  `view` with no structured non-production marker (buried comments only;
  state change limited to LOG1 by the pinned callee).
- **L8** Small duplications/dead code reported by reviewers: `u256_string`
  duplicated verbatim (yul_emit.rs:1175 / vm/mod.rs:4168), two pow5
  recognizers, dead `_quotient_max_stack` binding (quotient.rs:134), empty
  `render/yul.rs`, dead `hex_padded` branch and duplicate `proof_len` check
  in models.rs. (Note: the hardcoded 8/10 accumulator word constants in
  `api.rs` originally reported here turned out to have a tying test —
  `lowering/tests.rs:1692-1707` — and are dropped as a finding.)

## 4. Redesign proposals

Ordered by (leverage ÷ risk). P0 items are small and should land before the
audit; none change verifier semantics. Items marked ⚠ change rendered
bytecode and require regenerating pinned fixtures and the
`REPRODUCIBLE_BUILDS.md` hashes — batch them into one regeneration.

### P0 — Assurance-process fixes (small, high leverage)

**P0.1 Fix CI test selection and skip semantics** *(F1, F17)*.
Enumerate the env-gated EVM tests explicitly in `ci.yaml` (or adopt one
enforced prefix and add a meta-test asserting the filter matches every
`#[test]` in `src/test.rs`); add a post-step check that the executed-test
count is non-zero and matches expectation so a filter regression fails
loudly. Replace `solidity_output_is_true_or_skip` with the existing loud
variant when `HALO2_SOLIDITY_RUN_EVM_TESTS=1` (matching the suite's own
loud-prerequisite philosophy). Draw `bit_idx` from `0..proof_len*8`. Wire the
two libFuzzer targets into a scheduled workflow with a committed corpus; give
the PBT runner a persistence file and a higher default in CI. Move the
slowest tests to the weekly workflow if per-PR time matters — but into *some*
workflow. Fix the misleading CI step comment. *Risk: CI minutes.*

**P0.2 Runtime free-memory-pointer guard + pragma pin** *(F3)* ⚠.
Emit `if gt(mload(0x40), TRANSCRIPT_MPTR) { revert(0, 0) }` as the first
statement of the terminal assembly block in both `Halo2Verifier` and
`Halo2QuotientEvaluator` — via-IR initializes the FMP to the memoryguard
value, so this converts the spill-window assumption into a fail-closed
on-chain check for ~10 gas per proof. Pin the pragma to the audited compiler
(or document why not). Keep the memoryguard host test and run it per-PR
(P0.1). *Risk: minimal; confirm the legacy pipeline also initializes 0x40
before the block (it does).*

**P0.3 Promote by-construction frame checks into `validate()`** *(F5)*.
Move the `AccumulatorPairingBatch`/`FinalPairing` disjointness assertion from
`cfg(test)` into `VerifierMemoryLayout::validate()` so every generation is
gated on it. Cheap, generation-time only.

**P0.4 One documentation-refresh pass with drift guards** *(F6, F15, L6)*.
Correct the `REPRODUCIBLE_BUILDS.md` pinning claim and record the workspace
commit alongside published hashes (the bench script can emit it into
`contract-sizes.txt`); update `src/codegen` paths in the dossier and audit
docs; replace README test counts with the command that produces them; fix
broken links; add status markers to ROADMAP; fix the 0x80 NatSpec ⚠; define a
re-assessment trigger (any change under `src/lowering` or `templates/` bumps
a dated stamp). Guard recurrence with a CI link checker plus a small test
asserting every path cited in `docs/audit` exists. *No code risk; high
audit-readiness leverage.*

### P1 — API contract and performance (small–medium)

**P1.1 Make the lowering pipeline fallible end-to-end** *(F2, F9-adjacent)*.
The leaf validators already return `Result<_, String>`: change
`LoweringPlan::new` to `try_new -> Result<LoweringPlan, GeneratorError>`,
threading through `generate_vk`, `meta_data_for_stable_static_layout`,
model validation, and certification. Introduce an internal error taxonomy
{UnsupportedShape, ResourceLimit, InternalInvariant} carried in
`GeneratorError::Planning` so callers can distinguish rejection classes.
Keep panics only for true internal-invariant bugs, and document them under
`# Panics` on every public method that retains one. Honor the
`reference.rs` contract that certification failures surface as
`GeneratorError`. *Risk: low functionally; moderate churn (~8 modules); keep
the current panic messages as error text.*

**P1.2 Cache one converged plan per generator; decouple repacking** *(F4)*.
Store `OnceCell<Result<Arc<LoweringPlan>, GeneratorError>>` on
`SolidityGenerator` (inputs are already immutable; determinism is pinned by
the repeated-plan test) and route every entry point through it — this also
*structurally* guarantees render/repack/diagnostics agree on one plan instead
of by convention. Additionally derive `RepackedProofLayoutPlan` directly from
`ProofCalldataLayout::from_protocol` + meta counts so per-proof calldata
encoding never needs VK generation or certification at all. *Risk: low.*

**P1.3 Make invalid render states unrepresentable** *(F10, F13, L4)* ⚠.
Collapse `quotient_external` + `expected_quotient_{len,codehash}` into one
`Option<PinnedQuotient { frame, len, codehash }>` model field; delete the
`when None` codehash-free branches from `Constructors.sol` and
`QuotientAndLinearization.yul` (already unreachable; removing them deletes
the hole-shaped text and the template-level `unwrap()`). Seal model
construction behind validating constructors (or have `render()` call
`validate_layout()` first) so an unvalidated model cannot render. *Risk:
none functionally; fixture regeneration.*

**P1.4 Record the feature/build profile in rendered artifacts** *(F12)* ⚠.
Emit a feature-profile constant (bitmask or three booleans + crate version)
and a NatSpec line in `Halo2Verifier.sol`; expose it as a typed field on
`RenderedArtifacts`; include it in the reproducible-builds manifest; surface
it in `RepackError` context so an off-chain repack against the wrong profile
is diagnosable in one step. Consider making `RenderDiagnostics::default()`
feature-independent (breaking change to a documented-intentional behavior —
decide explicitly). Add a CI matrix job compiling + running lib tests under
default features and each outer-* feature alone. *Risk: pinned-hash
regeneration.*

**P1.5 Plan-derived diagnostics only** *(F16)*.
Remove the `cfg(test)` gate on the plan-derived manifest and implement
`quotient_identity_manifest` as `plan.quotient_identity_parts().manifest()`
via the cached plan; derive `ProofEvaluationCounts` from the protocol plan's
per-family counts, keeping the `meta.num_evals` assert as the net. *Risk:
low; output shape already pinned by tests.*

### P2 — Structural improvements (medium–large)

**P2.1 Single operand-layout descriptor + `ValidatedProgram` newtype**
*(F8, F9)*. Define each opcode's operand schema once (typed field sequence:
u8 const-slot, u16 ptr, counted blocks) attached to `QUOTIENT_VM_SPEC`, and
drive the checked length walker, const-slot validator, pointer walker, and
trusted walker from it; render the schema into the template's case
documentation so the Yul reviewer diffs against the same source. Keep
`reference.rs`'s decoder deliberately independent (document that choice — it
is the N-version defense). Add `ValidatedProgram<'a>` constructible only via
`validate_quotient_program`, and make the panicking walkers take it. *Risk:
touches the trusted emission path; land under the existing conformance tests
+ dual-build certification as the net.*

**P2.2 Mechanize the `MemoryPhase` ↔ template-schedule contract** *(F5)*.
Introduce a schedule manifest — a const ordered list of (phase, template
partial, marker) — that (a) the enum order is asserted against and (b) a lib
test extracts from rendered verifier output (per-section markers already
exist in gas-checkpoint form; add a non-feature-gated comment marker) so a
reordered include or misplaced enum variant fails a test instead of silently
disabling overlap detection. Optionally add explicit sub-phase ordering for
the 0x1000 band so its aliasing becomes checkable rather than exempt.

**P2.3 Split the monoliths; move repack types to the ABI boundary** *(F14)*.
Mechanical split of `vm/mod.rs` into `vm/{spec,builder,validate,recognize,
yul_parse}.rs`; move `RepackedProofLayoutPlan` (and friends) to
`lowering/abi/`. Split `kzg::computations` into per-block functions sharing
one linearization-term enumeration source, eliminating the trace/Block-5
duplicate walk. *Risk: low; no output change; pure `pub(crate)` refactor.*

**P2.4 Negative-conformance subgroup probe at deployment** *(L5)* ⚠.
Embed one constant on-curve, non-subgroup G1 point in the constructor smoke
and require the G1MSM staticcall on it to *fail* (optionally a non-subgroup
G2 for the pairing). This makes the deployment gate test the exact rejection
behavior the runtime soundness delegates to the precompile. Generate the
constants once with a Rust-side test proving on-curve ∧ outside r-torsion.
*Risk: slight deployment gas.*

**P2.5 Render-time differential execution of the assembled quotient Yul**
*(§3.2, F7, F11)*. Behind the `evm` feature (or a release-render gate),
execute the rendered quotient block on revm against a memory image generated
from `QuotientRefMemory`'s address-derived assignment and compare `-nu_y(x)`
plus every selector bucket with the reference interpreter. This closes the
reference→Yul leg and covers inline/native/tail identities per artifact
instead of per fixture — converting the two weakest assurance legs into a
render gate. Complements, not replaces, the raw-text template tests (which
should migrate to rendered-output assertions where feasible). *Risk: needs
the EVM harness inside generation (feature-gated); the memory image must
respect the structural constraints native kernels assume — the read-model
windows already describe them.*

**P2.6 Typed statement IR instead of the Yul-string round-trip** *(F7, F10)*
⚠ *(large; do last)*. Extend `QuotientExpr` into a small statement IR
(let-bindings + expression), make `yul_emit::Evaluator` produce it once per
identity, and derive everything from it: (a) one printer to Yul text for
inline/native blocks, (b) direct VM compilation (`emit_expr` already consumes
`QuotientExpr`), (c) limb7 fusion and pow5/helper detection as structural
rewrites/queries. Delete the assignment parser, the textual
`specialize_limb7_chains` matcher, one of the two pow5 recognizers, and the
substring helper-flag scan. This removes the largest class of convention
coupling and the certification blind spot at the parse seam. *Risk: medium —
output text will change, churning fixtures and published hashes; stage with
output-identity checks first, then the P2.5 differential as the semantic
net.*

### P3 — Hygiene batch (small, opportunistic)

Bound `num_instances` sanely at `try_new` (L2); promote the
security-adjacent `debug_assert!`s to `assert!` or `validate()` checks —
codegen is not hot enough to care (L4); register the full `scalar_inv`
0x100 window or update the stale comment (L1); harden `evm.rs` (solc
`--combined-json` output instead of substring parsing, fix the `code_size`
doc, deduplicate the two compile/two run-tx paths) (L3); add a structured
non-production marker to trace renders (contract-name suffix or NatSpec tag)
(L7) ⚠; delete the small duplications/dead code (L8).

## 5. Suggested sequencing

1. **Week 1 (audit-readiness):** P0.1–P0.4. Nothing here changes semantics;
   P0.2 and the NatSpec fix change bytecode — do one coordinated fixture/hash
   regeneration.
2. **Next:** P1.2 (caching — smallest high-value code change), then P1.1
   (Result threading) since its churn benefits from the single cached entry
   point; P1.3–P1.5 ride the same fixture regeneration as P0.2.
3. **Then:** P2.1–P2.4 in any order (independent); P2.5 before P2.6 so the
   IR migration lands under a per-render semantic differential.

## 6. Verification note

This assessment was produced by automated review with per-finding
adversarial re-verification against the source; corrections discovered
during that pass are recorded inline. Findings describe the snapshot above.
Review the accuracy and completeness of both documents against the current
tree before relying on them — responsibility for verification remains with
the reader.

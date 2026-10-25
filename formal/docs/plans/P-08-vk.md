# P-08 - Midfall.Generator.Vk (port of lowering/vk.rs)

Status: DRAFT - blocked on P-07 (kzg) because vk.rs imports `lowering::kzg`.
Depends on: P-05 (encoding: Data, Ptr, fe_to_u256, g1_to_u256s, g2_to_u256s,
ConstraintSystemMeta), P-05 (abi: ProofCalldataLayout, TranscriptBufferLayout), P-06
(api: AccumulatorEncoding, GeneratorConfig), P-07 (kzg), layout, models.
Unblocks: P-11 (plan), and the `Supported.vkPoints` field of PLAN 9.5.

Reference: `proofs/solidity-verifier/src/lowering/vk.rs`, 654 lines.
Lean target: `formal/Midfall/Generator/Vk.lean`.

**Also in scope:** `VerifierBuildInputs` at `lowering/mod.rs:38-45` - an 8-line struct
(params, vk, num_instances, num_committed_instances, acc_encoding, meta) that every
method in vk.rs is defined on, and that P-11 and P-12 also need. Port it here rather
than waiting for the `mod.rs` row, and say in the header that it landed early.

## Item map

| range | item | note |
|---|---|---|
| 37-48 | `srs_tau_is_consistent` | pairing check e([tau]G1, G2) = e(G1, s_g2) |
| 50-70 | `srs_tau_commitment` | Pippenger `multi_exp` over up to 2^20 points |
| 73-93 | `VerifierBuildInputs::srs_fingerprint` | Keccak over n, G2 base, s_g2, [tau]G1; feeds BUILD_ID |
| 95-307 | `generate_base_vk` | the bulk, 212 lines |
| 308-357 | `generate_vk_direct` | |
| 359-435 | `generate_vk` | assert at 436: quotient const table vs VK payload reservation |
| 475-529 | `meta_data_for_vk` | |
| 531-548 | `meta_data_for_stable_static_layout` | pub(super) |
| 550-561 | `memory_layout_for` | pub(super) |
## Hazards - each must be answered in the report

1. **`srs_tau_commitment` runs a Pippenger `multi_exp` over up to 2^20 points**
   (the comment says production SRS sizes reach 2^20 and a naive per-point mul
   "would stall every build"). PLAN 13 already flags Lean performance at k=20 as a
   risk. Decision required and to be stated in the header: port the **semantics**
   (a sum over the Lagrange-basis commitment of f(X)=X), gate it at small sizes only,
   and say plainly that it is never evaluated at production size. Do not port Pippenger
   for its own sake - R1 forbids improvements, but it also does not require porting a
   performance data structure whose observable behaviour is the group element it
   computes. Whichever way you go, record the choice and why.
2. **`omega_powers` is built by a mutating accumulator** (`omega_pow *= omega` inside a
   `map` over a captured `mut`), yielding [1, omega, omega^2, ...]. A port using
   `omega ^ i` computes the same list and is *not* the same program. R1 says mirror it;
   gate the first several entries and the length, and note the equivalence rather than
   silently substituting.
3. **`srs_tau_is_consistent` is a Phase 4 lemma wearing a port's clothes.** It asserts
   e([tau]G1, G2) = e(G1, s_g2) where [tau]G1 is recomputed from the Lagrange basis.
   Under D-P1 the pairing is the abstract `AdmissiblePairing`, so the def is easy and
   the *content* is: for an honestly generated SRS, the Lagrange-basis commitment of
   f(X)=X equals tau*G1. That belongs in `Midfall/Halo2/Spec/Lemmas.lean` as the fourth
   Phase 4a entry (it needs the Lagrange closed forms, which are also owed). Port the
   def here; **file the lemma as a separate task** and say so in the report - do not
   quietly drop it.
4. **`srs_fingerprint` is a Keccak preimage that feeds BUILD_ID** (misc-fixes 10,
   P10/L-8). Its byte layout is load-bearing and externally comparable: the deployed
   artifact carries a BUILD_ID. Gate the exact preimage bytes for a small hand-built
   params, and cross-check the field order the doc names (n, G2 base, s_g2, [tau]G1).
   If the order or the encodings are ambiguous in the Rust, that is a finding.
5. **The assert at vk.rs:436** ("quotient const table exceeded VK payload reservation")
   is an R4 panic site and is also a `Supported`-shaped invariant. Port the panic and
   note in the report that PLAN 9.5's `Supported` has no field for it yet - that is a
   statement-surface question for the orchestrator, not something to invent locally.
6. **Owed deferred work lands here.** `Models.lean` explicitly deferred
   `payload_layout` (M:344-378) and `validate_payload_layout` (M:381-399) because
   `VkPayloadLayout` and `PayloadSectionKind` did not exist. P-03 (Layout) has now
   landed both. So P-08 must either port those two functions or state precisely why
   they still cannot be ported. Leaving them deferred without re-examining them is the
   R-40 F3 pattern (a deferral that outlives its reason).
7. **`generate_base_vk` is 212 lines** and is where the VK payload is actually
   assembled - constants, fixed commitments, permutation commitments, theta, the
   quotient const table. It touches Layout.lean's `VkPayloadLayout` (P-03) and
   Models.lean's `Halo2VerifyingKey`. Expect the real divergences here: check that the
   section order the payload is written in matches the layout P-03 computes, and gate
   the byte offsets, not just the counts.

## Acceptance

Standard package acceptance (PLAN section 4; `lake build` and `scripts/checks.sh`
green; per-gate perturbation actually run; non-vacuity shown). Plus: at least one gate
pinning the *ordering* of VK payload sections against `VkPayloadLayout`, since a count
check cannot see a swap.

| 563-601 | `static_working_memory_size_for_meta` | private |
| 603-609 | `transcript_buffer_words_bound` | |
| 611-654 | `transcript_buffer_layout_for_meta` | pub(super) |

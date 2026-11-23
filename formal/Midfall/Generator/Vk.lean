-- |
-- Midfall.Generator.Vk
--
-- Verifying-key payload generation for a concrete verifier build: a port of
-- proofs/solidity-verifier/src/lowering/vk.rs (654 lines at git HEAD, verified
-- clean against the working copy) plus VerifierBuildInputs from
-- proofs/solidity-verifier/src/lowering/mod.rs:37-45 (51 lines at HEAD), which
-- every method in vk.rs is defined on.
--
-- TWO ITEMS LANDED EARLY, both recorded rather than hidden.
--
-- * VerifierBuildInputs (MOD:37-45) belongs to the mod.rs row of plan Section 8,
--   which has not fired. It lands here because all twelve items of vk.rs are
--   methods on it and there is nowhere else to put them.
-- * The VK header schema block (LM:396-665: VkHeaderSlot, VkHeaderFieldSpec,
--   VK_HEADER_FIELDS, VkHeaderLayout, VkHeaderBuilder) belongs to the Layout row,
--   which P-03 did NOT port: Layout.lean took the five header WIDTH constants
--   (LM:390-401, ported as vkHeaderScalarWords / vkHeaderG1BaseWord /
--   vkHeaderG2BaseWord / vkHeaderNegSG2BaseWord / vkHeaderWords) and stopped
--   there. generate_base_vk is the block's only consumer in the tree so far, and
--   without it the 212-line body of VK:95-299 cannot be written at all, so the
--   block is ported here and should move to Layout.lean when the LM row is
--   revisited. Cross-package finding F-P08-1.
--
-- CITATION NOTATION. Every prefix names its file and its line count at HEAD,
-- because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites that
-- silently pointed at the wrong file or at a declaration that does not exist.
-- Every range below was re-derived from git show HEAD:<path>, never from wc -l on
-- a checkout (docs/plans/README.md standing note; the working copy is clean for
-- all twelve files below, checked with git status --porcelain and not assumed).
--
-- * VK:   proofs/solidity-verifier/src/lowering/vk.rs (654 lines at HEAD) - the
--   file this module ports.
-- * MOD:  proofs/solidity-verifier/src/lowering/mod.rs (51 lines at HEAD) -
--   VerifierBuildInputs at MOD:37-45.
-- * LM:   proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines at HEAD)
--   - the VK header schema block LM:396-665 and the fixed addresses the memory
--   bound reads.
-- * VP:   proofs/solidity-verifier/src/lowering/layout/vk_payload.rs (322 lines at
--   HEAD) - VkPayloadLayout and PackedProgramCodec, ported in Layout.lean.
-- * MEM:  proofs/solidity-verifier/src/lowering/layout/memory.rs (1603 lines at
--   HEAD) - VerifierMemoryLayout and its config, ported in Layout.lean.
-- * ENC:  proofs/solidity-verifier/src/lowering/encoding/mod.rs (940 lines at
--   HEAD) - ConstraintSystemMeta, Data, Ptr, Word, fe_to_u256, g1_to_u256s,
--   g2_to_u256s, ported in Encoding.lean.
-- * M:    proofs/solidity-verifier/src/lowering/render/models.rs (1494 lines at
--   HEAD) - Halo2VerifyingKey, ported in Models.lean.
-- * AP:   proofs/solidity-verifier/src/lowering/abi/proof.rs (537 lines at HEAD) -
--   ProofCalldataLayout and TranscriptBufferLayout, ported in Abi.lean.
-- * KZ:   proofs/solidity-verifier/src/lowering/kzg/mod.rs (2226 lines at HEAD) -
--   num_dummy_queries KZ:1271, num_point_sets KZ:940, static_working_memory_size
--   KZ:1282, ported in Kzg.lean.
-- * PRM:  proofs/src/poly/kzg/params.rs (382 lines at HEAD) - ParamsKZG PRM:19-24
--   and its three accessors PRM:166-178.
-- * QRS:  proofs/solidity-verifier/src/lowering/quotient.rs (2147 lines at HEAD) -
--   the three methods generate_vk calls: compact_quotient_program_for QRS:165-181,
--   quotient_program_plan QRS:425-430, build_quotient_program_items QRS:2101-2110.
-- * QVM:  proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs
--   (4336 lines at HEAD) - QuotientProgramBuild QVM:118-137, QuotientProgramPlan
--   QVM:324-340.
-- * QDIR: proofs/solidity-verifier/src/lowering/quotient_numerator/direct/mod.rs
--   (1341 lines at HEAD) - TableWord QDIR:334-340 and table_words QDIR:653.
--
-- WHAT THIS FILE DOES NOT PORT, AND WHY.
--
-- * The four callees that belong to rows that have not fired. memory_layout_for
--   ends in VerifierMemoryLayout::new (MEM:591-973), which Layout.lean explicitly
--   declined (Layout.lean:716-721) and which is 383 lines of arena planning;
--   generate_vk calls three quotient.rs methods whose return types live in
--   quotient_numerator/vm/mod.rs, the P-09 row; generate_vk_direct takes a
--   DirectQuotientProgram (QDIR) and reads exactly one accessor off it. Rather
--   than drop the five vk.rs items that call them - which would have dropped
--   hazard 5's panic with them - the callees enter as the explicit fields of
--   VkBuildEnv and are threaded to every def that needs one. The Rust reaches them
--   through &self; the port reaches them through one extra argument, and each site
--   says so. Their bodies are NOT invented: VkQuotientBuild carries only the two
--   fields vk.rs reads (QVM:120 bytes, QVM:122 consts) and the plan is an abstract
--   type parameter, because vk.rs never inspects plan.items or plan.selector_fold
--   beyond handing them to build_quotient_program_items (VK:452-455).
-- * The params.g field of ParamsKZG (PRM:20). vk.rs cannot read it - the field is
--   pub(crate) to the proofs crate and VK:132-135 says so out loud, which is why
--   the reference reconstructs the G1 base from g_lagrange instead - so the Lean
--   ParamsKZG carries the three fields the three accessors return and no fourth.
--   Recorded as a narrowing, not a rename.
-- * #[cfg(test)] mod tests: vk.rs has none. The one #[cfg(test)] item in the file
--   is transcript_buffer_words_bound (VK:601-608), which is in the plan's item map
--   and is ported and marked test-only at its site.
-- * The derives of MOD:37 (Clone, Copy, Debug). Clone and Copy are Lean's value
--   semantics and Debug is not ported anywhere in this row, so VerifierBuildInputs
--   carries no derive.
--
-- THE THREE PLAN HAZARDS ABOUT THE GROUP, AND WHAT WAS DONE.
--
-- 1. srs_tau_commitment (VK:50-62) runs a Pippenger multi_exp over up to 2^20
--    points. THE SEMANTICS ARE PORTED, NOT THE ALGORITHM: srsTauCommitment is the
--    scalar-weighted sum of omega^i over g_lagrange[i], folded from the identity
--    left-to-right. Pippenger is a performance data structure whose observable
--    behaviour is the group element it computes; the group here is abelian
--    (ArkLib's PrimeOrder gives IsCyclic at
--    .lake/packages/ArkLib/ArkLib/Data/GroupTheory/PrimeOrder.lean:32, and
--    IsCyclic gives CommGroup at :35), so even the fold order cannot be observed.
--    It is NEVER evaluated at production size: the gates run it at n = 4 and 8.
--    Stated here because the plan asked for the decision and because a reader who
--    looks for the bucket decomposition should know its absence is deliberate.
-- 2. omega_powers (VK:53-60) is built by a MUTATING accumulator - omega_pow starts
--    at Fq::ONE, each step yields the current value and then multiplies - and the
--    port mirrors that shape: omegaPowers folds a pair (accumulator, output) and
--    yields the accumulator BEFORE the update, which is VK:56-58. omega ^ i would
--    compute the same list and is a different program, so it is not used; the
--    equivalence is asserted by omegaPowers_accumulatorEquivalence_ok rather than
--    assumed.
-- 3. srs_tau_is_consistent (VK:37-44) is a Phase 4a lemma wearing a port's
--    clothes. The DEF is ported. Its content - for an honestly generated SRS the
--    Lagrange-basis commitment of f(X) = X is tau * G1 - is NOT proved here and
--    cannot be proved in this tree today: see R-47 (docs/REVIEW.md:1553-1588).
--    FieldConsts F (Exec/Arith.lean:64-72) is four bare data fields with no
--    hypothesis that rootOfUnity is a primitive 2^S-th root of unity, and
--    EvaluationDomain (Exec/Domain.lean:55-83) carries omega : F with no
--    hypothesis that it has order exactly n. So the lemma is not merely unproved,
--    it is not STATABLE as the plan wants it: what is missing is a named
--    hypothesis structure (plans/P-4a-roots.md's FieldConsts.IsWellFormed, or an
--    EvaluationDomain.IsPrimitive variant) asserting omega ^ n = 1 AND
--    (0 < i < n -> omega ^ i <> 1) for the domain being committed over, plus the
--    Lagrange closed form L_i(x) = (x^n - 1) / (n * omega^-i * (x - omega^i))
--    that nothing in Spec/Lemmas.lean states yet. Filed as F-P08-2. The gate
--    srsTauIsConsistent_honestSrs_ok stands in for it the only way a gate can: on
--    one concrete domain (n = 4 over Fr 17) where the root property was checked by
--    hand, with a false case built by substituting a different tau, so the gate
--    cannot pass vacuously.
--
-- PORT RULES AS THEY APPLY HERE (plan Section 4, R1-R11).
--
-- * R1 order. The Rust's order is kept except for the moves marked at each site
--   and listed at the end of this header.
-- * R2 names. meta is a Lean command modifier and cannot even be a let binder, so
--   the VerifierBuildInputs FIELD meta is meta_ and every Rust parameter or local
--   named meta is meta_ - the convention Encoding.lean:610-613 and Kzg.lean
--   record. That is an R2 exception at eight sites: the field (MOD:44),
--   metaDataForVk, metaDataForStableStaticLayout, memoryLayoutFor,
--   staticWorkingMemorySizeForMeta, transcriptBufferLayoutForMeta,
--   transcriptBufferWordsBound and the local at VK:504.
-- * R4 panics. The reference profile is release (docs/BASELINE.md), so overflow
--   does NOT panic, and vk.rs contains no debug_assert! at all (checked: the
--   string debug_assert does not occur in the file). What does panic in both
--   profiles and is ported as a Fault.panic: the three SRS asserts at VK:151,
--   VK:180, VK:189, the reservation non-convergence panic at VK:395-399, the
--   payload asserts at VK:343, VK:414, VK:420, VK:426, VK:436, VK:438, VK:457,
--   VK:461, the unwrap/expect sites at VK:112, VK:211-264, VK:286, VK:323, VK:327,
--   VK:333, VK:407, VK:410, VK:413, VK:417, VK:422, VK:470, VK:546, VK:598, and the
--   two direct vk.constants[..] writes at VK:444 and VK:447. Fault.panic carries a
--   site and no payload (docs/REVIEW.md R-43 F2), so the reference's formatted
--   messages - "invalid VK header layout: {err}", "did not converge after 8
--   iterations: const_words=..., program_words=..." - are lost. That is F-P08-3;
--   the sites stay distinct, which is the most this surface can do.
-- * R5 integers. usize is Nat, u64 is Nat, i32 stays Int (rotation_last is signed
--   and VK:116's unsigned_abs is Int.natAbs). 1u64 << k (VK:112) panics for
--   k >= 64 in both profiles; unreachable for a real domain (k <= F::S = 32) and
--   stated at the site.
-- * R6 collections. Vec and &[T] are List, following the Generator row rather than
--   PLAN R6's literal "Array" (docs/REVIEW.md R-43 F5). The header builder's
--   Vec<Option<(&'static str, U256)>> is a List (Option (String x Word256)).
-- * R7 curve. There is no concrete BLS12-381 in this tree (design decision D-P1),
--   so group elements enter on the abstract AdmissiblePairing surface every Exec
--   statement already uses, and G1Projective vs G1Affine COLLAPSE: one carrier, so
--   every .to_affine() in vk.rs is the identity here and the to_affine closure of
--   VK:269 is a comment rather than a function. That is a recorded divergence, not
--   a silent one. Field elements enter as Fr p and leave through frToRepr
--   (Common/Codec.lean:32) into feToU256, which is the Fq::to_repr plus
--   U256::from_le_bytes pair ENC:904-915 models. Points reach g1ToU256s /
--   g2ToU256s through VkPointCodecs, the bridge below: the tree has no G1Affine to
--   project from, and Encoding.lean:917-942 already states that a point enters a
--   port as "exactly the data the function inspects".
--   One extra binder is needed and recorded: AdmissiblePairing carries
--   decEqG1 and decEqGt but NOT a decidable equality on G2 (Common/Curve.lean:65-66
--   explains why only those two are fields), and VK:180 compares two G2 elements.
--   Rather than edit the frozen class this file takes [DecidableEq G2] as a binder.
-- * R8 features. VK:505 is cfg!(feature = "outer-fewer-point-sets"), ported as a
--   runtime branch on the Features record (Exec/Features.lean:17), both arms
--   ported and both gated - the treatment Kzg.lean:144-155 records for the branch
--   that reads the vector this one fills. Features.solidity has it FALSE
--   (BASELINE.md), so the zero arm is the deployed one.
-- * R10. Everything here is computable: no partial, no unbounded loop. The two
--   bounded Rust loops (for _ in 0..3 at VK:537, for _ in 0..8 at VK:367) are
--   List.range folds with an early-exit flag, the pattern Abi.lean:535 sets.
--
-- THE TWO LANDMINES P-08 INHERITS (plans/P-08-vk.md, "Added after P-07R").
--
-- 1. LayoutKats.verifierLayoutFixture has every PCS base at 0, so point-comparison
--    gates pass vacuously on it (docs/REVIEW.md R-48). HANDLED BY BUILDING A
--    FIXTURE, not by editing the shared one: VkKats.memV overrides the same seven
--    bases Kzg.lean's memF overrides, and every gate that compares points asserts
--    pairwise distinctness first (fixturePointsDistinct_ok,
--    payloadOrder_sectionsTiled_ok). The shared fixture is untouched, exactly as
--    R-48's deliberate non-fix requires.
-- 2. valueBeq / locationBeq / ptrBeq / wordBeq already exist twice
--    (Encoding.lean:1083-1094 and Kzg.lean:260-277). This file needed pointer
--    comparisons and was about to add a third copy - at which point the brief says
--    to stop and add deriving BEq to Location, Value and Ptr instead. It turned out
--    to be unnecessary: Kzg.lean's four comparators are declared at the top level
--    of namespace Midfall.Generator, so importing Kzg.lean - which this file must
--    do anyway for numDummyQueries - brings them into scope. NO THIRD COPY WAS
--    ADDED and no foreign file was edited. Recorded so a reviewer can confirm the
--    count is still two.
--
-- FINDINGS THIS PACKAGE PRODUCES (full text in the package report; named here so a
-- reader of the file meets them where they belong).
--
-- * F-P08-1 the VK header schema block is the Layout row's content and landed here
--   out of necessity; it should move to Layout.lean.
-- * F-P08-2 hazard 3's lemma is not merely unproved, it is not STATABLE: what is
--   missing is a named hypothesis that the domain's omega has order exactly n (the
--   R-47 gap) plus the Lagrange closed form
--   L_i(x) = (x^n - 1) / (n * omega^-i * (x - omega^i)) and the two identities
--   sum_i L_i(x) = 1 and sum_i omega^i * L_i(x) = x. Owner: plans/P-4a-roots.md.
-- * F-P08-3 R-43 F2 recurs: Fault.panic carries no payload, and vk.rs is the worst
--   offender so far because its abort messages carry the numbers an operator needs
--   ("const_words=..., program_words=..."). Twelve distinct messages, twelve sites,
--   no payloads.
-- * F-P08-4 SIX of the asserts in generate_vk and generate_vk_direct cannot fire on
--   any input: VK:414, VK:420, VK:426, VK:436, VK:438 and VK:343 each restate the
--   reservation loop's own break condition (VK:384-386) or compare
--   VkPayloadLayout::for_vk's output against the quantity it was built from. They
--   are guards against a future change to the layout code, not checks on the input.
--   Hazard 5's panic is one of them. All are ported per R1 and R4; the evidence is
--   generateVk_hazard5_ok, which asserts that the attempted perturbation fires
--   VK:461 instead.
-- * F-P08-5 Layout.lean:716-721 declines VerifierMemoryLayout::new because
--   ConstraintSystemMeta and VerifierMemoryLayoutConfig "do not exist in this tree
--   yet". Both do now (Encoding.lean:364, Layout.lean:970). The deferral has outlived
--   its stated reason - the R-40 F3 pattern - and it is why memory_layout_for had to
--   be threaded through VkBuildEnv.
-- * F-P08-6 Models.lean:40-42 still lists payload_layout (M:344-378) and
--   validate_payload_layout (M:381-399) under "WHAT THIS PACKAGE DOES NOT PORT", but
--   P-03 landed both as Layout.lean:665-692 and :696-709 with eight gates. Hazard 6
--   was therefore already discharged before this package fired; the stale note is the
--   R-46 pattern and belongs to the Models row.
-- * F-P08-7 the item map in plans/P-08-vk.md gives line ranges that are off for nine
--   of the twelve items at HEAD (generate_base_vk is 95-299, not 95-307; generate_vk
--   is 359-472, not 359-435; meta_data_for_vk is 475-523, not 475-529;
--   transcript_buffer_words_bound is 601-608, not 603-609; and so on). The one range
--   the plan cites in prose - the assert at 436 - is correct. R11 checklists are
--   checked against these numbers, so the plan should be corrected.
-- * F-P08-8 VK:546's non-convergence panic is ported but NO stub in this file can
--   reach it, and three different attempts are recorded (see the section above the
--   R11-evidence gates) rather than quietly dropped. The reason is structural: the
--   plan can only move through num_point_sets, and num_point_sets is invariant under
--   the address shifts a planner stub can produce.
-- * F-P08-9 hazard 5's statement-surface question: PLAN 9.5's Supported has no field
--   for the "const table within reservation" invariant. Reported, not invented.
-- * F-P08-10 landmine 2 did not fire: no third copy of valueBeq / ptrBeq was needed,
--   because Kzg.lean declares them at the top level of Midfall.Generator and this
--   file imports Kzg anyway. The count stays at two and no foreign file was edited.
--
-- PERTURBATION CAMPAIGN (R-41's rule, actually run). Thirty perturbations were
-- applied one at a time to this file and to Layout.lean, each followed by a rebuild
-- and a byte-for-byte restore check; the harness is /tmp/perturb*.js in the session
-- and the per-gate results are in the package report. Twenty-four reddened at least
-- one gate. SIX did not, and each is a fact rather than an oversight: the n_inv /
-- omega fixture coincidence (F noted at generateBaseVk_header_ok), the finish index
-- equivalence (F noted at VkHeaderBuilder.finish), the multi_exp argument-order
-- swap being unrepresentable, the stable-layout loop bound 3 -> 2, the
-- pairing-batch term of the memory bound (dominated), and the six unreachable
-- asserts of F-P08-4.
--
-- MOVES FROM RUST ORDER (each also marked at its site).
--
-- * srs_tau_commitment (VK:50-62) before srs_tau_is_consistent (VK:37-44), which
--   calls it at VK:42.
-- * The six-item cluster VK:549-653 (transcript_buffer_layout_for_meta,
--   static_working_memory_size_for_meta, transcript_buffer_words_bound,
--   memory_layout_for, meta_data_for_vk, meta_data_for_stable_static_layout) moves
--   above generate_vk (VK:359-472), which calls the last of them. Within the
--   cluster transcript_buffer_layout_for_meta comes first because the other five
--   reach it; the rest keep the Rust's relative order.
-- * VkHeaderLayout::builder (LM:559-562) after VkHeaderBuilder::new (LM:571-577),
--   which it calls.
-- * VerifierBuildInputs, ParamsKZG and the scaffolding records come first, because
--   every method in the impl block takes the struct.

import Midfall.Generator.Kzg
import Midfall.Generator.Api
import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Keccak
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.VerifyingKey

namespace Midfall.Generator
open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]
  [DecidableEq G₂]
  {Plan : Type}

/-! ## Lean scaffolding, not Rust items -/

/-- R4's rendering of Result::unwrap / unwrap_or_else(|err| panic!(..)) on an
    Except String value: the error channel becomes a panic at the CALLER's line,
    because that is where the reference aborts. Fault.panic carries a site and no
    payload (R-43 F2), so the Rust's formatted message is dropped - finding
    F-P08-3. Lean scaffolding, not a Rust item. -/
def unwrapAt {α : Type} (site : String) (e : Except String α) : Except Fault α :=
  match e with
  | .ok a => .ok a
  | .error _ => .error (Fault.panic site)

/-- itertools::max([...]).unwrap() (VK:577-598). The array has a statically known
    six elements so the Option can never be none, but the unwrap is a real Rust
    line, so the port keeps the Option and the caller keeps the site. Scaffolding,
    not a Rust item. -/
def natMaximum : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl (fun a b => max a b) x)

/-- The bridge the abstract-curve model needs (R7): the two projections
    g1_to_u256s and g2_to_u256s read their point off, expressed as functions rather
    than as a hard-coded curve. Not a Rust item - in the reference these are
    inherent methods on G1Affine / G2Affine, which this tree has no type for. -/
structure VkPointCodecs (G₁ G₂ : Type) where
  /-- G1Affine::coordinates() + is_identity(), i.e. ENC:835-859's input. -/
  g1Repr : G₁ → G1AffineRepr
  /-- G2Affine::coordinates() + is_identity(), i.e. ENC:867-901's input. -/
  g2Repr : G₂ → G2AffineRepr

/-- rust: PRM:19-24 (struct ParamsKZG<E>) plus its three accessors PRM:166-168
    (g_lagrange), PRM:171-173 (g2), PRM:176-178 (s_g2), as vk.rs uses them.
    NARROWED, recorded: the Rust has a fourth field g: Vec<E::G1> (PRM:20) which
    vk.rs cannot read - VK:132-135 says the field is crate-private and that is why
    the reference reconstructs the G1 base from g_lagrange at VK:146-150 instead -
    so it is absent here rather than faked. -/
structure ParamsKZG (G₁ G₂ : Type) where
  /-- PRM:21 + PRM:166-168: g_lagrange(), the Lagrange-basis G1 powers. -/
  gLagrange : List G₁
  /-- PRM:22 + PRM:171-173: g2(). -/
  g2 : G₂
  /-- PRM:23 + PRM:176-178: s_g2(). -/
  sG2 : G₂

/-- rust: MOD:37-45 (struct VerifierBuildInputs) @formal-baseline. LANDED EARLY:
    this is the mod.rs row's item, ported here because every method in vk.rs is
    defined on it (plans/P-08-vk.md, "Also in scope"). All six fields in the Rust's
    order. The two lifetimes 'params / 'meta are Lean value semantics and vanish.
    params is the prover SRS, not ParamsVerifierKZG, because VK:76 reads
    g_lagrange() off it, which the verifier subset does not carry
    (Exec/Kzg/Params.lean:15-17 notes exactly that absence).
    num_committed_instances (MOD:42) is carried and never read in vk.rs; it is
    present for the same reason the Rust has it - the struct is one type, not a
    per-consumer projection.
    R2 DEVIATION, recorded: the Rust field is meta (MOD:44) and meta is a Lean
    command modifier, so the field is meta_. -/
structure VerifierBuildInputs (p : ℕ) (G₁ G₂ : Type) where
  /-- MOD:39: params: &'params ParamsKZG<Bls12>. -/
  params : ParamsKZG G₁ G₂
  /-- MOD:40: vk: &'params VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>. Under
      rule R9's KZG instantiation that is Exec's VerifyingKey (Fr p) G₁
      (Exec/VerifyingKey.lean:41-57), the same six fields in the same order, so no
      parallel copy is invented here. -/
  vk : VerifyingKey (Fr p) G₁
  /-- MOD:41: num_instances: usize. -/
  numInstances : Nat
  /-- MOD:42: num_committed_instances: usize. -/
  numCommittedInstances : Nat
  /-- MOD:43: acc_encoding: Option<AccumulatorEncoding>. The GENERATOR's
      AccumulatorEncoding (Api.lean:413-426), not the Exec stand-in
      (Exec/Accumulator.lean:180-189): design decision D-P16 point 1 says the
      generator config field means the faithful one. -/
  accEncoding : Option Midfall.Generator.AccumulatorEncoding
  /-- MOD:44: meta: &'meta ConstraintSystemMeta. Renamed meta_ per R2. -/
  meta_ : ConstraintSystemMeta

/-- rust: QVM:118-137 (struct QuotientProgramBuild) as vk.rs reads it. vk.rs
    touches exactly two of its five fields: bytes (QVM:120, read at VK:382,
    compared at VK:457) and consts (QVM:122, read at VK:380, compared at VK:461).
    max_stack, used_ops and used_mem_tokens are not read here, so they are not
    modelled: P-09 owns the full record and this projection should become an alias
    of it when it lands. Named with a Vk prefix on purpose - the Rust's name would
    collide with P-09's in the shared Midfall.Generator namespace. -/
structure VkQuotientBuild where
  bytes : Bytes
  consts : List Word256

/-- rust: QDIR:334-340 (struct TableWord) as generate_vk_direct reads it:
    value (QDIR:335, VK:315), label (QDIR:337, VK:336), headers (QDIR:339,
    VK:340-342). Same naming note as VkQuotientBuild. -/
structure VkTableWord where
  value : Word256
  label : String
  headers : List String

/-- Lean-side scaffolding, NOT a Rust item: the four callees vk.rs reaches through
    &self that this tree has not ported (see the header). The Rust resolves them as
    methods on VerifierBuildInputs; the port passes them in, which is the same
    relation spelled as data instead of as a trait. Plan is abstract because vk.rs
    never looks inside the plan: it takes plan.items and plan.selector_fold
    (VK:453-454) and hands them straight to build_quotient_program_items, so the
    pair travels as one opaque value. -/
structure VkBuildEnv (Plan : Type) where
  /-- MEM:591-973 (VerifierMemoryLayout::new), declined by Layout.lean:716-721.
      Infallible in the Rust, so no Except. -/
  newVerifierMemoryLayout :
    ConstraintSystemMeta → Halo2VerifyingKey → Ptr → VerifierMemoryLayoutConfig →
      VerifierMemoryLayout
  /-- QRS:165-181 (compact_quotient_program_for). The Rust returns
      (QuotientProgramBuild, Vec<usize>) and VK:379 destructures it as
      let (candidate, _), discarding the second component, so only the build is
      carried. -/
  compactQuotientProgramFor :
    ConstraintSystemMeta → Data → Except Fault VkQuotientBuild
  /-- QRS:425-430 (quotient_program_plan). -/
  quotientProgramPlan : ConstraintSystemMeta → Data → Except Fault Plan
  /-- QRS:2101-2110 (build_quotient_program_items), whose two Rust arguments
      (items, selector_fold) are the opaque Plan above. -/
  buildQuotientProgramItems : Plan → Except Fault VkQuotientBuild

/-- rust: VK:273 and VK:278, the |[a, b, c, d]| destructuring of a g1_to_u256s
    result into the 4-tuple M:28 calls G1Words. Scaffolding because Lean cannot
    write an irrefutable array pattern over a List. The fallback arm is the case the
    reference cannot express: g1ToU256s returns exactly four words (ENC:857-859,
    pinned by Encoding.lean's g1ToU256s_generator_ok), so the arm is unreachable,
    and it panics at VK:273 rather than defaulting, because R4 does not let a port
    soften a panic site. -/
def vkG1WordsOf (ws : List Word256) : Except Fault G1Words :=
  match ws with
  | [a, b, c, d] => Except.ok { xHi := a, xLo := b, yHi := c, yLo := d }
  | _ => throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:273")

/-! ## The VK header schema block (rust: LM:396-665)

LANDED EARLY from the Layout row; see the header. The five width constants it
depends on are already in Layout.lean (LM:390-401), so this block sits after the
scaffolding and before generate_base_vk, which is its only consumer. -/

/-- rust: LM:404-435 (enum VkHeaderSlot, #[repr(usize)]) @formal-baseline. The
    discriminants are explicit in the Rust, so - following the precedent
    Layout.lean:747-756 sets for ThetaSlot - they are ported as an explicit table
    in VkHeaderSlot.word and not as Lean's implicit constructor order. -/
inductive VkHeaderSlot
  /-- LM:408: VkDigest = 0. -/
  | vkDigest
  /-- LM:410: NumInstances = 1. -/
  | numInstances
  /-- LM:412: K = 2. -/
  | k
  /-- LM:414: NInv = 3. -/
  | nInv
  /-- LM:416: Omega = 4. -/
  | omega
  /-- LM:418: OmegaInv = 5. -/
  | omegaInv
  /-- LM:420: OmegaInvToL = 6. -/
  | omegaInvToL
  /-- LM:422: HasAccumulator = 7. -/
  | hasAccumulator
  /-- LM:424: AccOffset = 8. -/
  | accOffset
  /-- LM:426: NumAccLimbs = 9. -/
  | numAccLimbs
  /-- LM:428: NumAccLimbBits = 10. -/
  | numAccLimbBits
  /-- LM:430: G1Base = VK_HEADER_G1_BASE_WORD. -/
  | g1Base
  /-- LM:432: G2Base = VK_HEADER_G2_BASE_WORD. -/
  | g2Base
  /-- LM:434: NegSG2Base = VK_HEADER_NEG_S_G2_BASE_WORD. -/
  | negSG2Base
  deriving BEq

/-- rust: LM:437-442 (VkHeaderSlot::word, self as usize) @formal-baseline, read
    against the explicit discriminants of LM:408-434 and the three derived
    constants LM:397-401. -/
def VkHeaderSlot.word : VkHeaderSlot → Nat
  | .vkDigest => 0
  | .numInstances => 1
  | .k => 2
  | .nInv => 3
  | .omega => 4
  | .omegaInv => 5
  | .omegaInvToL => 6
  | .hasAccumulator => 7
  | .accOffset => 8
  | .numAccLimbs => 9
  | .numAccLimbBits => 10
  | .g1Base => vkHeaderG1BaseWord
  | .g2Base => vkHeaderG2BaseWord
  | .negSG2Base => vkHeaderNegSG2BaseWord

/-- rust: LM:448-456 (struct VkHeaderFieldSpec) @formal-baseline. -/
structure VkHeaderFieldSpec where
  /-- LM:451: slot: VkHeaderSlot. -/
  slot : VkHeaderSlot
  /-- LM:453: name: &'static str - widened to String, the same widening
      ENC:611-616 records for Value::Identifier. -/
  name : String
  /-- LM:455: width_words: usize. -/
  widthWords : Nat
  deriving BEq

/-- rust: LM:459-530 (const VK_HEADER_FIELDS: [VkHeaderFieldSpec; 14])
    @formal-baseline. Fourteen rows in the Rust's order; the three point rows take
    their widths from G1_WORDS / G2_WORDS (LM:518, LM:523, LM:528), which are this
    file's g1WordsCount / g2WordsCount. -/
def vkHeaderFields : List VkHeaderFieldSpec :=
  [ { slot := .vkDigest, name := "vk_digest", widthWords := 1 },
    { slot := .numInstances, name := "num_instances", widthWords := 1 },
    { slot := .k, name := "k", widthWords := 1 },
    { slot := .nInv, name := "n_inv", widthWords := 1 },
    { slot := .omega, name := "omega", widthWords := 1 },
    { slot := .omegaInv, name := "omega_inv", widthWords := 1 },
    { slot := .omegaInvToL, name := "omega_inv_to_l", widthWords := 1 },
    { slot := .hasAccumulator, name := "has_accumulator", widthWords := 1 },
    { slot := .accOffset, name := "acc_offset", widthWords := 1 },
    { slot := .numAccLimbs, name := "num_acc_limbs", widthWords := 1 },
    { slot := .numAccLimbBits, name := "num_acc_limb_bits", widthWords := 1 },
    { slot := .g1Base, name := "G1_BASE", widthWords := g1WordsCount },
    { slot := .g2Base, name := "G2_BASE", widthWords := g2WordsCount },
    { slot := .negSG2Base, name := "NEG_S_G2_BASE", widthWords := g2WordsCount } ]

/-- rust: LM:533 (struct VkHeaderLayout) - a unit namespace, no fields. -/
structure VkHeaderLayout deriving BEq

namespace VkHeaderLayout

/-- rust: LM:536-539 (VkHeaderLayout::header_words) @formal-baseline. The Rust
    returns VK_HEADER_WORDS (LM:445), which Layout.lean already ports as
    vkHeaderWords (the LM:390-401 chain), so this is a re-export and not a second
    copy of the arithmetic. -/
def headerWords : Nat := vkHeaderWords

/-- rust: LM:541-544 (VkHeaderLayout::fields) @formal-baseline. The Rust returns
    &'static [VkHeaderFieldSpec]; Lean has no slice, so the list itself. -/
def fields : List VkHeaderFieldSpec := vkHeaderFields

/-- rust: LM:546-557 (VkHeaderLayout::field) @formal-baseline. The Rust is a
    while-loop over the table with panic!("unknown VK header slot") after it
    (LM:556). The port is a closed match over the fourteen constructors, which is
    total by construction: there is no value of VkHeaderSlot with no table row, so
    LM:556 has no Lean counterpart. That is a difference in kind and not in
    behaviour, and vkHeaderField_agreesWithTable_ok is what keeps the match and the
    table from drifting apart - the only way that claim could rot. -/
def field : VkHeaderSlot → VkHeaderFieldSpec
  | .vkDigest => { slot := .vkDigest, name := "vk_digest", widthWords := 1 }
  | .numInstances => { slot := .numInstances, name := "num_instances", widthWords := 1 }
  | .k => { slot := .k, name := "k", widthWords := 1 }
  | .nInv => { slot := .nInv, name := "n_inv", widthWords := 1 }
  | .omega => { slot := .omega, name := "omega", widthWords := 1 }
  | .omegaInv => { slot := .omegaInv, name := "omega_inv", widthWords := 1 }
  | .omegaInvToL => { slot := .omegaInvToL, name := "omega_inv_to_l", widthWords := 1 }
  | .hasAccumulator => { slot := .hasAccumulator, name := "has_accumulator", widthWords := 1 }
  | .accOffset => { slot := .accOffset, name := "acc_offset", widthWords := 1 }
  | .numAccLimbs => { slot := .numAccLimbs, name := "num_acc_limbs", widthWords := 1 }
  | .numAccLimbBits => { slot := .numAccLimbBits, name := "num_acc_limb_bits", widthWords := 1 }
  | .g1Base => { slot := .g1Base, name := "G1_BASE", widthWords := g1WordsCount }
  | .g2Base => { slot := .g2Base, name := "G2_BASE", widthWords := g2WordsCount }
  | .negSG2Base => { slot := .negSG2Base, name := "NEG_S_G2_BASE", widthWords := g2WordsCount }

end VkHeaderLayout

/-- rust: LM:566-569 (struct VkHeaderBuilder) @formal-baseline. The Rust's
    Vec<Option<(&'static str, U256)>> is a List (Option (String x Word256)),
    indexed by header word. -/
structure VkHeaderBuilder where
  words : List (Option (String × Word256))

/-- rust: LM:571-577 (VkHeaderBuilder::new) @formal-baseline. vec![None; n] is
    List.replicate. -/
def VkHeaderBuilder.new : VkHeaderBuilder :=
  { words := List.replicate VkHeaderLayout.headerWords none }

/-- rust: LM:559-562 (VkHeaderLayout::builder) @formal-baseline. MOVED below
    VkHeaderBuilder::new, which it calls; the Rust needs no forward reference
    because both are inherent methods. -/
def VkHeaderLayout.builder : VkHeaderBuilder := VkHeaderBuilder.new

/-- One word-write step of `VkHeaderBuilder.insert`, named so the `foldlM` invariants can be
    stated and proved. -/
def VkHeaderBuilder.step (start : Nat) (name : String) (self : VkHeaderBuilder)
    (pair : Nat × (String × Word256)) : Except String VkHeaderBuilder := do
  let (offset, value) := pair
  let word := start + offset
  match self.words[word]? with
  | some (some _) =>
      Except.error ("VK header field " ++ name
        ++ " overlaps already-written word " ++ toString word)
  | _ =>
      Except.ok { words := self.words.take word ++ [some value]
        ++ self.words.drop (word + 1) }

/-- `step` preserves the number of header words. PROVED. -/
theorem VkHeaderBuilder.step_length (start : Nat) (name : String) (self : VkHeaderBuilder)
    (pair : Nat × (String × Word256)) (b' : VkHeaderBuilder)
    (h : VkHeaderBuilder.step start name self pair = .ok b')
    (hword : start + pair.1 < self.words.length) :
    b'.words.length = self.words.length := by
  obtain ⟨offset, value⟩ := pair
  unfold VkHeaderBuilder.step at h
  dsimp only at h
  cases hw : self.words[start + offset]? with
  | none =>
      simp only [hw] at h
      injection h with hb
      subst hb
      simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
        List.length_nil]
      omega
  | some x =>
      cases x with
      | none =>
          simp only [hw] at h
          injection h with hb
          subst hb
          simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
            List.length_nil]
          omega
      | some v =>
          simp only [hw] at h
          cases h

private theorem update_get?_at {α : Type} (l : List α) (w : Nat) (v : α)
    (hw : w < l.length) :
    (l.take w ++ [v] ++ l.drop (w + 1))[w]? = some v := by
  rw [List.getElem?_append]
  have hlen : (l.take w).length = w := List.length_take_of_le (Nat.le_of_lt hw)
  have hlen2 : (l.take w ++ [v]).length = w + 1 := by simp [hlen]
  rw [if_pos (by omega)]
  rw [List.getElem?_append]
  rw [if_neg (by omega)]
  simp [hlen]

private theorem update_get?_other {α : Type} (l : List α) (w : Nat) (v : α)
    (hw : w < l.length) (i : Nat) (hne : i ≠ w) :
    (l.take w ++ [v] ++ l.drop (w + 1))[i]? = l[i]? := by
  rw [List.getElem?_append]
  have hlen : (l.take w).length = w := List.length_take_of_le (Nat.le_of_lt hw)
  have hlen2 : (l.take w ++ [v]).length = w + 1 := by simp [hlen]
  by_cases hi : i < w
  · rw [if_pos (by omega)]
    rw [List.getElem?_append]
    rw [if_pos (by omega)]
    rw [List.getElem?_take_of_lt hi]
  · have hi' : w + 1 ≤ i := by omega
    rw [if_neg (by omega)]
    rw [List.getElem?_drop]
    congr 1
    omega

/-- A successful `step` writes its own word. PROVED. -/
theorem VkHeaderBuilder.step_get?_at (start : Nat) (name : String) (self : VkHeaderBuilder)
    (offset : Nat) (value : String × Word256) (b' : VkHeaderBuilder)
    (h : VkHeaderBuilder.step start name self (offset, value) = .ok b')
    (hword : start + offset < self.words.length) :
    b'.words[start + offset]? = some (some value) := by
  unfold VkHeaderBuilder.step at h
  dsimp only at h
  cases hw : self.words[start + offset]? with
  | none =>
      simp only [hw] at h
      injection h with hb
      subst hb
      rw [update_get?_at self.words (start + offset) (some value) hword]
  | some x =>
      cases x with
      | none =>
          simp only [hw] at h
          injection h with hb
          subst hb
          rw [update_get?_at self.words (start + offset) (some value) hword]
      | some v =>
          simp only [hw] at h
          cases h

/-- A successful `step` leaves every other word unchanged. PROVED. -/
theorem VkHeaderBuilder.step_get?_other (start : Nat) (name : String) (self : VkHeaderBuilder)
    (offset : Nat) (value : String × Word256) (b' : VkHeaderBuilder)
    (h : VkHeaderBuilder.step start name self (offset, value) = .ok b')
    (hword : start + offset < self.words.length)
    (i : Nat) (hne : i ≠ start + offset) :
    b'.words[i]? = self.words[i]? := by
  unfold VkHeaderBuilder.step at h
  dsimp only at h
  cases hw : self.words[start + offset]? with
  | none =>
      simp only [hw] at h
      injection h with hb
      subst hb
      rw [update_get?_other self.words (start + offset) (some value) hword i hne]
  | some x =>
      cases x with
      | none =>
          simp only [hw] at h
          injection h with hb
          subst hb
          rw [update_get?_other self.words (start + offset) (some value) hword i hne]
      | some v =>
          simp only [hw] at h
          cases h

/-- A `foldlM` of length-preserving `step`s preserves the number of header words. PROVED. -/
theorem VkHeaderBuilder.foldlM_step_length (l : List (Nat × (String × Word256)))
    (self : VkHeaderBuilder) (start : Nat) (name : String) (b' : VkHeaderBuilder)
    (h : l.foldlM (VkHeaderBuilder.step start name) self = .ok b')
    (hbound : ∀ p ∈ l, start + p.1 < self.words.length) :
    b'.words.length = self.words.length := by
  induction l generalizing self with
  | nil =>
      change Except.ok self = Except.ok b' at h
      injection h with hb
      subst hb
      rfl
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      cases hs : VkHeaderBuilder.step start name self p with
      | error e => simp only [hs] at h; cases h
      | ok b1 =>
          simp only [hs] at h
          have hp : start + p.1 < self.words.length := hbound p (by simp)
          have hsl := VkHeaderBuilder.step_length start name self p b1 hs hp
          rw [ih b1 h (fun q hq => by simpa [hsl] using hbound q (by simp [hq])), hsl]

/-- rust: LM:579-621 (VkHeaderBuilder::insert) @formal-baseline. &mut self becomes
    a returned builder, the reading Layout.lean:238-241 uses for reserve. Four
    error paths, all Result::Err(String), with the Rust's message text kept because
    the message is the observable: LM:588 width mismatch, LM:594 wrong word count,
    LM:604 header overflow, LM:612 overlap with an already-written word. The
    self.words[word] read at LM:612 is a direct index, but LM:603 already rejected
    end > self.words.len(), so every word = start + offset in the loop is in range
    and no listGetMut site is needed - stated rather than assumed, and
    vkHeaderBuilder_overflowErr_ok is what makes the guard observable. -/
def VkHeaderBuilder.insert (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (expectedWidth : Nat) (values : List (String × Word256)) :
    Except String VkHeaderBuilder := do
  let spec := VkHeaderLayout.field slot
  if spec.widthWords != expectedWidth then
    Except.error ("VK header field " ++ spec.name ++ " width mismatch: descriptor="
      ++ toString spec.widthWords ++ " caller=" ++ toString expectedWidth)
  else if values.length != spec.widthWords then
    Except.error ("VK header field " ++ spec.name ++ " expected "
      ++ toString spec.widthWords ++ " word(s), got " ++ toString values.length)
  else
    let start := VkHeaderSlot.word slot
    let finish := start + spec.widthWords
    if finish > self.words.length then
      Except.error ("VK header field " ++ spec.name
        ++ " overflows header: range " ++ toString start ++ ".."
        ++ toString finish ++ ", header=" ++ toString self.words.length)
    else
      (List.zip (List.range values.length) values).foldlM
        (VkHeaderBuilder.step start spec.name) self

/-- A `foldlM` of steps that all avoid word `i` leaves word `i` unchanged. PROVED. -/
theorem VkHeaderBuilder.foldlM_step_frame (l : List (Nat × (String × Word256)))
    (self : VkHeaderBuilder) (start : Nat) (name : String) (b' : VkHeaderBuilder)
    (h : l.foldlM (VkHeaderBuilder.step start name) self = .ok b')
    (hbound : ∀ p ∈ l, start + p.1 < self.words.length)
    (i : Nat) (havoid : ∀ p ∈ l, start + p.1 ≠ i) :
    b'.words[i]? = self.words[i]? := by
  induction l generalizing self with
  | nil =>
      change Except.ok self = Except.ok b' at h
      injection h with hb
      subst hb
      rfl
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      cases hs : VkHeaderBuilder.step start name self p with
      | error e => simp only [hs] at h; cases h
      | ok b1 =>
          simp only [hs] at h
          have hpbound : start + p.1 < self.words.length := hbound p (by simp)
          have hpne : start + p.1 ≠ i := havoid p (by simp)
          have hsl := VkHeaderBuilder.step_get?_other start name self p.1 p.2 b1 hs hpbound i
            (Ne.symm hpne)
          have hsl_len := VkHeaderBuilder.step_length start name self p b1 hs hpbound
          rw [ih b1 h (fun q hq => by simpa [hsl_len] using hbound q (by simp [hq]))
            (fun q hq => havoid q (by simp [hq])), hsl]

/-- An insert whose slot range excludes `i` leaves word `i` unchanged. PROVED. -/
theorem VkHeaderBuilder.insert_get?_other (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (expectedWidth : Nat) (values : List (String × Word256)) (b' : VkHeaderBuilder)
    (h : self.insert slot expectedWidth values = .ok b')
    (i : Nat) (hi : i < VkHeaderSlot.word slot ∨
      VkHeaderSlot.word slot + values.length ≤ i) :
    b'.words[i]? = self.words[i]? := by
  by_cases hw : ((VkHeaderLayout.field slot).widthWords != expectedWidth)
  · simp only [VkHeaderBuilder.insert, hw] at h; cases h
  · by_cases hv : (values.length != (VkHeaderLayout.field slot).widthWords)
    · simp only [VkHeaderBuilder.insert, hw, hv] at h; cases h
    · by_cases hf : (VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords >
          self.words.length)
      · simp only [VkHeaderBuilder.insert, hw, hv, hf] at h; cases h
      · simp only [VkHeaderBuilder.insert, hw, hv, hf] at h
        have hlen : values.length = (VkHeaderLayout.field slot).widthWords := by
          have hfalse : (values.length != (VkHeaderLayout.field slot).widthWords) = false := by
            cases hh : (values.length != (VkHeaderLayout.field slot).widthWords) <;>
              simp_all
          exact bne_eq_false_iff_eq.mp hfalse
        have hfit : VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords ≤
            self.words.length := by omega
        refine VkHeaderBuilder.foldlM_step_frame
          ((List.range values.length).zip values) self (VkHeaderSlot.word slot)
          (VkHeaderLayout.field slot).name b' h ?_ i ?_
        · intro p hp
          obtain ⟨a, b⟩ := p
          have hmem := List.of_mem_zip hp
          have ha : a < values.length := List.mem_range.mp hmem.1
          have : VkHeaderSlot.word slot + a <
              VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords := by omega
          omega
        · intro p hp
          obtain ⟨a, b⟩ := p
          have hmem := List.of_mem_zip hp
          have ha : a < values.length := List.mem_range.mp hmem.1
          rcases hi with hi | hi
          · omega
          · omega

/-- A `foldlM` of header-builder steps whose offsets are distinct writes each of its own
    words and no others. PROVED. -/
theorem VkHeaderBuilder.foldlM_step_get?_at
    (l : List (Nat × (String × Word256))) (self : VkHeaderBuilder)
    (start : Nat) (name : String) (b' : VkHeaderBuilder)
    (h : l.foldlM (VkHeaderBuilder.step start name) self = .ok b')
    (hbound : ∀ p ∈ l, start + p.1 < self.words.length)
    (hnd : (l.map Prod.fst).Nodup)
    (j : Nat) (v : String × Word256) (hj : (j, v) ∈ l) :
    b'.words[start + j]? = some (some v) := by
  induction l generalizing self with
  | nil => simp at hj
  | cons p ps ih =>
      obtain ⟨k, w⟩ := p
      simp only [List.foldlM_cons] at h
      cases hs : VkHeaderBuilder.step start name self (k, w) with
      | error e => simp only [hs] at h; cases h
      | ok b1 =>
          simp only [hs] at h
          have hp : (k, w) ∈ (k, w) :: ps := List.mem_cons_self ..
          have hkw := hbound (k, w) hp
          have hlen := VkHeaderBuilder.step_length start name self (k, w) b1 hs hkw
          have hnd' : (ps.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
          have hknot : k ∉ ps.map Prod.fst := (List.nodup_cons.mp hnd).1
          have hbound' : ∀ q ∈ ps, start + q.1 < b1.words.length := by
            intro q hq
            have hq' := hbound q (List.mem_cons_of_mem _ hq)
            omega
          by_cases hjk : j = k
          · subst hjk
            have hvw : v = w := by
              rcases List.mem_cons.mp hj with heq | hin
              · simpa using heq
              · exfalso
                exact hknot (List.mem_map_of_mem (f := Prod.fst) hin)
            subst hvw
            have hframe := VkHeaderBuilder.foldlM_step_frame ps b1 start name b' h
              hbound' (start + j) (by
                intro q hq heq
                have hqj : q.1 = j := by omega
                exact hknot (hqj ▸ List.mem_map_of_mem (f := Prod.fst) hq))
            rw [hframe]
            exact VkHeaderBuilder.step_get?_at start name self j v b1 hs hkw
          · have hmem : (j, v) ∈ ps := by
              rcases List.mem_cons.mp hj with heq | hin
              · exact absurd (by simpa using (Prod.mk.injEq j v k w ▸ heq).1) hjk
              · exact hin
            exact ih b1 h hbound' hnd' hmem

/-- A successful multi-word `insert` writes each word of its value list at its own
    offset. PROVED. -/
theorem VkHeaderBuilder.insert_get?_at (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (expectedWidth : Nat) (values : List (String × Word256)) (b' : VkHeaderBuilder)
    (h : self.insert slot expectedWidth values = .ok b')
    (i : Nat) (v : String × Word256) (hv : values[i]? = some v) :
    b'.words[VkHeaderSlot.word slot + i]? = some (some v) := by
  by_cases hw : ((VkHeaderLayout.field slot).widthWords != expectedWidth)
  · simp only [VkHeaderBuilder.insert, hw] at h; cases h
  · by_cases hvlen : (values.length != (VkHeaderLayout.field slot).widthWords)
    · simp only [VkHeaderBuilder.insert, hw, hvlen] at h; cases h
    · by_cases hf : (VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords >
          self.words.length)
      · simp only [VkHeaderBuilder.insert, hw, hvlen, hf] at h; cases h
      · simp only [VkHeaderBuilder.insert, hw, hvlen, hf] at h
        have hvfalse : (values.length != (VkHeaderLayout.field slot).widthWords) = false := by
          cases hh : (values.length != (VkHeaderLayout.field slot).widthWords) <;> simp_all
        have hlen : values.length = (VkHeaderLayout.field slot).widthWords :=
          bne_eq_false_iff_eq.mp hvfalse
        have hi : i < values.length := (List.getElem?_eq_some_iff.mp hv).1
        refine VkHeaderBuilder.foldlM_step_get?_at ((List.range values.length).zip values)
          self (VkHeaderSlot.word slot) (VkHeaderLayout.field slot).name b' h ?_ ?_ i v ?_
        · intro p hp
          have hp' := List.of_mem_zip hp
          have hp1 : p.1 < values.length := List.mem_range.mp hp'.1
          have hpw : p.1 < (VkHeaderLayout.field slot).widthWords := by omega
          omega
        · rw [show List.map Prod.fst ((List.range values.length).zip values) =
              List.range values.length from List.map_fst_zip (by simp)]
          exact List.nodup_range
        · rw [List.mem_iff_getElem]
          refine ⟨i, ?_, ?_⟩
          · rw [List.length_zip, Nat.min_eq_right (by simp)]
            exact hi
          · rw [List.getElem_zip]
            rw [List.getElem_range]
            rw [(List.getElem?_eq_some_iff.mp hv).2]

/-- `insert` preserves the number of header words. PROVED. -/
theorem VkHeaderBuilder.insert_length (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (expectedWidth : Nat) (values : List (String × Word256)) (b' : VkHeaderBuilder)
    (h : self.insert slot expectedWidth values = .ok b') :
    b'.words.length = self.words.length := by
  by_cases hw : ((VkHeaderLayout.field slot).widthWords != expectedWidth)
  · simp only [VkHeaderBuilder.insert, hw] at h
    cases h
  · by_cases hv : (values.length != (VkHeaderLayout.field slot).widthWords)
    · simp only [VkHeaderBuilder.insert, hw, hv] at h
      cases h
    · by_cases hf : (VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords >
          self.words.length)
      · simp only [VkHeaderBuilder.insert, hw, hv, hf] at h
        cases h
      · simp only [VkHeaderBuilder.insert, hw, hv, hf] at h
        have hlen : values.length = (VkHeaderLayout.field slot).widthWords := by
          have hfalse : (values.length != (VkHeaderLayout.field slot).widthWords) = false := by
            cases hh : (values.length != (VkHeaderLayout.field slot).widthWords) <;>
              simp_all
          exact bne_eq_false_iff_eq.mp hfalse
        have hfit : VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords ≤
            self.words.length := by omega
        refine VkHeaderBuilder.foldlM_step_length
          ((List.range values.length).zip values) self (VkHeaderSlot.word slot)
          (VkHeaderLayout.field slot).name b' h ?_
        intro p hp
        obtain ⟨a, b⟩ := p
        have hmem := List.of_mem_zip hp
        have ha : a < values.length := List.mem_range.mp hmem.1
        have : VkHeaderSlot.word slot + a <
            VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords := by omega
        omega

/-- rust: LM:623-631 (VkHeaderBuilder::scalar) @formal-baseline. -/
def VkHeaderBuilder.scalar (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (name : String) (value : Word256) : Except String VkHeaderBuilder :=
  self.insert slot 1 [(name, value)]

private theorem except_bind_pure {ε α : Type} (e : Except ε α) :
    (e >>= fun x => Except.ok x) = e := by
  cases e <;> rfl

/-- A successful scalar insert writes its slot. PROVED. -/
theorem VkHeaderBuilder.scalar_get (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (name : String) (value : Word256) (b' : VkHeaderBuilder)
    (h : self.scalar slot name value = .ok b') :
    b'.words[VkHeaderSlot.word slot]? = some (some (name, value)) := by
  unfold VkHeaderBuilder.scalar at h
  by_cases hw : ((VkHeaderLayout.field slot).widthWords != 1)
  · simp only [VkHeaderBuilder.insert, hw] at h; cases h
  · by_cases hv : ([(name, value)].length != (VkHeaderLayout.field slot).widthWords)
    · simp only [VkHeaderBuilder.insert, hw, hv] at h; cases h
    · by_cases hf : (VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords >
          self.words.length)
      · simp only [VkHeaderBuilder.insert, hw, hv, hf] at h; cases h
      · have hwfalse : ((VkHeaderLayout.field slot).widthWords != 1) = false := by
          cases hh : ((VkHeaderLayout.field slot).widthWords != 1) <;> simp_all
        have hvfalse : ([(name, value)].length != (VkHeaderLayout.field slot).widthWords) = false := by
          cases hh : ([(name, value)].length != (VkHeaderLayout.field slot).widthWords) <;>
            simp_all
        have hwidth : (VkHeaderLayout.field slot).widthWords = 1 :=
          bne_eq_false_iff_eq.mp hwfalse
        have hlen : ([(name, value)].length : Nat) = (VkHeaderLayout.field slot).widthWords :=
          bne_eq_false_iff_eq.mp hvfalse
        simp only [VkHeaderBuilder.insert, hwfalse, hvfalse, hf, Bool.false_eq_true,
          if_false] at h
        have hfit : VkHeaderSlot.word slot + (VkHeaderLayout.field slot).widthWords ≤
            self.words.length := by omega
        have hword : VkHeaderSlot.word slot < self.words.length := by omega
        have hsingle : (List.zip (List.range [(name, value)].length) [(name, value)]) =
            [(0, (name, value))] := by rfl
        rw [hsingle] at h
        simp only [List.foldlM_cons, List.foldlM_nil, pure, Except.bind] at h
        change (VkHeaderBuilder.step (VkHeaderSlot.word slot)
          (VkHeaderLayout.field slot).name self (0, (name, value)) >>=
            fun x => Except.ok x) = Except.ok b' at h
        rw [except_bind_pure] at h
        exact VkHeaderBuilder.step_get?_at (VkHeaderSlot.word slot)
          (VkHeaderLayout.field slot).name self 0 (name, value) b' h hword

/-- A successful scalar insert leaves every other slot unchanged. PROVED. -/
theorem VkHeaderBuilder.scalar_frame (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (name : String) (value : Word256) (b' : VkHeaderBuilder)
    (h : self.scalar slot name value = .ok b') (i : Nat) (hne : i ≠ VkHeaderSlot.word slot) :
    b'.words[i]? = self.words[i]? := by
  have hi : i < VkHeaderSlot.word slot ∨
      VkHeaderSlot.word slot + [(name, value)].length ≤ i := by
    have hlen : [(name, value)].length = 1 := rfl
    omega
  simpa [VkHeaderBuilder.scalar] using
    VkHeaderBuilder.insert_get?_other self slot 1 [(name, value)] b'
      (by simpa [VkHeaderBuilder.scalar] using h) i hi

/-- rust: LM:633-642 (VkHeaderBuilder::g1) @formal-baseline. The Rust zips a
    [&str; G1_WORDS] with a [U256; G1_WORDS]; the port takes two lists and
    List.zip, which truncates to the shorter input (rule R3) exactly as
    into_iter().zip() does. Both are length 4 by construction at the call site. -/
def VkHeaderBuilder.g1 (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) : Except String VkHeaderBuilder :=
  self.insert slot g1WordsCount (List.zip names values)

/-- rust: LM:644-653 (VkHeaderBuilder::g2) @formal-baseline. Same zip note. -/
def VkHeaderBuilder.g2 (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) : Except String VkHeaderBuilder :=
  self.insert slot g2WordsCount (List.zip names values)

/-- rust: LM:655-664 (VkHeaderBuilder::finish) @formal-baseline. The first unwritten
    word is reported by its index, and collect over a Result short-circuits at the
    first Err, which the foldl below reproduces.
    A claim an earlier draft made here was wrong and is corrected: it said the
    enumerate-before-map order is what distinguishes the WORD index from the index
    among the unwritten words. It does not, and cannot be observed to: because the
    fold stops at the FIRST unwritten word, every word before it was written, so the
    two counts are equal at the point the message is built. Perturbation P14 (report
    xs.length instead of word) reddened nothing, which is the evidence for the
    equivalence rather than for a missing gate. -/
def VkHeaderBuilder.finish (self : VkHeaderBuilder) :
    Except String (List (String × Word256)) :=
  ((List.range self.words.length).zip self.words).foldl
    (fun acc pair =>
      match acc with
      | .error e => .error e
      | .ok xs =>
          let (word, value) := pair
          match value with
          | some v => .ok (xs ++ [v])
          | none => .error ("VK header word " ++ toString word
              ++ " was not written"))
    (.ok [])

/-- One step of `VkHeaderBuilder.finish`, named for the length proof. -/
private def finishStep (acc : Except String (List (String × Word256)))
    (pair : Nat × Option (String × Word256)) : Except String (List (String × Word256)) :=
  match acc with
  | .error e => .error e
  | .ok xs =>
      match pair.2 with
      | some v => .ok (xs ++ [v])
      | none => .error ("VK header word " ++ toString pair.1 ++ " was not written")

private theorem finishFold_error (ps : List (Nat × Option (String × Word256))) (e : String) :
    ps.foldl finishStep (.error e) = .error e := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases p with
      | mk word value =>
          cases value <;> simp [finishStep, ih]

private theorem finishFold_length (ws : List (Nat × Option (String × Word256)))
    (xs : List (String × Word256)) (l : List (String × Word256))
    (h : ws.foldl finishStep (.ok xs) = .ok l) :
    l.length = xs.length + ws.length := by
  induction ws generalizing xs l with
  | nil =>
      simp only [List.foldl_nil, Except.ok.injEq] at h
      rw [← h]
      simp
  | cons p ps ih =>
      cases p with
      | mk word value =>
          cases value with
          | none =>
              simp [finishStep, finishFold_error] at h
          | some v =>
              simp only [finishStep, List.foldl_cons] at h
              have hl := ih (xs ++ [v]) l h
              simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢
              omega

private theorem finishFold_eq (ws : List (Nat × Option (String × Word256)))
    (xs : List (String × Word256)) (l : List (String × Word256))
    (h : ws.foldl finishStep (.ok xs) = .ok l) :
    l = xs ++ (ws.map (fun p => p.2)).filterMap id := by
  induction ws generalizing xs l with
  | nil =>
      simp only [List.foldl_nil, Except.ok.injEq] at h
      subst h
      simp
  | cons p ps ih =>
      cases p with
      | mk word value =>
          cases value with
          | none => simp [finishStep, finishFold_error] at h
          | some v =>
              simp only [finishStep, List.foldl_cons] at h
              have := ih (xs ++ [v]) l h
              simpa [List.append_assoc] using this

private theorem finishFold_all (ws : List (Nat × Option (String × Word256)))
    (xs : List (String × Word256)) (l : List (String × Word256))
    (h : ws.foldl finishStep (.ok xs) = .ok l) :
    ws.all (fun p => p.2.isSome) = true := by
  induction ws generalizing xs l with
  | nil => rfl
  | cons p ps ih =>
      cases p with
      | mk word value =>
          cases value with
          | none => simp [finishStep, finishFold_error] at h
          | some v =>
              simp only [finishStep, List.foldl_cons] at h
              simpa using ih (xs ++ [v]) l h

private theorem filterMap_id_get? (ws : List (Option (String × Word256)))
    (hall : ws.all (fun o => o.isSome) = true) (i : Nat)
    {v : String × Word256} (hv : ws[i]? = some (some v)) :
    (ws.filterMap id)[i]? = some v := by
  induction ws generalizing i with
  | nil => simp at hv
  | cons w ws ih =>
      cases w with
      | none => simp at hall
      | some v0 =>
          cases i with
          | zero =>
              simpa using hv
          | succ i =>
              simp only [List.filterMap_cons, List.getElem?_cons_succ] at hv ⊢
              have hall' : ws.all (fun o => o.isSome) = true := by simpa using hall
              exact ih hall' i hv

private theorem zip_range_get? {α : Type} (l : List α) {n i : Nat} (hi : i < n) :
    (List.zip (List.range n) l)[i]? = l[i]?.map (fun v => (i, v)) := by
  rw [show List.zip (List.range n) l =
    List.zipWith Prod.mk (List.range n) l from rfl]
  rw [List.getElem?_zipWith, List.getElem?_range hi]
  cases l[i]? <;> rfl

/-- **A SUCCESSFUL `finish` PRESERVES EACH WRITTEN SLOT.** The value half of the
    `VkHeaderBuilder` spec the payload leaves need. PROVED. -/
theorem VkHeaderBuilder.finish_get? (b : VkHeaderBuilder) (l : List (String × Word256))
    (h : b.finish = .ok l) (i : Nat) {v : String × Word256}
    (hi : i < b.words.length) (hv : b.words[i]? = some (some v)) :
    l[i]? = some v := by
  unfold VkHeaderBuilder.finish at h
  let ws := (List.range b.words.length).zip b.words
  have h' : ws.foldl finishStep (.ok []) = .ok l := by
    unfold ws
    unfold finishStep
    exact h
  have heq := finishFold_eq ws [] l h'
  have hall := finishFold_all ws [] l h'
  obtain ⟨w, hw⟩ := List.getElem?_eq_some_iff.mp hv
  have hws : ws[i]? = some (i, some v) := by
    unfold ws
    rw [zip_range_get? b.words hi]
    rw [hv]
    rfl
  have hall' : (ws.map (fun p => p.2)).all (fun o => o.isSome) = true := by
    simpa using hall
  have hmapget : (ws.map (fun p => p.2))[i]? = some (some v) := by
    rw [List.getElem?_map]
    rw [hws]
    rfl
  have hfilter := filterMap_id_get? (ws.map (fun p => p.2)) hall' i hmapget
  rw [heq]
  simpa using hfilter

/-- `finish` reads a written word back at the same index. PROVED. -/
theorem VkHeaderBuilder.finish_getD (b : VkHeaderBuilder) (l : List (String × Word256))
    (h : b.finish = .ok l) (i : Nat) (hi : i < b.words.length)
    {v : String × Word256} (hv : b.words[i]? = some (some v)) (d : String × Word256) :
    l.getD i d = v := by
  rw [List.getD_eq_getElem?_getD, VkHeaderBuilder.finish_get? b l h i hi hv]
  rfl


/-- **A SUCCESSFUL `finish` RETURNS ONE WORD PER HEADER SLOT.** The length half of the
    `VkHeaderBuilder` spec the payload leaves need. PROVED. -/
theorem VkHeaderBuilder.finish_length (b : VkHeaderBuilder) (l : List (String × Word256))
    (h : b.finish = .ok l) : l.length = b.words.length := by
  unfold VkHeaderBuilder.finish at h
  have h' : ((List.range b.words.length).zip b.words).foldl finishStep (.ok []) = .ok l := by
    unfold finishStep
    exact h
  have := finishFold_length _ _ _ h'
  simpa using this

/-! ## The SRS tau binding (rust: VK:29-62)

MOVED: srs_tau_commitment (VK:50-62) is declared before srs_tau_is_consistent
(VK:37-44), which calls it at VK:42. Lean is order-sensitive and the Rust's order
would need a forward reference. -/

/-- rust: VK:53-60, the omega_powers vector built by a MUTATING accumulator inside
    a map over a captured mut omega_pow. Hazard 2: the shape is mirrored and not
    paraphrased - the accumulator starts at Fq::ONE, each step yields the
    accumulator BEFORE multiplying it by omega, and the list has exactly n entries,
    which is VK:56-58. omega ^ i computes the same list and is a different program,
    so it is not used; the equivalence is gated by
    omegaPowers_accumulatorEquivalence_ok rather than assumed. Scaffolding for
    VK:54-60 rather than a Rust item of its own, because in the Rust the accumulator
    is a closure body inside srs_tau_commitment and Lean cannot name it there. -/
def omegaPowers (omega : Fr p) (n : Nat) : List (Fr p) :=
  ((List.range n).foldl (fun st _ => (st.1 * omega, st.2 ++ [st.1])) (1, [])).2

/-- rust: VK:50-62 (srs_tau_commitment) @formal-baseline. Commit f(X) = X in the
    Lagrange basis: [tau]G1 = sum_i omega^i * L_i(tau) * G, which is what
    G1Projective::multi_exp(g_lagrange, &omega_powers) computes - the group crate's
    signature is multi_exp(bases, scalars), so g_lagrange is the base and omega^i
    the scalar, and VK:46's doc comment says the same.
    HAZARD 1'S DECISION, restated at the site: the SEMANTICS are ported (a
    left-to-right fold of scalar multiplications from the identity) and the
    Pippenger bucket algorithm is not. .to_affine() (VK:61) is the identity here -
    R7's projective/affine collapse. Never evaluated at production size. -/
def srsTauCommitment (g_lagrange : List G₁) (omega : Fr p) : G₁ :=
  ((omegaPowers omega g_lagrange.length).zip g_lagrange).foldl
    (fun acc (s, g) => acc * gsmul s g) 1

/-- rust: VK:37-44 (srs_tau_is_consistent) @formal-baseline. The pairing check
    e([tau]G1, G2) = e(G1, s_g2), where G1Affine::generator() and
    G2Affine::generator() are the distinguished generators of D-P1's
    AdmissiblePairing (Common/Curve.lean:45-46) and Bls12::pairing is
    AdmissiblePairing.e (Common/Curve.lean:42). HAZARD 3: this is a Phase 4a lemma
    wearing a port's clothes - the def is ported, the content is finding F-P08-2. -/
def srsTauIsConsistent (g_lagrange : List G₁) (omega : Fr p) (s_g2 : G₂) : Bool :=
  let tau_g1 := srsTauCommitment g_lagrange omega
  decideBool (P.decEqGₜ (Additive.toMul (P.e (Additive.ofMul tau_g1) (Additive.ofMul P.g₂)))
    (Additive.toMul (P.e (Additive.ofMul P.g₁) (Additive.ofMul s_g2))))

/-- Scaffolding, not a Rust item: the exact preimage srsFingerprint hashes, split
    out so hazard 4 can gate the BYTES and not only the digest. VK:80-90 appends
    five groups in this order. -/
def srsFingerprintPreimage (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂) (tau_g1 : G₁) : Except Fault Bytes := do
  let g_lagrange := inputs.params.gLagrange
  -- VK:80: hasher.update(b"halo2-solidity-verifier-srs-v1")
  let pre1 := asciiBytes "halo2-solidity-verifier-srs-v1"
  -- VK:81: (g_lagrange.len() as u64).to_be_bytes() - EIGHT bytes, not thirty-two.
  let pre2 := pre1.append (natToBytesBE g_lagrange.length 8)
  -- VK:82-84: every word of g2, big-endian.
  let g2Words ← g2ToU256s (codecs.g2Repr inputs.params.g2)
  let pre3 := g2Words.foldl (fun acc word => acc.append (wordToBytesBE word)) pre2
  -- VK:85-87: every word of s_g2, big-endian.
  let sG2Words ← g2ToU256s (codecs.g2Repr inputs.params.sG2)
  let pre4 := sG2Words.foldl (fun acc word => acc.append (wordToBytesBE word)) pre3
  -- VK:88-90: every word of [tau]G1, big-endian.
  let tauWords ← g1ToU256s (codecs.g1Repr tau_g1)
  Except.ok (tauWords.foldl (fun acc word => acc.append (wordToBytesBE word)) pre4)

/-- rust: VK:73-92 (VerifierBuildInputs::srs_fingerprint) @formal-baseline.
    HAZARD 4. The preimage order is exactly the Rust's and exactly what the doc
    comment at VK:69-71 names: the tag, then n as 8 big-endian bytes, then the
    eight G2 words of params.g2(), then the eight G2 words of params.s_g2(), then
    the four G1 words of [tau]G1. The order is NOT ambiguous in the Rust - the four
    hasher.update groups are sequential - so the plan's "if the order or the
    encodings are ambiguous, that is a finding" does not fire. What is worth a
    finding is that n is 8 bytes while every word is 32 (VK:81), a stride change
    waiting to happen, pinned by srsFingerprint_preimage_ok.
    The Rust returns [u8; 32]; the port returns H256 = BitVec 256
    (Common/Bytes.lean:24), which is what keccak256 already returns
    (Common/Keccak.lean:15). -/
def srsFingerprint (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂) : Except Fault H256 := do
  let g_lagrange := inputs.params.gLagrange
  let omega := EvaluationDomain.getOmega inputs.vk.domain
  let tau_g1 := srsTauCommitment g_lagrange omega
  Except.ok (keccak256 (← srsFingerprintPreimage codecs inputs tau_g1))

/-! ## generate_base_vk (rust: VK:94-299)

The bulk of the file, and hazard 7's home. -/

/-- rust: VK:95-299 (VerifierBuildInputs::generate_base_vk) @formal-baseline.
    Private in the Rust, ported anyway per R1. The to_affine closure of VK:269 is
    the identity here (R7's collapse) and so is a comment rather than a function.
    HAZARD 7: the payload is assembled here - constants, fixed commitments,
    permutation commitments - and the section order the emitted bytes appear in is
    header scalars, G1_BASE, G2_BASE, NEG_S_G2_BASE, then the quotient sections
    that generate_vk / generate_vk_direct append, then the G1 commitment words,
    which is the order VkPayloadLayout::for_vk reserves (VP:76-94). The gate that
    pins the ORDER and not just the counts is payloadOrder_sectionsTiled_ok. -/
def generateBaseVkPrefix (inputs : VerifierBuildInputs p G₁ G₂) :
    Except Fault (Word256 × Word256 × Word256 × Word256 × Word256) := do
  -- VK:100: let domain = self.vk.get_domain();
  let domain := inputs.vk.domain
  -- VK:109: fe_to_u256::<Fq>(&self.vk.transcript_repr())
  let vkDigest ← feToU256 (bytesToNats (frToRepr inputs.vk.transcriptRepr))
  -- VK:112: Fq::from(1u64 << domain.k()).invert().unwrap(). The shift panics for
  -- k >= 64 in both profiles (unreachable: k <= F::S = 32); the unwrap is a real
  -- panic site and is ported as one.
  let nInvField ← match invert ((2 ^ domain.k : ℕ) : Fr p) with
    | some x => Except.ok x
    | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:112")
  let nInv ← feToU256 (bytesToNats (frToRepr nInvField))
  -- VK:113-114
  let omega ← feToU256 (bytesToNats (frToRepr (EvaluationDomain.getOmega domain)))
  let omegaInv ← feToU256 (bytesToNats (frToRepr (EvaluationDomain.getOmegaInv domain)))
  -- VK:115-118: omega_inv ^ |rotation_last|, the i32 made unsigned first.
  let l := Int.natAbs inputs.meta_.rotationLast
  let omegaInvToL ← feToU256 (bytesToNats (frToRepr
    (powVartime (EvaluationDomain.getOmegaInv domain) l)))
  -- VK:145-150: srs_g1_base = sum of g_lagrange, from the identity.
  let g_lagrange := inputs.params.gLagrange
  let srsG1Base := g_lagrange.foldl (fun acc g => acc * g) 1
  -- VK:151-156: assert_eq!(srs_g1_base, G1Affine::generator()). The first of the
  -- three SRS controls the audit calls H-1: the only build-time check that can
  -- catch a substituted SRS, because every other control in the repository checks
  -- self-consistency and a substituted SRS is perfectly self-consistent.
  unless (decideBool (P.decEqG₁ srsG1Base P.g₁)) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:151")
  -- VK:180-185: assert_eq!(g2_pt, G2Affine::generator()).
  let g2Pt : G₂ := inputs.params.g2
  unless (g2Pt == P.g₂) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:180")
  Except.ok (vkDigest, nInv, omega, omegaInv, omegaInvToL)

def generateBaseVkEncodings (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂) :
    Except Fault (List Word256 × List Word256 × List Word256) := do
  let domain := inputs.vk.domain
  -- VK:110-111: U256::from(usize) for the instance count and the domain exponent.
  let numInstancesW : Word256 := BitVec.ofNat 256 inputs.numInstances
  let kW : Word256 := BitVec.ofNat 256 domain.k
  -- VK:119-131: the accumulator quadruple; unwrap_or_default() is the zero word.
  let hasAccumulator : Word256 := BitVec.ofNat 256 (if inputs.accEncoding.isSome then 1 else 0)
  let accOffset : Word256 := match inputs.accEncoding with
    | some e => BitVec.ofNat 256 e.offset
    | none => 0
  let numAccLimbs : Word256 := match inputs.accEncoding with
    | some e => BitVec.ofNat 256 e.numLimbs
    | none => 0
  let numAccLimbBits : Word256 := match inputs.accEncoding with
    | some e => BitVec.ofNat 256 e.numLimbBits
    | none => 0
  let g_lagrange := inputs.params.gLagrange
  -- VK:157-159
  let g1Pt : G₁ := P.g₁
  let g2Pt : G₂ := inputs.params.g2
  let negSG2Pt : G₂ := inputs.params.sG2⁻¹
  -- VK:189-199: assert!(srs_tau_is_consistent(...)).
  unless (srsTauIsConsistent g_lagrange (EvaluationDomain.getOmega domain)
      inputs.params.sG2) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:189")
  -- VK:206-208: the EIP-2537 padded encodings.
  let g1Words ← g1ToU256s (codecs.g1Repr g1Pt)
  let g2Words ← g2ToU256s (codecs.g2Repr g2Pt)
  let negSG2Words ← g2ToU256s (codecs.g2Repr negSG2Pt)
  -- VK:210-264: the header builder. Every .unwrap() is its own Rust line and so
  -- its own panic site; the messages are lost with Fault.panic's payload
  -- (F-P08-3).
  pure (g1Words, g2Words, negSG2Words)

/-- `unwrapAt` success is its argument's success. PROVED. -/
theorem unwrapAt_ok {α : Type} {site : String} {e : Except String α} {a : α}
    (h : unwrapAt site e = .ok a) : e = .ok a := by
  unfold unwrapAt at h
  cases e with
  | error err => simp at h
  | ok a => simpa using h

/-- One scalar header insert, opaque so the header peel sees a small continuation. -/
def headerScalarInsert (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (name : String) (value : Word256) : Except Fault VkHeaderBuilder :=
  unwrapAt site (b.scalar slot name value)

/-- One G1 header insert. -/
def headerG1Insert (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) : Except Fault VkHeaderBuilder :=
  unwrapAt site (b.g1 slot names values)

/-- One G2 header insert. -/
def headerG2Insert (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) : Except Fault VkHeaderBuilder :=
  unwrapAt site (b.g2 slot names values)

theorem headerScalarInsert_length (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (name : String) (value : Word256) (b' : VkHeaderBuilder)
    (h : headerScalarInsert b site slot name value = .ok b') :
    b'.words.length = b.words.length := by
  apply VkHeaderBuilder.insert_length
  simpa [headerScalarInsert, VkHeaderBuilder.scalar] using unwrapAt_ok h

theorem headerScalarInsert_get (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (name : String) (value : Word256) (b' : VkHeaderBuilder)
    (h : headerScalarInsert b site slot name value = .ok b') :
    b'.words[VkHeaderSlot.word slot]? = some (some (name, value)) := by
  exact VkHeaderBuilder.scalar_get b slot name value b'
    (by simpa [headerScalarInsert] using unwrapAt_ok h)

theorem headerScalarInsert_frame (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (name : String) (value : Word256) (b' : VkHeaderBuilder)
    (h : headerScalarInsert b site slot name value = .ok b')
    (i : Nat) (hne : i ≠ VkHeaderSlot.word slot) :
    b'.words[i]? = b.words[i]? := by
  exact VkHeaderBuilder.scalar_frame b slot name value b'
    (by simpa [headerScalarInsert] using unwrapAt_ok h) i hne

theorem headerG1Insert_frame (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) (b' : VkHeaderBuilder)
    (h : headerG1Insert b site slot names values = .ok b')
    (i : Nat) (hi : i < VkHeaderSlot.word slot ∨
      VkHeaderSlot.word slot + (List.zip names values).length ≤ i) :
    b'.words[i]? = b.words[i]? := by
  exact VkHeaderBuilder.insert_get?_other b slot g1WordsCount (List.zip names values) b'
    (by simpa [headerG1Insert, VkHeaderBuilder.g1] using unwrapAt_ok h) i hi

theorem headerG2Insert_frame (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) (b' : VkHeaderBuilder)
    (h : headerG2Insert b site slot names values = .ok b')
    (i : Nat) (hi : i < VkHeaderSlot.word slot ∨
      VkHeaderSlot.word slot + (List.zip names values).length ≤ i) :
    b'.words[i]? = b.words[i]? := by
  exact VkHeaderBuilder.insert_get?_other b slot g2WordsCount (List.zip names values) b'
    (by simpa [headerG2Insert, VkHeaderBuilder.g2] using unwrapAt_ok h) i hi

theorem headerG1Insert_length (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) (b' : VkHeaderBuilder)
    (h : headerG1Insert b site slot names values = .ok b') :
    b'.words.length = b.words.length := by
  apply VkHeaderBuilder.insert_length
  simpa [headerG1Insert, VkHeaderBuilder.g1] using unwrapAt_ok h

theorem headerG2Insert_length (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) (b' : VkHeaderBuilder)
    (h : headerG2Insert b site slot names values = .ok b') :
    b'.words.length = b.words.length := by
  apply VkHeaderBuilder.insert_length
  simpa [headerG2Insert, VkHeaderBuilder.g2] using unwrapAt_ok h
/-- A successful G1 insert writes each of its four words. PROVED. -/
theorem headerG1Insert_get (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) (b' : VkHeaderBuilder)
    (h : headerG1Insert b site slot names values = .ok b')
    (j : Nat) (v : String × Word256) (hv : (List.zip names values)[j]? = some v) :
    b'.words[VkHeaderSlot.word slot + j]? = some (some v) := by
  exact VkHeaderBuilder.insert_get?_at b slot g1WordsCount (List.zip names values) b'
    (by simpa [headerG1Insert, VkHeaderBuilder.g1] using unwrapAt_ok h) j v hv

/-- A successful G2 insert writes each of its eight words. PROVED. -/
theorem headerG2Insert_get (b : VkHeaderBuilder) (site : String) (slot : VkHeaderSlot)
    (names : List String) (values : List Word256) (b' : VkHeaderBuilder)
    (h : headerG2Insert b site slot names values = .ok b')
    (j : Nat) (v : String × Word256) (hv : (List.zip names values)[j]? = some v) :
    b'.words[VkHeaderSlot.word slot + j]? = some (some v) := by
  exact VkHeaderBuilder.insert_get?_at b slot g2WordsCount (List.zip names values) b'
    (by simpa [headerG2Insert, VkHeaderBuilder.g2] using unwrapAt_ok h) j v hv



def generateBaseVkHeader (inputs : VerifierBuildInputs p G₁ G₂)
    (pre : Word256 × Word256 × Word256 × Word256 × Word256)
    (g1Words g2Words negSG2Words : List Word256) :
    Except Fault (List (String × Word256)) := do
  let (vkDigest, nInv, omega, omegaInv, omegaInvToL) := pre
  let domain := inputs.vk.domain
  -- VK:110-111: U256::from(usize) for the instance count and the domain exponent.
  let numInstancesW : Word256 := BitVec.ofNat 256 inputs.numInstances
  let kW : Word256 := BitVec.ofNat 256 domain.k
  -- VK:119-131: the accumulator quadruple; unwrap_or_default() is the zero word.
  let hasAccumulator : Word256 := BitVec.ofNat 256 (if inputs.accEncoding.isSome then 1 else 0)
  let accOffset : Word256 := match inputs.accEncoding with
    | some e => BitVec.ofNat 256 e.offset
    | none => 0
  let numAccLimbs : Word256 := match inputs.accEncoding with
    | some e => BitVec.ofNat 256 e.numLimbs
    | none => 0
  let numAccLimbBits : Word256 := match inputs.accEncoding with
    | some e => BitVec.ofNat 256 e.numLimbBits
    | none => 0
  let h0 := VkHeaderLayout.builder
  let h1 ← headerScalarInsert h0 "proofs/solidity-verifier/src/lowering/vk.rs:211"
    .vkDigest "vk_digest" vkDigest
  let h2 ← headerScalarInsert h1 "proofs/solidity-verifier/src/lowering/vk.rs:212"
    .numInstances "num_instances" numInstancesW
  let h3 ← headerScalarInsert h2 "proofs/solidity-verifier/src/lowering/vk.rs:213"
    .k "k" kW
  let h4 ← headerScalarInsert h3 "proofs/solidity-verifier/src/lowering/vk.rs:214"
    .nInv "n_inv" nInv
  let h5 ← headerScalarInsert h4 "proofs/solidity-verifier/src/lowering/vk.rs:215"
    .omega "omega" omega
  let h6 ← headerScalarInsert h5 "proofs/solidity-verifier/src/lowering/vk.rs:216"
    .omegaInv "omega_inv" omegaInv
  let h7 ← headerScalarInsert h6 "proofs/solidity-verifier/src/lowering/vk.rs:217"
    .omegaInvToL "omega_inv_to_l" omegaInvToL
  let h8 ← headerScalarInsert h7 "proofs/solidity-verifier/src/lowering/vk.rs:218"
    .hasAccumulator "has_accumulator" hasAccumulator
  let h9 ← headerScalarInsert h8 "proofs/solidity-verifier/src/lowering/vk.rs:219"
    .accOffset "acc_offset" accOffset
  let h10 ← headerScalarInsert h9 "proofs/solidity-verifier/src/lowering/vk.rs:220"
    .numAccLimbs "num_acc_limbs" numAccLimbs
  let h11 ← headerScalarInsert h10 "proofs/solidity-verifier/src/lowering/vk.rs:222"
    .numAccLimbBits "num_acc_limb_bits" numAccLimbBits
  let h12 ← headerG1Insert h11 "proofs/solidity-verifier/src/lowering/vk.rs:225"
    .g1Base ["g1_x_hi", "g1_x_lo", "g1_y_hi", "g1_y_lo"] g1Words
  let h13 ← headerG2Insert h12 "proofs/solidity-verifier/src/lowering/vk.rs:231"
    .g2Base ["g2_x_c0_hi", "g2_x_c0_lo", "g2_x_c1_hi", "g2_x_c1_lo",
      "g2_y_c0_hi", "g2_y_c0_lo", "g2_y_c1_hi", "g2_y_c1_lo"] g2Words
  let h14 ← headerG2Insert h13 "proofs/solidity-verifier/src/lowering/vk.rs:247"
    .negSG2Base ["neg_s_g2_x_c0_hi", "neg_s_g2_x_c0_lo", "neg_s_g2_x_c1_hi",
      "neg_s_g2_x_c1_lo", "neg_s_g2_y_c0_hi", "neg_s_g2_y_c0_lo", "neg_s_g2_y_c1_hi",
      "neg_s_g2_y_c1_lo"] negSG2Words
  let constants ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:264" (h14.finish)
  pure constants

def generateBaseVkBody (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂)
    (pre : Word256 × Word256 × Word256 × Word256 × Word256) :
    Except Fault Halo2VerifyingKey := do
  let (g1Words, g2Words, negSG2Words) ← generateBaseVkEncodings codecs inputs
  let constants ← generateBaseVkHeader inputs pre g1Words g2Words negSG2Words
  -- VK:267-279: the commitment vectors. chain! with ONE argument is the identity
  -- iterator (itertools' chain! over a single iterable), so nothing is flattened;
  -- that is worth saying because a reader may look for a second iterator.
  let fixedComms ← inputs.vk.fixedCommitments.toList.mapM fun g =>
    g1ToU256s (codecs.g1Repr g) >>= vkG1WordsOf
  let permutationComms ← inputs.vk.permutation.commitments.toList.mapM fun g =>
    g1ToU256s (codecs.g1Repr g) >>= vkG1WordsOf
  -- VK:280-286: the constructor memory reservation and its validation.
  let constructorPayloadLen :=
    constants.length * wordBytes + (fixedComms.length + permutationComms.length) * g1Bytes
  let constructorMemory :=
    VkConstructorMemoryLayout.new (constructorPayloadLen + vkRuntimePrefixLen)
  unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:286" (constructorMemory.validate)
  -- VK:287-298: the record. The four quotient fields are the empty ones: this is
  -- the BASE, and generate_vk / generate_vk_direct fill the quotient sections.
  let vkBase : Halo2VerifyingKey :=
    { constructorPayloadMptr := constructorMemory.payloadMptr
      constants := constants
      fixedComms := fixedComms
      permutationComms := permutationComms
      quotientConstOffsetWords := none
      quotientConstWords := 0
      quotientProgramOffsetWords := none
      quotientProgramWords := 0
      quotientConstLabels := []
      quotientConstHeaders := [] }
  Except.ok vkBase

def generateBaseVk (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂) : Except Fault Halo2VerifyingKey := do
  let pre ← generateBaseVkPrefix inputs
  generateBaseVkBody codecs inputs pre

/-- rust: VK:301-357 (VerifierBuildInputs::generate_vk_direct) @formal-baseline.
    The Rust takes program: &DirectQuotientProgram and calls program.table_words()
    (QDIR:653) once, at VK:314; the port takes that one result, because
    DirectQuotientProgram is P-09's type and table_words is its only use here.
    Recorded, not silent. -/
def generateVkDirect (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂) (tableWords : List VkTableWord) :
    Except Fault Halo2VerifyingKey := do
  let vk0 ← generateBaseVk codecs inputs
  -- VK:313
  let headerWords := vk0.constants.length
  -- VK:314-315
  let extended := vk0.constants ++ tableWords.map (fun w => ("quotient_const", w.value))
  let vk1 : Halo2VerifyingKey := { vk0 with constants := extended }
  -- VK:316-323: the payload layout, with the program section reserved at zero.
  let payloadLayout ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:323"
    (VkPayloadLayout.forVk headerWords tableWords.length 0
      vk1.fixedComms.length vk1.permutationComms.length)
  -- VK:324-328
  let qcOffset ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:327"
    (payloadLayout.wordOffset PayloadSectionKind.quotientConstants)
  -- VK:329
  let vk2 : Halo2VerifyingKey :=
    { vk1 with
      quotientConstOffsetWords := some qcOffset, quotientConstWords := tableWords.length }
  -- VK:330-334
  let qpOffset ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:333"
    (payloadLayout.wordOffset PayloadSectionKind.quotientProgram)
  -- VK:335-342: the program section is empty in the direct lowering; the labels
  -- and headers come from the table words, and enumerate-then-filter means the
  -- index in quotient_const_headers is the index in the WHOLE table and not the
  -- index among the headed words.
  let labels := tableWords.map (fun w => w.label)
  let headers := ((tableWords.zipIdx).filterMap fun (w, idx) =>
    if w.headers.isEmpty then none else some (idx, w.headers))
  let vk3 : Halo2VerifyingKey :=
    { vk2 with
      quotientProgramOffsetWords := some qpOffset, quotientProgramWords := 0,
      quotientConstLabels := labels, quotientConstHeaders := headers }
  -- VK:343-347: assert_eq!(payload_layout.total_bytes(), vk.len()).
  unless (payloadLayout.totalBytes == vk3.len) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:343")
  -- VK:348-349
  unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:349" (vk3.validatePayloadLayout)
  Except.ok vk3

/-! ## The transcript and memory-bound cluster (rust: VK:549-653)

MOVED as a block; see the header. generate_vk (VK:359) calls
meta_data_for_stable_static_layout, which calls meta_data_for_vk, which calls
memory_layout_for, which calls transcript_buffer_layout_for_meta, so the whole
cluster has to precede generate_vk. -/

/-- rust: VK:610-653 (VerifierBuildInputs::transcript_buffer_layout_for_meta)
    @formal-baseline. An associated function - it takes meta and num_instances and
    not &self - so the port has no receiver. The 27-line comment at VK:615-641 is
    the streaming-Keccak bound argument; the claim in it that later code depends on
    is VK:632-635: a word absorb is 32 bytes and an uncompressed G1 absorb is 128,
    NOT the 49 the retired compressed-G1 emitter used, and that is what
    Abi.lean's transcriptWordAbsorbBytes / transcriptG1AbsorbBytes (AP:111,
    AP:114) carry.
    The Rust's ProofCalldataLayout::from_protocol returns Self (AP:122-127), but
    the ported one returns Except Fault because the assert inside it at AP:210 is a
    panic site, so this function's error channel is Fault and the site belongs to
    AP:210 rather than to VK:642. -/
def transcriptBufferLayoutForMeta (meta_ : ConstraintSystemMeta) (numInstances : Nat) :
    Except Fault TranscriptBufferLayout := do
  -- VK:642-647
  let proofLayout ← ProofCalldataLayout.fromProtocol meta_.protocol 0
    meta_.numEvals meta_.numPointSets
  -- VK:648-652
  Except.ok (TranscriptBufferLayout.fromProofLayout proofLayout numInstances
    meta_.protocol.numUserChallenges)

/-- rust: VK:562-599 (VerifierBuildInputs::static_working_memory_size_for_meta)
    @formal-baseline. Private in the Rust. Six candidate ends and
    itertools::max(...).unwrap(); the unwrap cannot fail on a six-element array and
    the port keeps the Option anyway so VK:598 stays a visible site.

    OBJ.7 RECEIVER REFACTOR (card Do 1), stated once for all four defs it touches. The Rust
    is a method on &self and the body reads TWO fields of it: the meta passed in as the
    argument (VK:575-576) and self.num_instances (VK:566). The port therefore takes those
    two values and not the record, which is the same deviation OBJ.6's header records for the
    quotient glue (PlanNew.lean:28-37, R1 arity) and for the same reason: the caller that
    owns the pipeline - OBJ.7's newFromVk - has the meta and the instance count in hand and
    has no VerifierBuildInputs to spend, because the Rust's inputs is built around a
    generate_vk it does not run. Fabricating one to satisfy the old signature would have put
    params := { gLagrange := [], g2 := (), sG2 := () } - five fields the body never reads -
    into the port of a constructor. The &self form is KEPT as a one-line wrapper below
    (staticWorkingMemorySizeForInputs), which is what generateVk and the six VkKats that
    already called these four names now call, so no gate's content moved. -/
def staticWorkingMemorySizeForMeta (meta_ : ConstraintSystemMeta) (numInstances : Nat) :
    Except Fault Nat := do
  -- VK:564
  let pcsComputation := staticWorkingMemorySize
  -- VK:565-566
  let transcript ← transcriptBufferLayoutForMeta meta_ numInstances
  let transcriptWords := transcript.words
  -- VK:567-575: the six ends, in the Rust's order.
  let transcriptEnd := transcriptBufferStart + transcriptWords * wordBytes
  let pcsEnd := pcsPairingScratchStart + pcsComputation * wordBytes
  let pairingBatchEnd := accumulatorPairingBatchPtr + accumulatorPairingBatchHashBytes
  let finalPairingEnd := finalPairingScratchStart + pairingStaticWorkingWords * wordBytes
  let verifierReturnEnd := verifierReturnBufferStart + wordBytes
  let quotientReturnEnd :=
    quotientReturnBufferStart + (2 + meta_.numSimpleSelectors) * wordBytes
  -- VK:577-598
  match natMaximum [transcriptEnd, pcsEnd, pairingBatchEnd, finalPairingEnd,
      verifierReturnEnd, quotientReturnEnd] with
  | some v => Except.ok v
  | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:598")

/-- The &self form of staticWorkingMemorySizeForMeta, kept as a wrapper (see the note on that
    def): the two arguments it forwards are the two fields of the receiver the Rust reads.
    Lean-side scaffolding, not a Rust item. -/
def staticWorkingMemorySizeForInputs (inputs : VerifierBuildInputs p G₁ G₂)
    (meta_ : ConstraintSystemMeta) : Except Fault Nat :=
  staticWorkingMemorySizeForMeta meta_ inputs.numInstances

/-- rust: VK:601-608 (VerifierBuildInputs::transcript_buffer_words_bound),
    #[cfg(test)] in the reference and marked test-only here - the convention
    Layout.lean:41-45 and Kzg.lean:51-56 record. It is in the plan's item map, so
    it is ported rather than skipped. -/
def transcriptBufferWordsBound (meta_ : ConstraintSystemMeta) (numInstances : Nat) :
    Except Fault Nat :=
  Except.map (fun t => t.words) (transcriptBufferLayoutForMeta meta_ numInstances)

/-- rust: VK:549-561 (VerifierBuildInputs::memory_layout_for) @formal-baseline.
    The last line, VerifierMemoryLayout::new(meta, vk, vk_mptr, config)
    (MEM:591-973), is the unported callee threaded through VkBuildEnv; see the
    header. Everything above it - the two config fields the reference fills - is
    ported and gated by memoryLayoutFor_config_ok.
    OBJ.7 RECEIVER REFACTOR (card Do 1; the note on staticWorkingMemorySizeForMeta is the
    one statement of it): the body reads exactly one field of the receiver, num_instances
    (VK:557-559), so the port takes that value and not the record. The &self form is kept as
    memoryLayoutForInputs below. -/
def memoryLayoutFor (env : VkBuildEnv Plan) (meta_ : ConstraintSystemMeta)
    (numInstances : Nat) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) : Except Fault VerifierMemoryLayout := do
  -- VK:557-558
  let t ← transcriptBufferLayoutForMeta meta_ numInstances
  let config1 := { config with transcriptWords := t.words }
  -- VK:559
  let config2 := { config1 with numInstances := numInstances }
  -- VK:560
  Except.ok (env.newVerifierMemoryLayout meta_ vk vkMptr config2)

/-- The &self form of memoryLayoutFor, kept as a wrapper. Lean-side scaffolding. -/
def memoryLayoutForInputs (env : VkBuildEnv Plan) (inputs : VerifierBuildInputs p G₁ G₂)
    (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) : Except Fault VerifierMemoryLayout :=
  memoryLayoutFor env meta_ inputs.numInstances vk vkMptr config

/-- rust: VK:474-523 (VerifierBuildInputs::meta_data_for_vk) @formal-baseline.
    The Phase 3 / outer-fewer-point-sets two-pass Data construction the 16-line
    comment at VK:480-496 describes. R8: VK:505's cfg! is a runtime branch on
    Features here, both arms ported and both gated; the feature is FALSE in
    Features.solidity, so the zero arm is the deployed one and the comment's claim
    that "the result is byte-identical to the pre-Phase-3 single-pass path" is what
    metaDataForVk_featureOff_ok checks.
    The Rust's (*self.meta).clone() at VK:504 is Lean's ordinary value copy.
    OBJ.7 RECEIVER REFACTOR (card Do 1): the body reads two receiver fields - self.meta
    (VK:497, VK:503, VK:504) and self.num_instances (through memory_layout_for) - so the
    port takes those two values. The &self form is kept as metaDataForVkInputs below. -/
def metaDataForVk (feat : Features) (env : VkBuildEnv Plan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    (vk : Halo2VerifyingKey) (vkMptr : Ptr) :
    Except Fault (ConstraintSystemMeta × Data × VerifierMemoryLayout) := do
  -- VK:497-502: pass 1 against the raw meta.
  let rawMemory ← memoryLayoutFor env meta_ numInstances vk vkMptr
    verifierMemoryLayoutConfigDefault
  -- VK:503
  let rawData ← Data.new meta_ vk rawMemory
  -- VK:504-509
  let meta0 := meta_
  let nDummy ← if feat.outerFewerPointSets then numDummyQueries meta0 rawData
                 else Except.ok 0
  -- VK:510-511
  let mainEvals := meta0.numEvals
  let meta1 := meta0.setNumDummyEvals nDummy
  -- VK:512-514
  let memory ← memoryLayoutFor env meta1 numInstances vk vkMptr
    verifierMemoryLayoutConfigDefault
  let data0 ← Data.new meta1 vk memory
  -- VK:515-517
  let data := if nDummy > 0 then data0.setDummyEvalWords mainEvals nDummy else data0
  -- VK:519-522: num_point_sets is written AFTER data is built, and the third
  -- memory layout is built from the meta that carries it. Reordering those three
  -- lines is the mistake this shape is easy to make and
  -- metaDataForVk_pointSetsOrder_ok is what pins it.
  let nSets ← numPointSets meta1 data
  let meta2 := meta1.setNumPointSets nSets
  let memory2 ← memoryLayoutFor env meta2 numInstances vk vkMptr
    verifierMemoryLayoutConfigDefault
  Except.ok (meta2, data, memory2)

/-- The &self form of metaDataForVk, kept as a wrapper. Lean-side scaffolding. -/
def metaDataForVkInputs (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂)
    (vk : Halo2VerifyingKey) (vkMptr : Ptr) :
    Except Fault (ConstraintSystemMeta × Data × VerifierMemoryLayout) :=
  metaDataForVk feat env inputs.meta_ inputs.numInstances vk vkMptr

/-- One iteration of the VK:537-544 stabilisation loop, named so its `rotationLast`
    invariant can be stated and proved. Lean-side scaffolding: the body is the lambda
    `metaDataForStableStaticLayout` folded. -/
def metaDataReservationStep (feat : Features) (env : VkBuildEnv Plan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    (st : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr)
    (_ : Nat) :
    Except Fault (Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr) := do
  if st.1.isSome then Except.ok st else do
    let vkMptr := st.2
    let (metaOut, data, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
    let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
    let cur ← Value.asUsize vkMptr.value
    if planned == cur then
      Except.ok (some (vkMptr, metaOut, data, memory), vkMptr)
    else
      Except.ok (none, ptrMemory (valueFromNat planned))

/-- rust: VK:525-547 (VerifierBuildInputs::meta_data_for_stable_static_layout)
    @formal-baseline. for _ in 0..3 with an early return becomes a List.range 3
    fold carrying an Option result and short-circuiting once it is some - the
    early-exit-flag pattern Abi.lean:535 sets - so both the iteration count and the
    vk_mptr reassignment of VK:543 are preserved. The panic at VK:546 is reached
    exactly when three iterations did not settle.
    OBJ.7 RECEIVER REFACTOR (card Do 1): the loop reads self.meta once (VK:535) and
    self.num_instances only through the two callees, so the port takes the meta and the
    instance count. The &self form is kept as metaDataForStableStaticLayoutInputs below and
    is what generateVk calls, because generate_vk IS a method on the receiver (VK:378-382).
    NOTE THE SHADOWING: the Rust's loop body rebinds `let (meta, data, _) = ...`; the port
    names the converged meta `metaOut` so the parameter stays visible, which is what the
    third iteration's static-size query needs to read. -/
def metaDataForStableStaticLayout (feat : Features) (env : VkBuildEnv Plan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    (vk : Halo2VerifyingKey) :
    Except Fault (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) := do
  -- VK:535
  let start ← staticWorkingMemorySizeForMeta meta_ numInstances
  let startPtr := ptrMemory (valueFromNat start)
  -- VK:537-544
  let (result, _) ← (List.range 3).foldlM
    (metaDataReservationStep feat env meta_ numInstances vk)
    (none, startPtr)
  -- VK:546
  match result with
  | some r => Except.ok r
  | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:546")

private theorem meta_except_bind_ok {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ### `meta_data_for_vk`'s three passes, decomposed (CERT.1)

  `PlanMeta` (`LoweringV3/Statements.lean:595`) asks for `Data.new meta1 vk plan.memory`, where
  `plan.memory` is the FINAL layout (`plan.rs:259-270`, PCS/quotient config, meta after
  `set_num_point_sets`). `meta_data_for_vk` builds its `Data` against the SECOND layout
  (`vk.rs:512-514`, default config, meta before `set_num_point_sets`). The two layouts are not
  syntactically equal, so the equation is not a rewrite; `LayoutMemory`'s
  `new_dataBases_setNumPointSets` supplies the ten pointer equalities `Data.new` actually reads.
  The lemmas below peel the three passes so that the stability fact can be applied to the real
  bind chain instead of a hand-written one. -/

/-- `memoryLayoutFor` returns the concrete constructor: it fills `transcriptWords` and
    `numInstances` and calls `env.newVerifierMemoryLayout`, which `envOf` spells
    `VerifierMemoryLayout.new`. PROVED. -/
theorem memoryLayoutFor_new (env : VkBuildEnv Plan) (meta_ : ConstraintSystemMeta)
    (numInstances : Nat) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) {mem : VerifierMemoryLayout}
    (h : memoryLayoutFor env meta_ numInstances vk vkMptr config = .ok mem) :
    ∃ cfg' : VerifierMemoryLayoutConfig,
      mem = env.newVerifierMemoryLayout meta_ vk vkMptr cfg' := by
  unfold memoryLayoutFor at h
  simp only [Bind.bind] at h
  obtain ⟨t, _, h1⟩ := meta_except_bind_ok h
  let cfg' : VerifierMemoryLayoutConfig :=
    { transcriptWords := t.words, numInstances := numInstances,
      quotientStateWords := config.quotientStateWords,
      quotientStackWords := config.quotientStackWords,
      accMsmTerms := config.accMsmTerms, pcs := config.pcs }
  exact ⟨cfg', (Except.ok.inj h1).symm⟩

/-- **`meta_data_for_vk` AT `Features.solidity` (VK:474-523).** With `outer-fewer-point-sets`
    off the dummy-eval count is the literal `0` (VK:507-509), so the meta the `Data` is built
    from is `meta_.setNumDummyEvals 0`; the returned meta is that value after
    `setNumPointSets n` (VK:519-522), the returned data is the SECOND pass's `Data.new`, and the
    second and third layouts are the concrete constructor on those two metas. Every fact
    `PlanMeta` needs except the layout-stability equation is exposed here. PROVED. -/
theorem metaDataForVk_parts (feat : Features) (env : VkBuildEnv Plan)
    (m : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (hfew : feat.outerFewerPointSets = false)
    {meta' : ConstraintSystemMeta} {dat : Data} {mem : VerifierMemoryLayout}
    (h : metaDataForVk feat env m numInstances vk vkMptr = .ok (meta', dat, mem)) :
    ∃ (rawMemory memory : VerifierMemoryLayout) (rawData data0 : Data) (n : Nat),
      memoryLayoutFor env m numInstances vk vkMptr
          verifierMemoryLayoutConfigDefault = .ok rawMemory ∧
      Data.new m vk rawMemory = .ok rawData ∧
      memoryLayoutFor env (m.setNumDummyEvals 0) numInstances vk vkMptr
          verifierMemoryLayoutConfigDefault = .ok memory ∧
      Data.new (m.setNumDummyEvals 0) vk memory = .ok data0 ∧
      dat = data0 ∧
      numPointSets (m.setNumDummyEvals 0) dat = .ok n ∧
      meta' = (m.setNumDummyEvals 0).setNumPointSets n ∧
      memoryLayoutFor env meta' numInstances vk vkMptr
          verifierMemoryLayoutConfigDefault = .ok mem := by
  unfold metaDataForVk at h
  simp only [Bind.bind, hfew, Bool.false_eq_true, ite_false] at h
  obtain ⟨rawMemory, hrm, h1⟩ := meta_except_bind_ok h
  obtain ⟨rawData, hrd, h2⟩ := meta_except_bind_ok h1
  obtain ⟨nDummy, hnd, h3⟩ := meta_except_bind_ok h2
  cases hnd
  obtain ⟨memory, hmem, h4⟩ := meta_except_bind_ok h3
  obtain ⟨data0, hdata0, h5⟩ := meta_except_bind_ok h4
  simp only [Nat.lt_irrefl, ite_false] at h5
  obtain ⟨n, hn, h6⟩ := meta_except_bind_ok h5
  obtain ⟨memory2, hmem2, h7⟩ := meta_except_bind_ok h6
  have hval : ((m.setNumDummyEvals 0).setNumPointSets n, data0, memory2) = (meta', dat, mem) :=
    Except.ok.inj h7
  simp only [Prod.mk.injEq] at hval
  obtain ⟨hmeta', hdat', hmem'⟩ := hval
  exact ⟨rawMemory, memory, rawData, data0, n, hrm, hrd, hmem, hdata0, hdat'.symm, by
      rw [← hdat']; exact hn, hmeta'.symm, by rw [← hmem', ← hmeta']; exact hmem2⟩

/-- One stabilisation step: if it settles, its witness is `metaDataForVk` at the pointer
    stored in the step's state (`VK:537-544` returns `(vk_mptr, metaOut, data, memory)`). -/
theorem metaDataReservationStep_metaDataForVk {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    {st st' : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr}
    (x : Nat) (h : metaDataReservationStep feat env meta_ numInstances vk st x = .ok st')
    (hinv : ∀ r, st.1 = some r →
      metaDataForVk feat env meta_ numInstances vk r.1 = .ok (r.2.1, r.2.2.1, r.2.2.2)) :
    ∀ r, st'.1 = some r →
      metaDataForVk feat env meta_ numInstances vk r.1 = .ok (r.2.1, r.2.2.1, r.2.2.2) := by
  unfold metaDataReservationStep at h
  by_cases hb : st.1.isSome
  · simp only [hb, ite_true] at h
    cases h
    exact hinv
  · simp only [hb, ite_false, Bool.false_eq_true] at h
    obtain ⟨md, hmd, h⟩ := meta_except_bind_ok h
    obtain ⟨_planned, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_cur, _, h⟩ := meta_except_bind_ok h
    split at h
    · cases h
      intro r hr
      simp only [Option.some.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hmd
    · cases h
      intro r hr
      simp at hr

/-- The stabilisation fold keeps the witness property: a settled result is `metaDataForVk`
    at its own pointer. -/
theorem foldlM_metaDataReservationStep_metaDataForVk (l : List Nat)
    {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    (st st' : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr)
    (h : l.foldlM (metaDataReservationStep feat env meta_ numInstances vk) st = .ok st')
    (hinv : ∀ r, st.1 = some r →
      metaDataForVk feat env meta_ numInstances vk r.1 = .ok (r.2.1, r.2.2.1, r.2.2.2)) :
    ∀ r, st'.1 = some r →
      metaDataForVk feat env meta_ numInstances vk r.1 = .ok (r.2.1, r.2.2.1, r.2.2.2) := by
  induction l generalizing st with
  | nil =>
      change Except.ok st = Except.ok st' at h
      injection h with hst
      subst hst
      exact hinv
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : metaDataReservationStep feat env meta_ numInstances vk st x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          exact ih s1 h (metaDataReservationStep_metaDataForVk x hs hinv)

/-- **THE INTERMEDIATE Layout AND THE FINAL ONE COME FROM ONE `meta_data_for_vk` CALL.**
    `meta_data_for_stable_static_layout` (VK:525-547) only iterates `meta_data_for_vk` with the
    same `meta_`, so the tuple it returns is one call's result: the data and the meta are those
    of the same two passes that built the plan's payload. This is what lets `PlanMeta`'s
    `Data.new` equation be checked against a layout the constructor actually produced. PROVED. -/
theorem metaDataForStableStaticLayout_metaDataForVk {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    {vkMptr : Ptr} {metaOut : ConstraintSystemMeta} {dat : Data}
    {memory : VerifierMemoryLayout}
    (h : metaDataForStableStaticLayout feat env meta_ numInstances vk =
      .ok (vkMptr, metaOut, dat, memory)) :
    metaDataForVk feat env meta_ numInstances vk vkMptr = .ok (metaOut, dat, memory) := by
  simp only [metaDataForStableStaticLayout] at h
  obtain ⟨start, _, h⟩ := meta_except_bind_ok h
  obtain ⟨⟨result, lastPtr⟩, hres, h⟩ := meta_except_bind_ok h
  cases result with
  | none =>
      simp only at h
      cases h
  | some r =>
      cases h
      exact foldlM_metaDataReservationStep_metaDataForVk (List.range 3)
        (none, ptrMemory (valueFromNat start))
        (some (vkMptr, metaOut, dat, memory), lastPtr) hres
        (by intro q hq; simp at hq) (vkMptr, metaOut, dat, memory) rfl

/-- `metaDataForVk` changes `numEvals`, `numDummyEvals` and `numPointSets` only, so the
    rotation survives. PROVED. -/
theorem metaDataForVk_rotationLast {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    {vkMptr : Ptr} {metaOut : ConstraintSystemMeta} {data : Data}
    {memory : VerifierMemoryLayout}
    (h : metaDataForVk feat env meta_ numInstances vk vkMptr = .ok (metaOut, data, memory)) :
    metaOut.rotationLast = meta_.rotationLast := by
  simp only [metaDataForVk] at h
  obtain ⟨_rawMemory, _, h⟩ := meta_except_bind_ok h
  obtain ⟨_rawData, _, h⟩ := meta_except_bind_ok h
  split at h
  · obtain ⟨_nDummy, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_memory, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_data0, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_nSets, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_memory2, _, h⟩ := meta_except_bind_ok h
    cases h
    rfl
  · obtain ⟨_nDummy, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_memory, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_data0, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_nSets, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_memory2, _, h⟩ := meta_except_bind_ok h
    cases h
    rfl

/-- One stabilisation step keeps every stored meta's rotation. PROVED. -/
theorem metaDataReservationStep_rotationLast {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    {st st' : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr}
    (x : Nat) (h : metaDataReservationStep feat env meta_ numInstances vk st x = .ok st')
    (hinv : ∀ r, st.1 = some r → r.2.1.rotationLast = meta_.rotationLast) :
    ∀ r, st'.1 = some r → r.2.1.rotationLast = meta_.rotationLast := by
  unfold metaDataReservationStep at h
  by_cases hb : st.1.isSome
  · simp only [hb, if_true] at h
    cases h
    exact hinv
  · simp only [hb, if_false, Bool.false_eq_true] at h
    obtain ⟨metaOut, hmeta, h⟩ := meta_except_bind_ok h
    obtain ⟨_planned, _, h⟩ := meta_except_bind_ok h
    obtain ⟨_cur, _, h⟩ := meta_except_bind_ok h
    split at h
    · cases h
      intro r hr
      simp only [Prod.mk.injEq, Option.some.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact metaDataForVk_rotationLast hmeta
    · cases h
      intro r hr
      simp at hr

/-- The stabilisation fold keeps every stored meta's rotation. PROVED. -/
theorem foldlM_metaDataReservationStep_rotationLast (l : List Nat)
    {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    (st st' : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr)
    (h : l.foldlM (metaDataReservationStep feat env meta_ numInstances vk) st = .ok st')
    (hinv : ∀ r, st.1 = some r → r.2.1.rotationLast = meta_.rotationLast) :
    ∀ r, st'.1 = some r → r.2.1.rotationLast = meta_.rotationLast := by
  induction l generalizing st with
  | nil =>
      change Except.ok st = Except.ok st' at h
      injection h with hst
      subst hst
      exact hinv
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : metaDataReservationStep feat env meta_ numInstances vk st x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          exact ih s1 h (metaDataReservationStep_rotationLast x hs hinv)

/-- `metaDataForStableStaticLayout` converges to a meta with the input's rotation.
    PROVED. -/
theorem metaDataForStableStaticLayout_rotationLast {feat : Features} {env : VkBuildEnv Plan}
    {meta_ : ConstraintSystemMeta} {numInstances : Nat} {vk : Halo2VerifyingKey}
    {vkMptr : Ptr} {metaOut : ConstraintSystemMeta} {data : Data}
    {memory : VerifierMemoryLayout}
    (h : metaDataForStableStaticLayout feat env meta_ numInstances vk =
      .ok (vkMptr, metaOut, data, memory)) :
    metaOut.rotationLast = meta_.rotationLast := by
  simp only [metaDataForStableStaticLayout] at h
  obtain ⟨start, _, h⟩ := meta_except_bind_ok h
  obtain ⟨⟨result, lastPtr⟩, hres, h⟩ := meta_except_bind_ok h
  cases result with
  | none =>
      simp only at h
      cases h
  | some r =>
      cases h
      exact foldlM_metaDataReservationStep_rotationLast (List.range 3)
        (none, ptrMemory (valueFromNat start))
        (some (vkMptr, metaOut, data, memory), lastPtr) hres
        (by intro q hq; simp at hq) (vkMptr, metaOut, data, memory) rfl

/-- The &self form of metaDataForStableStaticLayout, kept as a wrapper: this is the call
    generate_vk (VK:378, VK:450) and plan.rs's constructor (PL:238) make on the receiver. -/
def metaDataForStableStaticLayoutInputs (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (vk : Halo2VerifyingKey) :
    Except Fault (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) :=
  metaDataForStableStaticLayout feat env inputs.meta_ inputs.numInstances vk

/-! ## generate_vk (rust: VK:353-472)

The reservation loop, the eight asserts, and hazard 5's panic. -/

/-- Scaffolding, not a Rust item: the four locals the for _ in 0..8 loop of
    VK:367-393 mutates, bundled so the fold can thread them. Field order is the
    Rust's declaration order (VK:360, VK:363, VK:364, VK:365). -/
structure VkReservationState where
  vk : Halo2VerifyingKey
  quotientConstWords : Nat
  quotientProgramWords : Nat
  build : Option VkQuotientBuild

private theorem reserve_except_bind_ok {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- One iteration of the VK reservation loop, named so its length invariant can be stated. -/
def reserveStep (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat)
    (st : VkReservationState) (_ : Nat) : Except Fault VkReservationState := do
  if st.build.isSome then Except.ok st else do
    let zeroFilled := st.vk.constants.take headerWords
      ++ List.replicate st.quotientConstWords ("quotient_const", 0)
      ++ List.replicate st.quotientProgramWords ("quotient_program", 0)
    let vkZ0 : Halo2VerifyingKey := { st.vk with constants := zeroFilled }
    let vkZ : Halo2VerifyingKey :=
      { vkZ0 with
        quotientConstOffsetWords := none, quotientConstWords := 0,
        quotientProgramOffsetWords := none, quotientProgramWords := 0 }
    let (_, meta_, data, _) ← metaDataForStableStaticLayoutInputs feat env inputs vkZ
    let candidate ← env.compactQuotientProgramFor meta_ data
    let candidateConstWords := candidate.consts.length
    let candidateProgramWords := PackedProgramCodec.wordLenForBytes candidate.bytes.size
    if candidateConstWords ≤ st.quotientConstWords &&
        candidateProgramWords ≤ st.quotientProgramWords then
      Except.ok
        { vk := vkZ, quotientConstWords := st.quotientConstWords,
          quotientProgramWords := st.quotientProgramWords, build := some candidate }
    else
      Except.ok
        { vk := vkZ,
          quotientConstWords := max st.quotientConstWords candidateConstWords,
          quotientProgramWords := max st.quotientProgramWords candidateProgramWords,
          build := none }

theorem listSetMut_getD_lt {α : Type} (xs : List α) (i : Nat) (v : α) (site : String)
    (xs' : List α) (h : listSetMut xs i v site = .ok xs') (k : Nat) (hk : k < i) (d : α) :
    xs'.getD k d = xs.getD k d := by
  unfold listSetMut at h
  split at h
  · injection h with hb
    subst hb
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [update_get?_other xs i v (by assumption) k (by omega)]
  · cases h

theorem reserveStep_getD (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat)
    (st st' : VkReservationState) (x : Nat)
    (h : reserveStep feat env inputs headerWords st x = .ok st') (k : Nat) (hk : k < headerWords)
    (hlen : headerWords ≤ st.vk.constants.length) (d : String × Word256) :
    st'.vk.constants.getD k d = st.vk.constants.getD k d := by
  unfold reserveStep at h
  by_cases hb : st.build.isSome
  · simp only [hb, if_true] at h; cases h; rfl
  · simp only [hb, if_false, Bool.false_eq_true] at h
    obtain ⟨_meta, _, h⟩ := reserve_except_bind_ok h
    obtain ⟨_cand, _, h⟩ := reserve_except_bind_ok h
    split at h <;> cases h
    all_goals
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.append_assoc]
      rw [List.getElem?_append_left (by rw [List.length_take]; omega)]
      rw [List.getElem?_take_of_lt hk]

theorem reserveStep_ge (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat)
    (st st' : VkReservationState) (x : Nat)
    (h : reserveStep feat env inputs headerWords st x = .ok st')
    (hge : headerWords ≤ st.vk.constants.length) :
    headerWords ≤ st'.vk.constants.length := by
  unfold reserveStep at h
  by_cases hb : st.build.isSome
  · simp only [hb, if_true] at h
    cases h
    exact hge
  · simp only [hb, if_false, Bool.false_eq_true] at h
    obtain ⟨_meta, _, h⟩ := reserve_except_bind_ok h
    obtain ⟨_cand, _, h⟩ := reserve_except_bind_ok h
    split at h <;> cases h
    all_goals
      simp only [List.length_append, List.length_take, List.length_replicate] at *
      omega

theorem foldlM_reserve_getD (l : List Nat) (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat)
    (init st : VkReservationState)
    (h : l.foldlM (reserveStep feat env inputs headerWords) init = .ok st)
    (k : Nat) (hk : k < headerWords) (hlen : headerWords ≤ init.vk.constants.length)
    (d : String × Word256) :
    st.vk.constants.getD k d = init.vk.constants.getD k d := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      injection h with hst
      subst hst
      rfl
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : reserveStep feat env inputs headerWords init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          have hge : headerWords ≤ s1.vk.constants.length :=
            reserveStep_ge feat env inputs headerWords init s1 x hs hlen
          rw [ih s1 h hge, reserveStep_getD feat env inputs headerWords init s1 x hs k hk hlen d]

theorem foldlM_reserve_ge (l : List Nat) (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat)
    (init st : VkReservationState)
    (h : l.foldlM (reserveStep feat env inputs headerWords) init = .ok st)
    (hge : headerWords ≤ init.vk.constants.length) :
    headerWords ≤ st.vk.constants.length := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      injection h with hst
      subst hst
      exact hge
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : reserveStep feat env inputs headerWords init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          exact ih s1 h (reserveStep_ge feat env inputs headerWords init s1 x hs hge)

def fillConstStep (offset : Nat) (vk : Halo2VerifyingKey) (pair : Word256 × Nat) :
    Except Fault Halo2VerifyingKey := do
  let (value, i) := pair
  let cs ← listSetMut vk.constants (offset + i) ("quotient_const", value)
    "proofs/solidity-verifier/src/lowering/vk.rs:444"
  Except.ok ({ vk with constants := cs } : Halo2VerifyingKey)

/-- One program write-back step of `generateVk`. -/
def fillProgramStep (offset : Nat) (vk : Halo2VerifyingKey) (pair : Word256 × Nat) :
    Except Fault Halo2VerifyingKey := do
  let (value, i) := pair
  let cs ← listSetMut vk.constants (offset + i) ("quotient_program", value)
    "proofs/solidity-verifier/src/lowering/vk.rs:447"
  Except.ok ({ vk with constants := cs } : Halo2VerifyingKey)
theorem fillConstStep_getD (offset : Nat) (vk vk' : Halo2VerifyingKey)
    (pair : Word256 × Nat) (h : fillConstStep offset vk pair = .ok vk')
    (k : Nat) (hk : k < offset) (d : String × Word256) :
    vk'.constants.getD k d = vk.constants.getD k d := by
  unfold fillConstStep at h
  obtain ⟨value, i⟩ := pair
  obtain ⟨cs, hcs, h⟩ := reserve_except_bind_ok h
  cases h
  change cs.getD k d = vk.constants.getD k d
  exact listSetMut_getD_lt vk.constants (offset + i) (("quotient_const", value) : String × Word256)
    "proofs/solidity-verifier/src/lowering/vk.rs:444" cs hcs k (by omega) d

theorem fillProgramStep_getD (offset : Nat) (vk vk' : Halo2VerifyingKey)
    (pair : Word256 × Nat) (h : fillProgramStep offset vk pair = .ok vk')
    (k : Nat) (hk : k < offset) (d : String × Word256) :
    vk'.constants.getD k d = vk.constants.getD k d := by
  unfold fillProgramStep at h
  obtain ⟨value, i⟩ := pair
  obtain ⟨cs, hcs, h⟩ := reserve_except_bind_ok h
  cases h
  change cs.getD k d = vk.constants.getD k d
  exact listSetMut_getD_lt vk.constants (offset + i) (("quotient_program", value) : String × Word256)
    "proofs/solidity-verifier/src/lowering/vk.rs:447" cs hcs k (by omega) d

theorem foldlM_fillConst_getD (l : List (Word256 × Nat)) (offset : Nat)
    (init st : Halo2VerifyingKey)
    (h : l.foldlM (fillConstStep offset) init = .ok st)
    (k : Nat) (hk : k < offset) (d : String × Word256) :
    st.constants.getD k d = init.constants.getD k d := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      injection h with hst
      subst hst
      rfl
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : fillConstStep offset init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          rw [ih s1 h, fillConstStep_getD offset init s1 x hs k hk d]

theorem foldlM_fillProgram_getD (l : List (Word256 × Nat)) (offset : Nat)
    (init st : Halo2VerifyingKey)
    (h : l.foldlM (fillProgramStep offset) init = .ok st)
    (k : Nat) (hk : k < offset) (d : String × Word256) :
    st.constants.getD k d = init.constants.getD k d := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      injection h with hst
      subst hst
      rfl
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : fillProgramStep offset init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          rw [ih s1 h, fillProgramStep_getD offset init s1 x hs k hk d]

theorem listSetMut_length {α : Type} (xs : List α) (i : Nat) (v : α) (site : String)
    (xs' : List α) (h : listSetMut xs i v site = .ok xs') : xs'.length = xs.length := by
  unfold listSetMut at h
  split at h
  · cases h
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
      List.length_nil]
    omega
  · cases h

theorem fillConstStep_ge (H : Nat) (offset : Nat) (vk vk' : Halo2VerifyingKey)
    (pair : Word256 × Nat)
    (h : fillConstStep offset vk pair = .ok vk') (hge : H ≤ vk.constants.length) :
    H ≤ vk'.constants.length := by
  unfold fillConstStep at h
  obtain ⟨value, i⟩ := pair
  obtain ⟨cs, hcs, h⟩ := reserve_except_bind_ok h
  cases h
  change H ≤ cs.length
  have := listSetMut_length vk.constants (offset + i) (("quotient_const", value) : String × Word256)
    "proofs/solidity-verifier/src/lowering/vk.rs:444" cs hcs
  omega

theorem fillProgramStep_ge (H : Nat) (offset : Nat) (vk vk' : Halo2VerifyingKey)
    (pair : Word256 × Nat)
    (h : fillProgramStep offset vk pair = .ok vk') (hge : H ≤ vk.constants.length) :
    H ≤ vk'.constants.length := by
  unfold fillProgramStep at h
  obtain ⟨value, i⟩ := pair
  obtain ⟨cs, hcs, h⟩ := reserve_except_bind_ok h
  cases h
  change H ≤ cs.length
  have := listSetMut_length vk.constants (offset + i) (("quotient_program", value) : String × Word256)
    "proofs/solidity-verifier/src/lowering/vk.rs:447" cs hcs
  omega
theorem foldlM_fillConst_ge (H : Nat) (l : List (Word256 × Nat)) (offset : Nat)
    (init st : Halo2VerifyingKey)
    (h : l.foldlM (fillConstStep offset) init = .ok st)
    (hge : H ≤ init.constants.length) : H ≤ st.constants.length := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      injection h with hst
      subst hst
      exact hge
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : fillConstStep offset init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          exact ih s1 h (fillConstStep_ge H offset init s1 x hs hge)

theorem foldlM_fillProgram_ge (H : Nat) (l : List (Word256 × Nat)) (offset : Nat)
    (init st : Halo2VerifyingKey)
    (h : l.foldlM (fillProgramStep offset) init = .ok st)
    (hge : H ≤ init.constants.length) : H ≤ st.constants.length := by
  induction l generalizing init with
  | nil =>
      change Except.ok init = Except.ok st at h
      injection h with hst
      subst hst
      exact hge
  | cons x xs ih =>
      simp only [List.foldlM_cons] at h
      cases hs : fillProgramStep offset init x with
      | error e => simp only [hs] at h; cases h
      | ok s1 =>
          simp only [hs] at h
          exact ih s1 h (fillProgramStep_ge H offset init s1 x hs hge)

/-- rust: VK:353-472 (VerifierBuildInputs::generate_vk) @formal-baseline.
    HAZARD 5 lives at VK:434-437: the assert that the quotient const table did not
    exceed the VK payload reservation. It is ported as a Fault.panic at that site.
    PLAN 9.5's Supported has no field for the invariant - that is a
    statement-surface question for the orchestrator and is reported, not invented
    here. -/
structure VkLayoutChecked where
  qbuild : VkQuotientBuild
  constOffset : Nat
  programOffset : Nat
  chunks : List Word256

def generateVkLayoutChecks (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat) (st : VkReservationState) :
    Except Fault VkLayoutChecked := do
  -- VK:395-399
  let quotientProgramBuild ← match st.build with
    | some b => Except.ok b
    | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:396")
  -- VK:400-407
  let payloadLayout ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:407"
    (VkPayloadLayout.forVk headerWords st.quotientConstWords st.quotientProgramWords
      st.vk.fixedComms.length st.vk.permutationComms.length)
  -- VK:408-413
  let quotientConstOffsetWords ← unwrapAt
    "proofs/solidity-verifier/src/lowering/vk.rs:410"
    (payloadLayout.wordOffset PayloadSectionKind.quotientConstants)
  let quotientProgramOffsetWords ← unwrapAt
    "proofs/solidity-verifier/src/lowering/vk.rs:413"
    (payloadLayout.wordOffset PayloadSectionKind.quotientProgram)
  -- VK:414-425: the two section-length asserts.
  let qcLen ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:417"
    (payloadLayout.wordLen PayloadSectionKind.quotientConstants)
  unless (qcLen == st.quotientConstWords) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:414")
  let qpLen ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:422"
    (payloadLayout.wordLen PayloadSectionKind.quotientProgram)
  unless (qpLen == st.quotientProgramWords) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:420")
  -- VK:426-430
  unless (payloadLayout.totalBytes == st.vk.len) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:426")
  -- VK:432-433
  let quotientProgramChunks := PackedProgramCodec.encodeWords quotientProgramBuild.bytes
  -- VK:434-437: HAZARD 5.
  unless (quotientProgramBuild.consts.length ≤ st.quotientConstWords) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:436")
  -- VK:438-441
  unless (quotientProgramChunks.length ≤ st.quotientProgramWords) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:438")
  let out : VkLayoutChecked :=
    { qbuild := quotientProgramBuild, constOffset := quotientConstOffsetWords,
      programOffset := quotientProgramOffsetWords, chunks := quotientProgramChunks }
  pure out

def generateVkFillAndFinal (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (st : VkReservationState)
    (lc : VkLayoutChecked) : Except Fault Halo2VerifyingKey := do
  let quotientProgramBuild := lc.qbuild
  let quotientConstOffsetWords := lc.constOffset
  let quotientProgramOffsetWords := lc.programOffset
  let quotientProgramChunks := lc.chunks
  -- VK:443-448: the two write-back loops. vk.constants[i] = .. is a direct index,
  -- so an out-of-range write is a panic in both profiles (rule R4) even though the
  -- two asserts above make it unreachable.
  let vkFilled ← quotientProgramBuild.consts.zipIdx.foldlM
    (fillConstStep quotientConstOffsetWords) st.vk
  let vkFilled2 ← quotientProgramChunks.zipIdx.foldlM
    (fillProgramStep quotientProgramOffsetWords) vkFilled
  -- VK:450-455
  let (_, finalMeta, finalData, _) ←
    metaDataForStableStaticLayoutInputs feat env inputs vkFilled2
  let finalPlan ← env.quotientProgramPlan finalMeta finalData
  let finalQuotientBuild ← env.buildQuotientProgramItems finalPlan
  -- VK:456-463: the two "changed after materialisation" asserts.
  unless (finalQuotientBuild.bytes == quotientProgramBuild.bytes) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:457")
  unless (finalQuotientBuild.consts == quotientProgramBuild.consts) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:461")
  -- VK:465-470
  let vkFinal : Halo2VerifyingKey :=
    { vkFilled2 with
      quotientConstOffsetWords := some quotientConstOffsetWords,
      quotientConstWords := st.quotientConstWords,
      quotientProgramOffsetWords := some quotientProgramOffsetWords,
      quotientProgramWords := st.quotientProgramWords }
  unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:470" (vkFinal.validatePayloadLayout)
  Except.ok vkFinal

def generateVkFinalize (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂) (headerWords : Nat)
    (st : VkReservationState) : Except Fault Halo2VerifyingKey := do
  let lc ← generateVkLayoutChecks feat env inputs headerWords st
  generateVkFillAndFinal feat env inputs st lc

def generateVk (feat : Features) (env : VkBuildEnv Plan)
    (codecs : VkPointCodecs G₁ G₂) (inputs : VerifierBuildInputs p G₁ G₂) :
    Except Fault Halo2VerifyingKey := do
  -- VK:360
  let vk0 ← generateBaseVk codecs inputs
  -- VK:362
  let headerWords := vk0.constants.length
  -- VK:363-366
  let init : VkReservationState :=
    { vk := vk0, quotientConstWords := 0, quotientProgramWords := 0, build := none }
  -- VK:367-393
  let st ← (List.range 8).foldlM (reserveStep feat env inputs headerWords) init
  generateVkFinalize feat env inputs headerWords st


end Midfall.Generator

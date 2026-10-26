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
import Midfall.Instances.ExponentModel

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
      let step (b : VkHeaderBuilder) (pair : Nat × (String × Word256)) :
          Except String VkHeaderBuilder := do
        let (offset, value) := pair
        let word := start + offset
        match b.words[word]? with
        | some (some _) =>
            Except.error ("VK header field " ++ spec.name
              ++ " overlaps already-written word " ++ toString word)
        | _ =>
            Except.ok { words := b.words.take word ++ [some value]
              ++ b.words.drop (word + 1) }
      (List.zip (List.range values.length) values).foldlM step self

/-- rust: LM:623-631 (VkHeaderBuilder::scalar) @formal-baseline. -/
def VkHeaderBuilder.scalar (self : VkHeaderBuilder) (slot : VkHeaderSlot)
    (name : String) (value : Word256) : Except String VkHeaderBuilder :=
  self.insert slot 1 [(name, value)]

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
def generateBaseVk (codecs : VkPointCodecs G₁ G₂)
    (inputs : VerifierBuildInputs p G₁ G₂) : Except Fault Halo2VerifyingKey := do
  -- VK:100: let domain = self.vk.get_domain();
  let domain := inputs.vk.domain
  -- VK:109: fe_to_u256::<Fq>(&self.vk.transcript_repr())
  let vkDigest ← feToU256 (bytesToNats (frToRepr inputs.vk.transcriptRepr))
  -- VK:110-111: U256::from(usize) for the instance count and the domain exponent.
  let numInstancesW : Word256 := BitVec.ofNat 256 inputs.numInstances
  let kW : Word256 := BitVec.ofNat 256 domain.k
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
  -- VK:145-150: srs_g1_base = sum of g_lagrange, from the identity.
  let g_lagrange := inputs.params.gLagrange
  let srsG1Base := g_lagrange.foldl (fun acc g => acc * g) 1
  -- VK:151-156: assert_eq!(srs_g1_base, G1Affine::generator()). The first of the
  -- three SRS controls the audit calls H-1: the only build-time check that can
  -- catch a substituted SRS, because every other control in the repository checks
  -- self-consistency and a substituted SRS is perfectly self-consistent.
  unless (decideBool (P.decEqG₁ srsG1Base P.g₁)) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:151")
  -- VK:157-159
  let g1Pt : G₁ := P.g₁
  let g2Pt : G₂ := inputs.params.g2
  let negSG2Pt : G₂ := inputs.params.sG2⁻¹
  -- VK:180-185: assert_eq!(g2_pt, G2Affine::generator()).
  unless (g2Pt == P.g₂) do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:180")
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
  let h0 := VkHeaderLayout.builder
  let h1 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:211"
    (h0.scalar .vkDigest "vk_digest" vkDigest)
  let h2 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:212"
    (h1.scalar .numInstances "num_instances" numInstancesW)
  let h3 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:213"
    (h2.scalar .k "k" kW)
  let h4 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:214"
    (h3.scalar .nInv "n_inv" nInv)
  let h5 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:215"
    (h4.scalar .omega "omega" omega)
  let h6 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:216"
    (h5.scalar .omegaInv "omega_inv" omegaInv)
  let h7 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:217"
    (h6.scalar .omegaInvToL "omega_inv_to_l" omegaInvToL)
  let h8 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:218"
    (h7.scalar .hasAccumulator "has_accumulator" hasAccumulator)
  let h9 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:219"
    (h8.scalar .accOffset "acc_offset" accOffset)
  let h10 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:220"
    (h9.scalar .numAccLimbs "num_acc_limbs" numAccLimbs)
  let h11 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:222"
    (h10.scalar .numAccLimbBits "num_acc_limb_bits" numAccLimbBits)
  let h12 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:225"
    (h11.g1 .g1Base ["g1_x_hi", "g1_x_lo", "g1_y_hi", "g1_y_lo"] g1Words)
  let h13 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:231"
    (h12.g2 .g2Base ["g2_x_c0_hi", "g2_x_c0_lo", "g2_x_c1_hi", "g2_x_c1_lo",
      "g2_y_c0_hi", "g2_y_c0_lo", "g2_y_c1_hi", "g2_y_c1_lo"] g2Words)
  let h14 ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:247"
    (h13.g2 .negSG2Base ["neg_s_g2_x_c0_hi", "neg_s_g2_x_c0_lo", "neg_s_g2_x_c1_hi",
      "neg_s_g2_x_c1_lo", "neg_s_g2_y_c0_hi", "neg_s_g2_y_c0_lo", "neg_s_g2_y_c1_hi",
      "neg_s_g2_y_c1_lo"] negSG2Words)
  let constants ← unwrapAt "proofs/solidity-verifier/src/lowering/vk.rs:264" (h14.finish)
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
    the port keeps the Option anyway so VK:598 stays a visible site. -/
def staticWorkingMemorySizeForMeta (inputs : VerifierBuildInputs p G₁ G₂)
    (meta_ : ConstraintSystemMeta) : Except Fault Nat := do
  -- VK:564
  let pcsComputation := staticWorkingMemorySize
  -- VK:565-566
  let transcript ← transcriptBufferLayoutForMeta meta_ inputs.numInstances
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
    ported and gated by memoryLayoutFor_config_ok. -/
def memoryLayoutFor (env : VkBuildEnv Plan) (inputs : VerifierBuildInputs p G₁ G₂)
    (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) : Except Fault VerifierMemoryLayout := do
  -- VK:557-558
  let t ← transcriptBufferLayoutForMeta meta_ inputs.numInstances
  let config1 := { config with transcriptWords := t.words }
  -- VK:559
  let config2 := { config1 with numInstances := inputs.numInstances }
  -- VK:560
  Except.ok (env.newVerifierMemoryLayout meta_ vk vkMptr config2)

/-- rust: VK:474-523 (VerifierBuildInputs::meta_data_for_vk) @formal-baseline.
    The Phase 3 / outer-fewer-point-sets two-pass Data construction the 16-line
    comment at VK:480-496 describes. R8: VK:505's cfg! is a runtime branch on
    Features here, both arms ported and both gated; the feature is FALSE in
    Features.solidity, so the zero arm is the deployed one and the comment's claim
    that "the result is byte-identical to the pre-Phase-3 single-pass path" is what
    metaDataForVk_featureOff_ok checks.
    The Rust's (*self.meta).clone() at VK:504 is Lean's ordinary value copy. -/
def metaDataForVk (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂)
    (vk : Halo2VerifyingKey) (vkMptr : Ptr) :
    Except Fault (ConstraintSystemMeta × Data × VerifierMemoryLayout) := do
  -- VK:497-502: pass 1 against the raw meta.
  let rawMemory ← memoryLayoutFor env inputs inputs.meta_ vk vkMptr
    verifierMemoryLayoutConfigDefault
  -- VK:503
  let rawData ← Data.new inputs.meta_ vk rawMemory
  -- VK:504-509
  let meta0 := inputs.meta_
  let nDummy ← if feat.outerFewerPointSets then numDummyQueries meta0 rawData
                 else Except.ok 0
  -- VK:510-511
  let mainEvals := meta0.numEvals
  let meta1 := meta0.setNumDummyEvals nDummy
  -- VK:512-514
  let memory ← memoryLayoutFor env inputs meta1 vk vkMptr
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
  let memory2 ← memoryLayoutFor env inputs meta2 vk vkMptr
    verifierMemoryLayoutConfigDefault
  Except.ok (meta2, data, memory2)

/-- rust: VK:525-547 (VerifierBuildInputs::meta_data_for_stable_static_layout)
    @formal-baseline. for _ in 0..3 with an early return becomes a List.range 3
    fold carrying an Option result and short-circuiting once it is some - the
    early-exit-flag pattern Abi.lean:535 sets - so both the iteration count and the
    vk_mptr reassignment of VK:543 are preserved. The panic at VK:546 is reached
    exactly when three iterations did not settle. -/
def metaDataForStableStaticLayout (feat : Features) (env : VkBuildEnv Plan)
    (inputs : VerifierBuildInputs p G₁ G₂)
    (vk : Halo2VerifyingKey) :
    Except Fault (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) := do
  -- VK:535
  let start ← staticWorkingMemorySizeForMeta inputs inputs.meta_
  let startPtr := ptrMemory (valueFromNat start)
  -- VK:537-544
  let (result, _) ← (List.range 3).foldlM
    (fun st _ => do
      if st.1.isSome then Except.ok st else do
        let vkMptr := st.2
        let (meta_, data, memory) ← metaDataForVk feat env inputs vk vkMptr
        let planned ← staticWorkingMemorySizeForMeta inputs meta_
        let cur ← Value.asUsize vkMptr.value
        if planned == cur then
          Except.ok (some (vkMptr, meta_, data, memory), vkMptr)
        else
          Except.ok (none, ptrMemory (valueFromNat planned)))
    (none, startPtr)
  -- VK:546
  match result with
  | some r => Except.ok r
  | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:546")

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

/-- rust: VK:353-472 (VerifierBuildInputs::generate_vk) @formal-baseline.
    HAZARD 5 lives at VK:434-437: the assert that the quotient const table did not
    exceed the VK payload reservation. It is ported as a Fault.panic at that site.
    PLAN 9.5's Supported has no field for the invariant - that is a
    statement-surface question for the orchestrator and is reported, not invented
    here. -/
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
  let st ← (List.range 8).foldlM (fun st _ => do
    if st.build.isSome then Except.ok st else do
      -- VK:368-372: truncate to the header, then zero-fill the two reservations.
      let zeroFilled := st.vk.constants.take headerWords
        ++ List.replicate st.quotientConstWords ("quotient_const", 0)
        ++ List.replicate st.quotientProgramWords ("quotient_program", 0)
      let vkZ0 : Halo2VerifyingKey := { st.vk with constants := zeroFilled }
      -- VK:373-376: the four reservation fields are reset. The label and header
      -- tables are NOT reset, because the Rust does not reset them either.
      let vkZ : Halo2VerifyingKey :=
        { vkZ0 with
          quotientConstOffsetWords := none, quotientConstWords := 0,
          quotientProgramOffsetWords := none, quotientProgramWords := 0 }
      -- VK:378-382
      let (_, meta_, data, _) ← metaDataForStableStaticLayout feat env inputs vkZ
      let candidate ← env.compactQuotientProgramFor meta_ data
      let candidateConstWords := candidate.consts.length
      let candidateProgramWords := PackedProgramCodec.wordLenForBytes candidate.bytes.size
      -- VK:384-392
      if candidateConstWords ≤ st.quotientConstWords &&
          candidateProgramWords ≤ st.quotientProgramWords then
        let settled : VkReservationState :=
          { vk := vkZ, quotientConstWords := st.quotientConstWords,
            quotientProgramWords := st.quotientProgramWords, build := some candidate }
        Except.ok settled
      else
        let grown : VkReservationState :=
          { vk := vkZ,
            quotientConstWords := max st.quotientConstWords candidateConstWords,
            quotientProgramWords := max st.quotientProgramWords candidateProgramWords,
            build := none }
        Except.ok grown)
    init
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
  -- VK:443-448: the two write-back loops. vk.constants[i] = .. is a direct index,
  -- so an out-of-range write is a panic in both profiles (rule R4) even though the
  -- two asserts above make it unreachable.
  let vkFilled ← quotientProgramBuild.consts.zipIdx.foldlM
    (fun vk pair => do
      let (value, i) := pair
      let cs ← listSetMut vk.constants (quotientConstOffsetWords + i)
        ("quotient_const", value) "proofs/solidity-verifier/src/lowering/vk.rs:444"
      Except.ok ({ vk with constants := cs } : Halo2VerifyingKey))
    st.vk
  let vkFilled2 ← quotientProgramChunks.zipIdx.foldlM
    (fun vk pair => do
      let (value, i) := pair
      let cs ← listSetMut vk.constants (quotientProgramOffsetWords + i)
        ("quotient_program", value) "proofs/solidity-verifier/src/lowering/vk.rs:447"
      Except.ok ({ vk with constants := cs } : Halo2VerifyingKey))
    vkFilled
  -- VK:450-455
  let (_, finalMeta, finalData, _) ←
    metaDataForStableStaticLayout feat env inputs vkFilled2
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


end Midfall.Generator

/-! # Known-answer tests

The model these gates run on is Midfall.Instances.ExponentModel (D-P1's runnable
AdmissiblePairing: three copies of the additive group of ZMod p, pairing =
multiplication of exponents). That import is a KAT-only dependency: this file
states no theorems, so nothing proved anywhere can acquire a dependence on the
exponent model, and scripts/checks.sh's axiom probe on the frozen statements is
unaffected. The model's own header (Instances/ExponentModel.lean:52-70) states
what it certifies and what it does not; these gates use it for exponent
arithmetic and for nothing else.

LANDMINE 1 (docs/REVIEW.md R-48): the shared LayoutKats.verifierLayoutFixture has
every PCS base at 0, so any gate that compares points passes vacuously on it.
This package therefore (a) builds memV, overriding the same seven bases Kzg.lean's
memF overrides for the same reason, (b) asserts pairwise distinctness
(fixturePointsDistinct_ok) BEFORE any comparison gate is trusted, and (c) leaves
the shared fixture alone. -/

namespace Midfall.Generator.VkKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances

local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Reading a Fault-channel result as "did it panic at exactly this site". -/
def panickedAtSite {α : Type} (e : Except Fault α) (site : String) : Bool :=
  match e with
  | .error (Fault.panic s) => s == site
  | _ => false

def isFaultV {α : Type} (e : Except Fault α) : Bool :=
  match e with | .error _ => true | .ok _ => false

def isOkV {α : Type} (e : Except Fault α) : Bool :=
  match e with | .error _ => false | .ok _ => true

/-- The same probe on the Except String channel the layout validators use. -/
def isOkS {α : Type} (e : Except String α) : Bool :=
  match e with | .error _ => false | .ok _ => true

def orNat {α : Type} (e : Except Fault α) (d : α) : α :=
  match e with | .ok a => a | .error _ => d

def f17 (x : Fr 17) : Nat := x.val

/-- The Rust's panic-site prefix, spelled once. -/
def vkSite (n : Nat) : String :=
  "proofs/solidity-verifier/src/lowering/vk.rs:" ++ toString n

/-- The 48-byte little-endian Fp::to_repr of a small number, i.e. what
    g1_to_u256s / g2_to_u256s are handed by the reference. -/
def le48 (n : Nat) : List Nat := bytesToNats (natToBytesLE n 48)

/-- The port's stand-in for "the coordinates of this G1 point": exponent n, and a
    second coordinate that differs from the first so a swapped (x, y) or a swapped
    (hi, lo) is visible. Exponent 0 is the identity, the only point with no
    coordinates at all. -/
def g1ReprV : Exp 17 -> G1AffineRepr := fun P =>
  let n := P.toAdd.val
  if n == 0 then { coordinates := none, isIdentity := true }
  else { coordinates := some (le48 n, le48 (n + 1)), isIdentity := false }

/-- The G2 analogue: four distinct components, so the c0/c1 order inside each of
    x and y is observable and not only the x/y order. -/
def g2ReprV : Exp 17 -> G2AffineRepr := fun P =>
  let n := P.toAdd.val
  if n == 0 then
    { coordinates := none, isIdentity := true }
  else
    { coordinates := some ((le48 n, le48 (n + 1)), (le48 (n + 2), le48 (n + 3))),
      isIdentity := false }

def codecsV : VkPointCodecs (Exp 17) (Exp 17) :=
  { g1Repr := g1ReprV, g2Repr := g2ReprV }

/-- A REAL domain, built by the ported EvaluationDomain.new rather than
    hand-faked: fc17 has rootOfUnity = 3 of order 16, k = 2 and a degree-3
    constraint system, so n = 4 and omega is a primitive 4th root of 1 in
    ZMod 17. That it really is primitive is what fixtureDomain_ok checks - the
    hand-check hazard 3's finding says no lemma can replace yet. -/
def domV : EvaluationDomain (Fr 17) :=
  orNat (EvaluationDomain.new (F := Fr 17) fc17 3 2)
    { n := 0, k := 0, extendedK := 0, omega := 0, omegaInv := 0,
      extendedOmega := 0, extendedOmegaInv := 0, gCoset := 0, gCosetInv := 0,
      quotientPolyDegree := 0, ifftDivisor := 0, extendedIfftDivisor := 0,
      tEvaluations := #[], barycentricWeight := 0 }

/-- tau = 3, which is not in the domain: the four domain points are 1, omega,
    omega^2, omega^3 = 1, 13, 16, 4 and none of them is 3 (fixtureDomain_ok
    checks it). Chosen so that tau, minus tau and the four L_i(tau) are all
    distinct from each other AND from the commitment exponents below - which is
    what makes fixturePointsDistinct_ok true rather than a wish. -/
def tauV : Fr 17 := 3

/-- L_i(x) = (x^n - 1) / (n * omega^-i * (x - omega^i)), the closed form of the
    Lagrange basis over a multiplicative subgroup. Scaffolding for the fixture:
    it is how an honest g_lagrange is built, and the fact that it is honest is
    what srsTauCommitment_semantics_ok then checks. -/
def lagrangeAt (omega tau : Fr 17) (n i : Nat) : Fr 17 :=
  let x := omega ^ i
  (tau ^ n - 1) / ((n : Fr 17) * Inv.inv x * (tau - x))

/-- The honest Lagrange-basis SRS: g_lagrange[i] = L_i(tau) * G, over n = 4. -/
def gLagrangeV : List (Exp 17) :=
  (List.range domV.n).map fun i => ex (f17 (lagrangeAt domV.omega tauV domV.n i))

/-- The honest G2 side: s_g2 = tau * G2. -/
def sG2V : Exp 17 := gsmul tauV (expGen (p := 17))

/-- The commitment points, all distinct and none the identity, so a gate that
    compares them can actually fail (landmine 1). -/
def fixedV : Array (Exp 17) := #[ex 2, ex 6]
def permV : Array (Exp 17) := #[ex 7, ex 9, ex 11]

def vkCurveV : VerifyingKey (Fr 17) (Exp 17) :=
  { domain := domV
    fixedCommitments := fixedV
    permutation := { commitments := permV }
    cs := ConstraintSystem.default (F := Fr 17)
    csDegree := 3
    transcriptRepr := 7 }

def paramsV : ParamsKZG (Exp 17) (Exp 17) :=
  { gLagrange := gLagrangeV, g2 := expGen (p := 17), sG2 := sG2V }

def accV : Midfall.Generator.AccumulatorEncoding :=
  { offset := 4, numLimbs := 7, numLimbBits := 56,
    kind := Midfall.Generator.AccumulatorEncodingKind.pointAndScalar }

/-- rust: MOD:37-45 as a value: the six fields, filled. -/
def inputsV : VerifierBuildInputs 17 (Exp 17) (Exp 17) :=
  { params := paramsV,
    vk := vkCurveV,
    numInstances := 3,
    numCommittedInstances := 1,
    accEncoding := some accV,
    meta_ := Midfall.Generator.EncodingKats.metaFixture }

/-- The same inputs with no accumulator: VK:119-131's unwrap_or_default arm. -/
def inputsNoAcc : VerifierBuildInputs 17 (Exp 17) (Exp 17) :=
  { inputsV with accEncoding := none }

/-- The memory layout the stub planner returns. Built from the shared fixture
    with SEVEN bases overridden - the same seven Kzg.lean:1872-1880 overrides, for
    the reason R-48 records: with every PCS base at 0 the commitment pointers
    coincide and a comparison gate cannot fail. -/
def memV : VerifierMemoryLayout :=
  { Midfall.Generator.EncodingKats.memFixture with
    quotientLimbCommsMptrBase := ptrMemory (valueFromNat 0x7000)
    fComMptr := ptrMemory (valueFromNat 0x9000)
    piMptr := ptrMemory (valueFromNat 0x9020)
    pcsQEvalSourceTableMptr := 0x8000
    pcsQComTraceScratchMptr := 0x8100
    pcsFinalMsmScratchMptr := 0x8200
    pcsPairingScratchMptr := 0x9200 }

/-- The stub for the unported VerifierMemoryLayout::new (MEM:591-973). A STUB, and
    it says so: it returns memV regardless, except that it copies the two config
    fields memory_layout_for is supposed to fill into fields the gates can read
    back. That is what makes memoryLayoutFor_config_ok a gate and not a tautology:
    a port that forgot VK:557-559 leaves both at the default zero. -/
def newLayoutV : ConstraintSystemMeta -> Halo2VerifyingKey -> Ptr ->
    VerifierMemoryLayoutConfig -> VerifierMemoryLayout :=
  fun _ _ vkMptr cfg =>
    { memV with
      vkMptr := vkMptr
      transcriptMptr := cfg.transcriptWords
      verifierReturnMptr := cfg.numInstances }

/-- A quotient build with three constants and forty program bytes, i.e. two
    program words, so the two reservation sizes are non-degenerate and distinct. -/
def buildV : VkQuotientBuild :=
  { bytes := ByteArray.mk ((List.range 40).map Nat.toUInt8).toArray
    consts := [101, 202, 303] }

/-- The three quotient.rs stubs (QRS:165-181, QRS:425-430, QRS:2101-2110).
    Deterministic, which is exactly the property VK:456-463 asserts of the real
    ones; the two "changed after materialisation" gates break that on purpose to
    show the asserts can fire. -/
def envV : VkBuildEnv Nat :=
  { newVerifierMemoryLayout := newLayoutV
    compactQuotientProgramFor := fun _ _ => Except.ok buildV
    quotientProgramPlan := fun _ _ => Except.ok 0
    buildQuotientProgramItems := fun _ => Except.ok buildV }

/-- The render-side VK the meta/data path is built against: Encoding.lean's own
    fixture, so Data.new's internal asserts hold exactly as Encoding.lean already
    pins them. -/
def renderVkV : Halo2VerifyingKey := Midfall.Generator.EncodingKats.vkFixture

/-- The empty Data used as a loud fallback by one gate below. -/
def dataEmptyStub : Data := Midfall.Generator.EncodingKats.dataEmpty


/-! ## Fixture sanity -/

/-- THE DOMAIN AND THE SRS ARE HONEST, which is the hand-check hazard 3's finding
    says no lemma can replace yet. Five things: omega has order EXACTLY 4 (so it is
    a primitive 4th root - precisely the hypothesis R-47 says the tree does not
    carry); the four domain points are distinct; tau is off the domain; the
    Lagrange basis sums to 1 (the constant-1 polynomial, which is what VK:141-144
    says the sum of g_lagrange must be); and the basis reproduces X at tau. Rules
    out a fixture whose SRS was not honestly generated, which would make every
    assert gate below vacuous in the wrong direction.
    PERTURBATION RUN: setting tauV to 1 (a domain point) reddens the third and
    fourth conjuncts, because a Lagrange basis evaluated AT a domain point is a
    delta function that still sums to 1 but reproduces 1 and not tau. Replacing
    omega ^ i by omega ^ (i + 1) in lagrangeAt reddens the fifth conjunct and
    srsTauCommitment_semantics_ok. Replacing fc17's rootOfUnity with 2 reddens the
    first conjunct. -/
def fixtureDomain_ok : Bool :=
  f17 domV.omega == 13 && f17 domV.omegaInv == 4 && domV.n == 4 && domV.k == 2
    && f17 (domV.omega ^ 4) == 1 && f17 (domV.omega ^ 1) != 1
    && f17 (domV.omega ^ 2) != 1 && f17 (domV.omega ^ 3) != 1
    && ! [1, 13, 16, 4].contains (f17 tauV)
    && ((List.range 4).map (fun i => f17 (domV.omega ^ i))).eraseDups.length == 4
    && f17 ((List.range 4).foldl
        (fun acc i => acc + lagrangeAt domV.omega tauV 4 i) 0) == 1
    && f17 ((List.range 4).foldl (fun acc i =>
          acc + domV.omega ^ i * lagrangeAt domV.omega tauV 4 i) 0) == f17 tauV

/-- LANDMINE 1'S DISTINCTNESS ASSERTION, made before any comparison gate below is
    trusted. The fixture's group elements - four g_lagrange points, the G1 base,
    s_g2, minus s_g2, and the five commitment points - must be pairwise distinct as
    points, as exponents, and as encoded word quadruples. Without this,
    generateBaseVk_comms_ok and generateBaseVk_g1g2Slots_ok would be comparing a
    value against itself.
    PERTURBATION RUN: setting permV to #[ex 2, ex 3, ex 2] (repeating two fixed
    commitments) reddens this gate and nothing else, which is the point: the
    comparison gates stay green on a degenerate fixture and this one does not. -/
def fixturePointsDistinct_ok : Bool :=
  let pts : List (Exp 17) :=
    gLagrangeV ++ [expGen (p := 17), sG2V, Inv.inv sG2V] ++ fixedV.toList ++ permV.toList
  pts.length == pts.eraseDups.length
    && (pts.map (fun q => q.toAdd.val)).eraseDups.length == pts.length
    && (match (pts.mapM fun q => g1ToU256s (g1ReprV q)) with
        | .ok ws => (ws.map (fun w => w.map (fun x => x.toNat))).eraseDups.length == ws.length
        | .error _ => false)

/-! ## The VK header schema block (LM:396-665) -/

/-- rust: LM:824-831, the reference's OWN test of the slot words and the header
    width, ported: VkDigest 0, G1Base 11, G2Base 15, NegSG2Base 23, header_words
    31, and the field widths summing to the header width. The seven scalar slots
    between them are ones the reference does not pin and this does.
    PERTURBATION RUN: changing VkHeaderSlot.word's omegaInv arm from 5 to 6
    reddens this gate and generateBaseVk_header_ok. -/
def vkHeaderSlot_word_ok : Bool :=
  VkHeaderSlot.word .vkDigest == 0 && VkHeaderSlot.word .numInstances == 1
    && VkHeaderSlot.word .k == 2 && VkHeaderSlot.word .nInv == 3
    && VkHeaderSlot.word .omega == 4 && VkHeaderSlot.word .omegaInv == 5
    && VkHeaderSlot.word .omegaInvToL == 6
    && VkHeaderSlot.word .hasAccumulator == 7
    && VkHeaderSlot.word .accOffset == 8 && VkHeaderSlot.word .numAccLimbs == 9
    && VkHeaderSlot.word .numAccLimbBits == 10
    && VkHeaderSlot.word .g1Base == 11 && VkHeaderSlot.word .g2Base == 15
    && VkHeaderSlot.word .negSG2Base == 23
    && VkHeaderLayout.headerWords == 31
    && (VkHeaderLayout.fields.map (fun f => f.widthWords)).foldl (· + ·) 0 == 31
    && VkHeaderLayout.fields.length == 14

/-- The closed match in VkHeaderLayout.field agrees with the table it replaces, for
    all fourteen slots, on all three fields. This is the gate that keeps the
    "LM:556 is unrepresentable" claim honest: add a slot to the enum and forget the
    table, and the match still compiles - only this says.
    PERTURBATION RUN: renaming the table's "n_inv" to "ninv" reddens this gate
    alone; changing the match's nInv width to 2 reddens this gate and
    vkHeaderSlot_word_ok. -/
def vkHeaderField_agreesWithTable_ok : Bool :=
  let slots : List VkHeaderSlot := [.vkDigest, .numInstances, .k, .nInv, .omega,
    .omegaInv, .omegaInvToL, .hasAccumulator, .accOffset, .numAccLimbs,
    .numAccLimbBits, .g1Base, .g2Base, .negSG2Base]
  slots.length == 14
    && slots.all (fun s =>
      match (VkHeaderLayout.fields.find? (fun f => f.slot == s)) with
      | some f => VkHeaderLayout.field s == f
      | none => false)

/-- A full header build: thirty-one words in the schema's order, each carrying the
    name the caller passed and the value it passed. This is the header half of
    hazard 7 - the ORDER, not the count: a builder that wrote G1_BASE into the
    G2_BASE slot, or emitted the scalars in another order, keeps the count at 31
    and is caught only here.
    PERTURBATION RUN: swapping the two g2 calls' slots reddens this gate and
    generateBaseVk_g1g2Slots_ok; writing numAccLimbBits twice reddens it with the
    overlap error. -/
def vkHeaderBuilder_fullOk_ok : Bool :=
  let v (n : Nat) : Word256 := BitVec.ofNat 256 n
  let bs : List (VkHeaderSlot × String) := [(.vkDigest, "vk_digest"),
    (.numInstances, "num_instances"), (.k, "k"), (.nInv, "n_inv"), (.omega, "omega"),
    (.omegaInv, "omega_inv"), (.omegaInvToL, "omega_inv_to_l"),
    (.hasAccumulator, "has_accumulator"), (.accOffset, "acc_offset"),
    (.numAccLimbs, "num_acc_limbs"), (.numAccLimbBits, "num_acc_limb_bits")]
  match bs.foldlM (fun (h : VkHeaderBuilder) (s, n) => h.scalar s n (v 7))
      VkHeaderLayout.builder with
  | .error _ => false
  | .ok h1 =>
    match h1.g1 .g1Base ["g1_x_hi", "g1_x_lo", "g1_y_hi", "g1_y_lo"]
        ((List.range 4).map (fun i => v (100 + i))) with
    | .error _ => false
    | .ok h2 =>
      match h2.g2 .g2Base ((List.range 8).map (fun i => "g2_" ++ toString i))
          ((List.range 8).map (fun i => v (200 + i))) with
      | .error _ => false
      | .ok h3 =>
        match h3.g2 .negSG2Base ((List.range 8).map (fun i => "neg_" ++ toString i))
            ((List.range 8).map (fun i => v (300 + i))) with
        | .error _ => false
        | .ok h4 =>
          match h4.finish with
          | .error _ => false
          | .ok cs =>
            cs.length == 31
              && cs.getD 0 ("", 0) == ("vk_digest", v 7)
              && cs.getD 6 ("", 0) == ("omega_inv_to_l", v 7)
              && cs.getD 10 ("", 0) == ("num_acc_limb_bits", v 7)
              && cs.getD 11 ("", 0) == ("g1_x_hi", v 100)
              && cs.getD 14 ("", 0) == ("g1_y_lo", v 103)
              && cs.getD 15 ("", 0) == ("g2_0", v 200)
              && cs.getD 22 ("", 0) == ("g2_7", v 207)
              && cs.getD 23 ("", 0) == ("neg_0", v 300)
              && cs.getD 30 ("", 0) == ("neg_7", v 307)

/-- rust: LM:837-846, the reference's own duplicate-slot test, ported: writing
    VkDigest twice fails with the OVERLAP message naming the word index.
    PERTURBATION RUN: making insert overwrite instead of rejecting reddens this
    gate and leaves vkHeaderBuilder_fullOk_ok green, which is the pair that shows
    the check is load-bearing. -/
def vkHeaderBuilder_duplicateErr_ok : Bool :=
  match (VkHeaderLayout.builder).scalar .vkDigest "vk_digest" 1
      >>= (fun b => b.scalar .vkDigest "vk_digest" 2) with
  | .error m => m == "VK header field vk_digest overlaps already-written word 0"
  | .ok _ => false

/-- rust: LM:848-851 (the too-wide insert) plus LM:594's word-count arm, both
    ported and both pinned: the descriptor/caller width mismatch and the
    values-length mismatch are DIFFERENT messages, so a port that collapses them
    passes a count-only check and fails this one. -/
def vkHeaderBuilder_widthErr_ok : Bool :=
  let b := VkHeaderLayout.builder
  (match b.insert .g1Base 8 [] with
    | .error m => m == "VK header field G1_BASE width mismatch: descriptor=4 caller=8"
    | .ok _ => false)
    && (match b.g1 .g1Base ["a", "b"] [1, 2] with
        | .error m => m == "VK header field G1_BASE expected 4 word(s), got 2"
        | .ok _ => false)

/-- LM:603-609's overflow arm. Unreachable through the typed slots - every slot
    fits a 31-word header - so it is exercised by calling insert directly on a
    truncated builder. The range in the message is start..end in DECIMAL, matching
    LM:605's format string, which is itself worth a note: every other address in
    these messages is hex (Layout.lean's hashHex), and this one is not.
    PERTURBATION RUN: rendering the range with hashHex reddens this gate. -/
def vkHeaderBuilder_overflowErr_ok : Bool :=
  let b : VkHeaderBuilder := { words := List.replicate 12 none }
  match b.insert .g2Base 8 ((List.range 8).map (fun i => ("w" ++ toString i, 0))) with
  | .error m => m == "VK header field G2_BASE overflows header: range 15..23, header=12"
  | .ok _ => false

/-- LM:656-664's finish error: the empty builder reports word 0, and a builder whose
    only unset word is number 3 reports 3. The second arm is the one that pins the
    short-circuit - a port that collected every missing word and reported the last
    would say 3 as well, so what it really pins is that the fold reports the FIRST
    missing word and stops; the word-index-versus-unwritten-index distinction is not
    observable at all (see the note at VkHeaderBuilder.finish and perturbation P14). -/
def vkHeaderBuilder_finishMissingErr_ok : Bool :=
  (match (VkHeaderLayout.builder).finish with
    | .error m => m == "VK header word 0 was not written"
    | .ok _ => false)
    && (match ({ words := [some ("a", 1), some ("b", 2), some ("c", 3), none] }
        : VkHeaderBuilder).finish with
        | .error m => m == "VK header word 3 was not written"
        | .ok _ => false)

/-! ## The tau binding (VK:29-62) -/

/-- HAZARD 2. The mutating accumulator's output, pinned four ways: the first eight
    entries against hand-computed powers, the two degenerate lengths, and the
    equivalence with omega ^ i that the port deliberately does NOT rely on.
    PERTURBATION RUN: yielding the accumulator AFTER the multiply (moving VK:56's
    current below VK:57) reddens the first conjunct and
    srsTauCommitment_semantics_ok. Replacing the fold with omega ^ i leaves this
    gate green - which is exactly what the fifth conjunct is for: it makes the
    substitution safe rather than lucky. -/
def omegaPowers_accumulatorEquivalence_ok : Bool :=
  let w := domV.omega
  let ps := omegaPowers w 8
  (ps.map f17 == [1, 13, 16, 4, 1, 13, 16, 4])
    && omegaPowers w 0 == []
    && (omegaPowers w 1).map f17 == [1]
    && ps.length == 8
    && ps.zipIdx.all (fun (x, i) => f17 x == f17 (w ^ i))
    && (omegaPowers 3 5).map f17 == [1, 3, 9, 10, 13]

/-- HAZARD 1'S GATE. The semantics of the multi_exp, at the sizes the port is
    allowed to run (4 and 8, never 2^20). Four conjuncts: (a) on the honest
    fixture the result is tau * G, which is the whole point of the function and
    the content of the Phase 4a lemma, checked here on one concrete domain rather
    than proved; (b) it equals a hand-written fold of omega^i * g_i computed
    WITHOUT omegaPowers, so the two cannot share a bug; (c) the empty SRS gives the
    identity; (d) doubling the basis doubles the commitment, the first thing a
    bucket-decomposition shortcut would get wrong.
    PERTURBATION RUN: P01 (yield the accumulator after the multiply, i.e. start
    the list at omega instead of 1) reddens this gate plus sixteen others. P33
    (same shift written the other way) does too. Replacing omega^i with omega^(i+1)
    reddens (a). Dropping the fold and returning the last term reddens (a), (b), (d).
    ONE CLAIM IN AN EARLIER DRAFT OF THIS COMMENT WAS FALSE AND IS CORRECTED HERE:
    it said that swapping the zip so the SCALARS become the BASES - reading
    multi_exp's argument order backwards - would redden (a) and (b). It does not,
    because it CANNOT be written: gsmul takes a scalar and a point, so the two lists
    are different types and no transposition of the zip is well-typed. The argument
    order of VK:61 is therefore carried by the Lean types and not by this gate, and
    a perturbation attempt that only renames the pair pattern (g, s) / (s, g) is a
    no-op - which is what actually happened when it was run (P02, nothing reddened). -/
def srsTauCommitment_semantics_ok : Bool :=
  let w := domV.omega
  let tauG1 := srsTauCommitment gLagrangeV w
  expOf tauG1 == f17 tauV
    && expOf ((List.range 4).foldl
        (fun acc i => acc * gsmul (w ^ i) (gLagrangeV.getD i 1)) 1) == expOf tauG1
    && expOf (srsTauCommitment [] w) == 0
    && expOf (srsTauCommitment (gLagrangeV ++ gLagrangeV) w) == f17 (tauV * 2)

/-- HAZARD 3'S GATE, and the stand-in for the lemma that cannot be stated yet.
    True on the honest fixture; FALSE when s_g2 is the commitment of a different
    tau, which is exactly the substituted-SRS case VK:195-198 says the assert
    exists to catch; FALSE when the basis is tampered with. The false arms are what
    make this gate non-vacuous: a srsTauIsConsistent that returned true
    unconditionally would pass a one-conjunct version of this gate.
    PERTURBATION RUN: returning true unconditionally reddens the second and third
    conjuncts. Swapping the pairing's two arguments so the check becomes
    e(tau*G1, s_g2) = e(G1, G2) reddens the first conjunct, because that equation
    says tau = 1. -/
def srsTauIsConsistent_honestSrs_ok : Bool :=
  srsTauIsConsistent gLagrangeV domV.omega sG2V
    && ! srsTauIsConsistent gLagrangeV domV.omega (ex 6)
    && ! srsTauIsConsistent (gLagrangeV ++ [ex 1]) domV.omega sG2V

/-! ## The SRS fingerprint (VK:73-92) -/

/-- HAZARD 4: the EXACT preimage bytes, not just the digest, because the digest
    feeds BUILD_ID and a deployed artifact carries it. The layout is
    30 + 8 + 256 + 256 + 128 = 678 bytes: the ASCII tag, then n as EIGHT
    big-endian bytes, then the eight G2 words of g2, then the eight G2 words of
    s_g2, then the four G1 words of [tau]G1, every word 32 big-endian bytes. Every
    segment is pinned at its own offset, so a stride change, a dropped segment, or
    a swapped pair of segments all show up.
    PERTURBATION RUN: writing n as 32 bytes (the natural mistake, since every other
    segment is 32) reddens the length conjunct and the n conjunct; dropping the g2
    segment reddens the length and the offset-38 conjunct; hashing the words
    little-endian reddens the word conjuncts; hashing the preimage twice reddens the
    last conjunct. -/
def srsFingerprint_preimage_ok : Bool :=
  match srsFingerprintPreimage codecsV inputsV
      (srsTauCommitment gLagrangeV domV.omega) with
  | .error _ => false
  | .ok pre =>
    let bs := bytesToNats pre
    let byteAt (k : Nat) : Nat := bs.getD k 255
    -- The value of word j of the segment starting at byte off. Every word here is
    -- a small number, so it lives in the segment's last byte; padsOk is what stops a
    -- wrong-endian or wrong-stride encoding from passing on the value byte alone.
    let wordVals (off nwords : Nat) : List Nat :=
      (List.range nwords).map (fun j => byteAt (off + j * 32 + 31))
    let padsOk (off nwords : Nat) : Bool :=
      ((List.range (nwords * 32)).all (fun i => i % 32 == 31 || byteAt (off + i) == 0))
    bs.length == 678
      && bs.take 30 == ("halo2-solidity-verifier-srs-v1".toList.map (fun c => c.toNat))
      && (bs.drop 30).take 8 == [0, 0, 0, 0, 0, 0, 0, 4]
      && wordVals 38 8 == [0, 1, 0, 2, 0, 3, 0, 4] && padsOk 38 8
      && wordVals 294 8 == [0, 3, 0, 4, 0, 5, 0, 6] && padsOk 294 8
      && wordVals 550 4 == [0, 3, 0, 4] && padsOk 550 4
      && (match srsFingerprint codecsV inputsV with
          | .error _ => false
          | .ok h => h == keccak256 pre)
      && (match srsFingerprint codecsV inputsV with
          | .error _ => false
          | .ok h => h != keccak256 (bytesFromNats (bs ++ [0])))

/-- HAZARD 4's cross-check of the field ORDER the doc comment names (n, G2 base,
    s_g2, [tau]G1). Two things a count check cannot see: that changing tau moves
    the s_g2 segment and nothing before it, and that the digests differ, so a
    substituted SRS would carry a different BUILD_ID.
    The 32-byte slice is NOT enough to see the change - the first word of a G2
    encoding is x.c0_hi, which is zero for every small exponent - so the second
    conjunct compares the whole 256-byte segment. That was found by running it, not
    by reasoning: the first version of this gate compared 32 bytes and passed
    without noticing.
    PERTURBATION RUN: emitting [tau]G1 before s_g2 reddens the first conjunct (the
    bytes at offset 294 would then be the G1 quadruple and everything after
    shifts). Swapping the g2 and s_g2 segments reddens the first conjunct too,
    because g2 is exponent 1 and s_g2 is exponent 3. -/
def srsFingerprint_fieldOrder_ok : Bool :=
  let honest := match srsFingerprintPreimage codecsV inputsV
      (srsTauCommitment gLagrangeV domV.omega) with
    | .ok b => b
    | .error _ => Bytes.empty
  let paramsOther : ParamsKZG (Exp 17) (Exp 17) := { paramsV with sG2 := ex 6 }
  let other : VerifierBuildInputs 17 (Exp 17) (Exp 17) :=
    { inputsV with params := paramsOther }
  match srsFingerprintPreimage codecsV other (srsTauCommitment gLagrangeV domV.omega) with
  | .error _ => false
  | .ok changed =>
    ((bytesToNats honest).take 294) == ((bytesToNats changed).take 294)
      && ((bytesToNats honest).drop 294).take 256
          != ((bytesToNats changed).drop 294).take 256
      && (match srsFingerprint codecsV inputsV, srsFingerprint codecsV other with
          | .ok h1, .ok h2 => h1 != h2
          | _, _ => false)


/-! ## generate_base_vk (VK:94-299) -/

/-- The header half of hazard 7: the thirty-one constants the reference emits,
    pinned by NAME and by VALUE at every slot, in order. The values are the
    fixture's own: transcript_repr 7, num_instances 3, k 2, n_inv = 4^-1 = 13,
    omega 13, omega_inv 4, omega_inv^|rotation_last| = 4^10 = 16 (omega_inv has
    order 4, so the tenth power is the second), and the accumulator quadruple
    1 / 4 / 7 / 56. Then the three point fields.
    PERTURBATION RUN: putting omega_inv (4) where n_inv belongs reddens this gate.
    So does reading num_main_evals where the reference reads num_instances, and so
    does dropping the Int.natAbs at VK:116 (l := 0 instead of 10).
    ONE PERTURBATION THAT DID NOT REDDEN, stated because the fixture is the reason:
    putting OMEGA where n_inv belongs reddens nothing, because at k = 2 over Fr 17
    n_inv = (2^2)^-1 = 4^-1 = 13 and omega = 13 are the same number. That is a
    property of the chosen domain, not of the port - and it is the R-30 shape (a
    fixture that collapses two distinct slots onto one value), so this gate cannot
    distinguish those two slots and no claim is made that it does. -/
def generateBaseVk_header_ok : Bool :=
  match generateBaseVk codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    let cs := vk.constants
    cs.length == 31
      && cs.map (fun c => c.1) == ["vk_digest", "num_instances", "k", "n_inv",
          "omega", "omega_inv", "omega_inv_to_l", "has_accumulator", "acc_offset",
          "num_acc_limbs", "num_acc_limb_bits", "g1_x_hi", "g1_x_lo", "g1_y_hi",
          "g1_y_lo", "g2_x_c0_hi", "g2_x_c0_lo", "g2_x_c1_hi", "g2_x_c1_lo",
          "g2_y_c0_hi", "g2_y_c0_lo", "g2_y_c1_hi", "g2_y_c1_lo",
          "neg_s_g2_x_c0_hi", "neg_s_g2_x_c0_lo", "neg_s_g2_x_c1_hi",
          "neg_s_g2_x_c1_lo", "neg_s_g2_y_c0_hi", "neg_s_g2_y_c0_lo",
          "neg_s_g2_y_c1_hi", "neg_s_g2_y_c1_lo"]
      && cs.map (fun c => c.2.toNat) ==
          [7, 3, 2, 13, 13, 4, 16, 1, 4, 7, 56,
           0, 1, 0, 2,
           0, 1, 0, 2, 0, 3, 0, 4,
           0, 14, 0, 15, 0, 16, 0, 17]

/-- The three point slots at their BYTE offsets, which is what hazard 7 asks for
    beyond a count: G1_BASE at word 11 = byte 352, G2_BASE at word 15 = byte 480,
    NEG_S_G2_BASE at word 23 = byte 736. The negation is checked to be a REAL
    negation - s_g2 is exponent 3, minus s_g2 is exponent 14, and the eight words
    differ in the four places a missing minus sign would leave equal.
    PERTURBATION RUN: dropping the inverse at VK:159 reddens the last conjunct and
    nothing else in the file, because every other use of s_g2 goes through the
    un-negated value. Writing the G2 words in (c1, c0) order reddens the
    byte-offset conjuncts. -/
def generateBaseVk_g1g2Slots_ok : Bool :=
  match generateBaseVk codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    let payload := vk.bytes
    let wordAt (byteOff : Nat) : Nat :=
      bytesToNatBE ((bytesTake payload byteOff 32).getD Bytes.empty)
    wordAt 352 == 0 && wordAt 384 == 1 && wordAt 416 == 0 && wordAt 448 == 2
      && wordAt 480 == 0 && wordAt 512 == 1 && wordAt 736 == 0 && wordAt 768 == 14
      && (vk.constants.map (fun c => c.2.toNat)).getD 23 999 == 0
      && (vk.constants.map (fun c => c.2.toNat)).getD 24 999 == 14
      && expOf sG2V == 3 && expOf (Inv.inv sG2V) == 14

/-- The three SRS asserts, each at its own site, each broken independently. This is
    the gate that says the controls the audit calls H-1 actually fire: a bad
    g_lagrange sum (VK:151), a non-canonical G2 base (VK:180), and an s_g2 that does
    not correspond to the tau behind g_lagrange (VK:189).
    PERTURBATION RUN: this gate is the evidence for the three sites. Deleting any
    one unless from generateBaseVk reddens exactly the conjunct that expects that
    panic and leaves the other two green, which is what makes the three sites
    separately observable rather than one lump. -/
def generateBaseVk_srsAsserts_ok : Bool :=
  panickedAtSite (generateBaseVk codecsV
    { inputsV with params := { paramsV with gLagrange := gLagrangeV.drop 1 } })
      (vkSite 151)
    && panickedAtSite (generateBaseVk codecsV
      { inputsV with params := { paramsV with g2 := ex 2 } }) (vkSite 180)
    && panickedAtSite (generateBaseVk codecsV
      { inputsV with params := { paramsV with sG2 := ex 6 } }) (vkSite 189)
    && isOkV (generateBaseVk codecsV inputsV)

/-- The commitment vectors: two fixed and three permutation commitments, each four
    words, each from a DISTINCT point (landmine 1), in source order, and the
    constructor reservation sized from them: 31*32 + 5*128 bytes plus the 1-byte
    runtime prefix. Also pins that the base VK carries NO quotient section, which is
    what makes payload_layout's constants-minus-quotient-words arithmetic yield the
    header width and not something else.
    PERTURBATION RUN: emitting the permutation commitments from the fixed vector
    (the classic copy-paste) reddens the word comparison; using g1Bytes where the
    reference uses WORD_BYTES at VK:281 reddens the length conjunct. -/
def generateBaseVk_comms_ok : Bool :=
  match generateBaseVk codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    vk.fixedComms.length == 2 && vk.permutationComms.length == 3
      && vk.fixedComms.map (fun w => [w.xHi.toNat, w.xLo.toNat, w.yHi.toNat, w.yLo.toNat])
          == [[0, 2, 0, 3], [0, 6, 0, 7]]
      && vk.permutationComms.map (fun w => [w.xHi.toNat, w.xLo.toNat, w.yHi.toNat, w.yLo.toNat])
          == [[0, 7, 0, 8], [0, 9, 0, 10], [0, 11, 0, 12]]
      && vk.len == 31 * 32 + 5 * 128
      && vk.constructorPayloadMptr == vkConstructorPayloadStart
      && vk.quotientConstOffsetWords == none && vk.quotientConstWords == 0
      && vk.quotientProgramOffsetWords == none && vk.quotientProgramWords == 0
      && vk.quotientConstLabels == [] && vk.quotientConstHeaders == []
      && (VkConstructorMemoryLayout.new (vk.len + vkRuntimePrefixLen)).validate == .ok ()

/-- VK:119-131, both arms of the accumulator option: is_some() as usize for the
    flag and unwrap_or_default() for the three values. The no-accumulator arm is the
    one a port that defaults to 1/1/1 gets wrong, and it is also the arm the deployed
    Moonlight build does not take, so both are pinned.
    PERTURBATION RUN: reading offset into num_acc_limbs reddens the second
    conjunct; using 1 for has_accumulator when absent reddens the first. -/
def generateBaseVk_accEncoding_ok : Bool :=
  match generateBaseVk codecsV inputsNoAcc, generateBaseVk codecsV inputsV with
  | .ok vk0, .ok vk1 =>
    let w0 := vk0.constants.map (fun c => c.2.toNat)
    let w1 := vk1.constants.map (fun c => c.2.toNat)
    [w0.getD 7 999, w0.getD 8 999, w0.getD 9 999, w0.getD 10 999] == [0, 0, 0, 0]
      && [w1.getD 7 999, w1.getD 8 999, w1.getD 9 999, w1.getD 10 999] == [1, 4, 7, 56]
  | _, _ => false

/-- VK:115-118: omega_inv_to_l is omega_inv raised to the ABSOLUTE value of
    rotation_last, which for the fixture meta is -10, so 4^10 mod 17 = 16. The
    signedness is the point: a port that used the signed rotation, or that forgot
    the abs, gets a different word, and the difference is invisible to any length or
    count check.
    PERTURBATION RUN: using the signed exponent reddens this gate (powVartime on a
    negative is not what the reference computes). So does using omega instead of
    omega_inv: 13^10 = 1, not 16. -/
def generateBaseVk_omegaInvToL_ok : Bool :=
  inputsV.meta_.rotationLast == -10
    && f17 (powVartime domV.omegaInv 10) == 16
    && f17 (powVartime domV.omegaInv 0) == 1
    && f17 (powVartime domV.omegaInv 1) == 4
    && match generateBaseVk codecsV inputsV with
       | .ok vk => (vk.constants.getD 6 ("", 0)).2.toNat == 16
       | .error _ => false

/-! ## generate_vk_direct (VK:301-357) -/

/-- The direct lowering: the constant table grows by the table words, the
    quotient-program section is reserved at ZERO words but still gets an offset, the
    labels are one per word, and the headers are keyed by the index in the WHOLE
    table after enumerate-then-filter. Also the assert at VK:343 that the typed
    layout preserves the emitted byte length.
    PERTURBATION RUN: filtering before enumerating, so the header indices count only
    the headed words, reddens the headers conjunct; setting quotient_program_words
    to 1 instead of 0 reddens the length conjunct. -/
def generateVkDirect_table_ok : Bool :=
  let words : List VkTableWord :=
    [ { value := 11, label := "run_a[0]", headers := ["hdr 1", "hdr 2"] },
      { value := 12, label := "run_a[1]", headers := [] },
      { value := 13, label := "pool[0]", headers := ["hdr 3"] } ]
  match generateVkDirect codecsV inputsV words with
  | .error _ => false
  | .ok vk =>
    vk.constants.length == 34
      && vk.constants.getD 31 ("", 0) == ("quotient_const", 11)
      && vk.constants.getD 33 ("", 0) == ("quotient_const", 13)
      && vk.quotientConstWords == 3
      && vk.quotientProgramWords == 0
      && vk.quotientConstOffsetWords == some 31
      && vk.quotientProgramOffsetWords == some 34
      && vk.quotientConstLabels == ["run_a[0]", "run_a[1]", "pool[0]"]
      && vk.quotientConstHeaders == [(0, ["hdr 1", "hdr 2"]), (2, ["hdr 3"])]
      && vk.len == 34 * 32 + 5 * 128
      && isOkS (vk.validatePayloadLayout)

/-- The empty-table arm: a direct program with no words still gets both offsets,
    the two quotient sections collapse onto the cursor, and the byte length is still
    preserved. A port that skipped the layout call when the table was empty would
    leave none in the offset fields and fail here. -/
def generateVkDirect_empty_ok : Bool :=
  match generateVkDirect codecsV inputsV [] with
  | .error _ => false
  | .ok vk =>
    vk.constants.length == 31 && vk.quotientConstWords == 0
      && vk.quotientConstOffsetWords == some 31
      && vk.quotientProgramOffsetWords == some 31
      && vk.quotientConstLabels == [] && vk.quotientConstHeaders == []
      && isOkS (vk.validatePayloadLayout)

/-- The word_headers / word_comment round trip through Models.lean: the direct
    table's headers must be readable back at the word index the layout says, which
    is the only place the offset fields do observable work outside this file. -/
def generateVkDirect_wordHeaders_ok : Bool :=
  let words : List VkTableWord :=
    [ { value := 11, label := "run_a[0]", headers := ["h1"] },
      { value := 12, label := "run_a[1]", headers := [] },
      { value := 13, label := "pool[0]", headers := ["h3"] } ]
  match generateVkDirect codecsV inputsV words with
  | .error _ => false
  | .ok vk =>
    vk.wordHeaders 31 == ["h1"] && vk.wordHeaders 32 == []
      && vk.wordHeaders 33 == ["h3"] && vk.wordHeaders 0 == []
      && vk.wordComment 32 == "run_a[1]" && vk.wordComment 0 == "vk_digest"

/-! ## generate_vk (VK:353-472) and the payload section ORDER -/

/-- THE ACCEPTANCE GATE hazard 7 asks for: the ORDER of the VK payload sections
    against VkPayloadLayout, pinned at the BYTE level and not by counts. A count
    check cannot see a swap of the quotient-constant and quotient-program sections;
    this can, because the two sections carry different labels and different values
    and because the byte offsets are named.
    PERTURBATION RUN: swapping the two reserve calls in VkPayloadLayout.forVk
    reddens this gate and generateVk_converges_ok; writing the program chunks at
    the const offset (a one-token swap at VK:444) reddens the label conjunct. -/
def payloadOrder_sectionsTiled_ok : Bool :=
  match generateVk Features.solidity envV codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    match vk.payloadLayout with
    | .error _ => false
    | .ok layout =>
      let kinds := layout.sections.map (fun s => payloadSectionKindDebug s.kind)
      let wordOffsets := layout.sections.map (fun s => s.wordOffset)
      let byteOffsets := layout.sections.map (fun s => s.byteOffset)
      kinds == ["Header", "QuotientConstants", "QuotientProgram",
        "FixedCommitments", "PermutationCommitments"]
        && wordOffsets == [0, 31, 34, 36, 44]
        && byteOffsets == [0, 992, 1088, 1152, 1408]
        && layout.totalBytes == vk.len
        && ((vk.constants.drop 31).take 3).all (fun c => c.1 == "quotient_const")
        && ((vk.constants.drop 34).take 2).all (fun c => c.1 == "quotient_program")
        && vk.quotientConstOffsetWords == some 31
        && vk.quotientProgramOffsetWords == some 34

/-- The converged build field by field: three const words (101, 202, 303) written
    OVER the zero fill at the const offset, two program words at the program
    offset, and the four reservation fields set at the end and not before. The zero
    fill is what makes the write-back observable: a port that appended instead of
    overwriting would produce a table that is too long and trip the layout assert.
    PERTURBATION RUN: appending the consts instead of writing them in place reddens
    this gate and payloadOrder_sectionsTiled_ok; never writing back (leaving the
    zeros) reddens the three value conjuncts. -/
def generateVk_converges_ok : Bool :=
  match generateVk Features.solidity envV codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    vk.constants.length == 36
      && vk.constants.getD 31 ("", 0) == ("quotient_const", 101)
      && vk.constants.getD 32 ("", 0) == ("quotient_const", 202)
      && vk.constants.getD 33 ("", 0) == ("quotient_const", 303)
      && vk.quotientConstWords == 3
      && vk.quotientProgramWords == 2
      && vk.len == 36 * 32 + 5 * 128
      && isOkS (vk.validatePayloadLayout)
      && ((vk.constants.drop 34).take 2).map (fun c => c.2.toNat) != [0, 0]

/-- THE REACHABLE PANICS of generate_vk, each at its own site: the reservation never
    converging (VK:396), the bytecode changing after materialisation (VK:457), and
    the constants changing after materialisation (VK:461).
    The VK:396 arm needs a candidate that GROWS on every iteration - a constant
    over-large candidate does NOT do it, because the loop converges as soon as the
    reservation reaches it, which is the first thing this gate got wrong and is why
    the stub below reads the address the reservation moved. That is exactly the
    feedback VK:355-357 describes: the program depends on memory addresses and the
    addresses depend on the VK length.
    PERTURBATION RUN: this gate is the evidence. Deleting the VK:457 unless reddens
    only its conjunct; deleting the VK:396 arm turns the panic into a wrong answer
    and reddens the third conjunct. -/
def generateVk_panics_ok : Bool :=
  let envBytes : VkBuildEnv Nat :=
    { envV with buildQuotientProgramItems := fun _ =>
        Except.ok { buildV with bytes := ByteArray.mk ((List.replicate 40 17).map Nat.toUInt8).toArray } }
  let envConsts : VkBuildEnv Nat :=
    { envV with buildQuotientProgramItems := fun _ =>
        Except.ok { buildV with consts := [9, 9, 9] } }
  let growEnv : VkBuildEnv Nat :=
    { envV with compactQuotientProgramFor := fun _ data => do
        -- the first fixed commitment's address, which Data.new derives as
        -- VK_MPTR + constants.len() words (ENC:309), so it grows with the
        -- reservation: exactly the feedback VK:355-357 describes.
        let basePtr := (data.fixedComms.head?).map (fun c => c.base.value)
        let base ← Value.asUsize (basePtr.getD valueDefault)
        Except.ok { buildV with consts := List.replicate (base / 32 + 1) 5 } }
  let envBig : VkBuildEnv Nat :=
    { envV with
      compactQuotientProgramFor := fun _ _ => Except.ok { buildV with consts := List.replicate 40 5 },
      buildQuotientProgramItems := fun _ => Except.ok { buildV with consts := List.replicate 40 5 } }
  panickedAtSite (generateVk Features.solidity envBytes codecsV inputsV) (vkSite 457)
    && panickedAtSite (generateVk Features.solidity envConsts codecsV inputsV) (vkSite 461)
    && panickedAtSite (generateVk Features.solidity growEnv codecsV inputsV) (vkSite 396)
    && isOkV (generateVk Features.solidity envV codecsV inputsV)
    -- CONTROL: a constant over-large candidate CONVERGES rather than failing to,
    -- because the loop breaks as soon as the reservation reaches the candidate.
    -- That is the conjunct that says the third one is about growth and not about
    -- size - and it is a conjunct this gate got wrong the first time, when only the
    -- compact stub was enlarged and the items stub was not, so the panic that came
    -- out was VK:461 and the control was silently testing something else.
    && isOkV (generateVk Features.solidity envBig codecsV inputsV)

/-- HAZARD 5, ANSWERED HONESTLY: the assert at VK:434-437 ("quotient const table
    exceeded VK payload reservation") and its sibling at VK:438-441 RESTATE the
    loop's own break condition at VK:384-386 over the same value, so no input can
    fire them. The perturbation the plan asked for was attempted and it FAILED to
    redden the site: a stub whose surviving build is larger than the reservation it
    converged on cannot be constructed, because convergence is defined as "not
    larger". What fires instead is VK:461, which is the first conjunct here and the
    second half of the evidence. The same holds of the two section-length asserts
    (VK:414, VK:420) and the byte-length assert (VK:426): each compares
    VkPayloadLayout::for_vk's own output against the quantity it was built from. All
    five are ported anyway, per R1 and R4, and they are regression guards on the
    LAYOUT code rather than on the input - which is what the report says.
    PERTURBATION RUN: the env below makes the compact build smaller than the items
    build, the closest reachable thing to an over-long const table; the panic that
    comes out is VK:461 and NOT VK:436, and this gate asserts exactly that. -/
def generateVk_hazard5_ok : Bool :=
  let envSmaller : VkBuildEnv Nat :=
    { envV with compactQuotientProgramFor := fun _ _ =>
        Except.ok { buildV with consts := [1, 2] } }
  let r := generateVk Features.solidity envSmaller codecsV inputsV
  panickedAtSite r (vkSite 461) && ! panickedAtSite r (vkSite 436)
    && ! panickedAtSite r (vkSite 438)


/-! ## The transcript and memory cluster (VK:549-653) -/

/-- VK:610-653. The three arguments the reference passes to from_protocol are pinned
    individually - proof_cptr 0, meta.num_evals (NOT num_main_evals) and
    meta.num_point_sets - because the second is the one a port reaches for by habit,
    and with the feature off the two are equal, so the mistake is invisible to the
    deployed fixture. The gate therefore also runs a meta whose dummy evals are
    non-zero, where the two differ.
    PERTURBATION RUN: passing num_main_evals reddens the second conjunct on the
    with-dummies meta; passing numDummyEvals where numPointSets belongs reddens the
    first conjunct (the recomputation on the right-hand side uses numEvals);
    passing numInstances as the proof_cptr reddens the first conjunct too. -/
def transcriptBufferLayoutForMeta_ok : Bool :=
  let m := inputsV.meta_
  let withDummies := m.setNumDummyEvals 4
  match transcriptBufferLayoutForMeta m 3 with
  | .error _ => false
  | .ok t =>
    t.words == orNat (do
        let p ← ProofCalldataLayout.fromProtocol m.protocol 0 m.numEvals m.numPointSets
        Except.ok (TranscriptBufferLayout.fromProofLayout p 3
          m.protocol.numUserChallenges).words) 999
      && (match transcriptBufferLayoutForMeta withDummies 3 with
          | .error _ => false
          | .ok t2 => t2.words != t.words)
      -- numInstances 0 gives the SAME bound: for this meta the dominating run is
      -- the eval block (VK:626-627's arm (b)), not the initial absorb, so the
      -- instance count cannot move the max. A thousand instances does move it, and
      -- that is the discriminating arm rather than a silent 0-vs-3.
      && (match transcriptBufferLayoutForMeta m 0 with
          | .error _ => false
          | .ok t3 => t3.words == t.words)
      && (match transcriptBufferLayoutForMeta m 1000 with
          | .error _ => false
          | .ok t4 => t4.words > t.words)

/-- VK:601-608, the #[cfg(test)] helper: the same number as the function it exposes,
    by construction, and pinning that keeps the helper from drifting. -/
def transcriptBufferWordsBound_ok : Bool :=
  match transcriptBufferLayoutForMeta inputsV.meta_ 3,
      transcriptBufferWordsBound inputsV.meta_ 3 with
  | .ok t, .ok w => t.words == w
  | _, _ => false

/-- VK:562-599. All six candidate ends computed independently and the max taken over
    them, plus the two conjuncts that make the max meaningful: the result is at
    least each candidate, and it changes when the dominating candidate changes. The
    dominating term for this fixture is the transcript end, which is the one that
    grows with the proof shape - the reason VK:578-583's comment says the buffer
    must stay below VK_MPTR at all.
    PERTURBATION RUN: dropping the quotient-return candidate from the list reddens
    the equality conjunct only when the quotient term dominates, so the gate also
    runs a meta with 400 simple selectors, where it does dominate and the omission
    shows. Dropping the pairing-batch end reddens nothing on this fixture, and that
    is stated rather than hidden: it is dominated by the transcript end, which is
    why the reference lists it "explicitly so the bound survives if that derivation
    changes" (VK:586-588). -/
def staticWorkingMemorySizeForMeta_ok : Bool :=
  let m := inputsV.meta_
  match staticWorkingMemorySizeForMeta inputsV m with
  | .error _ => false
  | .ok v =>
    let tw := (orNat (transcriptBufferLayoutForMeta m inputsV.numInstances)
      transcriptBufferLayoutDefault).words
    let candidates : List Nat :=
      [ transcriptBufferStart + tw * wordBytes,
        pcsPairingScratchStart + staticWorkingMemorySize * wordBytes,
        accumulatorPairingBatchPtr + accumulatorPairingBatchHashBytes,
        finalPairingScratchStart + pairingStaticWorkingWords * wordBytes,
        verifierReturnBufferStart + wordBytes,
        quotientReturnBufferStart + (2 + m.numSimpleSelectors) * wordBytes ]
    candidates.length == 6 && v == (natMaximum candidates).getD 0
      && candidates.all (fun c => c <= v)
      && v == candidates.head?.getD 0
      && (match staticWorkingMemorySizeForMeta inputsV
            { m with numSimpleSelectors := 400 } with
          | .error _ => false
          | .ok v2 => v2 == quotientReturnBufferStart + (2 + 400) * wordBytes && v2 > v)

/-- VK:549-561 against the stub planner: the two config fields the reference fills
    arrive at the callee, and the fields it does not touch arrive unchanged from the
    default. This is the gate that makes the threaded hole observable - the stub
    copies the two fields into readable layout fields precisely so that a port that
    forgot VK:557-559 goes red.
    PERTURBATION RUN: deleting the transcriptWords assignment reddens the first
    conjunct; deleting numInstances reddens the second; passing
    verifierMemoryLayoutConfigDefault instead of the incoming config reddens the
    third. -/
def memoryLayoutFor_config_ok : Bool :=
  let expected := orNat
    (Except.map (fun t => t.words) (transcriptBufferLayoutForMeta inputsV.meta_
      inputsV.numInstances)) 999
  match memoryLayoutFor envV inputsV inputsV.meta_ renderVkV
      (ptrMemory (valueFromNat 0x4000)) verifierMemoryLayoutConfigDefault with
  | .error _ => false
  | .ok mem =>
    mem.transcriptMptr == expected
      && mem.verifierReturnMptr == inputsV.numInstances
      && mem.pcs.rotPointsWords == pcsMemoryRequirementsDefault.rotPointsWords
      && mem.scalarInvScratchMptr == memV.scalarInvScratchMptr
      && ptrBeq mem.vkMptr (ptrMemory (valueFromNat 0x4000))

/-- VK:474-523, the feature-off arm: n_dummy is 0, so num_evals is unchanged, no
    dummy words are written, and the meta that comes back differs from the input
    only in num_point_sets.
    PERTURBATION RUN: forcing n_dummy to 1 reddens the first three conjuncts;
    calling setNumDummyEvals with mainEvals instead of n reddens the second. -/
def metaDataForVk_featureOff_ok : Bool :=
  match metaDataForVk Features.solidity envV inputsV renderVkV
      (ptrMemory (valueFromNat 0x4000)) with
  | .error _ => false
  | .ok (meta_, data, mem) =>
    meta_.numDummyEvals == 0
      && meta_.numEvals == inputsV.meta_.numEvals
      && data.dummyEvalWords.isEmpty
      && meta_.numPointSets == orNat (numPointSets inputsV.meta_ data) 999
      && meta_.numPointSets > 0
      && ptrBeq mem.vkMptr (ptrMemory (valueFromNat 0x4000))

/-- The point-set ordering claim of VK:519-522, checked through the stub's recorded
    config: the layout the function returns was built from a meta whose
    num_point_sets is the planned count. Reordering VK:519-521 so the layout is
    built before the count is set changes the transcript bound whenever the
    point-set count affects the proof layout, which it does: from_protocol reads
    num_point_sets (AP:126) and the q_eval sections depend on it.
    PERTURBATION RUN: swapping the last two statements of metaDataForVk reddens the
    first conjunct. -/
def metaDataForVk_pointSetsOrder_ok : Bool :=
  match metaDataForVk Features.solidity envV inputsV renderVkV
      (ptrMemory (valueFromNat 0x4000)) with
  | .error _ => false
  | .ok (meta_, _, mem) =>
    mem.transcriptMptr == orNat
      (Except.map (fun t => t.words) (transcriptBufferLayoutForMeta meta_
        inputsV.numInstances)) 999
      && meta_.numPointSets == orNat
          (numPointSets meta_ (orNat (Data.new meta_ renderVkV mem) dataEmptyStub)) 998

/-- The feature-ON arm (R8's second branch): with outer-fewer-point-sets the dummy
    count comes from num_dummy_queries on the RAW data, num_evals grows by it, and
    the dummy words are written. Both arms are gated because the reference has both,
    and because the deployed profile is the off arm - so the on arm is the one nobody
    runs in production and the one most likely to rot.
    PERTURBATION RUN: hard-coding n_dummy to 0 reddens the second and third
    conjuncts whenever the fixture's dummy count is non-zero; deleting the
    n_dummy > 0 guard (always calling set_dummy_eval_words) reddens
    metaDataForVk_featureOff_ok. -/
def metaDataForVk_featureOn_ok : Bool :=
  let feat : Features := { Features.solidity with outerFewerPointSets := true }
  match metaDataForVk feat envV inputsV renderVkV
      (ptrMemory (valueFromNat 0x4000)) with
  | .error _ => false
  | .ok (meta_, data, _) =>
    meta_.numDummyEvals == orNat (numDummyQueries inputsV.meta_
        (orNat (Data.new inputsV.meta_ renderVkV memV) dataEmptyStub)) 997
      && meta_.numEvals == inputsV.meta_.numEvals + meta_.numDummyEvals
      && data.dummyEvalWords.length == meta_.numDummyEvals

/-- VK:525-547. The loop converges on the first iteration for this fixture - the
    starting VK_MPTR is computed from the same meta the first pass returns - and the
    returned pointer is the one the planner asked for.
    PERTURBATION RUN: changing the loop bound from 3 to 2 reddens nothing here,
    because the fixture settles on the second iteration; that is stated rather than
    hidden, and it is why the panic arm below is a real attempt and not a formality. -/
def metaDataForStableStaticLayout_ok : Bool :=
  match metaDataForStableStaticLayout Features.solidity envV inputsV renderVkV with
  | .error _ => false
  | .ok (vkMptr, meta_, data, _) =>
    -- the pointer that came back is the one the PLAN asked for, which is not the
    -- pointer the loop started from: the starting VK_MPTR is computed from the raw
    -- meta, and setting num_point_sets moves the transcript bound (9024 to 9184
    -- here), so the second iteration is the one that settles.
    ptrBeq vkMptr (ptrMemory (valueFromNat
      (orNat (staticWorkingMemorySizeForMeta inputsV meta_) 999)))
      && orNat (staticWorkingMemorySizeForMeta inputsV inputsV.meta_) 999
          != orNat (staticWorkingMemorySizeForMeta inputsV meta_) 998
      && meta_.numPointSets > 0
      && data.dummyEvalWords.isEmpty

/-! ## The one panic site this package could NOT reach

VK:546 - "static verifier memory layout did not converge after proof-shape
planning" - is ported (metaDataForStableStaticLayout's final arm), but NO stub in
this file can fire it, and the attempts are recorded here rather than dropped,
because a panic site with no demonstrated failure mode is exactly the R-38 / R-41
shape this project keeps hitting.

What was tried, and why each one converged instead:
* a planner stub that adds a constant to the transcript word count - the added
  words do not feed back into the plan, because staticWorkingMemorySizeForMeta
  reads the transcript bound from the META, not from the layout;
* a stub that aliases commsMptrBase onto VK_MPTR, and one that aliases the advice
  commitment base onto VK_MPTR plus the constant-table length (so the aliasing
  moves as the reservation moves): both settle on the second iteration, because
  num_point_sets depends on the EQUALITY PATTERN of the commitment pointers and
  not on their addresses, and a uniform shift preserves the pattern;
* a stub whose advice base alternates with the parity of the constant-table
  length: also converges, for the same reason.

The structural fact behind all three is that the plan can only move through
num_point_sets, and num_point_sets is address-invariant under the pointer model
Data.new uses. So VK:546 is, like VK:436 and VK:438, a guard against a FUTURE
change to the planner rather than a reachable input today - and unlike those three
it is not even restated from a loop condition, it is genuinely the "no fixed point
in three steps" case that the reference's own comment at VK:527-529 describes.
It stays ported per R1 and R4. No gate is claimed for it. -/

/-! ## R11 evidence: the struct itself -/

/-- MOD:37-45 read back: six fields in the Rust's order, and the two that vk.rs
    never reads are still carried. A reviewer checking R11 against the Rust should
    be able to see that the port did not quietly drop the fields it has no use for. -/
def verifierBuildInputs_fields_ok : Bool :=
  inputsV.numInstances == 3 && inputsV.numCommittedInstances == 1
    && (match inputsV.accEncoding with
        | some e => e.numLimbs == 7 && e.numLimbBits == 56 && e.offset == 4
        | none => false)
    && inputsV.meta_.numEvals == Midfall.Generator.EncodingKats.metaFixture.numEvals
    && inputsV.params.gLagrange.length == 4
    && expOf inputsV.params.g2 == 1 && expOf inputsV.params.sG2 == 3
    && inputsV.vk.domain.k == 2 && inputsV.vk.transcriptRepr.val == 7

#eval fixtureDomain_ok -- expect true
#eval fixturePointsDistinct_ok -- expect true
#eval vkHeaderSlot_word_ok -- expect true
#eval vkHeaderField_agreesWithTable_ok -- expect true
#eval vkHeaderBuilder_fullOk_ok -- expect true
#eval vkHeaderBuilder_duplicateErr_ok -- expect true
#eval vkHeaderBuilder_widthErr_ok -- expect true
#eval vkHeaderBuilder_overflowErr_ok -- expect true
#eval vkHeaderBuilder_finishMissingErr_ok -- expect true
#eval omegaPowers_accumulatorEquivalence_ok -- expect true
#eval srsTauCommitment_semantics_ok -- expect true
#eval srsTauIsConsistent_honestSrs_ok -- expect true
#eval srsFingerprint_preimage_ok -- expect true
#eval srsFingerprint_fieldOrder_ok -- expect true
#eval generateBaseVk_header_ok -- expect true
#eval generateBaseVk_g1g2Slots_ok -- expect true
#eval generateBaseVk_srsAsserts_ok -- expect true
#eval generateBaseVk_comms_ok -- expect true
#eval generateBaseVk_accEncoding_ok -- expect true
#eval generateBaseVk_omegaInvToL_ok -- expect true
#eval generateVkDirect_table_ok -- expect true
#eval generateVkDirect_empty_ok -- expect true
#eval generateVkDirect_wordHeaders_ok -- expect true
#eval payloadOrder_sectionsTiled_ok -- expect true
#eval generateVk_converges_ok -- expect true
#eval generateVk_panics_ok -- expect true
#eval generateVk_hazard5_ok -- expect true
#eval transcriptBufferLayoutForMeta_ok -- expect true
#eval transcriptBufferWordsBound_ok -- expect true
#eval staticWorkingMemorySizeForMeta_ok -- expect true
#eval memoryLayoutFor_config_ok -- expect true
#eval metaDataForVk_featureOff_ok -- expect true
#eval metaDataForVk_pointSetsOrder_ok -- expect true
#eval metaDataForVk_featureOn_ok -- expect true
#eval metaDataForStableStaticLayout_ok -- expect true
#eval verifierBuildInputs_fields_ok -- expect true

end Midfall.Generator.VkKats

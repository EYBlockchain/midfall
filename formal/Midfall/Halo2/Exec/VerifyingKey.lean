-- |
-- Midfall.Halo2.Exec.VerifyingKey
--
-- The verifying key (rust: proofs/src/plonk/mod.rs:61-70 and its verifier-
-- reachable methods). Six fields in source order, the accessors the verifier
-- uses, hash_into, and WellFormed - the side conditions plan 9.2 attaches to the
-- refinement theorem.
--
-- R-1 RESOLVED HERE (docs/REVIEW.md R-1). from_parts computes transcript_repr by
-- Blake2b-512 (personal "Halo2-Verify-Key") over: VERSION, k, the fixed
-- commitment count and each fixed commitment written RawBytesUnchecked, the
-- permutation commitment count and each of those, then the Rust {:?} renderings
-- of PinnedEvaluationDomain and PinnedConstraintSystem, finally
-- F::from_uniform_bytes of the 64-byte digest. Reproducing that in Lean means
-- byte-exact Debug output for two types, which is not a property of the proof
-- system at all - it is an artefact of how halo2 formats structs, and the Rust
-- code comment itself says "We should eventually move away from debug
-- implementation for this purpose" (plonk/mod.rs:289-291, halo2 issue #5).
-- Plan Section 1 already settles it: keygen is out of scope and transcript_repr
-- is TAKEN AS GIVEN. So the port carries transcriptRepr as a field supplied on
-- import, and conformance asserts the imported value equals the Rust one
-- rather than recomputing it. fromParts below therefore takes it as an
-- argument and does not hash anything.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Transcript

namespace Midfall.Halo2

/-- rust: proofs/src/plonk/mod.rs:61-70 (struct VerifyingKey). Field order is
    the Rust order (rule R1). The Rust is generic in the PCS and its Commitment
    type is CS::Commitment; under rule R9's KZG instantiation that is G1, so
    the port is parameterised by G1 directly. -/
structure VerifyingKey (Fr G₁ : Type) where
  /-- rust: domain: EvaluationDomain<F> -/
  domain : EvaluationDomain Fr
  /-- rust: fixed_commitments: Vec<CS::Commitment> -/
  fixedCommitments : Array G₁
  /-- rust: permutation: permutation::VerifyingKey<F, CS> -/
  permutation : Permutation.VerifyingKey G₁
  /-- rust: cs: ConstraintSystem<F> -/
  cs : ConstraintSystem Fr
  /-- rust: cs_degree - cached maximum degree of cs, which by construction
      cannot change after construction. The cache is what makes the verifier's
      chunk arithmetic cheap, and WellFormed.csDegreeMatches is the proof that
      the cache and the recomputation agree. -/
  csDegree : Nat
  /-- rust: transcript_repr - the representative of this VK in transcripts.
      Imported, not computed: see the file header and R-1. -/
  transcriptRepr : Fr

/-- rust: plonk/mod.rs:122-124 (n). -/
def VerifyingKey.n {Fr G₁ : Type} (vk : VerifyingKey Fr G₁) : Nat := vk.domain.n

/-- rust: plonk/mod.rs:223-282 (from_parts). The Rust computes cs_degree and
    transcript_repr here; the port takes both as arguments (R-1) and is
    otherwise the same construction. -/
def VerifyingKey.fromParts {Fr G₁ : Type} (domain : EvaluationDomain Fr)
    (fixedCommitments : Array G₁) (permutation : Permutation.VerifyingKey G₁)
    (cs : ConstraintSystem Fr) (csDegree : Nat) (transcriptRepr : Fr) :
    VerifyingKey Fr G₁ :=
  { domain, fixedCommitments, permutation, cs, csDegree, transcriptRepr }

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
  [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]

/-- rust: plonk/mod.rs:283-291 (hash_into): absorb the transcript representative
    and nothing else. The verifier calls this first (plonk/verifier.rs:70), so
    every later challenge depends on it - which is exactly why importing the
    value rather than recomputing it makes the VK binding an assumption about
    the importer, not a theorem. -/
def VerifyingKey.hashInto (vk : VerifyingKey (Fr p) G₁) : TranscriptM Unit :=
  tmCommon hashableFr vk.transcriptRepr

/-- The side conditions plan 9.2 attaches to the refinement theorem
    (verifyMsgs_iff_spec). These are the invariants the verifier itself relies
    on and which a malformed-but-parseable VK can violate - each one below
    corresponds to a concrete panic or silent misread elsewhere in the port:

  * csDegreeMatches - the cached cs_degree must equal a recomputation, and the
    recomputation must not panic (ConstraintSystem.degree is Except-valued
    precisely because of the R-13 logUp division by zero).
  * chunkLenPositive - permutation/verifier.rs:41 computes chunk_len =
    cs_degree - 2 and calls columns.chunks(chunk_len), which PANICS at 0 (Rust
    usize subtraction also wraps below 2). cs_degree >= 3 is what the constant
    permutation required_degree guarantees for a Rust-built CS; stated here so
    a hand-built one cannot silently break the read schedule (finding P1).
  * domainConsistent - the domain must be the one the CS implies. The second
    conjunct is assessment F7 (hLimbs) at VK level: the quotient degree is
    cs_degree - 1, which is what pins how many limb commitments the verifier
    reads out of the proof (verifier.rs:288).
  * permutationCommitmentsMatch - the VK carries one sigma commitment per
    permutation COLUMN: permutation.rs:123 reads (0..argument.columns.len())
    and keygen.rs:244-250 pushes one per column, so a mismatch is an
    out-of-bounds read in permutation::VerifyingKey::evaluate (finding P1).
  * fixedCommitmentsMatch - the verifier indexes vk.fixed_commitments by the
    column indices the CS names.
  * singlePhase - plan Section 13: multi-phase circuits are excluded, and the
    challenge schedule the transcript implements has no per-phase loop.
  * committedInstancesOn - BASELINE.md records committed-instances as always
    enabled; the instance-absorb path at verifier.rs:92-101 assumes it.
  * advicePhaseTotal / challengePhaseTotal - D-GATE7: the phase vectors are the
    same length as the column/challenge counts, so the Rust's pre-filled
    `Commitment::default()` / `F::ZERO` slots are never observed and the port's
    `scatterIndexed` fault is off-domain. `scatterIndexed_hole_is_a_fault` keeps
    the off-domain behaviour as a W12 witness.
  * lookupChunkable - D-GATE12: every lookup's `nb_parallel_lookups_per_chunk`
    is defined and positive, so `chunkByDegree` succeeds. Neither follows from
    the counts above: `logup.rs:237` divides by a zero input degree and
    `rustChunks` panics on a zero chunk count, both STATIC properties of the
    key. Stated as a decidable Bool equation so every witness is a computation.
  * fixedSelectorBound - D-GATE14: `num_simple_selectors ≤ num_fixed_columns`,
    the no-throw precondition of `readFixedEvals` (`verifier.rs:400`).
  * fixedQueriesBound / simpleSelectorQueriesBound - D-GATE15: the two counts that
    keep `listInsertAt` in range during `readFixedEvals`'s insert fold.
  * instanceRotZero - D-GATE15: instance-query rotations are `0` (the deployed
    `noRotInst` profile), making `i32Abs minRot` and the instance slice window
    well-defined. -/
structure VerifyingKey.WellFormed (vk : VerifyingKey (Fr p) G₁) (F : Features) : Prop where
  csDegreeMatches : vk.cs.degree = .ok vk.csDegree
  chunkLenPositive : 3 ≤ vk.csDegree
  domainConsistent : vk.domain.n = 2 ^ vk.domain.k ∧
    vk.domain.quotientPolyDegree = vk.csDegree - 1
  permutationCommitmentsMatch :
    vk.permutation.commitments.size =
      vk.cs.permutation.columns.size
  fixedCommitmentsMatch : vk.fixedCommitments.size = vk.cs.numFixedColumns
  singlePhase : vk.cs.numChallenges = 0
  committedInstancesOn : F.committedInstances = true
  /-- D-GATE7 (2026-11-22): every advice slot is placeable. Rust `parse_trace`
      pre-fills `advice_commitments` with `CS::Commitment::default()` and zips
      `advice_column_phase` against the row (verifier.rs:107-126), so a phase
      vector shorter than `num_advice_columns` leaves defaults in the transcript;
      the port's `scatterIndexed` instead faults on such a hole. The statements
      quantify over this interface, where the hole does not exist.
      `scatterIndexed_hole_is_a_fault` stays as the off-domain W12 witness. -/
  advicePhaseTotal : vk.cs.adviceColumnPhase.size = vk.cs.numAdviceColumns
  /-- D-GATE7: every challenge slot is placeable, for the same reason, over
      `challenge_phase` / `num_challenges` (verifier.rs:127-143). -/
  challengePhaseTotal : vk.cs.challengePhase.size = vk.cs.numChallenges
  /-- **D-GATE12: every lookup chunks.** The verifier's read walk runs
      `LogupBatchedArgument.chunkByDegree` on every lookup
      (`verifier.rs:155-162` and `:188-189`). That function is not total: it
      panics at `logup.rs:237` when the lookup's input degree is zero (a
      division by zero) and `rustChunks` panics at `logup.rs:329` when the
      parallel-lookups count is zero. Both are STATIC facts about the key, and
      neither follows from the fields above. Stated as a decidable Bool
      equation (success AND positivity) so every witness is a computation. -/
  lookupChunkable : ∀ l ∈ vk.cs.lookups.toList,
    (match l.nbParallelLookupsPerChunk vk.csDegree with
     | .ok nb => decide (0 < nb)
     | .error _ => false) = true
  /-- **D-GATE14: the fixed-eval read does not throw.** `readFixedEvals` reads
      `num_fixed_columns - num_simple_selectors` scalars and throws
      `Error.transcript unexpectedEof` when `numSimpleSelectors > numFixedColumns`
      (`verifier.rs:400`). `WellFormed` pins neither count against the other, so the
      read walk needs the bound explicitly. (The generator's `programOk` and the
      protocol plan's `validate` each imply it for the deployed renders; this is the
      interface clause the verifier statements quantify over.) -/
  fixedSelectorBound : vk.cs.numSimpleSelectors ≤ vk.cs.numFixedColumns
  /-- **D-GATE15(a): the fixed-query insert has room.** `readFixedEvals` folds
      `listInsertAt acc step.1` over the fixed queries, which panics when
      `step.1 > acc.length` (`verifier.rs:410`). The list starts at
      `numFixedColumns - numSimpleSelectors` and grows by one per simple-selector
      query, so these two counts are the no-panic precondition. -/
  fixedQueriesBound : vk.cs.fixedQueries.size ≤ vk.cs.numFixedColumns
  /-- D-GATE15(a), second half: at most `numSimpleSelectors` of the fixed queries are
      simple, so the insert fold never outruns the list. -/
  simpleSelectorQueriesBound : vk.cs.numSimpleSelectors ≤
    (vk.cs.fixedQueries.toList.filter
      (fun q => vk.cs.hasSimpleSelectorCol q.1.index)).length
  /-- **D-GATE15(b): the instance-query rotations are `0`** (the deployed profile's
      `SupportedV2.noRotInst`, lifted to the interface). This is the key-side half of
      the `i32Abs`/instance-window side conditions: with all rotations `0`,
      `minRot = maxRot = 0` and `i32Abs 0` succeeds. (The runtime half -
      `inst.size < 2^31` so the `asI32` window does not wrap - is a calldata fact,
      stated at the `readAlgebra` walk, not a key field.) -/
  instanceRotZero : ∀ q ∈ vk.cs.instanceQueries.toList, q.2.int = 0
  /-- **D-GATE15(c): every instance query names a valid instance column.**
      `readAlgebra` indexes the instance matrix as
      `instances[q.1.index - nbCommittedInstances]` (`verifier.rs:366`), a slice
      index; `parse_trace`'s column-count check is a `zip` and does not cover a
      query whose column is past `numInstanceColumns`. The interface pins the
      bound so the read walk's index is always in range (the runtime half,
      `inst.size < 2^31`, stays at the walk). -/
  instanceQueriesBound : ∀ q ∈ vk.cs.instanceQueries.toList,
    q.1.index < vk.cs.numInstanceColumns

/-! rust: plonk/mod.rs:94-120 (write), :124-150 (read), :151-186
    (read_from_cs), :218-221 (bytes_length), :293-300 (pinned), and
    permutation.rs:105-134 (the permutation VK's own serde) - NOT ported.
    Evidence: the binary VK serde is reached only from itself and from
    ProvingKey::read (plonk/mod.rs:416, prover side); nothing in the verifier-
    reachable set calls it, and plan Section 5 has conformance import the VK as
    vk.json (full cs, k, omega, commitments, cs_degree, transcript_repr) rather
    than replaying the Rust byte format. read_from_cs additionally depends on
    ConstraintSystem::default plus the whole selector-conversion path, which is
    keygen-side. If a later package wants the binary reader, the pieces are
    already ported: SerdeFormat and byteLength (Exec/Arith), the codecs
    (Common/Codec) and the CS record (Exec/Circuit). -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

-- A key over Fr 17 on the size-4 domain hand-computed in Exec/Domain (omega =
-- 13). j = 3 gives quotient_poly_degree 2, which is what cs_degree - 1 = 2
-- demands, so domainConsistent's second conjunct is exercised rather than
-- assumed. The permutation argument has no columns, so the commitment count is
-- 0 as well and the vector is legitimately empty.
def vkKats_ok : Bool :=
  match EvaluationDomain.new (F := Fr 17) fc17 3 2 with
  | .error _ => false
  | .ok dom =>
      let cs0 := ConstraintSystem.default (F := Fr 17)
      let vk : VerifyingKey (Fr 17) Nat :=
        { domain := dom, fixedCommitments := #[0, 0], permutation := ⟨#[]⟩,
          cs := { cs0 with numFixedColumns := 2 },
          csDegree := 3, transcriptRepr := 7 };
      (match vk.cs.degree with | .ok d => d == 3 | .error _ => false) &&
      dom.quotientPolyDegree == 2 && dom.n == 4 && vk.n == 4 &&
      vk.csDegree - 2 == 1 &&
      vk.permutation.commitments.size ==
        vk.cs.permutation.columns.size &&
      vk.fixedCommitments.size == vk.cs.numFixedColumns &&
      vk.cs.numChallenges == 0 &&
      (match (vk.hashInto).run (Transcript.initFromBytes Bytes.empty) with
       | .ok ((), t) => t.pos == 0 &&
         t.state == (hashableFr (p := 17)).toInput 7
       | .error _ => false)

-- hash_into absorbs exactly the 32-byte big-endian repr of transcript_repr and
-- reads nothing, so the cursor stays at 0.
def vkHashInto_kats_ok : Bool :=
  ((hashableFr (p := 17)).toInput 7).size == 32

end Kats

#eval Midfall.Halo2.vkKats_ok          -- expect true
#eval Midfall.Halo2.vkHashInto_kats_ok -- expect true

end Midfall.Halo2

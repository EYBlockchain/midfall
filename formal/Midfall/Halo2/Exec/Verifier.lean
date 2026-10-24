-- |
-- Midfall.Halo2.Exec.Verifier
--
-- The proof-parsing half of the verifier (rust: proofs/src/plonk/verifier.rs).
-- This package ports VerifierTrace and parse_trace: the sequence of transcript
-- reads and squeezes that turns a proof byte string into the commitments and
-- challenges the algebraic checks consume.
--
-- Why this file is the one to be most careful with: the ORDER of these reads and
-- squeezes is the Fiat-Shamir protocol. Reordering two squeezes, or reading a
-- commitment that the Rust does not read, does not produce a wrong answer that a
-- test would catch - it produces a different challenge stream, so the verifier
-- accepts a different language. Everything here is transcribed line by line.
--
-- Not ported: VerifierTrace's Debug/trace plumbing and the
-- solidity-verifier-trace record_* calls (plan Section 1 excludes trace render
-- modes), and parse_trace's own trace capture, which is what the conformance
-- harness reads - the Lean side gets the same values by running this function.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Common.Codec
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Logup
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Transcript
import Midfall.Halo2.Exec.Trash
import Midfall.Halo2.Exec.VerifyingKey
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Linearization
import Midfall.Halo2.Exec.Pcs
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Kzg.Params
import Midfall.Halo2.Exec.Kzg.Utils

namespace Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- rust: plonk/verifier.rs:26-37 (struct VerifierTrace). Field order is the
    Rust order. One entry per PROOF in the outer vectors (the Rust is
    multi-proof-capable; the Solidity path uses exactly one, which is what
    plan 9.2's `[[0]]` / `[[inst]]` nesting encodes). -/
structure VerifierTrace (Fr G₁ : Type) where
  adviceCommitments : Array (Array G₁)
  lookups : Array (Array (Logup.Committed G₁))
  trashcans : Array (Array (Trash.Committed G₁))
  permutations : Array (Permutation.Committed G₁)
  challenges : Array Fr
  beta : Fr
  gamma : Fr
  theta : Fr
  trashChallenge : Fr
  y : Fr

/-- The order in which advice commitments are read: for each phase in
    `cs.phases()`, the advice columns whose `advice_column_phase` equals that
    phase, in column order (verifier.rs:108-127). The Rust pre-fills the matrix
    with `Commitment::default()` and then overwrites each slot; the port computes
    each slot from the read sequence instead, which agrees exactly when every
    column index appears once below - and it does, because `phases()` is
    `0..=max_phase` over the same vector (circuit.rs:2431-2440). -/
def adviceReadOrder {F : Type} (cs : ConstraintSystem F) : List Nat :=
  cs.phases.flatMap fun ph =>
    (List.range cs.numAdviceColumns).filterMap fun i =>
      if (cs.adviceColumnPhase[i]?.map (fun q => q.val)) == some ph.val then some i else none

/-- Place `(index, value)` pairs into a vector of length `n`, faulting on a hole.

    This models the Rust writing into a matrix that was pre-filled with
    `CS::Commitment::default()` (verifier.rs:106-107): every slot must be written
    exactly once, and a hole would leave the default point in the transcript -- a
    DIFFERENT point, absorbed into every later challenge -- so it is a fault, not a
    silent default. A duplicate index overwrites, which is also what the Rust does.
    -/
def scatterIndexed {α : Type} (n : Nat) (pairs : List (Nat × α)) (site : String) :
    Except Fault (Array α) :=
  let placed : List (Option α) :=
    pairs.foldl (init := List.replicate n none) fun acc e =>
      if e.1 < n then acc.take e.1 ++ [some e.2] ++ acc.drop (e.1 + 1) else acc
  match placed.mapM (fun x => x) with
  | some xs => .ok xs.toArray
  | none => .error (Fault.panic site)
/-- rust: plonk/verifier.rs:24-232 (parse_trace). -/
def parseTrace (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) :
    TranscriptM (VerifierTrace (Fr p) G₁) := do
  -- verifier.rs:46-47, rule R8: WITHOUT the committed-instances feature the Rust
  -- REPLACES the caller's argument with one empty row per proof, and it does so
  -- BEFORE the is_empty check at :49. Porting that only inside
  -- verify_algebraic_constraints - which an earlier revision did - makes the
  -- feature-off profile diverge twice: an empty committed argument is rejected
  -- where the Rust accepts it, and a non-empty one is absorbed into the transcript
  -- where the Rust would never have seen it, i.e. a different challenge stream.
  -- Found by external audit; recorded as docs/REVIEW.md R-32.
  let committed :=
    if feat.committedInstances then committed₀
    else (List.range inst.size).toArray.map fun _ => #[]
  -- verifier.rs:49-67: instance shape checks. Three distinct
  -- Error::InvalidInstances exits, and the third uses zip, so a committed/inst
  -- length mismatch leaves the extra rows UNCHECKED (rule R3).
  if committed.isEmpty then
    throw (Fault.error Error.invalidInstances)
  let nbCommitted := (committed[0]?.map (fun r => r.size)).getD 0;
  if committed.toList.any (fun r => r.size ≠ nbCommitted) then
    throw (Fault.error Error.invalidInstances)
  if ((List.zip committed.toList inst.toList).any fun (c, i) =>
       c.size + i.size ≠ vk.cs.numInstanceColumns) then
    throw (Fault.error Error.invalidInstances)
  let numProofs := inst.size;
  -- verifier.rs:70: hash the VK in. Everything downstream is bound to it.
  vk.hashInto
  -- verifier.rs:90-92: absorb the committed instance commitments
  for row in committed.toList do
    for com in row do
      tmCommon (hashableG1 g1) com
  -- verifier.rs:96-101: per instance column, absorb its LENGTH then its values.
  -- The length is absorbed as a field element, so an instance column of length
  -- n and one of length n' with n ≠ n' cannot collide even if their values do.
  for row in inst.toList do
    for col in row do
      tmCommon (hashableFr (p := p)) (Nat.cast col.size)
      for v in col do
        tmCommon (hashableFr (p := p)) v
  -- verifier.rs:105-146: the phase loop. The nesting is
  --   for phase in cs.phases():
  --     for proof in proofs:            read that proof's columns OF THIS PHASE
  --     for idx, ch in challenge_phase: squeeze the challenges OF THIS PHASE
  -- so phase is the OUTERMOST axis: all proofs' phase-0 columns, then the
  -- phase-0 challenges, then all proofs' phase-1 columns, and so on.
  --
  -- Reading every commitment first and squeezing every challenge afterwards --
  -- the obvious transcription, and what an earlier revision of this file did --
  -- agrees only when there is one phase, or one proof and no challenges. That is
  -- exactly the supported profile (WellFormed.singlePhase), so no theorem here
  -- depends on it, but rule R1 asks for the loop the Rust has and the divergence
  -- is a different transcript for any multi-phase key. Found by external review;
  -- pinned by phaseInterleave_kats_ok below.
  let (advPairs, chalPairs) ← vk.cs.phases.foldlM
      (init := ((List.range numProofs).map (fun _ => ([] : List (Nat × G₁))),
                ([] : List (Nat × Fr p))))
      (fun st ph => do
        let cols := (List.range vk.cs.numAdviceColumns).filterMap fun i =>
          if (vk.cs.adviceColumnPhase[i]?.map (fun q => q.val)) == some ph.val
          then some i else none;
        let adv ← (List.range numProofs).foldlM (init := st.1) fun acc k => do
          let reads ← tmReadN (hashableG1 g1) cols.length;
          pure ((acc.take k) ++
                [((acc[k]?.getD []) ++ (List.zip cols reads.toList))] ++
                (acc.drop (k + 1)))
        let chalIdxPhase := List.zip (List.range vk.cs.numChallenges)
          vk.cs.challengePhase.toList
        let chals ← chalIdxPhase.foldlM (init := st.2) fun acc e =>
          if e.2.val == ph.val then do
            let c ← tmSqueezeChallenge
            pure (acc ++ [(e.1, c)])
          else pure acc
        pure (adv, chals))
  let adviceCommitments ← advPairs.foldlM (init := #[]) fun acc pairs => do
    let row ← StateT.lift (scatterIndexed vk.cs.numAdviceColumns pairs
      "proofs/src/plonk/verifier.rs:118")
    pure (acc.push row)
  let challenges ← StateT.lift (scatterIndexed vk.cs.numChallenges chalPairs
    "proofs/src/plonk/verifier.rs:134")
  -- verifier.rs:150: theta keeps the lookup columns linearly independent
  let theta ← tmSqueezeChallenge
  -- verifier.rs:155-162: read the lookup multiplicities, one per proof per
  -- lookup, where the chunking is derived from vk.cs_degree.
  let lookupMultiplicities ← (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let row ← vk.cs.lookups.toList.foldlM (init := #[]) fun acc' l => do
        let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
        let m ← Logup.readMultiplicities chunked (hashableG1 g1)
        pure (acc'.push (m, chunked))
      pure (acc.push row)
  -- verifier.rs:167,172: beta then gamma, squeezed between the multiplicity
  -- reads and the permutation product reads.
  let beta ← tmSqueezeChallenge
  let gamma ← tmSqueezeChallenge
  let permutations ← (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
        (hashableG1 g1)
      pure (acc.push pc)
  -- verifier.rs:176-190: the lookup commitments. NOTE the Rust calls
  -- chunk_by_degree a SECOND time here (verifier.rs:188-189) rather than reusing
  -- the value from the multiplicity pass, so the transcript layout depends on
  -- chunking being a pure function of cs_degree. Kept that way.
  let lookups ← lookupMultiplicities.toList.foldlM
    (init := #[]) fun acc row => do
      let out ← row.toList.foldlM (init := #[]) fun acc' (m, chunked) => do
        let c ← m.readCommitment chunked.numChunks (hashableG1 g1)
        pure (acc'.push c)
      pure (acc.push out)
  -- verifier.rs:194: the trash challenge, squeezed BEFORE the trashcan
  -- commitments are read (and note the trace records it only when there is at
  -- least one trashcan - the squeeze itself is unconditional).
  let trashChallenge ← tmSqueezeChallenge
  let trashcans ← (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let row ← vk.cs.trashcans.toList.foldlM (init := #[]) fun acc' t => do
        let c ← Trash.readCommitted t (hashableG1 g1)
        pure (acc'.push c)
      pure (acc.push row)
  -- verifier.rs:215: y keeps the gates linearly independent
  let y ← tmSqueezeChallenge
  pure { adviceCommitments, lookups, trashcans, permutations, challenges,
         beta, gamma, theta, trashChallenge, y }


-- ## Known-answer checks on the read schedule
--
-- These exist because of docs/REVIEW.md R-20: a schedule bug does not produce a
-- wrong *value* that a self-consistent test would notice, it produces a different
-- number of bytes consumed and a different challenge stream. So the checks below
-- pin the byte accounting exactly, which is what a reordering would break.


/-- rust: proofs/src/plonk/mod.rs:481-608 (partially_evaluate_identities).

    The batched identity, evaluated at x but PARTIALLY: each entry is a pair
    `(Option Nat, F)` where the option is the fixed-column index of the first
    simple queried selector of the gate that produced the term, and `none` means
    the term is fully evaluated and belongs to the constant side. That pair is
    exactly what `computeLinearizationCommitment` consumes, and its grouping by
    selector column is what turns these into the linearization MSM's terms.

    Order is reproduced exactly: gates first (gate order, then polynomial order
    within a gate), then the permutation identities, then logUp, then trash - all
    per proof, with the five per-proof vectors zipped pairwise so a shorter one
    silently truncates the rest (rule R3). The five `.zip` calls nest
    left-associatively in Rust; the port mirrors that with nested pairs rather
    than a five-way zip, because a five-way zip would truncate on the MINIMUM of
    all five where the Rust truncates progressively.

    Panic sites: mod.rs:511 asserts the l_i_range length; the ten evaluation
    closures are `Expression.verifierCallbacks` (Exec/Circuit), which carries the
    virtual-selector panic at mod.rs:532 and the three
    `evals[query.index.unwrap()]` double-aborts at :533-535; and
    `Permutation.expressions` panics on chunk_len = 0 (permutation.rs:237).

    `delta` is a parameter, not a field: `FieldConsts` carries zeta but not delta
    (docs/REVIEW.md R-3 extended). -/
def partiallyEvaluateIdentities {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (delta : Fr p) (vk : VerifyingKey (Fr p) G₁)
    (fixedEvals : Array (Fr p))
    (instanceEvals : Array (Array (Fr p)))
    (adviceEvals : Array (Array (Fr p)))
    (permutationEvals : Array (Array (Permutation.SetEvaluated (Fr p))))
    (lookupEvals : Array (Array (Logup.Evals (Fr p))))
    (trashcanEvals : Array (Array (Trash.Eval (Fr p))))
    (permutationsCommon : Permutation.CommonEvaluated (Fr p))
    (x xn beta gamma theta trashChallenge : Fr p) (challenges : Array (Fr p)) :
    Except Fault (Array (Option Nat × Fr p)) := do
  -- mod.rs:509-515: the Lagrange prelude. The rotation range is
  -- (-(blinding_factors+1)) ..= 0, i.e. blinding_factors + 2 entries, and the
  -- assert at :511 is what pins that l_i_range did not silently drop any.
  let bf ← vk.cs.blindingFactors
  let rotations : List Int :=
    (List.range (bf + 2)).map (fun i => -((bf + 1 : Nat) : Int) + (i : Int))
  let lEvals := vk.domain.lIRange x xn rotations
  unless lEvals.size == bf + 2 do
    throw (Fault.panic "proofs/src/plonk/mod.rs:511")
  let lLast := lEvals[0]!
  let lBlind := ((lEvals.toList.drop 1).take bf).foldl (init := 0) (· + ·)
  let l0 := lEvals[bf + 1]!
  -- mod.rs:525-541: one proof's gate terms. The selector attached to a gate's
  -- polynomial is the FIRST simple queried selector (filter, then next), and the
  -- same index is attached to every polynomial of that gate.
  let oneProof (ae ie : Array (Fr p))
      (pe : Array (Permutation.SetEvaluated (Fr p)))
      (le : Array (Logup.Evals (Fr p))) (te : Array (Trash.Eval (Fr p))) :
      Except Fault (Array (Option Nat × Fr p)) := do
    let cb := Expression.verifierCallbacks (F := Fr p) ae fixedEvals ie challenges;
    let gateTerms ← vk.cs.gates.toList.foldlM (init := #[]) fun acc g => do
      let es ← mapExceptArray (fun poly => Expression.evaluate cb poly) g.polynomials
      let sels := g.queriedSelectors.toList.filter (fun s => s.isSimple)
      let simples := sels.map (fun s => s.index)
      let selIdx := match simples with | x :: _ => some x | [] => none
      pure (acc ++ (es.map fun e => (selIdx, e)))
    -- mod.rs:542-560: the permutation identities, all tagged None (they are
    -- fully evaluated in the selector sense - no gate selector multiplies them).
    let permEs ← Permutation.expressions (p := p) vk.cs vk.csDegree pe
      permutationsCommon ae fixedEvals ie l0 lLast lBlind beta gamma x delta
    -- mod.rs:561-585: logUp. chunk_by_degree is recomputed here from the CS, and
    -- the Rust zips it against the per-proof evals, so a length mismatch
    -- truncates rather than erroring (rule R3).
    let chunked ← mapExceptArray
      (fun l => l.chunkByDegree vk.csDegree) vk.cs.lookups
    let lookupTerms ← (List.zip le.toList chunked.toList).foldlM (init := #[])
      fun acc pair => do
        let es ← Logup.expressions (p := p) pair.1 l0 lLast lBlind theta beta
          pair.2 ae fixedEvals ie challenges
        pure (acc ++ (es.map fun e => (none, e)))
    -- mod.rs:586-600: trash.
    let trashTerms ← (List.zip te.toList vk.cs.trashcans.toList).foldlM
      (init := #[]) fun acc pair => do
        let es ← Trash.expressions (p := p) pair.1 pair.2 trashChallenge
          ae fixedEvals ie challenges
        pure (acc ++ (es.map fun e => (none, e)))
    pure (gateTerms ++ (permEs.map fun e => (none, e)) ++ lookupTerms ++ trashTerms)
  -- mod.rs:516-524 + :601: the five per-proof vectors, zipped left-associatively
  -- so the element type is ((((advice, instance), permutation), lookup), trash).
  let zipped := List.zip
    (List.zip (List.zip (List.zip adviceEvals.toList instanceEvals.toList)
                permutationEvals.toList) lookupEvals.toList) trashcanEvals.toList
  -- foldlM here MUST thread the accumulator: oneProof returns ONE proof's terms,
  -- so a body that ignores the accumulator silently keeps only the LAST proof's
  -- identities. With numProofs = 1 - every path the plan supports - that is
  -- invisible, which is how it survived the single-proof KAT.
  let rows ← (zipped.foldlM (init := (#[ ] : Array (Option Nat × Fr p)))
    fun acc e => do
      let row ← oneProof e.1.1.1.1 e.1.1.1.2 e.1.1.2 e.1.2 e.2
      pure (acc ++ row))
  pure rows
section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

-- A stand-in codec over Nat so the schedule can be exercised without a curve:
-- the 48-byte compressed slot is read as a big-endian natural.
def natG1Codec : G1Codec Nat where
  ofCompressed? b := if b.size == 48 then some (bytesToNatBE b) else none
  toCompressed P := natToBytesBE P 48
  toEip P := natToBytesBE P 128
  ofEip? b := if b.size == 128 then some (bytesToNatBE b) else none

-- The smallest CS the schedule can run on: one advice column, no lookups, no
-- trashcans, no permutation columns, no challenges, one instance column of two
-- values and no committed instances. cs_degree 3 keeps chunk_len = 1 positive.
def traceCs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default (F := Fr 17) with
    numAdviceColumns := 1, numInstanceColumns := 1,
    adviceColumnPhase := #[⟨0⟩] }

def traceDomFallback : EvaluationDomain (Fr 17) :=
  { n := 4, k := 2, extendedK := 2, omega := 13, omegaInv := 4,
    extendedOmega := 13, extendedOmegaInv := 4, gCoset := 2, gCosetInv := 4,
    quotientPolyDegree := 2, ifftDivisor := 13, extendedIfftDivisor := 13,
    tEvaluations := #[8], barycentricWeight := 13 }


def traceVk : VerifyingKey (Fr 17) Nat :=
  match EvaluationDomain.new (F := Fr 17) fc17 3 2 with
  | .ok dom =>
      { domain := dom, fixedCommitments := #[], permutation := ⟨#[]⟩,
        cs := traceCs, csDegree := 3, transcriptRepr := 7 }
  | .error _ =>
      { domain := (traceDomFallback), fixedCommitments := #[], permutation := ⟨#[]⟩,
        cs := traceCs, csDegree := 3, transcriptRepr := 7 }

-- 48 bytes of advice commitment, and one instance column of length 2.
def traceProof : Bytes := natToBytesBE 42 48

def parseTrace_kats_ok : Bool :=
  match (parseTrace natG1Codec Features.solidity traceVk #[#[]] (#[#[#[0, 1]]])).run
        (Transcript.initFromBytes traceProof) with
  | .error _ => false
  | .ok (tr, t) =>
      -- exactly the one 48-byte commitment is consumed, nothing more
      t.pos == 48 &&
      tr.adviceCommitments.size == 1 &&
      tr.adviceCommitments[0]?.map (fun r => r.size) == some 1 &&
      (match tr.adviceCommitments[0]? with
       | some r => r[0]? == (42 : Nat)
       | none => false) &&
      tr.challenges.size == 0 &&
      tr.permutations.size == 1 &&
      tr.permutations[0]?.map (fun pc => pc.permutationProductCommitments.size) ==
        some 0 &&
      tr.lookups.size == 1 && tr.lookups[0]?.map (fun r => r.size) == some 0 &&
      tr.trashcans.size == 1 &&
        tr.trashcans[0]?.map (fun r => r.size) == some 0

-- a one-byte-short proof must fail as a transcript error, not silently read less
def parseTrace_short_kats_ok : Bool :=
  match (parseTrace natG1Codec Features.solidity traceVk #[#[]] (#[#[#[0, 1]]])).run
        (Transcript.initFromBytes (natToBytesBE 42 47)) with
  | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => true
  | _ => false

-- the instance shape checks fire before anything is absorbed
def parseTrace_shape_kats_ok : Bool :=
  -- no proofs at all
  (match (parseTrace natG1Codec Features.solidity traceVk #[] #[]).run
        (Transcript.initFromBytes traceProof) with
   | .error (Fault.error Error.invalidInstances) => true
   | _ => false) &&
      -- two instance columns where the CS declares one
      (match (parseTrace natG1Codec Features.solidity traceVk #[#[]] (#[#[#[0], #[0]]])).run
            (Transcript.initFromBytes traceProof) with
       | .error (Fault.error Error.invalidInstances) => true
       | _ => false) &&
      -- committed rows of differing lengths
      (match (parseTrace natG1Codec Features.solidity traceVk (#[#[], #[1]] : Array (Array Nat)) (#[#[], #[]])).run
            (Transcript.initFromBytes traceProof) with
       | .error (Fault.error Error.invalidInstances) => true
       | _ => false)


-- partially_evaluate_identities: two gates over one proof. Gate 1 is
-- advice0 * advice1 with a SIMPLE queried selector (index 1); gate 2 is
-- advice0 + advice1 whose only queried selector is VIRTUAL (is_simple = false).
-- Expected, hand-computed over Fr 17 with advice evals [3, 4]:
--   [(Some 1, 12), (None, 7)]
-- i.e. the gate order is preserved, a simple selector tags its gate's terms with
-- its column index, a virtual one tags them None (the Rust takes the FIRST
-- simple selector via filter-then-next, mod.rs:543-547), and the empty
-- permutation / logUp / trash inputs contribute nothing.
def advx (i : Nat) : Expression (Fr 17) :=
  .advice { index := some i, columnIndex := i, rotation := .cur, phase := ⟨0⟩ }

def peGate1 : Gate (Fr 17) :=
  { name := "g1", constraintNames := #["c"],
    polys := #[Expression.product (advx 0) (advx 1)],
    queriedSelectors := #[{ index := 1, isSimple := true }], queriedCells := #[] }

def peGate2 : Gate (Fr 17) :=
  { name := "g2", constraintNames := #["c"],
    polys := #[Expression.sum (advx 0) (advx 1)],
    queriedSelectors := #[{ index := 0, isSimple := false }], queriedCells := #[] }

def peCs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default (F := Fr 17) with
    numAdviceColumns := 2, adviceColumnPhase := #[⟨0⟩, ⟨0⟩],
    numInstanceColumns := 1, gates := #[peGate1, peGate2] }

def peDom : EvaluationDomain (Fr 17) :=
  { n := 4, k := 2, extendedK := 2, omega := 13, omegaInv := 4, extendedOmega := 13,
    extendedOmegaInv := 4, gCoset := 2, gCosetInv := 4, quotientPolyDegree := 2,
    ifftDivisor := 13, extendedIfftDivisor := 13, tEvaluations := #[8],
    barycentricWeight := 13 }

def peVk : VerifyingKey (Fr 17) Nat :=
  { domain := peDom, fixedCommitments := #[], permutation := ⟨#[]⟩, cs := peCs,
    csDegree := 3, transcriptRepr := 7 }

def partiallyEvaluate_kats_ok : Bool :=
  match partiallyEvaluateIdentities (p := 17) (delta := 2) peVk #[] (#[#[]])
      (#[#[3, 4]]) (#[#[]]) (#[#[]]) (#[#[]]) ⟨#[]⟩ (x := 1) (xn := 1) (beta := 2)
      (gamma := 3) (theta := 4) (trashChallenge := 5) #[] with
  | .ok a => (a.toList.map (fun e => (e.1, ZMod.val e.2))) ==
      [((some 1 : Option Nat), 12), (none, 7)]
  | .error _ => false

#eval Midfall.Halo2.partiallyEvaluate_kats_ok   -- expect true


-- Regression for the phase-interleaving fix. Two advice columns in DIFFERENT
-- phases and two proofs. The Rust order is: read proof0.col0, read proof1.col0,
-- (squeeze phase-0 challenges), read proof0.col1, read proof1.col1. So with
-- proof bytes 1,2,3,4 the matrices must be proof0 = [1,3] and proof1 = [2,4].
-- The old code read 1,3 then 2,4 per proof, which gives proof0 = [1,3] by
-- accident for the FIRST proof but proof1 = [3,4] - so the second row is what
-- distinguishes the two orders.
def phaseInterleave_kats_ok : Bool :=
  let cs : ConstraintSystem (Fr 17) :=
    { ConstraintSystem.default (F := Fr 17) with
      numAdviceColumns := 2, adviceColumnPhase := #[⟨0⟩, ⟨1⟩], numChallenges := 1,
      challengePhase := #[⟨0⟩], numInstanceColumns := 0 };
  match EvaluationDomain.new (F := Fr 17) fc17 3 2 with
  | .error _ => false
  | .ok dom =>
      let vk : VerifyingKey (Fr 17) Nat :=
        { domain := dom, fixedCommitments := #[], permutation := ⟨#[]⟩, cs := cs,
          csDegree := 3, transcriptRepr := 7 };
      let proof : Bytes := ByteArray.mk (((natToBytesBE 1 48).data.toList ++
        (natToBytesBE 2 48).data.toList ++ (natToBytesBE 3 48).data.toList ++
        (natToBytesBE 4 48).data.toList).toArray);
      -- two proofs, each with no ordinary instance columns
      let inst : Array (Array (Array (Fr 17))) := #[(#[] : Array (Array (Fr 17))), #[]];
      match (parseTrace natG1Codec Features.solidity vk (#[#[], #[]]) inst)
            (Transcript.initFromBytes proof) with
      | .error _ => false
      | .ok (tr, _) =>
        (tr.adviceCommitments[0]?.map (fun r => r.toList)) == some [1, 3] &&
        (tr.adviceCommitments[1]?.map (fun r => r.toList)) == some [2, 4] &&
        tr.challenges.size == 1

-- Regression for the dropped-accumulator bug: with two proofs the result must
-- carry BOTH proofs' gate terms. Gate 1 is advice0*advice1 (tagged Some 1), gate
-- 2 is advice0+advice1 (untagged); proof 0 has evals [3,4] giving 12 and 7,
-- proof 1 has [5,6] giving 30 mod 17 = 13 and 11 mod 17 = 11.
def multiProofPartiallyEvaluate_kats_ok : Bool :=
  match partiallyEvaluateIdentities (p := 17) (delta := 2) peVk #[]
      (#[#[], #[]]) (#[#[3, 4], #[5, 6]]) (#[#[], #[]]) (#[#[], #[]])
      (#[#[], #[]]) ⟨#[]⟩
      (x := 1) (xn := 1) (beta := 2) (gamma := 3) (theta := 4)
      (trashChallenge := 5) #[] with
  | .ok a => (a.toList.map (fun e => (e.1, ZMod.val e.2))) ==
      [((some 1 : Option Nat), 12), (none, 7), ((some 1 : Option Nat), 13), (none, 11)]
  | .error _ => false

#eval Midfall.Halo2.phaseInterleave_kats_ok             -- expect true
#eval Midfall.Halo2.multiProofPartiallyEvaluate_kats_ok -- expect true


-- Rule R8 regression, found by external audit (docs/REVIEW.md R-32). With the
-- committed-instances feature OFF the Rust replaces the caller's committed
-- argument with one empty row per proof BEFORE its is_empty check
-- (verifier.rs:46-49). Every conjunct below was probed individually - the first
-- draft of this test passed on a conjunct that was vacuously true, which is the
-- R-20 lesson again.

def offFeatures : Features := { Features.solidity with committedInstances := false }

-- A key whose CS expects TWO instance columns, so a supplied committed column is
-- shape-legal only when the feature is on.
def traceVk2 : VerifyingKey (Fr 17) Nat :=
  match EvaluationDomain.new (F := Fr 17) fc17 3 2 with
  | .ok dom =>
      { domain := dom, fixedCommitments := #[], permutation := ⟨#[]⟩,
        cs := { traceCs with numInstanceColumns := 2 }, csDegree := 3,
        transcriptRepr := 7 }
  | .error _ => traceVk

def inst1 : Array (Array (Array (Fr 17))) := #[#[#[0, 1]]]
def instOne : Array (Array (Array (Fr 17))) := #[#[#[0]]]
def oneCommitted : Array (Array Nat) := #[#[7]]

/-- The observable transcript effect of a run: what was read, and how far the
    cursor got. `none` means the run failed. -/
def traceOutcome (feat : Features) (vk : VerifyingKey (Fr 17) Nat)
    (c : Array (Array Nat)) (inst : Array (Array (Array (Fr 17)))) :
    Option (Array (Array Nat) × Nat) :=
  match (parseTrace natG1Codec feat vk c inst)
        (Transcript.initFromBytes traceProof) with
  | .ok (tr, t) => some (tr.adviceCommitments, t.pos)
  | .error _ => none

def committedInstancesOff_kats_ok : Bool :=
  -- 1. feature off, empty committed: ACCEPTED. Before the fix this was
  --    InvalidInstances, because the is_empty check ran on the raw [].
  (traceOutcome offFeatures traceVk #[] inst1) ≠ none &&
  -- 2. feature off, a NON-empty committed argument is ignored entirely: the
  --    outcome is identical to the empty case, so nothing was absorbed.
  traceOutcome offFeatures traceVk oneCommitted inst1 ==
    traceOutcome offFeatures traceVk #[] inst1 &&
  -- 3. feature ON with an empty committed argument: still rejected, so the fix
  --    did not loosen the supported profile.
  traceOutcome Features.solidity traceVk #[] inst1 == none &&
  -- 4. the discriminator. With two instance columns expected, one committed plus
  --    one normal is legal ONLY with the feature on; with it off the committed
  --    row is replaced by an empty one and the shape check fails. Without this
  --    conjunct the fix could have been 'accept anything' and still looked green.
  (traceOutcome Features.solidity traceVk2 oneCommitted instOne) ≠ none &&
  traceOutcome offFeatures traceVk2 oneCommitted instOne == none
#eval Midfall.Halo2.committedInstancesOff_kats_ok  -- expect true
#eval Midfall.Halo2.committedInstancesOff_kats_ok  -- expect true

end Kats

#eval Midfall.Halo2.parseTrace_kats_ok          -- expect true
#eval Midfall.Halo2.parseTrace_short_kats_ok    -- expect true
#eval Midfall.Halo2.parseTrace_shape_kats_ok    -- expect true

/-! ## verify_algebraic_constraints and prepare (plonk/verifier.rs:238-696)

The algebraic half of the verifier: everything after the trace has been parsed.
It reads the quotient limbs and every evaluation opening, squeezes the opening
challenge `x`, partially evaluates the batched identities, builds the
linearization commitment, assembles the multi-open query vector and hands it to
`CS::multi_prepare`.

### Why these live in a `Verifier` namespace

Plan 9.2 - and the frozen `Midfall/Statements.lean` - already own the name
`Midfall.Halo2.prepare` for the *interface* entry point, whose arity is pinned by
the frozen file. The Rust `plonk::verifier::prepare` needs three pieces of
environment that the plan's signature does not carry (next block), so the faithful
port cannot share the name. The namespace mirrors the Rust module path instead:
`Midfall.Halo2.Verifier.prepare` *is* `plonk::verifier::prepare`, and
`Midfall.Halo2.prepare` stays the plan-9.2 shape.

### The environment the plan's signature omits (REPORTED, plan Section 12)

* `G1Codec G₁` - D-P6. Every commitment read and every commitment absorb needs
  it (`hashableG1`), and under D-P1 there is no concrete curve to read one from.
* `FieldConsts (Fr p)` - D-P1/R-3. `multi_prepare` needs `NUM_BITS` for
  `truncate`/`truncated_powers` (kzg/mod.rs:394,457,502,521), and the deployed
  profile has truncated-challenges ON, so this is not optional (R-22).
* `delta : Fr p` - R-3 extended. `permutation.rs` uses `F::DELTA`, which
  `FieldConsts` does not carry, so `partiallyEvaluateIdentities` takes it as an
  explicit parameter and every caller has to thread it.

`Pcs` is a parameter too, not a local: the Rust calls `CS::multi_prepare` through
the trait (:651), so rule R9 makes the record a parameter and `Pcs.kzg` the
instantiation the caller supplies.

### Why nothing here is exercised end to end

There is no model of `AdmissiblePairing` anywhere in the tree: design.md D-P1
consequence 3 asks for "at least one *constructed* model", and
`Assumptions/Pairing.lean` currently supplies only the moduli and the
`pBaseKats_ok` check. So `Pcs`, `DualMSM`, `multiPrepare` and therefore
`verifyAlgebraicConstraints` and `Verifier.prepare` are type-correct but not yet
runnable - no fixture can be fed to them. The KATs below therefore target the two
pure sub-steps, `readFixedEvals` and `collectQueries`, which is exactly where the
R-14 shift and the query-order hazards live. Closing this is an `Assumptions/`
item, not an `Exec/Verifier` one.

### Skipped, with evidence -/

/-! rust: proofs/src/plonk/verifier.rs:292-300, 305-324, 359-363, 382-390,
    402-407, 441-473, 494-533, 544-574 - the `solidity-verifier-trace` blocks.
    Same evidence as Exec/Permutation, Exec/Logup and Exec/Trash: the feature is
    proofs/Cargo.toml:117, it is not one of the four flags Exec/Features.lean
    carries under rule R8, and every block is a `solidity_trace::record_*` call
    over a value the surrounding code already has. Note :441-473 recomputes
    `blinding_factors` and `l_i_range` purely to log them, and :450 adds an
    `(xn - 1).invert().unwrap()` that exists only inside that logging block, so
    R-2's third face is NOT reachable on the real path. Dropping the blocks changes
    no value, no error class and no transcript byte. -/

namespace Verifier

/-- rust: proofs/src/plonk/verifier.rs:410 (`Vec::insert`). INSERT, not replace:
    `Vec::insert(i, x)` shifts the tail right and GROWS the vector, and it panics
    when `i > len` (it allows `i == len`, i.e. append). Exec/Kzg/Utils.lean has
    `listReplaceAt`; this is the other operation, and the difference is the whole
    of docs/REVIEW.md R-14. -/
def listInsertAt {α : Type} (xs : List α) (i : Nat) (v : α) (site : String) :
    Except Fault (List α) :=
  if i > xs.length then
    .error (Fault.panic site)
  else
    .ok (xs.take i ++ [v] ++ xs.drop i)

/-- rust: `i32::abs` at proofs/src/plonk/verifier.rs:348 (`min_rotation.abs()`).
    docs/REVIEW.md R-5 named this site: `i32::MIN.abs()` overflows, and because
    the check is inside `abs` itself rather than in an arithmetic operator it
    fires in the release profile too (BASELINE.md), so it is a `Fault.panic` and
    not a wrap. The port's `Rotation.value` can hold any `Int`, so the guard is
    genuinely reachable here and is kept rather than argued away. -/
def i32Abs (x : Int) (site : String) : Except Fault Int :=
  if x = -2147483648 then .error (Fault.panic site)
  else if x < 0 then .ok (-x) else .ok x

/-- rust: proofs/src/plonk/verifier.rs:395-412, the fixed-evaluation read and the
    simple-selector back-fill. Split out of `verifyAlgebraicConstraints` so the
    R-14 shift is testable without a whole proof.

    THE R-14 BUG, PORTED AS WRITTEN. The Rust reads
    `num_fixed_columns - num_simple_selectors` evaluations and then walks
    `fixed_queries` - which counts distinct (column, rotation) PAIRS, not columns
    - inserting `F::ONE` at the query index. Two consequences, both real and both
    kept:

    1. `Vec::insert` SHIFTS. Every insert moves the already-present elements
       right and grows the vector past the number of evaluations that were read,
       so a later `fixed_evals[query_index]` (:641) reads a shifted slot. The
       port must use `listInsertAt`, not `listReplaceAt`, and the query assembly
       must index the POST-INSERT position - which is exactly what :633's
       `.enumerate()` over ALL fixed queries produces.
    2. `Vec::insert` panics when the index exceeds the length. R-14: "a real
       reachable panic site for a circuit with a fixed column queried at two
       rotations". Kept as `Fault.panic` at :410.

    The `num_fixed_columns - num_simple_selectors` at :400 is a `usize`
    subtraction. In the reference release profile (BASELINE.md) it WRAPS when the
    constraint system claims more simple selectors than fixed columns, and
    `read_n` of a wrapped count is a guaranteed `UnexpectedEof` - no proof buffer
    is 2^64 scalars long - so the port reproduces the observable outcome directly
    instead of materialising the number (rule R5, and the same treatment
    Exec/Permutation gives the `cs_degree - 2` wrap). -/
def readFixedEvals {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p)) :
    TranscriptM (Array (Fr p)) := do
  let nRead := cs.numFixedColumns
  let nSimple := cs.numSimpleSelectors
  -- :400, the wrapped usize subtraction described above
  if nSimple > nRead then
    throw (Fault.error (Error.transcript IoErrorKind.unexpectedEof))
  let read ← tmReadN (hashableFr (p := p)) (nRead - nSimple)
  let steps := List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList
  let out ← steps.foldlM (init := (read.toList : List (Fr p))) fun acc step => do
    if cs.hasSimpleSelectorCol step.2.1.index then
      StateT.lift (listInsertAt acc step.1 1 "proofs/src/plonk/verifier.rs:410")
    else
      pure acc
  pure out.toArray

/-- rust: proofs/src/plonk/verifier.rs:576-647 (the `queries` vector).

    THE ORDER IS LOAD-BEARING. Six `.zip` calls nest left-associatively, so a
    per-proof element is `((((((committed, instance_evals), advice_coms),
    advice_evals), permutation), lookups), trash)` and the whole flat_map
    truncates to the SHORTEST of the seven inputs (rule R3) - a proof that
    produced fewer per-proof vectors silently drops whole proofs from the batch
    rather than failing. Inside each proof the chains run advice, instance
    (committed columns only), permutation, lookups, trash; AFTER the flat_map come
    the fixed queries (non-simple-selector only, enumerated over ALL fixed queries
    so the index is the post-insert position - see R-14), then the common sigma
    openings, then the linearization polynomial last. `multi_prepare` groups by
    commitment and point set in this order, so a reordering changes x1..x4 and
    with them the whole Fiat-Shamir binding.

    Panic sites, all of them Rust slice indexes kept as `Fault.panic` (rule R4):
    :605 advice commitment by column index, :606 advice eval by query index,
    :616 committed instance by column index, :617 instance eval by query index,
    :640 fixed commitment by column index, :641 fixed eval by query index. The
    last is where R-14 bites: after enough inserts the vector is longer than the
    read, and a shifted index reads the wrong evaluation. -/
def collectQueries {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (committedInstances adviceCommitments : Array (Array G₁))
    (instanceEvals adviceEvals : Array (Array (Fr p)))
    (permutationsEvaluated : Array (Permutation.Evaluated (Fr p) G₁))
    (lookupsEvaluated : Array (Array (Logup.Evaluated (Fr p) G₁)))
    (trashcansEvaluated : Array (Array (Trash.Evaluated (Fr p) G₁)))
    (fixedEvals : Array (Fr p)) (permutationsCommon : Permutation.CommonEvaluated (Fr p))
    (linCom : VerifierQuery (Fr p) G₁) :
    Except Fault (Array (VerifierQuery (Fr p) G₁)) := do
  -- :580-587 the six left-nested zips
  let zipped := List.zip (List.zip (List.zip (List.zip (List.zip
      (List.zip committedInstances.toList instanceEvals.toList)
      adviceCommitments.toList) adviceEvals.toList)
      permutationsEvaluated.toList) lookupsEvaluated.toList) trashcansEvaluated.toList
  -- :588-628 the flat_map body, per proof
  let perProof ← zipped.mapM fun e => do
    let ci := e.1.1.1.1.1.1
    let ie := e.1.1.1.1.1.2
    let ac := e.1.1.1.1.2
    let ae := e.1.1.1.2
    let pe := e.1.1.2
    let le := e.1.2
    let te := e.2
    -- :600-609 advice queries, enumerated so the eval index is the query index
    let adv ← (List.zip (List.range vk.cs.adviceQueries.size)
        vk.cs.adviceQueries.toList).mapM fun q => do
      let com ← Permutation.atIndex ac q.2.1.index "proofs/src/plonk/verifier.rs:605"
      let ev ← Permutation.atIndex ae q.1 "proofs/src/plonk/verifier.rs:606"
      pure [VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
        (CommitmentLabel.advice q.2.1.index) com ev]
    -- :610-623 instance queries, filter_map keeps only the committed columns
    let inst ← (List.zip (List.range vk.cs.instanceQueries.size)
        vk.cs.instanceQueries.toList).mapM fun q => do
      if q.2.1.index < nbCommitted then
        let com ← Permutation.atIndex ci q.2.1.index "proofs/src/plonk/verifier.rs:616"
        let ev ← Permutation.atIndex ie q.1 "proofs/src/plonk/verifier.rs:617"
        pure [VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
          (CommitmentLabel.instance_ q.2.1.index) com ev]
      else
        pure []
    -- :624 permutation.queries(vk, x). blinding_factors is computed INSIDE the
    -- Rust fn (:150), so the i32::MAX panic at circuit.rs:2510 is observed here,
    -- after this proof's advice and instance queries have been built.
    let bf ← vk.cs.blindingFactors
    let perm ← pe.queries (p := p) vk.domain bf x
    -- :625-626 lookups then trashcans, flat over the per-proof vectors
    let lk := le.flatMap (fun lq => lq.queries (p := p) vk.domain x)
    let tr := te.flatMap (fun tq => tq.queries (p := p) x)
    pure (adv.flatten ++ inst.flatten ++ perm.toList ++ lk.toList ++ tr.toList)
  -- :629-644 fixed queries, AFTER the per-proof block, filtered to non-simple
  let fixed ← ((List.zip (List.range vk.cs.fixedQueries.size)
      vk.cs.fixedQueries.toList).filter
      fun q => !vk.cs.hasSimpleSelectorCol q.2.1.index).mapM fun q => do
    let com ← Permutation.atIndex vk.fixedCommitments q.2.1.index
      "proofs/src/plonk/verifier.rs:640"
    let ev ← Permutation.atIndex fixedEvals q.1 "proofs/src/plonk/verifier.rs:641"
    pure (VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
      (CommitmentLabel.fixed q.2.1.index) com ev)
  -- :645-646 the sigma openings, then the linearization polynomial, last
  let common := permutationsCommon.queries (p := p) vk.permutation x
  pure ((perProof.flatten ++ fixed ++ common.toList ++ [linCom]).toArray)

/-- rust: proofs/src/plonk/verifier.rs:238-652 (verify_algebraic_constraints).

    The Rust is generic in `CS: PolynomialCommitmentScheme` and calls
    `CS::multi_prepare` through the trait (:651), so under rule R9 the port takes
    the `Pcs` record as a parameter and `Pcs.kzg` is the instantiation the caller
    supplies - which is also why `FieldConsts` and the fewer-point-sets runtime
    switch are NOT parameters here: the Rust does not see them either, they are
    baked into the record by `Verifier.prepare`. `feat` is needed separately for
    the two `#[cfg]` branches at :260 and :287 (rule R8), and `delta` because
    `partially_evaluate_identities` takes it (R-3 extended).

    The error at :651 is COLLAPSED: `.map_err(|_| Error::Opening)`. docs/REVIEW.md
    R-8 records that this collapse is local to this call site and must not be
    "improved": a short proof fails as `Opening` here but as
    `Transcript(UnexpectedEof)` at :291, and the two-phase `prepare` +
    `Guard::verify` path that Exec/Native composes does not collapse at all. Only
    the `Result::Err` arm is mapped - a Rust panic is not a `Result`, so
    `Fault.panic` propagates untouched, which is also what rule R4 requires. -/
def verifyAlgebraicConstraints {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁)) (instances : Array (Array (Array (Fr p)))) :
    TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) := do
  -- :260-261 rule R8: without the committed-instances feature the Rust builds one
  -- EMPTY row per proof, so nb_committed_instances is 0 and every instance column
  -- is reconstructed by inner product rather than read from the transcript.
  let committed := if feat.committedInstances then committedInstances
                   else arrayReplicate instances.size (#[] : Array G₁)
  -- :263-265. NOTE: this is the ONLY shape check on this path. The package brief
  -- said "is_empty and uniform row length, two InvalidInstances exits", but the
  -- baseline source has ONE check here (:263-265); the uniform-row check is
  -- :54-58 and the column-count check is :61-65, both inside parse_trace. Adding
  -- the second check here would be an improvement, which rule R1 forbids; the
  -- discrepancy is reported rather than patched.
  if committed.isEmpty then
    throw (Fault.error Error.invalidInstances)
  -- :267-268
  let nbCommitted := (committed[0]?.map (fun r => r.size)).getD 0
  let numProofs := instances.size
  -- :270-281 destructure the trace
  let adviceCommitments := trace.adviceCommitments
  let lookups := trace.lookups
  let trashcans := trace.trashcans
  let permutations := trace.permutations
  let challenges := trace.challenges
  let beta := trace.beta
  let gamma := trace.gamma
  let theta := trace.theta
  let trashChallenge := trace.trashChallenge
  let y := trace.y
  -- :283-291 the quotient limbs, one commitment per limb; rule R8, the
  -- single-h-commitment feature pins the count to 1 instead.
  let nbQuotientComs :=
    if feat.outerSingleHCommitment then 1 else vk.domain.getQuotientPolyDegree
  let quotientLimbComs ← tmReadN (hashableG1 g1) nbQuotientComs
  -- :302-304 the opening challenge
  let x ← tmSqueezeChallenge
  -- :326-327. `vk.n() - 1` is a usize subtraction, but n = 1 << k with k >= 0 so
  -- n >= 1 always and it cannot underflow (domain.rs:42).
  let splittingFactor := powVartime x (vk.n - 1)
  let xn := splittingFactor * x
  -- :329-377 the instance evaluations.
  -- :330-339 the (min,max) fold. It is if / ELSE IF, so a rotation that equals
  -- neither bound updates nothing, and the seed is (0,0): an all-positive query
  -- set therefore gets min = 0, not the smallest positive rotation. Kept.
  let rotBounds := vk.cs.instanceQueries.toList.foldl (init := ((0 : Int), (0 : Int)))
    fun st q =>
      let r := q.2.int
      if r < st.1 then (r, st.2) else if r > st.2 then (st.1, r) else st
  let minRot := rotBounds.1
  let maxRot := rotBounds.2
  -- :340-344 max_by(Ord::cmp).unwrap_or_default() over the FLAT map of column
  -- lengths. For usize, max_by and a `foldl max` agree on the value, and the
  -- default of an empty iterator is 0.
  let maxInstanceLen := (instances.toList.flatMap (fun row =>
      (row.toList.map (fun col => col.size)))).foldl (init := 0) max
  -- :345-349 l_i_range over `-max_rotation .. max_instance_len as i32 +
  -- |min_rotation|`. The Rust range is EXCLUSIVE at the top, both bounds are i32,
  -- the `as i32` widening truncates (R-9) and `abs` aborts at i32::MIN (R-5). An
  -- empty range (end <= start) yields an empty vector, which is what makes the
  -- slice check below reachable rather than merely theoretical.
  let absMin ← StateT.lift (i32Abs minRot "proofs/src/plonk/verifier.rs:348")
  let windowStart := Permutation.negI32 maxRot
  let windowStop := Permutation.wrapI32 (Permutation.asI32 maxInstanceLen + absMin)
  let rotations :=
    if windowStop > windowStart then
      (List.range ((windowStop - windowStart).toNat)).map (fun i => windowStart + (i : Int))
    else
      []
  let lIS := vk.domain.lIRange x xn rotations
  -- :350-377 per proof, per instance query, in order: the transcript reads
  -- interleave with the inner products exactly as the Rust map does.
  let oneInstanceQuery (row : Array (Array (Fr p))) (q : Column × Rotation) :
      TranscriptM (Fr p) := do
    if q.1.index < nbCommitted then
      -- :358 transcript.read()
      tmRead (hashableFr (p := p))
    else
      -- :366 instances[column.index() - nb_committed_instances] is a slice index.
      -- PANIC SITE (rule R4), and reachable: verify_algebraic_constraints does NOT
      -- re-check the column count (that check is parse_trace's, and it uses `zip`,
      -- so a committed/inst length mismatch leaves the extra rows unchecked).
      let colIdx := q.1.index - nbCommitted
      match row[colIdx]? with
      | none => throw (Fault.panic "proofs/src/plonk/verifier.rs:366")
      | some col =>
        -- :367 offset = (max_rotation - rotation.0) as usize. Non-negative
        -- because the fold's max is >= every rotation, so the cast is lossless.
        let offset := (maxRot - q.2.int).toNat
        -- :370 &l_i_s[offset..offset + len] PANICS when it overruns the window -
        -- docs/REVIEW.md R-5's second named site. Reported at the slice line,
        -- which is where Rust aborts, before compute_inner_product's own length
        -- assert at arithmetic.rs:83 could fire.
        let slice := (lIS.toList.drop offset).take col.size
        unless slice.length == col.size do
          throw (Fault.panic "proofs/src/plonk/verifier.rs:370")
        StateT.lift (computeInnerProduct col slice.toArray)
  let instanceEvalsList ← instances.toList.mapM (fun row =>
      vk.cs.instanceQueries.toList.mapM (oneInstanceQuery row))
  let instanceEvals := (instanceEvalsList.map (fun l => l.toArray)).toArray
  -- :379-393 advice evaluations, one block of advice_queries.len() per proof.
  let adviceEvalsList ← (List.range numProofs).mapM (fun _ =>
      tmReadN (hashableFr (p := p)) vk.cs.adviceQueries.size)
  let adviceEvals := adviceEvalsList.toArray
  -- :395-412 fixed evaluations, with the R-14 insert back-fill.
  let fixedEvals ← readFixedEvals vk.cs
  -- :414 the common permutation evaluations, read once for the VK
  let permutationsCommon ← Permutation.VerifyingKey.evaluate (p := p) vk.permutation
  -- :416-439 the per-proof evaluated vectors, in the Rust's order
  let permutationsEvaluatedList ← permutations.toList.mapM (fun pc =>
      Permutation.Committed.evaluate (p := p) pc)
  let permutationsEvaluated := permutationsEvaluatedList.toArray
  let lookupsEvaluatedList ← lookups.toList.mapM (fun row =>
      row.toList.mapM (fun l => Logup.Committed.evaluate (p := p) l))
  let lookupsEvaluated := (lookupsEvaluatedList.map (fun r => r.toArray)).toArray
  let trashcansEvaluatedList ← trashcans.toList.mapM (fun row =>
      row.toList.mapM (fun t => Trash.Committed.evaluate (p := p) t))
  let trashcansEvaluated := (trashcansEvaluatedList.map (fun r => r.toArray)).toArray
  -- :475-493 partially evaluate the batched identities
  let expressions ← StateT.lift (partiallyEvaluateIdentities (p := p) (delta := delta)
    (vk := vk) (fixedEvals := fixedEvals) (instanceEvals := instanceEvals)
    (adviceEvals := adviceEvals)
    (permutationEvals := permutationsEvaluated.map (fun e => e.sets))
    (lookupEvals := lookupsEvaluated.map (fun row => row.map (fun e => e.evaluated)))
    (trashcanEvals := trashcansEvaluated.map (fun row => row.map (fun e => e.evaluated)))
    (permutationsCommon := permutationsCommon) (x := x) (xn := xn) (beta := beta)
    (gamma := gamma) (theta := theta) (trashChallenge := trashChallenge)
    (challenges := challenges))
  -- :535-543 the linearization commitment query
  let linCom ← StateT.lift (computeLinearizationCommitment (F := Fr p) (G₁ := G₁)
    expressions vk x y xn splittingFactor quotientLimbComs)
  -- :575-647 the multi-open query vector
  let queries ← StateT.lift (collectQueries (p := p) nbCommitted vk x
    (committedInstances := committed) (adviceCommitments := adviceCommitments)
    (instanceEvals := instanceEvals) (adviceEvals := adviceEvals)
    (permutationsEvaluated := permutationsEvaluated)
    (lookupsEvaluated := lookupsEvaluated) (trashcansEvaluated := trashcansEvaluated)
    (fixedEvals := fixedEvals) (permutationsCommon := permutationsCommon)
    (linCom := linCom))
  -- :649-651 CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
  let t ← StateT.get
  match (pcs.multiPrepare queries).run t with
  | .ok (guard, t2) =>
      StateT.set t2
      pure guard
  | .error (Fault.panic site) => throw (Fault.panic site)
  | .error (Fault.error _) => throw (Fault.error Error.opening)

/-- rust: proofs/src/plonk/verifier.rs:659-696 (prepare). Thin by design:
    parse_trace, then verify_algebraic_constraints, with the same committed and
    instance arguments threaded into both (:682-684 and :691-693). The
    trailing-bytes check the doc comment promises is the caller's -
    `Transcript::assert_empty` - and Exec/Native does it there, which is where the
    two-phase Rust composition does it (test.rs:377). -/
def prepare {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (committedInstances : Array (Array G₁))
    (instances : Array (Array (Array (Fr p)))) :
    TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) := do
  let trace ← parseTrace g1 feat vk committedInstances instances
  verifyAlgebraicConstraints (p := p) g1 delta feat pcs vk trace
    committedInstances instances

end Verifier

/-! ### Known-answer checks for the algebraic half

    Same style as the schedule KATs above: hand-computed booleans over `Fr 17`
    with `G₁ := Nat`, so no curve is needed. The two the package brief asks for
    are here: the R-14 INSERT-shift check on `fixed_evals`, and the query-vector
    order check that pins the first and last `CommitmentLabel`. -/

section AlgebraicKats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A fixed column, as the query tables want it. -/
def vCol (i : Nat) (t : Any) : Column := { index := i, columnType := t }

/-- R-14: the INSERT-shift KAT, two-element example.

    `num_fixed_columns = 3`, one simple selector on column 0, so the transcript
    carries only `3 - 1 = 2` evaluations - here `[7, 11]`. The fixed queries are
    `[(col1, cur), (col0, cur), (col2, cur)]`, i.e. the simple selector is the
    SECOND query. `Vec::insert(1, ONE)` shifts `11` right, so the vector becomes
    `[7, 1, 11]`: length 3, and the value read second now sits at index 2. A
    `listReplaceAt` port would give `[7, 1]` of length 2, and every later
    `fixed_evals[query_index]` would read the wrong slot. Hand-computed over
    `Fr 17`. -/
def r14Insert_kats_ok : Bool :=
  let cs : ConstraintSystem (Fr 17) :=
    { ConstraintSystem.default (F := Fr 17) with
      numFixedColumns := 3,
      selectorFlags := #[{ isSimple := true, colIdx := some 0 }],
      fixedQueries := #[(vCol 1 Any.fixed, Rotation.cur),
                         (vCol 0 Any.fixed, Rotation.cur),
                         (vCol 2 Any.fixed, Rotation.cur)] }
  let buf := natToBytesLE 7 32 ++ natToBytesLE 11 32
  match (Verifier.readFixedEvals (p := 17) cs).run (Transcript.initFromBytes buf) with
  | .ok (ev, t) =>
      (ev.map ZMod.val).toList == [7, 1, 11] && ev.size == 3 && t.pos == 64
  | .error _ => false

/-- R-14's panic half: `Vec::insert` aborts when the index exceeds the length.
    Column 0 (the simple selector) is queried at cur AND next, and only one
    evaluation is read, so the second insert is asked for index 2 of a length-1
    vector. This is exactly the "fixed column queried at two rotations" case
    docs/REVIEW.md R-14 predicts. -/
def r14Panic_kats_ok : Bool :=
  let cs : ConstraintSystem (Fr 17) :=
    { ConstraintSystem.default (F := Fr 17) with
      numFixedColumns := 2,
      selectorFlags := #[{ isSimple := true, colIdx := some 0 }],
      fixedQueries := #[(vCol 1 Any.fixed, Rotation.cur),
                         (vCol 1 Any.fixed, Rotation.next),
                         (vCol 0 Any.fixed, Rotation.cur)] }
  match (Verifier.readFixedEvals (p := 17) cs).run
      (Transcript.initFromBytes (natToBytesLE 7 32)) with
  | .error (Fault.panic "proofs/src/plonk/verifier.rs:410") => true
  | _ => false

/-- The wrapped `usize` subtraction at :400: a constraint system claiming more
    simple selectors than fixed columns makes Rust's `num_fixed_columns -
    num_simple_selectors` wrap and `read_n` hit EOF. The port reports the same
    observable class without materialising 2^64. -/
def r14Wrap_kats_ok : Bool :=
  let cs : ConstraintSystem (Fr 17) :=
    { ConstraintSystem.default (F := Fr 17) with
      numFixedColumns := 1,
      selectorFlags := #[{ isSimple := true, colIdx := some 0 },
                          { isSimple := true, colIdx := some 0 }] }
  match (Verifier.readFixedEvals (p := 17) cs).run (Transcript.initFromBytes Bytes.empty) with
  | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => true
  | _ => false

/-- `listInsertAt` itself, pinned against `listReplaceAt` semantics: insert at 1
    of `[7, 11]` grows to `[7, 1, 11]`; insert at the length appends; insert past
    it is the :410 panic. -/
def listInsertAt_kats_ok : Bool :=
  (match Verifier.listInsertAt ([7, 11] : List Nat) 1 1 "x" with
   | .ok l => l == [7, 1, 11]
   | .error _ => false) &&
  (match Verifier.listInsertAt ([7] : List Nat) 1 1 "x" with
   | .ok l => l == [7, 1]
   | .error _ => false) &&
  (match Verifier.listInsertAt ([] : List Nat) 0 1 "x" with
   | .ok l => l == [1]
   | .error _ => false) &&
  (match Verifier.listInsertAt ([] : List Nat) 1 1 "x" with
   | .error (Fault.panic "x") => true
   | _ => false)

/-- `i32::abs` at :348 (R-5): `i32::MIN` aborts, everything else is the plain
    absolute value. -/
def i32Abs_kats_ok : Bool :=
  (match Verifier.i32Abs (-2147483648) "site" with
   | .error (Fault.panic "site") => true
   | _ => false) &&
  (match Verifier.i32Abs (-5 : Int) "site" with
   | .ok v => v == 5
   | .error _ => false) &&
  (match Verifier.i32Abs (7 : Int) "site" with
   | .ok v => v == 7
   | .error _ => false)

/-- The smallest constraint system `collectQueries` can run on: one advice query,
    one COMMITTED instance query (so it survives the filter), one non-simple fixed
    query, no permutation columns, no lookups, no trashcans. Over `Fr 17` with the
    size-4 domain (`omega = 13`) and `x = 5`.

    Expected assembly, read off the Rust chain order:
      1. `Advice 0` at `x`, eval `advice_evals[0] = 8`, commitment 60
      2. `Instance 0` at `x`, eval `instance_evals[0] = 7`, commitment 50
         (column 0 < nbCommitted = 1, so it is NOT filtered)
      3. nothing from the permutation (empty sets), lookups or trashcans
      4. `Fixed 0` at `x`, eval `fixed_evals[0] = 9`, commitment 70 - AFTER the
         per-proof block, and indexed into the POST-INSERT fixed vector
      5. nothing from the common sigma openings (no commitments)
      6. the linearization query, LAST
    So: length 4, first label `Advice 0`, last label
    `Custom "linearization_poly"`. -/
def cqCs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default (F := Fr 17) with
    numAdviceColumns := 1, adviceColumnPhase := #[⟨0⟩],
    numInstanceColumns := 1, numFixedColumns := 1,
    adviceQueries := #[(vCol 0 (Any.adviceFirst), Rotation.cur)],
    instanceQueries := #[(vCol 0 Any.instance, Rotation.cur)],
    fixedQueries := #[(vCol 0 Any.fixed, Rotation.cur)] }

def cqVk : VerifyingKey (Fr 17) Nat :=
  { domain := peDom, fixedCommitments := #[70], permutation := ⟨#[]⟩,
    cs := cqCs, csDegree := 3, transcriptRepr := 7 }

def collectQueries_kats_ok : Bool :=
  let lin : VerifierQuery (Fr 17) Nat :=
    VerifierQuery.new 5 (CommitmentLabel.custom "linearization_poly") 99 3
  match Verifier.collectQueries (p := 17) 1 cqVk 5
      (#[#[50]] : Array (Array Nat)) (#[#[60]] : Array (Array Nat))
      (#[#[7]] : Array (Array (Fr 17))) (#[#[8]] : Array (Array (Fr 17)))
      (#[{ coms := ⟨#[]⟩, sets := #[] }] : Array (Permutation.Evaluated (Fr 17) Nat))
      (#[#[]] : Array (Array (Logup.Evaluated (Fr 17) Nat)))
      (#[#[]] : Array (Array (Trash.Evaluated (Fr 17) Nat)))
      (#[9] : Array (Fr 17)) ⟨#[]⟩ lin with
  | .error _ => false
  | .ok qs =>
      qs.size == 4 &&
      (qs.map (fun q => q.commitmentLabel)).toList ==
        [CommitmentLabel.advice 0, CommitmentLabel.instance_ 0,
         CommitmentLabel.fixed 0, CommitmentLabel.custom "linearization_poly"] &&
      (qs.map (fun q => ZMod.val q.eval)).toList == [8, 7, 9, 3] &&
      (qs.map (fun q => ZMod.val q.point)).toList == [5, 5, 5, 5] &&
      (qs.map (fun q => match q.commitment with
        | .onePiece c => c
        | .linear _ _ _ => 0)).toList == [60, 50, 70, 99]

/-- The committed-instance filter and the R-14 index coupling in one check.
    `nbCommitted = 0` drops the instance query from the batch (there is no
    commitment to open it against). The fixed table is
    `[(col0, cur), (col1, cur), (col1, next)]` with column 0 a simple selector, so
    the filter keeps query INDICES 1 and 2 - the post-insert positions - and the
    evaluations they must read are `fixed_evals[1] = 9` and `fixed_evals[2] = 10`.
    A replace-semantics port would read `[0] = 1` and `[1] = 9` instead. The
    `next` rotation opens at `omega * x = 5 * 13 = 65 = 14` in `Fr 17`. -/
def collectQueriesOrder_kats_ok : Bool :=
  let cs : ConstraintSystem (Fr 17) :=
    { cqCs with
      numFixedColumns := 2,
      selectorFlags := #[{ isSimple := true, colIdx := some 0 }],
      fixedQueries := #[(vCol 0 Any.fixed, Rotation.cur),
                         (vCol 1 Any.fixed, Rotation.cur),
                         (vCol 1 Any.fixed, Rotation.next)] }
  let vk : VerifyingKey (Fr 17) Nat :=
    { cqVk with cs := cs, fixedCommitments := #[70, 71] }
  let lin : VerifierQuery (Fr 17) Nat :=
    VerifierQuery.new 5 (CommitmentLabel.custom "linearization_poly") 99 3
  match Verifier.collectQueries (p := 17) 0 vk 5
      (#[#[]] : Array (Array Nat)) (#[#[60]] : Array (Array Nat))
      (#[#[]] : Array (Array (Fr 17))) (#[#[8]] : Array (Array (Fr 17)))
      (#[{ coms := ⟨#[]⟩, sets := #[] }] : Array (Permutation.Evaluated (Fr 17) Nat))
      (#[#[]] : Array (Array (Logup.Evaluated (Fr 17) Nat)))
      (#[#[]] : Array (Array (Trash.Evaluated (Fr 17) Nat)))
      (#[1, 9, 10] : Array (Fr 17)) ⟨#[]⟩ lin with
  | .error _ => false
  | .ok qs =>
      (qs.map (fun q => q.commitmentLabel)).toList ==
        [CommitmentLabel.advice 0, CommitmentLabel.fixed 1,
         CommitmentLabel.fixed 1, CommitmentLabel.custom "linearization_poly"] &&
      (qs.map (fun q => ZMod.val q.eval)).toList == [8, 9, 10, 3] &&
      (qs.map (fun q => ZMod.val q.point)).toList == [5, 5, 14, 5]

/-- The :641 panic: one proof, one advice query, but the advice COMMITMENTS vector
    is empty, so `advice_commitments[column.index()]" is out of bounds. Reported at
    the advice line, not the fixed one, because the advice chain runs first. -/
def collectQueriesPanic_kats_ok : Bool :=
  let lin : VerifierQuery (Fr 17) Nat :=
    VerifierQuery.new 5 (CommitmentLabel.custom "linearization_poly") 99 3
  match Verifier.collectQueries (p := 17) 0 cqVk 5
      (#[#[]] : Array (Array Nat)) (#[#[]] : Array (Array Nat))
      (#[#[]] : Array (Array (Fr 17))) (#[#[8]] : Array (Array (Fr 17)))
      (#[{ coms := ⟨#[]⟩, sets := #[] }] : Array (Permutation.Evaluated (Fr 17) Nat))
      (#[#[]] : Array (Array (Logup.Evaluated (Fr 17) Nat)))
      (#[#[]] : Array (Array (Trash.Evaluated (Fr 17) Nat)))
      (#[9] : Array (Fr 17)) ⟨#[]⟩ lin with
  | .error (Fault.panic "proofs/src/plonk/verifier.rs:605") => true
  | _ => false

/-- The seven-way zip truncates to the shortest input (rule R3): with two proofs'
    worth of advice commitments but only one proof's worth of lookups, the second
    proof contributes NOTHING at all - no error, no partial row. -/
def collectQueriesZip_kats_ok : Bool :=
  let lin : VerifierQuery (Fr 17) Nat :=
    VerifierQuery.new 5 (CommitmentLabel.custom "linearization_poly") 99 3
  match Verifier.collectQueries (p := 17) 0 cqVk 5
      (#[#[50], #[51]] : Array (Array Nat)) (#[#[60], #[61]] : Array (Array Nat))
      (#[#[7], #[7]] : Array (Array (Fr 17))) (#[#[8], #[8]] : Array (Array (Fr 17)))
      (#[{ coms := ⟨#[]⟩, sets := #[] },
         { coms := ⟨#[]⟩, sets := #[] }] : Array (Permutation.Evaluated (Fr 17) Nat))
      (#[#[]] : Array (Array (Logup.Evaluated (Fr 17) Nat)))
      (#[#[]] : Array (Array (Trash.Evaluated (Fr 17) Nat)))
      (#[9] : Array (Fr 17)) ⟨#[]⟩ lin with
  | .error _ => false
  | .ok qs =>
      -- one advice query per proof would give 2; the zip keeps only the first
      (qs.map (fun q => q.commitmentLabel)).toList ==
        [CommitmentLabel.advice 0, CommitmentLabel.fixed 0,
         CommitmentLabel.custom "linearization_poly"]

end AlgebraicKats

#eval Midfall.Halo2.r14Insert_kats_ok                -- expect true
#eval Midfall.Halo2.r14Panic_kats_ok                 -- expect true
#eval Midfall.Halo2.r14Wrap_kats_ok                  -- expect true
#eval Midfall.Halo2.listInsertAt_kats_ok             -- expect true
#eval Midfall.Halo2.i32Abs_kats_ok                   -- expect true
#eval Midfall.Halo2.collectQueries_kats_ok           -- expect true
#eval Midfall.Halo2.collectQueriesOrder_kats_ok      -- expect true
#eval Midfall.Halo2.collectQueriesPanic_kats_ok      -- expect true
#eval Midfall.Halo2.collectQueriesZip_kats_ok        -- expect true

end Midfall.Halo2

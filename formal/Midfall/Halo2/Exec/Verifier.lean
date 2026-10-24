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

/-- rust: plonk/verifier.rs:24-232 (parse_trace). -/
def parseTrace (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁)
    (committed : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) :
    TranscriptM (VerifierTrace (Fr p) G₁) := do
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
  -- verifier.rs:105-146: the phase loop. Advice commitments first, then the
  -- challenges of that phase - and the challenge loop is INSIDE the phase loop
  -- but OUTSIDE the per-proof loop, so all proofs' commitments for a phase are
  -- read before that phase's challenge is squeezed.
  let order := adviceReadOrder vk.cs;
  let nAdv := order.length;
  let adviceCommitments ← (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let reads ← tmReadN (hashableG1 g1) nAdv
      -- scatter the read sequence back into column order. A hole here would mean
      -- adviceReadOrder and the phase loop disagreed, i.e. a column whose phase is
      -- outside cs.phases() - impossible for a Rust-built CS, so it is a panic site
      -- rather than a silent default (the Rust would have left Commitment::default()
      -- in the slot, which is a DIFFERENT point and would change the transcript).
      let base : List (Option G₁) := List.replicate vk.cs.numAdviceColumns none;
      let placed := (List.zip order reads.toList).foldl
        (init := base) fun acc e =>
          acc.take e.1 ++ [some e.2] ++ acc.drop (e.1 + 1)
      match placed.mapM (fun x => x) with
      | none => throw (Fault.panic "proofs/src/plonk/verifier.rs:118")
      | some cols => pure (acc.push cols.toArray)
  let challenges ← (List.range vk.cs.numChallenges).foldlM
    (init := #[]) fun acc _ => do
      let c ← tmSqueezeChallenge
      pure (acc.push c)

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
  let rows ← zipped.foldlM (init := #[]) fun acc e =>
    oneProof e.1.1.1.1 e.1.1.1.2 e.1.1.2 e.1.2 e.2
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
  match (parseTrace natG1Codec traceVk #[#[]] (#[#[#[0, 1]]])).run
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
  match (parseTrace natG1Codec traceVk #[#[]] (#[#[#[0, 1]]])).run
        (Transcript.initFromBytes (natToBytesBE 42 47)) with
  | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => true
  | _ => false

-- the instance shape checks fire before anything is absorbed
def parseTrace_shape_kats_ok : Bool :=
  -- no proofs at all
  (match (parseTrace natG1Codec traceVk #[] #[]).run
        (Transcript.initFromBytes traceProof) with
   | .error (Fault.error Error.invalidInstances) => true
   | _ => false) &&
      -- two instance columns where the CS declares one
      (match (parseTrace natG1Codec traceVk #[#[]] (#[#[#[0], #[0]]])).run
            (Transcript.initFromBytes traceProof) with
       | .error (Fault.error Error.invalidInstances) => true
       | _ => false) &&
      -- committed rows of differing lengths
      (match (parseTrace natG1Codec traceVk (#[#[], #[1]] : Array (Array Nat)) (#[#[], #[]])).run
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

end Kats

#eval Midfall.Halo2.parseTrace_kats_ok          -- expect true
#eval Midfall.Halo2.parseTrace_short_kats_ok    -- expect true
#eval Midfall.Halo2.parseTrace_shape_kats_ok    -- expect true
end Midfall.Halo2

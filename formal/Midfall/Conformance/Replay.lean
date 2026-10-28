-- |
-- Midfall.Conformance.Replay
--
-- The Phase 3 replay: Lean re-runs the verifier's Fiat-Shamir transcript over the
-- exporter's bundle and compares every value. This is the thin slice of PLAN
-- section 5 and docs/conformance-schema.md acceptance step 1.
--
-- WHAT IS INDEPENDENTLY DERIVED, AND WHAT IS NOT. The runner is given `vk.json`,
-- `instances.json` and `proof.bin`, and from those it computes the absorb prefix
-- itself (the vk representative, the committed instance, each instance column
-- length and value), decodes every proof read with the ported codecs, and squeezes
-- every challenge with the ported keccak-and-reduce. The exporter's `trace.json` is
-- the reference OUTPUT, never an input to those computations: each derived value is
-- compared against the recorded one. A trace value the port computes differently
-- reddens the run, which is the point - hazard 6 says a harness that cannot fail
-- manufactures confidence.
--
-- WHY NOT `verifyNative` ITSELF. `Exec/Native.lean`'s `verifyNative` and
-- `decodeRust` are generic over an `AdmissiblePairing`, and the only
-- `AdmissiblePairing` in the tree is the exponent model (R-28), whose codec cannot
-- decode a real 48-byte BLS12-381 point. `Midfall/Instances/Bls12_381.lean`
-- supplies a real codec but deliberately not a group law or a pairing, so the full
-- pipeline cannot be executed on real bytes yet. PLAN section 5 names the fallback:
-- "if the pairing is not executable in Lean, it compares the pairing *inputs* and
-- the Rust check result". That is what the `dual_msm` checks do - every MSM term is
-- re-decoded and re-encoded on the Lean side, and the Rust verdict is compared with
-- the verdict Lean reaches from the transcript. What IS executed here is the
-- transcript half of `decodeRust`: reads, decodes, absorbs, squeezes, at the real
-- modulus with the real curve codec.
--
-- THE THREE BUGS THIS WOULD HAVE CAUGHT. R-20 (a digest or repr emitted
-- little-endian) is caught by the digest comparison and by every absorb-width
-- comparison. R-30 / R-32 (a read schedule paraphrased differently in two places)
-- are caught because the runner's cursor advances by what IT decoded, so a dropped,
-- added or reordered read desynchronises every later byte and reddens the run from
-- that point on rather than once.

import Midfall.Conformance.Bundle
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Transcript
import Midfall.Instances.Bls12_381

namespace Midfall.Conformance

open Midfall Midfall.Halo2

/-- The BLS12-381 scalar modulus at the port's `Fr` parameter. CompPoly carries the
    primality fact, so no `decide` on a 255-bit number is needed. -/
abbrev R : ℕ := Midfall.Assumptions.r

local instance factR : Fact (Nat.Prime R) := inferInstance

/-- The scalar codec the port uses: wire little-endian repr, absorbed big-endian. -/
def hFr : Halo2.Hashable (Fr R) := hashableFr (p := R)

/-- The real BLS12-381 G1 codec: 48-byte compressed wire, 128-byte EIP-2537 absorb. -/
def hG1 : Halo2.Hashable Midfall.Instances.G1Affine :=
  hashableG1 Midfall.Instances.g1AffineCodec

/-! ## Diagnostics -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (b : Bytes) : String :=
  String.ofList (b.data.toList.flatMap fun u => [hexDigit (u.toNat / 16), hexDigit (u.toNat % 16)])

/-- Long payloads (a 128-byte EIP point) print with their head and length so a
    failure line stays readable. -/
def shortHex (b : Bytes) : String :=
  if b.size <= 24 then toHex b
  else toHex (b.extract 0 16) ++ "..(" ++ toString b.size ++ "B)"

/-! ## The report -/

structure Report where
  /-- Comparisons performed. A runner that compares nothing must not look green, so
      the exe refuses a zero check count as well as a non-empty failure list. -/
  checks : Nat := 0
  failures : Array String := #[]
  absorbs : Nat := 0
  reads : Nat := 0
  squeezes : Nat := 0
  terms : Nat := 0

def Report.eq {α : Type} [BEq α] [ToString α] (r : Report) (name : String)
    (expect got : α) (detail : String) : Report :=
  { r with
      checks := r.checks + 1,
      failures := if expect == got then r.failures else r.failures.push
        (name ++ ": " ++ detail ++ " [expected " ++ toString expect ++ ", got "
         ++ toString got ++ "]") }

def Report.ok (r : Report) (name : String) (good : Bool) (detail : String) : Report :=
  r.eq name true good detail

/-! ## The absorb prefix, derived by Lean -/

/-- An absorb the verifier performs, carrying the VALUE it absorbs: the bytes are
    what the runner computes from the port's codec and then compares. -/
inductive Abs where
  | fr (x : Fr R)
  | pt (P : Midfall.Instances.G1Affine)

def Abs.bytes : Abs → Bytes
  | Abs.fr x => hFr.toInput x
  | Abs.pt P => hG1.toInput P

def Abs.apply : Abs → Transcript → Transcript
  | Abs.fr x, t => t.common hFr x
  | Abs.pt P, t => t.common hG1 P

/-- A scalar the bundle claims is a field element: 32 bytes big-endian and
    canonical, or the runner says which. Rule R7 - a non-canonical repr is a
    refusal, not a reduction. -/
def scalarFromBE (bs : Bytes) : Except String (Fr R) :=
  if bs.size ≠ 32 then
    .error ("expected a 32-byte scalar, got " ++ toString bs.size ++ " bytes")
  else
    let n := bytesToNatBE bs
    if n ≥ R then .error "scalar is not canonical (>= r)"
    else .ok (Nat.cast n)

/-- The prefix, in the order `parse_trace` performs it
    (proofs/src/plonk/verifier.rs:71-105): the vk representative, then every
    committed instance commitment, then per public instance column the column
    length followed by its values. docs/ecosystem.md section 11 named this exact
    data as the reason `rust_trace.json` could not drive a replay; it is now
    exported, and Lean rebuilds it from `vk.json` + `instances.json` rather than
    reading it from the trace. -/
def derivePrefix (b : Bundle) : Except String (Array (String × Abs)) := do
  let mut out : Array (String × Abs) := #[]
  let mut errs : Array String := #[]
  match scalarFromBE b.vk.transcriptRepr with
  | .ok x => out := out.push ("vk_repr", Abs.fr x)
  | .error e => errs := errs.push ("vk.json transcript_repr_be_hex: " ++ e)
  for row in b.committed.toList do
    for j in List.range row.size do
      let tag := "committed_instance[" ++ toString j ++ "]"
      match hG1.readRepr? row[j]! with
      | some P => out := out.push (tag, Abs.pt P)
      | none => errs := errs.push (tag ++ ": Lean refused the compressed encoding")
  for c in List.range b.publicCols.size do
    let col := b.publicCols[c]!
    out := out.push ("instance_len[" ++ toString c ++ "]", Abs.fr (Nat.cast col.size))
    for v in List.range col.size do
      let tag := "instance[" ++ toString c ++ "][" ++ toString v ++ "]"
      match scalarFromBE col[v]! with
      | .ok x => out := out.push (tag, Abs.fr x)
      | .error e => errs := errs.push (tag ++ ": " ++ e)
  if errs.isEmpty then .ok out else .error (String.intercalate "; " errs.toList)

/-! ## The replay -/

structure St where
  t : Transcript
  pre : Array (String × Abs)
  pi : Nat
  /-- What Lean absorbed since its own last squeeze, in order: the counterpart of
      the exporter's `absorbed_before_hex`. -/
  since : Array Bytes
  r : Report


def step (b : Bundle) (st : St) (e : Ev) : St :=
  match e with
  | Ev.absorb tag bytes =>
      match st.pre[st.pi]? with
      | none =>
          let rr := st.r.ok ("absorb/" ++ tag) false "trace records a prefix absorb the VK shape does not predict"
          { st with r := rr }
      | some (ptag, abs) =>
          let got := abs.bytes
          let r1 := st.r.eq ("absorb_tag[" ++ toString st.pi ++ "]") tag ptag "the two disagree about which absorb comes next"
          let r2 := r1.eq ("absorb/" ++ tag) got bytes ("Lean absorbs 0x" ++ shortHex got ++ ", exporter 0x" ++ shortHex bytes)
          { t := abs.apply st.t, pre := st.pre, pi := st.pi + 1, since := st.since.push got, r := { r2 with absorbs := r2.absorbs + 1 } }
  | Ev.read name wire absorbed =>
      if wire.size == 48 then
        match st.t.read hG1 with
        | .error _ =>
            let rr := st.r.ok ("read/" ++ name) false ("Lean refused a read the Rust accepted (48 bytes at offset " ++ toString st.t.pos ++ ", 0x" ++ shortHex wire ++ ")")
            { st with r := rr }
        | .ok (P, t2) =>
            let logged := (t2.log.back?.map Prod.snd).getD Bytes.empty
            let r1 := st.r.eq ("read/" ++ name ++ "/wire") logged wire "the bytes Lean consumed from proof.bin are not the bytes the trace records"
            let r2 := r1.eq ("read/" ++ name ++ "/absorbed") (hG1.toInput P) absorbed ("Lean absorbs the EIP form 0x" ++ shortHex (hG1.toInput P) ++ ", exporter 0x" ++ shortHex absorbed)
            { t := t2, pre := st.pre, pi := st.pi, since := st.since.push (hG1.toInput P), r := { r2 with reads := r2.reads + 1 } }
      else if wire.size == 32 then
        match st.t.read hFr with
        | .error _ =>
            let rr := st.r.ok ("read/" ++ name) false ("Lean refused a scalar read the Rust accepted (offset " ++ toString st.t.pos ++ ", 0x" ++ shortHex wire ++ ")")
            { st with r := rr }
        | .ok (x, t2) =>
            let logged := (t2.log.back?.map Prod.snd).getD Bytes.empty
            let r1 := st.r.eq ("read/" ++ name ++ "/wire") logged wire "the bytes Lean consumed from proof.bin are not the bytes the trace records"
            let r2 := r1.eq ("read/" ++ name ++ "/absorbed") (hFr.toInput x) absorbed ("Lean absorbs 0x" ++ shortHex (hFr.toInput x) ++ ", exporter 0x" ++ shortHex absorbed)
            { t := t2, pre := st.pre, pi := st.pi, since := st.since.push (hFr.toInput x), r := { r2 with reads := r2.reads + 1 } }
      else
        let rr := st.r.ok ("read/" ++ name) false ("a read of width " ++ toString wire.size ++ " is neither a 48-byte point nor a 32-byte scalar")
        { st with r := rr }
  | Ev.squeeze name digest challenge before =>
      let (d, t2) := st.t.squeeze
      -- rust: Sampleable<Keccak256> for Fq is BigUint(digest_be) mod r
      -- (implementors.rs:20-39, 341-345). x3 is the one squeeze the verifier
      -- truncates AFTER sampling (poly/kzg/mod.rs:455-459), so the recorded
      -- challenge is truncate(digest mod r) and not digest mod r.
      let raw : Fr R := frOfDigest (p := R) (bytesToWordBE d)
      let c := if name == "x3" && b.vk.truncatedChallenges then truncate b.vk.scalarNumBits raw else raw
      let r1 := st.r.eq ("squeeze/" ++ name ++ "/digest") d digest ("Lean's keccak of its own absorb stream is 0x" ++ shortHex d ++ ", exporter 0x" ++ shortHex digest)
      let r2 := r1.eq ("squeeze/" ++ name ++ "/challenge") (hFr.toInput c) challenge ("Lean samples 0x" ++ shortHex (hFr.toInput c) ++ ", exporter 0x" ++ shortHex challenge)
      let r3 := r2.eq ("squeeze/" ++ name ++ "/absorbed_before") before st.since "the absorb stream since the previous squeeze differs"
      { t := t2, pre := st.pre, pi := st.pi, since := #[], r := { r3 with squeezes := r3.squeezes + 1 } }

/-- Re-encode one MSM term on the Lean side: the scalar must be a canonical
    big-endian field element and the point a canonical compressed encoding that
    survives decode and re-encode to the EIP form. This is the pairing-INPUT
    comparison PLAN section 5 sanctions when the pairing is not executable. -/
def checkTerm (r : Report) (channel : String) (i : Nat) (t : Term) : Report :=
  let scalarOk := t.scalar.size == 32 && bytesToNatBE t.scalar < R
  let r1 := r.ok (channel ++ "[" ++ toString i ++ "]/scalar") scalarOk ("not a canonical 32-byte big-endian scalar: 0x" ++ shortHex t.scalar)
  let r2 := r1.ok (channel ++ "[" ++ toString i ++ "]/label") (! (t.label == "")) "an MSM term with no label cannot be matched to the Rust"
  match hG1.readRepr? t.point with
  | none => r2.ok (channel ++ "[" ++ toString i ++ "]/point") false ("Lean refused the compressed point encoding 0x" ++ shortHex t.point)
  | some P => r2.eq (channel ++ "[" ++ toString i ++ "]/point-eip") (hG1.toInput P).size 128 "the decoded point must have a 128-byte EIP form"

def replay (b : Bundle) : Report :=
  let derived := derivePrefix b
  let pre : Array (String × Abs) := match derived with
    | .ok p => p
    | .error _ => #[]
  let st0 : St := { t := Transcript.initFromBytes b.proof, pre := pre, pi := 0, since := #[], r := {} }
  let st := b.trace.events.foldl (fun acc e => step b acc e) st0
  let r0 := match derived with
    | .error e => st.r.ok "prefix-derivation" false ("Lean could not derive the absorb prefix from the bundle: " ++ e)
    | .ok _ => st.r
  let r1 := r0.eq "prefix-consumed" st.pi pre.size "the runner did not consume every absorb it derived from vk.json and instances.json"
  let r2 := match st.t.assertEmpty with
    | .ok _ => r1.eq "verdict/transcript-exhausted" b.trace.verdict "accept" ("Lean consumed the proof exactly; the exporter reported " ++ b.trace.verdict)
    | .error _ => r1.ok "verdict/transcript-exhausted" false ("Lean's transcript did not consume proof.bin exactly (pos " ++ toString st.t.pos ++ " of " ++ toString st.t.buffer.size ++ ")")
  let r3 := r2.eq "proof_len" b.trace.proofLen b.proof.size "trace.json's proof_len disagrees with the bytes on disk"
  let r4 := b.trace.leftTerms.toList.zipIdx.foldl (fun rr (t, i) => checkTerm rr "left" i t) r3
  let r5 := b.trace.rightTerms.toList.zipIdx.foldl (fun rr (t, i) => checkTerm rr "right" i t) r4
  let r6 := r5.eq "dual_msm/left_count" b.trace.leftTerms.size 1 "the solidity verifier's left channel is the single pi term"
  let r7 := r6.ok "dual_msm/right_nonempty" (b.trace.rightTerms.size > 0) "an empty right channel means the guard was never built"
  let r8 := r7.ok "pairing/rust-verdict" b.trace.pairingCheck "the Rust pairing check did not accept, so there is nothing to conform to"
  -- The error class is a compared field, not a printed one: on an accepting run the
  -- exporter must report none, and on a rejecting run the runner reaches a
  -- different verdict above, so a non-empty class here is a contradiction between
  -- the two fields the exporter publishes.
  let r9 := r8.eq "error-class" b.trace.error "" "the exporter named an error class on a run it claims was accepted"
  { r9 with terms := b.trace.leftTerms.size + b.trace.rightTerms.size }

end Midfall.Conformance

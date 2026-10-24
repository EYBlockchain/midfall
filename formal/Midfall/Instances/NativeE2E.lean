-- |
-- Midfall.Instances.NativeE2E
--
-- End-to-end evidence for the plan-9.2 top-level API of `Exec/Native.lean`:
-- `prepare`, `decodeRust`, `prepareMsgs`, `verifyNative`, `verifyMsgs` (and the
-- `With` variants they unfold to), executed on a fixture whose constraint system
-- has the shape `verifyNative` hardcodes.
--
-- WHY A SECOND FIXTURE WAS NEEDED. `Instances/ExponentModel.lean` has the only
-- end-to-end fixture in the tree, and it calls `Verifier.prepare` directly with
-- `committed = [[]]` and ONE instance column. The §9.2 entry points call
-- `prepare ... [[1]] [[inst.toList]]`: one proof, one COMMITTED instance column
-- holding the identity point, plus one public instance column. `parseTrace`'s
-- column-count check (verifier.rs:61-65, ported at Exec/Verifier.lean:116)
-- requires `committed[0].size + inst[0].size = cs.numInstanceColumns`, so under
-- that shape the key must declare TWO instance columns - and the schedule then
-- reads one extra 32-byte scalar, the committed instance evaluation
-- (verifier.rs:357-358), that the old fixture has no bytes for. Every §9.2 call
-- against the old fixture therefore faults at that shape check before a single
-- proof byte is read (KAT 13 pins it) and so proves nothing. This file is the
-- missing evidence: the same model, the same size-4 `Fr 17` domain, a key with
-- the §9.2 shape, and a proof the pipeline accepts.
--
-- WHAT THE FIXTURE LOOKS LIKE. One advice column (phase 0), one fixed column that
-- is a SIMPLE selector, two instance columns, one gate `q_fixed(0) * advice(0)`,
-- cs_degree 3 over the size-4 domain, so two quotient limbs. The proof is 336
-- bytes in the order the Rust reads them:
--
--     advice commitment          48   exponent 3
--     quotient limb 0            48   exponent 1
--     quotient limb 1            48   exponent 2
--     committed instance eval    32   value 9      <- the read the old shape lacks
--     advice eval at x           32   value 5
--     f_com                      48   exponent 6
--     q_evals_on_x3              32   value 4
--     pi                         48   exponent 8   <- the one value that balances
--
-- π = 8 is found the same way the first fixture found 11: in the exponent model
-- the final pairing equation is linear in π, so exactly one of the seventeen
-- candidates balances it. `n2AcceptingNative` below SEARCHES all 17 and reports
-- the answer rather than asserting one value works: all seventeen run to
-- completion and consume exactly 336 bytes, and exactly one - 8 - is accepted.
--
-- WHAT THIS DOES NOT CERTIFY. Everything docs/REVIEW.md R-33 says the exponent
-- model does not certify: it is a model of exponent arithmetic, not of
-- BLS12-381, every element is its own discrete log, and no theorem here depends
-- on it (the dependency runs Instances -> Exec, never back). These are Bool
-- computations, not proofs; the frozen `verifyNative_iff_msgs` stays a `sorry`
-- and this file is its executable shadow, nothing more.
--
-- ON `[[1]]` VERSUS THE PLAN'S `[[0]]`. The plan sketch writes
-- `prepare E F vk [[0]] [[inst.toList]]`. The baseline Rust
-- (proofs/solidity-verifier/src/test.rs, the identity-accumulator case) passes
-- `&[&committed_pi]` where `committed_pi = [identity]` - one proof row, one
-- committed instance column, the curve identity - so the SHAPE is right and
-- `[[1]]` is how the identity of a `Group` is written multiplicatively. `[[0]]`
-- is the same element in additive notation and does not even typecheck here:
-- `Exp 17` has no `OfNat _ 0`. Reported, not changed.

import Midfall.Halo2.Exec.Native
import Midfall.Instances.ExponentModel

namespace Midfall.Instances

open Midfall Midfall.Halo2

section Kats

local instance fact17n : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The §9.2 runtime environment (D-P9): the model codec, the `Fr 17` field
    constants, the permutation delta and the fewer-point-sets runtime switch. The
    delta is the same 2 the first fixture uses. -/
def n2Env : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) :=
  { g1 := expG1Codec, field := fc17, delta := 2, fewerPointSetsRuntime := false }

/-- The gate: `q_fixed(0) * advice(0)` with a SIMPLE queried selector, so the
    linearization puts it on the fixed commitment. A `Expression.selector` would
    panic at mod.rs:532 (R-33). -/
def n2Gate : Gate (Fr 17) :=
  { name := "g", constraintNames := #["c"],
    polys := #[Expression.product
      (Expression.fixed { index := some 0, columnIndex := 0, rotation := .cur })
      (Expression.advice { index := some 0, columnIndex := 0, rotation := .cur, phase := ⟨0⟩ })],
    queriedSelectors := #[{ index := 0, isSimple := true }], queriedCells := #[] }

/-- The §9.2 shape: TWO instance columns (one committed, one public), one advice
    column, one fixed simple-selector column, one gate. -/
def n2Cs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default (F := Fr 17) with
    numAdviceColumns := 1, adviceColumnPhase := #[⟨0⟩],
    numInstanceColumns := 2, numFixedColumns := 1,
    selectorFlags := #[{ isSimple := true, colIdx := some 0 }],
    fixedQueries := #[({ index := 0, columnType := Any.fixed }, Rotation.cur)],
    adviceQueries := #[({ index := 0, columnType := Any.adviceFirst }, Rotation.cur)],
    instanceQueries := #[({ index := 0, columnType := Any.instance }, Rotation.cur),
                          ({ index := 1, columnType := Any.instance }, Rotation.cur)],
    gates := #[n2Gate] }

/-- The size-4 extended domain over `Fr 17`, the same one the first fixture and
    Exec/Verifier's own KATs use; `quotientPolyDegree = 2` is what makes the
    proof carry two quotient limbs. -/
def n2Dom : EvaluationDomain (Fr 17) :=
  { n := 4, k := 2, extendedK := 2, omega := 13, omegaInv := 4,
    extendedOmega := 13, extendedOmegaInv := 4, gCoset := 2, gCosetInv := 4,
    quotientPolyDegree := 2, ifftDivisor := 13, extendedIfftDivisor := 13,
    tEvaluations := #[8], barycentricWeight := 13 }

/-- The key. `permutation := ⟨#[]⟩` keeps the fixture to the advice/quotient/
    instance reads: no copy constraints, so nothing else is read or opened. -/
def n2Vk : VerifyingKey (Fr 17) (Exp 17) :=
  { domain := n2Dom, fixedCommitments := #[ex 7], permutation := ⟨#[]⟩,
    cs := n2Cs, csDegree := 3, transcriptRepr := 7 }

/-- The public instance column the caller supplies to `verifyNative`. -/
def n2Inst : Array (Fr 17) := #[0, 1]

/-- Encode (wire width, value) slots the way the transcript reads them: a G1 point
    is 48 big-endian bytes, a scalar is 32 little-endian bytes. -/
def n2Bytes (slots : List (Nat × Nat)) : Bytes :=
  slots.foldl (init := Bytes.empty) fun acc s =>
    ByteArray.append acc
      (if s.1 == g1CompressedWidth then natToBytesBE s.2 g1CompressedWidth
       else natToBytesLE s.2 32)

/-- Everything but π: advice, the two quotient limbs, the committed instance
    evaluation, the advice evaluation, `f_com` and the one `q_evals_on_x3`. -/
def n2Slots : List (Nat × Nat) :=
  [(48, 3), (48, 1), (48, 2), (32, 9), (32, 5), (48, 6), (32, 4)]

/-- The proof stream as a function of π: 288 fixed bytes plus the 48-byte π, so
    336 bytes and no slack - `verifyNative` calls `assertEmpty` itself. -/
def n2Proof (pi : Nat) : Bytes := n2Bytes (n2Slots ++ [(48, pi)])

/-- The accepted π, found by the search reported at the bottom of this file. -/
def n2Pi : Nat := 8

/-- Same stream with a NON-CANONICAL scalar (17 ≡ 0) in the advice-evaluation slot:
    rule R7 says the read must fail, so this is the negative control that separates
    "the decoder refused a bad repr" from "the decoder refused a bad length". -/
def n2ProofNonCanonical : Bytes :=
  n2Bytes [(48, 3), (48, 1), (48, 2), (32, 9), (32, 17), (48, 6), (32, 4), (48, 8)]

/-- `prepare` at the §9.2 shape, with the transcript it left behind. -/
def n2Prepare (π : Bytes) :
    Except Fault (DualMSM (Fr 17) (Exp 17) (Exp 17) (Exp 17) × Transcript) :=
  (prepare (Gₜ := Exp 17) n2Env Features.solidity n2Vk [[1]] [[n2Inst.toList]]).run
    (Transcript.initFromBytes π)

/-- The two MSM channels as exponents: what `DualMSM.check` compares, made visible. -/
def n2DualExp (d : DualMSM (Fr 17) (Exp 17) (Exp 17) (Exp 17)) : Nat × Nat :=
  (expOf d.left.eval, expOf d.right.eval)

def n2PrepareExp (π : Bytes) : Option (Nat × Nat) :=
  match n2Prepare π with
  | .ok (d, _) => some (n2DualExp d)
  | .error _ => none

/-- How many bytes the pipeline actually consumed: 0 when it faulted. -/
def n2RunPos (π : Bytes) : Nat :=
  match n2Prepare π with
  | .ok (_, t) => t.pos
  | .error _ => 0

/-- `decodeRust` at the §9.2 shape. -/
def n2Decode (π : Bytes) : Option (List (Midfall.Halo2.Msg (Fr 17) (Exp 17))) :=
  decodeRust (Gₜ := Exp 17) n2Env Features.solidity n2Vk n2Inst π

/-- A decoded message as a decidable tag: (0, exponent) for a point, (1, value)
    for a scalar. The tag is the first component so a width test that mixed up the
    two cases cannot hide behind equal payloads. -/
def n2MsgTag (m : Midfall.Halo2.Msg (Fr 17) (Exp 17)) : Nat × Nat :=
  match m with
  | .g1 P => (0, expOf P)
  | .fr s => (1, ZMod.val s)

/-- `msgWire ∘ decodeRust`: put the decoded messages back on the wire. -/
def n2ReEnc (ms : List (Midfall.Halo2.Msg (Fr 17) (Exp 17))) : Bytes :=
  ms.foldl (init := Bytes.empty) fun acc m => ByteArray.append acc (msgWire n2Env m)

def n2IsG1 (m : Midfall.Halo2.Msg (Fr 17) (Exp 17)) : Bool :=
  match m with
  | .g1 _ => true
  | .fr _ => false

/-- `verifyNative` as a Bool. -/
def n2VerifyNative (π : Bytes) : Bool :=
  match verifyNative (Gₜ := Exp 17) n2Env Features.solidity expPrm n2Vk n2Inst π with
  | .ok () => true
  | .error _ => false

/-- `verifyNative`, but only `Error::Opening` counts as a rejection: a proof that
    fails to PARSE must not be scored as a verifier that correctly rejected a bad
    equation. This is the conjunct that keeps the reject side non-vacuous. -/
def n2VerifyNativeOpening (π : Bytes) : Bool :=
  match verifyNative (Gₜ := Exp 17) n2Env Features.solidity expPrm n2Vk n2Inst π with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- The fault `verifyNative` reports at an arbitrary key, as a name: so a KAT can
    say WHICH failure it expects instead of accepting any rejection. -/
def n2FaultKindOn (vk : VerifyingKey (Fr 17) (Exp 17)) (π : Bytes) : String :=
  match verifyNative (Gₜ := Exp 17) n2Env Features.solidity expPrm vk n2Inst π with
  | .ok () => "ok"
  | .error (Fault.error Error.opening) => "opening"
  | .error (Fault.error Error.invalidInstances) => "invalidInstances"
  | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => "eof"
  | .error (Fault.error (Error.transcript IoErrorKind.notFound)) => "notFound"
  | .error (Fault.error (Error.transcript IoErrorKind.other)) => "other"
  | .error (Fault.error _) => "error-other"
  | .error (Fault.panic s) => "panic:" ++ s

/-- The fault at this file's key. -/
def n2FaultKind (π : Bytes) : String := n2FaultKindOn n2Vk π

/-- `verifyMsgs` fed by `decodeRust`: the right-hand side of the frozen
    `verifyNative_iff_msgs`, evaluated. `none` from the decoder is a rejection here,
    which is what makes the ⇒ direction of that theorem visible as a Bool. -/
def n2VerifyMsgs (H : Hash) (π : Bytes) : Bool :=
  match n2Decode π with
  | none => false
  | some ms =>
      match verifyMsgs (Gₜ := Exp 17) n2Env H Features.solidity expPrm n2Vk n2Inst ms with
      | .ok () => true
      | .error _ => false

/-- `prepareMsgs` at the caller's hash, as channel exponents. -/
def n2PrepareMsgsExp (H : Hash) (π : Bytes) : Option (Nat × Nat) :=
  match n2Decode π with
  | none => none
  | some ms =>
      match prepareMsgs (Gₜ := Exp 17) n2Env H Features.solidity n2Vk n2Inst ms with
      | .ok d => some (n2DualExp d)
      | .error _ => none

/-- A hash that is NOT keccak256: keccak over the input with one extra byte, so it
    is a different function with sane (non-degenerate) digests. If
    `Transcript.initWithHash` were decorative - i.e. `squeeze` still hard-coding
    keccak256 - every challenge stream under this H would equal the keccak one. -/
def n2AltHash : Hash := fun b => keccak256 (ByteArray.append b (natToBytesBE 7 1))

/-- Which π in 0..16 does `verifyNative` accept? THE SEARCH RESULT, reported
    rather than asserted: exactly [8]. -/
def n2AcceptingNative : List Nat :=
  (List.range 17).filter (fun pi => n2VerifyNative (n2Proof pi))

/-- The same search through the message-level verifier. -/
def n2AcceptingMsgs (H : Hash) : List Nat :=
  (List.range 17).filter (fun pi => n2VerifyMsgs H (n2Proof pi))

/-- The π that accepts when the committed-instance evaluation slot carries `ie`
    instead of 9: the column is read, absorbed and opened, so changing it moves the
    answer. -/
def n2AcceptingWithInstEval (ie : Nat) : List Nat :=
  (List.range 17).filter fun pi =>
    match (prepare (Gₜ := Exp 17) n2Env Features.solidity n2Vk [[1]] [[n2Inst.toList]]).run
        (Transcript.initFromBytes
          (n2Bytes [(48, 3), (48, 1), (48, 2), (32, ie), (32, 5), (48, 6), (32, 4), (48, pi)])) with
    | .ok (d, t) => DualMSM.check d expPrm && t.pos == t.buffer.size
    | .error _ => false

/-- The π that accepts for a different public instance column: the caller's
    `inst` reaches the batched identity through the inner product at :366-370, so
    a verifier that dropped it would answer the same for every column. -/
def n2AcceptingForInst (c : List (Fr 17)) : List Nat :=
  (List.range 17).filter fun pi =>
    match (prepare (Gₜ := Exp 17) n2Env Features.solidity n2Vk [[1]] [[c]]).run
        (Transcript.initFromBytes (n2Proof pi)) with
    | .ok (d, t) => DualMSM.check d expPrm && t.pos == t.buffer.size
    | .error _ => false

/-! ### The KATs -/

/-- (1) `decodeRust` on the accepted proof: eight messages, five points and three
    scalars, in read order, carrying the values the bytes encoded.

    Rules out: a decoder that answers `none` for a proof the verifier accepts; a
    decoder that stops where `parse_trace` stops and so misses `f_com`,
    `q_evals_on_x3` and π (the R-27 gap the read log exists to close - the list
    would be 5 long, not 8); a reordering (the exact list pins the order); and a
    width test that swapped the two branches: that answers `none` outright, because
    `ofCompressed?` refuses a 32-byte record, and even a swap that somehow decoded
    would report 3 g1 / 5 fr instead of 5 g1 / 3 fr. -/
def n2Decode_ok : Bool :=
  match n2Decode (n2Proof n2Pi) with
  | some ms =>
      ms.length == 8 &&
      ms.map n2MsgTag == [(0, 3), (0, 1), (0, 2), (1, 9), (1, 5), (0, 6), (1, 4), (0, 8)] &&
      (ms.filter n2IsG1).length == 5 &&
      (ms.filter (fun m => ! n2IsG1 m)).length == 3
  | none => false

/-- (2) A truncated proof does not decode - at every cut, including the one that
    leaves a single byte missing and the one that leaves only the advice
    commitment. The first conjunct is what stops this being vacuous: the same
    decoder must still accept the uncut stream, so `none` here is about length
    and not about the fixture.

    Rules out: a decoder that returns the messages it managed to read and drops
    the rest (a partial schedule would look fine here unless the `isSome`
    conjunct is present), and a `bytesTake` that clamps to the buffer end instead
    of faulting - which would turn the 335-byte cut into a successful read of a
    short π. -/
def n2DecodeTrunc_ok : Bool :=
  (n2Decode (n2Proof n2Pi)).isSome &&
  [0, 1, 48, 100, 288, 300, 335].all (fun n => (n2Decode ((n2Proof n2Pi).extract 0 n)).isNone)

/-- (3) Trailing bytes are refused: "schedule-driven, exact length" (plan 9.2).
    One byte of slack is enough to fail, so the check is the cursor comparison and
    not a coarse size test.

    Rules out: a decoder that ignores `assertEmpty` - which is exactly what the
    repack/encode round trip would silently break on, because a contract calldata
    buffer is padded - and a decoder that reports success while leaving the cursor
    short. The `isSome` conjunct again pins non-vacuity. -/
def n2DecodeTrailing_ok : Bool :=
  let π := n2Proof n2Pi
  (n2Decode π).isSome &&
  (n2Decode (ByteArray.append π (natToBytesBE 0 1))).isNone &&
  (n2Decode (ByteArray.append π (natToBytesBE 0 64))).isNone

/-- (4) The `none` of (2) and (3) is not the only failure mode: a full-length
    stream carrying a NON-CANONICAL scalar repr (17 in a 32-byte slot) also
    refuses to decode, and `verifyNative` faults with the transcript's
    `io::Error::other` arm rather than `Error::Opening`.

    Rules out: a scalar reader that reduces mod `p` instead of rejecting (rule R7)
    - under such a decoder this proof would decode to `some` and the fault would be
    `opening` - and a decoder whose `none` is unconditional, which (2) and (3)
    alone cannot tell apart from a correct one. -/
def n2DecodeNonCanonical_ok : Bool :=
  (n2Decode n2ProofNonCanonical).isNone &&
  n2FaultKind n2ProofNonCanonical == "other" &&
  n2FaultKind (n2Proof n2Pi) == "ok" &&
  (n2Decode (n2Proof n2Pi)).isSome

/-- (5) THE ROUND TRIP the read-log design depends on: re-encoding the decoded
    messages with `msgWire` reproduces EXACTLY the prefix of the buffer the
    pipeline consumed - not merely something of the same length. The prefix is
    taken at the position the run itself reports, and the buffer carries 64 bytes
    of slack so "prefix" cannot collapse into "the whole input".

    Rules out: an endianness slip of the R-20 kind - the last two conjuncts say the
    scalar wire form is the little-endian repr and NOT the big-endian absorb form,
    and the point wire form is the 48-byte compressed encoding and NOT the 128-byte
    EIP absorb form, so a `msgWire` that reached for `toInput` instead of `toBytes`
    fails here even though it would still round-trip against itself; and a decoder
    that reported values whose encoding differs from the bytes read, i.e. a
    non-canonical codec. -/
def n2RoundTrip_ok : Bool :=
  let π := n2Proof n2Pi
  let buf := ByteArray.append π (natToBytesBE 0 64)
  match n2Decode π with
  | some ms =>
      let re := n2ReEnc ms
      let pos := n2RunPos buf
      pos == 336 && re == buf.extract 0 pos && re.size == 336 &&
      buf.size == 400 && re != buf &&
      msgWire n2Env (Midfall.Halo2.Msg.fr 5) == frToRepr (p := 17) (5 : Fr 17) &&
      msgWire n2Env (Midfall.Halo2.Msg.fr 5) != frToInputBE (p := 17) (5 : Fr 17) &&
      msgWire n2Env (Midfall.Halo2.Msg.g1 (ex 3)) == natToBytesBE 3 48 &&
      msgWire n2Env (Midfall.Halo2.Msg.g1 (ex 3)) != expG1Codec.toEip (ex 3)
  | none => false

/-- (6) `prepareMsgs` with keccak256 as the caller's hash builds the SAME DualMSM
    as `prepare` on the byte stream - the two paths execute one schedule, which is
    the whole point of going through the byte level. The exponents are pinned to
    (8, 15) rather than compared only against each other, and the mutated π = 9
    stream is required to agree too while producing a DIFFERENT pair (9, 11).

    Rules out: a `prepareMsgs` that re-serialises with the wrong widths or order
    (its MSM would differ from the byte stream's), one that ignores `ms` and re-reads
    the original buffer, and - because (9, 11) != (8, 15) is asserted - a pair of
    paths that agree only because both are constant. -/
def n2PrepareMsgsAgrees_ok : Bool :=
  n2PrepareMsgsExp keccak256 (n2Proof n2Pi) == n2PrepareExp (n2Proof n2Pi) &&
  n2PrepareExp (n2Proof n2Pi) == some (8, 15) &&
  n2PrepareMsgsExp keccak256 (n2Proof 9) == n2PrepareExp (n2Proof 9) &&
  n2PrepareExp (n2Proof 9) == some (9, 11) &&
  n2PrepareMsgsExp keccak256 (n2Proof 8) != n2PrepareMsgsExp keccak256 (n2Proof 9)

/-- (7) `verifyNative` accepts the good proof and rejects a mutated one, and the
    rejection is `Error::Opening` - the pairing equation failed, not the parse.
    The whole 17-way sweep is asserted: every candidate runs to completion (so none
    of the sixteen rejections is a transcript accident counted as a win) and
    exactly π = 8 is accepted.

    Rules out: the R-27 trap in the other direction - a verifier that rejects
    everything, which would satisfy "rejects π = 9" but not "accepts π = 8" - and
    one that accepts everything, which fails the π = 9 conjunct. Demanding
    `opening` by name rules out a third: a fixture that rejects for an unrelated
    reason (a short buffer, a non-canonical repr) and looks discriminating while
    testing nothing. -/
def n2VerifyNative_ok : Bool :=
  n2VerifyNative (n2Proof n2Pi) &&
  n2FaultKind (n2Proof n2Pi) == "ok" &&
  ! n2VerifyNative (n2Proof 9) && n2VerifyNativeOpening (n2Proof 9) &&
  n2AcceptingNative == [8] &&
  (List.range 17).all (fun pi =>
    ["ok", "opening"].contains (n2FaultKind (n2Proof pi)))

/-- (8) The executable shadow of the frozen `verifyNative_iff_msgs`: for all
    seventeen streams, `verifyNative` accepts iff `decodeRust` decodes and
    `verifyMsgs` at keccak256 accepts. Stated as a Bool because the theorem stays
    `sorry`; the mutated proof is included on purpose - it decodes to `some ms` and
    is rejected by both sides, so the ∃ is witnessed on the reject side too and the
    equivalence is not carried by "the bad proof does not decode".

    Rules out: a message-level verifier that disagrees with the byte-level one on
    some proof (the theorem's actual content), and - via the last two conjuncts -
    the vacuous case where both sides reject everything, which would make the
    seventeen-way ↔ true for the wrong reason. -/
def n2VerifyMsgsAgrees_ok : Bool :=
  (List.range 17).all (fun pi =>
    n2VerifyNative (n2Proof pi) == n2VerifyMsgs keccak256 (n2Proof pi)) &&
  (n2Decode (n2Proof 9)).isSome &&
  n2VerifyMsgs keccak256 (n2Proof n2Pi) &&
  ! n2VerifyMsgs keccak256 (n2Proof 9) &&
  n2VerifyNative (n2Proof 9) == n2VerifyMsgs keccak256 (n2Proof 9)

/-- (9) The hash parameter is honoured, not decorative: with a non-keccak `H` the
    DualMSM is a different object (right channel 9 instead of 15 at the same
    bytes), and the message-level verifier accepts a DIFFERENT π - 11 under the
    alternate hash against 8 under keccak - while the byte-level `verifyNative`,
    which is keccak-only by construction, rejects 11.

    Rules out: `Transcript.initWithHash` storing `hash` without `squeeze` reading it
    (then the two accepting sets would coincide and the exponents would match
    keccak's), and a `prepareMsgs` that ignores `H` entirely. The keccak arm of the
    comparison is (6), which shows the same function at the keccak hash agreeing
    with the byte stream - so "different" here is about `H` and not about the path. -/
def n2HashHonoured_ok : Bool :=
  n2PrepareMsgsExp n2AltHash (n2Proof n2Pi) == some (8, 9) &&
  n2PrepareMsgsExp n2AltHash (n2Proof n2Pi) != n2PrepareMsgsExp keccak256 (n2Proof n2Pi) &&
  n2AcceptingMsgs n2AltHash == [11] &&
  n2AcceptingMsgs keccak256 == [8] &&
  n2AcceptingMsgs n2AltHash != n2AcceptingMsgs keccak256 &&
  ! n2VerifyNative (n2Proof 11)

/-- (10) The caller's instance column reaches the pairing equation: the accepting
    π moves with it - [0,1] gives 8, [1,0] gives 2, [0,0] gives 14, [3,5] gives 16.

    Rules out: a verifier that ignores `inst` (a dropped instance inner product at
    verifier.rs:366-370, the R-30/R-32 family of "a term that is not there"), and a
    fixture whose answer is pinned by a zero column so that dropping the term is
    invisible. Four distinct answers from four columns is the cheapest way to say
    the data flows. -/
def n2InstMatters_ok : Bool :=
  n2AcceptingForInst [0, 1] == [8] &&
  n2AcceptingForInst [1, 0] == [2] &&
  n2AcceptingForInst [0, 0] == [14] &&
  n2AcceptingForInst [3, 5] == [16]

/-- (11) The committed instance column is not decorative either: replacing the
    32-byte committed-instance evaluation changes the accepted π (9 -> 8, 8 -> 1,
    16 -> 3), because the value is absorbed and so re-keys every later challenge.
    And at the accepted proof both channels are non-identity points (8 and 15), so
    neither side of the pairing equation is trivially zero - the R-33 non-vacuity
    check, repeated for this fixture.

    Rules out: a fixture that passes because everything cancels, and a decoder or
    reader that skips the committed-instance read while still consuming the right
    number of bytes. -/
def n2NonVacuous_ok : Bool :=
  n2PrepareExp (n2Proof n2Pi) == some (8, 15) &&
  n2AcceptingWithInstEval 9 == [8] &&
  n2AcceptingWithInstEval 8 == [1] &&
  n2AcceptingWithInstEval 16 == [3]

/-- (12) The `With` variants are the same verifier: `verifyNativeWith` accepts the
    good stream and rejects the mutated one with `opening`, agreeing with
    `verifyNative` on both. Without this the two definitions the §9.2 API unfolds to
    would still be unexecuted anywhere in the tree.

    Rules out: `verifyNativeWith` drifting from `verifyNative` - they are written as
    the same four lines, and this is the check that they still are. -/
def n2WithVariants_ok : Bool :=
  (match verifyNativeWith (Gₜ := Exp 17) n2Env Features.solidity expPrm n2Vk n2Inst
        (n2Proof n2Pi) with
   | .ok () => true
   | .error _ => false) &&
  (match verifyNativeWith (Gₜ := Exp 17) n2Env Features.solidity expPrm n2Vk n2Inst
        (n2Proof 9) with
   | .error (Fault.error Error.opening) => true
   | _ => false)

/-- (13) WHY THIS FILE EXISTS, pinned by execution: the `Exec/Native` entry points
    reject the FIRST fixture's key outright - `verifyNative` at `e2eVk` faults with
    `Error::InvalidInstances` before a single proof byte is read, because the hardcoded
    `[[1]]` / `[[inst]]` shape needs two instance columns and `e2eCs` declares one -
    while the same call at this file's key accepts. So "the existing end-to-end KAT
    already covers the §9.2 API" is false, and the shape requirement is now executed
    rather than argued.

    Rules out: a §9.2 wrapper that silently normalises the shape (dropping the
    committed column would make the old key pass here and would diverge from the
    Rust's solidity call), and a coverage claim nobody has run. The fourth conjunct
    is the discriminator that keeps this from being "any key fails": the OLD proof
    bytes at the NEW key are refused too, for a DIFFERENT reason (trailing bytes -
    the old stream is 304 bytes of schedule plus 64 of slack), so the two fixtures
    differ in shape and not in some accidental parameter: same codec, same delta,
    same params, same domain. -/
def n2OldShapeRejected_ok : Bool :=
  n2FaultKindOn e2eVk (e2eProof 11) == "invalidInstances" &&
  n2FaultKindOn e2eVk (n2Proof n2Pi) == "invalidInstances" &&
  n2FaultKindOn n2Vk (n2Proof n2Pi) == "ok" &&
  n2FaultKindOn n2Vk (e2eProof 11) == "notFound"

#eval n2Decode_ok              -- expect true
#eval n2DecodeTrunc_ok         -- expect true
#eval n2DecodeTrailing_ok      -- expect true
#eval n2DecodeNonCanonical_ok  -- expect true
#eval n2RoundTrip_ok           -- expect true
#eval n2PrepareMsgsAgrees_ok   -- expect true
#eval n2VerifyNative_ok        -- expect true
#eval n2VerifyMsgsAgrees_ok    -- expect true
#eval n2HashHonoured_ok        -- expect true
#eval n2InstMatters_ok         -- expect true
#eval n2NonVacuous_ok          -- expect true
#eval n2WithVariants_ok        -- expect true
#eval n2OldShapeRejected_ok      -- expect true

-- The search results themselves, as data: exactly one pi in 0..16 is accepted by
-- `verifyNative` (8), the same set comes out of the message-level path at keccak,
-- and a different hash moves it to 11. Written as equalities rather than printing
-- the list because scripts/kat_gate.py's "expect" token cannot end in a bracket or
-- a quote - `-- expect [8]` parses as the expectation `[8` and fails the gate.
#eval n2AcceptingNative == [8]                -- expect true
#eval n2AcceptingMsgs keccak256 == [8]        -- expect true
#eval n2AcceptingMsgs n2AltHash == [11]       -- expect true
#eval n2RunPos (n2Proof n2Pi)          -- expect 336
#eval (n2Proof n2Pi).size              -- expect 336
#eval n2FaultKind (n2Proof 9) == "opening"    -- expect true
#eval n2FaultKind ((n2Proof n2Pi).extract 0 100) == "eof"    -- expect true
#eval n2FaultKind (ByteArray.append (n2Proof n2Pi) (natToBytesBE 0 4)) == "notFound" -- expect true

-- The same thirteen checks compiled rather than interpreted, for the same reason the
-- first fixture does it: the pipeline is built out of `Array` operations that do not
-- reduce in the kernel, and the transcript squeezes keccak. `native_decide` is
-- confined to this directory by scripts/checks.sh and is used only inside
-- `example`s, so nothing here depends on it.
example : n2Decode_ok = true := by native_decide
example : n2DecodeTrunc_ok = true := by native_decide
example : n2DecodeTrailing_ok = true := by native_decide
example : n2DecodeNonCanonical_ok = true := by native_decide
example : n2RoundTrip_ok = true := by native_decide
example : n2PrepareMsgsAgrees_ok = true := by native_decide
example : n2VerifyNative_ok = true := by native_decide
example : n2VerifyMsgsAgrees_ok = true := by native_decide
example : n2HashHonoured_ok = true := by native_decide
example : n2InstMatters_ok = true := by native_decide
example : n2NonVacuous_ok = true := by native_decide
example : n2WithVariants_ok = true := by native_decide
example : n2OldShapeRejected_ok = true := by native_decide

end Kats

end Midfall.Instances

-- |
-- Midfall.Halo2.Exec.Native
--
-- The L0 interface: the executable, line-faithful port of the Rust verifier
-- (plan Section 9.2). The declarations below fix the names, arities and types
-- the port must realise; their bodies are filled in during Phase 2 and are
-- tracked in formal/SORRY.md until then.
--
-- Everything is stated over an `AdmissiblePairing` (design decision D-P1), so
-- the same interface serves the abstract proofs and, once
-- `Assumptions/Pairing.lean` supplies the instance, the concrete BLS12-381 run
-- the conformance harness compares against Rust.

import Midfall.Common.Curve
import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Keccak
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Types
import Midfall.Halo2.Exec.VerifyingKey
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Transcript
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Pcs
import Midfall.Halo2.Exec.Verifier

namespace Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- Runtime data required by the §9.2 verifier path. -/
structure VerifierEnv (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where
  g1 : G1Codec G₁
  field : FieldConsts (Fr p)
  delta : Fr p
  fewerPointSetsRuntime : Bool

/-- A hash: the concrete Keccak for execution, or a random oracle in the proofs
    (plan 9.1 `abbrev Hash`). -/
abbrev Hash := Bytes → H256

/-! ## Historical blocker analysis (D-P9 adopted)

D-P9 now bundles the codec, field constants, delta and runtime switch in
`VerifierEnv`; `prepare` and `verifyNative` use it, and the §9.2 statements have
been re-pinned. `decodeRust` additionally takes `inst`. The two remaining
execution blockers are KZG read-schedule exposure and a hash-parameterised
transcript for `prepareMsgs`; the historical analysis below explains why the
original frozen signatures could not be implemented.

Reported under plan Section 12 ("if a Rust behaviour makes a statement false,
stop and report; never weaken the statement silently"). The port itself is
complete - `Exec/Verifier.lean` has `Verifier.verifyAlgebraicConstraints` and
`Verifier.prepare` end to end - but the plan 9.2 arities do not carry three
pieces of data that every leaf on this path requires:

1. `G1Codec G₁` (D-P6). `parse_trace` reads advice, lookup, permutation,
   trashcan and quotient commitments and `multi_prepare` reads `f_com` and `pi`;
   each read decodes a 48-byte compressed point and then absorbs its 128-byte
   EIP-2537 form, i.e. it needs `ofCompressed?` and `toEip`. Under D-P1 there is
   no concrete curve to read a codec from, so it is a parameter everywhere else
   in the port (`parseTrace`, `hashableG1`, `multiPrepare`, `Pcs.kzg`,
   Exec/Accumulator).
2. `FieldConsts (Fr p)` (D-P1/R-3). `multi_prepare` needs `NUM_BITS` for
   `truncate`/`truncated_powers` (kzg/mod.rs:394,457,502,521), and the deployed
   profile has truncated-challenges ON, so this is not optional (R-22).
3. `delta : Fr p` (R-3 extended). `permutation.rs` uses `F::DELTA`, which
   `FieldConsts` does not carry, so `partiallyEvaluateIdentities` takes it as an
   explicit parameter and every caller has to thread it.

And they cannot be added. Both alternatives were tried against the frozen file:

* as an *explicit* parameter, `verifyNative F params vk inst pi` at
  `Statements.lean:43` fails to elaborate: "Application type mismatch: The argument
  F has type `Features` but is expected to have type `G1Codec ?m`".
* as an *instance-implicit*, Lean refuses outright: "invalid binder annotation,
  type is not a class instance: `G1Codec G₁`" - and even with `G1Codec` made a
  class, `Statements.lean` binds only `[P : AdmissiblePairing G₁ G₂ Gₜ]` and
  supplies no such instance, so synthesis would fail there anyway.

A degenerate `G1Codec G₁` *can* be written for an abstract group (every
compressed read returns `none`, every absorb returns the empty word) and it
would make the four bodies compile. That is the trap: it is not an admitted hole,
it is a verifier that rejects every proof while `verifyNative_iff_msgs` still
elaborates. It is therefore not done here. (The word for that hole is deliberately
not spelled here: scripts/lean_grep.py treats a `/-! -/` block as code, so
spelling it would register as a false proof hole.)

### Consequences for the frozen statements

* `verifyNative_iff_msgs` elaborates but is not provable as written. Three of
  the four defs it mentions (`verifyNative`, `decodeRust`, `verifyMsgs`) have no
  faithful inhabitant at their frozen types, and `prepareMsgs` is pinned the
  same way by `Midfall/Lowering/Types.lean`.
* `decodeRust` has a second, independent gap: the read schedule is not a
  function of `(F, vk, pi)` alone. `verify_algebraic_constraints` reads one
  evaluation per *committed* instance column (verifier.rs:357-358) and one block
  of advice evaluations per *proof* (:379-381), so the schedule depends on
  `committed_instances` and `instances`, which `decodeRust` does not take. `verifyNative`
  hardcodes the solidity shape (`[[1]]` / `[[inst]]`), so the two agree only
  under that convention and the equivalence is only statable with the shape as an
  explicit hypothesis.
* Even with the shape fixed, `decodeRust` cannot see the reads `multi_prepare`
  performs internally (`f_com`, the `q_evals_on_x3` block, `pi` at
  kzg/mod.rs:447,463,531): `multiPrepare` returns only the `DualMSM`, so a
  schedule-driven decoder would have to re-implement the KZG leaf, which the
  package rules forbid. Exec/Transcript.lean needs a read-recording hook (or
  Exec/Kzg/MultiOpen needs to expose its read shape) before `decodeRust` is
  statable at all.
* `verifyMsgs_iff_spec` quantifies over an arbitrary `H : Hash`, but
  `Transcript.squeeze` hard-codes `keccak256` (Exec/Transcript.lean:172) and
  `TranscriptM` has no hash parameter, so no `TranscriptM`-based definition can
  honour a non-keccak `H`. Rule R9 ("the hash is a parameter `H : Hash`
  everywhere, defaulting to keccak256") is not satisfied by the existing
  transcript leaf, and §9.5's "all lowering proofs are hash-agnostic (forall H)"
  inherits that. Owner: Exec/Transcript.

### D-P9 interface re-pin

`Statements.lean` is now re-pinned with the environment bundled in
`VerifierEnv`; remaining decoder/hash limitations are implementation blockers.

    structure VerifierEnv (p : Nat) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
        [Group G₁] [Group G₂] [Group Gₜ]
        [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
        [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
        [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where
      g1 : G1Codec G₁
      fc : FieldConsts (Fr p)
      delta : Fr p
      fewerPointSetsRuntime : Bool

`prepareWith` and `verifyNativeWith` below are the bodies that would go into the
holes the moment that decision lands; they are complete, so the remaining work is
a re-pin, not a port. -/

/-- The wire encoding of one message: a G1 point is its 48-byte compressed form,
    a scalar its little-endian repr - the same two widths Transcript.read logged. -/
def msgWire {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) : Msg (Fr p) G₁ → Bytes
  | Msg.g1 P => E.g1.toCompressed P
  | Msg.fr s => frToRepr (p := p) s

/-- rust: proofs/src/plonk/verifier.rs:659-696 (Verifier::prepare), at the arity
    the port actually needs. `Midfall.Halo2.Verifier.prepare` is the faithful def;
    this is the plan-9.2 shape with the three missing environment parameters
    added (see the BLOCKED note). `committed` is the per-instance-column list of
    committed G1 points and `inst` the per-column instance values. -/
def prepareWith (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (committed : List (List G₁)) (inst : List (List (List (Fr p)))) :
    TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) :=
  Verifier.prepare (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.delta F
    (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime) vk
    (committed.map (fun r => r.toArray)).toArray
    (inst.map (fun row => (row.map (fun col => col.toArray)).toArray)).toArray

/-- rust: proofs/solidity-verifier/src/test.rs:340-380, the canonical composition,
    at the arity the port actually needs. Compare `verifyNative` below: identical
    body, three more parameters. The committed instance is the identity and there
    is exactly one proof, which is what test.rs:366-367 passes. -/
def verifyNativeWith {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) :
    Except Fault Unit := do
  -- Gₜ is a phantom of DualMSM, so it has to be named: nothing in the
  -- arguments pins it.
  let m := prepareWith (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]
  let (g, t) ← StateT.run m (Transcript.initFromBytes proof)
  t.assertEmpty
  unless DualMSM.check g params do throw (Fault.error Error.opening)

/-- rust: proofs/src/plonk/verifier.rs Verifier::prepare. Absorbs the proof
    stream, squeezes the challenges, evaluates the quotient identity and builds
    the dual MSM. `committed` is the per-instance-column list of committed G1
    points and `inst` the per-column instance values.

    BLOCKED (see the note above): this arity cannot carry the `G1Codec`, the
    `FieldConsts` or `delta`, so there is no faithful body for it. The body is
    `prepareWith` with those three supplied; filling this hole is a re-pin of
    `Statements.lean`, not a porting task. -/
def prepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (committed : List (List G₁)) (inst : List (List (List (Fr p)))) :
    TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) :=
  prepareWith (Gₜ := Gₜ) E F vk committed inst

/-- rust: proofs/solidity-verifier/src/test.rs:340-367, the canonical
    composition (plan Section 4, Exec/Native). -/
def verifyNative {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) :
    Except Fault Unit := do
  -- Gₜ is a phantom of DualMSM, so it has to be named: nothing in the
  -- arguments pins it.
  let m := prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]
  let (g, t) ← StateT.run m (Transcript.initFromBytes proof)
  t.assertEmpty
  unless DualMSM.check g params do throw (Fault.error Error.opening)

/-- Schedule-driven decode of a proof stream into the messages the verifier
    absorbs (plan 9.2).

    BLOCKED, for two independent reasons (see the note above): the frozen arity
    cannot carry the `G1Codec` its `Msg.g1` payloads require, and the read
    schedule is not a function of `(F, vk, pi)` alone - it depends on the number
    of proofs and committed instance columns, and on reads inside `multiPrepare`
    that the KZG leaf does not expose. -/
def decodeRust (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) :
    Option (List (Msg (Fr p) G₁)) := do
  -- The messages are whatever the pipeline actually consumed, recorded by
  -- Transcript.read. Deriving them this way is deliberate: a hand-written second
  -- copy of the schedule is exactly what R-30 and R-32 got wrong, and it would
  -- drift the moment the Rust changed. If the run faults, there is no message
  -- stream; if it leaves trailing bytes, the proof is not exactly the schedule
  -- either ("schedule-driven, exact length" in plan 9.2).
  let t0 := Transcript.initFromBytes π
  let (_, t) ← (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run t0 |>.toOption
  if t.buffer.size ≠ t.pos then none
  else
    let wG1 := (hashableG1 E.g1).width
    let wFr := (hashableFr (p := p)).width
    t.log.toList.mapM fun rec =>
      if rec.1 == wG1 then (E.g1.ofCompressed? rec.2).map Msg.g1
      else if rec.1 == wFr then (frOfRepr? (p := p) rec.2).map Msg.fr
      else none

/-- `prepare` driven by already-decoded messages instead of a byte stream.

    BLOCKED: the same three missing parameters, plus the `H : Hash` parameter
    cannot be honoured at all - `Transcript.squeeze` hard-codes keccak256 and
    `TranscriptM` has no hash parameter, so a `TranscriptM`-based body is
    keccak-only whatever `H` is passed (rule R9 is not satisfied by the existing
    transcript leaf). -/
def prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ) := do
  -- Re-serialise the messages to the wire bytes the transcript would have read,
  -- then run the SAME pipeline with the caller's hash. Going through the byte
  -- level rather than a parallel message-driven interpreter is what keeps
  -- verifyNative_iff_msgs close to a definitional unfolding: both sides execute
  -- one schedule, not two that must be proved to agree.
  let bytes := ms.foldl (init := Bytes.empty)
    (fun acc m => ByteArray.append acc (msgWire E m))
  let (g, t) ← (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
    (Transcript.initWithHash H bytes)
  t.assertEmpty
  pure g

/-- `verifyNative` at the message level.

    BLOCKED: `prepareMsgs` above, and the same `H` limitation. -/
def verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    Except Fault Unit := do
  let g ← prepareMsgs (Gₜ := Gₜ) E H F vk inst ms
  unless DualMSM.check g params do throw (Fault.error Error.opening)

end Midfall.Halo2

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
import Midfall.Common.Keccak
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Types

namespace Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- A hash: the concrete Keccak for execution, or a random oracle in the proofs
    (plan 9.1 `abbrev Hash`). -/
abbrev Hash := Bytes → H256

/-- rust: proofs/src/transcript/mod.rs CircuitTranscript::init_from_bytes. -/
def Transcript.initFromBytes (_ : Bytes) : Transcript := {}

/-- Consume-and-check that the proof stream was read exactly. -/
def Transcript.assertEmpty (_ : Transcript) : Except Fault Unit := .ok ()

/-- rust: proofs/src/poly/kzg/msm.rs:284 DualMSM::check, i.e.
    e(left, sG2) * e(right, -G2) = 1. -/
def DualMSM.check (g : DualMSM (Fr p) G₁ G₂) (params : ParamsVerifierKZG G₁ G₂) : Bool := sorry

/-- rust: proofs/src/plonk/verifier.rs Verifier::prepare. Absorbs the proof
    stream, squeezes the challenges, evaluates the quotient identity and builds
    the dual MSM. `committed` is the per-instance-column list of committed G1
    points and `inst` the per-column instance values. -/
def prepare (F : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed : List (List G₁)) (inst : List (List (List (Fr p)))) :
    TranscriptM (DualMSM (Fr p) G₁ G₂) := sorry

/-- rust: proofs/solidity-verifier/src/test.rs:340-367, the canonical
    composition (plan Section 4, Exec/Native). -/
def verifyNative (F : Features) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) :
    Except Fault Unit := do
  let (g, t) ← (prepare F vk [[1]] [[inst.toList]]).run (Transcript.initFromBytes proof)
  t.assertEmpty
  unless DualMSM.check g params do throw (Fault.error Error.opening)

/-- Schedule-driven decode of a proof stream into the messages the verifier
    absorbs (plan 9.2). -/
def decodeRust (F : Features) (vk : VerifyingKey (Fr p) G₁) (_ : Bytes) :
    Option (List (Msg (Fr p) G₁)) := sorry

/-- `prepare` driven by already-decoded messages instead of a byte stream. -/
def prepareMsgs (H : Hash) (F : Features) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    Except Fault (DualMSM (Fr p) G₁ G₂) := sorry

/-- `verifyNative` at the message level. -/
def verifyMsgs (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    Except Fault Unit := sorry

end Midfall.Halo2

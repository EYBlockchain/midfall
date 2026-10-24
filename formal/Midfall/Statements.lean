-- |
-- Midfall.Statements
--
-- THE FROZEN STATEMENTS (deliverable D6). Do not edit the meaning of anything
-- here: plan Section 12 forbids it, and CI checks this file's SHA-256 against
-- Midfall/Statements.sha256. Renaming or re-typing a declaration here requires
-- a sign-off and a re-pin of the hash.
--
-- Design decision D-P1 (docs/design.md): the statements are quantified over an
-- `AdmissiblePairing` rather than a named curve, because no Lean library has
-- BLS12-381 (docs/ecosystem.md). This makes them strictly more general than the
-- plan's Section 9, not weaker.

import Midfall.Common.Curve
import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Keccak
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.VerifyingKey
import Midfall.Halo2.Spec.Piop
import Midfall.Lowering.Types
import Midfall.Security.SRS
import Midfall.Security.Challenges

namespace Midfall.Statements

open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

section
variable (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
  (params : ParamsVerifierKZG G₁ G₂)
  (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes)

/-- Plan 9.2: the byte-level verifier and the message-level verifier accept
    exactly the same proofs, and every accepted proof decodes. -/
theorem verifyNative_iff_msgs :
    verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔
      ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧
        verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by sorry

end

section
variable (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
  (params : ParamsVerifierKZG G₁ G₂)
  (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
  (ms : List (Msg (Fr p) G₁))

/-- Plan 9.2: the compiled verifier and the mathematical spec agree. -/
theorem verifyMsgs_iff_spec (hwf : vk.WellFormed F) :
    (verifyMsgs (Gₜ := Gₜ) E H F params vk inst ms).isOk ↔
      Spec.accepts H F params vk inst ms := by sorry

end

section
variable (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
  (vk : VerifyingKey (Fr p) G₁)
  (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁))

/-- Plan 9.5 L6, the no-accumulator case: the contract-level reference predicate
    agrees with the message-level Rust-faithful verifier. Stated now over the
    placeholder ContractRefAccepts so the shape is frozen before the port exists;
    the accumulator arm (contractRef_acc_complete) needs Exec/Accumulator and
    lands with Phase 2. -/
theorem contractRef_noAcc :
    Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms ↔
      verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () := by sorry

end

end Midfall.Statements

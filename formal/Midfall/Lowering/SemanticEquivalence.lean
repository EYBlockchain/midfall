import Midfall.Lowering.Types

/-!
# Semantic equivalence obligations

This module states the proof boundary between the Rust-faithful Lean verifier and
the generated contract. `Midfall.Statements` is frozen, while the Yul run layer,
calldata decoder, and completed generator are still under construction. The
first result below is about code that already exists; the contract obligations
will be stated separately so no missing execution step can be hidden in a
vacuous implication.
-/

namespace Midfall.Lowering

open Midfall.Halo2

variable {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [AdmissiblePairing G₁ G₂ Gₜ]

/-- The currently implemented contract reference has no accumulator arm. It
    accepts exactly when the Rust-faithful message-level verifier succeeds;
    unlike the frozen `contractRef_noAcc` placeholder, this lemma has a proof
    and permits any hash `H`. Do not use it to claim accumulator-mode parity. -/
theorem contractRefAccepts_iff_verifyMsgs
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    ContractRefAccepts E H params vk inst ms = true ↔
      verifyMsgs E H Features.solidity params vk inst ms = .ok () := by
  cases h : prepareMsgs E H Features.solidity vk inst ms with
  | error err => simp [ContractRefAccepts, verifyMsgs, h, bind, Except.bind]
  | ok dual =>
      by_cases hc : DualMSM.check dual params
      · simp [ContractRefAccepts, verifyMsgs, h, hc, bind, Except.bind, pure, Except.pure]
      · simp [ContractRefAccepts, verifyMsgs, h, hc, bind, Except.bind, pure, Except.pure]

end Midfall.Lowering
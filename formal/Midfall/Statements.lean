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
--
-- D-P27 (adopted round 68, executed by P-REPIN) is the sign-off this header asks for,
-- and so far the only exception: the three statements below were amended because two
-- were FALSE as written and one was superseded. A hash freeze stops statements drifting
-- silently; it is not a licence to leave a known falsehood frozen. The old texts are not
-- deleted - each is pinned as a named proposition in Midfall/Instances/StatementsRepair.lean
-- together with the refutation showing it was genuinely false and the witness showing the
-- repaired hypotheses are satisfiable (D-P23, both halves). The digest in
-- Midfall/Statements.sha256 is re-pinned against this text.

import Midfall.Common.Curve
import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Keccak
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.VerifyingKey
import Midfall.Halo2.Spec.Piop
import Midfall.Lowering.Types
import Midfall.Lowering.Obligations
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
    exactly the same proofs, and every accepted proof decodes.

    AMENDED under D-P27. As frozen at `formal-baseline-v1` this carried no codec
    hypothesis, and it was FALSE: `prepareMsgs` re-serialises a G1 message with
    `E.g1.toCompressed` while `decodeRust` reads it with `ofCompressed?`, so with
    `toCompressed := fun _ => Bytes.empty` the left side accepts the 336-byte fixture
    proof while the right side has no witness at all (P-SE finding 1, attack.md line 107,
    `Midfall/Assumptions/Codec.lean:35-42`). `compressedRoundtrip` is the law the
    equivalence needs - decoder-first, i.e. re-encoding what the decoder accepted
    reproduces the bytes that were read - and it is the ONLY law needed: `p <= 2^256`
    was shown decorative here (attack.md line 107 FIX) and has not been added, so the
    repair is not a hypothesis pile-up. D-P23 halves: `repair1_satisfiable` exhibits an
    environment meeting it; `repair1_old_false_at_degEnv` and
    `repair1_old_universal_refuted` keep the old text and refute it. -/
theorem verifyNative_iff_msgs (hc : E.g1.compressedRoundtrip) :
    verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔
      ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧
        verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () :=
  Midfall.Lowering.verifyNative_iff_msgs_codec E F params vk inst π hc

end

section
variable (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
  (params : ParamsVerifierKZG G₁ G₂)
  (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
  (ms : List (Msg (Fr p) G₁))

/-- Plan 9.2: the compiled verifier and the mathematical spec agree.

    AMENDED under D-P27. The right-hand side used to be `Spec.accepts H F params vk inst ms`
    with no environment, while the left-hand side depends on `E.g1`, `E.delta`, `E.field`
    and `E.fewerPointSetsRuntime`. That cannot hold for every `E` - a predicate that
    ignores the environment cannot be equivalent to a verifier that reads it (P-SE
    finding 2, survey.md L0 area note). The spec now takes the same `E` the verifier runs
    under; `Spec.accepts` is still a registered hole and still must not be defined through
    Exec, so this repair makes the statement honest, not provable. D-P23 halves:
    `repair2_old_refuted` pins the old text as `verifyMsgs_iff_specOld` - the claim that
    some E-independent predicate agrees with `verifyMsgs` for every environment - and
    refutes it from two verdicts on one message stream; `repair2_new_shape_inhabited`
    shows the repaired binder class is inhabited, which the old one provably was not. -/
theorem verifyMsgs_iff_spec (hwf : vk.WellFormed F) :
    (verifyMsgs (Gₜ := Gₜ) E H F params vk inst ms).isOk ↔
      Spec.accepts E H F params vk inst ms := by sorry

end

section
variable (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
  (vk : VerifyingKey (Fr p) G₁)
  (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁))

/-- Plan 9.5 L6, the no-accumulator case: the contract-level reference predicate
    agrees with the message-level Rust-faithful verifier.

    SUPERSEDED under D-P27, and marked rather than deleted. This is no longer an open
    obligation of the lowering track: `Midfall.Lowering.contractRef_noAcc_of_semanticEquivalence`
    (Lowering/Obligations.lean:646) proves the same equivalence by re-exporting
    `contractRefAccepts_iff_verifyMsgs` (Lowering/SemanticEquivalence.lean:29), with no
    `sorryAx` in its dependencies, and `repair3_rederived` exhibits THIS text as a special
    case of that lemma. The original note - "stated now over the placeholder
    ContractRefAccepts so the shape is frozen before the port exists" - is refuted by the
    port existing, and the frozen form is strictly weaker than the proved one because it
    fixes `keccak256` where the lemma permits any hash (`repair3_hash_is_not_forced`
    shows another hash exists, so the generalisation is real and not vacuous). The
    accumulator arm it deferred to, `contractRef_acc_complete`, has also landed
    (Lowering/Accumulator.lean:538), so that half of the note is stale too. The statement
    is kept, `sorry` and all, because what this file freezes is the SHAPE of the
    obligation, and the shape is now known to be right. -/
theorem contractRef_noAcc :
    Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms ↔
      verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () := by sorry

end

end Midfall.Statements

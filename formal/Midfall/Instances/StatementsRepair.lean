-- |
-- Midfall.Instances.StatementsRepair
--
-- D-P27 EVIDENCE FOR THE THREE AMENDED FROZEN STATEMENTS (docs/plans/P-REPIN.md).
--
-- D-P23 requires BOTH halves for every amended statement: a satisfiability witness
-- showing some object meets the new hypotheses, and a retained refutation showing the
-- OLD text was genuinely false. This file carries all six for the three statements of
-- Midfall/Statements.lean, in three sections named after them. Nothing here is cited BY
-- the frozen file; the dependency runs Instances -> Exec, never back.
--
-- WHY HERE, IN Instances/. Every witness and every refutation is a claim about a
-- concrete verifier environment, and the only model of AdmissiblePairing in the tree is
-- the exponent model (Midfall/Instances/ExponentModel.lean, R-28). A theorem-bearing
-- file may not import it - D-P17, enforced by scripts/checks.sh - so the exhibits have
-- to live on this side of that wall, next to the fixture they borrow: NativeE2E's
-- accepting 336-byte proof, its key, its params and its decoded message list.
--
-- native_decide appears here and nowhere outside Midfall/Instances/ (the confinement
-- gate). Eight call sites across six theorems discharge closed verifier-pipeline
-- computations, each of which the same fixture already runs as a #eval gate; the frozen
-- statements do not depend on any of them, and their axiom set is unchanged by this
-- package.
--
-- A LEAN GOTCHA THAT COST HALF AN HOUR, recorded because it is invisible in the printed
-- type: in a binder body, `h -> a <-> b` parses as `(h -> a) <-> b`, not `h -> (a <-> b)`,
-- and the pretty-printer does not show the difference. A def written that way elaborates,
-- prints as the intended proposition, and then every application of it fails with
-- "function expected". The parentheses in verifyMsgs_iff_specOld are load-bearing.

import Midfall.Instances.NativeE2E
import Midfall.Lowering.SemanticEquivalence
import Midfall.Common.Bytes
import Midfall.Assumptions.Codec

namespace Midfall.Instances

open Midfall Midfall.Halo2 Midfall.Lowering

/-- The exponent model needs its primality fact at the use site (ExponentModel header). -/
local instance fact17rep : Fact (Nat.Prime 17) := ⟨by decide⟩

/-! ### Shared fixture facts -/

/-- The eight messages the §9.2 pipeline consumes for the accepted proof, in read
    order: five 48-byte points and three 32-byte scalars. Pinned by NativeE2E's KAT (1). -/
def n2Ms : List (Msg (Fr 17) (Exp 17)) :=
  [Msg.g1 (ex 3), Msg.g1 (ex 1), Msg.g1 (ex 2), Msg.fr 9, Msg.fr 5,
   Msg.g1 (ex 6), Msg.fr 4, Msg.g1 (ex 8)]

/-- The §9.2 fixture key is well formed at the Solidity profile, so the amended
    statements' binder context plus their one side condition is inhabited and not a
    hypothesis nothing satisfies. Every field is a closed computation. -/
theorem n2Vk_wellFormed : n2Vk.WellFormed Features.solidity :=
  ⟨rfl, by decide, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- Accept/reject as a Bool, so a verdict can be discharged by computation. -/
def vb (r : Except Fault Unit) : Bool :=
  match r with
  | .ok () => true
  | .error _ => false

theorem vb_ok {r : Except Fault Unit} (h : vb r = true) : r = .ok () := by
  cases r with
  | ok u => cases u; rfl
  | error a =>
      have h2 : vb (Except.error (α := Unit) a) = false := rfl
      rw [h2] at h; exact absurd h (by simp)

theorem vb_isOk {r : Except Fault Unit} (h : r.isOk = true) : r = .ok () := by
  cases r with
  | ok u => cases u; rfl
  | error a =>
      have h2 : (Except.error (α := Unit) a : Except Fault Unit).isOk = false := rfl
      rw [h2] at h; exact absurd h (by simp)

/-- The (kind, value) tag NativeE2E uses, as an injective map: two messages with the
    same tag are the same message, so a verdict that depends only on the tags can be
    pinned by a computation on them. -/
theorem n2MsgTag_injective : Function.Injective (n2MsgTag : Msg (Fr 17) (Exp 17) → Nat × Nat) := by
  intro a b h
  cases a with
  | g1 P =>
      cases b with
      | g1 Q =>
          have hv : (P.toAdd).val = (Q.toAdd).val :=
            by simpa [n2MsgTag, expOf] using congrArg Prod.snd h
          have hpq : P.toAdd = Q.toAdd := ZMod.val_injective (17 : ℕ) hv
          exact congrArg Msg.g1 (show P = Q from hpq)
      | fr s => exact absurd h (by simp [n2MsgTag])
  | fr s =>
      cases b with
      | g1 Q => exact absurd h (by simp [n2MsgTag])
      | fr t =>
          have hst : s = t := ZMod.val_injective (17 : ℕ)
            (by simpa [n2MsgTag] using congrArg Prod.snd h)
          exact congrArg Msg.fr hst

theorem list_map_inj {α β : Type} (f : α → β) (l l' : List α)
    (hf : Function.Injective f) (h : l.map f = l'.map f) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons b bs => exact absurd h (by simp)
  | cons a as ih =>
      cases l' with
      | nil => exact absurd h (by simp)
      | cons b bs =>
          have h2 := List.cons.inj (by simpa using h)
          have hab : a = b := hf h2.1
          subst hab
          exact congrArg (List.cons a) (ih bs h2.2)

/-! ### Repair 1 - Statements.verifyNative_iff_msgs, the codec law -/

/-- The last byte of a string as a natural (0 on the empty string). -/
def lastByteNat (b : Bytes) : Nat := b.data.toList.getLastD (0 : UInt8) |>.toNat

/-- The canonical compressed form of an exponent on the model: 47 zero bytes then the
    byte holding the exponent - a string of the pinned 48-byte width, injective on
    exponents. -/
def cbytes (n : Nat) : Bytes :=
  ByteArray.mk (((List.replicate 47 (0 : UInt8)) ++ [Nat.toUInt8 n]).toArray)

theorem cbytes_width (n : Nat) : (cbytes n).size = g1CompressedWidth := by
  classical
  show (((List.replicate 47 (0 : UInt8)) ++ [Nat.toUInt8 n]).toArray).size = 48
  simp [Array.size]

/-- A codec on the exponent model that IS canonical in the compressed direction: the
    decoder answers only for a string that is the encoding of its own last byte, which
    is exactly the equation compressedRoundtrip asks for. This is the witness, not the
    real curve codec - the byte ORDER it uses is the model's, and the width law is
    proved for it above so it is not a degenerate one-byte encoder. -/
def canonG1Codec : G1Codec (Exp 17) where
  ofCompressed? b :=
    if b = cbytes (lastByteNat b) ∧ lastByteNat b < 17 then
      some (Multiplicative.ofAdd (lastByteNat b : ZMod 17))
    else none
  toCompressed P := cbytes P.toAdd.val
  toEip P := natToBytesBE P.toAdd.val g1EipWidth
  ofEip? b :=
    if b.size == g1EipWidth then
      some (Multiplicative.ofAdd (Nat.cast (bytesToNatBE b)))
    else none

theorem canonG1Codec_compressedRoundtrip : canonG1Codec.compressedRoundtrip := by
  intro b P hb
  have h1 : canonG1Codec.ofCompressed? b =
      (if b = cbytes (lastByteNat b) ∧ lastByteNat b < 17 then
        some (Multiplicative.ofAdd (lastByteNat b : ZMod 17)) else none) := rfl
  by_cases hc : b = cbytes (lastByteNat b) ∧ lastByteNat b < 17
  · rw [h1, ite_eq_left hc] at hb
    have hP : Multiplicative.ofAdd (lastByteNat b : ZMod 17) = P := Option.some.inj hb
    subst hP
    show cbytes ((Multiplicative.ofAdd (lastByteNat b : ZMod 17)).toAdd.val) = b
    rw [show ((Multiplicative.ofAdd (lastByteNat b : ZMod 17)).toAdd) = (lastByteNat b : ZMod 17) from rfl,
        ZMod.val_natCast_of_lt hc.2]
    exact hc.1.symm
  · rw [h1, ite_eq_right hc] at hb
    exact absurd hb (by simp)

/-- The honest environment: the §9.2 fixture with a canonical compressed codec. -/
def canonEnv : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) :=
  { n2Env with g1 := canonG1Codec }

/-- SATISFIABILITY, repair 1: some environment meets the hypothesis the amended
    Statements.verifyNative_iff_msgs now demands. Not a vacuous binder class. -/
theorem repair1_satisfiable :
    ∃ (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17)), E.g1.compressedRoundtrip :=
  ⟨canonEnv, canonG1Codec_compressedRoundtrip⟩

/-- The degenerate codec finding B1 named: an honest decoder and an encoder that emits
    nothing, so a decoded stream cannot be put back on the wire. -/
def degG1Codec : G1Codec (Exp 17) where
  ofCompressed? b :=
    if b.size == g1CompressedWidth then
      some (Multiplicative.ofAdd (Nat.cast (bytesToNatBE b)))
    else none
  toCompressed _ := Bytes.empty
  toEip P := natToBytesBE P.toAdd.val g1EipWidth
  ofEip? b :=
    if b.size == g1EipWidth then
      some (Multiplicative.ofAdd (Nat.cast (bytesToNatBE b)))
    else none

def degEnv : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) :=
  { n2Env with g1 := degG1Codec }

/-- THE OLD TEXT, PINNED: the frozen statement as it stood at formal-baseline-v1, with
    no codec hypothesis, read as a claim about one environment. Kept as a named
    proposition rather than deleted, exactly as g1DecodesOld is for R-63, so the
    refutation below is a theorem about the text that was there. -/
def verifyNative_iff_msgsOld (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17))
    (F : Features) (params : ParamsVerifierKZG (Exp 17) (Exp 17))
    (vk : VerifyingKey (Fr 17) (Exp 17)) (inst : Array (Fr 17)) (pi : Bytes) : Prop :=
  verifyNative (Gₜ := Exp 17) E F params vk inst pi = .ok () ↔
    ∃ ms, decodeRust (Gₜ := Exp 17) E F vk inst pi = some ms ∧
      verifyMsgs (Gₜ := Exp 17) E keccak256 F params vk inst ms = .ok ()

theorem degNative_ok :
    verifyNative (Gₜ := Exp 17) degEnv Features.solidity expPrm n2Vk n2Inst
      (n2Proof n2Pi) = .ok () :=
  vb_ok (by native_decide : vb
    (verifyNative (Gₜ := Exp 17) degEnv Features.solidity expPrm n2Vk n2Inst
      (n2Proof n2Pi)) = true)

theorem degMsgs_not_ok :
    verifyMsgs (Gₜ := Exp 17) degEnv keccak256 Features.solidity expPrm n2Vk n2Inst n2Ms
      ≠ .ok () := by
  intro h
  have hfalse : vb (verifyMsgs (Gₜ := Exp 17) degEnv keccak256 Features.solidity expPrm n2Vk
      n2Inst n2Ms) = false := by native_decide
  rw [h] at hfalse
  exact absurd hfalse (by decide)

/-- REFUTATION, repair 1: the frozen text was FALSE, not merely unproved. At the
    degenerate environment the byte-level verifier accepts the fixture proof while no
    message stream both decodes and re-verifies - the mechanism attack.md line 107
    records, now discharged by computation instead of narrative. -/
theorem repair1_old_false_at_degEnv :
    ¬ verifyNative_iff_msgsOld degEnv Features.solidity expPrm n2Vk n2Inst (n2Proof n2Pi) := by
  intro h
  obtain ⟨ms, h1, h2⟩ := h.mp degNative_ok
  classical
  have htag : Option.map (fun ms : List (Msg (Fr 17) (Exp 17)) => ms.map n2MsgTag)
      (decodeRust (Gₜ := Exp 17) degEnv Features.solidity n2Vk n2Inst (n2Proof n2Pi))
      = some (n2Ms.map n2MsgTag) := by native_decide
  have h3 : Option.map (fun ms : List (Msg (Fr 17) (Exp 17)) => ms.map n2MsgTag)
      (some ms) = some (n2Ms.map n2MsgTag) := by rw [← h1]; exact htag
  have hms : ms = n2Ms :=
    list_map_inj n2MsgTag ms n2Ms n2MsgTag_injective (Option.some.inj h3)
  exact degMsgs_not_ok (by rw [← hms]; exact h2)

/-- The same refutation in the shape the frozen file states it: the old text was
    quantified over EVERY environment, and one environment refutes the lot. -/
theorem repair1_old_universal_refuted :
    ¬ (∀ (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17)) (F : Features)
        (params : ParamsVerifierKZG (Exp 17) (Exp 17)) (vk : VerifyingKey (Fr 17) (Exp 17))
        (inst : Array (Fr 17)) (pi : Bytes),
          verifyNative_iff_msgsOld E F params vk inst pi) :=
  fun h => repair1_old_false_at_degEnv
    (h degEnv Features.solidity expPrm n2Vk n2Inst (n2Proof n2Pi))

/-! ### Repair 2 - Statements.verifyMsgs_iff_spec, the verifier environment -/

/-- THE OLD TEXT, PINNED IN THE FORM THE DEFECT IS ABOUT. The frozen statement put an
    E-FREE right-hand side next to an E-dependent left-hand side, for every environment.
    Rather than cite the old Spec.accepts arity - which this package changes - pin the
    property that formulation asserted: that some predicate not mentioning E agrees with
    verifyMsgs for every environment. The frozen text entails that, so refuting this
    refutes the frozen text, and it is the stronger claim. -/
def verifyMsgs_iff_specOld : Prop :=
  ∃ (S : Hash → Features → ParamsVerifierKZG (Exp 17) (Exp 17) →
        VerifyingKey (Fr 17) (Exp 17) → Array (Fr 17) →
        List (Msg (Fr 17) (Exp 17)) → Prop),
    ∀ (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17)) (H : Hash) (F : Features)
        (params : ParamsVerifierKZG (Exp 17) (Exp 17)) (vk : VerifyingKey (Fr 17) (Exp 17))
        (inst : Array (Fr 17)) (ms : List (Msg (Fr 17) (Exp 17))),
      vk.WellFormed F →
        ((verifyMsgs (Gₜ := Exp 17) E H F params vk inst ms).isOk = true ↔ S H F params vk inst ms)

/-- Note on the parentheses above, which are load-bearing: in Lean 4.35 the binder body
    `h → a ↔ b` parses as `(h → a) ↔ b`, not `h → (a ↔ b)`, and the resulting proposition
    still prints without the parens that would show the difference. The first draft of this
    file lost half an hour to that: the def elaborated, printed as if it meant one thing,
    and then `hS E H F params vk inst ms hwf` failed with "function expected" because the
    hypothesis had been absorbed into the left arm of the `↔`. -/

theorem honestMsgs_isOk :
    (verifyMsgs (Gₜ := Exp 17) n2Env keccak256 Features.solidity expPrm n2Vk n2Inst n2Ms).isOk = true :=
  by native_decide

theorem degMsgs_isOk_false :
    (verifyMsgs (Gₜ := Exp 17) degEnv keccak256 Features.solidity expPrm n2Vk n2Inst n2Ms).isOk = false :=
  by native_decide

/-- REFUTATION, repair 2: no E-independent predicate can agree with verifyMsgs for every
    environment, because the same message stream at the same key is accepted under the
    fixture codec and rejected under the degenerate one. This is P-SE finding 2 and
    survey.md's "a predicate that ignores E cannot be equivalent for every E", discharged
    by computation rather than by narrative. -/
theorem repair2_old_refuted : ¬ verifyMsgs_iff_specOld := by
  rintro ⟨S, hS⟩
  have hn := hS n2Env keccak256 Features.solidity expPrm n2Vk n2Inst n2Ms n2Vk_wellFormed
  have h0 : S keccak256 Features.solidity expPrm n2Vk n2Inst n2Ms := hn.1 honestMsgs_isOk
  have hd := hS degEnv keccak256 Features.solidity expPrm n2Vk n2Inst n2Ms n2Vk_wellFormed
  have h1 : (verifyMsgs (Gₜ := Exp 17) degEnv keccak256 Features.solidity expPrm n2Vk
      n2Inst n2Ms).isOk = true := hd.2 h0
  have hne : (verifyMsgs (Gₜ := Exp 17) degEnv keccak256 Features.solidity expPrm n2Vk
      n2Inst n2Ms).isOk ≠ true := by simp [degMsgs_isOk_false]
  exact absurd h1 hne

/-- SATISFIABILITY, repair 2: the amended shape - a spec that sees the environment -
    admits a solution, which the pinned old shape provably did not. This is a non-vacuity
    witness and NOT a candidate definition of Spec.accepts: defining the spec through
    Exec is what Spec/Piop.lean:22-30 forbids, because it would make the refinement a
    tautology. What is established here is only that threading E does not empty the
    binder class, which is exactly what D-P23 asks of a repaired statement. -/
theorem repair2_new_shape_inhabited :
    ∃ (S : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) → Hash → Features →
        ParamsVerifierKZG (Exp 17) (Exp 17) → VerifyingKey (Fr 17) (Exp 17) →
        Array (Fr 17) → List (Msg (Fr 17) (Exp 17)) → Prop),
    ∀ (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17)) (H : Hash) (F : Features)
        (params : ParamsVerifierKZG (Exp 17) (Exp 17)) (vk : VerifyingKey (Fr 17) (Exp 17))
        (inst : Array (Fr 17)) (ms : List (Msg (Fr 17) (Exp 17))),
      vk.WellFormed F →
      ((verifyMsgs (Gₜ := Exp 17) E H F params vk inst ms).isOk ↔
        S E H F params vk inst ms) :=
  ⟨fun E H F params vk inst ms => (verifyMsgs (Gₜ := Exp 17) E H F params vk inst ms).isOk,
    fun _ _ _ _ _ _ _ _ => Iff.rfl⟩

/-! ### Repair 3 - Statements.contractRef_noAcc, superseded -/

/-- SATISFIABILITY, repair 3: the frozen statement is not an open obligation. It is the
    keccak256 arm of a lemma the tree already proves, restated here at the model with no
    sorryAx in its dependencies. -/
theorem repair3_rederived
    (E : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17))
    (params : ParamsVerifierKZG (Exp 17) (Exp 17)) (vk : VerifyingKey (Fr 17) (Exp 17))
    (inst : Array (Fr 17)) (ms : List (Msg (Fr 17) (Exp 17))) :
    ContractRefAccepts E keccak256 params vk inst ms = true ↔
      verifyMsgs (Gₜ := Exp 17) E keccak256 Features.solidity params vk inst ms = .ok () :=
  contractRefAccepts_iff_verifyMsgs E keccak256 params vk inst ms

/-- REFUTATION, repair 3: the frozen docstring's premise - that the shape was frozen
    over a placeholder "before the port exists" - is false, and the frozen text is
    strictly weaker than the proved lemma it duplicates: the lemma permits ANY hash and
    the frozen statement fixes keccak256, and there is a hash other than keccak256. So
    the frozen statement carries no obligation the proved lemma does not already carry. -/
theorem repair3_hash_is_not_forced : ∃ (H : Hash) (b : Bytes), H b ≠ keccak256 b :=
  ⟨n2AltHash, natToBytesBE 7 1, by native_decide⟩

/-- The proved lemma really does apply at a hash the frozen statement cannot name: this
    is the half that makes the frozen text a special case rather than a peer. -/
theorem repair3_lemma_is_hash_polymorphic
    (params : ParamsVerifierKZG (Exp 17) (Exp 17)) (vk : VerifyingKey (Fr 17) (Exp 17))
    (inst : Array (Fr 17)) (ms : List (Msg (Fr 17) (Exp 17))) :
    ContractRefAccepts n2Env n2AltHash params vk inst ms = true ↔
      verifyMsgs (Gₜ := Exp 17) n2Env n2AltHash Features.solidity params vk inst ms = .ok () :=
  contractRefAccepts_iff_verifyMsgs n2Env n2AltHash params vk inst ms

#print axioms n2Vk
#print axioms expPrm
#print axioms repair1_satisfiable
#print axioms repair1_old_false_at_degEnv
#print axioms repair1_old_universal_refuted
#print axioms repair2_old_refuted
#print axioms repair2_new_shape_inhabited
#print axioms repair3_rederived
#print axioms repair3_hash_is_not_forced
#print axioms n2Vk_wellFormed
#print axioms canonG1Codec_compressedRoundtrip

/-! ### Audit exhibits

  P-REPIN was told to be the review the freeze prevented, not only the re-pin. These are
  the checkable parts of that review. The narrative findings are in the package report;
  what is here is what could be proved or refuted at the model. -/

/-- The frozen file's whole binder block is inhabited: at p = 17 the exponent model
    supplies Group, PrimeOrderWith, the three Module instances and an AdmissiblePairing,
    and n2Env is a VerifierEnv over all of it. Recorded because the freeze stopped anyone
    asking: three statements quantified over an empty context would be as useless as a
    false one, and D-P1's "strictly more general, not weaker" is only safe while something
    satisfies the generality. -/
theorem frozen_binder_context_inhabited :
    Nonempty (VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17)) := ⟨n2Env⟩

/-- The side condition of the amended statement 2 is satisfiable at a real key, so it is
    not an empty binder class. What this package could NOT establish, and reports rather
    than hides, is that it is LOAD-BEARING: verifyMsgs does not consume it (its arity is
    E, H, F, params, vk, inst, ms and nothing else), so while Spec.accepts is still a
    sorry there is no way to show the equivalence fails for an ill-formed key. Flagged
    for Phase 4: prove it needed, or drop it as decoration of the R-58 F9 class. -/
theorem repair2_side_condition_satisfiable :
    ∃ (vk : VerifyingKey (Fr 17) (Exp 17)), vk.WellFormed Features.solidity :=
  ⟨n2Vk, n2Vk_wellFormed⟩

/-- The law the amended statement 1 demands is a REAL restriction and not a restatement
    of what the tree already has: the model codec every §9.2 KAT runs on, expG1Codec,
    FAILS it. Its ofCompressed? accepts any 48-byte string, so the non-canonical string
    natToBytesBE 18 48 decodes to the generator's square and re-encodes as
    natToBytesBE 1 48 - two distinct strings, one point. Consequence, stated plainly:
    the amended statement has no executable instance at n2Env, only at canonEnv. -/
theorem repair1_law_is_not_free : ¬ (expG1Codec (p := 17)).compressedRoundtrip := by
  intro h
  have hb : (expG1Codec (p := 17)).ofCompressed? (natToBytesBE 18 48)
      = some (Multiplicative.ofAdd (1 : ZMod 17)) := by native_decide
  have h2 := h (natToBytesBE 18 48) (Multiplicative.ofAdd (1 : ZMod 17)) hb
  exact absurd h2 (by native_decide)

/-- And the witness codec does satisfy the width law, so the repair did not buy
    canonicity by letting the encoder emit a one-byte string: 48 bytes, same as the wire. -/
theorem repair1_witness_has_the_right_width :
    ∀ Q : Exp 17, (canonG1Codec.toCompressed Q).size = g1CompressedWidth :=
  fun Q => cbytes_width Q.toAdd.val

#print axioms frozen_binder_context_inhabited
#print axioms repair2_side_condition_satisfiable
#print axioms repair1_law_is_not_free
#print axioms repair1_witness_has_the_right_width

end Midfall.Instances

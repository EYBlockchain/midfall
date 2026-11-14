-- |
-- Midfall/Instances/HoldsStaging
--
-- P-G2B STEP 4: the LANDMARK, STAGED. With the G1 side four of four (P-POINTCOUNT) and 'g2Valid'
-- discharged at a non-degenerate codec (P-G2B, Instances/G2Codec.lean), this file exhibits
-- 'Eip2537.Holds' as ONE term over BOTH codecs - conditional on exactly one named hypothesis, the
-- D-P36a 'AdmissiblePairing' on the exhibited groups. That is the whole point of the file: it turns
-- "what is left before a single Holds term?" from a prose claim into a term with one binder.
--
-- THE ONE NONTRIVIAL BIT, CHECKED. 'pairingProductOf' needs 'FrameLaws', whose first field is the
-- ENCODER-FIRST codec law 'c.ofEip? (c.toEip Q) = some Q'. P-G2 flagged this as the place the
-- landmark could still stall, because 'g1zOfEip?' is a 'Classical.choose' over the encoder's image
-- and choosing correctly needs 'g1zToEip' to be INJECTIVE. IT HOLDS, and the reason is short:
-- 'ptPair' is injective (P-POINTCOUNT), the G1 encoder is the padded byte map on canonical pairs,
-- and canonical pairs are read back exactly by 'g1Of?'. So the choose is unique and the law is four
-- lines. The G2 side needed the same ingredient and got it the same way
-- ('g2foldToEip_injective', via 'addOrderOf_emb2_h2').
--
-- WHAT THIS FILE DOES NOT CLAIM, and what P-HOLDS-FINAL changed since it was written:
--   * The theorem below is CONDITIONAL and this file never discharges its hypothesis: its binder
--     is exactly D-P36a. What changed in P-HOLDS-FINAL is that D-P36a became a NAMED assumption -
--     five constants in Assumptions/CurvePairing.lean, recorded as 'assumption_dP36a' - so the
--     unconditional exhibit exists one file away, as 'holds_exhibited' in
--     Instances/HoldsFinal.lean, and it is this theorem with that binder discharged. Before that
--     package the honest statement was 'no AdmissiblePairing on the curve groups exists in the
--     tree'; now it is 'one is assumed, by name, and the gate pins the assumption set'. The only
--     'AdmissiblePairing' MODEL in the tree is still the exponent model
--     (Instances/ExponentModel.lean), and 'Exp blsR' is used here as the G2 CARRIER (an
--     exponent-indexed carrier, which is what makes a G2 encoder computable at all), NOT as a
--     pairing model: nothing here constructs a pairing.
--   * The G2 carrier is not a set of curve points, so the 'Holds' term is not a claim that the
--     precompile's accepted G2 frames are exactly the multiples of H2. See Instances/G2Codec.lean's
--     header for what the carrier does and does not certify.
--   * 'product' is exhibited as 'pairingProductOf', i.e. DEFINED from the assumed 'P.e'. That is
--     D-P1's design, not a computation of a pairing.
--
-- D-P23: witness and falsification as THEOREMS below. No gate in the tree deletes a falsification
-- theorem and reddens the build; that limit has now been measured thirteen times in this project.

import Midfall.Instances.G2Codec
import Midfall.Instances.G1PointCount

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions

/-! ### THE ENCODER-FIRST LAW ON THE G1 SIDE (the one bit P-G2 said could stall) -/

/-- **THE G1 ENCODER IS INJECTIVE ON ITS CARRIER.** Three links, each already a theorem: the bytes
    decode back to the canonical pair ('g1Of?_g1PointBytes' + 'g1zPair_canonical'), the canonical
    pair determines the curve point ('ptPair_injective', P-POINTCOUNT), and the curve point
    determines the carrier element (the carrier is a subtype of the ambient group). This is the
    ingredient the 'Classical.choose' inside 'g1zOfEip?' needs. -/
theorem g1zToEip_injective : Function.Injective g1zToEip := by
  classical
  intro P Q h
  have e1 : g1Of? (g1zToEip P) = some (g1zPair P) :=
    g1Of?_g1PointBytes (g1zPair P) (g1zPair_canonical P).1 (g1zPair_canonical P).2
  have e2 : g1Of? (g1zToEip Q) = some (g1zPair Q) :=
    g1Of?_g1PointBytes (g1zPair Q) (g1zPair_canonical Q).1 (g1zPair_canonical Q).2
  have e3 : g1Of? (g1zToEip P) = g1Of? (g1zToEip Q) := congrArg g1Of? h
  rw [e1, e2] at e3
  have hpair : g1zPair P = g1zPair Q := Option.some.inj e3
  have hpt : g1zPoint P = g1zPoint Q := ptPair_injective hpair
  exact Subtype.ext (Multiplicative.ext hpt)

/-- **THE ENCODER-FIRST LAW FOR 'g1CodecZ'** - 'FrameLaws.g1_ofEip', the field P-G2 named as the
    place the landmark could stall. IT DOES NOT STALL: 'Classical.choose' picks the unique
    pre-existing element, and uniqueness is exactly 'g1zToEip_injective'. -/
theorem g1CodecZ_ofEip_toEip (Q : G₁z) : g1CodecZ.ofEip? (g1CodecZ.toEip Q) = some Q := by
  classical
  have hex : ∃ R : G₁z, g1zToEip R = g1zToEip Q := ⟨Q, rfl⟩
  show g1zOfEip? (g1zToEip Q) = some Q
  unfold g1zOfEip?
  rw [dif_pos hex]
  exact congrArg some (g1zToEip_injective (Classical.choose_spec hex))

/-- **THE G1 WIDTH LAW** - 'FrameLaws.g1_width'. -/
theorem g1CodecZ_toEip_size (Q : G₁z) : (g1CodecZ.toEip Q).size = g1Bytes :=
  g1PointBytes_size (g1zPair Q)

/-! ### THE FRAME LAWS AT BOTH CODECS, AND THE STAGED LANDMARK -/

/-- **THE FOUR FRAME LAWS, AT THE REAL-CURVE G1 CODEC AND THE EXPONENT-FOLD G2 CODEC.** Every field
    is a theorem of this tree or of P-G2B; none is an assumption. -/
theorem frameLaws_g2fold : FrameLaws g1CodecZ g2CodecFold g2foldOfEip? :=
  ⟨fun Q => g1CodecZ_ofEip_toEip Q,
    fun Q => g1CodecZ_toEip_size Q,
    fun R => g2foldOfEip?_g2foldToEip R,
    fun R => g2foldToEip_size R⟩

/-- **THE LANDMARK, STAGED.** Given the ONE remaining hypothesis - an 'AdmissiblePairing' on the
    exhibited groups, D-P36a - there is a pairing product for which 'Eip2537.Holds' holds at the
    real-curve G1 codec 'g1CodecZ' and the exponent-fold G2 codec 'g2CodecFold'. All six fields:
    'g1Valid', 'g1Add', 'g1Msm1' and 'g1Decodes' from P-G1CODEC and P-POINTCOUNT, 'g2Valid' from
    P-G2B, and 'pairing2' from P-HOLDS2's 'pairingProductOf_pairing2' once the frame laws are on
    the table. NOTHING here constructs a pairing: 'product' is 'pairingProductOf', defined from the
    assumed 'P.e', which is exactly what D-P1 designed and what the gap record said the clause
    needed. -/
theorem holds_staged {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ blsR]
    [Module (ZMod blsR) (Additive Gₜ)] [P : AdmissiblePairing G₁z G2fold Gₜ] :
    ∃ product : PairingProduct, Eip2537.Holds g1CodecZ g2CodecFold product := by
  classical
  refine ⟨pairingProductOf g1CodecZ g2foldOfEip?,
    g1CodecZ_g1Valid, g2fold_g2Valid, ?_, g1CodecZ_g1Add, g1CodecZ_g1Msm1,
      g1CodecZ_g1DecodesWidth⟩
  exact pairingProductOf_pairing2 g1CodecZ g2CodecFold g2foldOfEip? frameLaws_g2fold

/-- **THE PROJECTION CHECK** (the pattern of 'holds_pairing2_is_the_clause'): the term above really
    is the live 'Holds' structure and not a look-alike, because its fields project. -/
theorem holds_staged_g2Valid_projection {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ blsR]
    [Module (ZMod blsR) (Additive Gₜ)] [P : AdmissiblePairing G₁z G2fold Gₜ]
    (h : Eip2537.Holds g1CodecZ g2CodecFold
      (pairingProductOf g1CodecZ g2foldOfEip?)) :
    ∀ R : G2fold, ∃ pt, g2Of? (g2CodecFold.toEip R) = some pt ∧ g2PointValid pt = true :=
  h.g2Valid

/-- **WITNESS FOR THE STAGING (D-P23 satisfiability).** The exhibit is not vacuous in its OWN
    hypothesis-free part: the two decoders really do invert the two encoders at the published
    generators, which is the content of 'FrameLaws' and the only thing 'pairingProductOf' asks for.
    Stated at the generator elements, not at variables, so a codec that only works on the identity
    would not satisfy it. -/
theorem frameLaws_g2fold_witness :
    g1CodecZ.ofEip? (g1CodecZ.toEip g1zGen) = some g1zGen ∧
      g2foldOfEip? (g2CodecFold.toEip (g2foldExp 1)) = some (g2foldExp 1) ∧
        (g1CodecZ.toEip g1zGen).size = g1Bytes ∧ (g2CodecFold.toEip (g2foldExp 1)).size = g2Bytes :=
  ⟨g1CodecZ_ofEip_toEip g1zGen, g2foldOfEip?_g2foldToEip (g2foldExp 1),
    g1CodecZ_toEip_size g1zGen, g2foldToEip_size (g2foldExp 1)⟩

/-- **FALSIFICATION FOR THE STAGING (D-P23): the G2 half of 'FrameLaws' cannot be discharged by the
    DEGENERATE encoder.** The constant all-zero encoder satisfies 'g2Valid' - that is the
    over-statement correction of step 2, proved in Instances/G2Codec.lean - but it cannot supply
    'g2_ofEip' for ANY decoder, so it cannot appear in this exhibit. The landmark is not one step
    closer just because a clause is weak. -/
theorem holds_staged_needs_a_real_g2_encoder :
    ¬ ∃ (d₂ : Bytes → Option G2fold),
        FrameLaws g1CodecZ (⟨fun _ => bytesZero g2Bytes⟩ : G2Enc G2fold) d₂ := by
  rintro ⟨d₂, laws⟩
  exact constant_encoder_has_no_decoder ⟨d₂, laws.g2_ofEip⟩

/-- **AND THE G1 HALF IS NOT FREE EITHER**: the encoder-first law fails for a decoder that ignores
    its input, so 'g1CodecZ_ofEip_toEip' is a fact about 'g1zOfEip?' and not about the shape of
    'FrameLaws'. -/
theorem g1_ofEip_needs_the_real_decoder :
    ¬ (∀ Q : G₁z, (fun (_ : Bytes) => none : Bytes → Option G₁z) (g1CodecZ.toEip Q) = some Q) := by
  intro h
  have h1 := h g1zGen
  exact absurd h1.symm (Option.some_ne_none _)

#print axioms holds_staged
#print axioms g1zToEip_injective

end Midfall.Instances

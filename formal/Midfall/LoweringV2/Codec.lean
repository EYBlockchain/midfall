/-
  Midfall.LoweringV2.Codec

  THE CODEC BUNDLES THE V2 STATEMENT SURFACE NEEDS (D-P64, landed by ST.4).

  WHY HERE, AND NOT IN `Midfall/Assumptions/Codec.lean`. The v1 assumption layer is not a file this
  package may edit (the V3 cut-over ports into V2-owned modules; `Assumptions/Codec.lean` belongs to
  P-CODEC). Everything below is a NEW bundle, not a change to the frozen seven: `G1CodecLaws`
  (`Assumptions/Codec.lean:75-90`) is kept exactly as it is and is EXTENDED here.

  WHAT THE FOUR LAWS ARE FOR, and why the seven are not enough: `verifyMsgs`
  (`Halo2/Exec/Native.lean`) re-serialises every decoded G1 message with `toCompressed` and re-reads
  it with `ofCompressed?` (`Halo2/Exec/Transcript.lean`). `G1CodecLaws.compressedRoundtrip` is
  DECODER-first, so a codec whose `ofCompressed?` is the constant `none` satisfies all seven laws
  (`Instances/CurveSurface.lean`, `g1CodecZ_laws` is that proof, and
  `Instances/StatementsV3Deploy.lean`, `g1CodecZ_not_headlineLaws`, is the refutation of the
  headline bundle at the same codec) and makes `LeanAccepts` identically false. The ENCODER-first
  law is what forces the re-read to return the point that was decoded from calldata.

  WITNESS AND FALSIFIER, as W12 requires of a changed statement:
    * satisfiability, generic: `withCompressed_lawsV3` below (PROVED, no `sorryAx`);
    * satisfiability at a real codec: `Instances/StatementsV3Deploy.lean`, `lawsV3_satisfiable_at_G1z`;
    * the refutation that separates the bundle from the frozen seven:
      `Instances/StatementsV3Deploy.lean`, `g1CodecZ_not_headlineLaws`.
-/
import Midfall.Assumptions.Codec
set_option autoImplicit false

namespace Midfall.LoweringV2

open Midfall Midfall.Assumptions

/-- THE LAWS EVERY CONJUNCT OF THE HEADLINE NEEDS (soundness included).

    * `eipRoundtrip` - `decodeCalldata` yields `Q` with `ofEip? b = some Q`; the contract absorbed
      and copied the raw bytes `b`; `Inv` compares memory with `toEip Q` (`Lowering/Inv.lean`).
    * `compressedEncoderFirst` - `verifyMsgs` reads back `ofCompressed? (toCompressed Q)`; without
      this law it reads `none` (Lean rejects everything) or another point (finding A-4).
    * `compressedWidth` - the transcript cursor advances by `g1CompressedWidth` per G1 read
      (`Transcript.read`), so a wrong width misaligns every later read.
    * `toEip_one` - the committed-instance commitment is absorbed by the contract as 128 zero
      bytes (`TranscriptProofParser.yul`) and by Lean as `toEip 1`; the `g1_identity`
      window of `Inv` is the same pin. -/
structure G1CodecHeadlineLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  toEip_one : c.toEip 1 = natToBytesBE 0 128

/-- THE FULL BUNDLE `EndToEnd` NEEDS: the seven frozen laws plus the encoder-first one. The four
    extra laws over `G1CodecHeadlineLaws` are consumed by the calldata round trip only:
    `compressedRoundtrip` by `verifyNative_iff_msgs_codec` (`Lowering/Obligations.lean`) and
    `repack_spec_of_decodeRust` (`Lowering/Calldata.lean`); `ofEip_toEip`, `eipShape`, `eipWidth` by
    `calldata_roundtrip` (`Lowering/Calldata.lean`). -/
structure G1CodecLawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop
    extends G1CodecLaws c where
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q

/-- The full bundle gives the headline bundle. PROVED. -/
theorem G1CodecLawsV3.headline {G₁ : Type} [Group G₁] {c : G1Codec G₁} (h : G1CodecLawsV3 c) :
    G1CodecHeadlineLaws c :=
  ⟨h.eipRoundtrip, h.compressedEncoderFirst, h.compressedWidth, h.toEip_one⟩

/-- A codec whose compressed half is `comp`, with the decoder chosen classically. This is the
    shape `g1zOfEip?` already has for the EIP half (`Instances/G1Agreement.lean`). -/
noncomputable def withCompressed {G₁ : Type} (c : G1Codec G₁) (comp : G₁ → Bytes) : G1Codec G₁ :=
  { c with
    toCompressed := comp
    ofCompressed? := fun b =>
      open Classical in if h : ∃ Q, comp Q = b then some (Classical.choose h) else none }

/-- WITNESS (joint satisfiability, generic). Any codec satisfying the seven frozen laws becomes a
    codec satisfying all eight once its compressed half is replaced by an INJECTIVE map of the
    right width. PROVED: so the headline law set is satisfiable wherever the frozen one is and an
    injection `G₁ → 48 bytes` exists. `Instances/StatementsV3Deploy.lean` instantiates it at `G₁z`. -/
theorem withCompressed_lawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) (hc : G1CodecLaws c)
    (comp : G₁ → Bytes) (hinj : Function.Injective comp)
    (hw : ∀ Q, (comp Q).size = g1CompressedWidth) : G1CodecLawsV3 (withCompressed c comp) where
  eipRoundtrip := hc.eipRoundtrip
  compressedRoundtrip := by
    intro b Q h
    simp only [withCompressed] at h
    by_cases hex : ∃ Q, comp Q = b
    · simp only [hex, ↓reduceDIte] at h
      have hQ : Classical.choose hex = Q := Option.some.inj h
      rw [← hQ]
      exact Classical.choose_spec hex
    · simp only [hex, ↓reduceDIte] at h
      cases h
  ofEip_toEip := hc.ofEip_toEip
  eipShape := hc.eipShape
  toEip_one := hc.toEip_one
  compressedWidth := hw
  eipWidth := hc.eipWidth
  compressedEncoderFirst := by
    intro Q
    have hex : ∃ Q', comp Q' = comp Q := ⟨Q, rfl⟩
    simp only [withCompressed, hex, ↓reduceDIte]
    exact congrArg some (hinj (Classical.choose_spec hex))

#print axioms Midfall.LoweringV2.withCompressed_lawsV3

end Midfall.LoweringV2

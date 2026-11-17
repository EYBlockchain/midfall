/- Attempt to PROVE the leaf `decodeCalldata_eq_raw` of SoundnessV3.lean (definitions copied). -/
import Midfall.Lowering.Calldata
import Midfall.Instances.PoseidonInputs
import Midfall.Generator.Calldata
import Midfall.Assumptions.Eip2537
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace RawDecodeScratch
open Midfall Midfall.Halo2 Midfall.Lowering
open Midfall.Generator (RepackedProofLayoutPlan ProofCalldataLayout)

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}

inductive RawMsg (p : ℕ) where
  | g1 (frame : Bytes)
  | fr (s : Fr p)

def rawSlots (cd : Bytes) : List WireSlot → Nat → Option (List (RawMsg p) × Nat)
  | [], cur => some ([], cur)
  | .g1 :: rest, cur =>
      if g1WordsOk cd cur then
        match bytesTake cd cur g1EipWidth with
        | none => none
        | some b =>
          match rawSlots cd rest (cur + g1EipWidth) with
          | none => none
          | some (ms, cur') => some (RawMsg.g1 b :: ms, cur')
      else none
  | .fr :: rest, cur =>
      if (cdWord cd cur).toNat < p then
        match rawSlots cd rest (cur + 32) with
        | none => none
        | some (ms, cur') => some (RawMsg.fr (Nat.cast (cdWord cd cur).toNat) :: ms, cur')
      else none

def liftRaw (c : G1Codec G₁) : RawMsg p → Option (Msg (Fr p) G₁)
  | .g1 b => (c.ofEip? b).map Msg.g1
  | .fr s => some (Msg.fr s)

theorem decodeSlots_eq_raw (c : G1Codec G₁) (cd : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat),
      decodeSlots (p := p) c cd slots cur =
        (rawSlots (p := p) cd slots cur).bind fun r =>
          (r.1.mapM (liftRaw c)).map fun ms => (ms, r.2) := by
  intro slots
  induction slots with
  | nil => intro cur; simp [decodeSlots, rawSlots]
  | cons sl rest ih =>
      intro cur
      cases sl with
      | g1 =>
          simp only [decodeSlots, rawSlots, ih]
          by_cases hg : g1WordsOk cd cur = true
          · cases hb : bytesTake cd cur g1EipWidth with
            | none => simp [hg, hb, guard]
            | some b =>
                cases hr : rawSlots (p := p) cd rest (cur + g1EipWidth) with
                | none => simp [hg, hb, hr, guard]
                | some r =>
                    obtain ⟨raw, cur'⟩ := r
                    cases hq : c.ofEip? b with
                    | none => simp [hg, hb, hr, hq, guard, liftRaw]
                    | some Q =>
                        cases hm : raw.mapM (liftRaw (p := p) c) with
                        | none => simp [hg, hb, hr, hq, hm, guard, liftRaw]
                        | some ms => simp [hg, hb, hr, hq, hm, guard, liftRaw]
          · simp [hg, guard]
      | fr =>
          simp only [decodeSlots, rawSlots, ih]
          by_cases hg : (cdWord cd cur).toNat < p
          · cases hr : rawSlots (p := p) cd rest (cur + 32) with
            | none => simp [hg, hr, guard]
            | some r =>
                obtain ⟨raw, cur'⟩ := r
                cases hm : raw.mapM (liftRaw (p := p) c) with
                | none => simp [hg, hr, hm, guard, liftRaw]
                | some ms => simp [hg, hr, hm, guard, liftRaw]
          · simp [hg, guard]


def abiHeadOk (L : ProofCalldataLayout) (cd : Bytes) : Bool :=
  (bytesTake cd 0 4 == some Midfall.Generator.fnSigVerifyProof) &&
  (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr) &&
  (L.proofEnd == L.proofCptr + L.proofLen) &&
  ((cdWord cd 4).toNat == 0x40 && (cdWord cd 0x24).toNat == L.proofEnd - 4)

def envelopeOk (L : ProofCalldataLayout) (numInstances : Nat) (cd : Bytes) : Bool :=
  abiHeadOk L cd &&
  ((cdWord cd 0x44).toNat == L.proofLen) &&
  ((cdWord cd L.proofEnd).toNat == numInstances) &&
  (cd.size == L.proofEnd + 32 + 32 * numInstances)

def rawDecode (L : ProofCalldataLayout) (numInstances : Nat) (cd : Bytes) :
    Option (List (RawMsg p) × Array Word256) :=
  if envelopeOk L numInstances cd then
    match rawSlots (p := p) cd (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr with
    | none => none
    | some (ms, cur) =>
      let inst := (List.range numInstances).map (fun i => cdWord cd (L.proofEnd + 32 + 32 * i))
      if cur == L.proofEnd && inst.all (fun w => w.toNat < p) then some (ms, inst.toArray) else none
  else none

theorem decodeCalldata_eq_raw (L : ProofCalldataLayout) (n : Nat) (c : G1Codec G₁) (cd : Bytes) :
    decodeCalldata (p := p) L n c cd =
      (rawDecode (p := p) L n cd).bind fun r =>
        (r.1.mapM (liftRaw c)).map fun ms => (ms, r.2) := by
  unfold decodeCalldata rawDecode envelopeOk abiHeadOk
  simp only [decodeSlots_eq_raw]
  by_cases h1 : (bytesTake cd 0 4 == some Midfall.Generator.fnSigVerifyProof) = true
  <;> by_cases h2 : (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr) = true
  <;> by_cases h3 : (L.proofEnd == L.proofCptr + L.proofLen) = true
  <;> by_cases h4 : ((cdWord cd 4).toNat == 0x40 && (cdWord cd 0x24).toNat == L.proofEnd - 4) = true
  <;> by_cases h5 : ((cdWord cd 0x44).toNat == L.proofLen) = true
  <;> by_cases h6 : ((cdWord cd L.proofEnd).toNat == n) = true
  <;> by_cases h7 : (cd.size == L.proofEnd + 32 + 32 * n) = true
  <;> simp [h1, h2, h3, h4, h5, h6, h7, guard]
  cases hr : rawSlots (p := p) cd (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr with
  | none => simp
  | some r =>
      obtain ⟨raw, cur⟩ := r
      cases hm : raw.mapM (liftRaw (p := p) c) with
      | none => simp [hm]; split_ifs <;> simp_all
      | some ms =>
          simp [hm]; split_ifs <;> simp_all
          rename_i hex hall
          obtain ⟨x, hx, hle⟩ := hex
          exact absurd (hall.2 x hx) (Nat.not_lt.mpr hle)


/-! MEASUREMENT: the RAW stage on the Rust-generated fixture calldata (untracked build artefact
    proofs/solidity-verifier/target/poseidon-fixture-dump/calldata.bin), at the deployed layout
    `poseidonPlanV2.proofLayout` and the BLS12-381 scalar prime. -/
def RawMsg.isG1 {p : ℕ} : RawMsg p → Bool
  | .g1 _ => true
  | .fr _ => false

open Midfall.Instances.PoseidonInputs in
def rawStageOnFixture : IO String := do
  let cd ← Midfall.Generator.CalldataKats.readBinOrEmpty
    "../proofs/solidity-verifier/target/poseidon-fixture-dump/calldata.bin" 65536
  let L := poseidonPlanV2.proofLayout
  let r := rawDecode (p := Midfall.Yul.blsR) L 1 cd
  let g1s := match r with
    | some (ms, _) => (ms.filter RawMsg.isG1).length
    | none => 0
  let frs := match r with
    | some (ms, _) => (ms.filter (fun m => !RawMsg.isG1 m)).length
    | none => 0
  -- one flipped byte in an eval word (make it >= r): the raw stage must reject
  let nats := Midfall.Generator.bytesToNats cd
  let bad := Midfall.Generator.bytesFromNats
    ((List.take L.evals.start nats) ++ List.replicate 32 255 ++ (List.drop (L.evals.start + 32) nats))
  pure s!"size={cd.size} abiHead={abiHeadOk L cd} envelope={envelopeOk L 1 cd} raw.isSome={r.isSome} g1Slots={g1s} frSlots={frs} staticLayout={(L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr, L.proofEnd == L.proofCptr + L.proofLen)} badScalarRejected={(rawDecode (p := Midfall.Yul.blsR) L 1 bad).isNone} wrongCount={(rawDecode (p := Midfall.Yul.blsR) L 2 cd).isNone}"

#eval rawStageOnFixture

end RawDecodeScratch

/-
  D5/D6 - REAL KEY DATA AT THE DEPLOYMENT, and the pins that tie the Lean key to the payload.

  Part 1: the generic pin structure `KeyAgrees` (what `EnvAgrees` does not say: E+1, G-4, H-3, A-5).
  Part 2: the deployment terms, named from the fixture bytes.
  Part 3: every pin EVALUATED at the deployment data, in the VM.
-/
import RunLib
import Midfall.Lowering.Inv
import Midfall.Instances.PoseidonInputs
set_option autoImplicit false

namespace RefKey
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2 RefModel RefRun
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv Midfall.Conformance
open Midfall.Lowering Midfall.Generator Midfall.Instances.PoseidonInputs

/-! ## Part 1. The pins, generically -/

/-- The four words of a payload commitment as the 128 bytes the contract loads. -/
def g1WordsBytes (w : G1Words) : Bytes :=
  [w.xHi, w.xLo, w.yHi, w.yLo].foldl (fun acc x => ByteArray.append acc (wordToBytesBE x)) Bytes.empty

/-- A named header word of the payload. -/
def headerWord? (vk : Halo2VerifyingKey) (name : String) : Option Word256 :=
  (vk.constants.find? fun c => c.1 == name).map fun c => c.2

section Generic
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **THE KEY PINS.** Everything the contract loads from the VK payload and the Lean verifier
    reads from its own key, tied together. `EnvAgrees` (Lowering/Inv.lean:533-579) pins k, n, the
    barycentric weight and the digest word and NOTHING ELSE of the key; these clauses are the rest.

    Every clause is an equation between payload bytes/words and an encoding, so each is decided by
    evaluation once the carrier is computable (Part 3). No clause mentions a class generator of
    G₂: the two G2 points the final pairing uses are the DATA `params.nG2Prepared` and
    `params.sG2Prepared`. -/
structure KeyAgrees (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) (PV : PlanView)
    (params : ParamsVerifierKZG G₁ G₂) (encG2 : G₂ → Bytes) (frDelta : String) : Prop where
  /-- the fixed-commitment section of the payload is the encoding of the Lean key's commitments,
      one for one and in order -/
  fixedWords : PV.vk.fixedComms.map g1WordsBytes = vk.fixedCommitments.toList.map E.g1.toEip
  /-- the same for the sigma commitments (one per permutation COLUMN) -/
  permWords : PV.vk.permutationComms.map g1WordsBytes =
    vk.permutation.commitments.toList.map E.g1.toEip
  /-- Lagrange.yul reads omega, omega_inv and omega_inv_to_l from VK memory; the Lean verifier
      rotates by `vk.domain.omega` / `omegaInv` (H-3's omega^3 counterexample) -/
  omegaWord : headerWord? PV.vk "omega" = some (frWord vk.domain.omega)
  omegaInvWord : headerWord? PV.vk "omega_inv" = some (frWord vk.domain.omegaInv)
  /-- G1_BASE holds the encoding of the generator the Lean verifier uses for the `-G` term
      (Exec/Kzg/MultiOpen.lean:311; rust kzg/mod.rs:547 `-E::G1::generator()`) -/
  g1Base : vkG1Words PV vkG1BaseSlot = E.g1.toEip P.g₁
  /-- G2_BASE is the encoding of the point whose inverse the Lean check pairs `right` with -/
  g2Base : vkG2Words PV vkG2BaseSlot = encG2 params.nG2Prepared⁻¹
  /-- NEG_S_G2_BASE is the encoding of the inverse of the point the Lean check pairs `left` with -/
  negSG2 : vkG2Words PV vkNegSG2BaseSlot = encG2 params.sG2Prepared⁻¹
  /-- the DELTA literal the quotient program is rendered from is the Lean verifier's delta
      (rust: fr_delta_literal = u256_string(fe_to_u256(Fq::DELTA)), QVM:4131) -/
  delta : frDelta = Midfall.Generator.QuotientFoldCompute.u256String (frWord E.delta)

end Generic

/-! ## Part 2. The deployment terms, from the fixture bytes -/

/-- The 19 fixed commitments of vk.json, decoded into the carrier (NOT 19 identities). -/
def poseidonFixedCommitmentsReal : Array G₁z :=
  (decodeAll poseidonVkData.fixedCommitmentHex).getD #[]

/-- The 8 sigma commitments of vk.json. -/
def poseidonPermutationCommitmentsReal : Array G₁z :=
  (decodeAll poseidonVkData.permutationCommitmentHex).getD #[]

/-- Fr::DELTA, DERIVED: the multiplicative generator 7 raised to 2^S, S = 32
    (curves/src/bls12_381/fq.rs:492-503 with MULTIPLICATIVE_GENERATOR = 7 at :531). -/
def frDelta : Fr blsR := (7 : Fr blsR) ^ (2 ^ 32)

/-- TERM 3, REAL: the Exec key with the real commitments. Computable. -/
def poseidonVkReal : VerifyingKey (Fr blsR) G₁z :=
  { domain := poseidonDomain,
    fixedCommitments := poseidonFixedCommitmentsReal,
    permutation := { commitments := poseidonPermutationCommitmentsReal },
    cs := poseidonCs,
    csDegree := poseidonVkData.csDegree,
    transcriptRepr := poseidonTranscriptRepr }

/-- TERM 1, REAL: the environment at the computable codec and the real delta. Computable. -/
def poseidonEReal : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecC, field := poseidonFc, delta := frDelta, fewerPointSetsRuntime := false }

/-- TERM 2, REAL, as a function of the SRS trapdoor: `ParamsKZG::verifier_params` (params.rs:313, the constructor test.rs:378 calls) at the constructed
    pairing's `g₂` (exponent 1, the published H2) and at `s · G2`. For a known-trapdoor test SRS
    this is a closed computable term; for the Filecoin SRS `s` is the bound variable of the one
    named hypothesis `SrsEncodes` below. -/
def poseidonParamsAt (s : ZMod blsR) : ParamsVerifierKZG G₁z G2fold :=
  ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd s)

/-- The 256 payload bytes of NEG_S_G2_BASE, read from the deployed artifact. -/
def poseidonNegSG2Bytes : Bytes :=
  ((poseidonVkGen.constants.drop vkNegSG2BaseSlot).take 8).foldl
    (fun acc c => ByteArray.append acc (wordToBytesBE c.2)) Bytes.empty

/-- **THE ONE SRS HYPOTHESIS** (Gap B, stated honestly): the payload's NEG_S_G2 is the encoding of
    `-s · H2`. True for the s of the ceremony; not provable in the tree without the cyclicity of
    the r-torsion of the twist (G-3); a closed computation when s is known. -/
def SrsEncodes (s : ZMod blsR) : Prop :=
  g2foldToEip (Multiplicative.ofAdd s)⁻¹ = poseidonNegSG2Bytes

/-! ## Part 3. The pins, evaluated at the deployment data -/

def frWordHex (x : Fr blsR) : String := hexOf (wordToBytesBE (frWord x))
def wordHex (w : Word256) : String := hexOf (wordToBytesBE w)

def pins : IO Bool := do
  let vk := poseidonVkReal
  let pay := poseidonVkGen
  let c := g1CodecC
  let fixedOk := pay.fixedComms.map g1WordsBytes == vk.fixedCommitments.toList.map c.toEip
  let permOk := pay.permutationComms.map g1WordsBytes == vk.permutation.commitments.toList.map c.toEip
  IO.println s!"sizes: {vk.fixedCommitments.size} fixed, {vk.permutation.commitments.size} sigma (payload {pay.fixedComms.length}, {pay.permutationComms.length})"
  IO.println s!"fixedWords  : {fixedOk}"
  IO.println s!"permWords   : {permOk}"
  let omegaOk := headerWord? pay "omega" == some (frWord vk.domain.omega)
  let omegaInvOk := headerWord? pay "omega_inv" == some (frWord vk.domain.omegaInv)
  IO.println s!"omegaWord   : {omegaOk}"
  IO.println s!"omegaInvWord: {omegaInvOk}"
  let g1BaseBytes := ((pay.constants.drop vkG1BaseSlot).take 4).foldl
    (fun acc c => ByteArray.append acc (wordToBytesBE c.2)) Bytes.empty
  let g1BaseOk := g1BaseBytes == c.toEip pairingC.g₁
  IO.println s!"g1Base      : {g1BaseOk}   (slot {vkG1BaseSlot}; pairingC.g₁ = g1zGen)"
  let g2BaseBytes := ((pay.constants.drop vkG2BaseSlot).take 8).foldl
    (fun acc c => ByteArray.append acc (wordToBytesBE c.2)) Bytes.empty
  let prm := poseidonParamsAt 5
  let g2BaseOk := g2BaseBytes == g2foldToEip prm.nG2Prepared⁻¹
  IO.println s!"g2Base      : {g2BaseOk}   (slot {vkG2BaseSlot}; nG2Prepared⁻¹ = exponent 1 = H2)"
  -- NEG_S_G2: not decidable without the trapdoor; what IS checkable is the byte tie to params.json
  let sHex := poseidonParamsData.sG2Hex
  let xc1 := ByteArray.mk (List.toArray (Nat.toUInt8 (((sHex.data[0]?.map (·.toNat)).getD 0) &&& 0x1f) :: (sHex.data.toList.drop 1).take 47))
  let xc0 := ByteArray.mk ((sHex.data.toList.drop 48).take 48).toArray
  let payX0 := bytesToNatBE (ByteArray.mk ((poseidonNegSG2Bytes.data.toList.drop 0).take 64).toArray)
  let payX1 := bytesToNatBE (ByteArray.mk ((poseidonNegSG2Bytes.data.toList.drop 64).take 64).toArray)
  let negSTie := payX0 == bytesToNatBE xc0 && payX1 == bytesToNatBE xc1
  IO.println s!"negSG2 x-coordinate equals params.json s_g2 x-coordinate (c0, c1): {negSTie}"
  let notGen := poseidonNegSG2Bytes != g2foldToEip (g2foldExp 1)⁻¹
  IO.println s!"negSG2 is NOT -H2 (so sG2 := g₂ is refuted by bytes): {notGen}"
  let deltaStr := poseidonInputs.frDelta
  let deltaOk := deltaStr == Midfall.Generator.QuotientFoldCompute.u256String (frWord frDelta)
  IO.println s!"delta       : {deltaOk}   (inputs.frDelta = {deltaStr})"
  let deltaOld := deltaStr == Midfall.Generator.QuotientFoldCompute.u256String (frWord (2 : Fr blsR))
  IO.println s!"delta pin at the placeholder 2 (must be false): {deltaOld}"
  -- the falsifier of fixedWords: the tree's 19 identities
  let fixedOld := pay.fixedComms.map g1WordsBytes ==
    (Array.replicate 19 (1 : G₁z)).toList.map c.toEip
  IO.println s!"fixedWords at 19 identities (must be false): {fixedOld}"
  pure (fixedOk && permOk && omegaOk && omegaInvOk && g1BaseOk && g2BaseOk && negSTie && notGen
        && deltaOk && !deltaOld && !fixedOld)

end RefKey

#eval RefKey.pins    -- expect true

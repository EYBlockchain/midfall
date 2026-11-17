/-
  Midfall.Instances.PoseidonEnv

  D.2 (ALG - PORT): the Lean verifier's side of the deployment as FIVE PURE TERMS - poseidonE,
  poseidonParams, poseidonVkExec : VerifyingKey (Fr blsR) G₁z, poseidonSG2, poseidonEncG2 - read
  out of fixtures/conformance/poseidon/vk.json and .../params.json, in the curve model that
  Instances/HoldsFinal.lean's holds_exhibited is stated over.

  WHICH WORLD THIS IS - THE CARD'S VERIFY-FIRST, ANSWERED BY MEASUREMENT AND NOT BY INFERENCE.
  Decoding a compressed point INTO this model is NOT computable, and it is worse than noncomputable.
  Two independent walls, both measured on this branch:

  1. g1zOfEip? is noncomputable (Instances/G1Agreement.lean:1995, Classical.choose), and its own
     docstring says why: an element of G₁z = Subgroup.zpowers g₁ (G1Agreement.lean:1814) is a point
     PAIRED WITH A PROOF that it is a power of the generator, and the only way the tree knows to
     produce that proof is to name the exponent. So the whole g1CodecZ record is noncomputable and
     NOTHING that projects from it can be compiled. Evaluating the isSome of a compressed decode in
     the VM is refused by the compiler, verbatim:

       error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as
         'noncomputable' because it depends on 'g1CodecZ', which is 'noncomputable'

  2. g1CodecZ.ofCompressed? := fun _ => none (G1Agreement.lean:2006). The compressed decoder is a
     PLACEHOLDER THAT DECODES NOTHING, so the 48-byte hexes in vk.json cannot reach G₁z even
     noncomputably. This is a v1 placeholder V2 has inherited and it is a STANDING GAP, not a D.2
     to-do: any card that wants the deployment's commitments AS CARRIER ELEMENTS needs a real
     ofCompressed? first, and a real one needs an r-torsion-to-zpowers route the tree does not have
     (r-torsion is decidable - g1InSubgroup_iff, G1Agreement.lean:1167 - but 'X in zpowers g₁' is a
     discrete log as literally typed).

  SO THIS FILE SHIPS THE FALLBACK SHAPE THE CARD SANCTIONS: the terms are definable, the point
  FIELDS are carried by their COUNT and by their BYTES, and the KATs cover every field vk.json
  actually supplies. Three deliberate choices follow from that world and are worth naming:

  * poseidonVkExec is kept COMPUTABLE. The commitment arrays are Array.replicate n (1 : G₁z) -
    computable, because 1 is the carrier's identity and its membership proof is zpow at exponent 0
    - and the codec route is stated as a THEOREM over them (poseidonVkCodecRoute), not as the
    definition. Defining the VK through g1CodecZ would make the whole VK noncomputable and take it
    out of reach of D.3's replay and WP-I2's Valid, which is the opposite of what this card is for.
    The theorem says the two are the same term TODAY: the decoder answers none for every input, so
    .getD 1 is 1 definitionally - and it is refuted the moment a real ofCompressed? lands, which is
    the right direction for a placeholder to fail.
  * The point CONTENT is not lost, only its carrier. Instances/Bls12_381.lean has a COMPUTABLE
    compressed decoder, G1Affine.ofCompressed?, into a real affine point (a genuine square root,
    p = 3 mod 4). Gate 8 re-encodes all 27 fixture commitments and gate 9 checks their COORDINATES
    against the EIP-2537 words D.1 parsed out of the deployed artifact. So vk.json and the .sol
    fixture are pinned to denote the same 27 curve points, in the VM, at the point type that can
    hold them - which is as much of the card's "re-encodes to its hex" ask as this world allows.
  * poseidonEncG2 IS g2foldToEip, the encoder holds_exhibited is stated over, and that is PINNED BY
    RFL THEOREMS rather than asserted in prose: poseidonEncG2_isTheExhibitEncoder (= g2CodecFold.toEip)
    and poseidonHolds_isTheExhibitsClause, which says the exhibit's Holds binder and this file's
    are the SAME PROPOSITION, so the non-vacuity exhibit transfers verbatim.

  TWO PREMISE GAPS, both the card's own stop condition, both reported to the orchestrator before
  this file was written and neither of them worked around:

  A. vk.json DOES NOT CONTAIN the constraint-system data VerifyingKey needs. The missing keys, by
     name: gates (the whole Vec<Gate<F>>), lookups (vk.json has num_lookups: 1, the COUNT, and no
     BatchedArgument), trashcans (same: num_trashcans: 1 only), and permutation.columns (absent;
     permutation_commitments_compressed_hex gives the chunk COUNT, which pins the column count only
     to [22, 24] under divCeil _ 3). The orchestrator asked whether D.1's poseidonPlanV2.meta_ can
     supply them: MEASURED, NO - the typed-in meta has permutationColumns = [], adviceQueries = [],
     instanceQueries = [], numFixeds = 0, permutationChunkLen = 0, and it has no gates field at all.
     It does agree with vk.json on numLookups = 1, numTrashcans = 1 and numSimpleSelectors = 4, and
     gate 14 pins that agreement. CONSEQUENCE, stated and gated and NOT papered over: with gates = #[]
     the ported ConstraintSystem.degree recomputes to 3 while the fixture says cs_degree = 5, so
     VerifyingKey.WellFormed.csDegreeMatches is NOT dischargable from vk.json. poseidonVkExec is
     therefore delivered WITHOUT a WellFormed proof, and gate 13 is a pin on the gap: it goes FALSE
     the day someone fills gates from a real source, which is when WellFormed becomes reachable. No
     gate data was invented. Also open, same cause: unblindedAdviceColumns, generalColumnAnnotations,
     constants, minimumDegree - vk.json has none of them, so they are ConstraintSystem.default's
     empties.
  B. params.json carries the deployment's s_g2_compressed_hex, and G2fold = Exp blsR is the EXPONENT
     carrier, so naming s·G₂ is a discrete log in G₂. poseidonSG2 is therefore the assumed pairing's
     own g₂ - the same substitution curveParams makes - and poseidonParams.sG2Prepared = poseidonSG2
     is rfl about that substitution and NOT a check against params.json. The byte-level facts
     params.json DOES support are gated instead (gate 11): widths, max_k = k, and that
     n_g2_compressed_hex is g2_compressed_hex with the sign bit of byte 0 flipped, which is the
     file's own note field made checkable.

  THE DOMAIN IS NOT frFc's DOMAIN, AND THAT IS A FINDING ABOUT THE TREE. frFc
  (Assumptions/TwoAdicity.lean:371) takes rootOfUnity := frRootOfUnity = 5^((r-1)/2^32). Run the
  ported constructor at it and the size-64 domain's omega is
  0xe4840ac57f86f5e293b1d67bc8de5d9a12a70a615d0b8e4d2fc5e69ac5db47f. vk.json's omega_be_hex is
  0x45af6345ec055e4d14a1e27164d8fdbd2d967f4be2f951558140d032f0a9ee53. Both are PRIMITIVE 64th roots
  (each has w^64 = 1 and w^32 <> 1 - gated), so they differ by an odd power: the tree's generator of
  the 2^32-nd roots of unity is not the one halo2curves used. The fixture is the authority for the
  deployment, so poseidonFc is frFc with the root REPAIRED: poseidonRootExponent is the odd i < 64
  with (frRootOfUnity^2^26)^i = omega, found by a 64-case search the VM runs and not transcribed,
  and poseidonRootOfUnity := frRootOfUnity^i. Then EvaluationDomain.new poseidonFc csDegree k
  reproduces vk.json's omega_be_hex AND omega_inv_be_hex AND n, k, extended_k, quotient_poly_degree
  exactly (gates 2, 3). WHAT THAT DOES NOT PIN, recorded because an unpinned field is where a later
  card will quietly disagree with the artifact: extendedOmega, extendedOmegaInv and tEvaluations
  depend on the root at the 2^24 level, and vk.json has no extended_omega key, so they are
  consistent with the repaired root and NOT verified against the deployment. i is determined mod 4
  only; the search returns the least positive representative (61, gated), and any odd i' = i [4]
  gives the same omega and a different extendedOmega.

  WHAT IS NOT HERE, and why. No Yul, no generator, no pairing implementation - the headline
  quantifies over product, so this file only names the codecs and the data. No transcriptRepr
  computation: R-1 imports it, and it arrives here as vk.json's transcript_repr_be_hex. No
  poseidonRender: that is C.1, and it consumes these five terms plus D.1's five.
-/
import Midfall.Assumptions.CurvePairing
import Midfall.Instances.Bls12_381
import Midfall.Instances.G1Agreement
import Midfall.Instances.G2Codec
import Midfall.Instances.PoseidonInputs
import Midfall.Conformance.Bundle
import Midfall.Common.Json

namespace Midfall.Instances.PoseidonEnv

open Midfall Midfall.Halo2 Midfall.Conformance
open Midfall.Instances Midfall.Assumptions Midfall.Yul

/-! ## 1. The fixtures, reached purely -/

/-- vk.json, baked in at build time. include_str resolves relative to THIS file and not to the CWD
    (measured in D.1, re-measured here), so the path is ../../fixtures/... from Midfall/Instances/. -/
def vkText : String := include_str "../../fixtures/conformance/poseidon/vk.json"

/-- params.json, same channel. -/
def paramsText : String := include_str "../../fixtures/conformance/poseidon/params.json"

/-- The one totaliser this file needs: a failed parse leaves the EMPTY payload behind, and gate 1 is
    what reddens if it is ever taken. Same shape as D.1's poseidonVkUnparsed, for the same reason: a
    default a parse failure can reach must be obviously broken, not plausibly fine. -/
def fromExcept {ε : Type} {α : Type} (e : Except ε α) (d : α) : α :=
  match e with | .ok a => a | .error _ => d

/-- col_idx is Option<usize> in Rust, and the exporter writes null for a selector that was converted
    away. jNat would call that an error, so the option gets its own strict reader. -/
def jOptNat (o : JValue) (k : String) : Except String (Option Nat) :=
  match o.getObjVal? k with
  | .ok Lean.Json.null => .ok none
  | .ok v => do pure (some (← jNatVal v))
  | .error e => .error e

/-- A hex field whose width the schema fixes. jHexBytes' would accept any even length, and R-20 is
    the record of what a width slip costs, so the width is asserted here. -/
def jHexFixed (o : JValue) (k : String) (nBytes : Nat) : Except String Bytes :=
  do jHexBytes (← jString o k) nBytes

/-- The vk.json payload as data. Every field is read with a strict accessor and nothing is coerced.
    The record keeps the JSON's shapes - (column, rotation) pairs, phases as Nat - rather than the
    Exec record's, so the KATs compare against the file and not against a translation of it. -/
structure PoseidonVkData where
  k : Nat
  n : Nat
  extendedK : Nat
  csDegree : Nat
  quotientPolyDegree : Nat
  numFixedColumns : Nat
  numAdviceColumns : Nat
  numInstanceColumns : Nat
  numChallenges : Nat
  numLookups : Nat
  numTrashcans : Nat
  numCommittedInstances : Nat
  nbPublicInputs : Nat
  scalarNumBits : Nat
  truncatedChallenges : Bool
  adviceColumnPhases : Array Nat
  adviceQueries : Array (Nat × Int)
  instanceQueries : Array (Nat × Int)
  fixedQueries : Array (Nat × Int)
  selectorFlags : Array SelectorFlag
  omegaBytes : Bytes
  omegaInvBytes : Bytes
  transcriptReprBytes : Bytes
  fixedCommitmentHex : Array Bytes
  permutationCommitmentHex : Array Bytes

def jSelectorFlags (o : JValue) (k : String) : Except String (Array SelectorFlag) := do
  let a ← jArray o k
  a.mapM fun f => do pure { isSimple := (← jBool f "is_simple"), colIdx := (← jOptNat f "col_idx") }

def poseidonVkData? : Except String PoseidonVkData := do
  let j ← jParse vkText
  pure {
    k := (← jNat j "k"), n := (← jNat j "n"), extendedK := (← jNat j "extended_k"),
    csDegree := (← jNat j "cs_degree"),
    quotientPolyDegree := (← jNat j "quotient_poly_degree"),
    numFixedColumns := (← jNat j "num_fixed_columns"),
    numAdviceColumns := (← jNat j "num_advice_columns"),
    numInstanceColumns := (← jNat j "num_instance_columns"),
    numChallenges := (← jNat j "num_challenges"),
    numLookups := (← jNat j "num_lookups"),
    numTrashcans := (← jNat j "num_trashcans"),
    numCommittedInstances := (← jNat j "num_committed_instances"),
    nbPublicInputs := (← jNat j "nb_public_inputs"),
    scalarNumBits := (← jNat j "scalar_num_bits"),
    truncatedChallenges := (← jBool j "truncated_challenges"),
    adviceColumnPhases := (← jNatArr j "advice_column_phase"),
    adviceQueries := (← jQueryArr j "advice_queries"),
    instanceQueries := (← jQueryArr j "instance_queries"),
    fixedQueries := (← jQueryArr j "fixed_queries"),
    selectorFlags := (← jSelectorFlags j "selector_flags"),
    omegaBytes := (← jHexFixed j "omega_be_hex" 32),
    omegaInvBytes := (← jHexFixed j "omega_inv_be_hex" 32),
    transcriptReprBytes := (← jHexFixed j "transcript_repr_be_hex" 32),
    fixedCommitmentHex := (← jHexArr j "fixed_commitments_compressed_hex"),
    permutationCommitmentHex := (← jHexArr j "permutation_commitments_compressed_hex") }

/-- The empty payload: every count 0, every list empty. A parse failure therefore cannot masquerade
    as a small key - poseidonVkExec built from it has an empty CS and a zero domain, and gate 1
    fails long before anything downstream could be believed. -/
def poseidonVkDataUnparsed : PoseidonVkData :=
  { k := 0, n := 0, extendedK := 0, csDegree := 0, quotientPolyDegree := 0,
    numFixedColumns := 0, numAdviceColumns := 0, numInstanceColumns := 0, numChallenges := 0,
    numLookups := 0, numTrashcans := 0, numCommittedInstances := 0, nbPublicInputs := 0,
    scalarNumBits := 0, truncatedChallenges := false, adviceColumnPhases := #[],
    adviceQueries := #[], instanceQueries := #[], fixedQueries := #[], selectorFlags := #[],
    omegaBytes := ByteArray.mk #[], omegaInvBytes := ByteArray.mk #[],
    transcriptReprBytes := ByteArray.mk #[], fixedCommitmentHex := #[],
    permutationCommitmentHex := #[] }

def poseidonVkData : PoseidonVkData := fromExcept poseidonVkData? poseidonVkDataUnparsed

/-! ## 2. params.json, as data -/

structure PoseidonParamsData where
  curve : String
  format : String
  schema : Nat
  maxK : Nat
  g1Hex : Bytes
  g2Hex : Bytes
  nG2Hex : Bytes
  sG2Hex : Bytes

def poseidonParamsData? : Except String PoseidonParamsData := do
  let j ← jParse paramsText
  pure {
    curve := (← jString j "curve"),
    format := (← jString j "format"),
    schema := (← jNat j "schema"),
    maxK := (← jNat j "max_k"),
    g1Hex := (← jHexFixed j "g1_compressed_hex" 48),
    g2Hex := (← jHexFixed j "g2_compressed_hex" 96),
    nG2Hex := (← jHexFixed j "n_g2_compressed_hex" 96),
    sG2Hex := (← jHexFixed j "s_g2_compressed_hex" 96) }

def poseidonParamsData : PoseidonParamsData := fromExcept poseidonParamsData?
  { curve := "", format := "", schema := 0, maxK := 0, g1Hex := ByteArray.mk #[],
    g2Hex := ByteArray.mk #[], nG2Hex := ByteArray.mk #[], sG2Hex := ByteArray.mk #[] }

/-- The leading byte of a point encoding, as a Nat (0 when the string is empty). -/
def byte0 (b : Bytes) : Nat := (b.data[0]?.map (fun u => u.toNat)).getD 0

/-! ## 3. The field, the root repair, and the domain -/

/-- vk.json's omega_be_hex as a field element. The cast is faithful because the value is below blsR,
    which gate 3 checks rather than assumes. -/
def poseidonOmega : Fr blsR := (bytesToNatBE poseidonVkData.omegaBytes : Fr blsR)

/-- The odd exponent i < 64 with (frRootOfUnity ^ 2^26) ^ i = poseidonOmega, found by search.
    frRootOfUnity ^ 2^26 is the tree's own primitive 64th root - what EvaluationDomain.new frFc 5 6
    would have produced - so this IS the change of generator between the tree and the deployment.
    Gate 12 asserts the search found something and that the answer is 61. -/
def poseidonRootExponent : Nat :=
  ((List.range 64).filter (fun i => (frRootOfUnity ^ 2 ^ 26) ^ i == poseidonOmega)).head!

/-- THE REPAIRED ROOT: a primitive 2^32-nd root of unity whose 2^26-th power is the deployment's. -/
def poseidonRootOfUnity : Fr blsR := frRootOfUnity ^ poseidonRootExponent

/-- The deployment's field constants: frFc with ONLY the root replaced. numBits, s and zeta are the
    tree's, and numBits is gated against vk.json's scalar_num_bits. -/
def poseidonFc : FieldConsts (Fr blsR) := { frFc with rootOfUnity := poseidonRootOfUnity }

/-- The domain, as the ported constructor computes it at the repaired constants. -/
def poseidonDomain? : Except Fault (EvaluationDomain (Fr blsR)) :=
  EvaluationDomain.new poseidonFc poseidonVkData.csDegree poseidonVkData.k

/-- The zero domain, reached only if the constructor errors. Gate 2 requires poseidonDomain? to be
    .ok, so no green gate ever ran on this. -/
def poseidonDomainUnparsed : EvaluationDomain (Fr blsR) :=
  { n := 0, k := 0, extendedK := 0, omega := 0, omegaInv := 0, extendedOmega := 0,
    extendedOmegaInv := 0, gCoset := 0, gCosetInv := 0, quotientPolyDegree := 0,
    ifftDivisor := 0, extendedIfftDivisor := 0, tEvaluations := #[], barycentricWeight := 0 }

def poseidonDomain : EvaluationDomain (Fr blsR) :=
  fromExcept poseidonDomain? poseidonDomainUnparsed

/-- vk.json's transcript_repr_be_hex, imported and not recomputed (R-1). -/
def poseidonTranscriptRepr : Fr blsR := (bytesToNatBE poseidonVkData.transcriptReprBytes : Fr blsR)

/-! ## 4. The constraint system, from the keys vk.json has -/

/-- An advice column carries its phase in its kind (Exec/Circuit structural choice 2), and the phase
    is vk.json's advice_column_phase[i]. -/
def poseidonAdviceColumn (idx : Nat) : Column :=
  { index := idx, columnType := Any.advice { phase := { val :=
      (poseidonVkData.adviceColumnPhases[idx]?.getD 0) } } }

/-- A JSON rotation is an i32, so it becomes Rotation.value and never Rotation.cur: the port's own
    header records that the two are distinct inhabitants here and one value in Rust, and an importer
    that collapsed them would silently deduplicate queries the reference keeps apart. -/
def poseidonRotation (r : Int) : Rotation := Rotation.value r

def poseidonAdviceQueries : Array (Column × Rotation) :=
  poseidonVkData.adviceQueries.map fun (c, r) => (poseidonAdviceColumn c, poseidonRotation r)

def poseidonInstanceQueries : Array (Column × Rotation) :=
  poseidonVkData.instanceQueries.map fun (c, r) =>
    ({ index := c, columnType := Any.instance }, poseidonRotation r)

def poseidonFixedQueries : Array (Column × Rotation) :=
  poseidonVkData.fixedQueries.map fun (c, r) =>
    ({ index := c, columnType := Any.fixed }, poseidonRotation r)

/-- num_advice_queries[i] is how many distinct queries advice column i has: circuit.rs's
    query_advice_index bumps it exactly when the (column, rotation) pair is new. So it is derivable
    from advice_queries, and it is derived here rather than invented. -/
def poseidonNumAdviceQueries : Array Nat :=
  (List.range poseidonVkData.numAdviceColumns).toArray.map fun i =>
    (poseidonVkData.adviceQueries.filter (fun q => q.1 == i)).size

/-- THE CONSTRAINT SYSTEM. Filled from vk.json where vk.json has the data and from
    ConstraintSystem.default where it does not. The four fields with no source are named in the
    header (gap A): gates, lookups, trashcans, permutation.columns. numSelectors is NOT one of them:
    the reference's selector() pushes one flag per selector, so num_selectors = selector_flags.len(),
    and that is how it is derived here. -/
def poseidonCs : ConstraintSystem (Fr blsR) :=
  { ConstraintSystem.default with
    numFixedColumns := poseidonVkData.numFixedColumns
    numAdviceColumns := poseidonVkData.numAdviceColumns
    numInstanceColumns := poseidonVkData.numInstanceColumns
    numSelectors := poseidonVkData.selectorFlags.size
    selectorFlags := poseidonVkData.selectorFlags
    numChallenges := poseidonVkData.numChallenges
    adviceColumnPhase := poseidonVkData.adviceColumnPhases.map fun ph => { val := ph }
    adviceQueries := poseidonAdviceQueries
    numAdviceQueries := poseidonNumAdviceQueries
    instanceQueries := poseidonInstanceQueries
    fixedQueries := poseidonFixedQueries }

/-! ## 5. The commitments, and the codec route stated as a theorem -/

/-- 19 copies of the identity of G₁z. NOT a claim that the deployment's fixed commitments are the
    identity - a claim about what this file can put in that field, which is nothing until
    g1CodecZ.ofCompressed? stops being fun _ => none. The COUNT is the deployment's, and the bytes
    are carried next to it and pinned against the artifact by gates 8 and 9. -/
def poseidonFixedCommitments : Array G₁z :=
  Array.replicate poseidonVkData.numFixedColumns (1 : G₁z)

/-- The permutation chunk count, from the number of compressed commitments vk.json lists. -/
def poseidonPermutationCommitments : Array G₁z :=
  Array.replicate poseidonVkData.permutationCommitmentHex.size (1 : G₁z)

/-- **THE CODEC ROUTE, ELEMENTWISE.** The card's "the terms are still definable through the
    codec", discharged the way this world allows. For EVERY byte string - so for every one of the 27
    fixture commitments - decoding through g1CodecZ and falling back to the identity IS the identity,
    definitionally, because the placeholder decoder answers none. Stated elementwise rather than as an
    array equality: the array-level rfl does not fire (measured), because Array.map over the parsed
    19-element literal does not reduce inside isDefEq, and an induction over ByteArray would be
    plumbing rather than content. The sizes are gated instead (gate 4). Refuted the moment a real
    ofCompressed? is installed, which is the direction a placeholder should fail in. -/
theorem poseidonVkCodecRoute (b : Bytes) :
    (g1CodecZ.ofCompressed? b).getD (1 : G₁z) = (1 : G₁z) := rfl

/-! ## 6. THE FIVE TERMS -/

/-- **TERM 3 OF 5, the one the card names.** The Exec verifying key over the exhibit's carrier.
    COMPUTABLE on purpose - see the header - so D.3 and WP-I2 can run projections of it in the VM. -/
def poseidonVkExec : VerifyingKey (Fr blsR) G₁z :=
  { domain := poseidonDomain,
    fixedCommitments := poseidonFixedCommitments,
    permutation := { commitments := poseidonPermutationCommitments },
    cs := poseidonCs,
    csDegree := poseidonVkData.csDegree,
    transcriptRepr := poseidonTranscriptRepr }

/-- **TERM 1 OF 5.** The verifier environment at the exhibit's G1 codec. Noncomputable because
    g1CodecZ is, exactly like curveE; the pin below is what says it is the SAME codec and not a
    look-alike. field is the repaired constants of section 3, so the environment's own field record
    is the one whose root reproduces the deployment's omega. -/
noncomputable def poseidonE : VerifierEnv blsR G₁z G2fold blsGT :=
  { g1 := g1CodecZ, field := poseidonFc, delta := 2, fewerPointSetsRuntime := false }

/-- **TERM 4 OF 5.** The Surface's sG2gen slot for the deployment. Gap B: the deployment's s·G₂ is in
    params.json only as s_g2_compressed_hex, and G2fold = Exp blsR is the exponent carrier, so
    naming it is a discrete log in G₂. This is the assumed pairing's generator - the same
    substitution curveParams makes at the fixture - and it is NOT checked against that hex. -/
noncomputable def poseidonSG2 : G2fold := bls12_381Pairing.g₂

/-- **TERM 2 OF 5.** The KZG verifier parameters. nG2Prepared = sG2⁻¹ is the relation params.json's
    own note states ("n_g2 is -g2, the negated generator the final pairing uses"), and the byte half
    of that claim is gated at gate 11; sG2Prepared inherits gap B. -/
noncomputable def poseidonParams : ParamsVerifierKZG G₁z G2fold :=
  { sG2 := poseidonSG2, nG2Prepared := poseidonSG2⁻¹, sG2Prepared := poseidonSG2 }

/-- **TERM 5 OF 5.** The abstract G2 encoder, AT THE EXHIBIT'S FUNCTION. g2foldToEip is the encoder of
    g2CodecFold, and g2CodecFold is the second codec holds_exhibited quantifies Eip2537.Holds over
    (Instances/HoldsFinal.lean:57), and it is also what Instances/CurveSurface.lean:154 installs at
    encG2. This is a def and not a copy: the three are the same term, and the theorems below are the
    kernel saying so. -/
def poseidonEncG2 : G2fold → Bytes := g2foldToEip

/-! ## 7. THE CODEC IDENTITY PINS -/

/-- poseidonE's G1 codec IS g1CodecZ, the codec of the exhibit. By rfl, i.e. by the kernel and not
    by a tactic. -/
theorem poseidonE_g1_isTheExhibitCodec : poseidonE.g1 = g1CodecZ := rfl

/-- poseidonEncG2 IS the encoder of g2CodecFold, the G2 codec of the exhibit. -/
theorem poseidonEncG2_isTheExhibitEncoder : poseidonEncG2 = g2CodecFold.toEip := rfl

/- poseidonEncG2 IS what the curve Surface installs at encG2. That pin MOVED to
    Instances/CurveSurface.lean (C.1, curveEncG2_isPoseidonEncG2): citing curveSurface from here
    imported Midfall.Instances.CurveSurface, whose transitive closure carries ten of the AVOID 14
    retired modules, and C.1's cone root has to import THIS file. The pin is unchanged in content -
    it is the same rfl, restated where the term it names lives - and dropping it would have left the
    V2 cone importing retired v1. -/

/-- **THE TRANSFER, AND THE ANSWER TO THE CARD'S ITEM 5.** For every product, the exhibit's Holds
    binder and this file's are the SAME PROPOSITION - not equivalent, identical. So holds_exhibited
    discharges this file's binder with no transport and the non-vacuity exhibit transfers verbatim to
    the deployment. Had poseidonEncG2 or poseidonE.g1 been restated instead of cited, this would not
    elaborate. -/
theorem poseidonHolds_isTheExhibitsClause (product : PairingProduct) :
    Eip2537.Holds poseidonE.g1 ⟨poseidonEncG2⟩ product =
      Eip2537.Holds g1CodecZ g2CodecFold product := rfl

/-- The existential form of the same transfer, which is the shape holds_exhibited actually closes. -/
theorem poseidonHolds_transfers :
    (∃ product : PairingProduct, Eip2537.Holds poseidonE.g1 ⟨poseidonEncG2⟩ product) ↔
      (∃ product : PairingProduct, Eip2537.Holds g1CodecZ g2CodecFold product) :=
  ⟨fun ⟨p, h⟩ => ⟨p, h⟩, fun ⟨p, h⟩ => ⟨p, h⟩⟩

/-- The parameters are read off the assumed pairing, so the two generator clauses of EnvAgrees
    (nG2Prepared = P.g₂⁻¹, sG2Prepared = sG2gen) are rfl here exactly as they are at curveParams. -/
theorem poseidonParams_areTheAssumedGenerators :
    poseidonParams.sG2 = bls12_381Pairing.g₂ ∧ poseidonParams.nG2Prepared = bls12_381Pairing.g₂⁻¹ :=
  ⟨rfl, rfl⟩

end Midfall.Instances.PoseidonEnv
namespace Midfall.Instances.PoseidonEnvKats

open Midfall Midfall.Halo2 Midfall.Conformance
open Midfall.Instances Midfall.Assumptions Midfall.Yul
open Midfall.Instances.PoseidonEnv
open Midfall.Instances.PoseidonInputs

/-- A G1 commitment as the four words it is, so the two fixtures can be compared STRUCTURALLY
    without asking G1Words for a BEq it does not have (D.1's pv/g1 adapters, same reason). -/
def wordPair (w : Midfall.Generator.G1Words) : Nat × Nat :=
  (w.xHi.toNat * 2 ^ 256 + w.xLo.toNat, w.yHi.toNat * 2 ^ 256 + w.yLo.toNat)

/-- The coordinates a compressed encoding denotes, at the ONE codec in the tree that can decode
    compressed bytes computably (Instances/Bls12_381.lean:76). none for a non-point. -/
def decompressed (b : Bytes) : Option (Nat × Nat) :=
  (G1Affine.ofCompressed? b).map fun P => (P.x.val, P.y.val)

/-- GATE 1 (the parse, and the widths). Every key vk.json is asked for is there, every commitment hex
    is 48 bytes, every field hex is 32, and the counts the other gates read are the file's. This is
    the gate that reddens if poseidonVkDataUnparsed is ever what the parse returned: the empty payload
    has zero-width hexes and zero counts, so the whole conjunction fails. -/
def poseidonVkParse_ok : Bool :=
  poseidonVkData?.isOk && poseidonParamsData?.isOk
    && poseidonVkData.k == 6 && poseidonVkData.n == 64 && poseidonVkData.extendedK == 8
    && poseidonVkData.csDegree == 5 && poseidonVkData.quotientPolyDegree == 4
    && poseidonVkData.omegaBytes.size == 32 && poseidonVkData.omegaInvBytes.size == 32
    && poseidonVkData.transcriptReprBytes.size == 32
    && poseidonVkData.fixedCommitmentHex.size == 19
    && poseidonVkData.permutationCommitmentHex.size == 8
    && poseidonVkData.fixedCommitmentHex.all (fun b => b.size == 48)
    && poseidonVkData.permutationCommitmentHex.all (fun b => b.size == 48)
    && poseidonVkData.adviceColumnPhases.size == 8
    && poseidonVkData.selectorFlags.size == 19 && poseidonVkData.scalarNumBits == 255
    && poseidonVkData.truncatedChallenges && poseidonVkData.numCommittedInstances == 1
    && poseidonVkData.nbPublicInputs == 1
    && poseidonVkData.numLookups == 1 && poseidonVkData.numTrashcans == 1

/-- GATE 2 (the card's k and n). The VK's own domain carries vk.json's k, n and extended_k, the
    VerifyingKey.n accessor agrees, n really is 2^k (WellFormed.domainConsistent's first conjunct),
    and the zero fallback was not taken. -/
def poseidonVk_k_n_ok : Bool :=
  poseidonDomain?.isOk && poseidonVkExec.domain.k == poseidonVkData.k
    && poseidonVkExec.domain.n == poseidonVkData.n && poseidonVkExec.n == poseidonVkData.n
    && poseidonVkExec.domain.extendedK == poseidonVkData.extendedK
    && poseidonVkExec.domain.k == 6 && poseidonVkExec.domain.n == 64
    && poseidonVkExec.domain.n == 2 ^ poseidonVkExec.domain.k
    && poseidonVkExec.domain.extendedK == 8 && poseidonVkExec.domain.omega != 0

/-- GATE 3 (the card's omega). The domain's omega and omega_inv are vk.json's, byte for byte, both
    below blsR so the casts are faithful, the omega is a PRIMITIVE 64th root (order 64, not a
    divisor of it), and omega_inv really is its inverse. The primitive half is what stops a
    degenerate omega = 1 from passing, which is the bug class TwoAdicity refutes at fxDomDegenerate. -/
def poseidonVk_omega_ok : Bool :=
  poseidonVkExec.domain.omega.val == bytesToNatBE poseidonVkData.omegaBytes
    && poseidonVkExec.domain.omegaInv.val == bytesToNatBE poseidonVkData.omegaInvBytes
    && bytesToNatBE poseidonVkData.omegaBytes < blsR
    && bytesToNatBE poseidonVkData.omegaInvBytes < blsR
    && poseidonVkExec.domain.omega == poseidonOmega
    && poseidonVkExec.domain.omega ^ 64 == 1 && poseidonVkExec.domain.omega ^ 32 ≠ 1
    && poseidonVkExec.domain.omega ≠ 1
    && poseidonVkExec.domain.omegaInv == poseidonVkExec.domain.omega⁻¹
    && poseidonVkExec.domain.omega * poseidonVkExec.domain.omegaInv == 1

/-- GATE 4 (the card's column counts). Every count in the CS is vk.json's and the commitment arrays
    have the lengths vk.json implies. WellFormed.fixedCommitmentsMatch IS discharged here, as a fact
    about the term rather than a structure proof. WellFormed.permutationCommitmentsMatch is NOT: with
    no permutation columns in the fixture, divCeil 0 3 = 0 against 8 commitments, and gate 13 pins
    that failure instead of hiding it. -/
def poseidonVk_columnCounts_ok : Bool :=
  poseidonCs.numFixedColumns == 19 && poseidonCs.numAdviceColumns == 8
    && poseidonCs.numInstanceColumns == 2 && poseidonCs.numChallenges == 0
    && poseidonCs.numSelectors == 19 && poseidonCs.selectorFlags.size == 19
    && poseidonCs.adviceColumnPhase.size == 8 && poseidonCs.adviceColumnPhase == Array.mk
      (List.replicate 8 ({ val := 0 } : Phase))
    && poseidonCs.numSimpleSelectors == 4
    && poseidonVkExec.fixedCommitments.size == poseidonCs.numFixedColumns
    && poseidonVkExec.fixedCommitments.size == poseidonVkData.fixedCommitmentHex.size
    && poseidonVkExec.permutation.commitments.size == 8
    && poseidonCs.numFixedColumns == poseidonVkData.fixedCommitmentHex.size
    && poseidonCs.numAdviceColumns == poseidonVkData.adviceColumnPhases.size

/-- GATE 5 (the card's query lists). advice_queries, instance_queries and fixed_queries read back out
    of the CS as exactly the (column, rotation) pairs vk.json lists - columns by index, rotations as
    signed ints through the port's own Rotation.int, so nothing was collapsed into Rotation.cur. The
    derived num_advice_queries is the per-column histogram the reference bumps, and noRotInst (every
    instance query at rotation 0) is checked rather than assumed. -/
def poseidonVk_queries_ok : Bool :=
  (poseidonCs.adviceQueries.map fun q => (q.1.index, q.2.int)) == poseidonVkData.adviceQueries
    && (poseidonCs.instanceQueries.map fun q => (q.1.index, q.2.int))
        == poseidonVkData.instanceQueries
    && (poseidonCs.fixedQueries.map fun q => (q.1.index, q.2.int)) == poseidonVkData.fixedQueries
    && poseidonCs.adviceQueries.size == 11 && poseidonCs.instanceQueries.size == 2
    && poseidonCs.fixedQueries.size == 19
    && poseidonCs.numAdviceQueries == #[2, 2, 2, 1, 1, 1, 1, 1]
    && poseidonCs.instanceQueries.toList.all (fun q => q.2.int == 0)
    && poseidonCs.adviceQueries.toList.all (fun q => q.2.int == 0 || q.2.int == 1)
    && poseidonCs.adviceQueries.toList.all (fun q =>
      q.1.columnType == Any.advice { phase := { val := 0 } })
    && poseidonCs.fixedQueries.toList.all (fun q => q.1.columnType == Any.fixed)
    && poseidonCs.instanceQueries.toList.all (fun q => q.1.columnType == Any.instance)

/-- GATE 6 (cs_degree, and the domain half of domainConsistent). The cached csDegree is vk.json's 5,
    the domain's quotient degree is vk.json's 4, and 4 == 5 - 1 is SupportedV2.hLimbs and
    WellFormed.domainConsistent's second conjunct - the two clauses of WellFormed that DO survive
    vk.json. -/
def poseidonVk_csDegree_ok : Bool :=
  poseidonVkExec.csDegree == 5 && poseidonVkExec.csDegree == poseidonVkData.csDegree
    && poseidonVkExec.domain.quotientPolyDegree == 4
    && poseidonVkExec.domain.quotientPolyDegree == poseidonVkData.quotientPolyDegree
    && poseidonVkExec.domain.quotientPolyDegree == poseidonVkExec.csDegree - 1

/-- GATE 7 (transcript_repr, imported and not recomputed: R-1). The VK's transcriptRepr is vk.json's
    transcript_repr_be_hex, canonically below blsR, and it is not the zero element a failed cast
    would leave behind. -/
def poseidonVk_transcriptRepr_ok : Bool :=
  poseidonVkExec.transcriptRepr.val == bytesToNatBE poseidonVkData.transcriptReprBytes
    && bytesToNatBE poseidonVkData.transcriptReprBytes < blsR
    && poseidonVkExec.transcriptRepr ≠ 0

/-- GATE 8 (the point KAT this world allows). All 27 compressed commitments - 19 fixed, 8
    permutation - decompress at G1Affine and RE-ENCODE TO THE HEX THEY CAME FROM, byte for byte.
    This is the card's item 4, run at the codec that can decode compressed bytes instead of the one
    that cannot, and it is what says the hexes are real points and not padding. -/
def poseidonPoints_roundTrip_ok : Bool :=
  (poseidonVkData.fixedCommitmentHex ++ poseidonVkData.permutationCommitmentHex).size == 27
    && (poseidonVkData.fixedCommitmentHex ++ poseidonVkData.permutationCommitmentHex).all
        (fun b => match G1Affine.ofCompressed? b with
          | some P => (G1Affine.toCompressed P).data.toList == b.data.toList
          | none => false)

/-- GATE 9 (THE CROSS-FIXTURE PIN). The 19 fixed and 8 permutation commitments vk.json lists in
    COMPRESSED form are the same points the deployed artifact lists in EIP-2537 PADDED form, which
    is what D.1 parsed into poseidonVkGen. Coordinates compared as Nats, so a drift in either fixture
    reddens this and nothing else has to be believed. This is the closest this world gets to a
    point-level KAT on the VK: the content is checked, the carrier is not. -/
def poseidonPoints_matchArtifact_ok : Bool :=
  poseidonVkData.fixedCommitmentHex.size == poseidonVkGen.fixedComms.length
    && poseidonVkData.permutationCommitmentHex.size == poseidonVkGen.permutationComms.length
    && (poseidonVkData.fixedCommitmentHex.toList.zip poseidonVkGen.fixedComms).all
        (fun (b, w) => decompressed b == some (wordPair w))
    && (poseidonVkData.permutationCommitmentHex.toList.zip poseidonVkGen.permutationComms).all
        (fun (b, w) => decompressed b == some (wordPair w))
    && poseidonVkGen.fixedComms.length == 19 && poseidonVkGen.permutationComms.length == 8

/-- GATE 10 (the G2 encoder is a real encoder). poseidonEncG2 emits 256 bytes that the precompile's
    own reader accepts and its validator passes, it separates two different exponents (so it is not
    the constant map the fixture's encoder is), and the identity encodes to the EIP-2537 infinity
    word. -/
def poseidonEncG2_ok : Bool :=
  (poseidonEncG2 (g2foldExp 1)).size == 256
    && (match g2Of? (poseidonEncG2 (g2foldExp 1)) with
        | some pt => g2PointValid pt
        | none => false)
    && poseidonEncG2 (g2foldExp 1) ≠ poseidonEncG2 (g2foldExp 2)
    && poseidonEncG2 (g2foldExp 0) == bytesZero g2Bytes

/-- GATE 11 (params.json, the half it can be checked on). Widths - G1 compressed is 48 bytes, G2
    compressed is 96 (two 48-byte Fp2 halves, NOT the 48 a reader that trusted the field name would
    assume), curve and format and schema, max_k equal to vk.json's k, the file's own note made
    checkable (n_g2 is g2 with the sign bit of byte 0 flipped and the same tail), s_g2 distinct from
    g2, and the G1 generator decompressing to exactly the coordinates of g1zGen - the carrier the
    exhibit lives on. That last clause is the one real tie between params.json and G₁z. -/
def poseidonParams_bytes_ok : Bool :=
  poseidonParamsData.curve == "BLS12-381" && poseidonParamsData.format == "compressed"
    && poseidonParamsData.schema == 1 && poseidonParamsData.maxK == poseidonVkData.k
    && poseidonParamsData.g1Hex.size == 48 && poseidonParamsData.g2Hex.size == 96
    && poseidonParamsData.nG2Hex.size == 96 && poseidonParamsData.sG2Hex.size == 96
    && Nat.xor (byte0 poseidonParamsData.g2Hex) (byte0 poseidonParamsData.nG2Hex) == 0x20
    && poseidonParamsData.g2Hex.data.toList.drop 1
        == poseidonParamsData.nG2Hex.data.toList.drop 1
    && poseidonParamsData.sG2Hex.data.toList ≠ poseidonParamsData.g2Hex.data.toList
    && decompressed poseidonParamsData.g1Hex == some (g1zPair g1zGen)

/-- GATE 12 (THE ROOT REPAIR, AND THE FINDING THAT MADE IT NECESSARY). The search found an exponent
    and it is 61; the repaired root's 2^26-th power IS vk.json's omega; the repaired root is a
    primitive 2^32-nd root (its 2^32 power is 1 and its 2^31 is -1); poseidonFc keeps frFc's numBits
    and s and zeta; numBits is vk.json's scalar_num_bits. THE LAST TWO CLAUSES ARE THE FINDING: at
    the tree's own frFc the constructor produces a DIFFERENT omega, so without the repair gate 3
    could not pass. If someone fixes TwoAdicity's root, those two clauses go false and this gate
    says so out loud. -/
def poseidonRootRepair_ok : Bool :=
  poseidonRootExponent == 61 && poseidonRootOfUnity ^ 2 ^ 26 == poseidonOmega
    && poseidonRootOfUnity ^ 2 ^ 32 == 1 && poseidonRootOfUnity ^ 2 ^ 31 == -1
    && poseidonFc.numBits == poseidonVkData.scalarNumBits && poseidonFc.s == frFc.s
    && poseidonFc.zeta == frFc.zeta
    && (match EvaluationDomain.new frFc poseidonVkData.csDegree poseidonVkData.k with
        | .ok d => d.omega != poseidonOmega && d.n == poseidonVkData.n
        | .error _ => false)

/-- GATE 13 (THE OPEN OBLIGATION, PINNED RATHER THAN HIDDEN). vk.json carries no gates, no lookup
    arguments, no trashcan arguments and no permutation columns, so the CS's four fields are empty
    and the ported degree recomputation answers 3 where the fixture caches 5. That is
    WellFormed.csDegreeMatches failing, and it is a property of the FIXTURE, not of this file. The
    gate asserts the gap in a form that goes FALSE the day the data arrives from a real source, so
    the obligation cannot be quietly forgotten and cannot be quietly satisfied by invented gates. -/
def poseidonWellFormed_open_ok : Bool :=
  poseidonCs.gates.isEmpty && poseidonCs.lookups.isEmpty && poseidonCs.trashcans.isEmpty
    && poseidonCs.permutation.columns.isEmpty && poseidonCs.unblindedAdviceColumns.isEmpty
    && poseidonCs.generalColumnAnnotations.isEmpty && poseidonCs.constants.isEmpty
    && poseidonCs.minimumDegree == none
    && (match poseidonCs.degree with | .ok d => d == 3 | .error _ => false)
    && (match poseidonCs.degree with | .ok d => d != poseidonVkExec.csDegree | .error _ => false)
    && !(poseidonVkExec.permutation.commitments.size ==
        divCeil poseidonCs.permutation.columns.size (poseidonVkExec.csDegree - 2))

/-- GATE 14 (vk.json against D.1's typed-in meta). The three counts the deployed profile does carry
    agree with the exporter: one lookup, one trashcan, four simple selectors. Recorded as a gate
    because D.3 check 2 compares a whole ConstraintSystemMeta against this CS and the profile's meta
    is typed in - so the agreement that exists is worth pinning, and the empties that do not
    (permutationColumns, adviceQueries, numFixeds) are named in the header rather than glossed. -/
def poseidonMeta_crossCheck_ok : Bool :=
  poseidonPlanV2.meta_.numLookups == poseidonVkData.numLookups
    && poseidonPlanV2.meta_.numTrashcans == poseidonVkData.numTrashcans
    && poseidonPlanV2.meta_.numSimpleSelectors == poseidonCs.numSimpleSelectors
    && poseidonPlanV2.meta_.numSimpleSelectors == 4 && poseidonPlanV2.meta_.numLookups == 1
    && poseidonPlanV2.meta_.numTrashcans == 1

end Midfall.Instances.PoseidonEnvKats

#eval Midfall.Instances.PoseidonEnvKats.poseidonVkParse_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonVk_k_n_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonVk_omega_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonVk_columnCounts_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonVk_queries_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonVk_csDegree_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonVk_transcriptRepr_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonPoints_roundTrip_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonPoints_matchArtifact_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonEncG2_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonParams_bytes_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonRootRepair_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonWellFormed_open_ok -- expect true
#eval Midfall.Instances.PoseidonEnvKats.poseidonMeta_crossCheck_ok -- expect true
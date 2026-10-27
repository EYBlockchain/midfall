-- |
-- Midfall.Lowering.Accumulator
--
-- P-SE stage 2 (docs/plans/P-SE-stage2.md, file row 2; PLAN
-- P-SE-semantic-equivalence.md section F and index item 6; design1.md M5-3,
-- M5-4, M5-5, M5-6).
--
-- WHAT THIS FILE IS FOR. This is the layer the headline lowering theorems decode
-- the accumulator through: the normalised instance words (accWords), the
-- contract-convention relabelling (negateByTable), the two round trips
-- (decodeAcc_encode and its point-pair sibling), the S5 batching algebra
-- (batched_complete, batched_atMostOneRoot), the check-level pairing lift
-- (dualMsm_check_iff_contract), and the acceptance predicate with the accumulator
-- arm (ContractRefAcceptsAcc) plus its two lemmas.
--
-- TWO STATEMENTS ARE FALSE AS PLAN 9.5 WRITES THEM, and this file states the true
-- forms rather than the planned ones. Both are recorded in docs/REVIEW.md (R-25,
-- R-26) and annotated at Exec/Accumulator.lean, and the stage-2 brief says not to
-- restate them naively:
--
--   1. decodeAcc_injective. The accumulator decoder IGNORES the coordinate words
--      of an identity-flagged point (AccumulatorHelpers.yul:130-141, ported at
--      Exec/Accumulator.lean:396-403: with the flag set the coordinates are
--      neither decoded nor range-checked), so two instance tails that differ only
--      there decode to the SAME accumulator. Exec/Accumulator.lean states this at
--      the decoder and accIdentityKats_ok exhibits the pair. What survives is
--      injectivity of the NORMALISED words: accWords projects the coordinate words
--      of a flagged point to zero and keeps everything the decoder actually reads.
--      The doc comment on accWords says what the normalisation does and why each
--      kept word is recoverable.
--   2. decodeAcc_encode. encodeAccInstances always emits the two carried scalar
--      words (Exec/Accumulator.lean, via AccMsm.asPublicInput), so for a .pointPair
--      encoding the emitted tail is two words longer than the decoder expects and
--      fixedScalarCount returns none: the round trip is FALSE for .pointPair. It is
--      stated here restricted to hkind : enc.kind = .pointAndScalar, and the
--      point-pair case is stated separately over a kind-aware encoder
--      (encodeAccPublicInput) with the extra hypothesis that shape forces.
--
-- A THIRD DEFECT, found while stating item 2 and reported per PLAN 12: the
-- sketch's decodeAcc_encode_pointPair inherits decodeAcc_encode's binders, which
-- allow a non-empty fixed-base tail. For .pointPair that is impossible -
-- fixedScalarCount rejects any non-zero tail (api.rs:178-186, and the reference's
-- own KAT at lowering/tests.rs:2096-2104) - so with a non-empty table the left side
-- is none and the equation is false. The statement below adds hfb : fb.size = 0,
-- which is the deployed Moonlight shape (a point pair carries no tail at all). That
-- is a strengthening of the hypothesis list, not a weakening of the conclusion.
--
-- WHAT IS NOT HERE. The S5 proofs themselves (M9), the Inv/Partials layer (stages
-- 4-5), and any reference to Midfall/Instances/ (D-P17). The fixed-base table is a
-- parameter because Midfall.Halo2.fixedBases' "-G" entry is the identity (R-52, a
-- live defect in the Exec row) and no statement here may use it.

import Midfall.Lowering.AccEncoding
import Midfall.Assumptions.Codec
import Midfall.Halo2.Exec.Accumulator
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Lowering.Types
import Midfall.Halo2.Spec.Lemmas

namespace Midfall.Lowering
open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### 1. The R-25 normalisation -/

/-- R-25 projection of an instance array to the accumulator tail the decoder
    actually reads.

    WHAT THE NORMALISATION DOES, clause by clause, and why each clause is forced by
    a real malleability rather than chosen for convenience:

    * inst.extract enc.offset inst.size - decodeAcc reads nothing before enc.offset,
      so the prefix words are not part of the decoded value. Only the LENGTH
      survives, and it does so through the tail window's own length: a successful
      decode forces inst.size >= offset + fixedPayloadWords (fixedScalarCount), so
      the window length determines inst.size and no information is lost.
    * the coordinate words of a point whose identity flag is 1 are set to zero -
      this is the R-25 malleability itself. loadAccPoint returns 128 zero bytes for
      ANY coordinates when the flag is 1, so those words carry no meaning; zeroing
      them is what makes the decoder injective. The flag word itself is KEPT,
      because it is read (a flag of 2 is a rejection, not another encoding).
    * carried scalars and tail scalars are kept verbatim - each is compared against
      p and cast, so two different words give two different Fr values (Nat.cast is
      injective below p) and they must not be projected away.
    * the rhs point sits at pointWords + (1 if carried else 0) inside the window,
      exactly where decodeAcc puts it.

    Without the window, two arrays differing below enc.offset decode identically and
    injectivity fails; without the zeroing, accIdentityKats_ok's pair is a
    counterexample. accWordsKats_ok below exhibits both failures and the fix. -/
def accWords (enc : Midfall.Halo2.AccumulatorEncoding) (inst : Array Word256) :
    Array Word256 :=
  let tail := inst.extract enc.offset inst.size
  let cw := enc.coordinateWords
  let rhsSrc := enc.pointWords + (if enc.hasCarriedScalars then 1 else 0)
  let zeroCoords (a : Array Word256) (src : Nat) : Array Word256 :=
    if a.getD (src + 2 * cw) 0 = 1 then
      (List.range (2 * cw)).foldl (fun acc j => arraySetD acc (src + j) 0) a
    else a
  zeroCoords (zeroCoords tail 0) rhsSrc

/-- PLAN 9.5 decodeAcc_injective in its R-25 form: two instance arrays that decode
    to the same accumulator agree on the NORMALISED tail. Stated over the Exec
    encoding, which is what decodeAcc is typed over; decodeAcc_injective_gen below
    is the same fact for the generator encoding PLAN 9.5 means, via the D-P16
    bridge.

    hypotheses, each of which is load-bearing:
    * hrt : codec.eipRoundtrip - a flag-0 slot rebuilds 128 bytes from the decoded
      coordinates and then decodes them back to the same point, so two accepted
      flag-0 slots with the same point must have had the same bytes; that is exactly
      decoder-first canonicity, and without it two different coordinate words could
      name one point.
    * hone : codec.toEip 1 = 128 zero bytes - without it the identity would have
      BOTH a flag-1 encoding and a flag-0 encoding (the coordinates that decode to
      (0,0) are rejected only when the rebuilt bytes are the all-zero ones), and the
      two have different accWords because the flag word is kept.
    * hnodup - decodeAcc folds the tail through accMapInsert, which OVERWRITES a
      duplicate name, so a repeated base name silently drops a tail word and two
      tails differing there decode alike.

    No p <= 2^256 hypothesis is needed here, unlike decodeAcc_encode: the carried and
    tail words are checked < p before Nat.cast and Nat.cast is injective below p, so
    the words are recovered from the values.

    PROOF OBLIGATION, registered in SORRY.md (M5-3's lemma list:
    decodeAccCoord_inj, loadAccPoint_flag0_bytes, loadAccPoint_flag1,
    accMapInsert_fold_lookup_nodup, Nat.cast_injOn_lt_p, identity_flag_forced). The
    statement is the plan's, not a weakening: the plan's own decodeAcc_injective is
    the unprojected form and is FALSE. -/
theorem decodeAcc_injective {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁)
    (hrt : codec.eipRoundtrip) (hone : codec.toEip 1 = natToBytesBE 0 128)
    (fb : Array (AccFixedBase G₁)) (hnodup : (fb.toList.map AccFixedBase.name).Nodup)
    (i₁ i₂ : Array Word256) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (h₁ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₁ = some a)
    (h₂ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₂ = some a) :
    accWords enc i₁ = accWords enc i₂ := by
  sorry

/-- The same injectivity stated over the GENERATOR encoding, which is what PLAN 9.5
    and Supported.acc quantify over (hazard 1: the bridge direction is generator ->
    Exec, so the generator-typed form is the one a Surface field can consume). It is
    an instantiation, not a second theorem: the normalisation is applied to
    (toExec enc), whose coordinateWords / pointWords / hasCarriedScalars are the
    generator's by toExec_coordinateWords, toExec_fixedPayloadWords and
    toExec_hasCarriedScalars. -/
theorem decodeAcc_injective_gen {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Generator.AccumulatorEncoding) (codec : G1Codec G₁)
    (hrt : codec.eipRoundtrip) (hone : codec.toEip 1 = natToBytesBE 0 128)
    (fb : Array (AccFixedBase G₁)) (hnodup : (fb.toList.map AccFixedBase.name).Nodup)
    (i₁ i₂ : Array Word256) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (h₁ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb i₁ = some a)
    (h₂ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb i₂ = some a) :
    accWords (toExec enc) i₁ = accWords (toExec enc) i₂ :=
  decodeAcc_injective (p := p) (toExec enc) codec hrt hone fb hnodup i₁ i₂ a h₁ h₂

/-! ### 2. The contract's sign convention -/

/-- Contract-convention relabelling (R-26.3). A generated fixed-base entry whose
    negate flag is set carries the NEGATED scalar: the circuit's fixed base for
    "-G" is the negated generator (circuits/src/verifier/mod.rs:119) while the
    contract embeds the positive base from the VK header and negates the public
    scalar instead (artifacts.rs:200, AccumulatorHelpers.yul:322-326). decodeAcc
    models the contract's reading, so the accumulator it returns is a's rhs with
    those scalars flipped - NOT a. -/
def negateByTable {G₁ G₂ Gₜ : Type}
    (fb : Array (AccFixedBase G₁)) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) :
    KzgAcc (Fr p) G₁ G₂ Gₜ :=
  let neg (n : String) : Bool := fb.any (fun b => b.name == n && b.negate)
  { a with rhs := { a.rhs with fixedBaseScalars :=
      a.rhs.fixedBaseScalars.map (fun (n, s) => (n, if neg n then -s else s)) } }

/-! ### 3. The round trips -/

/-- Strictly ascending names. This is the BTreeMap invariant the Rust gets for free
    (circuits/src/verifier/msm.rs:40-54 keeps fixed_base_scalars sorted by key, and
    artifacts.rs:225 sorts the generated table), which decodeAcc's accMapInsert fold
    reproduces only if the input is already ascending.

    It is defined here rather than imported as Mathlib's List.Sorted (· < ·) because
    Mathlib's order/sorted theory is not in this project's imported surface - the
    lakefile builds only the Mathlib modules the tree already uses, and pulling in
    another one for a single predicate is not worth the rebuild. The three-clause
    recursion is the same proposition. -/
def namesAscending : List String → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ namesAscending (b :: rest)

/-- The singleton and empty cases are trivial, so the hypothesis is not vacuous; two
    equal names fail it, which is the case accMapInsert would silently collapse. -/
example : namesAscending [] ∧ namesAscending ["-G"] ∧ namesAscending ["-G", "a_fixed_com_0"] :=
  ⟨trivial, trivial, ⟨by simp, trivial⟩⟩

example : ¬ namesAscending ["a", "a"] := by
  intro h
  exact absurd h.1 (by simp)


/-- PLAN 9.5 decodeAcc_encode, restricted to the only shape the contract can read
    (R-26.2): a COLLAPSED point-and-scalar accumulator - one base with one carried
    scalar per side, plus the RHS fixed-base tail - behind enc.offset prefix words.

    hypotheses, each load-bearing:
    * hp : p < 2^256 - frWord truncates mod 2^256, and the decoder recovers the word
      and casts it back; below 2^256 that is the identity.
    * hkind - the .pointPair case is FALSE, for the reason in this file's header.
    * hshape - fixedScalarCount reaches validFor, which requires the 7x56 limb
      shape; without it the decoder returns none and the equation is about none.
    * hc : G1CodecLaws codec - ofEip_toEip recovers the point from the bytes the
      encoder rebuilt, eipShape makes those bytes the 16-48-16-48 frame with
      in-field non-(0,0) coordinates (which is what makes the rebuild byte-for-byte
      equal to toEip, and what keeps the (0,0) rejection from firing on a real
      point), and toEip_one covers L or R being the identity.
    * hsorted - decodeAcc rebuilds the fixed map with accMapInsert in fb order, so
      only a strictly ascending tail is reproduced verbatim; the BTreeMap invariant
      the Rust gets for free is not in this type.
    * hnames - the tail count must equal the table size and pair name-by-name
      (artifacts.rs:225 sorts by name).
    * hpre - decodeAcc reads at enc.offset, so the prefix must be exactly that long.

    PROOF OBLIGATION, registered in SORRY.md (M5-4's lemma list:
    encodeAccCoordWords_packingOk, biFromLimbs_biToLimbs, loadAccCoordShifted_encode,
    decodeAccCoord_encode, loadAccPoint_encode_nonId / _id,
    accMapInsert_fold_sorted_id, fixedScalarCount_exact). -/
theorem decodeAcc_encode {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (hp : p < 2 ^ 256)
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (tail : Array (String × Fr p))
    (hsorted : namesAscending (tail.toList.map Prod.fst))
    (fb : Array (AccFixedBase G₁))
    (hnames : fb.toList.map AccFixedBase.name = tail.toList.map Prod.fst)
    (pre : Array Word256) (hpre : pre.size = enc.offset) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := tail } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (pre ++ encodeAccInstances (toExec enc) codec a) = some (negateByTable fb a) := by
  sorry

/-- The PLAN's literal conclusion, which holds exactly when no base is negated.
    Same binders and same hypotheses as decodeAcc_encode; the extra hneg is what
    turns negateByTable fb a back into a. PROOF OBLIGATION, registered in SORRY.md. -/
theorem decodeAcc_encode_noNeg {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (hp : p < 2 ^ 256)
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (tail : Array (String × Fr p))
    (hsorted : namesAscending (tail.toList.map Prod.fst))
    (fb : Array (AccFixedBase G₁))
    (hnames : fb.toList.map AccFixedBase.name = tail.toList.map Prod.fst)
    (pre : Array Word256) (hpre : pre.size = enc.offset)
    (hneg : ∀ b ∈ fb.toList, b.negate = false) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := tail } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (pre ++ encodeAccInstances (toExec enc) codec a) = some a := by
  sorry

/-- Drop the two carried-scalar slots from an encodeAccInstances word stream: the
    lhs scalar sits at pointWords and the rhs scalar at 2*pointWords + 1, which is
    where decodeAcc would look for them if the layout carried scalars.

    This is the SKETCH name dropCarriedScalarWords from PLAN 9.5 section F, which
    does not exist in the tree (survey.md has no such name either); it is defined
    here rather than invented there, and it is only meaningful for a collapsed
    one-base-per-side accumulator, which is the only shape the point-pair layout
    admits (fixedScalarCount rejects a tail for .pointPair). -/
def dropCarriedScalarWords (enc : Midfall.Halo2.AccumulatorEncoding)
    (w : Array Word256) : Array Word256 :=
  let pw := enc.pointWords
  (w.extract 0 pw) ++ (w.extract (pw + 1) (2 * pw + 1)) ++ (w.extract (2 * pw + 2) w.size)

/-- Adjustment 1 of PLAN 9.5 section F: the kind-aware public-input encoder. For a
    point-pair encoding the contract reads no scalar words at all (the carried
    scalars are implicitly 1, api.rs:53-56), so the two slots are dropped; for a
    point-and-scalar encoding this is encodeAccInstances unchanged. -/
def encodeAccPublicInput {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 :=
  if enc.hasCarriedScalars then encodeAccInstances enc codec a
  else dropCarriedScalarWords enc (encodeAccInstances enc codec a)

/-- The round trip for the DEPLOYED point-pair shape.

    THREE restrictions beyond decodeAcc_encode, and each one is a place the PLAN's
    statement was false rather than a convenience:
    * hkind : enc.kind = .pointPair - the carried scalars are not emitted, so the
      two scalars the decoder produces are the literals 1, which is what hsL / hsR
      pin a's scalars to.
    * hfb : fb.size = 0 - THE PLAN DID NOT SAY THIS AND IT NEEDS IT. For a point-pair
      encoding, fixedScalarCount rejects any non-zero tail, so with a non-empty
      fixed-base table decodeAcc returns none and the equation fails. The deployed
      Moonlight shape has no tail, which is exactly what hfb says. Reported as the
      third false-as-written statement found in this layer.
    * the carried scalars of a are 1, matching what the decoder can produce.

    PROOF OBLIGATION, registered in SORRY.md. -/
theorem decodeAcc_encode_pointPair {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (hp : p < 2 ^ 256)
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointPair)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (hsL : sL = 1) (hsR : sR = 1)
    (fb : Array (AccFixedBase G₁)) (hfb : fb.size = 0)
    (pre : Array Word256) (hpre : pre.size = enc.offset) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := #[] } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (pre ++ encodeAccPublicInput (toExec enc) codec a) =
          some (negateByTable fb a) := by
  sorry

/-! ### 4. The algebra the S5 statements and the pairing lift consume -/

/-- A Decidable witness as a Bool, read back as an iff. The bridge between the
    Bool-typed checks of plan 9.2 and the Prop-level pairing equations. -/
theorem decideBool_eq_true_iff {α : Type} {a b : α} (d : Decidable (a = b)) :
    decideBool d = true <-> a = b := by
  cases d <;> simp [decideBool, *]

section Msm
variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]

/-- A one-term MSM with scalar 1 evaluates to its base: the shortcut in
    MSMKZG.eval fires and there is nothing else to add. -/
theorem MSMKZG.eval_fromBase (Q : G₁) : (MSMKZG.fromBase (p := p) Q).eval = Q := by
  simp [MSMKZG.eval, MSMKZG.fromBase]

/-- Scaling an MSM scales its value. No Wf hypothesis is needed: the [1] shortcut
    in MSMKZG.eval agrees with msmSpecific case by case (scalars #[1] scaled by c
    gives c - B either way, and the empty case is 1 on both sides), which is what
    attack.md's MSMKZG.eval_scale entry concludes and why P1's stronger .Wf
    hypothesis is decorative. PROOF OBLIGATION, registered in SORRY.md. -/
theorem MSMKZG.eval_scale (m : MSMKZG (Fr p) G₁) (c : Fr p) :
    (m.scale c).eval = gsmul c m.eval := by
  sorry

/-- Additivity of the MSM value across addMsm. Lockstep lengths ARE required:
    msmSpecific zips and truncates, so a scalars/bases mismatch silently drops a
    term and the sum changes. PROOF OBLIGATION, registered in SORRY.md. -/
theorem MSMKZG.eval_addMsm (m n : MSMKZG (Fr p) G₁)
    (hm : m.scalars.size = m.bases.size) (hn : n.scalars.size = n.bases.size) :
    (m.addMsm n).eval = m.eval * n.eval := by
  sorry

end Msm

section S5
variable {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- S5 completeness half: if both equations hold then the alpha-batched equation
    holds, for every alpha (bilinearity: the batched value is X + alpha - Y with X
    and Y each 0). No alpha <> 0 side condition is needed - the argument is linear in
    alpha and alphaOf maps 0 to 1 anyway.

    PROOF OBLIGATION, registered in SORRY.md (M5-5's statement, M9's proof). hWf is
    what eval_addMsm needs and is the owed prepareMsgs-Wf lemma, taken as a
    hypothesis until then. -/
theorem batched_complete (params : ParamsVerifierKZG G₁ G₂) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hd : DualMSM.check d params = true) (ha : KzgAcc.check a params tbl = true)
    (alpha : Fr p) : batchedCheck params alpha d a tbl = true := by
  sorry

/-- S5 soundness half: if either equation fails then at most one alpha makes the
    batched one pass. Over the ZMod p-module Additive Gt (a field, so no zero
    divisors), X + alpha - Y = 0 = X + beta - Y with alpha <> beta forces
    (alpha - beta) - Y = 0, hence Y = 0, hence X = 0 - contradicting the failure.
    PROOF OBLIGATION, registered in SORRY.md. -/
theorem batched_atMostOneRoot (params : ParamsVerifierKZG G₁ G₂)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hbad : DualMSM.check d params = false \/ KzgAcc.check a params tbl = false)
    (alpha beta : Fr p) (hα : batchedCheck params alpha d a tbl = true)
    (hβ : batchedCheck params beta d a tbl = true) : alpha = beta := by
  sorry

/-- The contract orientation at CHECK level: e(PAIRING_RHS, G2) *
    e(PAIRING_LHS, NEG_S_G2) = 1. The swap is FinalPairing.yul:88
    (ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)) against the frame
    layout at AssemblyHelpers.yul:284-287 ([lhs | G2_BASE | rhs | NEG_S_G2_BASE]). -/
def contractPairingHolds (g2 negSG2 : G₂) (lhs rhs : G₁) : Prop :=
  P.e (Additive.ofMul rhs) (Additive.ofMul g2) +
      P.e (Additive.ofMul lhs) (Additive.ofMul negSG2) = 0

/-- Lift of Spec.Lemmas.pairing_reorder to DualMSM.check. Only linearity in the G2
    slot is needed (ofMul_inv, map_neg, neg_add), so no exponent model and no
    cyclic-group lemma - attack.md's dualMsm_check entry confirms P3's reading
    against P2's heavier one, and exists_zmod_smul_generator below is kept only for
    Spec-level statements.

    hypotheses: hn : nG2Prepared = g2⁻¹ is R-4 (Params.lean builds ofParams with
    g2⁻¹ while the contract embeds G2_BASE = params.g2), hs : sG2Prepared = negSG2⁻¹
    is the NEG_S_G2_BASE = sG2⁻¹ embedding. Both are necessary: with hn dropped the
    two sides differ on the exponent model for lhs = rhs = g1.

    PROOF OBLIGATION, registered in SORRY.md. -/
theorem dualMsm_check_iff_contract (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (params : ParamsVerifierKZG G₁ G₂) (g2 negSG2 : G₂)
    (hn : params.nG2Prepared = g2⁻¹) (hs : params.sG2Prepared = negSG2⁻¹) :
    DualMSM.check d params = true <->
      contractPairingHolds g2 negSG2 d.left.eval d.right.eval := by
  sorry

/-- Spec-level: every G1 element is a multiple of the SRS base (prime order makes
    the group cyclic and g1 is nontrivial). TRUE but not needed by the check-level
    lift above; kept because the Spec-level statements consume it. PROOF
    OBLIGATION, registered in SORRY.md. -/
theorem exists_zmod_smul_generator (Q : G₁) : ∃ s : ZMod p, Q = gsmul s P.g₁ := by
  sorry

end S5

/-! ### 5. Canonicality of raw instance words -/

/-- The contract's canonicality gate on one instance word
    (TranscriptProofParser.yul:63-68: lt(inst_be, r)). A word at or above p is
    none, not a reduction - that is the R-26.7 point. -/
def frOfWord? (w : Word256) : Option (Fr p) :=
  if w.toNat < p then some (Nat.cast w.toNat) else none

/-- The same gate lifted over the whole instance array. ContractRefAcceptsAcc below
    takes instW : Array Word256 rather than Array (Fr p) precisely so this rejection
    stays visible. -/
def instOfWords? (ws : Array Word256) : Option (Array (Fr p)) :=
  (ws.toList.mapM frOfWord?).map List.toArray

/-! ### 6. The acceptance predicate with the accumulator arm -/

/-- PLAN 9.5 ContractRef.accepts with the accumulator arm, over RAW instance words
    so the >= r rejections of validate_public_accumulator stay visible (R-26.7), and
    with an explicit vkDigest word (attack.md's ContractRefAcceptsAcc entry settles
    on P1's signature: P2's frWord vk.transcriptRepr loses the >= r rejection and
    P3's liftWord reduces mod p).

    fb is the generated POSITIVE-base table (artifacts.rs:181-227) passed in as a
    parameter because Midfall.Halo2.fixedBases' "-G" entry is the identity (R-52, a
    live Exec-row defect) and must not appear in any statement until it is fixed.
    alphaOf's argument order is (kzgLhs kzgRhs accLhs accRhs) while the hashed
    preimage order is tag || vk_digest || RHS || LHS || ACC_RHS || ACC_LHS
    (FinalPairing.yul:21-26) - the R-11 trap, spelled out in Exec/Accumulator.lean's
    alphaOf doc comment.

    The encoding is the GENERATOR one (hazard 1) and the decoder is applied to
    (toExec enc), which is what makes this the statement PLAN 9.5 means. The
    vkDigest_spec link (vkDigest = frWord vk.transcriptRepr) is an Obligations field
    because it needs feToU256_frToRepr, which is in Lowering/VkDigest.lean. -/
def ContractRefAcceptsAcc {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (cfgAcc : Option Midfall.Generator.AccumulatorEncoding)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (ms : List (Msg (Fr p) G₁)) : Bool :=
  match instOfWords? (p := p) instW with
  | none => false
  | some inst =>
    match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
    | .error _ => false
    | .ok d =>
      match cfgAcc with
      | none => DualMSM.check d params
      | some enc =>
        match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW with
        | none => false
        | some a =>
          let tbl := fb.map (fun b => (b.name, b.base))
          let (accL, accR) := a.fullyCollapse tbl
          batchedCheck params
            (alphaOf (p := p) H vkDigest E.g1 d.left.eval d.right.eval accL accR)
            d a tbl

/-- The no-accumulator arm agrees with the existing ContractRefAccepts, over the
    SAME raw words: the instance rejection is the only difference and with cfgAcc =
    none the decoder is never reached. attack.md's ContractRefAcceptsAcc entry
    requires this lemma to be about the P1 signature (it is) and P3's _none lemma
    restated over it. PROOF OBLIGATION, registered in SORRY.md. -/
theorem contractRefAcceptsAcc_none {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (ms : List (Msg (Fr p) G₁)) :
    ContractRefAcceptsAcc E H params vk none vkDigest fb instW ms = true <->
      (∃ inst, instOfWords? (p := p) instW = some inst ∧
        Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E H params vk inst ms = true) := by
  sorry

/-- PLAN 9.5 contractRef_acc_complete: the R-26.4 direction ONLY (the contract is
    strictly stronger than the reference in accumulator mode, so there is no iff).
    Rust-accepts, plus a decodable accumulator that separately passes its own check,
    implies the contract reference accepts.

    hWf names the DualMSM prepareMsgs produces and gives batched_complete its
    lockstep lengths; it is the owed prepareMsgs-Wf lemma taken as a hypothesis.
    hchk is the accumulator's own invariant, which verifyMsgs does NOT run - that is
    the whole reason the direction is one-way. PROOF OBLIGATION, registered in
    SORRY.md (M5-6; the proof needs batched_complete, i.e. M9). -/
theorem contractRef_acc_complete {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (enc : Midfall.Generator.AccumulatorEncoding)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁))
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hinst : instOfWords? (p := p) instW = some inst)
    (hv : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk inst ms = .ok ())
    (ha : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW = some a)
    (hchk : KzgAcc.check a params (fb.map fun b => (b.name, b.base)) = true)
    (hWf : ∀ d, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok d ->
      d.left.scalars.size = d.left.bases.size /\ d.right.scalars.size = d.right.bases.size) :
    ContractRefAcceptsAcc E H params vk (some enc) vkDigest fb instW ms = true := by
  sorry


/-! ### 7. Known-answer checks

    The toy point type below exists so these gates can RUN: decodeAcc, accWords,
    frOfWord? and negateByTable need no pairing, no group and no curve, only a
    G1Codec, so a two-element stand-in with the all-zero-bytes codec exercises the
    decoder's identity arm exactly the way accIdentityKats_ok exercises the Exec
    one. Midfall/Instances/ stays out (D-P17). -/

namespace Kats

/-- A two-element stand-in for a G1 group, with the codec that maps everything to
    the 128 zero bytes the contract uses for the identity and decodes only those.
    That is enough to drive decodeAcc's identity arm, which is where the R-25
    malleability lives. -/
inductive ToyPt | one | other deriving BEq

def toyCodec : G1Codec ToyPt where
  toEip := fun _ => natToBytesBE 0 128
  ofEip? := fun b => if b == natToBytesBE 0 128 then some .one else none
  toCompressed := fun _ => Bytes.empty
  ofCompressed? := fun _ => none

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The 12-word collapsed point-and-scalar tail at offset 0: x(2) y(2) flag,
    lhs scalar, x(2) y(2) flag, rhs scalar - the layout decodeAcc reads and the
    shape lowering/tests.rs:2051-2073 builds. -/
def tailA : Array Word256 :=
  #[BitVec.ofNat 256 12345, 0, BitVec.ofNat 256 54321, 0, 1, 2,
    BitVec.ofNat 256 999, 0, BitVec.ofNat 256 888, 0, 1, 3]

/-- The same tail with DIFFERENT coordinate words under both identity flags and the
    same scalars. This is the R-25 pair: distinct instance tails, one accumulator. -/
def tailB : Array Word256 :=
  #[BitVec.ofNat 256 7, BitVec.ofNat 256 8, BitVec.ofNat 256 9, BitVec.ofNat 256 10, 1, 2,
    BitVec.ofNat 256 11, BitVec.ofNat 256 12, BitVec.ofNat 256 13, BitVec.ofNat 256 14, 1, 3]

/-- Comparing two decoded accumulators component by component: KzgAcc carries no BEq
    (it is a structure over abstract groups), so the gate compares what it holds. -/
def accParts (a : KzgAcc (Midfall.Fr 17) ToyPt ToyPt ToyPt) :
    List ToyPt × List (Midfall.Fr 17) × List ToyPt × List (Midfall.Fr 17) ×
    List (String × Midfall.Fr 17) :=
  (a.lhs.bases.toList, a.lhs.scalars.toList, a.rhs.bases.toList,
   a.rhs.scalars.toList, a.rhs.fixedBaseScalars.toList)

/-- THE R-25 EVIDENCE. (1) the two tails are different arrays; (2) decodeAcc gives
    the same accumulator for both, so the UNPROJECTED injectivity the plan states is
    false; (3) accWords makes them equal, which is what decodeAcc_injective claims;
    (4) the flag words and the carried scalars survive the normalisation, so a scalar
    change is still visible - the projection is not "zero everything"; (5) with the
    flag cleared the coordinate words survive too, which is the positive control that
    the zeroing is keyed on the flag; (6) two arrays that differ only below enc.offset
    normalise equal but are not equal, which is the window clause earning its place. -/
def accWordsKats_ok : Bool :=
  let enc := AccumulatorEncoding.new 0 7 56
  (tailA != tailB) &&
  (match decodeAcc (p := 17) enc toyCodec (#[] : Array (AccFixedBase ToyPt)) tailA,
         decodeAcc (p := 17) enc toyCodec (#[] : Array (AccFixedBase ToyPt)) tailB with
   | some x, some y => accParts x == accParts y
   | _, _ => false) &&
  (accWords enc tailA == accWords enc tailB) &&
  (accWords enc tailA).size == 12 &&
  (accWords enc tailA).getD 4 0 == 1 && (accWords enc tailA).getD 10 0 == 1 &&
  (accWords enc tailA).getD 5 0 == 2 && (accWords enc tailA).getD 11 0 == 3 &&
  (accWords enc (arraySetD tailA 5 4) != accWords enc tailA) &&
  (let t := arraySetD (arraySetD tailA 4 0) 10 0
   accWords enc t == t) &&
  (accWords enc tailA != tailA) &&
  let enc2 := AccumulatorEncoding.new 2 7 56
  let pre1 := #[BitVec.ofNat 256 111, BitVec.ofNat 256 222]
  let pre2 := #[BitVec.ofNat 256 333, BitVec.ofNat 256 444]
  (accWords enc2 (pre1 ++ tailA) == accWords enc2 (pre2 ++ tailA)) &&
  (pre1 ++ tailA != pre2 ++ tailA)

#eval accWordsKats_ok   -- expect true

/-- frOfWord? / instOfWords?: the canonicality gate the contract applies to every
    instance word (TranscriptProofParser.yul:63-68). A word at or above p is none,
    NOT a reduction - that distinction is R-26.7 and it is what
    ContractRefAcceptsAcc's raw-word interface preserves. The negative control is the
    word equal to p, the smallest value a mod-p reduction would wrongly accept, and
    the last conjunct shows the rejection is whole-array. -/
def instOfWordsKats_ok : Bool :=
  (frOfWord? (p := 17) (BitVec.ofNat 256 16) == some 16) &&
  (frOfWord? (p := 17) (BitVec.ofNat 256 17) == none) &&
  (frOfWord? (p := 17) (BitVec.ofNat 256 0) == some 0) &&
  (instOfWords? (p := 17) #[BitVec.ofNat 256 1, BitVec.ofNat 256 2] == some #[1, 2]) &&
  (instOfWords? (p := 17) #[BitVec.ofNat 256 1, BitVec.ofNat 256 40] == none) &&
  (instOfWords? (p := 17) #[BitVec.ofNat 256 40, BitVec.ofNat 256 1] == none)

#eval instOfWordsKats_ok   -- expect true

/-- negateByTable: a negate base flips its tail scalar, a non-negated one does not,
    and the lhs is never touched (the contract's tail is an RHS-only structure). The
    two-name table with OPPOSITE flags is the perturbation: flipping the flags changes
    the result, so neither arm is decorative. -/
def negateByTableKats_ok : Bool :=
  let fb : Array (AccFixedBase ToyPt) :=
    #[{ name := "-G", base := .one, negate := true },
      { name := "a_com_0", base := .one, negate := false }]
  let a : KzgAcc (Midfall.Fr 17) ToyPt ToyPt ToyPt :=
    { lhs := { bases := #[.one], scalars := #[2],
               fixedBaseScalars := #[("-G", (5 : Midfall.Fr 17))] },
      rhs := { bases := #[.other], scalars := #[3],
               fixedBaseScalars := #[("-G", (5 : Midfall.Fr 17)),
                                      ("a_com_0", (6 : Midfall.Fr 17))] } }
  let n := negateByTable fb a
  ((n.rhs.fixedBaseScalars.toList.map Prod.snd) ==
      [(-5 : Midfall.Fr 17), (6 : Midfall.Fr 17)]) &&
  ((n.rhs.fixedBaseScalars.toList.map Prod.fst) == ["-G", "a_com_0"]) &&
  (n.lhs.fixedBaseScalars.toList == a.lhs.fixedBaseScalars.toList) &&
  (negateByTable (fb.map (fun b => { b with negate := false })) a).rhs.fixedBaseScalars.toList ==
      a.rhs.fixedBaseScalars.toList &&
  (negateByTable (fb.map (fun b => { b with negate := ! b.negate })) a).rhs.fixedBaseScalars.toList !=
      a.rhs.fixedBaseScalars.toList

#eval negateByTableKats_ok   -- expect true

/-- dropCarriedScalarWords removes exactly the two scalar slots and keeps the point
    blocks in order, which is what makes encodeAccPublicInput the inverse of what
    decodeAcc reads for a point-pair layout. The words are tagged by index so a slot
    shift is visible: dropping the wrong slot changes the result. -/
def dropCarriedScalarWordsKats_ok : Bool :=
  let enc := AccumulatorEncoding.new 0 7 56
  let pw := enc.pointWords
  let w := (List.range (2 * pw + 2)).map (fun i => BitVec.ofNat 256 i) |>.toArray
  let d := dropCarriedScalarWords enc w
  d.size == 2 * pw &&
  d.toList == (List.range pw).map (fun i => BitVec.ofNat 256 i) ++
                (List.range pw).map (fun i => BitVec.ofNat 256 (i + pw + 1)) &&
  ! d.toList.contains (BitVec.ofNat 256 pw) &&
  ! d.toList.contains (BitVec.ofNat 256 (2 * pw + 1)) &&
  pw == 5

#eval dropCarriedScalarWordsKats_ok   -- expect true

/-- The restriction decodeAcc_encode_pointPair has to state and the plan does not:
    for a point-pair encoding a NON-EMPTY fixed-base tail makes the decode none,
    because fixedScalarCount rejects any non-zero tail (api.rs:178-186, KAT at
    lowering/tests.rs:2096-2104). This is the counterexample to the sketch's
    inherited binders, as a gate. The last conjunct is the positive control: the
    point-and-scalar layout DOES read the two carried scalars verbatim. -/
def pointPairTailKats_ok : Bool :=
  let pp := AccumulatorEncoding.pointPair 0 7 56
  let noTail : Array Word256 := #[0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
  let withTail : Array Word256 := noTail ++ #[BitVec.ofNat 256 4]
  (AccumulatorEncoding.fixedScalarCount pp 10 == some 0) &&
  (AccumulatorEncoding.fixedScalarCount pp 11 == none) &&
  ((decodeAcc (p := 17) (G₂ := ToyPt) (Gₜ := ToyPt) pp toyCodec
        #[{ name := "-G", base := ToyPt.one, negate := false }] withTail).isNone) &&
  (match decodeAcc (p := 17) pp toyCodec (#[] : Array (AccFixedBase ToyPt)) noTail with
   | some a => accParts a == ([.one], [1], [.one], [1], [])
   | none => false) &&
  (match decodeAcc (p := 17) (AccumulatorEncoding.new 0 7 56) toyCodec
      (#[] : Array (AccFixedBase ToyPt)) tailA with
   | some a => accParts a == ([.one], [2], [.one], [3], [])
   | none => false)

#eval pointPairTailKats_ok   -- expect true

end Kats

end Midfall.Lowering
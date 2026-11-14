-- |
-- Midfall/Instances/G2Codec
--
-- P-G2B STEP 1: the last plumbing item P-G2 named in 'gap_g2_codec_plumbing' (Instances/
-- G2Agreement.lean), landed. Two things were missing and both are byte plumbing, not
-- mathematics, exactly as that record said:
--
--   (1) THE 0x100 ROUND TRIP. 'g2Of? (g2PointBytes P) = some P' needs FOUR slice windows over a
--       three-fold 'bytesAppend' nest (G1 needed two over a one-fold nest). 'bytesAppend_size' is
--       private in Instances/G1Agreement.lean, so it is re-derived here - three lines - and the two
--       window lemmas it feeds ('bytesSlice_window_before' / '_after') are public and are reused
--       verbatim.
--
--       P-G2 PREDICTED these four lemmas would need 'set_option maxHeartbeats 400000000' and ran
--       out of budget before trying it. THE PREDICTION WAS WRONG IN KIND, and the measurement is
--       in 'slice_whole' and the section note below: at the default 200k the first attempt here
--       died inside 8 s of whnf, and at 4e8 the same attempt had not finished after 18 minutes -
--       so raising the budget would not have fixed it, it would have hidden it. What actually
--       fixes it is to stop the elaborator from choosing between 'g2PointBytes P' and the unfolded
--       nest: rewrite the structural equation FIRST and supply every byte width as an equation
--       that 'omega' can treat as an atom. With that, all four windows elaborate inside the DEFAULT
--       budget (measured: the whole file is 9.2 s, of which 4.4 s is one 'decide' about the
--       all-zero frame, and the four windows are under 1 s each). No heartbeat option appears on
--       any of them, deliberately.
--
--   (2) THE CARRIER. G1's carrier is 'Subgroup.zpowers (ofAdd (emb genFrame))': a set of CURVE
--       POINTS, encodable because G1's field is 'ZMod blsP' and 'ZMod.val' is a computable
--       canonical representative. G2's field is 'Fp2 = AdjoinRoot Fp (X^2+1)' (Instances/
--       Fp2.lean), whose elements are QUOTIENTS of polynomials: 'AdjoinRoot.mk' is a quotient lift
--       and nothing in the file extracts a representative. So a zpowers carrier for G2 cannot be
--       encoded at all - not "is awkward", but has no bytes to write.
--
--       THE ROUTE TAKEN, and it is the one the design named: make the CARRIER THE EXPONENT and let
--       the ENCODER WRITE THE FOLD'S BYTES. 'G2fold := Exp blsR' (the exponent carrier, with the
--       'Group' / 'PrimeOrderWith' / 'Module (ZMod blsR)' instances Instances/ExponentModel.lean
--       already provides), and 'g2foldToEip R := g2PointBytes (smulFrame2 R.toAdd.val h2Frame).1' -
--       the byte fold at the published H2, which is computable, lands in 'CanonPt' by
--       'smulFrame2_canonic', and is therefore decodable by (1). CANONICITY IS THE FOLD'S OWN
--       THEOREM, so no quotient is ever read back: the encoder never asks an 'Fp2' element for a
--       representative, it asks the byte model for bytes.
--
-- WHAT THAT DOES AND DOES NOT CLAIM, stated because the difference is the point. The carrier is
-- 'Z/r' written multiplicatively, NOT a set of curve points; the BYTES are real G2 bytes - every
-- frame the encoder emits is the EIP encoding of a genuine r-torsion point of y^2 = x^3 + 4(u+1)
-- over Fp2, computed by the byte-level fold that Instances/G2Agreement.lean proves agrees with
-- mathlib's group law ('emb2_smul'). So 'g2Valid' is discharged at a NON-DEGENERATE codec:
-- 'g2foldToEip' is injective ('addOrderOf_emb2_h2' - the exponent is recoverable), it is not the
-- constant all-zero map ('g2foldToEip_not_constant', 'g2foldToEip_not_the_zero_frame'), and its
-- image is a cyclic order-r set of accepted frames. What it is NOT is a claim that every accepted
-- G2 frame decodes into the carrier - that is the discrete log, and 'Holds' has no g2Decodes
-- clause (D-P34's note in gap_g2_no_fp2_model).
--
-- WHY THIS FILE HAS NO '#eval' LINE, and so no gate of its own: it is a theorem file, and the two
-- heavy computations it leans on ('h2Pair_r_smul_zero' at 16 s and 'g2PointBytes_inf' at 4.4 s) are
-- kernel 'decide's that 'lake build' caches in the olean. P-G2B step 3 moves the first of them out
-- of the '#eval'-bearing file for exactly that reason; a '#eval' here would put it back.
--
-- D-P23: every claim here carries a witness AND a falsification AS THEOREMS. The honest limit,
-- stated rather than glossed: 'checks.sh' runs the '#eval' lines and 'lake build' runs the
-- theorems, and NOTHING in either deletes a falsification theorem and reddens the build. That gap
-- has been measured twelve times in this project; this package measured it a thirteenth time (see
-- the report) and did not pretend otherwise.
import Midfall.Instances.G2Agreement
import Midfall.Instances.ExponentModel

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions WeierstrassCurve WeierstrassCurve.Affine

private theorem p_pos2b : 0 < blsP := Nat.Prime.pos (Fact.out : Nat.Prime blsP)
private theorem r_prime2b : Nat.Prime blsR := Fact.out (p := Nat.Prime blsR)

/-- 'blsP < 256 ^ fpBytes', re-derived: the G1 file's copy is private. -/
private theorem blsP_lt_fpBytes_pow2 : blsP < 256 ^ fpBytes := by decide

/-- **THE RE-DERIVATION P-G2 NAMED.** 'bytesAppend_size' is private in Instances/G1Agreement.lean;
    these three lines are the whole of blocker (1)'s first half. -/
private theorem bytesAppend_size2 (A B : Bytes) :
    (bytesAppend A B).size = A.size + B.size := by
  show (A.data ++ B.data).size = _
  exact Array.size_append

/-- Appending to the empty buffer is the identity: 'g2PointBytes' is a 'foldl' that starts at
    'Bytes.empty', so the innermost append is vacuous and the nest that matters is three deep. -/
private theorem bytesAppend_empty_left (A : Bytes) : bytesAppend Bytes.empty A = A := by
  show ByteArray.mk (#[] ++ A.data) = A
  rw [Array.empty_append]

/-- 'bytesZero' has the width it names, re-derived: the G1 file's copy is private. -/
private theorem bytesZero_size2 (n : Nat) : (bytesZero n).size = n := by
  show ((List.replicate n 0).toArray).size = n
  rw [Array.size_eq_length_toList, List.toList_toArray, List.length_replicate]

/-- A padded coordinate is 64 bytes: 'fpCoordBytes_size' restated at the literal, which is the form
    the window side conditions want. -/
private theorem fpCoord64 (x : Nat) : (fpCoordBytes x).size = 64 := by
  rw [fpCoordBytes_size]
  rfl

/-- The same equation read in the direction the window lemmas' hypotheses are stated in. Stating it
    as its own lemma is not decoration: 'Nat.le_of_eq (fpCoord64 x)' has type 'size ≤ 64', the WRONG
    direction, and making the elaborator repair it is one of the whnf walls below. -/
private theorem le64 (x : Nat) : 64 ≤ (fpCoordBytes x).size := by
  rw [fpCoord64]

/-- **THE NEST UNFOLDED.** 'g2PointBytes' is a four-element 'foldl'; at a VARIABLE point the fold
    still reduces, because the list is a literal and only its ENTRIES are variables. -/
private theorem g2PointBytes_nest (P : AffinePt (Nat × Nat)) :
    g2PointBytes P =
      bytesAppend (bytesAppend (bytesAppend (fpCoordBytes P.1.1) (fpCoordBytes P.1.2))
        (fpCoordBytes P.2.1)) (fpCoordBytes P.2.2) := by
  show (bytesAppend (bytesAppend (bytesAppend (bytesAppend Bytes.empty (fpCoordBytes P.1.1))
        (fpCoordBytes P.1.2)) (fpCoordBytes P.2.1)) (fpCoordBytes P.2.2)) = _
  rw [bytesAppend_empty_left]

/-- The two intermediate nest widths, pre-proved ONCE rather than rediscovered per lemma. -/
private theorem g2Nest_sizes (P : AffinePt (Nat × Nat)) :
    (bytesAppend (fpCoordBytes P.1.1) (fpCoordBytes P.1.2)).size = 128 ∧
      (bytesAppend (bytesAppend (fpCoordBytes P.1.1) (fpCoordBytes P.1.2))
        (fpCoordBytes P.2.1)).size = 192 := by
  refine ⟨by rw [bytesAppend_size2, fpCoord64, fpCoord64], ?_⟩
  rw [bytesAppend_size2, bytesAppend_size2, fpCoord64, fpCoord64, fpCoord64]

/-- 'bytesSlice' at the whole width, stated so the width is a LITERAL and the equation supplying it
    is a hypothesis. The reason this helper exists: 'bytesSlice_full A' asks the elaborator to unify
    '?A.size' with a literal, and for 'A := fpCoordBytes x' with 'x' a variable that unification
    whnfs 'ByteArray.size (bytesNatBE x 48)' - the 48-step byte-recursion on a stuck argument - and
    that single whnf is the wall P-G2 hit. It is NOT a heartbeat budget problem: with the size
    supplied as an equation the four window lemmas below elaborate inside the DEFAULT 200k budget
    (measured: each is under 1 s at 'maxHeartbeats 50000'). -/
private theorem slice_whole (A : Bytes) (n : Nat) (h : n = A.size) : bytesSlice A 0 n = A := by
  subst h
  exact bytesSlice_full A

/-! ### THE FOUR SLICE WINDOWS (blocker 1)

THE WALL, MEASURED, AND THE CURE. P-G2 predicted these four lemmas would need
'maxHeartbeats 400000000' and did not get to try it. They do not, but they DO need two things the
first attempt here did not do, and both are the same whnf:

* Do not state the goal with 'g2PointBytes P' and 'exact' a chain built over the unfolded nest:
  unifying 'g2PointBytes P' with the nest forces the elaborator to whnf the 'foldl' AND to compare
  'bytesAppend Bytes.empty (fpCoordBytes x)' with 'fpCoordBytes x', which drags in
  'ByteArray.size (bytesNatBE x 48)' on a stuck 'x'. That whnf alone ate the whole 200k budget and
  then some: at 'maxHeartbeats 4e8' it does not finish in 18 minutes. The cure is the one this
  project always reaches for - rewrite the structural equation FIRST ('rw [g2PointBytes_nest]') so
  the goal and the proof term agree syntactically, and never let the elaborator choose.
* Supply every size as an equation ('g2Nest_sizes', 'fpCoord64') and discharge the window bounds
  with 'omega' over those hypotheses, rather than rewriting with them. 'omega' treats 'size' as an
  atom; 'rw' whnfs. -/

/-- **WINDOW 1 OF 4**: bytes 0..64 of a G2 encoding are 'x.c0'. -/
theorem bytesSlice_g2PointBytes_x0 (P : AffinePt (Nat × Nat)) :
    bytesSlice (g2PointBytes P) 0 64 = fpCoordBytes P.1.1 := by
  rw [g2PointBytes_nest]
  obtain ⟨h128, h192⟩ := g2Nest_sizes P
  have h64 := fpCoord64 P.1.1
  refine ((bytesSlice_window_before 0 64 ?_).trans
      (bytesSlice_window_before 0 64 ?_)).trans
      ((bytesSlice_window_before 0 64 ?_).trans (slice_whole _ 64 ?_))
  · omega
  · omega
  · omega
  · exact h64.symm

/-- **WINDOW 2 OF 4**: bytes 64..128 are 'x.c1'. -/
theorem bytesSlice_g2PointBytes_x1 (P : AffinePt (Nat × Nat)) :
    bytesSlice (g2PointBytes P) 64 64 = fpCoordBytes P.1.2 := by
  rw [g2PointBytes_nest]
  obtain ⟨h128, h192⟩ := g2Nest_sizes P
  refine ((bytesSlice_window_before 64 64 ?_).trans
      (bytesSlice_window_before 64 64 ?_)).trans
      ((bytesSlice_window_after 64 64 ?_ ?_).trans (slice_whole _ 64 ?_))
  · omega
  · omega
  · exact (fpCoord64 P.1.1).symm
  · exact le64 P.1.2
  · exact (fpCoord64 P.1.2).symm

/-- **WINDOW 3 OF 4**: bytes 128..192 are 'y.c0'. -/
theorem bytesSlice_g2PointBytes_y0 (P : AffinePt (Nat × Nat)) :
    bytesSlice (g2PointBytes P) 128 64 = fpCoordBytes P.2.1 := by
  rw [g2PointBytes_nest]
  obtain ⟨h128, h192⟩ := g2Nest_sizes P
  refine ((bytesSlice_window_before 128 64 ?_).trans
      ((bytesSlice_window_after 128 64 ?_ ?_).trans (slice_whole _ 64 ?_)))
  · omega
  · exact h128.symm
  · exact le64 P.2.1
  · exact (fpCoord64 P.2.1).symm

/-- **WINDOW 4 OF 4**: bytes 192..256 are 'y.c1'. -/
theorem bytesSlice_g2PointBytes_y1 (P : AffinePt (Nat × Nat)) :
    bytesSlice (g2PointBytes P) 192 64 = fpCoordBytes P.2.2 := by
  rw [g2PointBytes_nest]
  obtain ⟨_, h192⟩ := g2Nest_sizes P
  refine ((bytesSlice_window_after 192 64 ?_ ?_).trans (slice_whole _ 64 ?_))
  · exact h192.symm
  · exact le64 P.2.2
  · exact (fpCoord64 P.2.2).symm

/-- A G2 encoding is exactly 'g2Bytes = 0x100' bytes, for every point, canonical or not. -/
theorem g2PointBytes_size (P : AffinePt (Nat × Nat)) : (g2PointBytes P).size = g2Bytes := by
  rw [g2PointBytes_nest, bytesAppend_size2, bytesAppend_size2, bytesAppend_size2,
    fpCoord64, fpCoord64, fpCoord64, fpCoord64]
  rfl

/-- **THE 0x100 ROUND TRIP.** The decoder reads back what the encoder wrote, for every point whose
    four coordinates are canonical - which is what 'CanonPt' says and what 'smulFrame2_canonic'
    delivers for free. Four slice windows, then four coordinate round trips. -/
theorem g2Of?_g2PointBytes (P : AffinePt (Nat × Nat)) (hP : CanonPt P) :
    g2Of? (g2PointBytes P) = some P := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := hP
  unfold g2Of?
  rw [bytesSlice_g2PointBytes_x0, bytesSlice_g2PointBytes_x1,
      bytesSlice_g2PointBytes_y0, bytesSlice_g2PointBytes_y1,
      fpCoordOf?_fpCoordBytes P.1.1 h1, fpCoordOf?_fpCoordBytes P.1.2 h2,
      fpCoordOf?_fpCoordBytes P.2.1 h3, fpCoordOf?_fpCoordBytes P.2.2 h4]

/-- **WITNESS FOR THE ROUND TRIP (D-P23 satisfiability)**, at the published H2. -/
theorem g2Of?_g2PointBytes_h2Pair : g2Of? (g2PointBytes h2Pair) = some h2Pair :=
  g2Of?_g2PointBytes h2Pair h2Frame_canonical

/-- **FALSIFICATION FOR THE ROUND TRIP (D-P23): the canonicity hypothesis is load-bearing.** A
    first coordinate of 'blsP' is not below 'blsP', so the decoder refuses the encoding of a frame
    the encoder writes happily - 'g1Of?_g1PointBytes_needs_canonical' arrived at from the first
    window instead of the second. -/
theorem g2Of?_g2PointBytes_needs_canonical :
    g2Of? (g2PointBytes ((blsP, 0), (0, 0))) = none := by
  classical
  have hx0 : fpCoordOf? (bytesSlice (g2PointBytes ((blsP, 0), (0, 0))) 0 64) = none := by
    rw [bytesSlice_g2PointBytes_x0,
        fpCoordOf?_fpCoordBytes_none_of_too_big blsP (Nat.lt_irrefl blsP)
          blsP_lt_fpBytes_pow2]
  unfold g2Of?
  rw [hx0]

/-! ### THE EXPONENT-FOLD CARRIER (blocker 2) -/

/-- **THE G2 CARRIER: THE EXPONENT-FOLD CARRIER.** The exponent group 'Z/r' written
    multiplicatively, with the instances 'Holds' needs already supplied by Instances/ExponentModel
    .lean ('Group' from 'Multiplicative', 'expPrimeOrderWith', 'expModule'). It is NOT a set of
    curve points and does not pretend to be: the header says why a curve-point carrier cannot be
    encoded over 'Fp2' at all, and what the encoder below does instead. -/
abbrev G2fold : Type := Exp blsR

/-- The carrier element of exponent 'n'. -/
def g2foldExp (n : Nat) : G2fold := Multiplicative.ofAdd (n : ZMod blsR)

theorem g2foldExp_val (n : Nat) (hn : n < blsR) : (g2foldExp n).toAdd.val = n := by
  show ((n : ZMod blsR)).val = n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

theorem g2foldExp_zero : (g2foldExp 0 : G2fold) = 1 := rfl

theorem g2foldExp_one_ne_one : (g2foldExp 1 : G2fold) ≠ 1 := by
  intro h
  have := congrArg Multiplicative.toAdd h
  exact (by decide : (1 : ZMod blsR) ≠ 0) this

/-- **THE FRAME THE ENCODER WRITES**: the byte fold at the published H2, at the element's exponent.
    Everything computable about a G2 point goes through this. -/
def g2foldFrame (R : G2fold) : Fp2Frame := smulFrame2 R.toAdd.val h2Frame

theorem g2foldFrame_val (R : G2fold) :
    (g2foldFrame R).1 = affineSmul fp2Ops R.toAdd.val h2Pair :=
  smulFrame2_val _ _

/-- **CANONICAL, FOR FREE.** The hinge of the design: the fold's output coordinates are below
    'blsP' by 'smulFrame2_canonic', so the encoder's bytes are decodable without ever extracting a
    representative from an 'AdjoinRoot' quotient. -/
theorem g2foldFrame_canonical (R : G2fold) : CanonicalFrame2 (g2foldFrame R) :=
  smulFrame2_canonic _ _ h2Frame_canonical

theorem g2foldFrame_emb (R : G2fold) :
    emb2 (g2foldFrame R) = R.toAdd.val • emb2 h2Frame := (emb2_smul _ _).symm

/-- **EVERY CARRIER ELEMENT IS r-TORSION**: the fold's point is 'n • H2' and 'r • H2 = 0', so
    'r • (n • H2) = n • (r • H2) = 0'. No point count and no Fp2 pigeonhole - the same D-P34 route
    that made the G1 side prime-order. -/
theorem g2foldFrame_r_smul (R : G2fold) : blsR • emb2 (g2foldFrame R) = 0 := by
  rw [g2foldFrame_emb, smul_smul, Nat.mul_comm, ← smul_smul, r_nsmul_emb2_h2, nsmul_zero]

/-- **THE ENCODER**: the EIP-2537 padded 0x100 bytes of the fold's frame. -/
def g2foldToEip (R : G2fold) : Bytes := g2PointBytes (g2foldFrame R).1

/-- The encoder emits exactly the width the pairing layout reads. -/
theorem g2foldToEip_size (R : G2fold) : (g2foldToEip R).size = g2Bytes :=
  g2PointBytes_size _

/-- **THE DECODED POINT IS THE FOLD'S FRAME** - the round trip, at the carrier. -/
theorem g2Of?_g2foldToEip (R : G2fold) :
    g2Of? (g2foldToEip R) = some (g2foldFrame R).1 :=
  g2Of?_g2PointBytes _ (g2foldFrame_canonical R)

/-- **THE PRECOMPILE'S OWN VALIDATOR ACCEPTS EVERY ENCODING.** -/
theorem g2PointValid_g2fold (R : G2fold) : g2PointValid (g2foldFrame R).1 = true :=
  (g2PointValid_iff2 (g2foldFrame R) (g2foldFrame_canonical R)).mpr (g2foldFrame_r_smul R)

/-- **'g2Valid', DISCHARGED AT A NON-DEGENERATE CODEC.** The quantifier is over the whole carrier,
    the encoder is the byte fold at the published H2, and the validator is the precompile's own.
    This is the clause P-G2 left as plumbing, and the plumbing was what it said: four slice windows
    and a carrier that can be written down. -/
theorem g2fold_g2Valid :
    ∀ R : G2fold, ∃ pt, g2Of? (g2foldToEip R) = some pt ∧ g2PointValid pt = true :=
  fun R => ⟨(g2foldFrame R).1, g2Of?_g2foldToEip R, g2PointValid_g2fold R⟩

/-- **THE ADDITIVE ORDER OF H2 IS EXACTLY r.** 'r • H2 = 0' is the kernel 'decide' P-G2 computed
    (16 s of elaboration, cached in the olean), 'H2 ≠ 0' is 'emb2_h2_ne_zero', and primality of r
    closes it. Instances/G1PointCount.lean's 'addOrderOf_genFrame' is the template; the mirror costs
    the same four lines. -/
theorem addOrderOf_emb2_h2 : addOrderOf (emb2 h2Frame) = blsR := by
  refine (Nat.Prime.eq_one_or_self_of_dvd r_prime2b _
      (addOrderOf_dvd_of_nsmul_eq_zero r_nsmul_emb2_h2)).resolve_left ?_
  intro h1
  have hz : (1 : ℕ) • emb2 h2Frame = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, h1]
  rw [one_nsmul] at hz
  exact emb2_h2_ne_zero hz

theorem nsmul_emb2_h2_eq_zero_iff (k : ℕ) : k • emb2 h2Frame = 0 ↔ blsR ∣ k := by
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_emb2_h2]

/-- **THE ENCODER IS INJECTIVE**, so the decoder below is well defined and the carrier is not
    collapsed onto itself. The argument is the ORDER of H2 and not a byte fact: equal bytes decode
    to equal frames, equal frames are equal points, so the difference of the two exponents kills H2
    - and 'addOrderOf_emb2_h2' forces that difference to be a multiple of r, while both
    representatives sit in '[0, r)'. -/
theorem g2foldToEip_injective : Function.Injective g2foldToEip := by
  classical
  intro P Q h
  have e1 : g2Of? (g2foldToEip P) = some (g2foldFrame P).1 := g2Of?_g2foldToEip P
  have e2 : g2Of? (g2foldToEip Q) = some (g2foldFrame Q).1 := g2Of?_g2foldToEip Q
  have e3 : g2Of? (g2foldToEip P) = g2Of? (g2foldToEip Q) := congrArg g2Of? h
  rw [e1, e2] at e3
  have hf : g2foldFrame P = g2foldFrame Q := Subtype.ext (Option.some.inj e3)
  -- 'congrArg emb2' and then two rewrites, rather than a term-mode chain: unifying a goal that
  -- mentions 'emb2 (g2foldFrame P)' against a term that mentions the exponent smul forces the
  -- elaborator to whnf 'g2Of?' over a symbolic nest, which is the same wall as the slice lemmas.
  have hsmul : P.toAdd.val • emb2 h2Frame = Q.toAdd.val • emb2 h2Frame := by
    have h4 : emb2 (g2foldFrame P) = emb2 (g2foldFrame Q) := congrArg emb2 hf
    rwa [g2foldFrame_emb, g2foldFrame_emb] at h4
  have hp : P.toAdd.val < blsR := ZMod.val_lt _
  have hq : Q.toAdd.val < blsR := ZMod.val_lt _
  rcases Nat.lt_trichotomy P.toAdd.val Q.toAdd.val with hlt | heq | hgt
  · have h1 : (Q.toAdd.val - P.toAdd.val) • emb2 h2Frame
        = Q.toAdd.val • emb2 h2Frame + -(P.toAdd.val • emb2 h2Frame) :=
      sub_nsmul _ (Nat.le_of_lt hlt)
    have hdiff : (Q.toAdd.val - P.toAdd.val) • emb2 h2Frame = 0 := by
      rw [h1, hsmul]
      abel
    obtain hdvd := (nsmul_emb2_h2_eq_zero_iff _).mp hdiff
    have hge := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
    have hlt2 : Q.toAdd.val - P.toAdd.val < blsR := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq
    omega
  · exact Multiplicative.ext (ZMod.val_injective blsR heq)
  · have h1 : (P.toAdd.val - Q.toAdd.val) • emb2 h2Frame
        = P.toAdd.val • emb2 h2Frame + -(Q.toAdd.val • emb2 h2Frame) :=
      sub_nsmul _ (Nat.le_of_lt hgt)
    have hdiff : (P.toAdd.val - Q.toAdd.val) • emb2 h2Frame = 0 := by
      rw [h1, hsmul.symm]
      abel
    obtain hdvd := (nsmul_emb2_h2_eq_zero_iff _).mp hdiff
    have hge := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd
    have hlt2 : P.toAdd.val - Q.toAdd.val < blsR := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hp
    omega

/-- **THE DECODER, NONCOMPUTABLY.** The same wall as 'g1zOfEip?' and the same shape of answer:
    reading an exponent off a frame is a discrete log, so the decoder is a 'Classical.choose' over
    the encoder's image. Injectivity above is what makes the choice unique, and so what makes the
    ENCODER-FIRST law below hold. -/
noncomputable def g2foldOfEip? (b : Bytes) : Option G2fold := by
  classical
  exact if h : ∃ R : G2fold, g2foldToEip R = b then some (Classical.choose h) else none

/-- **THE ENCODER-FIRST FRAME LAW FOR G2**: 'd₂ (c₂.toEip R) = some R', the third field of
    'FrameLaws'. -/
theorem g2foldOfEip?_g2foldToEip (R : G2fold) : g2foldOfEip? (g2foldToEip R) = some R := by
  classical
  have hex : ∃ S : G2fold, g2foldToEip S = g2foldToEip R := ⟨R, rfl⟩
  unfold g2foldOfEip?
  rw [dif_pos hex]
  exact congrArg some (g2foldToEip_injective (Classical.choose_spec hex))

/-- **THE G2 ENCODER AS A 'G2Enc'**, the structure 'Holds' quantifies over. -/
def g2CodecFold : G2Enc G2fold where
  toEip := g2foldToEip

theorem g2CodecFold_toEip (R : G2fold) : g2CodecFold.toEip R = g2foldToEip R := rfl

/-- **THE DECODER INVERTS THE ENCODER AT THE 'G2Enc' WRAPPER** - the two 'FrameLaws' fields for G2,
    as one declaration, so the exhibit cannot silently drop one of them. -/
theorem g2CodecFold_frameLaws_g2 :
    (∀ R : G2fold, g2foldOfEip? (g2CodecFold.toEip R) = some R) ∧
      (∀ R : G2fold, (g2CodecFold.toEip R).size = g2Bytes) :=
  ⟨fun R => g2foldOfEip?_g2foldToEip R, fun R => g2foldToEip_size R⟩

/-! ### D-P23: witnesses and falsifications for the codec -/

/-- The fold at exponent 1 is the generator frame - one byte step, so this 'decide' is cheap and
    belongs in a gate; the fold at 'blsR' is the 16 s one and does not. -/
private theorem g2foldFrame_gen : (g2foldFrame (g2foldExp 1)).1 = h2Pair := by
  show (smulFrame2 (g2foldExp 1).toAdd.val h2Frame).1 = h2Pair
  rw [g2foldExp_val 1 (by decide), smulFrame2_val]
  exact beq_iff_eq.mp (by decide : affineSmul fp2Ops 1 h2Pair == h2Pair)

private theorem g2foldFrame_id : (g2foldFrame (1 : G2fold)).1 = ((0, 0), (0, 0)) := by
  show (smulFrame2 (1 : G2fold).toAdd.val h2Frame).1 = _
  rw [show ((1 : G2fold).toAdd.val : Nat) = 0 from rfl, smulFrame2_val]
  exact beq_iff_eq.mp (by decide : affineSmul fp2Ops 0 h2Pair == ((0, 0), (0, 0)))

/-- **WITNESS FOR 'g2fold_g2Valid' (D-P23 satisfiability), AT THE GENERATOR EXPONENT**: the decoded
    point IS the published H2 byte frame - not the identity, and not a point anybody chose. -/
theorem g2fold_g2Valid_witness :
    ∃ pt, g2Of? (g2foldToEip (g2foldExp 1)) = some pt ∧ g2PointValid pt = true ∧
      pt = h2Pair := by
  classical
  refine ⟨h2Pair, ?_, g2PointValid_h2Pair, rfl⟩
  rw [← g2foldFrame_gen, ← g2Of?_g2foldToEip]

/-- **FALSIFICATION FOR THE CODEC (D-P23): 'g2foldToEip' IS NOT A CONSTANT MAP.** If it were, the
    clause above would be the vacuity the old gap wording walked into. The generator exponent and the
    identity exponent encode differently, because H2 is not the point at infinity. -/
theorem g2foldToEip_not_constant :
    g2foldToEip (g2foldExp 1) ≠ g2foldToEip (1 : G2fold) := by
  classical
  intro h
  have e1 : g2Of? (g2foldToEip (g2foldExp 1)) = some h2Pair := by
    rw [← g2foldFrame_gen, ← g2Of?_g2foldToEip]
  have e2 : g2Of? (g2foldToEip (1 : G2fold)) = some ((0, 0), (0, 0)) := by
    rw [← g2foldFrame_id, ← g2Of?_g2foldToEip]
  have e3 : some h2Pair = some ((0, 0), (0, 0)) := by rw [← e1, ← e2, h]
  exact (by decide : h2Pair ≠ ((0, 0), (0, 0))) (Option.some.inj e3)

/-- **FALSIFICATION FOR THE DECODER (D-P23): 'g2foldOfEip?' REFUSES FRAMES OUTSIDE THE IMAGE.**
    Width is the cheap witness - every encoding is exactly 'g2Bytes' long - and the interesting one
    is a WIDTH-CORRECT frame that is not an encoding at all: the junk frame whose first coordinate
    is 'blsP' has the right length and is refused by the decoder before the carrier is consulted.
    So the encoder-first law above is not the vacuous truth of a decoder that accepts everything. -/
theorem g2foldOfEip?_refuses_outside_the_image :
    g2foldOfEip? (bytesZero (g2Bytes + 1)) = none ∧
      g2foldOfEip? (g2PointBytes ((blsP, 0), (0, 0))) = none := by
  classical
  refine ⟨dif_neg ?_, dif_neg ?_⟩
  · intro hex
    obtain ⟨R, hR⟩ := hex
    have hs : (g2foldToEip R).size = g2Bytes := g2foldToEip_size R
    rw [hR, bytesZero_size2] at hs
    omega
  · intro hex
    obtain ⟨R, hR⟩ := hex
    have e1 : g2Of? (g2foldToEip R) = some (g2foldFrame R).1 := g2Of?_g2foldToEip R
    rw [hR, g2Of?_g2PointBytes_needs_canonical] at e1
    exact absurd e1.symm (Option.some_ne_none _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **THE ZERO FRAME IS ACCEPTED**, which is the half of the step-2 correction that the old gap
    wording needed and never checked: 'g2Of?' reads the 0x100 all-zero word as the point at
    infinity and 'g2PointValid' short-circuits on that branch. MEASURED: this 'decide' costs about
    4.4 s of elaboration - the byte half of what P-G2 attributed to the gate - which is one reason
    this file carries no '#eval' line. -/
theorem g2PointBytes_inf : bytesZero g2Bytes = g2PointBytes ((0, 0), (0, 0)) := by
  show bytesZero 256 = _
  decide

theorem g2Valid_zero_frame : g2Of? (bytesZero g2Bytes) = some ((0, 0), (0, 0)) ∧
    g2PointValid ((0, 0), (0, 0)) = true := by
  classical
  refine ⟨?_, by decide⟩
  rw [g2PointBytes_inf]
  exact g2Of?_g2PointBytes ((0, 0), (0, 0)) ⟨p_pos2b, p_pos2b, p_pos2b, p_pos2b⟩

/-- **THE OVER-STATEMENT, MADE PRECISE AS A THEOREM (P-G2B step 2).** 'gap_g2_no_fp2_model' said
    'g2Valid' had nothing to quantify over. It did not: the clause is satisfied on ANY carrier by
    the CONSTANT all-zero encoder, because 'g2Of?' accepts the 0x100 zero frame
    ('g2Valid_zero_frame') and 'g2PointValid' short-circuits on the infinity branch. What was
    missing was a non-degenerate codec, not a field. This is the half that makes the correction a
    claim that can fail rather than a sentence: the degenerate encoder really does discharge the
    clause, on the very carrier the real codec uses. -/
theorem g2Valid_degenerate_constant_encoder :
    ∀ _R : G2fold, ∃ pt, g2Of? (bytesZero g2Bytes) = some pt ∧ g2PointValid pt = true :=
  fun _R => ⟨((0, 0), (0, 0)), (g2Valid_zero_frame).1, (g2Valid_zero_frame).2⟩

/-- **AND THE FALSIFICATION OF THAT DEGENERACY (D-P23): the constant encoder cannot be part of a
    'FrameLaws' pair at all.** It discharges 'g2Valid' and nothing else, because no decoder inverts
    a constant map on a carrier with two elements. This is the wall the old wording walked past,
    stated as a theorem: non-degeneracy is not a stylistic preference, it is what the rest of the
    bundle asks for. -/
theorem constant_encoder_has_no_decoder :
    ¬ ∃ d₂ : Bytes → Option G2fold, ∀ R : G2fold, d₂ (bytesZero g2Bytes) = some R := by
  rintro ⟨d₂, h⟩
  have h1 := h (1 : G2fold)
  have h2 := h (g2foldExp 1)
  rw [h1] at h2
  exact g2foldExp_one_ne_one (Option.some.inj h2.symm)

/-- **THE G2 CODEC IS NOT THE DEGENERATE ONE**: the real encoder's bytes on the generator exponent
    are not the all-zero frame. Together with 'g2Valid_degenerate_constant_encoder' this pins the
    distinction the corrected gap record rests on. -/
theorem g2foldToEip_not_the_zero_frame : g2foldToEip (g2foldExp 1) ≠ bytesZero g2Bytes := by
  classical
  intro h
  have e1 : g2Of? (g2foldToEip (g2foldExp 1)) = some h2Pair := by
    rw [← g2foldFrame_gen, ← g2Of?_g2foldToEip]
  have e2 : some h2Pair = some ((0, 0), (0, 0)) := by rw [← e1, h, (g2Valid_zero_frame).1]
  exact (by decide : h2Pair ≠ ((0, 0), (0, 0))) (Option.some.inj e2)

#print axioms g2fold_g2Valid
#print axioms g2foldToEip_injective

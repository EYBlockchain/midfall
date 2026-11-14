--      factorisation of p - 1 and a reduce_mod_char proof per prime factor at 381 bits,
-- Midfall.Instances.Bls12_381G1
--
-- P-CURVE (docs/plans/P-CURVE-real-g1.md): the real-curve G1 type and codec, and the
-- precise location of what an Eip2537.Holds exhibit still needs.
--
-- WHAT THIS FILE IS. G1 as the EIP-2537 precompile sees it: the set of 128-byte frames whose
-- two padded coordinates are canonical, satisfy y^2 = x^3 + 4 over Fp, and are in the
-- r-torsion - exactly what Midfall/Yul/Externals.lean's g1Of? and g1PointMsmValid accept,
-- which is the pair the g1Valid and g1Decodes clauses quantify over. Elements ARE real curve
-- points (the generator below is the published H1 and its r-torsion membership is a kernel
-- proof, not an assertion), and the codec is the byte codec: toEip is the identity on a
-- frame, ofEip? is the validator. That makes two of the six Holds clauses TRUE over real
-- curve points AT THIS CODEC - g1Valid, and g1Decodes in the width-repaired form - and the
-- frame type is not the carrier the exhibit uses: g1CodecZ on the zpowers carrier G₁z
-- discharges FOUR of six (g1CodecZ_g1_four, Instances/G1PointCount.lean). Which is the part
-- of the brief that is achievable, and it is achievable in Instances/ rather than in
-- Assumptions/ because D-P17 keeps a concrete curve out of theorem-bearing files.
--
-- WHAT THIS FILE IS NOT. Three findings, in order of how much they cost.
--
--   1. THE CLAUSE THAT BLOCKED FIRST WAS NOT A CURVE CLAUSE AT ALL, AND IT IS NOW REPAIRED.
--      g1Decodes as written was unsatisfiable for every codec on every prime-order group, curve
--      model included; Midfall/Assumptions/Eip2537.lean proves it of the pinned old text
--      (g1DecodesOld_unsatisfiable, holdsOld_unsatisfiable, not_exists_holdsOld) and the width
--      condition b.size == g1Bytes is now the live field (R-63 level 1, applied by P-HOLDS). So
--      the four-way bundle BlkIsEmitter /\ SupportedS /\ EnvAgrees /\ Eip2537.Holds is no longer
--      refuted BY THE CLAUSE: this file discharges the repaired clause outright
--      (g1FrameCodec_decodesWidth) and refutes the pinned old text (g1FrameCodec_not_g1DecodesOld).
--      What the repair does NOT buy is the exhibit: repairing g1Decodes unblocks the clause,
--      not the exhibit, for the two reasons below.
--   2. G1Frame IS NOT A GROUP, AND CANNOT BE MADE INTO ONE HERE - THOUGH THE CLAUSES THAT
--      DEPENDED ON IT ARE PROVED ANYWAY, ON A DIFFERENT CARRIER. The obstruction is not the
--      codec and not the byte model: affineAdd and affineSmul in Externals.lean are integer
--      arithmetic on decoded bytes, and the facts that would make them a group law - the sum
--      of two on-curve points is on-curve, the chord-and-tangent law is associative, r * P = O
--      for every valid P - are statements about the FIELD Fp. Stating them in mathlib's terms
--      (AlgebraicGeometry/EllipticCurve, whose affine group law is proved at
--      Affine/Point.lean:805) needs a Field instance on ZMod pBase, i.e. Fact (Nat.Prime
--      pBase): a 381-bit primality proof. THE TREE NOW HAS ONE: Assumptions/BasePrime.lean
--      proves Nat.Prime pBase by a Lucas/Pratt certificate (CompPoly's pattern for r, extended
--      to the base modulus), so ZMod pBase is a Field and the blocker below is construction,
--      not a missing fact: the group law on the FRAME type still has to be BUILT, and the
--      agreement of affineAdd with mathlib's AffinePoint.add still has to be proved AT THE
--      FRAME TYPE. WHAT P-GAPFIX CORRECTS IN THIS HEADER is the sentence that used to follow,
--      "until that construction exists g1Add and g1Msm1 cannot be stated for all points at
--      all". That is no longer true and was overtaken by P-G1AGREE and P-G1CODEC: the general
--      statements exist on the zpowers carrier G₁z, whose group law is mathlib's own on
--      WeierstrassCurve.Affine.Point, and g1CodecZ_g1Add and g1CodecZ_g1Msm1 are theorems
--      about EVERY point of that carrier (jointly with g1Valid and g1Decodes in
--      g1CodecZ_g1_four, Instances/G1PointCount.lean). So the frame type's missing Group
--      instance is now redundant plumbing rather than the wall: the exhibit does not need it,
--      because it has a carrier that already has one. What is demonstrated below is still
--      what it always was - the concrete instances of those equations on real frames, as
--      gates, at the byte codec rather than at the subgroup carrier.
--   3. G1Frame STILL HAS NO PRIME ORDER INSTANCE - BUT THE COUNT THAT USED TO BE BLAMED FOR
--      IT IS A THEOREM NOW, AND THAT CHANGED WHAT THIS FILE IS. PrimeOrderWith G1Frame r is
--      Nat.card G1Frame = r: the r-torsion of E(Fp) has exactly r elements. This header used
--      to say that proving it needs a point count of E over Fp (Schoof-Elkies-Atkin, which no
--      Lean library has) or the n-torsion structure theorem plus gcd(r, p - 1) = 1, and that
--      the demand "a prime-order group whose codec hits EVERY precompile-valid frame" IS a
--      statement about how many curve points there are. Every clause of that was overtaken:
--      P-POINTCOUNT proved the count by a third route nobody had priced - #E(Fp) <= 2p+1 (two
--      square roots per x, no Hasse bound) squeezed against 2p+1 < r^2 forces every r-torsion
--      point into the cyclic subgroup generated by the published generator
--      (Instances/G1PointCount.lean, torsion_eq_zpowers_gen), with no Weil pairing, no
--      structure theorem and no new named assumption - and the carrier Holds is exhibited on
--      never needed the count at all, since PrimeOrderWith G₁z blsR follows from
--      primeOrderWith_zpowers (D-P34). So the G1 side of Holds is FOUR OF FOUR at a real-curve
--      codec (g1CodecZ_g1_four), and what is left of Holds is g2Valid and pairing2, neither of
--      which is a G1 question. gap_g1_prime_order is re-pointed to the two transport jobs that
--      actually remain.
--
-- WHY THE FRAME TYPE AND NOT AN EXPONENT TYPE. The cheaper-looking model - keep G1 as
-- Multiplicative (ZMod r) and define toEip n as the bytes of n * G - satisfies nothing this
-- file does and costs more: g1Valid then needs on-curve (n * G) for all n, which is note 2,
-- and g1Decodes needs the count of note 3 PLUS a discrete log to make ofEip? computable. The
-- frame type takes the codec as the identity, so the two codec clauses are theorems here and
-- out of reach there. The brief's diagnosis that g1Valid, g1Add and g1Msm1 are the codec-and-
-- frame clauses rather than pairing clauses is correct about WHERE the work is; what the
-- measurement adds is that the cheap half is the codec half, and the expensive half is not
-- the pairing but the field and the count.
--
-- COMPUTATION. Every Bool below is a gate evaluated by scripts/kat_gate.py in the VM. The
-- kernel proofs that need a computation are the generator's r-torsion membership (measured:
-- about 20 s of decide) and the identity frame (instant). No native_decide appears in this
-- file: the facts that need a big computation are gates, and the one that matters as a
-- theorem is proved by decide.

import Midfall.Common.Codec
import Midfall.Assumptions.Eip2537
import Midfall.Instances.Bls12_381
import Midfall.Yul.Externals

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions

/-! ### The type of precompile-accepted G1 frames -/

/-- The byte-level validator the Holds codec clauses run: a frame is accepted when it is
exactly 0x80 bytes, its two padded coordinates decode canonically (fpCoordOf? rejects a
coordinate at or above p, so this is canonicity and not merely a bound check), and the decoded
point is infinity or on the curve AND in the r-torsion. The subgroup half is deliberate:
g1PointMsmValid is what G1MSM and PAIRING_CHECK require, and g1PointAddValid - which skips it,
because EIP-2537 says G1ADD performs no subgroup check - would let the off-subgroup probe into
a frame. -/
def g1FrameValid (b : Bytes) : Bool :=
  b.size == g1Bytes &&
    match g1Of? b with
    | some pt => g1PointMsmValid pt
    | none => false

/-- G1 as the precompile sees it: the frames its own validators accept. Elements are real
    curve points in canonical EIP-2537 encoding, which is what the exponent model never was. -/
def G1Frame : Type := { b : Bytes // g1FrameValid b = true }

/-- The decoded point of a frame, computably: the decoder is g1Of? itself, with a junk default
    the subtype makes unreachable (and never inspected: point_eq proves the real branch). -/
def G1Frame.point (Q : G1Frame) : Nat × Nat := (g1Of? Q.val).getD (0, 0)

theorem G1Frame.point_eq (Q : G1Frame) : g1Of? Q.val = some Q.point := by
  cases h : g1Of? Q.val with
  | none => have := Q.prop; simp [g1FrameValid, h] at this
  | some pt => simp [G1Frame.point, h]

theorem G1Frame.point_valid (Q : G1Frame) : g1PointMsmValid Q.point = true := by
  have h := Q.prop
  simp only [g1FrameValid, Bool.and_eq_true] at h
  cases h2 : g1Of? Q.val with
  | none => simp [h2] at h
  | some pt =>
      have hpt : g1PointMsmValid pt = true := by simpa [h2] using h.2
      have hq : Q.point = pt := by simp [G1Frame.point, h2]
      rw [hq]; exact hpt

theorem G1Frame.val_size (Q : G1Frame) : Q.val.size = g1Bytes := by
  have h := Q.prop
  simp only [g1FrameValid, Bool.and_eq_true] at h
  exact (decide_eq_true_eq (p := Q.val.size = g1Bytes)).mp h.1

/-- The frame codec: toEip is the identity on the frame and ofEip? is the validator, so the
    precompile's accepted bytes and the codec's bytes are the same object. That is the whole
    point of the representation, and it is what makes the two codec clauses below theorems
    rather than obligations. Note what it does NOT need: no round trip through bytesToNatBE,
    which Assumptions/Codec.lean used to record as the thing the tree could not prove - P-BYTES
    closed it (Common/Bytes.lean, bytesToNatLE_natToBytesLE) and this def does not change: the
    exponent codec's ofEip? stays a cast rather than a decode, by design and not by gap. The
    compressed half delegates to G1Affine (Bls12_381.lean), gated against real trace bytes. -/
def g1FrameCodec : G1Codec G1Frame where
  toEip Q := Q.val
  ofEip? b := if h : g1FrameValid b = true then some ⟨b, h⟩ else none
  toCompressed Q :=
    G1Affine.toCompressed
      { isInfinity := Q.point == (0, 0), x := Q.point.1, y := Q.point.2 }
  ofCompressed? b :=
    match G1Affine.ofCompressed? b with
    | some P' => let e := G1Affine.toEip P'
                 if h : g1FrameValid e = true then some ⟨e, h⟩ else none
    | none => none

theorem g1FrameCodec_ofEip?_some {b : Bytes} {Q : G1Frame}
    (h : g1FrameCodec.ofEip? b = some Q) : Q.val = b := by
  classical
  by_cases hv : g1FrameValid b = true
  · simp only [g1FrameCodec, dif_pos hv] at h
    obtain ⟨rfl⟩ := h
    rfl
  · simp only [g1FrameCodec, dif_neg hv] at h
    exact absurd h (by simp)

/-- G1VALID, discharged at real curve points. This is the clause the exponent model fails for
    every non-identity exponent - SurfaceFixture.vkPointsKats_ok shows the failure - and the
    clause R-61 named as the reason a curve model is needed at all. Here it is a theorem about
    the frame type with no hypothesis beyond the definition, and its witness is the published
    generator, not the identity. -/
theorem g1FrameCodec_g1Valid :
    ∀ Q : G1Frame, ∃ pt, g1Of? (g1FrameCodec.toEip Q) = some pt ∧ g1PointMsmValid pt = true :=
  fun Q => ⟨Q.point, Q.point_eq, Q.point_valid⟩

/-- G1DECODES in the width-repaired form (Assumptions.Eip2537.g1DecodesWidth): every frame the
    validators accept at the EIP width is in the codec's image and re-encodes to the bytes it
    came from. This is the clause that makes a codec a codec rather than an encoder, and the
    frame type satisfies it by construction. -/
theorem g1FrameCodec_decodesWidth : g1DecodesWidth g1FrameCodec := by
  intro b hb ⟨pt, hpt, hv⟩
  have hvalid : g1FrameValid b = true := by simp [g1FrameValid, hb, hpt, hv]
  have hdecode : g1FrameCodec.ofEip? b = some ⟨b, hvalid⟩ := dif_pos hvalid
  exact ⟨⟨b, hvalid⟩, hdecode, rfl⟩

/-- The decoder-first canonicality law of Common/Codec.lean, at the real codec: whatever ofEip?
    accepts re-encodes to the bytes it was given. -/
theorem g1FrameCodec_eipRoundtrip : G1Codec.eipRoundtrip g1FrameCodec := by
  intro b Q h
  exact g1FrameCodec_ofEip?_some h

/-- THE ENCODER-FIRST LAW, which G1CodecLaws states as ofEip_toEip (Assumptions/Codec.lean:79)
    and which Common/Codec.lean:97-105 deliberately REMOVED from the G1Codec structure
    because a representation with redundant structure made it false for junk: with
    G1Affine := { isInfinity, x, y }, the value (false, 0, 0) is not a point at all, yet it
    encodes as the identity and decodes back as something else. The frame type has no junk
    to be false about - an element IS an accepted frame - so the law holds outright, by
    proof irrelevance on the subtype. -/
theorem g1FrameCodec_ofEip_toEip :
    ∀ Q : G1Frame, g1FrameCodec.ofEip? (g1FrameCodec.toEip Q) = some Q := by
  intro Q
  show (if h : g1FrameValid Q.val = true then some (⟨Q.val, h⟩ : G1Frame) else none) = some Q
  rw [dif_pos Q.prop]
  exact congrArg some (Subtype.eq rfl)

/-- AND THE PINNED OLD CLAUSE STILL FAILS HERE - for the byte reason, not a curve reason. The
    codec is not at fault; the quantifier was. Proved directly rather than by citing
    g1DecodesOld_unsatisfiable, because that theorem needs a Group and a PrimeOrderWith instance
    on G1Frame, which is exactly what note 2 and note 3 say is missing: the failure of the old
    clause does not depend on the missing group law at all. The LIVE clause is the one this
    codec satisfies (g1FrameCodec_decodesWidth), so this is a regression pin and not an open
    obligation: it reddens the day the width condition is dropped from the structure again. -/
theorem g1FrameCodec_not_g1DecodesOld : ¬ g1DecodesOld g1FrameCodec := by
  intro h
  obtain ⟨Q, _, hQ⟩ := h (garbageFrame 1) (garbageFrame_accepted 1)
  have h2 : Q.val = garbageFrame 1 := hQ
  have hsz : Q.val.size = g1Bytes := Q.val_size
  rw [h2, garbageFrame_size] at hsz
  simp [g1Bytes] at hsz

/-! ### Real points -/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- The published EIP-2537 H1 generator as a frame. Its membership of G1Frame is a KERNEL
    PROOF by decide: the coordinates are canonical, y^2 = x^3 + 4 holds, and r * G = O under
    the same affine double-and-add the precompile model computes with. Measured cost: about
    15 s of kernel reduction and about 40 M heartbeats, which is why it is proved once here and
    reused by the gates rather than re-decided, and why the double of the generator is a gate
    and not a second kernel proof of the same shape. -/
theorem g1GenFrame_valid : g1FrameValid (bytesOfWords katG1GenWords) = true := by
  decide

def g1GenFrame : G1Frame := ⟨bytesOfWords katG1GenWords, g1GenFrame_valid⟩

/-- The EIP-2537 infinity frame: 0x80 zero bytes, the encoding the contract emits for the
    identity (AccumulatorHelpers.yul:137-140) and the one the fixture's VK commitment uses.
    Cheap by decide because g1PointMsmValid short-circuits on the infinity case. -/
theorem g1InfFrame_valid : g1FrameValid (bytesZero g1Bytes) = true := by
  set_option maxRecDepth 1000000 in decide

def g1InfFrame : G1Frame := ⟨bytesZero g1Bytes, g1InfFrame_valid⟩

/-! ### Gates -/

/-- THE CODEC IS THE REAL ONE, pinned against published bytes rather than against itself.
    Line 1: the generator frame decodes to the EIP's H1 coordinates, so the type is populated
    by a point nobody chose. Line 2: the identity frame decodes to (0, 0). Line 3: the
    generator's double is a valid frame, so the type has a second distinct point and g1Valid
    is not satisfied by a two-point codec either. Line 4: the off-subgroup probe (4, y) - on
    the curve, not in the r-torsion (PrecompileSmoke.sol:137-151) - is REFUTED, so the
    validator bites on the subgroup half and not only the curve half. Line 5: a truncated
    frame is refuted. Line 6: a frame with trailing garbage is refuted at the width, which is
    the condition the repair adds and the reason the unrepaired clause is unsatisfiable.
    Lines 7-8: the codec round-trips on the generator and refuses the garbage frame. -/
def g1FrameCodecKats_ok : Bool :=
  (match g1Of? (g1FrameCodec.toEip g1GenFrame) with
   | some pt => pt.1 == 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb &&
                pt.2 == 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1
   | none => false) &&
  (match g1Of? (g1FrameCodec.toEip g1InfFrame) with
   | some pt => pt == (0, 0)
   | none => false) &&
  g1FrameValid (bytesOfWords katG1DoubleWords) &&
  ! g1FrameValid (bytesOfWords katOffSubgroupWords) &&
  ! g1FrameValid (bytesSlice (bytesOfWords katG1GenWords) 0 127) &&
  ! g1FrameValid (garbageFrame 1) &&
  (match g1FrameCodec.ofEip? (g1FrameCodec.toEip g1GenFrame) with
   | some Q => Q.val == g1GenFrame.val
   | none => false) &&
  (match g1FrameCodec.ofEip? (garbageFrame 1) with
   | some _ => false
   | none => true) &&
  (g1FrameCodec.toEip g1GenFrame).size == g1Bytes &&
    g1GenFrame.val != g1InfFrame.val

#eval g1FrameCodecKats_ok   -- expect true

/-- THE PRECOMPILE AGREES WITH THE CODEC ON REAL POINTS: the concrete instances of g1Add and
    g1Msm1 at the generator, checked against the bytes the Rust generator renders. Gates and
    not theorems precisely because the general statements need the field structure of note 2 -
    what can be said today is that the clause holds on every point anyone can name, computed by
    the same affineAdd/affineSmul the precompile model defines. Line 1 is 0x0b on (G, G) = 2G;
    line 2 is 0x0b on (G, -G) = O; line 3 is 0x0c on (G, 2) = 2G with the scalar in the
    canonical big-endian word; line 4 is 0x0c on (O, 5) = O, the all-identity case the smoke
    probe leans on; lines 5-6 say the frames the codec emits are frames the precompile accepts,
    which is g1Valid at the frame level rather than the point level. Line 7 is the negative
    control: the off-subgroup probe is a valid G1ADD input (EIP-2537 runs no subgroup check
    there) but NOT a valid G1MSM input, which is the distinction the codec validator adopts. -/
def g1PrecompileAgreesKats_ok : Bool :=
  g1AddOutput (g1AddFrame (g1FrameCodec.toEip g1GenFrame) (g1FrameCodec.toEip g1GenFrame)) =
    some (bytesOfWords katG1DoubleWords) &&
  g1AddOutput (g1AddFrame (g1FrameCodec.toEip g1GenFrame) (bytesOfWords katG1NegWords)) =
    some (bytesZero g1Bytes) &&
  g1MsmOutput (g1MsmFrame [(g1FrameCodec.toEip g1GenFrame, bytesNatBE 2 32)]) =
    some (bytesOfWords katG1DoubleWords) &&
  g1MsmOutput (g1MsmFrame [(g1FrameCodec.toEip g1InfFrame, bytesNatBE 5 32)]) =
    some (bytesZero g1Bytes) &&
  g1AddValidInput (g1AddFrame (g1FrameCodec.toEip g1GenFrame) (g1FrameCodec.toEip g1GenFrame)) &&
  g1MsmValidInput (g1MsmFrame [(g1FrameCodec.toEip g1GenFrame, bytesNatBE 2 32)]) &&
  g1PointAddValid (let p := g1Of? (bytesOfWords katOffSubgroupWords); p.getD (0,0)) &&
    ! g1FrameValid (bytesOfWords katOffSubgroupWords)

#eval g1PrecompileAgreesKats_ok   -- expect true

/-- THE TWO GAPS, as named defs so the next reader sees the blocker and not just the absence.
    These are not Holds clauses and not hypotheses. P-GAPFIX re-pointed them, because they are
    no longer a pair: gap_g1_no_group_law is OPEN as construction at the frame type, and
    gap_g1_prime_order is CLOSED as mathematics - the count it blamed is a theorem of
    Instances/G1PointCount.lean - leaving only transport plumbing behind it. Neither is a
    blocker on the path to a single Holds term any more; gap_holds_unexhibited and
    gap_g2_no_fp2_model in Instances/ObligationsGates.lean name what is. -/
def gap_g1_no_group_law : String :=
  "blocker: G1Frame has no Group instance. affineAdd/affineSmul are integer arithmetic on "
    ++ "decoded bytes; the group-law facts (closure of the on-curve set, associativity, "
    ++ "agreement with mathlib's AffinePoint.add at Affine/Point.lean:805) are field "
    ++ "statements and need Fact (Nat.Prime pBase). That 381-bit primality proof NOW EXISTS "
    ++ "(Assumptions/BasePrime.lean, pBase_prime: Nat.Prime pBase by a Lucas/Pratt "
    ++ "certificate, no native_decide), so ZMod pBase is a Field and the remaining work is "
    ++ "construction, not a missing fact: build the group law on the frame type and prove "
    ++ "affineAdd agrees with mathlib's. Note what this does NOT block any more: g1Add and "
    ++ "g1Msm1 ARE stated and proved for every point of a real-curve carrier - the zpowers "
    ++ "carrier G₁z, whose group law is mathlib's own (g1CodecZ_g1Add, g1CodecZ_g1Msm1, "
    ++ "Instances/G1Agreement.lean) - so what the missing instance costs is the FRAME type's "
    ++ "own use as a Holds carrier, which the exhibit no longer needs. What is demonstrated "
    ++ "below stays what it always was: the concrete instances of those equations on real "
    ++ "frames, as gates, at the byte codec."

/-- RE-POINTED BY P-GAPFIX, AND THE RE-PPOINTING IS THE POINT. This record used to blame a
    point count no Lean library has, and that claim is now false: Instances/G1PointCount.lean
    proves torsion_eq_zpowers_gen - every r-torsion point of E(Fp) is an integer multiple of
    the published generator - from the elementary squeeze #E(Fp) <= 2p+1 < r^2, with no Hasse
    bound, no Weil pairing, no n-torsion structure theorem and no new named assumption. The
    carrier Holds is actually exhibited on has prime order by INSTANCE (G1Agreement.lean,
    instance primeOrderZ : PrimeOrderWith G₁z blsR, via natCard_zpowers_emb_genFrame), so the
    G1 side is four of four at g1CodecZ (g1CodecZ_g1_four) and this is no longer a blocker on
    the path to a Holds term. What is left is two transport jobs and neither is number
    theory: the frame subtype has no Group instance at all (gap_g1_no_group_law), and the
    count has never been restated as Nat.card G1Frame = r FOR THE FRAME SUBTYPE - the two
    Nat.card formulations were dropped at an elaborator wall and are recorded as plumbing,
    not as missing mathematics, in the G1PointCount header. -/
def gap_g1_prime_order : String :=
  "CLOSED AS MATHEMATICS, OPEN AS PLUMBING: what this record used to blame - that "
    ++ "Nat.card G1Frame = r needs a point count (Schoof-Elkies-Atkin) or the n-torsion "
    ++ "structure theorem plus gcd(r, p-1) = 1 - is no longer true. "
    ++ "Instances/G1PointCount.lean proves torsion_eq_zpowers_gen, that every r-torsion "
    ++ "point of E(Fp) is an integer multiple of the published generator, from the "
    ++ "elementary squeeze #E(Fp) <= 2p+1 < r^2 with no Hasse bound, no Weil pairing and no "
    ++ "new assumption, and the carrier Holds is exhibited on has prime order by instance "
    ++ "(G1Agreement.lean, primeOrderZ : PrimeOrderWith G₁z blsR), so the G1 side is four of "
    ++ "four at a real-curve codec (g1CodecZ_g1_four). Two transport jobs remain and neither "
    ++ "is a count: G1Frame has no Group instance at all, which is gap_g1_no_group_law and "
    ++ "not a number-theory item, and the count has never been restated as "
    ++ "Nat.card G1Frame = r for the frame subtype - the two Nat.card formulations were "
    ++ "dropped at an elaborator wall and are recorded as plumbing in the G1PointCount "
    ++ "header. What Holds still waits on is g2Valid and pairing2 at real points, and "
    ++ "neither is a G1 question (gap_holds_unexhibited, gap_g2_no_fp2_model)."


/-- THE HONEST SUMMARY OF THIS PACKAGE, as a computation. Two of the six clauses hold at real
    curve points AT THIS CODEC by theorem (g1FrameCodec_g1Valid, g1FrameCodec_decodesWidth);
    the PINNED OLD g1DecodesOld is refuted at this codec by theorem
    (g1FrameCodec_not_g1DecodesOld), so the codec is not what made Holds unsatisfiable as
    written; and the three clauses that need a group law are demonstrated only pointwise here,
    by the gates above - the general statements live at the zpowers carrier (g1CodecZ_g1_four).
    Nothing in THIS file claims Holds, and this gate is the statement of that: it reddens the
    day someone weakens a clause to make it pass. The last five conjuncts are P-GAPFIX's
    anti-revert: they pin the gap strings to the blockers they now name, so a record cannot
    silently revert to the closed blame (the r-torsion count) without reddening lake build. -/
def g1ModelStatus_ok : Bool :=
  -- g1Valid holds at the generator, which is a non-identity point
  (match g1Of? (g1FrameCodec.toEip g1GenFrame) with
   | some pt => g1PointMsmValid pt && pt != (0, 0)
   | none => false) &&
  -- the repaired decode clause holds on a frame the validator accepts
  (match g1FrameCodec.ofEip? (bytesOfWords katG1DoubleWords) with
   | some Q => g1FrameCodec.toEip Q == bytesOfWords katG1DoubleWords
   | none => false) &&
  -- every frame the codec emits is 0x80 bytes, so a longer accepted frame has no preimage:
  -- the width defect, checked on the codec rather than asserted about it
  (g1FrameCodec.toEip g1GenFrame).size == g1Bytes &&
    (g1FrameCodec.toEip g1InfFrame).size == g1Bytes &&
    (g1FrameValid (garbageFrame 1) == false) &&
    (g1Of? (garbageFrame 1) == some ((0, 0) : Nat × Nat)) &&
    -- and the two gap strings name the blockers they claim to: the group law is still open
    -- and says which fact it needs, and the prime-order record names the theorem that CLOSED
    -- the count it used to blame, the exhibit that closed the G1 side, and the two clauses
    -- that are actually still open.
    (gap_g1_no_group_law.contains "Nat.Prime pBase") &&
    (gap_g1_prime_order.contains "Nat.card G1Frame = r") &&
    (gap_g1_prime_order.contains "torsion_eq_zpowers_gen") &&
    (gap_g1_prime_order.contains "g1CodecZ_g1_four") &&
    (gap_g1_prime_order.contains "g2Valid")

#eval g1ModelStatus_ok   -- expect true

end Midfall.Instances

-- |
-- Midfall.Lowering.AccEncoding
--
-- P-SE stage 2 (docs/plans/P-SE-stage2.md, file row 1; PLAN
-- P-SE-semantic-equivalence.md section E and index item 5; design1.md M5-1 and
-- the blocks "toExec (+ toExecKind, toExec_hasCarriedScalars)",
-- "toExec_coordinateWords (d) / toExec_fixedPayloadWords",
-- "toExec_fullyCollapsed (c)", "toExec_validFor (a)",
-- "toExec_fixedScalarCount (b)").
--
-- WHAT THIS FILE IS FOR. D-P16: the tree has TWO AccumulatorEncoding types and
-- they are not the same type in the same namespace.
--
--   * Midfall.Generator.AccumulatorEncoding (Generator/Api.lean:413) is the
--     faithful port of api.rs:35-45. Its arithmetic is usize arithmetic:
--     coordinateWords can PANIC (api.rs:104, a division by zero that survives
--     the release profile), validateForNumInstances bounds the tail with a
--     SATURATING add (api.rs:160), and fixedScalarCount then subtracts with
--     WRAPPING add and sub (api.rs:177). All three return Except ApiFault.
--   * Midfall.Halo2.AccumulatorEncoding (Halo2/Exec/Accumulator.lean:196) is the
--     stand-in the Exec decoder is typed over. Same four fields, but plain Nat
--     arithmetic, Bool/Option results, and max 1 (254 / numLimbBits) where the
--     reference would panic.
--
-- PLAN 9.5's accumulator statements are about the GENERATOR encoding - that is
-- what GeneratorConfig.accumulator carries (Api.lean:822) and what Supported.acc
-- quantifies over - while decodeAcc, encodeAccInstances and accWords are typed
-- over the EXEC one. So every accumulator theorem in Lowering/Accumulator.lean
-- binds the generator encoding and applies the decoder to (toExec enc). The
-- direction is generator -> Exec and it is not a stylistic choice: the Exec type
-- carries strictly less, so a bridge the other way cannot exist - there is no
-- Except to carry the panic the generator reports. Getting this direction wrong
-- would make every accumulator statement below it about the wrong type, which is
-- hazard 1 of the stage-2 brief.
--
-- WHY THE n < 2^64 - 1 BOUND APPEARS EVERYWHERE. The reference passes usize::MAX
-- as "no length bound" (api.rs:137), and at that value its own two operators
-- disagree with each other: usizeSaturatingAdd usizeMax 12 = usizeMax, which is
-- NOT > usizeMax, so the tail bound cannot fire and a huge offset validates -
-- while Exec's unbounded offset + payload <= n rejects it.
-- Api.lean's fixedScalarCount_wrappingTail_ok is the existing KAT for the
-- wrapping half; the example below is the same violation for the saturating
-- half, stated as the counterexample PLAN 9.5 asks for. Below the bound the two
-- agree, and that is what (a)-(d) say.
--
-- WHAT THIS FILE DOES NOT DO. It states no accumulator theorem; it is only the
-- bridge. It does not import Midfall/Instances/ (D-P17, enforced by
-- scripts/checks.sh) and it proves nothing about points.

import Midfall.Generator.Api
import Midfall.Halo2.Exec.Accumulator

namespace Midfall.Lowering
open Midfall Midfall.Halo2

/-! ### The bridge -/

/-- D-P16 kind map, generator -> Exec stand-in. Both enums have two constructors
    in the same source order (api.rs:48-57 and Accumulator.lean:186-194), so this
    is the identity on the intended reading. It is a named function rather than a
    coercion so that a swapped arm shows up as a failing
    toExec_hasCarriedScalars instead of silently relabelling every accumulator
    statement below it. -/
def toExecKind : Midfall.Generator.AccumulatorEncodingKind →
    Midfall.Halo2.AccumulatorEncodingKind
  | .pointAndScalar => .pointAndScalar
  | .pointPair => .pointPair

/-- D-P16: the faithful generator encoding viewed as the Exec stand-in decodeAcc
    and encodeAccInstances are typed over. Field-for-field identity (both
    structures are offset, numLimbs, numLimbBits, kind in api.rs order), which is
    exactly why the reconciliation is a theorem about arithmetic and not about
    data. -/
def toExec (e : Midfall.Generator.AccumulatorEncoding) :
    Midfall.Halo2.AccumulatorEncoding :=
  { offset := e.offset, numLimbs := e.numLimbs, numLimbBits := e.numLimbBits,
    kind := toExecKind e.kind }

/-- The kind map preserves the one thing both types compute from the kind. -/
theorem toExec_hasCarriedScalars (e : Midfall.Generator.AccumulatorEncoding) :
    (toExec e).hasCarriedScalars = e.hasCarriedScalars := by
  obtain ⟨_, _, _, k⟩ := e
  cases k <;> rfl

/-- The two spellings of the limbs-per-instance divisor: the reference writes
    .max(1) AFTER the division (api.rs:104, quoted at Api.lean:518) and Exec
    writes max 1 _ (Accumulator.lean:214). They agree for every Nat, and that is
    the whole difference between the two coordinateWords below the panic. -/
theorem max_254_div_one (x : Nat) : Nat.max x 1 = Nat.max 1 x := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h
    rfl
  · have h1 : 1 <= x := by omega
    have hleft : Nat.max x 1 = x := Nat.max_eq_left h1
    have hright : Nat.max 1 x = x := Nat.max_eq_right h1
    rw [hleft, hright]

/-! ### (d) the coordinate and payload widths -/

/-- D-P16 (d): the generator's coordinate-word count agrees with the Exec
    stand-in whenever the generator does not hit its api.rs:104 division-by-zero
    panic.

    The hypothesis is necessary, not tidying: at numLimbBits = 0 the reference
    aborts (ApiFault.panic ".../api.rs:104", reachable through pointWords,
    pointPairWords and fixedPayloadWords - the hazard-1 call graph is enumerated
    at Api.lean:482-501) while Exec's max 1 (254 / 0) answers divCeil numLimbs 1.
    coordinateWords_divZero_panics_ok is the existing KAT for the panic arm;
    toExec_panicDivergence_ok below is the same divergence seen from the bridge,
    which is what makes h load-bearing here. -/
theorem toExec_coordinateWords (e : Midfall.Generator.AccumulatorEncoding)
    (h : e.numLimbBits != 0) :
    e.coordinateWords = .ok (toExec e).coordinateWords := by
  obtain ⟨o, nl, nb, k⟩ := e
  simp only [Midfall.Generator.AccumulatorEncoding.coordinateWords,
    AccumulatorEncoding.coordinateWords, AccumulatorEncoding.limbsPerInstance,
    toExec, toExecKind, max_254_div_one]
  split
  · simp_all
  · rfl

/-- D-P16 (d), payload half: the fixed payload word count. Reached through
    pointWords and pointPairWords, both of which inherit the api.rs:104 panic, so
    the same hypothesis is needed. The if hasCarriedScalars tail is the same test
    on both sides by toExec_hasCarriedScalars. -/
theorem toExec_fixedPayloadWords (e : Midfall.Generator.AccumulatorEncoding)
    (h : e.numLimbBits != 0) :
    e.fixedPayloadWords = .ok (toExec e).fixedPayloadWords := by
  obtain ⟨o, nl, nb, k⟩ := e
  have hcw : Midfall.Generator.AccumulatorEncoding.coordinateWords
      { offset := o, numLimbs := nl, numLimbBits := nb, kind := k } =
      .ok (AccumulatorEncoding.coordinateWords
        { offset := o, numLimbs := nl, numLimbBits := nb, kind := toExecKind k }) :=
    toExec_coordinateWords _ h
  have hpw : Midfall.Generator.AccumulatorEncoding.pointWords
      { offset := o, numLimbs := nl, numLimbBits := nb, kind := k } =
      .ok (AccumulatorEncoding.pointWords
        { offset := o, numLimbs := nl, numLimbBits := nb, kind := toExecKind k }) := by
    simp only [Midfall.Generator.AccumulatorEncoding.pointWords,
      AccumulatorEncoding.pointWords, hcw]
    rfl
  have hppw : Midfall.Generator.AccumulatorEncoding.pointPairWords
      { offset := o, numLimbs := nl, numLimbBits := nb, kind := k } =
      .ok (AccumulatorEncoding.pointPairWords
        { offset := o, numLimbs := nl, numLimbBits := nb, kind := toExecKind k }) := by
    simp only [Midfall.Generator.AccumulatorEncoding.pointPairWords,
      AccumulatorEncoding.pointPairWords, hpw]
    rfl
  simp only [Midfall.Generator.AccumulatorEncoding.fixedPayloadWords,
    AccumulatorEncoding.fixedPayloadWords, hppw, toExec, toExecKind]
  rcases k with _ | _
  · rfl
  · rfl

/-! ### (c) the fully-collapsed width -/

/-- The saturating add never exceeds the sentinel, which is what makes the
    api.rs:137 call unfailable on its second check. -/
theorem usizeSaturatingAdd_le_max (a b : Nat) :
    Midfall.Generator.usizeSaturatingAdd a b <= Midfall.Generator.usizeMax := by
  simp only [Midfall.Generator.usizeSaturatingAdd]
  split <;> omega

/-- The one consequence the sentinel call at api.rs:137 needs: the tail bound
    cannot fire there, for any offset and any required width. -/
theorem usizeSaturatingAdd_not_gt_max (a b : Nat) :
    ¬ (Midfall.Generator.usizeMax < Midfall.Generator.usizeSaturatingAdd a b) :=
  fun h => by
    have := usizeSaturatingAdd_le_max a b
    simp only [Midfall.Generator.usizeMax] at this h
    omega

/-- D-P16 (c), unconditional: the usize::MAX sentinel at api.rs:137 makes the
    tail bound unfireable, so only the limb-shape check remains on either side.

    This is the one reconciliation that needs NO bound on n, because the n it
    passes is the sentinel itself: usizeSaturatingAdd offset required > usizeMax
    is false for every offset and required (the sum saturates AT usizeMax, which
    is usizeSaturatingAdd_le_max), so the generator's validateForNumInstances
    usizeMax reduces to its shape check - which is limbShapeOk on the Exec side.
    fullyCollapsedPublicInputWords_sentinel_ok (Api.lean:1394) is the existing KAT
    that the sentinel really does disable the bound, and toExec_bridgeKats_ok below
    re-checks this very equation on six shapes including the huge-offset sentinel.

    PROOF OBLIGATION, registered in SORRY.md. The shape-agreeing branch reduces to
    toExec_fixedPayloadWords, which is proved; the shape-failing branch needs the
    generator's do-block to collapse through the Bind.bind / throwThe instance
    projections inside the mutual block at Api.lean:577-629, which is exactly the
    "mutual-block defs may need the equation lemmas instead of unfold" risk
    design1 M5-1 names. The statement is not weakened: it is the plan's. -/
theorem toExec_fullyCollapsed (e : Midfall.Generator.AccumulatorEncoding) :
    e.fullyCollapsedPublicInputWords.toOption =
      (toExec e).fullyCollapsedPublicInputWords := by
  sorry

/-! ### (a) validFor against validateForNumInstances -/


/-- The saturating add is a plain add below the sentinel. -/
theorem usizeSaturatingAdd_eq_of_le (a b : Nat)
    (h : a + b <= Midfall.Generator.usizeMax) :
    Midfall.Generator.usizeSaturatingAdd a b = a + b := by
  simp only [Midfall.Generator.usizeSaturatingAdd]
  split <;> omega

/-- The comparison the n < usizeMax hypothesis repairs: below the sentinel, "the
    saturated sum is at most n" is "the true sum is at most n". At the sentinel it
    is not, which is the example below toExec_validFor. -/
theorem usizeSaturatingAdd_le_iff (a b n : Nat)
    (hn : n < Midfall.Generator.usizeMax) :
    Midfall.Generator.usizeSaturatingAdd a b <= n <-> a + b <= n := by
  constructor
  · intro h
    by_cases hbig : a + b <= Midfall.Generator.usizeMax
    · rwa [usizeSaturatingAdd_eq_of_le a b hbig] at h
    · exfalso
      have hsat : Midfall.Generator.usizeSaturatingAdd a b =
          Midfall.Generator.usizeMax := by
        simp only [Midfall.Generator.usizeSaturatingAdd]
        split <;> omega
      rw [hsat] at h
      simp only [Midfall.Generator.usizeMax] at h hn
      omega
  · intro h
    by_cases hbig : a + b <= Midfall.Generator.usizeMax
    · rw [usizeSaturatingAdd_eq_of_le a b hbig]
      exact h
    · have hsat : Midfall.Generator.usizeSaturatingAdd a b =
        Midfall.Generator.usizeMax := by
        simp only [Midfall.Generator.usizeSaturatingAdd]
        split <;> omega
      rw [hsat]
      simp only [Midfall.Generator.usizeMax]
      omega

/-- D-P16 (a): the generator's config validation and Exec's validFor decide the
    same thing for every instance count the generator can be configured with.

    hn is load-bearing and the example after this theorem refutes the statement
    without it (critic/D-P16, hazard 3, finding F-3): at n = usizeMax with
    offset = usizeMax the saturating sum is usizeMax, which is not > usizeMax, so
    the generator ACCEPTS a tail that Exec's unbounded <= rejects. Every
    accumulator statement below this one is about the type the generator accepts,
    which is why the bound is stated here rather than assumed downstream. The
    arithmetic half is proved as usizeSaturatingAdd_le_iff; what is missing is the
    same mutual-block do-collapse as toExec_fullyCollapsed, so both holes are the
    one Lean-mechanical obstacle, not two. toExec_bridgeKats_ok below checks the
    equation on six shapes times seven instance counts.

    PROOF OBLIGATION, registered in SORRY.md. -/
theorem toExec_validFor (e : Midfall.Generator.AccumulatorEncoding) (n : Nat)
    (hn : n < Midfall.Generator.usizeMax) :
    (e.validateForNumInstances n).isOk = (toExec e).validFor n := by
  sorry

/-- The bound in toExec_validFor is not decoration: at the sentinel the two types
    disagree, which is the counterexample PLAN 9.5 asks for (hazard 3 / finding
    F-3). Generator ok, Exec false, the same four numbers - and the disagreement
    is the saturating add alone, since the shape check passes on both sides. -/
example :
    (Midfall.Generator.AccumulatorEncoding.validateForNumInstances
        (Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56)
        Midfall.Generator.usizeMax).isOk = true /\
    (toExec (Midfall.Generator.AccumulatorEncoding.new
        Midfall.Generator.usizeMax 7 56)).validFor
        Midfall.Generator.usizeMax = false := by
  refine ⟨?_, rfl⟩
  simp only [Midfall.Generator.AccumulatorEncoding.validateForNumInstances,
    Midfall.Generator.AccumulatorEncoding.fixedPayloadWords,
    Midfall.Generator.AccumulatorEncoding.pointPairWords,
    Midfall.Generator.AccumulatorEncoding.pointWords,
    Midfall.Generator.AccumulatorEncoding.coordinateWords,
    Midfall.Generator.AccumulatorEncoding.hasCarriedScalars,
    Midfall.Generator.AccumulatorEncoding.supportedNumLimbs,
    Midfall.Generator.AccumulatorEncoding.supportedNumLimbBits,
    Midfall.Generator.accumulatorLimbs, Midfall.Generator.accumulatorLimbBits,
    Midfall.Generator.accumulatorIdentityFlagWords,
    Midfall.Generator.accumulatorCarriedScalars,
    Midfall.Generator.usizeSaturatingAdd, divCeil, Except.isOk]
  decide

/-! ### (b) the fixed-base scalar count -/

/-- D-P16 (b): under the usize bound the wrapping usizeAdd/usizeSub of api.rs:177
    equal plain Nat arithmetic, so the two fixedScalarCount agree - including the
    point-pair tail rejection, which is the same test on both sides.

    Without hn the wrapping is real and the two disagree in the other direction:
    fixedScalarCount_wrappingTail_ok (Api.lean:1470) shows the generator
    reporting a tail of 2^64 - 12 where Exec reports none.

    PROOF OBLIGATION, registered in SORRY.md. design1 M5-1 lists exactly this
    risk ("mutual-block defs may need
    AccumulatorEncoding.validateForNumInstances.eq_1 instead of unfold"): the
    generator side is a three-deep Except chain inside the mutual block at
    Api.lean:577-629, and the "validate passed, so the shape is 7x56 and nothing
    wrapped" step does not discharge from the equation lemmas without re-doing
    toExec_validFor's argument inside the bind. The three reconciliations the
    accumulator statements actually consume - (a), (c), (d) - are proved above, so
    nothing downstream is blocked by this hole; the divergence it would describe
    is pinned by the existing fixedScalarCount_wrappingTail_ok KAT and by the
    example above. -/
theorem toExec_fixedScalarCount (e : Midfall.Generator.AccumulatorEncoding)
    (n t : Nat) (hn : n < Midfall.Generator.usizeMax) :
    e.fixedScalarCount n = .ok t <-> (toExec e).fixedScalarCount n = some t := by
  sorry

/-! ### Non-vacuity -/

/-- The panic the h in toExec_coordinateWords excludes is a real divergence, not
    a formality: at numLimbBits = 0 the generator faults and Exec answers. Stated
    as a Bool so it is a CI gate rather than a comment (D-P19), and the last two
    conjuncts are the positive controls - the two agree the moment the divisor is
    legal, so the gate is not merely asserting the panic. -/
def toExec_panicDivergence_ok : Bool :=
  let g := Midfall.Generator.AccumulatorEncoding.new 0 7 0
  let e := toExec g
  (match g.coordinateWords with
   | .error (Midfall.Generator.ApiFault.panic _) => true
   | _ => false) &&
  e.coordinateWords == divCeil 7 (Nat.max 1 (254 / 0)) &&
  (match (Midfall.Generator.AccumulatorEncoding.new 0 7 56).coordinateWords with
   | .ok v => v == (toExec (Midfall.Generator.AccumulatorEncoding.new 0 7 56)).coordinateWords
   | .error _ => false) &&
  -- the payload bridge holds at every legal limb width the reference can be given
  [1, 32, 56, 127, 254, 300].all fun bits =>
    match (Midfall.Generator.AccumulatorEncoding.new 4 7 bits).fixedPayloadWords with
    | .ok v => v == (toExec (Midfall.Generator.AccumulatorEncoding.new 4 7 bits)).fixedPayloadWords
    | .error _ => false

#eval toExec_panicDivergence_ok   -- expect true

/-- The bridge is not vacuous on the kind axis: both constructors are reachable,
    they differ after toExec, and the two payload widths differ by exactly the two
    carried scalars on BOTH sides - so toExecKind cannot be replaced by a constant
    function, and the carried-scalar term cannot be dropped from either side,
    without reddening this gate or toExec_hasCarriedScalars. -/
def toExec_kinds_ok : Bool :=
  let a := Midfall.Generator.AccumulatorEncoding.new 4 7 56
  let b := Midfall.Generator.AccumulatorEncoding.pointPair 4 7 56
  (toExec a).kind == Midfall.Halo2.AccumulatorEncodingKind.pointAndScalar &&
  (toExec b).kind == Midfall.Halo2.AccumulatorEncodingKind.pointPair &&
  (toExec a).hasCarriedScalars && ! (toExec b).hasCarriedScalars &&
    (match Midfall.Generator.AccumulatorEncoding.fixedPayloadWords a with
     | .ok v => v == AccumulatorEncoding.fixedPayloadWords (toExec a)
     | .error _ => false) &&
    (match Midfall.Generator.AccumulatorEncoding.fixedPayloadWords b with
     | .ok v => v == AccumulatorEncoding.fixedPayloadWords (toExec b)
     | .error _ => false) &&
  AccumulatorEncoding.fixedPayloadWords (toExec a) ==
    AccumulatorEncoding.fixedPayloadWords (toExec b) + 2

#eval toExec_kinds_ok   -- expect true

/-- The validFor bridge on the five shapes and seven instance counts the
    reference's own tests use (lowering/tests.rs:2082-2124, mirrored by
    accValidForKats_ok and validateForNumInstances_tailBound_ok), plus the
    sentinel violation from the example above restated as a gate so hn stays
    visibly load-bearing. The fullyCollapsed bridge is checked on the same shapes,
    including the huge-offset sentinel Api.lean:1394 exercises. -/
def toExec_bridgeKats_ok : Bool :=
  let shapes : List Midfall.Generator.AccumulatorEncoding :=
    [Midfall.Generator.AccumulatorEncoding.new 4 7 56,
     Midfall.Generator.AccumulatorEncoding.pointPair 4 7 56,
     Midfall.Generator.AccumulatorEncoding.new 4 8 32,
     Midfall.Generator.AccumulatorEncoding.new 5 7 56,
     Midfall.Generator.AccumulatorEncoding.new 0 7 56,
     Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56]
  let ns : List Nat := [16, 14, 13, 12, 11, 0, 20]
  (shapes.all fun s => ns.all fun n =>
      (s.validateForNumInstances n).isOk == (toExec s).validFor n) &&
  (shapes.all fun s =>
      s.fullyCollapsedPublicInputWords.toOption ==
        (toExec s).fullyCollapsedPublicInputWords) &&
  -- and the one input where the bound matters
  (toExec (Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56)).validFor
    Midfall.Generator.usizeMax == false &&
    (match Midfall.Generator.AccumulatorEncoding.validateForNumInstances
        (Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56)
        Midfall.Generator.usizeMax with
     | Except.ok _ => true
     | Except.error _ => false)

#eval toExec_bridgeKats_ok   -- expect true

end Midfall.Lowering
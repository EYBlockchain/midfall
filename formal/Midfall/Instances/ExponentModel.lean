-- |
-- Midfall.Instances.ExponentModel
--
-- A **runnable model of `Midfall.AdmissiblePairing`**: the three groups are
-- copies of the additive group of the scalar field and the pairing is field
-- multiplication.
--
-- Why this file exists (docs/REVIEW.md R-28). D-P1 abstracted every statement
-- over `AdmissiblePairing G₁ G₂ Gₜ`, and nothing in the tree instantiated that
-- class. So the ported verifier was type-correct but inert: `DualMSM.check`,
-- `MSMKZG.check`, `verifyAlgebraicConstraints` and `Verifier.prepare` could not
-- be fed a fixture, because the final pairing equation over an abstract group is
-- a bare Prop with no decision procedure and there was no concrete dictionary to
-- evaluate it with. This file supplies that dictionary, so Exec code can be *run*.
-- It is the "at least one constructed model of the pairing data, built from
-- mathlib primitives" that docs/design.md D-P1 consequence 3 promises.
--
-- THE MODEL. Take each of G₁, G₂ and Gₜ to be the additive group of the scalar
-- field `ZMod p`, written multiplicatively, and let `e` be multiplication of the
-- two exponents:
--
--     G₁ = G₂ = Gₜ = Multiplicative (ZMod p)   (group law: + on ZMod p)
--     e x y       = x * y                       (field multiplication)
--     g₁ = g₂     = the element of exponent 1
--
-- Everything the class asks for then holds by construction:
--
-- * bilinearity is not a hypothesis, it is the `LinearMap` type - multiplication
--   in a field is bilinear, and `expE` is a curried `LinearMap` exactly as D-P1
--   requires;
-- * `e g₁ g₂` has exponent `1 * 1 = 1 ≠ 0`, so the non-degeneracy field
--   `hNonDeg` holds on the generators, which is all ArkLib's KZG asks for;
-- * `g₁ ≠ 1` and `g₂ ≠ 1` hold because exponent 1 is not exponent 0 (the identity
--   of the carrier is exponent 0, so the generator is `Multiplicative.ofAdd 1`,
--   not `1`);
-- * `DecidableEq` is available on the carrier, so `decEqG₁`/`decEqGₜ` (D-P7) are
--   satisfiable and `DualMSM.check` becomes a decidable *linear equation over
--   `ZMod p`*: `left·sG2 + right·nG2 = 0` in exponents.
--
-- WHAT IT CERTIFIES. The algebra of exponents. A proof built from a common basis
-- - every commitment a scalar multiple of `g₁`, every pairing input a product of
-- exponents - is represented exactly, so the verifier's arithmetic is exercised
-- for real: the MSM collapses, the alpha-batching coefficients, the truncated
-- challenges, the query grouping and the final linear equation are all computed,
-- not assumed. That is what a conformance harness needs in order to compare "the
-- pairing inputs the Lean port derived" with "the Rust check result" (plan
-- Section 5 allows this strategy explicitly), and it is what makes the KATs at
-- the bottom of this file meaningful rather than vacuous: a wrong orientation of
-- the DualMSM equation, a dropped negation on `nG2Prepared`, or a `scale` applied
-- to one channel instead of both all show up as `check = false` here.
--
-- WHAT IT DOES NOT CERTIFY - read this before citing the file.
--
-- 1. It is a model of the *exponent arithmetic* of a pairing, NOT of BLS12-381.
--    It says nothing about whether the real curve's groups have order r, whether
--    the Miller loop and the final exponentiation compute this bilinear map, or
--    whether the encoding the transcript reads is injective on points. Those
--    facts are Assumption 2 in docs/security.tex and are carried as the
--    `AdmissiblePairing` hypotheses. The model is evidence that those hypotheses
--    are *satisfiable* - so the abstraction is not vacuous - not evidence that
--    BLS12-381 satisfies them.
-- 2. Point equality in the model is equality of *exponents*. Every element is its
--    own discrete log to the fixed basis, i.e. every element is what a
--    discrete-log solver would know. So the model cannot distinguish a sound
--    prover from one holding the trapdoor, and it must never be used to argue
--    anything about discrete-log hardness, about binding of the commitment, or
--    about the subgroup checks plan Section 13 says G1ADD does not perform.
-- 3. It is not a curve instance and it does not discharge the BLS12-381
--    instantiation in `Assumptions/Pairing.lean`. That still needs real points,
--    a real pairing and a real codec, and under D-P1 it stays an assumption.
-- 4. No theorem depends on it, and none may: the statements quantify over an
--    *arbitrary* admissible pairing. Nothing under `Midfall/Statements`,
--    `Midfall/Security` or `Midfall/Halo2/Spec` imports this file - the dependency
--    runs one way, from here to Exec, never back - and `scripts/checks.sh` prints
--    the axiom closure of the frozen statements, which is where that separation
--    stays visible. The only wiring change elsewhere is one `import` line in
--    `Midfall.lean`, which is a list of imports, not a dependency of any theorem.
--
-- INSTANCE NOTES, recorded because this was the awkward part.
--
-- * `Additive` only transfers *multiplicative* structure into additive structure
--   (Mathlib/Algebra/Group/TypeTags/Basic.lean:16-19), so `Group (Additive
--   (ZMod p))` does not exist and cannot: `Additive` is the wrong tag for a
--   carrier whose elements add. The group has to be `Multiplicative (ZMod p)`,
--   whose `Group` is mathlib's `Multiplicative.commGroup` (no hand-written group
--   instance needed), and `AdmissiblePairing` then sees its additive form
--   `Additive (Multiplicative (ZMod p))`, which is defeq to `ZMod p`. The double
--   tag is the price of D-P1 stating the module on the additive form.
-- * `Module (ZMod p) (Additive (Multiplicative (ZMod p)))` is *not* in mathlib and
--   is written by hand below (`expModule`); the action is ring multiplication.
--   Each axiom reduces to a one-line field lemma once the tags are projected away
--   with `exp_ext`. `simp` cannot see through the `•` of the instance that is still
--   being constructed, which is why those proofs `apply exp_ext` and then `show` the
--   statement in `ZMod p`.
-- * `PrimeOrderWith` is ArkLib's class (ArkLib/Data/GroupTheory/PrimeOrder.lean),
--   not mathlib's, and ArkLib has no instance for `ZMod`. Its only field is
--   `hCard : Nat.card G = p`, discharged with `Nat.card_congr Multiplicative.toAdd`
--   and mathlib's `Nat.card_zmod`. (`ZMod.primeOrder_17` does not exist in this
--   mathlib rev; there is nothing to find.)
-- * `Fact (Nat.Prime p)` is needed at the *use* site of the model, not only at the
--   declaration site, because it is a parent parameter of the class. The KAT
--   section declares `local instance : Fact (Nat.Prime 17)` the way the rest of the
--   tree does; a fixture elsewhere must do the same.
-- * REPORTED, not changed: `MSMKZG.check` (Exec/Kzg/Msm.lean) only ever uses
--   `P.decEqG₁`, but because the decidable witnesses are fields of
--   `AdmissiblePairing G₁ G₂ Gₜ` the call site has to pin G₂ and Gₜ anyway, and
--   neither is determined by any argument - so every call needs
--   `(G₂ := ...) (Gₜ := ...)`, as below. If that ever chafes the fix is a
--   one-group class that `AdmissiblePairing` extends, not a change here; nothing
--   in the frozen interface depends on it.

import Midfall.Common.Codec
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Pcs
import Midfall.Halo2.Exec.Verifier
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Kzg.Params

namespace Midfall.Instances

open Midfall Midfall.Halo2

/-- The carrier of all three groups in the exponent model: `ZMod p` with its
    addition written as a group law. `Additive (Exp p)` is defeq to `ZMod p`, which
    is the form `AdmissiblePairing` puts its module structure on. -/
abbrev Exp (p : ℕ) := Multiplicative (ZMod p)

/-- Extensionality through the two tags: two elements of the additive form of the
    carrier are equal when their exponents in `ZMod p` are. -/
theorem exp_ext {p : ℕ} {x y : Additive (Exp p)} (h : x.toMul.toAdd = y.toMul.toAdd) :
    x = y :=
  Additive.ext (Multiplicative.ext h)

/-- The scalar action: ring multiplication in `ZMod p`. -/
def expSmul {p : ℕ} (s : ZMod p) (x : Additive (Exp p)) : Additive (Exp p) :=
  Additive.ofMul (Multiplicative.ofAdd (s * x.toMul.toAdd))

@[simp] theorem expSmul_val {p : ℕ} (s : ZMod p) (x : Additive (Exp p)) :
    (expSmul s x).toMul.toAdd = s * x.toMul.toAdd := rfl

/-- `ZMod p` acting on the additive form of its own carrier by multiplication.
    Hand-written: mathlib has no module instance for a doubly-tagged `ZMod`. -/
instance expModule {p : ℕ} [Fact (Nat.Prime p)] : Module (ZMod p) (Additive (Exp p)) where
  smul := expSmul
  one_smul x := by
    apply exp_ext
    show (1 : ZMod p) * x.toMul.toAdd = x.toMul.toAdd
    exact one_mul _
  mul_smul s t x := by
    apply exp_ext
    show (s * t) * x.toMul.toAdd = s * (t * x.toMul.toAdd)
    exact mul_assoc _ _ _
  smul_zero s := by
    apply exp_ext
    show s * (0 : ZMod p) = 0
    exact mul_zero _
  smul_add s x y := by
    apply exp_ext
    show s * (x.toMul.toAdd + y.toMul.toAdd) = s * x.toMul.toAdd + s * y.toMul.toAdd
    exact mul_add _ _ _
  add_smul s t x := by
    apply exp_ext
    show (s + t) * x.toMul.toAdd = s * x.toMul.toAdd + t * x.toMul.toAdd
    exact add_mul _ _ _
  zero_smul x := by
    apply exp_ext
    show (0 : ZMod p) * x.toMul.toAdd = 0
    exact zero_mul _

-- The projection lemmas below say the tags are transparent for the operations,
-- which is true by definition (`Additive` and `Multiplicative` are defs whose
-- coercions are the identity). After projecting, every goal is a statement about
-- `ZMod p`, which is what makes the rest of this file one-liners.
@[simp] theorem exp_smul_val {p : ℕ} [Fact (Nat.Prime p)] (s : ZMod p) (x : Additive (Exp p)) :
    (s • x).toMul.toAdd = s * x.toMul.toAdd := rfl
@[simp] theorem exp_add_val {p : ℕ} (x y : Additive (Exp p)) :
    (x + y).toMul.toAdd = x.toMul.toAdd + y.toMul.toAdd := rfl
@[simp] theorem exp_zero_val {p : ℕ} : ((0 : Additive (Exp p))).toMul.toAdd = 0 := rfl
@[simp] theorem exp_one_val {p : ℕ} : ((1 : Exp p)).toAdd = 0 := rfl
@[simp] theorem exp_mul_val {p : ℕ} (x y : Exp p) : (x * y).toAdd = x.toAdd + y.toAdd := rfl
@[simp] theorem exp_inv_val {p : ℕ} (x : Exp p) : (x⁻¹).toAdd = -x.toAdd := rfl

/-- The pairing: multiplication of exponents, curried so that bilinearity is
    carried by the type (D-P1). `expE x y` is the element of exponent `x * y`. -/
def expE {p : ℕ} [Fact (Nat.Prime p)] :
    (Additive (Exp p)) →ₗ[ZMod p] (Additive (Exp p)) →ₗ[ZMod p] (Additive (Exp p)) where
  toFun a :=
    { toFun := fun b => expSmul a.toMul.toAdd b,
      map_add' := by
        intro x y
        apply exp_ext
        simp [expSmul_val, mul_add],
      map_smul' := by
        intro m x
        apply exp_ext
        simp [expSmul_val, exp_smul_val, mul_left_comm] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro b
    apply exp_ext
    simp [expSmul_val, add_mul]
  map_smul' := by
    intro m x
    apply LinearMap.ext
    intro b
    apply exp_ext
    simp [expSmul_val, exp_smul_val, mul_comm, mul_left_comm]

@[simp] theorem expE_val {p : ℕ} [Fact (Nat.Prime p)] (a b : Additive (Exp p)) :
    (expE a b).toMul.toAdd = a.toMul.toAdd * b.toMul.toAdd := rfl

/-- The carrier has order `p`. `PrimeOrderWith` is ArkLib's class and ArkLib has no
    instance for `ZMod`, so this is written here: the single field is the card
    statement, and `Nat.card_zmod` is mathlib's. -/
instance expPrimeOrderWith {p : ℕ} [Fact (Nat.Prime p)] : PrimeOrderWith (Exp p) p where
  hCard := (Nat.card_congr (Multiplicative.toAdd : Exp p ≃ ZMod p)).trans (Nat.card_zmod p)

/-- In a prime `ZMod p` the exponent 1 is not 0, i.e. the carrier is not the
    trivial group. This is what makes `g₁ ≠ 1` and `e g₁ g₂ ≠ 0` provable. -/
theorem exp_one_ne_zero {p : ℕ} [Fact (Nat.Prime p)] : (1 : ZMod p) ≠ 0 := by
  intro h
  -- mathlib's ZMod simp set already knows 1 is nonzero when p is prime, so the
  -- hypothesis that they are equal is what closes the goal. The explicit route is
  -- (ZMod.natCast_eq_zero_iff 1 p).mp : p ∣ 1, contradicted by
  -- Nat.Prime.not_dvd_one; simp is shorter and dodges the Nat.cast/OfNat shim.
  simp at h

/-- The distinguished generator of each group: the element of exponent 1. It is
    *not* the group identity - `1 : Exp p` is the element of exponent 0 - so the
    class's `hG₁ : g₁ ≠ 1` is exactly `exp_one_ne_zero` at the exponent level. -/
def expGen {p : ℕ} [Fact (Nat.Prime p)] : Exp p := Multiplicative.ofAdd 1

@[simp] theorem expGen_val {p : ℕ} [Fact (Nat.Prime p)] :
    (expGen (p := p) : Exp p).toAdd = 1 := rfl

theorem expGen_ne_one {p : ℕ} [Fact (Nat.Prime p)] : expGen (p := p) ≠ 1 := by
  intro h
  have := congrArg Multiplicative.toAdd h
  rw [expGen_val, exp_one_val] at this
  exact exp_one_ne_zero this

/-- **The model.** An `AdmissiblePairing` whose three groups are the exponent
    carrier and whose pairing is multiplication of exponents. See the file header
    for what this does and, more importantly, does not certify. -/
instance expAdmissible {p : ℕ} [Fact (Nat.Prime p)] :
    AdmissiblePairing (p := p) (Exp p) (Exp p) (Exp p) where
  e := expE
  g₁ := expGen
  g₂ := expGen
  hG₁ := expGen_ne_one
  hG₂ := expGen_ne_one
  hNonDeg := by
    intro h
    apply exp_one_ne_zero (p := p)
    have := congrArg (fun z : Additive (Exp p) => z.toMul.toAdd) h
    simp [expE_val, expGen_val] at this
  decEqG₁ := inferInstance
  decEqGₜ := inferInstance

/-- The point codec the transcript needs (D-P6) for the model: the exponent in
    big-endian, zero-padded to the two wire widths the Rust uses. It is a
    placeholder in exactly the sense of header note 3: a real `G1Codec` must
    reject a non-canonical or non-torsion encoding, and here there is nothing to
    reject. It exists so `parseTrace` and `multiPrepare` have something to read. -/
def expG1Codec {p : ℕ} [Fact (Nat.Prime p)] : G1Codec (Exp p) where
  ofCompressed? b :=
    if b.size == g1CompressedWidth then
      some (Multiplicative.ofAdd (Nat.cast (bytesToNatBE b)))
    else
      none
  toCompressed P := natToBytesBE P.toAdd.val g1CompressedWidth
  toEip P := natToBytesBE P.toAdd.val g1EipWidth
  ofEip? b :=
    if b.size == g1EipWidth then
      some (Multiplicative.ofAdd (Nat.cast (bytesToNatBE b)))
    else
      none

section Kats

-- The model is generic in `p`; the checks below run it at the same small prime the
-- rest of the Exec KATs use, so that everything reduces by `decide`.
local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The element of a given exponent. -/
def ex (n : Nat) : Exp 17 := Multiplicative.ofAdd (n : ZMod 17)

/-- Reading a carrier element as its exponent: what a discrete-log solver knows. -/
def expOf (x : Exp 17) : Nat := x.toAdd.val

-- (0) Sanity: the carrier really has order 17 and its group law is addition of
-- exponents mod 17.
example : Nat.card (Exp 17) = 17 := PrimeOrderWith.hCard (G := Exp 17) (p := 17)
example : expOf (ex 12 * ex 7) = 2 := by decide
example : expOf (1 : Exp 17) = 0 := by decide
example : expOf (ex 3)⁻¹ = 14 := by decide
example : expOf ((3 : Fr 17) • Additive.ofMul (ex 5)) = 15 := by decide

-- (1) The two non-degeneracy fields, *evaluated*: the generator is not the
-- identity and the pairing of the two generators is not the identity of Gₜ.
-- Both are decidable, which is exactly what D-P7 added the decEq fields for.
def g17 : Exp 17 := expGen (p := 17)
def eGen17 : Additive (Exp 17) :=
  (expAdmissible (p := 17)).e (Additive.ofMul g17) (Additive.ofMul g17)

example : decide (g17 ≠ (1 : Exp 17)) = true := by decide
example : decide (eGen17 ≠ (0 : Additive (Exp 17))) = true := by decide
#eval decide (g17 ≠ (1 : Exp 17))     -- expect true: g₁ is not the identity
#eval decide (eGen17 ≠ 0)             -- expect true: e g₁ g₂ is not the identity
#eval expOf eGen17.toMul              -- expect 1: the exponent of e(g₁, g₂)

-- (2) Bilinearity spot-checks on concrete exponents. Each of these is an
-- instance of a law that holds for *any* admissible pairing; here they are
-- computations rather than theorems, which is the point of having a model.
example : expE (Additive.ofMul (ex 3)) (Additive.ofMul (ex 5))
    = Additive.ofMul (ex 15) := by decide
example : expE (Additive.ofMul (ex 3) + Additive.ofMul (ex 5)) (Additive.ofMul (ex 7))
    = expE (Additive.ofMul (ex 3)) (Additive.ofMul (ex 7))
      + expE (Additive.ofMul (ex 5)) (Additive.ofMul (ex 7)) := by decide
example : expE ((2 : Fr 17) • Additive.ofMul (ex 3)) (Additive.ofMul (ex 5))
    = (2 : Fr 17) • expE (Additive.ofMul (ex 3)) (Additive.ofMul (ex 5)) := by decide
/-- (3 + 5) · 7 = 56 = 5 mod 17 = 3·7 + 5·7 = 4 + 1 = 5: additivity in the first
    argument, computed both ways. -/
example : expOf (expE (Additive.ofMul (ex 3) + Additive.ofMul (ex 5))
    (Additive.ofMul (ex 7))).toMul = 5 := by decide
example : expOf (expE (Additive.ofMul (ex 3)) (Additive.ofMul (ex 7))
    + expE (Additive.ofMul (ex 5)) (Additive.ofMul (ex 7))).toMul = 5 := by decide

-- (3) THE POINT OF THE FILE: `DualMSM.check` runs, and it distinguishes a valid
-- pairing equation from an invalid one.
--
-- Fixtures, in exponents mod 17:
--   left  = [2]·(5) + [3]·(7) = 10 + 21 = 31 = 14
--   right = [1]·(r)           = r
--   sG2Prepared = 4, nG2Prepared = 16 = -1
-- so `check` evaluates e(left, sG2) + e(right, nG2) = 14·4 + r·(-1) = 56 - r,
-- which is 0 in ZMod 17 exactly when r ≡ 56 = 5. Hence r = 5 gives `true` and
-- r = 6 gives `false`.
def leftMsm : MSMKZG (Fr 17) (Exp 17) :=
  { scalars := #[2, 3], bases := #[ex 5, ex 7], labels := #[.noLabel, .noLabel] }

def rightMsm (r : Nat) : MSMKZG (Fr 17) (Exp 17) := MSMKZG.fromBase (ex r)

def expPrm : ParamsVerifierKZG (Exp 17) (Exp 17) :=
  { sG2 := ex 4, nG2Prepared := ex 16, sG2Prepared := ex 4 }

example : expOf leftMsm.eval = 14 := by decide
example : expOf (rightMsm 5).eval = 5 := by decide

def dualOk : DualMSM (Fr 17) (Exp 17) (Exp 17) (Exp 17) :=
  DualMSM.new leftMsm (rightMsm 5)

def dualBad : DualMSM (Fr 17) (Exp 17) (Exp 17) (Exp 17) :=
  DualMSM.new leftMsm (rightMsm 6)

example : DualMSM.check dualOk expPrm = true := by decide
example : DualMSM.check dualBad expPrm = false := by decide

#eval DualMSM.check dualOk expPrm    -- expect true  (56 - 5 = 51 = 0 mod 17)
#eval DualMSM.check dualBad expPrm   -- expect false (56 - 6 = 50 = 16 mod 17)

/-- `Guard::verify` (msm.rs:223-234) on the same two fixtures: ok for the valid
    one, `Error::Opening` for the invalid one. Written as a match because `Fault`
    carries a `String` panic site and has no `DecidableEq`, so it cannot be
    `decide`d - the same reason Exec/Native compares faults by matching. -/
def dualVerifyOk_kats_ok : Bool :=
  match DualMSM.verify dualOk expPrm with
  | .ok () => true
  | .error _ => false

def dualVerifyBad_kats_ok : Bool :=
  match DualMSM.verify dualBad expPrm with
  | .error (Fault.error (Error.opening)) => true
  | _ => false

#eval dualVerifyOk_kats_ok           -- expect true
#eval dualVerifyBad_kats_ok          -- expect true

-- `MSMKZG.check` (msm.rs:136-138): the single-channel version, the MSM evaluates
-- to the identity of G₁. G₂ and Gₜ have to be named: they appear in no argument,
-- which is the D-P7 phantom-parameter situation.
example : MSMKZG.check (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17)
    (MSMKZG.fromBase (ex 0)) = true := by decide
example : MSMKZG.check (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17)
    (MSMKZG.fromBase (ex 1)) = false := by decide
/-- `msmSpecific` drops zero coefficients (msm.rs:163-191); the sum here is
    0·(9) + 4·(3) + 0·(1) = 12 ≠ 0, and adding a zero term must not change it. -/
example : MSMKZG.check (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17)
    { scalars := #[0, 4, 0], bases := #[ex 9, ex 3, ex 1],
      labels := #[.noLabel, .noLabel, .noLabel] } = false := by decide
example : MSMKZG.check (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17)
    { scalars := #[0, 4, 5], bases := #[ex 9, ex 3, ex 1],
      labels := #[.noLabel, .noLabel, .noLabel] } = true := by decide

-- The negation hazard of Exec/Kzg/Params.lean, made visible: with
-- `nG2Prepared = +1` instead of `-1` the *same* left channel needs a different
-- right channel, so a params file built by the wrong constructor flips the
-- answer. This is the class of bug the harness is for.
def expPrmNoNeg : ParamsVerifierKZG (Exp 17) (Exp 17) :=
  { sG2 := ex 4, nG2Prepared := ex 1, sG2Prepared := ex 4 }
example : DualMSM.check dualOk expPrmNoNeg = false := by decide
example : DualMSM.check (DualMSM.new leftMsm (rightMsm 12)) expPrmNoNeg = true := by decide

-- `DualMSM.scale` scales *both* channels (msm.rs:271-274), so it preserves the
-- check; scaling one channel only must break it.
--
-- Scaling the left channel of `dualOk` by 3 turns the left exponent into
-- 3·14 = 42 = 8, so the equation becomes 8·4 - r = 32 - r, i.e. r = 32 = 15.
def leftScaled : MSMKZG (Fr 17) (Exp 17) :=
  { scalars := #[6, 9], bases := #[ex 5, ex 7], labels := #[.noLabel, .noLabel] }
example : expOf leftScaled.eval = 8 := by decide
example : DualMSM.check (DualMSM.new leftScaled (rightMsm 15)) expPrm = true := by decide
example : DualMSM.check (DualMSM.new leftScaled (rightMsm 5)) expPrm = false := by decide

-- The same two facts through the `scale` function itself rather than through a
-- hand-scaled literal. These need `native_decide`, and only here in the file:
-- `scale` is `scalars.map`, and `Array.map` does not reduce in the kernel at all
-- (it is implemented over the private `Array` representation), so `decide` gets
-- stuck on it however small the array is. `native_decide` is the one tactic the CI
-- gate confines to this directory (scripts/checks.sh); it is used only inside
-- `example`s, so no definition or theorem here depends on it and
-- `Lean.ofReduceBool` cannot leak into any statement.
example : DualMSM.check (DualMSM.scale dualOk 3) expPrm = true := by native_decide
example : DualMSM.check (DualMSM.new (dualOk.left.scale 3) dualOk.right) expPrm = false :=
  by native_decide
example : (dualOk.scale 3).left.eval = leftScaled.eval := by native_decide

-- The codec round-trips, so a commitment the transcript reads is the point that
-- was absorbed. The 48-byte wire width makes the kernel reduction of
-- `natToBytesBE`/`bytesToNatBE` exceed the default recursion budget, hence the
-- local `maxRecDepth` bump: still `decide`, so the result is kernel-checked and
-- adds no axiom.
set_option maxRecDepth 100000 in
example : (expG1Codec (p := 17)).ofCompressed?
    ((expG1Codec (p := 17)).toCompressed (ex 11)) = some (ex 11) := by decide
set_option maxRecDepth 100000 in
example : (expG1Codec (p := 17)).ofEip?
    ((expG1Codec (p := 17)).toEip (ex 4)) = some (ex 4) := by decide
example : (expG1Codec (p := 17)).ofCompressed? (natToBytesBE 11 47)
    = (none : Option (Exp 17)) := by decide

-- ## End to end: the whole Exec verifier pipeline runs on a hand-built fixture
--
-- This is what R-28 was blocking. `Verifier.prepare` = `parseTrace` +
-- `verifyAlgebraicConstraints` = the transcript schedule, the instance inner
-- products, the fixed-eval insert back-fill, the partially evaluated batched
-- identities, the linearization MSM, the seven-input query vector,
-- `multiPrepare`'s two x-challenges, its `f_com`/`q_evals_on_x3` reads, the
-- truncation of `x3`, the `v` vector and finally `DualMSM.check`. Every one of
-- those steps is *executed* below, with the model supplying the pairing at the
-- end.
--
-- The fixture is a one-advice-column, one-fixed-column, one-instance-column
-- constraint system with a single gate `q_fixed(0) * advice(0)` whose queried
-- selector is simple, so the gate's term is linearized onto the fixed
-- commitment rather than folded into the constant side. The proof is 304 bytes
-- laid out in the order the Rust reads them.
--
-- The last of those bytes is pi, the KZG opening commitment, and it is the only
-- one that varies between the two checks below. In the exponent model the final
-- equation is `pi·sG2 - (seven-term sum) = 0`, i.e. a linear equation in `pi`,
-- so exactly one value of `pi` in `0..16` satisfies it - 11 - and the other
-- sixteen do not. Finding it is nothing harder than a division in `ZMod 17`,
-- which is exactly header note 2: the model knows every exponent, so it can play
-- the prover. What the KAT establishes is the verifier's side:
-- that 304 bytes of transcript, the alpha-batching, the truncation and the
-- seven-term right channel collapse to an equation that holds at pi = 11 and
-- fails at pi = 12.

/-- The advice commitment, the two quotient limbs, the advice evaluation, `f_com`,
    the single `q_evals_on_x3` entry and pi, in the order the Rust reads them. -/
def e2eProof (pi : Nat) : Bytes :=
  ByteArray.mk ((natToBytesBE 3 48).data.toList     -- advice commitment, exponent 3
    ++ (natToBytesBE 1 48).data.toList              -- quotient limb 0
    ++ (natToBytesBE 2 48).data.toList              -- quotient limb 1
    ++ (natToBytesLE 5 32).data.toList              -- advice evaluation at x
    ++ (natToBytesBE 6 48).data.toList              -- f_com
    ++ (natToBytesLE 4 32).data.toList              -- q_evals_on_x3
    ++ (natToBytesBE pi 48).data.toList             -- pi
    ++ (List.replicate 64 (0 : UInt8))).toArray     -- slack: assert_empty is the caller's

/-- The gate: `q_fixed(0) * advice(0)` with a SIMPLE queried selector, so the
    linearization puts it on the fixed commitment. A `Expression.selector` would
    panic at mod.rs:532 - virtual selectors are gone by VK time. -/
def e2eGate : Gate (Fr 17) :=
  { name := "g", constraintNames := #["c"],
    polys := #[Expression.product
      (Expression.fixed { index := some 0, columnIndex := 0, rotation := .cur })
      (Expression.advice { index := some 0, columnIndex := 0, rotation := .cur, phase := ⟨0⟩ })],
    queriedSelectors := #[{ index := 0, isSimple := true }], queriedCells := #[] }

def e2eCs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default (F := Fr 17) with
    numAdviceColumns := 1, adviceColumnPhase := #[⟨0⟩],
    numInstanceColumns := 1, numFixedColumns := 1,
    selectorFlags := #[{ isSimple := true, colIdx := some 0 }],
    fixedQueries := #[({ index := 0, columnType := Any.fixed }, Rotation.cur)],
    adviceQueries := #[({ index := 0, columnType := Any.adviceFirst }, Rotation.cur)],
    instanceQueries := #[({ index := 0, columnType := Any.instance }, Rotation.cur)],
    gates := #[e2eGate] }

/-- The size-4 extended domain over `Fr 17`, the same one Exec/Verifier's own
    KATs use. -/
def e2eDom : EvaluationDomain (Fr 17) :=
  { n := 4, k := 2, extendedK := 2, omega := 13, omegaInv := 4,
    extendedOmega := 13, extendedOmegaInv := 4, gCoset := 2, gCosetInv := 4,
    quotientPolyDegree := 2, ifftDivisor := 13, extendedIfftDivisor := 13,
    tEvaluations := #[8], barycentricWeight := 13 }

def e2eVk : VerifyingKey (Fr 17) (Exp 17) :=
  { domain := e2eDom, fixedCommitments := #[ex 7], permutation := ⟨#[]⟩,
    cs := e2eCs, csDegree := 3, transcriptRepr := 7 }

/-- The KZG instantiation of the PCS record (rule R9), with the production
    features and `fc17` from Exec/Domain. -/
def e2ePcs : Pcs 17 (Exp 17) (Exp 17) (Exp 17) :=
  Pcs.kzg (p := 17) expG1Codec fc17 Features.solidity false

/-- `Verifier.prepare` on the fixture, or the fault it failed with. -/
def e2eRun (pi : Nat) : Except Fault (DualMSM (Fr 17) (Exp 17) (Exp 17) (Exp 17)) :=
  match (Verifier.prepare (p := 17) expG1Codec 2 Features.solidity e2ePcs e2eVk
      (#[#[]] : Array (Array (Exp 17))) (#[#[#[0, 1]]])).run
      (Transcript.initFromBytes (e2eProof pi)) with
  | .ok (d, _) => .ok d
  | .error f => .error f

/-- The bytes the pipeline must consume: 48 advice + 96 quotient limbs + 32 advice
    eval + 48 f_com + 32 q_eval_on_x3 + 48 pi = 304. -/
def e2eBytesRead (pi : Nat) : Nat :=
  match (Verifier.prepare (p := 17) expG1Codec 2 Features.solidity e2ePcs e2eVk
      (#[#[]] : Array (Array (Exp 17))) (#[#[#[0, 1]]])).run
      (Transcript.initFromBytes (e2eProof pi)) with
  | .ok (_, t) => t.pos
  | .error _ => 0

/-- pi = 11: the verifier accepts. Left channel exponent 11, right channel 10,
    and 11·4 - 10 = 34 = 0 in ZMod 17. -/
def e2eAccept_kats_ok : Bool :=
  match e2eRun 11 with
  | .ok d => DualMSM.check d expPrm && e2eBytesRead 11 == 304
  | .error _ => false

/-- pi = 12: one byte of the proof changes and the verifier rejects with
    `Error::Opening`. Left 12, right 6, and 12·4 - 6 = 42 = 8 ≠ 0. -/
def e2eReject_kats_ok : Bool :=
  match e2eRun 12 with
  | .ok d => ! DualMSM.check d expPrm
  | .error _ => false

/-- And the guard really is non-vacuous: both channels evaluate to a non-identity
    point, so neither side of the pairing equation is trivially zero. -/
def e2eNonVacuous_kats_ok : Bool :=
  match e2eRun 11 with
  | .ok d => expOf d.left.eval == 11 && expOf d.right.eval == 10
  | .error _ => false

#eval e2eAccept_kats_ok        -- expect true
#eval e2eReject_kats_ok        -- expect true
#eval e2eNonVacuous_kats_ok    -- expect true
#eval e2eBytesRead 11          -- expect 304

-- `native_decide` again, and for the same reason as the `scale` checks: the
-- pipeline reads and writes `Array`s throughout (`Array.map`, `Array.zip`,
-- `Array.drop`), none of which reduce in the kernel. The keccak squeezes inside
-- the transcript would also exceed any sane `maxRecDepth`. These are `example`s
-- over a `Bool` defined above, so the computation is still checked - it is just
-- checked by the compiler rather than the kernel - and nothing in the file's
-- *definitions* depends on them.
example : e2eAccept_kats_ok = true := by native_decide
example : e2eReject_kats_ok = true := by native_decide
example : e2eNonVacuous_kats_ok = true := by native_decide
example : e2eBytesRead 11 = 304 := by native_decide

end Kats

end Midfall.Instances

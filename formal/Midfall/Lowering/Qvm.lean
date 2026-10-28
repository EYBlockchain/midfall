-- |
-- Midfall.Lowering.Qvm
--
-- P-SE stage 5, file 1 of 2 (docs/plans/P-SE-stage5.md; plan index section O,
-- P-SE-semantic-equivalence.md:1932-2076; design1.md M6-0 to M6-3 and hazard 5).
--
-- WHAT THIS FILE IS FOR. Everything M6 says about the quotient VM has to be typed
-- over four things that were ported by four different packages and never joined:
-- P-09b's reference interpreter (VmReference), P-09c's builder (VmBuilder),
-- P-09d's certifier (VmCertify) and P-09e's validator (VmValidator). This file
-- joins them, in four layers, and each layer says what it buys.
--
-- 1. THE QVMFr <-> Fr r BRIDGE. QVMFr is 'abbrev QVMFr : Type := Nat' with an
--    explicit '% qvmFrModulus' in every operation (VmReference.lean:252-266); the
--    verifier's field is 'Fr r = ZMod r'. The tie used to be a Bool KAT
--    (qvmFrModulus_agreesWithBlsR_ok). It is now a kernel fact: qvmFrModulus_eq_r is
--    PROVED by 'decide', and qvmToFr is PROVED to preserve +, *, - and to be
--    injective on canonical representatives. All four are theorems, not holes.
-- 2. THE VALUATION LAYER. evalQuotientExpr only ever ranges over Keccak-PRNG
--    assignments, so a theorem about it cannot be instantiated at real verifier
--    memory (survey, QVM area: "Quantifying over QuotientRefMemory only ranges over
--    Keccak-PRNG assignments"). Valuation, memKey, memOfρ and evalExprρ give the
--    ∀ρ reading, and evalQuotientExpr_memOfρ PROVES that the ported interpreter,
--    run on a memory whose cache is pre-populated from ρ, computes exactly ρ's
--    denotation and does not grow the cache. That is the whole reason no
--    VmReference refactor was needed (design1 open decision: "memOfρ now; revisit a
--    QuotientMemModel refactor only if the Yul composition proof needs per-step
--    memory reasoning").
-- 3. THE SHAPE DENOTATIONS AND RecognizersSound. VmReference has BYTE DECODERS
--    (limbLinearForm, limbRowForm, limbPairwiseForm, modarith7Form) and no
--    denotation of a QuotientLimbShape over a valuation, so the denotation is
--    written here - following the DECODER and not the builder, per design1 M6-1's
--    risk note (the MODARITH7 mem block is (slot, ptr); the standalone affine term
--    is (ptr, slot)). RecognizersSound is the hypothesis every compile-correctness
--    statement needs, and noShapeRecognizers_sound PROVES the conservative hook
--    bundle satisfies it.
-- 4. THE COMPILE-CORRECTNESS STATEMENTS. D-P20 (amended at 514c808) says
--    qvm_compile_correct is TWO claims. Claim 2 - per-identity compile correctness
--    over evalQuotientIdentity - is stated here as qvm_compile_correct_identity,
--    with the certifier forms (a) beside it and the restated qvm_validated_noOOB
--    under hazard 5. Claim 1 - the per-stream fold agreement over
--    evalQuotientProgramArtifacts vs expectedLinearizationArtifacts - lives in
--    QvmFold.lean, because it is a claim about the fold.
--
-- attack.md FIXES APPLIED HERE (binding).
--   * qvm_compile_correct_identity: the returned memory is EXISTENTIAL. A sound
--     recognizer may read a pointer outside leafKeys e, the interpreter's derive
--     then conses onto the cache, and '= memOfρ ...' fails while the value is
--     right. The plan's own sketch (section O) already carries the fix; it is kept,
--     and NoMiss is stated separately rather than folded into the conclusion.
--   * builder_segments_total: '.oob' does not exist. QVMFault has readPastEnd and
--     constSlotOutOfRange (VmReference.lean:284-296), so the statement is about the
--     two real fault classes - over the REAL validator predicate, hazard 5 below.
--   * itemStarts is DEFINED here from quotientOpLen, as design1 M6-3's FIX line
--     promises, rather than left as a sketch comment.
--
-- HAZARD 5, ANSWERED. The design sketched qvm_validated_noOOB over an abstract
-- 'validate : List Nat → List Word256 → OperandModel → Except String Unit' because
-- P-09e had no way to build an operand model from a plan. That is stale: P-09e
-- landed validateQuotientProgramOperands (VmValidator.lean:1162) and P-11 landed
-- the one-argument bridge quotientOperandModel plus LoweringPlan.supportedQvm
-- (LoweringPlan.lean:436, :740). So qvm_validated_noBoundsFault and
-- qvm_validated_windows below are stated against the REAL predicate, with the real
-- QuotientOperandModel built from a real LoweringPlan, and no stand-in field. The
-- window half is a LAYOUT property (D-P20 item 2's resolution: quantified over the
-- read model, not over a memory object and not as an interpreter fault).
--
-- STALE CLAIMS THIS FILE CORRECTS.
--   * Section O line 2002 documents RecognizersSound as "the recognizer hooks
--     (P-09f unported)". P-09f landed them (VmRecognizers.lean, shapeRecognizers).
--     The substantive warning stands - compile correctness is still false for an
--     arbitrary hook bundle, and recognizersSound_pow5ArmIsLoadBearing_ok exhibits
--     one - but the blocker note is gone.
--   * Section P line 2138 says quotient_expr_from_expression "is unported". It is
--     ported: QuotientBlocks.lean:308, with quotientExprFromPlonkExpr at :381 and
--     DataQuotientExpressionEnv at :340. See QvmFold.lean's header for what that
--     changes about IdentityCorrespondence.
--
-- SKETCH NAMES FROM SECTION O THAT DO NOT RESOLVE (reported, not invented):
--   * 'open Midfall.Generator (QuotientShapeRecognizers noShapeRecognizers)' - both
--     live in Midfall.Generator.QuotientBuilder, not Midfall.Generator.
--   * The bare '(r)' / '(hr)' / '(plan)' binders on qvm_compile_correct_certifier,
--     qvm_compile_correct_program and builder_segments_total do not elaborate:
--     lakefile.toml sets autoImplicit = false, so every binder is typed out below.
--   * shapePtrsU16 and modarith7WellFormed are sketched as ':= sorry' DEFINITIONS.
--     A hole in a definition is worse than a hole in a proof - every statement
--     reading it would be about an unknown Prop - so both are written out here from
--     the encoder's own widths (emitU16 exactness, the five count bytes, and
--     QuotientLimbShape.wellFormed).
--   * itemStarts (sketched, undefined) is defined here; limbScalars (sketched in
--     section P) is defined in QvmFold.lean.
--   * The sketch's '(s₁.bytes.drop s₀.bytes.length)' is fine only because the
--     BUILDER's bytes are a List Nat (VmBuilder.lean:261); the BUILD's bytes are a
--     Bytes and must go through qvmBytesToNats (VmTypes.lean:638). Both are used
--     below in those types, never interchanged.
--
-- NO Midfall/Instances/ IMPORT (D-P17): every object stated below comes from
-- Generator/Quotient/*, Generator/LoweringPlan.lean or Assumptions/Pairing.lean.
--
-- HAZARD 2 (Fr 17 is too small, R-55): every gate in this file runs over the REAL
-- modulus - either QVMFr Nat arithmetic at qvmFrModulus or Fr Midfall.Assumptions.r.
-- No gate here uses a small field.

import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.VmValidator
import Midfall.Generator.LoweringPlan
import Midfall.Assumptions.Pairing

namespace Midfall.Lowering

open Midfall
open Midfall.Generator
open Midfall.Generator (QVMFr QVMFault QuotientExpr QuotientMem QuotientRefMemory
  QuotientLimbShape QuotientModarith7Shape QuotientTarget QuotientIdentity
  QuotientProgramItem QuotientProgramPlan QuotientProgramBuild SelectorFoldPlan
  fqFromU256 qvmFrAdd qvmFrMul qvmFrNeg qvmFrModulus qvmBytesToNats qvmBytesOfNats
  deriveReferenceMemory quotientRefMemoryCacheGet quotientRefMemoryNew
  quotientVmLimbs qvmWordBytes)
open Midfall.Generator.QuotientBuilder
open Midfall.Generator.QuotientCertify
open Midfall.Generator.QuotientValidator

/-! ### 1. The QVMFr ↔ Fr r bridge (design1 M6-0) -/

/-- The two literals are the same number: qvmFrModulus (VmReference.lean:244) and
    Midfall.Assumptions.r (Assumptions/Pairing.lean:35, from CompPoly). 'decide' is
    what the plan asks for and it terminates; 'rfl' also works (both sides reduce to
    the same binary literal), and a gate below pins both so a wrong digit cannot
    survive either way. This replaces the Bool-only tie
    qvmFrModulus_agreesWithBlsR_ok. -/
theorem qvmFrModulus_eq_r : qvmFrModulus = Midfall.Assumptions.r := by decide

/-- The verifier-side scalar field at the BLS12-381 modulus; section O names it FrR. -/
abbrev FrR := Midfall.Fr Midfall.Assumptions.r

/-- The cast from the VM's canonical-Nat field to the verifier's 'ZMod r'. -/
def qvmToFr (v : QVMFr) : FrR := (v : FrR)

/-- qvmFrAdd is the cast of '+': the '% qvmFrModulus' the VM applies is the reduction
    ZMod applies anyway, so no canonicity hypothesis is needed. -/
theorem qvmToFr_add (a b : QVMFr) : qvmToFr (qvmFrAdd a b) = qvmToFr a + qvmToFr b := by
  unfold qvmToFr qvmFrAdd
  rw [qvmFrModulus_eq_r, ZMod.natCast_mod, Nat.cast_add]

/-- The multiplication twin of qvmToFr_add, same reason. -/
theorem qvmToFr_mul (a b : QVMFr) : qvmToFr (qvmFrMul a b) = qvmToFr a * qvmToFr b := by
  unfold qvmToFr qvmFrMul
  rw [qvmFrModulus_eq_r, ZMod.natCast_mod, Nat.cast_mul]

/-- Negation needs the canonicity hypothesis: qvmFrNeg is '(m - a) % m', and for
    'a ≥ m' that is '0', not '-a'. This is the R2 note in the plan's sketch ("QVMFr
    is Nat, only canonical representatives are field elements"). The 'a = 0' case is
    separate because '(m - 0) % m = 0 ≠ m - 0'. -/
theorem qvmToFr_neg (a : QVMFr) (ha : a < qvmFrModulus) :
    qvmToFr (qvmFrNeg a) = - qvmToFr a := by
  have ha' : a < Midfall.Assumptions.r := qvmFrModulus_eq_r ▸ ha
  unfold qvmToFr qvmFrNeg
  rw [qvmFrModulus_eq_r]
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · simp [Nat.mod_self]
  · have hlt : Midfall.Assumptions.r - a < Midfall.Assumptions.r := Nat.sub_lt (by decide) hpos
    rw [Nat.mod_eq_of_lt hlt, Nat.cast_sub (Nat.le_of_lt ha'), ZMod.natCast_self, zero_sub]

/-- Injectivity on canonical representatives, i.e. the cast is a bijection onto the
    window '0 .. r-1'. Without 'ha'/'hb' it is false: qvmToFr qvmFrModulus = qvmToFr 0
    with qvmFrModulus ≠ 0, gated by qvmToFr_needsCanonicity_ok. -/
theorem qvmToFr_injOn : ∀ (a b : QVMFr), a < qvmFrModulus → b < qvmFrModulus →
    qvmToFr a = qvmToFr b → a = b := by
  intro a b ha hb h
  unfold qvmToFr at h
  have ha' : a < Midfall.Assumptions.r := qvmFrModulus_eq_r ▸ ha
  have hb' : b < Midfall.Assumptions.r := qvmFrModulus_eq_r ▸ hb
  have h2 := congrArg (ZMod.val : FrR → ℕ) h
  rw [ZMod.val_natCast, ZMod.val_natCast] at h2
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2
  exact h2

/-! ### 2. The valuation layer (design1 M6-0) -/

/-- A valuation of verifier memory: domain 0 is the literal pointer space and domain
    '1 + t' is token t (VmReference.lean:441-453). Keys wrap exactly like the
    interpreter's cache key - 'domain % 256', 'address % 2^32'
    (VmReference.lean:424-428) - which is what makes token 0xff land in the literal
    domain, the behaviour the existing KAT tokenDomainU8Wrap_releaseProfile_ok pins.
    An UNWRAPPED memKey disagrees with the interpreter on that token;
    valuation_tokenWrapIsLoadBearing_ok is the gate for this sentence. -/
abbrev Valuation := Nat → Nat → QVMFr

/-- The cache key of one memory operand, with the interpreter's two reductions. -/
def memKey : QuotientMem → Nat × Nat
  | .literal ptr => (0, ptr % 2 ^ 32)
  | .token t => ((1 + t) % 256, 0)
  | .tokenOffset t o => ((1 + t) % 256, o % 2 ^ 32)

/-- The shadow denotation of an expression under a valuation: the same recursion as
    evalQuotientExpr (VmReference.lean:459-478) with the PRNG read replaced by ρ. The
    only failure it can report is fqFromU256 rejecting a non-canonical constant,
    which is divergence (1) of the survey's "Yul and reference diverge in two
    places". -/
def evalExprρ (ρ : Valuation) : QuotientExpr → Except QVMFault QVMFr
  | .const v => fqFromU256 v
  | .mem m => .ok (ρ (memKey m).1 (memKey m).2)
  | .add l r => do let a ← evalExprρ ρ l; let b ← evalExprρ ρ r; pure (qvmFrAdd a b)
  | .mul l r => do let a ← evalExprρ ρ l; let b ← evalExprρ ρ r; pure (qvmFrMul a b)
  | .neg e => do let a ← evalExprρ ρ e; pure (qvmFrNeg a)

/-- A reference memory whose cache is pre-populated from ρ on the key set S. The
    ported interpreter consults the cache FIRST (VmReference.lean:433-438), so on a
    hit it returns ρ's value and leaves the memory alone: that is how the ∀ρ
    statements are obtained without touching VmReference.lean, which this package
    does not own. Keys are stored reduced, matching the key derive inserts. -/
def memOfρ (ρ : Valuation) (S : List (Nat × Nat)) : QuotientRefMemory :=
  { seed := Midfall.Bytes.empty,
    cache := S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32, ρ (k.1 % 256) (k.2 % 2 ^ 32))) }

/-- No miss happened: the memo table did not grow, i.e. every read was a cache hit.
    Kept SEPARATE from the value statement, per attack.md's FIX ("require shapePtrs
    sh ⊆ S in RecognizersSound and keep NoMiss as a separate lemma"). -/
def NoMiss (m m' : QuotientRefMemory) : Prop := m'.cache = m.cache

/-- The invariant a certifier memory satisfies: every cached entry is the value the
    seed derives at that key, and the keys are reduced. A fresh
    'quotientRefMemoryNew seed' satisfies it trivially (empty cache) and every memory
    the interpreter produces from one satisfies it, because derive inserts exactly
    'deriveReferenceMemory seed d a' at the reduced key. -/
def CacheConsistent (m : QuotientRefMemory) : Prop :=
  ∀ e ∈ m.cache, e.2.2 = Midfall.Generator.deriveReferenceMemory m.seed e.1 e.2.1
    ∧ e.1 < 256 ∧ e.2.1 < 2 ^ 32

/-- The reduced cache keys of an expression's memory leaves. QuotientExpr.memLeaves
    is VmTypes.lean:484, so the sketch's SKETCH comment on leafKeys resolves. -/
def leafKeys (e : QuotientExpr) : List (Nat × Nat) := e.memLeaves.map memKey

/-- A cache hit short-circuits derive and leaves the memory untouched: the one
    property of VmReference.lean:433-439 the whole valuation layer rests on. -/
theorem derive_hit (m : QuotientRefMemory) (d a v : QVMFr)
    (h : quotientRefMemoryCacheGet m d a = some v) : m.derive d a = (v, m) := by
  unfold QuotientRefMemory.derive
  rw [h]

/-- The one-step equation of the interpreter's cache lookup on a cons: the head's key
    is tested first, and only when it misses does the tail get searched. Stated as a
    lemma because quotientRefMemoryCacheGet's match hides it. Not a Rust item. -/
theorem cacheGet_cons (c : List (Nat × Nat × QVMFr)) (e : Nat × Nat × QVMFr) (d a : Nat) :
    (match List.find? (fun t : Nat × Nat × QVMFr =>
          t.1 == d % 256 && t.2.1 == a % 2 ^ 32) (e :: c) with
    | some (_, _, v) => some v
    | none => none) =
    if e.1 == d % 256 && e.2.1 == a % 2 ^ 32 then some e.2.2
    else match List.find? (fun t : Nat × Nat × QVMFr =>
            t.1 == d % 256 && t.2.1 == a % 2 ^ 32) c with
      | some (_, _, v) => some v
      | none => none := by
  by_cases hc : (e.1 == d % 256 && e.2.1 == a % 2 ^ 32)
  · rw [List.find?_cons, hc]; rfl
  · have hc' : (e.1 == d % 256 && e.2.1 == a % 2 ^ 32) = false := by simpa using hc
    rw [List.find?_cons, hc']; rfl

theorem cacheGet_memOfρ (ρ : Valuation) : ∀ (S : List (Nat × Nat)) (d a : Nat),
    (d % 256, a % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32)) →
    quotientRefMemoryCacheGet (memOfρ ρ S) d a = some (ρ (d % 256) (a % 2 ^ 32))
  | [], _, _, h => by cases h
  | x :: xs, d, a, h => by
      cases x with
      | mk x1 x2 =>
        have hmem : (d % 256, a % 2 ^ 32) ∈ (x1 % 256, x2 % 2 ^ 32) ::
            xs.map (fun k => (k.1 % 256, k.2 % 2 ^ 32)) := by rwa [List.map_cons] at h
        have key : quotientRefMemoryCacheGet (memOfρ ρ ((x1, x2) :: xs)) d a =
            match List.find? (fun t : Nat × Nat × QVMFr =>
                  t.1 == d % 256 && t.2.1 == a % 2 ^ 32)
                ((x1 % 256, x2 % 2 ^ 32, ρ (x1 % 256) (x2 % 2 ^ 32)) ::
                  xs.map (fun k => (k.1 % 256, k.2 % 2 ^ 32, ρ (k.1 % 256) (k.2 % 2 ^ 32)))) with
          | some (_, _, v) => some v
          | none => none := rfl
        have htail : quotientRefMemoryCacheGet (memOfρ ρ xs) d a =
            match List.find? (fun t : Nat × Nat × QVMFr =>
                  t.1 == d % 256 && t.2.1 == a % 2 ^ 32)
                (xs.map (fun k => (k.1 % 256, k.2 % 2 ^ 32, ρ (k.1 % 256) (k.2 % 2 ^ 32)))) with
          | some (_, _, v) => some v
          | none => none := rfl
        rw [key, cacheGet_cons]
        split
        · rename_i hc
          have hsplit : (x1 % 256 == d % 256) = true ∧ (x2 % 2 ^ 32 == a % 2 ^ 32) = true :=
            (Iff.of_eq (Bool.and_eq_true _ _)).mp hc
          have h1 : x1 % 256 = d % 256 := Iff.mp beq_iff_eq hsplit.1
          have h2 : x2 % 2 ^ 32 = a % 2 ^ 32 := Iff.mp beq_iff_eq hsplit.2
          rw [← h1, ← h2]
        · rename_i hc
          have hrest : (d % 256, a % 2 ^ 32) ∈ xs.map (fun k => (k.1 % 256, k.2 % 2 ^ 32)) := by
            rcases List.mem_cons.mp hmem with he | hr
            · exfalso
              have h1 : d % 256 = x1 % 256 := by simpa using congrArg Prod.fst he
              have h2 : a % 2 ^ 32 = x2 % 2 ^ 32 := by simpa using congrArg Prod.snd he
              have hc' : (x1 % 256 == d % 256 && x2 % 2 ^ 32 == a % 2 ^ 32) = true := by
                rw [Bool.and_eq_true]
                exact ⟨Iff.mpr beq_iff_eq h1.symm, Iff.mpr beq_iff_eq h2.symm⟩
              exact absurd hc' hc
            · exact hr
          rw [← htail]
          exact cacheGet_memOfρ ρ xs d a hrest

/-- The literal read of a pre-populated memory is ρ, and the memory is unchanged. -/
theorem literal_memOfρ (ρ : Valuation) (S : List (Nat × Nat)) (ptr : Nat)
    (h : (0, ptr % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    (memOfρ ρ S).literal ptr = (ρ 0 (ptr % 2 ^ 32), memOfρ ρ S) := by
  have hget : quotientRefMemoryCacheGet (memOfρ ρ S) 0 ptr =
      some (ρ (0 % 256) (ptr % 2 ^ 32)) := cacheGet_memOfρ ρ S 0 ptr h
  have := derive_hit (memOfρ ρ S) 0 ptr (ρ (0 % 256) (ptr % 2 ^ 32)) hget
  show (memOfρ ρ S).derive 0 ptr = (ρ 0 (ptr % 2 ^ 32), memOfρ ρ S)
  exact this

/-- The token read, same proof, with the '1 + t' domain and the offset key. -/
theorem token_memOfρ (ρ : Valuation) (S : List (Nat × Nat)) (t o : Nat)
    (h : ((1 + t) % 256, o % 2 ^ 32) ∈ S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32))) :
    (memOfρ ρ S).token t o = (ρ ((1 + t) % 256) (o % 2 ^ 32), memOfρ ρ S) := by
  have hget : quotientRefMemoryCacheGet (memOfρ ρ S) (1 + t) o =
      some (ρ ((1 + t) % 256) (o % 2 ^ 32)) := cacheGet_memOfρ ρ S (1 + t) o h
  have := derive_hit (memOfρ ρ S) (1 + t) o (ρ ((1 + t) % 256) (o % 2 ^ 32)) hget
  show (memOfρ ρ S).derive (1 + t) o = (ρ ((1 + t) % 256) (o % 2 ^ 32), memOfρ ρ S)
  exact this




/-- THE VALUATION LAYER'S CORRECTNESS THEOREM, and the place this file turns a plan
    sketch (section O line 1982, ':= by sorry') into a proof. The ported oracle
    evaluated on a memory pre-populated from ρ computes ρ's denotation and leaves the
    memory alone. 'hS' is the no-miss condition on the leaves: without it derive fires
    and the value is a Keccak output rather than ρ's, which is what the existing KAT
    tokenDomainU8Wrap_releaseProfile_ok is about. -/
theorem evalQuotientExpr_memOfρ (ρ : Valuation) (e : QuotientExpr)
    (S : List (Nat × Nat)) (hS : ∀ k ∈ leafKeys e, k ∈ S) :
    Midfall.Generator.evalQuotientExpr e (memOfρ ρ S)
      = (evalExprρ ρ e).map (fun v => (v, memOfρ ρ S)) := by
  induction e with
  | const v =>
      show fqFromU256 v >>= (fun x => .ok (x, memOfρ ρ S)) = (evalExprρ ρ (QuotientExpr.const v)).map (fun v => (v, memOfρ ρ S))
      simp only [evalExprρ]
      cases fqFromU256 v <;> rfl
  | mem m =>
      have hleaf : memKey m ∈ leafKeys (QuotientExpr.mem m) := by
        simp [leafKeys, QuotientExpr.memLeaves]
      have hmem : memKey m ∈ S := hS (memKey m) hleaf
      have hmap : ((memKey m).1 % 256, (memKey m).2 % 2 ^ 32) ∈
          S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32)) :=
        List.mem_map.mpr ⟨memKey m, hmem, rfl⟩
      cases m with
      | literal ptr =>
          have h1 : (memOfρ ρ S).literal ptr = (ρ 0 (ptr % 2 ^ 32), memOfρ ρ S) :=
            literal_memOfρ ρ S ptr (by simpa [memKey] using hmap)
          show (.ok ((memOfρ ρ S).literal ptr) : Except QVMFault (QVMFr × QuotientRefMemory)) = (evalExprρ ρ (QuotientExpr.mem (QuotientMem.literal ptr))).map (fun v => (v, memOfρ ρ S))
          rw [h1]
          simp only [evalExprρ, memKey]
          rfl
      | token t =>
          have h1 : (memOfρ ρ S).token t 0 = (ρ ((1 + t) % 256) (0 % 2 ^ 32), memOfρ ρ S) :=
            token_memOfρ ρ S t 0 (by simpa [memKey] using hmap)
          show (.ok ((memOfρ ρ S).token t 0) : Except QVMFault (QVMFr × QuotientRefMemory)) = (evalExprρ ρ (QuotientExpr.mem (QuotientMem.token t))).map (fun v => (v, memOfρ ρ S))
          rw [h1]
          simp only [evalExprρ, memKey]
          rfl
      | tokenOffset t o =>
          have h1 : (memOfρ ρ S).token t o =
              (ρ ((1 + t) % 256) (o % 2 ^ 32), memOfρ ρ S) :=
            token_memOfρ ρ S t o (by simpa [memKey] using hmap)
          show (.ok ((memOfρ ρ S).token t o) : Except QVMFault (QVMFr × QuotientRefMemory)) =
              (evalExprρ ρ (QuotientExpr.mem (QuotientMem.tokenOffset t o))).map (fun v => (v, memOfρ ρ S))
          rw [h1]
          simp only [evalExprρ, memKey]
          rfl
  | add l r ihl ihr =>
      have hl : ∀ k ∈ leafKeys l, k ∈ S := fun k hk => hS k (by
        simp only [leafKeys, QuotientExpr.memLeaves, List.map_append]
        exact List.mem_append.mpr (Or.inl hk))
      have hr : ∀ k ∈ leafKeys r, k ∈ S := fun k hk => hS k (by
        simp only [leafKeys, QuotientExpr.memLeaves, List.map_append]
        exact List.mem_append.mpr (Or.inr hk))
      show (Midfall.Generator.evalQuotientExpr l (memOfρ ρ S)).bind (fun x =>
          (Midfall.Generator.evalQuotientExpr r x.snd).map (fun y =>
            (qvmFrAdd x.fst y.fst, y.snd))) =
        Except.map (fun v => (v, memOfρ ρ S))
          ((evalExprρ ρ l).bind (fun a => (evalExprρ ρ r).map (fun b => qvmFrAdd a b)))
      rw [ihl hl]
      cases h : evalExprρ ρ l with
      | ok lv =>
          show (Midfall.Generator.evalQuotientExpr r (memOfρ ρ S)).map
              (fun y => (qvmFrAdd lv y.fst, y.snd)) =
            ((evalExprρ ρ r).map (fun b => qvmFrAdd lv b)).map (fun v => (v, memOfρ ρ S))
          rw [ihr hr]
          cases evalExprρ ρ r <;> rfl
      | error f =>
          show Except.error f = Except.error f
          rfl
  | mul l r ihl ihr =>
      have hl : ∀ k ∈ leafKeys l, k ∈ S := fun k hk => hS k (by
        simp only [leafKeys, QuotientExpr.memLeaves, List.map_append]
        exact List.mem_append.mpr (Or.inl hk))
      have hr : ∀ k ∈ leafKeys r, k ∈ S := fun k hk => hS k (by
        simp only [leafKeys, QuotientExpr.memLeaves, List.map_append]
        exact List.mem_append.mpr (Or.inr hk))
      show (Midfall.Generator.evalQuotientExpr l (memOfρ ρ S)).bind (fun x =>
          (Midfall.Generator.evalQuotientExpr r x.snd).map (fun y =>
            (qvmFrMul x.fst y.fst, y.snd))) =
        Except.map (fun v => (v, memOfρ ρ S))
          ((evalExprρ ρ l).bind (fun a => (evalExprρ ρ r).map (fun b => qvmFrMul a b)))
      rw [ihl hl]
      cases h : evalExprρ ρ l with
      | ok lv =>
          show (Midfall.Generator.evalQuotientExpr r (memOfρ ρ S)).map
              (fun y => (qvmFrMul lv y.fst, y.snd)) =
            ((evalExprρ ρ r).map (fun b => qvmFrMul lv b)).map (fun v => (v, memOfρ ρ S))
          rw [ihr hr]
          cases evalExprρ ρ r <;> rfl
      | error f =>
          show Except.error f = Except.error f
          rfl
  | neg i ihi =>
      have hi : ∀ k ∈ leafKeys i, k ∈ S := fun k hk => hS k (by
        simp only [leafKeys, QuotientExpr.memLeaves]
        exact hk)
      show (Midfall.Generator.evalQuotientExpr i (memOfρ ρ S)).map (fun x =>
          (qvmFrNeg x.fst, x.snd)) =
        Except.map (fun v => (v, memOfρ ρ S)) ((evalExprρ ρ i).map (fun a => qvmFrNeg a))
      rw [ihi hi]
      cases h : evalExprρ ρ i with
      | ok v => rfl
      | error f => rfl


/-- The memory is unchanged by a hit-only evaluation, stated apart from the value
    (attack.md's FIX: values only in the main statement, no-miss separate). -/
theorem NoMiss_evalQuotientExpr_memOfρ (ρ : Valuation) (e : QuotientExpr)
    (S : List (Nat × Nat)) (hS : ∀ k ∈ leafKeys e, k ∈ S) :
    ∀ m', Midfall.Generator.evalQuotientExpr e (memOfρ ρ S) = .ok (0, m') →
      NoMiss (memOfρ ρ S) m' := by
  intro m' h
  rw [evalQuotientExpr_memOfρ ρ e S hS] at h
  cases he : evalExprρ ρ e with
  | ok v =>
      rw [he] at h
      have hto : some (v, memOfρ ρ S) = some (0, m') := congrArg Except.toOption h
      have h5 : memOfρ ρ S = m' := congrArg Prod.snd (Option.some.inj hto)
      rw [← h5]
      rfl
  | error f =>
      rw [he] at h
      exact nomatch h



/-! ### 3. Shape denotations and recognizer soundness (design1 M6-1) -/

/-- Σ cᵢ · mload(pᵢ) over a limb term block: the shape-level form of limbLinearForm
    (VmReference.lean:576-587). The coefficients are shape VALUES, not const-table
    slots - the builder maps a value to a slot at emit time and the byte decoder
    reads the slot back, which is why the gate below goes through the builder. -/
def denoteLin (ρ : Valuation) (terms : List (Word256 × Nat)) : Except QVMFault QVMFr :=
  terms.foldlM (fun acc t => do
    let c ← fqFromU256 t.1
    pure (qvmFrAdd acc (qvmFrMul c (ρ 0 (t.2 % 2 ^ 32))))) 0

/-- Value of a recognised limb shape under ρ, following the three byte decoders
    (VmReference.lean:576-622) rather than the encoder: row = mload(lhs) · Σ cᵢ·mload(pᵢ)
    with the lhs read FIRST (QVR:403), pairwise = Σ_{i,j<7} coeff[i+j] · mload(a+32i) ·
    mload(b+32j) with the coefficient indexed by i + j over the 13 diagonals. -/
def denoteLimbShape (ρ : Valuation) : QuotientLimbShape → Except QVMFault QVMFr
  | .lin7 terms => denoteLin ρ terms
  | .bilin7Row lhs terms => do
      let inner ← denoteLin ρ terms
      pure (qvmFrMul (ρ 0 (lhs % 2 ^ 32)) inner)
  | .bilin7Pairwise a b coeffs =>
      (List.range quotientVmLimbs).foldlM (fun acc i =>
        (List.range quotientVmLimbs).foldlM (fun acc j => do
          let c ← fqFromU256 (coeffs.getD (i + j) 0)
          pure (qvmFrAdd acc (qvmFrMul (qvmFrMul (ρ 0 ((a + qvmWordBytes * i) % 2 ^ 32))
            (ρ 0 ((b + qvmWordBytes * j) % 2 ^ 32))) c))) acc) 0

/-- The MODARITH7 denotation: const + Σ lin blocks + Σ rows + Σ pairwise + Σ c·mem +
    Σ c·l·r, the whole sum multiplied by mload(cond) when the flag is present
    (VmReference.lean:636-697). A zero 'constant' is the absent FLAG_CONST and
    contributes 0 either way, which is why the decoder's conditional and this
    unconditional add agree - the point VmBuilder's header F-1 records about
    coefficientOperands. -/
def denoteModarith7 (ρ : Valuation) (sh : QuotientModarith7Shape) :
    Except QVMFault QVMFr := do
  let v0 ← fqFromU256 sh.constant
  let v1 ← sh.lin.foldlM (fun acc t => do pure (qvmFrAdd acc (← denoteLin ρ t))) v0
  let v2 ← sh.rows.foldlM (fun acc r => do
    pure (qvmFrAdd acc (← denoteLimbShape ρ (.bilin7Row r.1 r.2)))) v1
  let v3 ← sh.pairwise.foldlM (fun acc q => do
    pure (qvmFrAdd acc (← denoteLimbShape ρ (.bilin7Pairwise q.1 q.2.1 q.2.2)))) v2
  let v4 ← sh.memTerms.foldlM (fun acc t => do
    let c ← fqFromU256 t.1
    pure (qvmFrAdd acc (qvmFrMul c (ρ 0 (t.2 % 2 ^ 32))))) v3
  let v5 ← sh.productTerms.foldlM (fun acc t => do
    let c ← fqFromU256 t.1
    pure (qvmFrAdd acc (qvmFrMul (qvmFrMul c (ρ 0 (t.2.1 % 2 ^ 32)))
      (ρ 0 (t.2.2 % 2 ^ 32))))) v4
  pure (match sh.cond with
    | none => v5
    | some ptr => qvmFrMul v5 (ρ 0 (ptr % 2 ^ 32)))

/-- Every pointer a shape carries fits the u16 the encoder writes: emitU16 panics
    above 0xffff (VmBuilder.lean:339-346), so a denotation and the bytes agree only
    under this bound. Written over pointerOperands, the encoder's own operand list.
    The plan sketches this as ':= sorry'; a definition hole is filled here instead. -/
def shapePtrsU16 (sh : QuotientLimbShape) : Prop :=
  ∀ p ∈ sh.pointerOperands, p ≤ 0xffff

/-- The MODARITH7 well-formedness the encoder assumes: five count bytes, so each block
    has at most 255 entries (VmBuilder.lean:613-615); 7 terms per lin and per row block
    and 13 coefficients per pairwise block, which is exactly QuotientLimbShape.wellFormed
    (VmTypes.lean:511); and every pointer inside the u16 width. The plan sketches this
    as ':= sorry'; it is written out here. -/
def modarith7WellFormed (sh : QuotientModarith7Shape) : Prop :=
  sh.lin.length ≤ 255 ∧ sh.rows.length ≤ 255 ∧ sh.pairwise.length ≤ 255
    ∧ sh.memTerms.length ≤ 255 ∧ sh.productTerms.length ≤ 255
    ∧ (∀ terms ∈ sh.lin, (QuotientLimbShape.lin7 terms).wellFormed = true)
    ∧ (∀ row ∈ sh.rows, (QuotientLimbShape.bilin7Row row.1 row.2).wellFormed = true)
    ∧ (∀ pw ∈ sh.pairwise,
        (QuotientLimbShape.bilin7Pairwise pw.1 pw.2.1 pw.2.2).wellFormed = true)
    ∧ (∀ p ∈ sh.pointerOperands, p ≤ 0xffff)

/-- Soundness of a recognizer hook bundle: a recognised shape denotes the expression
    under EVERY valuation. The plan documents this as needed because "P-09f is
    unported"; P-09f has landed (VmRecognizers.lean, shapeRecognizers), and the
    requirement is unchanged - the hooks are plain functions and nothing in their type
    forces them to be right, so compile correctness is false for an arbitrary bundle
    (recognizersSound_pow5ArmIsLoadBearing_ok exhibits one). 'matched ≠ []' is
    P-09c's F-5 postcondition, whose absence emptyMatchedHookIsAFrontier_ok
    demonstrates. -/
structure RecognizersSound (r : QuotientShapeRecognizers) : Prop where
  /-- rust: QVM:3176-3187 (quotient_pow5_base): e ≡ b^5. -/
  pow5 : ∀ e b, r.pow5Base e = some b → ∀ ρ,
    evalExprρ ρ e = (evalExprρ ρ b).map (fun v =>
      qvmFrMul v (qvmFrMul (qvmFrMul v v) (qvmFrMul v v)))
  /-- rust: QVM:3157-3173 (quotient_limb_shape). -/
  limb : ∀ e sh, r.limbShape e = some sh →
    sh.wellFormed = true ∧ shapePtrsU16 sh ∧ ∀ ρ, evalExprρ ρ e = denoteLimbShape ρ sh
  /-- rust: QVM:3190-3227 (quotient_limb_subshape): shape, residue and matched terms,
        with the match non-empty and the shape equal to the sum of what it matched. -/
  limbSub : ∀ e sh res matched, r.limbSubshape e = some (sh, res, matched) →
    matched ≠ [] ∧ sh.wellFormed = true ∧ shapePtrsU16 sh ∧ ∀ ρ,
      evalExprρ ρ e = (denoteLimbShape ρ sh).bind (fun a =>
        (evalExprρ ρ res).map (fun b => qvmFrAdd a b)) ∧
      denoteLimbShape ρ sh = matched.foldlM
        (fun (acc : QVMFr) (m : QuotientExpr) =>
          (evalExprρ ρ m).map (fun b => qvmFrAdd acc b)) 0
  /-- rust: QVM:3231-3238 (quotient_modarith7_shape). -/
  modarith7 : ∀ e sh, r.modarith7Shape e = some sh →
    modarith7WellFormed sh ∧ ∀ ρ, evalExprρ ρ e = denoteModarith7 ρ sh

/-- The conservative bundle is sound: no hook ever fires, so every field is vacuous.
    This is the baseline build the dual-build certifier compares the optimized one
    against (certifyQuotientBuildsAgree). -/
theorem noShapeRecognizers_sound : RecognizersSound noShapeRecognizers := by
  constructor
  · intro e b h
    cases h
  · intro e sh h
    cases h
  · intro e sh res matched h
    cases h
  · intro e sh h
    cases h

/-- Operand widths the builder encodes exactly: tokens are pushed as raw bytes and
    pointers as u32/u16 (pushByte, emitU32 truncates - VmBuilder.lean:306, :348), so
    an expression outside these widths can name a memory the bytes do not denote.
    Survey, QVM area: "state theorems on qvmBytesToNats build.bytes (post-finish),
    never on the builder's s.bytes, or carry this hypothesis". -/
def exprBounded : QuotientExpr → Prop
  | .const _ => True
  | .mem (.literal ptr) => ptr < 2 ^ 32
  | .mem (.token t) => t < 256
  | .mem (.tokenOffset t o) => t < 256 ∧ o < 2 ^ 32
  | .add l r | .mul l r => exprBounded l ∧ exprBounded r
  | .neg e => exprBounded e

/-- The decidable reading of exprBounded. The Prop above has no Decidable instance (it
    is a pattern-matching Prop over Nat bounds and conjunctions), so a Bool gate cannot
    'if' on it; this is the computable twin and the theorem below ties them. -/
def exprBoundedBool : QuotientExpr → Bool
  | .const _ => true
  | .mem (.literal ptr) => ptr < 2 ^ 32
  | .mem (.token t) => t < 256
  | .mem (.tokenOffset t o) => t < 256 && o < 2 ^ 32
  | .add l r | .mul l r => exprBoundedBool l && exprBoundedBool r
  | .neg e => exprBoundedBool e

/-- The two readings agree, so the hypothesis of the compile-correctness theorems can be
    checked by a gate. -/
theorem exprBounded_iff (e : QuotientExpr) : exprBounded e ↔ exprBoundedBool e = true := by
  induction e with
  | const _ => simp [exprBounded, exprBoundedBool]
  | mem m => cases m <;> simp [exprBounded, exprBoundedBool]
  | add l r ihl ihr => simp [exprBounded, exprBoundedBool, ihl, ihr]
  | mul l r ihl ihr => simp [exprBounded, exprBoundedBool, ihl, ihr]
  | neg i ihi => simp [exprBounded, exprBoundedBool, ihi]


/-! ### 4. Per-identity compile correctness (design1 M6-2/M6-3, D-P20 claim 2) -/

/-- D-P20 claim 2, and the per-identity form the plan calls qvm_compile_correct_identity.
    PROOF HOLE (M6-2): the induction is over the emitter's fuel-bounded mutual block
    (VmBuilder.lean:700-894, about 40 panic sites) against the interpreter's step
    function, and needs the four peephole cases (pow5, modarith7, the limb family, the
    run decomposition) discharged under 'hr'. Everything it QUANTIFIES over exists
    today - that is what P-09c and P-09d bought - so this is a PROOF gap, not a
    statement gap, which is exactly what D-P20's addendum says changed.
    The conclusion is existential about the memory (attack.md's FIX): a sound
    recognizer may read a pointer outside leafKeys e, in which case the interpreter's
    derive conses onto the cache and the returned memory differs while the value is
    still right. 'hconsts' is the survey's divergence (1): Yul PUSH_CONST is a raw
    mload while fqFromU256 rejects at ≥ r on both the VM and the expression side. -/
theorem qvm_compile_correct_identity (r : QuotientShapeRecognizers)
    (hr : RecognizersSound r)
    (s₀ s₁ : QuotientProgramBuilder) (e : QuotientExpr) (t : QuotientTarget) (gap : Option Nat)
    (hb : exprBounded e)
    (hemit : identityExpr r s₀ e t gap = .ok s₁)
    (hconsts : ∀ c ∈ s₁.consts, c.toNat < qvmFrModulus)
    (cseg seg : List Nat)
    (hcompact : compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg)
    (hseg : finalizedIdentitySegment cseg = some seg)
    (ρ : Valuation) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity seg s₁.consts (memOfρ ρ (leafKeys e)) =
      .ok (v, mem') ∧ evalExprρ ρ e = .ok v := by
  sorry

/-! ### 5. The plan-items driver and the certifier forms (design1 M6-3) -/

/-- The plan-items driver. quotient.rs:2120
    (build_quotient_program_items_with_limb_ops) is unported, so the driver is defined
    here - survey, QVM area: "must be defined in the theorem file". It mirrors
    QuotientCertifyKats.buildStream but threads the hook bundle r and takes each
    selector identity's gap from the plan's own SelectorFoldPlan. -/
def buildItems (r : QuotientShapeRecognizers) (sf : SelectorFoldPlan) :
    List QuotientProgramItem → QuotientProgramBuilder → M QuotientProgramBuilder
  | [], s => .ok s
  | .identity id :: rest, s => do
      buildItems r sf rest (← identityExpr r s id.expr id.target (sf.gapFor id))
  | .nativePermutation :: rest, s => do buildItems r sf rest (← nativePermutation s)
  | .nativeLookup :: rest, s => do buildItems r sf rest (← nativeLookup s)
  | .nativeIdentity i :: rest, s => do buildItems r sf rest (← nativeIdentity s i)

/-- One driver call plus finish, i.e. the finalized artifact of a whole plan. -/
def buildPlan (r : QuotientShapeRecognizers) (plan : QuotientProgramPlan)
    (s₀ : QuotientProgramBuilder) : M QuotientProgramBuild :=
  buildItems r plan.selectorFold plan.items s₀ >>= finish

/-- The cursor arithmetic of certifyItemWalk, as a function of the finalized bytes:
    after an identity item the walk resumes at exprEnd + len(fold instruction), and
    after a native marker at cursor + len(marker). Where either step errors the walk
    stops, and this stops with it (the cursor it tried is still recorded). Not a Rust
    item: QVC keeps 'cursor' as a loop local. -/
def itemStartsGo (bytes : List Nat) :
    List QuotientProgramItem → Nat → List Nat → List Nat
  | [], _, acc => acc.reverse
  | item :: rest, cursor, acc =>
      match item with
      | .identity _ =>
          match identitySegment bytes cursor with
          | .ok (exprEnd, _) =>
              match Midfall.Generator.QuotientBuilder.quotientOpLen bytes exprEnd with
              | .ok len => itemStartsGo bytes rest (exprEnd + len) (cursor :: acc)
              | .error _ => (cursor :: acc).reverse
          | .error _ => (cursor :: acc).reverse
      | _ =>
          match Midfall.Generator.QuotientBuilder.quotientOpLen bytes cursor with
          | .ok len => itemStartsGo bytes rest (cursor + len) (cursor :: acc)
          | .error _ => (cursor :: acc).reverse

/-- The cursors certifyItemWalk visits, defined from quotientOpLen as design1 M6-3's
    FIX line promises (the plan sketches it as an undefined name). Gated against the
    real walk by itemStarts_matchesCertifierWalk_ok. -/
def itemStarts (plan : QuotientProgramPlan) (build : QuotientProgramBuild) : List Nat :=
  itemStartsGo (qvmBytesToNats build.bytes) plan.items 0 []

/-- Form (a): the certifier's own walk succeeds on every cache-consistent memory and
    consumes the whole stream, which is what makes certifyQuotientProgram succeed for
    every VK payload. PROOF HOLE (M6-3): induction over plan.items with the cursor
    arithmetic of itemStarts and qvm_compile_correct_identity at each step. The memory
    is threaded through BOTH sides of the comparison (VmCertify.lean:499-533), which is
    why only the end cursor is concluded about and no returned memory is ever equated
    (attack.md's rule, and the survey's "compare VALUES only"). -/
theorem qvm_compile_correct_certifier (r : QuotientShapeRecognizers)
    (hr : RecognizersSound r) (plan : QuotientProgramPlan) (limbOps : Bool)
    (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
    (mem : QuotientRefMemory) (hcc : CacheConsistent mem) :
    ∃ mem', certifyItemWalk plan build (qvmBytesToNats build.bytes) mem =
      .ok ((qvmBytesToNats build.bytes).length, mem') := by
  sorry

/-- The whole certifier entry point: form (a) plus the trailing-byte check
    (VmCertify.lean:590-605). PROOF HOLE: qvm_compile_correct_certifier plus the seed
    unfolding; the seed is irrelevant to a ∀ρ theorem, which is the point of the
    valuation layer - the Rust samples ONE Schwartz-Zippel challenge (VmCertify's
    header hazard 4) and this statement is strictly stronger. -/
theorem qvm_compile_correct_program (r : QuotientShapeRecognizers)
    (hr : RecognizersSound r) (plan : QuotientProgramPlan) (limbOps : Bool)
    (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
    (vk : Midfall.Generator.Halo2VerifyingKey) :
    certifyQuotientProgram plan build vk = .ok () := by
  sorry

/-! ### 6. Hazard 5: the no-OOB statement against the REAL validator predicate -/

/-- D-P20 item 2 restated over the two real fault classes, and - answering hazard 5 -
    stated against the validator that EXISTS rather than an abstract stand-in.
    PLAN's '.oob' cannot arise: certifier memory is a PRNG over the whole u32 space,
    so every read succeeds; the only out-of-range faults are past the end of the
    PROGRAM bytes and past the end of the CONSTANT TABLE (VmReference.lean:284-296).
    The design sketched this over an abstract 'validate' field because P-09e could not
    build a QuotientOperandModel from a plan. That is stale: P-09e landed
    validateQuotientProgramOperands and P-11 landed quotientOperandModel plus
    LoweringPlan.supportedQvm, so the hypothesis below IS PLAN 9.5's Supported.qvm.
    hvm IS LOAD-BEARING, and it is a defect found in THIS statement while writing it (the
    sixth such, in the pattern the brief predicted): LoweringPlan.supportedQvmBool answers
    TRUE for a Direct plan without looking at the quotient field at all
    (LoweringPlan.lean:716-718), so with L.lowering = .direct and a hand-built
    L.quotient = some q every hypothesis was satisfiable while the conclusion is refuted by
    q.build = [PUSH_CONST 0xff 0xff] over an empty table. The reference's own invariant
    (PL:434-437, exactly one of quotient/direct is some) is not carried by the Lean type,
    so the arm has to be pinned in the statement. validator_noOOB_onTheRealPlan_ok pins
    that the fixture really is the VM arm.
    PROOF HOLE (M6/M7): VmValidator's header states the two-phase soundness argument
    informally ("phase 1's byte span covers every offset the walker reads"); it has not
    been written as an induction over quotientBytecodeOps. -/
theorem qvm_validated_noBoundsFault {Program Layout : Type}
    (model : QuotientOperandModel)
    (L : Midfall.Generator.LoweringPlan Program Layout)
    (hvm : L.lowering = Midfall.Generator.QuotientLowering.vm)
    (q : Midfall.Generator.PlannedQuotient) (hq : L.quotient = some q)
    (hmodel : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
      q.build q.plan.selectorFold = .ok model)
    (hvalidated : Midfall.Generator.LoweringPlan.supportedQvm L)
    (hconsts : ∀ c ∈ q.build.consts, c.toNat < qvmFrModulus)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts q.plan q.build)
    (hseg : identitySegment (qvmBytesToNats q.build.bytes) cursor = .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory) (f : QVMFault)
    (hf : Midfall.Generator.evalQuotientIdentity
        (((qvmBytesToNats q.build.bytes).drop cursor).take (exprEnd - cursor))
        q.build.consts mem = .error f) :
    f ≠ QVMFault.readPastEnd exprEnd ∧
      (∀ slot idx, f ≠ QVMFault.constSlotOutOfRange slot idx) := by
  sorry

/-- The instruction list of a finalized program, or the empty list where phase 1 errors.
    Modelling scaffolding, not a Rust item. -/
def bytecodeOpList (bytes : List Nat) : List (Nat × Nat) :=
  match quotientBytecodeOps bytes with
  | .ok ops => ops.map fun (idx, op, _len) => (idx, op)
  | .error _ => []

/-- The operand list of one instruction, or the empty list where the walker errors.
    Modelling scaffolding, not a Rust item: QVM's phase 2 aborts on the first bad
    operand, so a statement about "every operand" needs the total reading. -/
def operandList (bytes : List Nat) (idx op : Nat) : List QuotientOperand :=
  match visitQuotientOperands bytes idx op with
  | .ok operands => operands
  | .error _ => []

/-- The window half of hazard 5, in the form D-P20 item 2's resolution asks for: a
    LAYOUT property, quantified over the read model rather than over a memory object
    and not as an interpreter fault. Every memory operand a validated program reads
    resolves to an address some declared window contains. PROOF HOLE: this is close to
    what checkQuotientMemOperand already enforces (VmValidator.lean:1119-1137), so the
    argument is an induction over the operand walk; it is not written. -/
theorem qvm_validated_windows {Program Layout : Type}
    (model : QuotientOperandModel)
    (L : Midfall.Generator.LoweringPlan Program Layout)
    (hvm : L.lowering = Midfall.Generator.QuotientLowering.vm)
    (q : Midfall.Generator.PlannedQuotient) (hq : L.quotient = some q)
    (hmodel : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
      q.build q.plan.selectorFold = .ok model)
    (hvalidated : Midfall.Generator.LoweringPlan.supportedQvm L) :
    ∀ (idx op : Nat),
      (idx, op) ∈ bytecodeOpList (Midfall.Generator.bytesToList q.build.bytes) →
      ∀ operand ∈ operandList (Midfall.Generator.bytesToList q.build.bytes) idx op,
        match operand with
        | QuotientOperand.mem _ ptr => model.read.windowFor ptr ≠ none
        | QuotientOperand.token t off =>
            match model.read.tokenBase t with
            | none => True
            | some base => model.read.windowFor (base + off) ≠ none
        | _ => True := by
  sorry

/-- The builder-side totality statement (design1's builder_segments_total): a segment
    of a builder-produced program never faults at all - so in particular never
    readPastEnd or constSlotOutOfRange - on every memory, when the constants are
    canonical. PROOF HOLE (M6-3): qvm_compile_correct_identity at
    ρ := fun d a => deriveReferenceMemory mem.seed d a, plus the fuel-adequacy lemmas
    the survey lists as owed (evalQuotientIdentityLoop.go never exhausts its fuel). -/
theorem builder_segments_total (r : QuotientShapeRecognizers) (hr : RecognizersSound r)
    (plan : QuotientProgramPlan) (limbOps : Bool) (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts plan build)
    (hseg : identitySegment (qvmBytesToNats build.bytes) cursor = .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity
      (((qvmBytesToNats build.bytes).drop cursor).take (exprEnd - cursor)) build.consts mem
      = .ok (v, mem') := by
  sorry

end Midfall.Lowering



/-! ====================================================================
    ## Known-answer tests
    ====================================================================

    R-41: every gate below was RUN, and the failures to redden are reported in the
    package report with their causes. HAZARD 2 (R-55): every gate runs at the REAL
    modulus - either QVMFr arithmetic at qvmFrModulus or Fr Midfall.Assumptions.r -
    because a small field makes the width and truncation checks collapse.
    Except has no BEq in this Lean (survey, QVM area: "QuotientExpr, QuotientMem,
    QuotientTarget, QVMFault derive BEq only"), so the comparisons go through okVal /
    okMemVal rather than the equality operator. -/

namespace Midfall.Lowering.QvmKats

open Midfall Midfall.Generator Midfall.Generator.QuotientBuilder
  Midfall.Generator.QuotientCertify Midfall.Generator.QuotientValidator
  Midfall.Lowering

/-- Comparing an Except QVMFault QVMFr without a BEq instance. Not a Rust item. -/
def okVal (x : Except QVMFault QVMFr) (v : QVMFr) : Bool :=
  match x with
  | .ok w => w == v
  | .error _ => false

/-- The same for the interpreter's pair return, comparing BOTH components (the memory
    has BEq, so the "memory unchanged" half is checkable). -/
def okMemVal (x : Except QVMFault (QVMFr × QuotientRefMemory)) (v : QVMFr)
    (m : QuotientRefMemory) : Bool :=
  match x with
  | .ok (w, m') => w == v && m' == m
  | .error _ => false

/-- Except has no BEq here, so the pair-returning comparison is spelled out. -/
def samePair (x y : Except QVMFault (QVMFr × QuotientRefMemory)) : Bool :=
  match x, y with
  | .ok (a, m), .ok (b, n) => a == b && m == n
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

/-- GATE 1 (bridge, non-vacuity). The two literals agree, and each of the two
    one-digit perturbations disagrees - so qvmFrModulus_eq_r is a fact about these
    digits and not a coincidence of notation. -/
def qvmFrBridge_modulusLiterals_ok : Bool :=
  qvmFrModulus == Midfall.Assumptions.r &&
    (qvmFrModulus + 1) != Midfall.Assumptions.r &&
    (qvmFrModulus - 1) != Midfall.Assumptions.r &&
    qvmFrModulus > 2 ^ 254 && qvmFrModulus < 2 ^ 255
#eval qvmFrBridge_modulusLiterals_ok -- expect true

/-- GATE 2 (bridge). The four proved homomorphism facts re-checked numerically at the
    real modulus on values that straddle it: 0, 1, m-1, m-2 and a 254-bit value. The
    injectivity arm is checked BOTH ways, so a cast that wrapped everything to 0 would
    not pass. -/
def qvmToFr_homOnFixtures_ok : Bool :=
  let vals : List (QVMFr × QVMFr) :=
    [(0, 1), (1, 1), (2, 3), (qvmFrModulus - 1, qvmFrModulus - 1),
     (qvmFrModulus - 1, 1), (2 ^ 254, 2 ^ 128 + 7),
     (qvmFrModulus - 2, qvmFrModulus - 3)]
  vals.all fun (a, b) =>
    (qvmToFr (qvmFrAdd a b) == qvmToFr a + qvmToFr b) &&
    (qvmToFr (qvmFrMul a b) == qvmToFr a * qvmToFr b) &&
    (a < qvmFrModulus → qvmToFr (qvmFrNeg a) == - qvmToFr a) &&
    ((qvmToFr a == qvmToFr b) == (a == b))
#eval qvmToFr_homOnFixtures_ok -- expect true

/-- GATE 3 (bridge, non-vacuity of the canonicity hypotheses). At a = m+1 the VM's
    truncated subtraction gives qvmFrNeg a = 0 while the field gives -1, so the
    hypothesis of qvmToFr_neg is doing work; and qvmToFr m = qvmToFr 0 with m ≠ 0 is
    the injectivity witness. -/
def qvmToFr_needsCanonicity_ok : Bool :=
  qvmToFr qvmFrModulus == qvmToFr 0 && qvmFrModulus != 0 &&
    qvmToFr (qvmFrNeg (qvmFrModulus + 1)) != - qvmToFr (qvmFrModulus + 1)
#eval qvmToFr_needsCanonicity_ok -- expect true

/-- GATE 4 (valuation layer). The token-0xff wrap the survey's evidence line names.
    Note WHERE the wrap is observable: deriveReferenceMemory reduces the domain itself
    (VmReference.lean:395-400), so a PRNG valuation cannot see the difference - what
    makes the reduction load-bearing is a general ρ, where ρ 256 0 and ρ 0 0 differ and
    only the reduced key hits the cache memOfρ builds. -/
def valuation_tokenWrapIsLoadBearing_ok : Bool :=
  memKey (QuotientMem.token 255) == (0, 0) &&
    (let ρ : Valuation := fun d a => if d == 256 then 7 else if d == 0 && a == 0 then 11 else 0
     okVal (evalExprρ ρ (QuotientExpr.mem (QuotientMem.token 255))) 11 &&
       ρ 256 0 != ρ 0 0 &&
       okMemVal (evalQuotientExpr (QuotientExpr.mem (QuotientMem.token 255))
         (memOfρ ρ [memKey (QuotientMem.token 255)])) 11
         (memOfρ ρ [memKey (QuotientMem.token 255)]))
#eval valuation_tokenWrapIsLoadBearing_ok -- expect true

/-- GATE 5 (valuation layer). The PROVED theorem evalQuotientExpr_memOfρ exercised on
    a fixture set covering every constructor of QuotientExpr and every arm of
    QuotientMem, with ρ the PRNG the interpreter itself would use. A wrongly stated
    theorem (wrong key reduction, wrong domain) fails here. -/
def valuation_agreesWithInterpreterOnFixtures_ok : Bool :=
  let seed := qvmBytesOfNats (List.range 32)
  let ρ : Valuation := fun d a => deriveReferenceMemory seed d a
  let lit (p : Nat) : QuotientExpr := QuotientExpr.mem (QuotientMem.literal p)
  let exprs : List QuotientExpr :=
    [QuotientExpr.const (BitVec.ofNat 256 0xdeadbeef),
     QuotientExpr.const (BitVec.ofNat 256 (qvmFrModulus - 1)),
     lit 0x100, lit 0,
     QuotientExpr.mem (QuotientMem.token qMemX),
     QuotientExpr.mem (QuotientMem.tokenOffset qMemL0 0x20),
     QuotientExpr.mem (QuotientMem.token 255),
     QuotientExpr.add (lit 0x100) (lit 0x120),
     QuotientExpr.mul (lit 0x140) (QuotientExpr.const 7),
     QuotientExpr.neg (QuotientExpr.add (lit 0x100) (QuotientExpr.const 3)),
     QuotientExpr.add (QuotientExpr.mul (lit 0x100) (lit 0x120))
       (QuotientExpr.neg (QuotientExpr.mem (QuotientMem.token 255)))]
  exprs.all fun e =>
    let want : Except QVMFault (QVMFr × QuotientRefMemory) :=
      match evalExprρ ρ e with
      | .ok v => .ok (v, memOfρ ρ (leafKeys e))
      | .error f => .error f
    samePair (evalQuotientExpr e (memOfρ ρ (leafKeys e))) want
#eval valuation_agreesWithInterpreterOnFixtures_ok -- expect true

/-- GATE 6 (valuation layer, non-vacuity). Dropping one leaf key from S makes the
    interpreter derive instead of hitting the cache, and the equation fails - so the
    hypothesis of evalQuotientExpr_memOfρ is load-bearing, not decoration. -/
def valuation_missingLeafBreaksAgreement_ok : Bool :=
  let seed := qvmBytesOfNats (List.range 32)
  let ρ : Valuation := fun d a => deriveReferenceMemory seed d a
  let e := QuotientExpr.add (QuotientExpr.mem (QuotientMem.literal 0x100))
    (QuotientExpr.mem (QuotientMem.literal 0x120))
  let missing : List (Nat × Nat) := [memKey (QuotientMem.literal 0x100)]
  let want : Except QVMFault (QVMFr × QuotientRefMemory) :=
    match evalExprρ ρ e with
    | .ok v => .ok (v, memOfρ ρ missing)
    | .error f => .error f
  !samePair (evalQuotientExpr e (memOfρ ρ missing)) want
#eval valuation_missingLeafBreaksAgreement_ok -- expect true

/-- GATE 7 (denotations, design1 M6-1's evidence). Each limb shape is emitted by the
    BUILDER, run by the INTERPRETER, and compared against the denotation written here.
    All three variants are covered, and the fixtures have distinct coefficients and
    distinct pointers, so a swapped (slot, ptr) order or a misread stride changes the
    value. -/
def denoteLimbShape_matchesByteDecoder_ok : Bool :=
  let seed := qvmBytesOfNats (List.range 32)
  let ρ : Valuation := fun d a => deriveReferenceMemory seed d a
  let mem := quotientRefMemoryNew seed
  let shapes : List QuotientLimbShape :=
    [Midfall.Generator.QuotientVmKats.lin7Fixture,
     Midfall.Generator.QuotientVmKats.bilin7RowFixture,
     Midfall.Generator.QuotientVmKats.bilin7PairwiseFixture]
  shapes.all fun sh =>
    match emitLimbShape builderDefault sh with
    | .ok s =>
        match evalQuotientIdentity s.bytes s.consts mem with
        | .ok (v, _) => okVal (denoteLimbShape ρ sh) v
        | .error _ => false
    | .error _ => false
#eval denoteLimbShape_matchesByteDecoder_ok -- expect true

/-- GATE 8 (denotations). The MODARITH7 denotation against the MODARITH7 byte decoder,
    on a shape with a FULL 7-term lin block, a full 7-term row block, the 13-coefficient
    pairwise block, one mem term and one product term - the operand order VmReference
    warns about at QVR:488-490 is observable here because every coefficient and pointer
    is distinct. (QuotientVmKats.modarith7Fixture cannot be used: it is a field census
    with ONE term per block, and the byte decoder always reads 7, so the emitted
    program faults readPastEnd. Recorded as a finding.) -/
def denoteModarith7_matchesByteDecoder_ok : Bool :=
  let seed := qvmBytesOfNats (List.range 32)
  let ρ : Valuation := fun d a => deriveReferenceMemory seed d a
  let mem := quotientRefMemoryNew seed
  let coeffs : List Word256 :=
    (List.range quotientVmPairwiseCoeffs).map fun k => BitVec.ofNat 256 (k + 2)
  let sh : QuotientModarith7Shape :=
    { cond := some 0x200
      constant := BitVec.ofNat 256 1
      lin := [Midfall.Generator.QuotientVmKats.lin7FixtureTerms]
      rows := [(0x200, Midfall.Generator.QuotientVmKats.lin7FixtureTerms)]
      pairwise := [(0x100, 0x200, coeffs)]
      memTerms := [(BitVec.ofNat 256 5, 0x140)]
      productTerms := [(BitVec.ofNat 256 6, 0x160, 0x180)] }
  match emitModarith7Shape builderDefault sh with
  | .ok s =>
      match evalQuotientIdentity s.bytes s.consts mem with
      | .ok (v, _) => okVal (denoteModarith7 ρ sh) v
      | .error _ => false
  | .error _ => false
#eval denoteModarith7_matchesByteDecoder_ok -- expect true

/-- GATE 9 (denotations, non-vacuity). With a valuation that reads the pointer back as
    its value, two shapes differing only in a mem-term POINTER denote different values
    - so the denotation is not ignoring the operand order it claims to follow. -/
def denoteModarith7_operandOrderIsObservable_ok : Bool :=
  let ρ : Valuation := fun _ a => a
  let base : QuotientModarith7Shape :=
    { cond := none, constant := 0, lin := [], rows := [], pairwise := [],
      memTerms := [(BitVec.ofNat 256 5, 0x140)], productTerms := [] }
  let swapped : QuotientModarith7Shape :=
    { base with memTerms := [(BitVec.ofNat 256 5, 0x160)] }
  okVal (denoteModarith7 ρ base) (5 * 0x140) && okVal (denoteModarith7 ρ swapped) (5 * 0x160)
#eval denoteModarith7_operandOrderIsObservable_ok -- expect true

/-- GATE 10 (RecognizersSound, non-vacuity). A hook bundle that claims every
    expression is a fifth power is NOT sound: at v = 3 the pow5 law demands 3 = 243.
    This is the gate for "compile correctness is false for arbitrary hooks". -/
def recognizersSound_pow5ArmIsLoadBearing_ok : Bool :=
  let bad : QuotientShapeRecognizers := { noShapeRecognizers with pow5Base := fun e => some e }
  let e := QuotientExpr.mem (QuotientMem.literal 0x100)
  let ρ : Valuation := fun _ _ => 3
  let v : QVMFr := 3
  let v5 := qvmFrMul v (qvmFrMul (qvmFrMul v v) (qvmFrMul v v))
  bad.pow5Base e == some e && okVal (evalExprρ ρ e) v && v5 != v && v5 == 243
#eval recognizersSound_pow5ArmIsLoadBearing_ok -- expect true

/-- GATE 11 (exprBounded). The widths the builder encodes exactly, at the boundary:
    token 255 in / 256 out, pointer 2^32-1 in / 2^32 out, and the conjunction arms.
    Checked through the decidable twin exprBoundedBool, which exprBounded_iff ties to
    the Prop the theorems assume. -/
def exprBounded_widths_ok : Bool :=
  exprBoundedBool (QuotientExpr.mem (QuotientMem.token 255)) &&
    !exprBoundedBool (QuotientExpr.mem (QuotientMem.token 256)) &&
    exprBoundedBool (QuotientExpr.mem (QuotientMem.literal (2 ^ 32 - 1))) &&
    !exprBoundedBool (QuotientExpr.mem (QuotientMem.literal (2 ^ 32))) &&
    exprBoundedBool (QuotientExpr.neg (QuotientExpr.mem (QuotientMem.tokenOffset 3 (2 ^ 32 - 1)))) &&
    !exprBoundedBool (QuotientExpr.add (QuotientExpr.mem (QuotientMem.literal 0))
      (QuotientExpr.mem (QuotientMem.token 256))) &&
    exprBoundedBool (QuotientExpr.const (BitVec.ofNat 256 (qvmFrModulus + 9)))
#eval exprBounded_widths_ok -- expect true

/-- GATE 12 (itemStarts). The new cursor walk agrees with the real certifier walk on
    the three-identity fixture: one start per item, all inside the program, and the
    walk ends exactly at the program end. -/
def itemStarts_matchesCertifierWalk_ok : Bool :=
  match Midfall.Generator.QuotientCertifyKats.threeIdentityBuild with
  | .ok build =>
      let plan := Midfall.Generator.QuotientCertifyKats.threeIdentityPlan
      let bytes := qvmBytesToNats build.bytes
      let starts := itemStarts plan build
      match certifyItemWalk plan build bytes (quotientRefMemoryNew (qvmBytesOfNats (List.range 32))) with
      | .ok (endCursor, _) =>
          starts.length == plan.items.length &&
            starts.head? == some 0 &&
            (starts.all fun c => c < bytes.length) &&
            endCursor == bytes.length
      | .error _ => false
  | .error _ => false
#eval itemStarts_matchesCertifierWalk_ok -- expect true

/-- GATE 13 (hazard 5). The REAL predicate on the REAL plan: P-11's VM fixture is
    supportedQvm, and every segment its itemStarts names evaluates without fault on a
    fresh certifier memory. This is the computational instance of
    qvm_validated_noBoundsFault, stated against validateQuotientProgramOperands and not
    against a stand-in. -/
def validator_noOOB_onTheRealPlan_ok : Bool :=
  let L := Midfall.Generator.LoweringPlanKats.planVM
  match L.quotient with
  | none => false
  | some q =>
      L.lowering == Midfall.Generator.QuotientLowering.vm &&
        L.supportedQvmBool &&
        (itemStarts q.plan q.build).all fun cursor =>
          match identitySegment (qvmBytesToNats q.build.bytes) cursor with
          | .ok (exprEnd, _) =>
              (Midfall.Generator.evalQuotientIdentity
                  (((qvmBytesToNats q.build.bytes).drop cursor).take (exprEnd - cursor))
                  q.build.consts (quotientRefMemoryNew (qvmBytesOfNats (List.range 32)))).isOk
          | .error _ => true
#eval validator_noOOB_onTheRealPlan_ok -- expect true

/-- GATE 14 (hazard 5, non-vacuity). Totality is not automatic: the hand-built program
    [PUSH_CONST 0xff 0xff] faults constSlotOutOfRange on an empty table, and a
    truncated PUSH_MEM_LITERAL faults readPastEnd. These are the two classes
    qvm_validated_noBoundsFault excludes through the validator, so a statement that
    excluded nothing would pass them too. -/
def validator_noOOB_isNotAutomatic_ok : Bool :=
  (match Midfall.Generator.evalQuotientIdentity [qOpPushConst, 0xff, 0xff] []
      (quotientRefMemoryNew Midfall.Bytes.empty) with
   | .error (QVMFault.constSlotOutOfRange 65535 0) => true
   | _ => false) &&
    (match Midfall.Generator.evalQuotientIdentity [qOpPushMemLiteral, 0, 0] []
        (quotientRefMemoryNew Midfall.Bytes.empty) with
     | .error (QVMFault.readPastEnd 3) => true
     | _ => false)
#eval validator_noOOB_isNotAutomatic_ok -- expect true

/-- GATE 15 (CacheConsistent). A fresh memory satisfies the invariant and so does every
    memory the interpreter produces from one - what the certifier forms assume. A
    memOfρ built from a NON-deriving ρ does not, which keeps the two uses apart. -/
def cacheConsistent_freshAndDerived_ok : Bool :=
  let seed := qvmBytesOfNats (List.range 32)
  let fresh := quotientRefMemoryNew seed
  fresh.cache.isEmpty &&
    (match evalQuotientExpr (QuotientExpr.add
        (QuotientExpr.mem (QuotientMem.literal 0x100))
        (QuotientExpr.mem (QuotientMem.token 255))) fresh with
     | .ok (_, mem') =>
         mem'.cache.length == 2 &&
           (mem'.cache.all fun (d, a, v) =>
             v == deriveReferenceMemory seed d a && d < 256 && a < 2 ^ 32)
     | .error _ => false) &&
    (let ρ : Valuation := fun _ _ => 7
     !(List.all (memOfρ ρ [(0, 0x100)]).cache fun (_, _, v) =>
        v == deriveReferenceMemory Midfall.Bytes.empty 0 0x100))
#eval cacheConsistent_freshAndDerived_ok -- expect true

end Midfall.Lowering.QvmKats


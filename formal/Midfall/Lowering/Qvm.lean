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
    been written as an induction over quotientBytecodeOps.

    RESTORED TO THE SKETCH'S STRENGTH BY P-QVM (docs/REVIEW.md R-69). The committed conclusion
    read 'f ≠ QVMFault.readPastEnd exprEnd', which excludes ONE index, while the plan's own
    sketch (P-SE-semantic-equivalence.md:2271) excludes EVERY readPastEnd - 'match f with
    | .readPastEnd _ => False | .constSlotOutOfRange _ _ => False | _ => True'. The second
    conjunct had already been written universally ('∀ slot idx, ...'), so the narrowing was
    asymmetric and silent: drift, not a decision, and the standing instruction is to restore the
    stronger original rather than keep a weaker committed form. The conclusion below is therefore
    the sketched one. What that costs, named precisely: the proof now needs "the interpreter never
    runs past the end of its own segment", i.e. the per-opcode agreement between
    evalQuotientIdentityStep's 'consumed' field and the validator's quotientOpLen across all
    ~25 opcode arms, plus the loop induction over the fuel-bounded walk. That is a package of its
    own; the hole stays open at the restored strength rather than being closed at the weak one.

    RELOCATED DOWNSTREAM BY CARD RELOC. The conclusion is now the sorry-free 'def QvmNoBoundsFault'
    below - DECLARED EXACTLY ONCE, here, where every module can see it - and the ROW that proves it
    moved to 'Midfall/Lowering/QvmNoBounds.lean', which imports 'QvmShift' and 'QvmWalk'. WHY: all
    three per-arm families this hole needs (the read bound, the width agreement, the const-slot
    correspondence) live in those two files, and both of them IMPORT this one, so no proof of this
    statement could be written where it stood. Nothing about the claim changed:
    'qvmNoBoundsFault_conj' below PROVES the def is exactly the two-conjunct conclusion above.
    WHAT STILL STANDS BETWEEN THE ROW AND A PROOF is named at the moved row: the loop inversion this
    doc asks for is now PROVED there ('qvmNoBounds_stepErrorIsReachable'), so what is left is the
    two-phase validator induction this comment has always named as unwritten, tying 'hvalidated' from
    the whole program bytes to one cursor of the segment, plus MODARITH7 on the three per-arm families.
    -/
def QvmNoBoundsFault (f : QVMFault) : Prop :=
  (∀ i, f ≠ QVMFault.readPastEnd i) ∧
    (∀ slot idx, f ≠ QVMFault.constSlotOutOfRange slot idx)

/-- **THE DEF IS THE COMMITTED CONCLUSION, NOT A WEAKER ONE - PROVED.** 'Iff.rfl' closes this only
    because the two propositions are the same up to the def's own equation, so the relocation to a
    named 'def : Prop' cannot have dropped a conjunct, narrowed a quantifier or lost a fault class:
    if the def ever stopped saying exactly the committed pair, this line would stop elaborating. -/
theorem qvmNoBoundsFault_conj (f : QVMFault) :
    QvmNoBoundsFault f ↔
      (∀ i, f ≠ QVMFault.readPastEnd i) ∧
        (∀ slot idx, f ≠ QVMFault.constSlotOutOfRange slot idx) :=
  Iff.rfl

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

/-! #### Proof machinery for the window half -/

/-- A successful monadic bind has a successful left action and a successful continuation on
    its result. The validator's checks are written in 'do' notation, whose statements are
    binds, so reading a check back from its own success needs this: 'h : x >>= k = .ok b'
    is the only shape the port's 'Except' blocks present, and Lean has no core lemma of
    this form ('Except.bind_eq_ok_iff' does not exist in v4.35.0 - measured). -/
theorem peel_bind {α β ε : Type} {x : Except ε α} {k : α → Except ε β} {b : β}
    (h : (x >>= k) = .ok b) : ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => cases h

/-- 'forEachM' succeeds exactly when every element's action succeeds. QVM's phase-2 loop is
    a Rust 'for' with '?' inside, ported as 'forEachM', so "every operand was checked" and
    "the check succeeded" are the same fact only under this lemma. -/
theorem forEachM_ok_iff {ε α : Type} (xs : List α) (f : α → Except ε Unit) :
    forEachM xs f = .ok () ↔ ∀ x ∈ xs, f x = .ok () := by
  constructor
  · induction xs with
    | nil => intro _ _ hx; cases hx
    | cons y rest ih =>
        intro h z hz
        have h1 : forEachM (y :: rest) f = (f y >>= fun _ => forEachM rest f) := rfl
        rw [h1] at h
        rcases List.mem_cons.mp hz with hz | hz
        · subst hz
          obtain ⟨a, ha, _⟩ := peel_bind h
          cases a
          exact ha
        · obtain ⟨_, _, hrest⟩ := peel_bind h
          exact ih hrest z hz
  · intro h
    induction xs with
    | nil => rfl
    | cons y rest ih =>
        have h1 : forEachM (y :: rest) f = (f y >>= fun _ => forEachM rest f) := rfl
        rw [h1, h y (by simp)]
        show (Except.ok () >>= fun _ => forEachM rest f) = .ok ()
        rw [show (Except.ok () >>= fun _ => forEachM rest f) = forEachM rest f from rfl]
        exact ih (fun x hx => h x (by simp [hx]))

/-- What 'validateQuotientProgramOperands' actually bought: the phase-1 walk succeeded, and
    every operand of every instruction it named passed 'checkQuotientOperand'. The two
    "total reading" scaffolds above ('bytecodeOpList', 'operandList') are what make this
    statement writable at all - phase 2 aborts on the first bad operand, so without the
    total reading there is no "every operand" to quantify over. -/
theorem operands_ok_of_validated {bytes : List Nat} {model : QuotientOperandModel}
    (h : validateQuotientProgramOperands bytes model = .ok ()) :
    ∃ ops, quotientBytecodeOps bytes = .ok ops ∧
      ∀ p ∈ ops.map (fun (idx, op, _len) => (idx, op)),
        ∀ operand ∈ operandList bytes p.1 p.2, checkQuotientOperand model p.1 operand = .ok () := by
  unfold validateQuotientProgramOperands at h
  obtain ⟨_, _, h1⟩ := peel_bind h
  obtain ⟨maxStack, _, h2⟩ := peel_bind h1
  by_cases hgt : maxStack > model.stackWords
  · simp only [if_pos hgt] at h2
    cases h2
  · simp only [if_neg hgt] at h2
    obtain ⟨_, _, h3⟩ := peel_bind h2
    obtain ⟨ops, ho, h4⟩ := peel_bind h3
    have hf := (forEachM_ok_iff (ops.map fun (idx, op, _len) => (idx, op))
        (fun x => match x with
          | (idx, op) => do
              let operands ← visitQuotientOperands bytes idx op
              forEachM operands (checkQuotientOperand model idx))).mp h4
    refine ⟨ops, ho, ?_⟩
    intro p hp
    have h5 := hf p hp
    obtain ⟨operands, hv', h6⟩ := peel_bind h5
    have hlist : operandList bytes p.1 p.2 = operands := by
      simp [operandList, hv']
    rw [hlist]
    exact (forEachM_ok_iff operands (checkQuotientOperand model p.1)).mp h6

/-- A literal memory operand that passed the check has a window: 'checkQuotientMemOperand'
    ends with exactly the test 'windowFor ptr == none', so a successful check cannot name a
    pointer outside every window. The reduction of the ported 'do' block is spelled out as
    'hred' because 'simp' will not unfold these definitions (measured: 'simp only
    [checkQuotientMemOperand]' reports no progress); 'unfold' plus 'rfl' does reduce it. -/
theorem windowFor_mem_ok {model : QuotientOperandModel} {idx : Nat} {kind : String} {ptr : Nat}
    (h : checkQuotientOperand model idx (QuotientOperand.mem kind ptr) = .ok ()) :
    model.read.windowFor ptr ≠ none := by
  have hred : checkQuotientOperand model idx (QuotientOperand.mem kind ptr) =
      (if (ptr % wordBytes != 0) = true then
          .error (QuotientValidationFault.pointerMisaligned kind ptr idx)
        else
          if (model.read.windowFor ptr == none) = true then
              .error (QuotientValidationFault.pointerOutsideWindows kind ptr idx
                (describeReadWindows model.read))
          else .ok ()) := by
    unfold checkQuotientOperand checkQuotientMemOperand
    rfl
  by_cases hc : (model.read.windowFor ptr == none) = true
  · refine absurd h ?_
    intro hh
    rw [hred, hc] at hh
    by_cases hd : (ptr % wordBytes != 0) = true
    · rw [if_pos hd] at hh; cases hh
    · rw [if_neg hd] at hh; cases hh
  · exact fun con => hc (by simp [con])

/-- The token twin. The offset-overflow leg is a separate fault from the window leg and both
    are errors, so the proof only needs "some fault", not a named one - which is why this
    destructs the hypothesis rather than computing a right-hand side. -/
theorem windowFor_token_window {model : QuotientOperandModel} {idx t off base : Nat}
    (h : checkQuotientOperand model idx (QuotientOperand.token t off) = .ok ())
    (hb : model.read.tokenBase t = some base) :
    model.read.windowFor (base + off) ≠ none := by
  intro con
  refine absurd h ?_
  intro hh
  have hc : (model.read.windowFor (base + off) == none) = true := by simp [con]
  unfold checkQuotientOperand checkQuotientMemOperand at hh
  simp only [bind, Except.bind] at hh
  rw [hb] at hh
  simp only [bind, Except.bind] at hh
  by_cases hd : base + off < base
  · rw [if_pos hd] at hh; cases hh
  · rw [if_neg hd] at hh
    by_cases halign : ((base + off) % wordBytes != 0) = true
    · rw [if_pos halign] at hh; cases hh
    · rw [if_neg halign, hc] at hh; cases hh


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
  have hsup : L.supportedQvmBool = true := hvalidated
  have hsb : L.supportedQvmBool =
      match L.quotient with
      | none => false
      | some q =>
          match Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
              q.build q.plan.selectorFold with
          | .error _ => false
          | .ok model =>
              match validateQuotientProgramOperands (bytesToList q.build.bytes) model with
              | .ok _ => true
              | .error _ => false := by
    unfold LoweringPlan.supportedQvmBool
    rw [hvm]
    rfl
  rw [hsb] at hsup
  rw [hq] at hsup
  dsimp only at hsup
  rw [hmodel] at hsup
  cases hx : validateQuotientProgramOperands (bytesToList q.build.bytes) model with
  | ok u =>
      cases u
      obtain ⟨ops, ho, hall⟩ := operands_ok_of_validated hx
      intro idx op hop operand hopd
      have hlist : bytecodeOpList (bytesToList q.build.bytes) =
          ops.map fun (idx, op, _len) => (idx, op) := by
        simp [bytecodeOpList, ho]
      rw [hlist] at hop
      have hok := hall (idx, op) hop operand hopd
      cases operand with
      | mem kind ptr => exact windowFor_mem_ok hok
      | token t off =>
          by_cases hb : model.read.tokenBase t = none
          · simp only [hb]
          · obtain ⟨base, hbase⟩ : ∃ base, model.read.tokenBase t = some base := by
              cases m : model.read.tokenBase t with
              | none => exact absurd m hb
              | some base => exact ⟨base, rfl⟩
            simp only [hbase]
            exact windowFor_token_window hok hbase
      | _ => trivial
  | error f => simp [hx] at hsup


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


/-! ### 7. The arms agreement: the interpreter's consumed vs the validator's width -/

/-- THE ARMS ENUMERATION (P-QVMARMS).

    evalQuotientIdentityStep (VmReference.lean:730-867) has 24 opcode arms plus the
    five-arm stream-level or-pattern and the unknown-opcode fallback.
    QuotientValidator.quotientOpLen (VmValidator.lean:651-666) has four decoded arms plus
    the static-table fallback. The two were run SIDE BY SIDE over (a) all 31 entries of
    QuotientVmValidatorKats.opcodeFixtures - one complete phase-1-accepted program per
    table opcode, at each fixture's own testIdx - and (b) every opcode byte 0..255 against
    a 604-byte operand payload engineered so every arm's operand reads succeed (MODARITH7
    flags legal, both AFFINE_SUM counts nonzero, the RUN count nonzero). The gate
    arms_agreement_differential_ok below re-runs both measurements inside the build.

    RESULT: NO DISAGREEMENT. All 26 identity arms agree exactly, including the four
    dynamic forms (on the fixtures: RUN 13 and 9, MODARITH7 148, AFFINE_SUM 13). The
    table is the enumeration; step is what evalQuotientIdentityStep reports as consumed,
    len is what quotientOpLen reports, and source is where quotientOpLen gets it.

--   push_const                     3            table
--   push_mem_literal               5            table
--   push_mem_token                 2            table
--   push_mem_token_offset          6            table
--   push_mem_u16                   3            table
--   add                            1            table
--   mul                            1            table
--   neg                            1            table
--   push_const_u8                  2            table
--   add_const_u8                   2            table
--   mul_const_u8                   2            table
--   add_const                      3            table
--   mul_const                      3            table
--   add_mem_u16                    3            table
--   mul_mem_u16                    3            table
--   add_mul_mem_mem_const_u8       6            table
--   add_mul_const_u8_mem_u16       4            table
--   add_mul_mem_mem                5            table
--   lin7                           22           table
--   bilin7_row                     24           table
--   bilin7_pairwise                18           table
--   pow5                           1            table
--   run_add_mul_mem_mem_const_u8   3+5n         decode
--   run_add_mul_const_u8_mem_u16   3+3n         decode
--   affine_sum                     5+3l+5p      decode
--   modarith7                      header+blocks decode
--   fold_main                      - / 1        stream
--   fold_selector                  - / 4        stream
--   native_permutation             - / 1        stream
--   native_identity                - / 3        stream
--   native_lookup                  - / 1        stream

    Two asymmetries were found, and NEITHER is a width disagreement:

      * the five stream-level opcodes have a validator width (1, 4, 1, 3, 1) but are an
        ERROR in the identity interpreter (streamOpcodeInIdentity, QVR:325-333). That is
        the documented DOMAIN OF QVM.run boundary, so streamIdentityExcluded below is
        EXCLUDED from every agreement statement rather than assumed away - and
        streamArms_error proves the exclusion rather than asserting it. A loop induction
        does NOT need a "no stream opcode in the segment" hypothesis: identitySegment
        (VmCertify.lean:409-435) stops at FOLD_MAIN / FOLD_SELECTOR and ERRORS on the
        three native markers, so a segment it delimits contains none by construction.
      * the interpreter refuses three shapes quotientOpLen happily walks: MODARITH7 with
        unknown flag bits, a zero-length RUN, and AFFINE_SUM with a zero count. So the
        agreement is CONDITIONAL - equal widths wherever both sides succeed - which is
        why every lemma below takes the step's success and the walk's success as
        hypotheses. A lemma stating the agreement unconditionally would be FALSE, and
        the validator-side half of that asymmetry was already pinned by
        twoPhase_checkedAndUncheckedWalksAgree_ok. -/
def staticIdentityArms : List Nat :=
  [qOpPushConst, qOpPushMemLiteral, qOpPushMemToken, qOpPushMemTokenOffset, qOpPushMemU16,
   qOpAdd, qOpMul, qOpNeg, qOpPushConstU8, qOpAddConstU8, qOpMulConstU8, qOpAddConst,
   qOpMulConst, qOpAddMemU16, qOpMulMemU16, qOpAddMulMemMemConstU8, qOpAddMulConstU8MemU16,
   qOpAddMulMemMem, qOpLin7, qOpBilin7Row, qOpBilin7Pairwise, qOpPow5]

/-- The four arms whose width quotientOpLen decodes from the operand bytes rather than
    reading from the table (byteLen = 0 in the table, pinned by
    opcodeTable_pinnedByteLengths_ok). -/
def dynamicIdentityArms : List Nat :=
  [qOpRunAddMulMemMemConstU8, qOpRunAddMulConstU8MemU16, qOpAffineSum, qOpModarith7]

/-- The five stream-level opcodes: a width to the validator, an ERROR to the identity
    interpreter. Not an oversight - see DOMAIN OF QVM.run, VmReference.lean:861-865. -/
def streamIdentityExcluded : List Nat :=
  [qOpFoldMain, qOpFoldSelector, qOpNativePermutation, qOpNativeLookup, qOpNativeIdentity]

/-- The enumeration is exhaustive and disjoint: 22 static + 4 dynamic + 5 stream = the 31
    entries of the opcode table, in table order, and nothing is counted twice. -/
theorem arms_enumeration_is_exhaustive :
    staticIdentityArms.length = 22 ∧ dynamicIdentityArms.length = 4
      ∧ streamIdentityExcluded.length = 5
      ∧ List.Nodup (staticIdentityArms ++ dynamicIdentityArms ++ streamIdentityExcluded)
      ∧ (staticIdentityArms ++ dynamicIdentityArms ++ streamIdentityExcluded).Perm
        (quotientVmSpec.opcodes.map fun s => s.opcode) := by
  refine ⟨by rfl, by rfl, by rfl, ?_, ?_⟩ <;> decide

/-- The shape-helper decoders return their byte length as the middle component of their
    triple. These five lemmas are what makes the LIN7 / BILIN7 / fused-affine arms'
    consumed a numeral rather than an uninterpreted fold result. -/
theorem affineProductTerm_ok_mid {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {idx : Nat} {w : QVMFr × Nat × QuotientRefMemory}
    (h : Midfall.Generator.affineProductTerm bytes consts mem idx = .ok w) : w.2.1 = 5 := by
  unfold Midfall.Generator.affineProductTerm at h
  repeat (obtain ⟨_, _, h⟩ := peel_bind h)
  rcases w with ⟨wv, wl, wm⟩
  simp at *
  omega

theorem affineLinearTerm_ok_mid {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {idx : Nat} {w : QVMFr × Nat × QuotientRefMemory}
    (h : Midfall.Generator.affineLinearTerm bytes consts mem idx = .ok w) : w.2.1 = 3 := by
  unfold Midfall.Generator.affineLinearTerm at h
  repeat (obtain ⟨_, _, h⟩ := peel_bind h)
  rcases w with ⟨wv, wl, wm⟩
  simp at *
  omega

theorem limbPairwiseForm_ok_mid {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {idx : Nat} {w : QVMFr × Nat × QuotientRefMemory}
    (h : Midfall.Generator.limbPairwiseForm bytes consts mem idx = .ok w) :
    w.2.1 = 4 + quotientVmPairwiseCoeffs := by
  unfold Midfall.Generator.limbPairwiseForm at h
  repeat (obtain ⟨_, _, h⟩ := peel_bind h)
  rcases w with ⟨wv, wl, wm⟩
  simp at *
  omega

/-- LOOP INDUCTION over the shape-helper fold: if every successful step advances the middle
    component by exactly w, a successful fold of n steps advances it by n*w. This is the
    induction the four dynamic decoders need, and it is the only place the fuel-bounded
    walk of the helper forms is inducted over. -/
theorem foldRangeIdxM_ok_advance {ε α β : Type} (w : Nat) :
    ∀ (n : Nat) (f : Nat → α × Nat × β → Except ε (α × Nat × β))
      (a₀ : α) (c₀ : Nat) (m₀ : β) (out : α × Nat × β),
      (∀ i s r, f i s = .ok r → r.2.1 = s.2.1 + w) →
      Midfall.Generator.foldRangeIdxM n (a₀, c₀, m₀) f = .ok out → out.2.1 = c₀ + w * n := by
  intro n
  induction n with
  | zero =>
      intro f a₀ c₀ m₀ out _ h
      cases h; rfl
  | succ k ih =>
      intro f a₀ c₀ m₀ out hf h
      have hstep : Midfall.Generator.foldRangeIdxM (k+1) (a₀, c₀, m₀) f =
          (f 0 (a₀, c₀, m₀) >>= fun x =>
             Midfall.Generator.foldRangeIdxM k x (fun i => f (i+1)) >>= fun y => .ok y) := by
        simp only [Midfall.Generator.foldRangeIdxM]
      rw [hstep] at h
      obtain ⟨x, hx, h1⟩ := peel_bind h
      obtain ⟨y, hy, h2⟩ := peel_bind h1
      have hyo : out = y := (Except.ok.inj h2).symm
      have hrec := ih (fun i => f (i+1)) x.1 x.2.1 x.2.2 y (fun i s r hr => hf (i+1) s r hr) hy
      rw [← hyo] at hrec
      have hw : x.2.1 = c₀ + w := hf 0 (a₀, c₀, m₀) x hx
      have hmul : w * (k+1) = w + w * k := by ring
      rw [hmul] at *
      omega

theorem limbLinearForm_ok_mid {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {idx : Nat} {w : QVMFr × Nat × QuotientRefMemory}
    (h : Midfall.Generator.limbLinearForm bytes consts mem idx = .ok w) : w.2.1 = 21 := by
  unfold Midfall.Generator.limbLinearForm at h
  obtain ⟨x, hx, hv⟩ := peel_bind h
  rcases x with ⟨xa, xc, xm⟩
  have key : xc = idx + 3 * quotientVmLimbs := by
    refine foldRangeIdxM_ok_advance 3 quotientVmLimbs _ qvmFrZero idx mem (xa, xc, xm) ?_ hx
    intro i s r hr
    rcases s with ⟨acc, cursor, mem⟩
    obtain ⟨slot, _, hr⟩ := peel_bind hr
    obtain ⟨ptr, _, hr⟩ := peel_bind hr
    obtain ⟨cc, _, hr⟩ := peel_bind hr
    rcases mem.literal ptr with ⟨vv, mm⟩
    rcases r with ⟨rv, rl, rm⟩
    simp at *
    omega
  have hlimbs : quotientVmLimbs = 7 := rfl
  rw [hlimbs] at key
  rcases w with ⟨wv, wl, wm⟩
  simp at *
  omega

theorem limbRowForm_ok_mid {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {idx : Nat} {w : QVMFr × Nat × QuotientRefMemory}
    (h : Midfall.Generator.limbRowForm bytes consts mem idx = .ok w) : w.2.1 = 23 := by
  unfold Midfall.Generator.limbRowForm at h
  obtain ⟨lhs, _, h⟩ := peel_bind h
  obtain ⟨inner, hin, h⟩ := peel_bind h
  rcases inner with ⟨i1, i2, i3⟩
  have hl2 := limbLinearForm_ok_mid hin
  rcases w with ⟨wv, wl, wm⟩
  simp at *
  omega

/-- THE PER-ARM AGREEMENT, 22 arms. For each of the 22 static identity arms: when the
    identity step succeeds on an instruction whose opcode byte is at index 0 and the
    validator's walker gives the same instruction a width, the consumed the step reports
    IS that width. Written at index 0 with the opcode consed on - that is the general
    statement up to renaming the suffix (List.drop), and it is the shape both walks
    actually present at a cursor. Conditional by construction: the hypotheses are the two
    successes, and dropping either one makes the statement false (see the doc above). -/
theorem evalQuotientIdentityStep_consumed_agrees
    (op : Nat)
    (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpBilin7Pairwise \/ op = qOpLin7 \/ op = qOpBilin7Row)
    (rest : List Nat)
    (consts : List Midfall.Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep (op :: rest) consts 0 op stack mem
      = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len) :
    step.consumed = len := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushConst :: rest) 0 = .ok 3 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemLiteral :: rest) 0 = .ok 5 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemToken :: rest) 0 = .ok 2 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemTokenOffset :: rest) 0 = .ok 6 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemU16 :: rest) 0 = .ok 3 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAdd :: rest) 0 = .ok 1 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMul :: rest) 0 = .ok 1 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpNeg :: rest) 0 = .ok 1 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushConstU8 :: rest) 0 = .ok 2 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddConstU8 :: rest) 0 = .ok 2 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMulConstU8 :: rest) 0 = .ok 2 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddConst :: rest) 0 = .ok 3 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMulConst :: rest) 0 = .ok 3 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMemU16 :: rest) 0 = .ok 3 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMulMemU16 :: rest) 0 = .ok 3 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMulMemMem :: rest) 0 = .ok 5 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPow5 :: rest) 0 = .ok 1 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    repeat (obtain ⟨_, _, hstep⟩ := peel_bind hstep)
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMulMemMemConstU8 :: rest) 0 = .ok 6 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    obtain ⟨_, _, hstep⟩ := peel_bind hstep
    obtain ⟨pw, hpw, hstep⟩ := peel_bind hstep
    have hl := affineProductTerm_ok_mid hpw
    rcases pw with ⟨p1, p2, p3⟩
    have hcw : quotientVmPairwiseCoeffs = 13 := rfl
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMulConstU8MemU16 :: rest) 0 = .ok 4 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    obtain ⟨_, _, hstep⟩ := peel_bind hstep
    obtain ⟨pw, hpw, hstep⟩ := peel_bind hstep
    have hl := affineLinearTerm_ok_mid hpw
    rcases pw with ⟨p1, p2, p3⟩
    have hcw : quotientVmPairwiseCoeffs = 13 := rfl
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpBilin7Pairwise :: rest) 0 = .ok 18 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    obtain ⟨pw, hpw, hstep⟩ := peel_bind hstep
    have hl := limbPairwiseForm_ok_mid hpw
    rcases pw with ⟨p1, p2, p3⟩
    have hcw : quotientVmPairwiseCoeffs = 13 := rfl
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpLin7 :: rest) 0 = .ok 22 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    obtain ⟨pw, hpw, hstep⟩ := peel_bind hstep
    have hl := limbLinearForm_ok_mid hpw
    rcases pw with ⟨p1, p2, p3⟩
    have hcw : quotientVmPairwiseCoeffs = 13 := rfl
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpBilin7Row :: rest) 0 = .ok 24 from rfl)] at hlen
    simp at hlen
    unfold Midfall.Generator.evalQuotientIdentityStep at hstep
    simp (config := { decide := true }) at hstep
    obtain ⟨pw, hpw, hstep⟩ := peel_bind hstep
    have hl := limbRowForm_ok_mid hpw
    rcases pw with ⟨p1, p2, p3⟩
    have hcw : quotientVmPairwiseCoeffs = 13 := rfl
    rcases step with ⟨st, c, hc2, m⟩
    simp at *
    omega

/-- The witness environment the two D-P23 halves below run in. Not a Rust item. -/
def armsWitnessConsts : List Word256 := Midfall.Generator.QuotientVmRefKats.refConsts

/-- ditto -/
def armsWitnessMem : QuotientRefMemory :=
  Midfall.Generator.quotientRefMemoryNew Midfall.Generator.QuotientVmRefKats.refSeedA

/-- D-P23 SATISFIABILITY HALF, as a theorem. The hypotheses of
    evalQuotientIdentityStep_consumed_agrees are satisfiable at concrete witnesses, and the
    agreed width is NOT a constant the statement could have guessed: PUSH_CONST agrees at
    3 and ADD agrees at 1. Without this the agreement lemma could in principle be vacuous
    on both arms. -/
theorem arms_agreement_hypotheses_satisfiable :
    (∃ step, Midfall.Generator.evalQuotientIdentityStep [qOpPushConst, 0, 3]
        armsWitnessConsts 0 qOpPushConst [1] armsWitnessMem = .ok step ∧
        Midfall.Generator.QuotientValidator.quotientOpLen [qOpPushConst, 0, 3] 0 = .ok 3
        ∧ step.consumed = 3)
    ∧ (∃ step, Midfall.Generator.evalQuotientIdentityStep [qOpAdd]
        armsWitnessConsts 0 qOpAdd [1, 2] armsWitnessMem = .ok step ∧
        Midfall.Generator.QuotientValidator.quotientOpLen [qOpAdd] 0 = .ok 1
        ∧ step.consumed = 1) := by
  refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩

/-- D-P23 FALSIFICATION HALF, as a theorem. The conclusion is not a tautology: at the SAME
    witness the step's consumed is 3 and NOT 4, so a walker that reported 4 for
    PUSH_CONST - the single-byte perturbation the battery in the package report names -
    satisfies every hypothesis of the agreement lemma and violates its conclusion. -/
theorem arms_agreement_conclusion_is_not_a_tautology :
    ∃ step, Midfall.Generator.evalQuotientIdentityStep [qOpPushConst, 0, 3]
        armsWitnessConsts 0 qOpPushConst [1] armsWitnessMem = .ok step ∧
        step.consumed ≠ 4 := by
  obtain ⟨step, h1, _, h2⟩ := arms_agreement_hypotheses_satisfiable.1
  exact ⟨step, h1, by omega⟩

/-- The five stream-level arms are an ERROR for the identity interpreter, so they are not
    missing from the agreement lemma above - they are outside its domain. This is what
    makes the exclusion a proved fact rather than a comment. -/
theorem streamArms_error (bytes : List Nat) (consts : List Midfall.Word256) (idx : Nat)
    (op : Nat) (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : op = qOpFoldMain \/ op = qOpFoldSelector \/ op = qOpNativePermutation
      \/ op = qOpNativeLookup \/ op = qOpNativeIdentity) :
    Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem
      = .error (QVMFault.streamOpcodeInIdentity op idx) := by
  rcases hop with (h|h|h|h|h)
  all_goals
    subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })

/-- LOOP INDUCTION over the fuel-bounded walk of evalQuotientIdentityLoop
    (VmReference.lean:874-892). Every arm advances the cursor by at least one byte - that
    is the hConsumed proof field of IdentityStep, which is why the arm that forgot to
    advance does not typecheck - so bytes.length iterations always suffice and the
    fuel-exhausted arm is unreachable. This is the fuel-adequacy lemma the survey lists as
    owed for builder_segments_total ("evalQuotientIdentityLoop.go never exhausts its
    fuel"), proved here for an arbitrary per-cursor success hypothesis rather than for one
    fixed program. -/
theorem evalQuotientIdentityLoop_fuelNeverBinds
    (bytes : List Nat) (consts : List Midfall.Word256)
    (hsteps : ∀ (j : Nat) (stk : List QVMFr) (m : QuotientRefMemory), j < bytes.length →
        ∃ step, Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0) stk m
          = .ok step) :
    ∀ (fuel j : Nat) (stk : List QVMFr) (m : QuotientRefMemory),
      bytes.length - j ≤ fuel →
      Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel j stk m ≠
        .error (QVMFault.panic "reference VM fuel exhausted") := by
  intro fuel
  induction fuel with
  | zero =>
      intro j stk m hlen
      by_cases hlt : j < bytes.length
      · have : Midfall.Generator.evalQuotientIdentityLoop.go bytes consts 0 j stk m =
            .error (QVMFault.panic "reference VM fuel exhausted") := by
          simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]
        omega
      · simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]
  | succ k ih =>
      intro j stk m hlen
      by_cases hlt : j < bytes.length
      · obtain ⟨step, hstep⟩ := hsteps j stk m hlt
        have hgo : Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (k+1) j stk m =
            (Midfall.Generator.evalQuotientIdentityStep bytes consts j (bytes.getD j 0) stk m
               >>= fun s =>
             Midfall.Generator.evalQuotientIdentityLoop.go bytes consts k (j + s.consumed)
               s.stack s.mem) := by
          simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]
        rw [hgo, hstep]
        simp only [bind, Except.bind]
        intro hcon
        have hpos : 1 ≤ step.consumed := step.hConsumed
        have hA : bytes.length - (j + step.consumed) ≤ bytes.length - (j + 1) :=
          Nat.sub_le_sub_left (by omega : j + 1 ≤ j + step.consumed) bytes.length
        have hE : bytes.length - j - 1 ≤ k := by omega
        have hB : bytes.length - (j + 1) ≤ k := by
          rw [← Nat.sub_sub]
          exact hE
        have hsub : bytes.length - (j + step.consumed) ≤ k := Nat.le_trans hA hB
        exact ih (j + step.consumed) step.stack step.mem hsub hcon
      · simp [Midfall.Generator.evalQuotientIdentityLoop.go, hlt]


/-! ### 8. The read bound: every operand read fits inside the stride (P-READOFF) -/

/-- No read fault: the computation never names the read-past-end class.

    WHY THIS PREDICATE EXISTS. Section 7 proved that the interpreter's 'consumed' and the
    validator's 'quotientOpLen' agree, and R-70 measured that
    'qvm_validated_noBoundsFault' needs a SECOND, different fact: that every operand the
    interpreter READS lies inside the stride it is about to advance by. Agreement on
    strides says nothing about read offsets - an arm could declare a byte it never reads,
    or read one byte past its declaration, and both walkers would still agree.

    'NoRF' is the operational reading of "the read fits": a computation names no
    read-past-end fault. Every fault the reference can raise comes from one of six readers
    (byteAt, readU16, readU32, constAt, popStack, indexOrPanic) plus three explicit
    throws, and only the first three can name readPastEnd - so a step is NoRF as soon as
    its byte reads are inside the buffer, whatever the constant table or the stack does.
    That decomposition is what makes the 26-arm pass mechanical, and it is why the lemma
    below is stated against the STRIDE rather than against a per-arm numeral: the four
    dynamic arms have no numeral (RUN is 3+5n, AFFINE_SUM is 5+3l+5p, MODARITH7 is a
    header plus five counted blocks), which is exactly why P-QVMARMS could measure them
    and not prove them.

    THE LIMIT OF THE MEASUREMENT, stated rather than hidden. The differential enumeration
    in the gates below shows the read extent EQUALS the stride on every arm that reads at
    all. That is a fact about the payload the enumeration engineered, not a property of the
    arm: nothing in the validator forbids a stride that over-declares, and a thinner payload
    makes an arm read less. So what the enumeration establishes is that NO COUNTEREXAMPLE
    EXISTS to the weak form under a payload built to defeat the guards. The weak form -
    reads inside the stride - is what is proved below and what the hole needs. R-70's
    warning ("do not strengthen it") is honoured: no lemma here claims the reads fill the
    stride. -/
def NoRF {α : Type} (x : Except QVMFault α) : Prop :=
  ∀ i, x ≠ .error (QVMFault.readPastEnd i)

namespace NoRF

theorem ok {α : Type} (a : α) : NoRF (Except.ok a) := by
  intro i h; cases h

theorem error {α : Type} (e : QVMFault) (h : ∀ i, e ≠ QVMFault.readPastEnd i) :
    NoRF (Except.error (α := α) e) := by
  intro i hh
  exact h i (Except.error.inj hh)

/-- Bind preserves the read bound: a fault of the read class is either the left action's
    own or the continuation's on the value the left action returned. -/
theorem bind {α β : Type} {x : Except QVMFault α} {f : α → Except QVMFault β}
    (hx : NoRF x) (hf : ∀ a, NoRF (f a)) : NoRF (x >>= f) := by
  intro i h
  cases x with
  | ok a => exact hf a i h
  | error e => exact hx i (congrArg Except.error (Except.error.inj h))

/-- The equation-carrying bind rule. Plain 'bind' is not enough for the counted folds: the
    induction hypothesis has to know that the intermediate state's CURSOR is the one the
    step function produced, and the plain rule hands the continuation an arbitrary value. -/
theorem bind2 {α β : Type} (x : Except QVMFault α) (f : α → Except QVMFault β)
    (hx : NoRF x) (hf : ∀ a, x = .ok a → NoRF (f a)) : NoRF (x >>= f) := by
  cases x with
  | ok a => exact hf a rfl
  | error e =>
      have hne : ∀ i, e ≠ QVMFault.readPastEnd i := by
        intro i hh
        exact hx i (congrArg (Except.error (α := α)) hh)
      exact NoRF.error e hne

/-- Matching a pair is never the source of a read fault: the arms of such a match are the
    two projections applied to the scrutinee. Needed because the reference's ported 'let
    (a, b) := e' blocks hide behind a stuck match when 'e' is a memory derivation, so the
    counted folds sit behind one. -/
theorem pair_match {ε α β : Type} (e : ε × α) (f : ε → α → Except QVMFault β)
    (h : ∀ x y, NoRF (f x y)) : NoRF (match e with | (x, y) => f x y) := by
  cases e with
  | mk x y => exact h x y

/-- LOOP LEMMA, plain form: a fold whose every step names no read fault names none. Used
    by the blocks whose only in-loop byte read is the PANIC-class one. -/
theorem fold_noRF {α : Type} : ∀ (n : Nat) (init : α)
    (f : Nat → α → Except QVMFault α),
    (∀ (i : Nat) (a : α), i < n → NoRF (f i a)) →
      NoRF (Midfall.Generator.foldRangeIdxM n init f) := by
  intro n
  induction n with
  | zero => intro init f _; exact NoRF.ok _
  | succ k ih =>
      intro init f hf
      have hgo : Midfall.Generator.foldRangeIdxM (k+1) init f =
          (f 0 init >>= fun x =>
             Midfall.Generator.foldRangeIdxM k x (fun i => f (i+1)) >>= fun y => .ok y) := rfl
      rw [hgo]
      exact NoRF.bind (hf 0 init (by omega))
        (fun x => NoRF.bind
          (ih x (fun i => f (i+1)) (fun i a hi => hf (i+1) a (by omega)))
          (fun _ => NoRF.ok _))

/-- LOOP LEMMA for the counted blocks. A stride-'w' fold of 'n' blocks over a cursor that
    starts at 'c₀' names no read fault whenever 'c₀ + w·n ≤ L', every step reads only
    below 'L', and every successful step advances the cursor by exactly 'w'.

    This is the read-side twin of 'foldRangeIdxM_ok_advance' (section 7), and it is the
    mechanism R-70 named as "the tool that would do" the dynamic arms: their stride is a
    function of operand bytes read mid-instruction, so the bound cannot be a numeral per
    arm and has to be carried through the fold as an invariant on the cursor. The
    invariant is stated on the cursor ('s.2.1 + w ≤ L') rather than on the block index
    because the fold's own recursion shifts the index, not the cursor. -/
theorem fold_blocks_noRF {β : Type} (w L : Nat) :
    ∀ (n : Nat) (init : QVMFr × Nat × β)
      (f : Nat → QVMFr × Nat × β → Except QVMFault (QVMFr × Nat × β)),
      init.2.1 + w * n ≤ L →
      (∀ (i : Nat) (s : QVMFr × Nat × β), i < n → s.2.1 + w ≤ L → NoRF (f i s)) →
      (∀ (i : Nat) (s r : QVMFr × Nat × β), i < n → f i s = .ok r → r.2.1 = s.2.1 + w) →
      NoRF (Midfall.Generator.foldRangeIdxM n init f) := by
  intro n
  induction n with
  | zero => intro init f _ _ _; exact NoRF.ok _
  | succ k ih =>
      intro init f hinit hf hadv
      have hw : w ≤ w * (k+1) := by nlinarith
      have h0 : init.2.1 + w ≤ L := by omega
      have hstep : NoRF (f 0 init) := hf 0 init (by omega) h0
      have hgo : Midfall.Generator.foldRangeIdxM (k+1) init f =
          (f 0 init >>= fun x =>
             Midfall.Generator.foldRangeIdxM k x (fun i => f (i+1)) >>= fun y => .ok y) := rfl
      rw [hgo]
      refine NoRF.bind2 (f 0 init)
        (fun x => Midfall.Generator.foldRangeIdxM k x (fun i => f (i+1)) >>= fun y => .ok y)
        hstep (fun x hx => ?_)
      have hw' : x.2.1 = init.2.1 + w := hadv 0 init x (by omega) hx
      have hmul : w * (k+1) = w + w * k := by ring
      have hrec : x.2.1 + w * k ≤ L := by omega
      exact NoRF.bind
        (ih x (fun i => f (i+1)) hrec
          (fun i s hi hs => hf (i+1) s (by omega) hs)
          (fun i s r hi hr => hadv (i+1) s r (by omega) hr))
        (fun _ => NoRF.ok _)

end NoRF

/-! #### The six readers, sorted by whether they can name a read fault at all -/

/-- 'byteAt' inside the buffer names no read fault. -/
theorem byteAt_noRF (bytes : List Nat) (k : Nat) (hk : k < bytes.length) :
    NoRF (Midfall.Generator.byteAt bytes k) := by
  unfold Midfall.Generator.byteAt
  have hne : bytes.drop k ≠ [] := by
    intro hh
    have hlen : (bytes.drop k).length = bytes.length - k := List.length_drop
    rw [hh] at hlen
    simp at hlen
    omega
  cases h : bytes.drop k with
  | cons b rest => exact NoRF.ok b
  | nil => exact absurd h hne

/-- 'readU16' is two 'byteAt' calls, so it needs two bytes. -/
theorem readU16_noRF (bytes : List Nat) (k : Nat) (hk : k + 1 < bytes.length) :
    NoRF (Midfall.Generator.readU16 bytes k) := by
  unfold Midfall.Generator.readU16
  refine NoRF.bind (byteAt_noRF bytes k (by omega)) (fun _ => ?_)
  refine NoRF.bind (byteAt_noRF bytes (k+1) (by omega)) (fun _ => NoRF.ok _)

/-- 'readU32' is four 'byteAt' calls. -/
theorem readU32_noRF (bytes : List Nat) (k : Nat) (hk : k + 3 < bytes.length) :
    NoRF (Midfall.Generator.readU32 bytes k) := by
  unfold Midfall.Generator.readU32
  refine NoRF.bind (byteAt_noRF bytes k (by omega)) (fun _ =>
    NoRF.bind (byteAt_noRF bytes (k+1) (by omega)) (fun _ =>
    NoRF.bind (byteAt_noRF bytes (k+2) (by omega)) (fun _ =>
    NoRF.bind (byteAt_noRF bytes (k+3) (by omega)) (fun _ => NoRF.ok _))))

/-- 'fqFromU256' names the canonicality PANIC, never a read fault. -/
theorem fqFromU256_noRF (value : Midfall.Word256) :
    NoRF (Midfall.Generator.fqFromU256 value) := by
  unfold Midfall.Generator.fqFromU256
  by_cases hb : value.toNat < qvmFrModulus
  · rw [if_pos hb]; exact NoRF.ok _
  · rw [if_neg hb]
    exact NoRF.error (QVMFault.panic
      "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs:548")
      (by intro i h; cases h)

/-- 'constAt' names the slot fault or the canonicality panic. It reads the CONSTANT TABLE,
    not the program bytes, so it is structurally incapable of a readPastEnd - which is what
    splits the hole into its two halves. No argument about bytes discharges the table half,
    and no argument about the table discharges the bytes half. -/
theorem constAt_noRF (consts : List Midfall.Word256) (slot idx : Nat) :
    NoRF (Midfall.Generator.constAt consts slot idx) := by
  unfold Midfall.Generator.constAt
  cases hcs : consts.drop slot with
  | cons v rest => show NoRF (Midfall.Generator.fqFromU256 v); exact fqFromU256_noRF v
  | nil =>
      exact NoRF.error (QVMFault.constSlotOutOfRange slot idx)
        (by intro i h; cases h)

/-- 'popStack' names the stack-underflow fault only. -/
theorem popStack_noRF (stack : List QVMFr) (idx : Nat) :
    NoRF (Midfall.Generator.popStack stack idx) := by
  unfold Midfall.Generator.popStack
  cases stack with
  | nil => exact NoRF.error (QVMFault.stackUnderflow idx) (by intro i h; cases h)
  | cons v rest => exact NoRF.ok (v, rest)

/-- 'indexOrPanic' - the one read in the reference that PANICS rather than returning Err
    (QVR:427, hazard 5's pair with the up-front guard) - names the panic class, never
    readPastEnd. This is why the pairwise coefficient block is free in the read bound: the
    guard is the only bounds-checked read of that block and the 49 indexed reads after it
    cannot produce the fault the hole excludes. -/
theorem indexOrPanic_noRF (bytes : List Nat) (k : Nat) :
    NoRF (Midfall.Generator.indexOrPanic bytes k) := by
  unfold Midfall.Generator.indexOrPanic
  cases h : bytes.drop k with
  | cons b rest => exact NoRF.ok b
  | nil =>
      exact NoRF.error (QVMFault.panic
        "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs:427")
        (by intro i hh; cases hh)

/-! #### The five shape helpers, read-bounded -/

/-- The fused affine product term reads 5 bytes at idx..idx+4 and returns that as its
    length; the read bound and 'affineProductTerm_ok_mid' (section 7) are the same numeral
    from two different directions. -/
theorem affineLinearTerm_noRF (bytes : List Nat) (idx : Nat)
    (hfit : idx + 3 ≤ bytes.length) (consts : List Midfall.Word256)
    (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.affineLinearTerm bytes consts mem idx) := by
  unfold Midfall.Generator.affineLinearTerm
  refine NoRF.bind (readU16_noRF bytes idx (by omega)) (fun _ =>
    NoRF.bind (byteAt_noRF bytes (idx+2) (by omega)) (fun _ =>
    NoRF.bind (constAt_noRF consts _ idx) (fun _ => NoRF.ok _)))

/-- The fused affine product term reads 5 bytes at idx..idx+4. -/
theorem affineProductTerm_noRF (bytes : List Nat) (idx : Nat)
    (hfit : idx + 5 ≤ bytes.length) (consts : List Word256)
    (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.affineProductTerm bytes consts mem idx) := by
  unfold Midfall.Generator.affineProductTerm
  refine NoRF.bind (readU16_noRF bytes idx (by omega)) (fun _ =>
    NoRF.bind (readU16_noRF bytes (idx+2) (by omega)) (fun _ =>
    NoRF.bind (byteAt_noRF bytes (idx+4) (by omega)) (fun _ =>
    NoRF.bind (constAt_noRF consts _ idx) (fun _ => NoRF.ok _))))

/-- The seven-limb linear block reads 3 bytes per limb at cursors idx, idx+3, ..., idx+18,
    so its read extent is 21 = 3 · quotientVmLimbs - the numeral 'limbLinearForm_ok_mid'
    proves from the other side. This is where the fold invariant earns its keep: the cursor
    is not a numeral in the term, it is the second component of the fold state, so the
    bound has to be carried through 'fold_blocks_noRF'. -/
theorem limbLinearForm_noRF (bytes : List Nat) (idx : Nat)
    (hfit : idx + 3 * quotientVmLimbs ≤ bytes.length) (consts : List Word256)
    (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.limbLinearForm bytes consts mem idx) := by
  have key := NoRF.fold_blocks_noRF (β := QuotientRefMemory) 3 bytes.length
  unfold Midfall.Generator.limbLinearForm
  refine NoRF.bind (key quotientVmLimbs (qvmFrZero, idx, mem) _ ?_ ?_ ?_) (fun _ => NoRF.ok _)
  · simp only [Prod.snd, Prod.fst]
    omega
  · intro i s hi hs
    obtain ⟨acc, cursor, m⟩ := s
    refine NoRF.bind (byteAt_noRF bytes cursor (by
        simp only [Prod.snd, Prod.fst] at hs ⊢; omega)) (fun slot =>
      NoRF.bind (readU16_noRF bytes (cursor+1) (by
        simp only [Prod.snd, Prod.fst] at hs ⊢; omega)) (fun _ =>
      NoRF.bind (constAt_noRF consts slot cursor) (fun _ => NoRF.ok _)))
  · intro i s r hi hr
    obtain ⟨acc, cursor, m⟩ := s
    obtain ⟨acc', cursor', m'⟩ := r
    obtain ⟨slot, _, hr⟩ := peel_bind hr
    obtain ⟨ptr, _, hr⟩ := peel_bind hr
    obtain ⟨c, _, hr⟩ := peel_bind hr
    rcases m.literal ptr with ⟨v, mm⟩
    simp at *
    omega

/-- The row block is a u16 plus the linear block at idx+2: extent 2 + 21 = 23, the numeral
    'limbRowForm_ok_mid' proves. -/
theorem limbRowForm_noRF (bytes : List Nat) (idx : Nat)
    (hfit : idx + 23 ≤ bytes.length) (consts : List Word256)
    (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.limbRowForm bytes consts mem idx) := by
  unfold Midfall.Generator.limbRowForm
  refine NoRF.bind (readU16_noRF bytes idx (by omega)) (fun _ =>
    NoRF.bind (limbLinearForm_noRF bytes (idx+2) ?_ consts _) (fun _ => NoRF.ok _))
  · have hl : quotientVmLimbs = 7 := rfl
    omega

/-- The pairwise block reads FOUR header bytes plus the coefficient guard at
    coeffIdx + 12 = idx + 16, so its read extent is 17 = 4 + quotientVmPairwiseCoeffs -
    and the stride the table declares for the ARM is 18 because the opcode byte is not part
    of the helper's view. This is the arm R-70 called "one arithmetic slip away" from
    declaring a byte it never reads: the margin is exactly that opcode byte.

    The 49 indexed coefficient reads inside the fold are the PANIC class, not readPastEnd
    ('indexOrPanic_noRF'), so the fold is unconditionally NoRF and needs no cursor
    invariant - the up-front guard is the only bounds-checked read of the block, which is
    hazard 5's pair in two adjacent lines and is now a proved distinction rather than a
    comment. -/
theorem limbPairwiseForm_noRF (bytes : List Nat) (idx : Nat)
    (hfit : idx + 4 + quotientVmPairwiseCoeffs ≤ bytes.length)
    (consts : List Word256) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.limbPairwiseForm bytes consts mem idx) := by
  have hc : quotientVmPairwiseCoeffs = 13 := rfl
  unfold Midfall.Generator.limbPairwiseForm
  refine NoRF.bind (readU16_noRF bytes idx (by omega)) (fun _ =>
    NoRF.bind (readU16_noRF bytes (idx+2) (by omega)) (fun _ =>
    NoRF.bind (byteAt_noRF bytes (idx + 4 + quotientVmPairwiseCoeffs - 1) (by omega))
      (fun _ => NoRF.bind (NoRF.fold_noRF quotientVmLimbs (qvmFrZero, mem) _ ?_)
        (fun _ => NoRF.ok _))))
  · intro i a hi
    obtain ⟨acc, m⟩ := a
    dsimp only
    apply NoRF.fold_noRF
    intro j b hj
    refine NoRF.bind (indexOrPanic_noRF bytes _) (fun _ =>
      NoRF.bind (constAt_noRF consts _ _) (fun _ => NoRF.ok _))

/-- THE PER-ARM READ BOUND, 22 arms (P-READOFF deliverable 2). For each of the 22 static
    identity arms: when the validator's walker gives the instruction at index 0 a stride and
    that stride FITS INSIDE THE BUFFER, the interpreter's step names no read-past-end fault.

    This is the second per-arm fact R-70 said 'qvm_validated_noBoundsFault' needs, and it is
    a DIFFERENT fact from 'evalQuotientIdentityStep_consumed_agrees' (section 7): that one
    compares two numbers, this one bounds where bytes are touched. Neither implies the other
    - an arm could agree on the stride and still read past it, or read short and disagree.

    Stated against the STRIDE rather than a per-arm numeral so the four dynamic arms can
    join the same statement; the fit hypothesis is what makes it a bound rather than a
    tautology - drop it and ADD is a counterexample at idx = bytes.length.

    CONDITIONAL BY CONSTRUCTION, for the same reason as section 7: 'hlen' is a hypothesis.
    The interpreter refuses three shapes the walker walks (unknown MODARITH7 flags, a
    zero-length RUN, zero AFFINE_SUM counts); those refusals are NOT read faults, which is
    what lets this statement survive them - see the gates.

    NOT INCLUDED HERE: the four dynamic arms. Two of them - the RUN pair - are proved
    separately below ('runAddMulMemMemConstU8_noRF', 'runAddMulConstU8MemU16_noRF') because
    their stride is a function of a count read mid-instruction and cannot be written as a
    numeral in this case split; AFFINE_SUM and MODARITH7 are measured-agreeing and not yet
    proved, for the chaining reason in their own doc comments. So the read bound covers
    24 of the 26 identity arms, and the two gaps are arithmetic depth, not a missing idea. -/
theorem evalQuotientIdentityStep_readsWithinStride
    (op : Nat)
    (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpLin7 \/ op = qOpBilin7Row \/ op = qOpBilin7Pairwise)
    (rest : List Nat)
    (len : Nat)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen (op :: rest) 0 = .ok len)
    (hfit : len ≤ (op :: rest).length)
    (consts : List Midfall.Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.evalQuotientIdentityStep (op :: rest) consts 0 op stack mem) := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushConst :: rest) 0 = .ok 3 from rfl)] at hlen
    obtain rfl : len = 3 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpPushConst :: rest) 1 ?_) (fun slot =>
        NoRF.bind (constAt_noRF consts slot 0) (fun _ => NoRF.ok _))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemLiteral :: rest) 0 = .ok 5 from rfl)] at hlen
    obtain rfl : len = 5 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU32_noRF (qOpPushMemLiteral :: rest) 1 ?_) (fun _ => NoRF.ok _)
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemToken :: rest) 0 = .ok 2 from rfl)] at hlen
    obtain rfl : len = 2 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (byteAt_noRF (qOpPushMemToken :: rest) 1 ?_) (fun _ => NoRF.ok _)
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemTokenOffset :: rest) 0 = .ok 6 from rfl)] at hlen
    obtain rfl : len = 6 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (byteAt_noRF (qOpPushMemTokenOffset :: rest) 1 ?_) (fun _ =>
        NoRF.bind (readU32_noRF (qOpPushMemTokenOffset :: rest) 2 ?_) (fun _ => NoRF.ok _))
    · omega
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushMemU16 :: rest) 0 = .ok 3 from rfl)] at hlen
    obtain rfl : len = 3 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpPushMemU16 :: rest) 1 ?_) (fun _ => NoRF.ok _)
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAdd :: rest) 0 = .ok 1 from rfl)] at hlen
    obtain rfl : len = 1 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (popStack_noRF stack 0) (fun _ =>
        NoRF.bind (popStack_noRF _ 0) (fun _ => NoRF.ok _))
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMul :: rest) 0 = .ok 1 from rfl)] at hlen
    obtain rfl : len = 1 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (popStack_noRF stack 0) (fun _ =>
        NoRF.bind (popStack_noRF _ 0) (fun _ => NoRF.ok _))
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpNeg :: rest) 0 = .ok 1 from rfl)] at hlen
    obtain rfl : len = 1 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPushConstU8 :: rest) 0 = .ok 2 from rfl)] at hlen
    obtain rfl : len = 2 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (byteAt_noRF (qOpPushConstU8 :: rest) 1 ?_) (fun slot =>
        NoRF.bind (constAt_noRF consts slot 0) (fun _ => NoRF.ok _))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddConstU8 :: rest) 0 = .ok 2 from rfl)] at hlen
    obtain rfl : len = 2 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (byteAt_noRF (qOpAddConstU8 :: rest) 1 ?_) (fun slot =>
        NoRF.bind (constAt_noRF consts slot 0) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMulConstU8 :: rest) 0 = .ok 2 from rfl)] at hlen
    obtain rfl : len = 2 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (byteAt_noRF (qOpMulConstU8 :: rest) 1 ?_) (fun slot =>
        NoRF.bind (constAt_noRF consts slot 0) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddConst :: rest) 0 = .ok 3 from rfl)] at hlen
    obtain rfl : len = 3 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpAddConst :: rest) 1 ?_) (fun slot =>
        NoRF.bind (constAt_noRF consts slot 0) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMulConst :: rest) 0 = .ok 3 from rfl)] at hlen
    obtain rfl : len = 3 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpMulConst :: rest) 1 ?_) (fun slot =>
        NoRF.bind (constAt_noRF consts slot 0) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMemU16 :: rest) 0 = .ok 3 from rfl)] at hlen
    obtain rfl : len = 3 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpAddMemU16 :: rest) 1 ?_) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpMulMemU16 :: rest) 0 = .ok 3 from rfl)] at hlen
    obtain rfl : len = 3 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpMulMemU16 :: rest) 1 ?_) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMulMemMem :: rest) 0 = .ok 5 from rfl)] at hlen
    obtain rfl : len = 5 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (readU16_noRF (qOpAddMulMemMem :: rest) 1 ?_) (fun _ =>
        NoRF.bind (readU16_noRF (qOpAddMulMemMem :: rest) 3 ?_) (fun _ =>
        NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)))
    · omega
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpPow5 :: rest) 0 = .ok 1 from rfl)] at hlen
    obtain rfl : len = 1 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (popStack_noRF stack 0) (fun _ => NoRF.ok _)
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMulMemMemConstU8 :: rest) 0 = .ok 6 from rfl)] at hlen
    obtain rfl : len = 6 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (popStack_noRF stack 0) (fun _ =>
        NoRF.bind (affineProductTerm_noRF (qOpAddMulMemMemConstU8 :: rest) 1 ?_ consts mem) (fun _ => NoRF.ok _))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpAddMulConstU8MemU16 :: rest) 0 = .ok 4 from rfl)] at hlen
    obtain rfl : len = 4 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (popStack_noRF stack 0) (fun _ =>
        NoRF.bind (affineLinearTerm_noRF (qOpAddMulConstU8MemU16 :: rest) 1 ?_ consts mem) (fun _ => NoRF.ok _))
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpLin7 :: rest) 0 = .ok 22 from rfl)] at hlen
    obtain rfl : len = 22 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (limbLinearForm_noRF (qOpLin7 :: rest) 1 ?_ consts mem) (fun _ => NoRF.ok _)
    · have hl : quotientVmLimbs = 7 := rfl
      omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpBilin7Row :: rest) 0 = .ok 24 from rfl)] at hlen
    obtain rfl : len = 24 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (limbRowForm_noRF (qOpBilin7Row :: rest) 1 ?_ consts mem) (fun _ => NoRF.ok _)
    · omega
  · subst h
    rw [(show Midfall.Generator.QuotientValidator.quotientOpLen (qOpBilin7Pairwise :: rest) 0 = .ok 18 from rfl)] at hlen
    obtain rfl : len = 18 := (Except.ok.inj hlen).symm
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := { decide := true })
    refine NoRF.bind (limbPairwiseForm_noRF (qOpBilin7Pairwise :: rest) 1 ?_ consts mem) (fun _ => NoRF.ok _)
    · have hc : quotientVmPairwiseCoeffs = 13 := rfl
      omega

/-- D-P23 SATISFIABILITY HALF, as a theorem. The hypotheses of the read-bound lemma are
    satisfiable at a concrete witness, and the witness is the live one: PUSH_MEM_LITERAL on
    a five-byte instruction fits its stride, succeeds, and names no read fault. -/
theorem reads_within_stride_hypotheses_satisfiable :
    (∃ step, Midfall.Generator.evalQuotientIdentityStep [qOpPushMemLiteral, 0, 0, 1, 0]
        armsWitnessConsts 0 qOpPushMemLiteral [] armsWitnessMem = .ok step
        ∧ step.consumed = 5)
    ∧ NoRF (Midfall.Generator.evalQuotientIdentityStep [qOpPushMemLiteral, 0, 0, 1, 0]
        armsWitnessConsts 0 qOpPushMemLiteral [] armsWitnessMem) := by
  refine ⟨⟨_, rfl, rfl⟩, fun i h => ?_⟩
  cases h

/-- D-P23 FALSIFICATION HALF, as a theorem. The conclusion is not a tautology: the SAME arm
    on a three-byte instruction DOES fault readPastEnd, at byte 3 - the first byte its stride
    claims that is missing. So "names no read fault" excludes a fault the interpreter really
    produces, and
    the fit hypothesis is exactly what separates the two cases. Without this the read lemma
    could have been vacuously true on every arm. -/
theorem reads_within_stride_conclusion_is_not_a_tautology :
    ∃ i, Midfall.Generator.evalQuotientIdentityStep
        [qOpPushMemLiteral, 0, 0] armsWitnessConsts 0 qOpPushMemLiteral
        [] armsWitnessMem = .error (QVMFault.readPastEnd i) := by
  refine ⟨3, ?_⟩
  unfold Midfall.Generator.evalQuotientIdentityStep Midfall.Generator.readU32
    Midfall.Generator.byteAt
  simp (config := { decide := true }) [bind, Except.bind]

/-- THE DYNAMIC ARMS, READ-BOUNDED (P-READOFF). R-70 said the four dynamic arms were
    measurable but not provable because "their widths come from nested counted blocks, and
    'foldRangeIdxM_ok_advance' is the tool that would do it". On the read side the twin tool
    is 'NoRF.fold_blocks_noRF', and these two RUN arms are it working: the stride is
    '3+5n' / '3+3n', a function of a u16 read out of the payload, so the bound is carried
    through the fold as a cursor invariant rather than written as a numeral per arm.

    NOTE THE SHAPE OF THE HYPOTHESES. Both take the decoded count as a hypothesis ('hn')
    rather than deriving it, because the step's own first action is the read that produces
    it - the same conditionality section 7 had to accept for the stride agreement, and for
    the same reason: the interpreter refuses shapes the walker walks (here a zero-length
    RUN), and a lemma that assumed the count was nonzero would be excluding a case the
    arm actually reaches. The zero case is discharged HERE, as a throw that names
    'zeroLengthRun' and therefore no read fault - not by a hypothesis that hides it. -/
theorem runAddMulMemMemConstU8_noRF (bytes : List Nat) (idx n : Nat)
    (hn : Midfall.Generator.readU16 bytes (idx + 1) = .ok n)
    (hfit : idx + 3 + 5 * n ≤ bytes.length)
    (consts : List Midfall.Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulMemMemConstU8 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [hn]
  simp only [bind, Except.bind]
  by_cases hc : n ≠ 0
  · rw [if_pos (by simp [hc])]
    refine NoRF.bind (popStack_noRF stack idx) (fun px =>
      NoRF.bind (NoRF.fold_blocks_noRF (β := QuotientRefMemory) 5
          (bytes.length - idx - 3) n (px.1, 0, mem) _ ?_ ?_ ?_) (fun _ => NoRF.ok _))
    · simp only [Prod.snd, Prod.fst]
      have h3 : idx + 3 ≤ bytes.length := by omega
      omega
    · intro i s hi hs
      refine NoRF.bind (affineProductTerm_noRF bytes (idx + 3 + s.2.1) ?_ consts s.2.2)
        (fun _ => NoRF.ok _)
      have h3 : idx + 3 ≤ bytes.length := by omega
      omega
    · intro i s r hi hr
      obtain ⟨acc, used, m⟩ := s
      obtain ⟨acc', used', m'⟩ := r
      obtain ⟨pw, hpw, hr⟩ := peel_bind hr
      have hl := affineProductTerm_ok_mid hpw
      rcases pw with ⟨v, l, mm⟩
      simp at *
      omega
  · rw [if_neg (by simp [hc])]
    refine NoRF.error (QVMFault.zeroLengthRun idx) (by intro i h; cases h)

/-- The second RUN arm: '3+3n' over affine LINEAR terms of 3 bytes each. Same mechanism,
    different stride - which is the point. -/
theorem runAddMulConstU8MemU16_noRF (bytes : List Nat) (idx n : Nat)
    (hn : Midfall.Generator.readU16 bytes (idx + 1) = .ok n)
    (hfit : idx + 3 + 3 * n ≤ bytes.length)
    (consts : List Midfall.Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpRunAddMulConstU8MemU16 stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [hn]
  simp only [bind, Except.bind]
  by_cases hc : n ≠ 0
  · rw [if_pos (by simp [hc])]
    refine NoRF.bind (popStack_noRF stack idx) (fun px =>
      NoRF.bind (NoRF.fold_blocks_noRF (β := QuotientRefMemory) 3
          (bytes.length - idx - 3) n (px.1, 0, mem) _ ?_ ?_ ?_) (fun _ => NoRF.ok _))
    · simp only [Prod.snd, Prod.fst]
      have h3 : idx + 3 ≤ bytes.length := by omega
      omega
    · intro i s hi hs
      refine NoRF.bind (affineLinearTerm_noRF bytes (idx + 3 + s.2.1) ?_ consts s.2.2)
        (fun _ => NoRF.ok _)
      have h3 : idx + 3 ≤ bytes.length := by omega
      omega
    · intro i s r hi hr
      obtain ⟨acc, used, m⟩ := s
      obtain ⟨acc', used', m'⟩ := r
      obtain ⟨lw, hlw, hr⟩ := peel_bind hr
      have hl := affineLinearTerm_ok_mid hlw
      rcases lw with ⟨v, l, mm⟩
      simp at *
      omega
  · rw [if_neg (by simp [hc])]
    refine NoRF.error (QVMFault.zeroLengthRun idx) (by intro i h; cases h)

/-! #### The phase-2 const-slot wiring (P-READOFF deliverable 3) -/

/-- THE WIRING. 'qvm_validated_noBoundsFault' excludes TWO fault classes and they need two
    unrelated facts: the read bound is about the program BYTES, this is about the CONSTANT
    TABLE. The interpreter's 'constAt consts slot idx' faults 'constSlotOutOfRange slot idx'
    exactly when 'slot ≥ consts.length' - 'consts.drop slot = []' is the only way that
    constructor is produced. The validator's phase-2 'checkQuotientConstSlot slot wide
    model.numConsts idx' rejects exactly 'slot ≥ model.numConsts'. The two bounds MEET
    because 'quotientOperandModel' builds the model with 'numConsts := build.consts.length',
    and this pins it. Without this the validator would be checking slots against a number
    nothing relates to the table the interpreter indexes, and the hole's second conjunct
    would be unprovable in principle rather than merely unproved.

    WHAT THIS DOES NOT BUY, named rather than glossed: it says the two BOUNDS coincide. It
    does not say the interpreter reads only slots the walker visited - that is a per-arm
    correspondence between 'evalQuotientIdentityStep' and 'visitQuotientOperands', it is a
    third 26-arm pass, and it is the remaining obstacle to closing the hole. -/
theorem numConsts_eq_build_length {Program Layout : Type}
    (L : Midfall.Generator.LoweringPlan Program Layout)
    (q : Midfall.Generator.PlannedQuotient)
    (model : QuotientOperandModel)
    (hmodel : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
      q.build q.plan.selectorFold = .ok model) :
    model.numConsts = q.build.consts.length := by
  cases h : Midfall.Generator.quotientReadModel L.meta_ L.data L.vk L.vkMptr L.memory with
  | error f =>
      have herr : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
          q.build q.plan.selectorFold = .error f := by
        unfold Midfall.Generator.quotientOperandModel
        rw [h]
        simp only [bind, Except.bind]
      exact absurd (herr ▸ hmodel) (by simp)
  | ok rm =>
      have hok : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
          q.build q.plan.selectorFold =
            .ok (QuotientOperandModel.mk rm q.build.consts.length
              L.meta_.numSimpleSelectors q.plan.selectorFold.maxPower
              ((L.memory.quotientStackHi - L.memory.quotientStackMptr) / wordBytes)) := by
        unfold Midfall.Generator.quotientOperandModel
        rw [h]
        simp only [bind, Except.bind, pure, Except.pure]
      rw [hok] at hmodel
      have he : QuotientOperandModel.mk rm q.build.consts.length L.meta_.numSimpleSelectors
          q.plan.selectorFold.maxPower
          ((L.memory.quotientStackHi - L.memory.quotientStackMptr) / wordBytes) = model :=
        Except.ok.inj hmodel
      rw [← he]

/-- The table half in the direction the hole needs: a slot below the table length cannot
    produce the slot fault, whatever value is stored there. Together with
    'numConsts_eq_build_length' this is the whole const-slot argument EXCEPT the per-arm
    correspondence named above. -/
theorem constAt_ok_of_lt {consts : List Midfall.Word256} {slot idx : Nat}
    (hlt : slot < consts.length) :
    Midfall.Generator.constAt consts slot idx ≠
      .error (QVMFault.constSlotOutOfRange slot idx) := by
  unfold Midfall.Generator.constAt
  cases hcs : consts.drop slot with
  | cons v rest =>
      show Midfall.Generator.fqFromU256 v ≠
        .error (QVMFault.constSlotOutOfRange slot idx)
      intro h
      unfold Midfall.Generator.fqFromU256 at h
      by_cases hb : v.toNat < qvmFrModulus
      · rw [if_pos hb] at h; cases h
      · rw [if_neg hb] at h; cases h
  | nil =>
      have hlen : (consts.drop slot).length = consts.length - slot := List.length_drop
      rw [hcs] at hlen
      simp at hlen
      omega
/-! ### 9. The third per-arm fact: the const-slot correspondence (P-CONTSLOT)

    THE HOLE NEEDS TWO UNRELATED FACTS and this section lands the second one. Section 7 made
    the two walkers take the same STRIDES; section 8 made the interpreter's operand READS fit
    inside them; both are about the program BYTES. The hole's second conjunct is
    'constSlotOutOfRange', which is about the CONSTANT TABLE, and it needs a third per-arm
    fact neither section supplies: every slot 'evalQuotientIdentityStep' looks up via 'constAt'
    must be a slot 'visitQuotientOperands' returns as a 'konst' operand, because phase 2 bounds
    only the slots the WALKER names (checkQuotientConstSlot slot wide model.numConsts idx), and
    'numConsts_eq_build_length' ties that bound to the table the interpreter indexes. Two
    independent code paths over the same bytes; nothing in the tree related them until now.

    WHY THERE IS NO READ-EFFECT MODEL, and what is measured instead. The reference has no
    notion of "the interpreter read byte p" - R-71 declined to invent one and this package
    does not either. The observable is the FAULT: 'constAt consts slot idx' produces
    'constSlotOutOfRange slot idx' exactly when 'slot >= consts.length', so a slot read is
    detectable by making the table shorter than the value that byte holds. Both sides are
    probed the same way - the interpreter by its fault, the walker by a 'konst' operand whose
    slot is out of range - so the comparison is between two measurements, not between a
    measurement and a definition. The lemma below is the statement those measurements agree
    with, and the gates in the KAT section re-run the measurements so the lemma cannot drift.

    WHAT THE ENUMERATION FOUND, before a single tactic was written (R-70's order). Over the 26
    identity arms the two position sets are EQUAL, not merely nested: 74 slot positions in
    total, per arm 2/1/1/1/2/2/1/1/7/7/13 for the static readers and 2/2/2/30 for the four
    dynamic ones. Zero disagreements. The five stream arms and the unknown-opcode class name
    nothing on either side.

    THE CONDITIONALITY, and it is the third time this has bitten. The lemma takes 'hw', that the
    walker succeeds on the instruction, and 'hw' is LOAD-BEARING: 'const_slot_correspondence_-
    needs_walker_success' exhibits LIN7 on a four-byte program with an empty table, where the
    interpreter faults 'constSlotOutOfRange 0 1' at limb term 0 while the walker panics at term
    1 and so names nothing. This is the same asymmetry section 7 met from the other direction
    (the interpreter refuses shapes the walker walks); here the walker refuses bytes the
    interpreter never reaches. It is discharged in the hole by 'supportedQvm', which runs phase
    2 over every instruction of the finalized program - so the hypothesis is one the caller can
    actually discharge, not an assumption nobody can supply.

    WHAT IS NOT HERE, named rather than glossed: the seven arms whose slot reads sit inside a
    counted fold - LIN7, BILIN7_ROW, BILIN7_PAIRWISE, the two RUN arms, AFFINE_SUM and
    MODARITH7 - are proved by the case split below only for their non-folded parts and are
    EXCLUDED from the 19-arm statement. Each needs a cursor-invariant induction over the
    interpreter's fold PLUS a prefix lemma over the walker's fold, because the erroring
    iteration's cursor is 'base + w * i' only if every earlier iteration succeeded and advanced
    by exactly w. That is the same chaining obstacle section 8 reports for the read bound, on
    the slot axis; the measurement above covers all 26 arms, the proof covers 19.

    ONE MORE THING THE HOLE NEEDS, and neither this brief nor R-71 named it. The membership
    form proved here is NOT by itself enough to refute a 'constSlotOutOfRange' fault. Validation
    bounds every slot the walker NAMES: 'slot in walkerKonstSlots implies slot < model.numConsts'.
    The correspondence gives the membership. What is still missing is that the faulted slot is
    the one the table lacks - 'step = .error (constSlotOutOfRange slot j) implies
    consts.length <= slot' - which is true (constAt is the only producer of that constructor and
    it carries its own slot argument, see 'constAt_slotFault') but has to be traced through the
    same 26-arm case split to be attached to the STEP rather than to one constAt call. So the
    brief's third per-arm fact is really TWO passes over the same arms: membership (here) and
    out-of-range-ness (not here). Both are case splits of the shape written below, so neither is
    obstructed; the second is shorter than the first because 'constAt_slotFault' already does the
    per-call work. -/

def walkerKonstSlots (bytes : List Nat) (idx op : Nat) : List Nat :=
  (operandList bytes idx op).filterMap fun o => match o with
    | QuotientOperand.konst slot _ => some slot
    | _ => none

def NamesSlot {α : Type} (x : Except QVMFault α) (S : List Nat) : Prop :=
  ∀ slot j, x = .error (QVMFault.constSlotOutOfRange slot j) → slot ∈ S

theorem NamesSlot.ok {α : Type} (a : α) (S : List Nat) : NamesSlot (Except.ok a) S := by
  intro slot j h; cases h
theorem NamesSlot.error {α : Type} {e : QVMFault} (S : List Nat)
    (h : ∀ slot j, e ≠ QVMFault.constSlotOutOfRange slot j) :
    NamesSlot (Except.error (α := α) e) S := by
  intro slot j hh
  exact absurd (Except.error.inj hh) (h slot j)
theorem NamesSlot.never {α : Type} {x : Except QVMFault α} (S : List Nat)
    (h : ∀ slot j, x ≠ .error (QVMFault.constSlotOutOfRange slot j)) : NamesSlot x S := by
  intro slot j hh; exact absurd hh (h slot j)
theorem NamesSlot.bind {α β : Type} {x : Except QVMFault α} {f : α → Except QVMFault β}
    {S : List Nat} (hx : NamesSlot x S) (hf : ∀ a, NamesSlot (f a) S) :
    NamesSlot (x >>= f) S := by
  intro slot j h
  cases x with
  | ok a => exact hf a slot j h
  | error e =>
      have h2 : e = QVMFault.constSlotOutOfRange slot j := Except.error.inj h
      subst h2
      exact hx slot j rfl
theorem NamesSlot.bind2 {α β : Type} (x : Except QVMFault α) (f : α → Except QVMFault β)
    {S : List Nat} (hx : NamesSlot x S) (hf : ∀ a, x = .ok a → NamesSlot (f a) S) :
    NamesSlot (x >>= f) S := by
  intro slot j h
  cases x with
  | ok a => exact hf a rfl slot j h
  | error e =>
      have h2 : e = QVMFault.constSlotOutOfRange slot j := Except.error.inj h
      subst h2
      exact hx slot j rfl
theorem NamesSlot.pair_match {ε α β : Type} (e : ε × α)
    (f : ε → α → Except QVMFault β) {S : List Nat}
    (h : ∀ x y, NamesSlot (f x y) S) :
    NamesSlot (match e with | (x, y) => f x y) S := by
  cases e with
  | mk x y => exact h x y

theorem byteAt_not_slotFault (bytes : List Nat) (k s j : Nat) :
    Midfall.Generator.byteAt bytes k ≠ .error (QVMFault.constSlotOutOfRange s j) := by
  unfold Midfall.Generator.byteAt
  cases hcs : bytes.drop k with
  | cons b rest => show Except.ok b ≠ _; intro h2; cases h2
  | nil => show Except.error (QVMFault.readPastEnd k) ≠ _; intro h2; cases h2
theorem byteAt_namesSlot (bytes : List Nat) (k : Nat) (S : List Nat) :
    NamesSlot (Midfall.Generator.byteAt bytes k) S :=
  NamesSlot.never S (byteAt_not_slotFault bytes k)
theorem readU16_namesSlot (bytes : List Nat) (k : Nat) (S : List Nat) :
    NamesSlot (Midfall.Generator.readU16 bytes k) S := by
  unfold Midfall.Generator.readU16
  refine NamesSlot.bind (byteAt_namesSlot bytes k S) (fun _ =>
    NamesSlot.bind (byteAt_namesSlot bytes (k+1) S) (fun _ => NamesSlot.ok _ S))
theorem readU32_namesSlot (bytes : List Nat) (k : Nat) (S : List Nat) :
    NamesSlot (Midfall.Generator.readU32 bytes k) S := by
  unfold Midfall.Generator.readU32
  refine NamesSlot.bind (byteAt_namesSlot bytes k S) (fun _ =>
    NamesSlot.bind (byteAt_namesSlot bytes (k+1) S) (fun _ =>
      NamesSlot.bind (byteAt_namesSlot bytes (k+2) S) (fun _ =>
        NamesSlot.bind (byteAt_namesSlot bytes (k+3) S) (fun _ => NamesSlot.ok _ S))))
theorem popStack_not_slotFault (stack : List QVMFr) (idx s j : Nat) :
    Midfall.Generator.popStack stack idx ≠ .error (QVMFault.constSlotOutOfRange s j) := by
  unfold Midfall.Generator.popStack
  cases stack with
  | cons v rest => show Except.ok (v, rest) ≠ _; intro h2; cases h2
  | nil => show Except.error _ ≠ _; intro h2; cases h2
theorem popStack_namesSlot (stack : List QVMFr) (idx : Nat) (S : List Nat) :
    NamesSlot (Midfall.Generator.popStack stack idx) S :=
  NamesSlot.never S (popStack_not_slotFault stack idx)
theorem fqFromU256_not_slotFault (v : Midfall.Word256) (s j : Nat) :
    Midfall.Generator.fqFromU256 v ≠ .error (QVMFault.constSlotOutOfRange s j) := by
  unfold Midfall.Generator.fqFromU256
  by_cases h : v.toNat < qvmFrModulus
  · rw [if_pos h]; intro h2; cases h2
  · rw [if_neg h]; intro h2; cases h2
theorem constAt_slotFault {consts : List Midfall.Word256} {slot idx s j : Nat}
    (h : Midfall.Generator.constAt consts slot idx =
        .error (QVMFault.constSlotOutOfRange s j)) : s = slot := by
  unfold Midfall.Generator.constAt at h
  cases hcs : consts.drop slot with
  | cons v rest =>
      rw [hcs] at h
      exact absurd h (fqFromU256_not_slotFault v s j)
  | nil =>
      rw [hcs] at h
      have h2 := Except.error.inj h
      cases h2
      rfl
theorem constAt_namesSlot {consts : List Midfall.Word256} (slot idx : Nat) (S : List Nat)
    (h : slot ∈ S) : NamesSlot (Midfall.Generator.constAt consts slot idx) S := by
  intro s j hh
  have : s = slot := constAt_slotFault hh
  subst this
  exact h

/-! #### Bridges: the two readers name the same byte -/

theorem drop_succ_tail {l : List Nat} (k : Nat) : l.drop (k+1) = (l.drop k).tail := by
  induction l generalizing k with
  | nil => simp [List.drop]
  | cons a rest ih =>
      cases k with
      | zero => rfl
      | succ j => show rest.drop (j+1) = (rest.drop j).tail; exact ih j

theorem drop_cons_of_byteAt_ok {bytes : List Nat} {k b : Nat}
    (h : Midfall.Generator.byteAt bytes k = .ok b) :
    ∃ rest, bytes.drop k = b :: rest := by
  unfold Midfall.Generator.byteAt at h
  cases hcs : bytes.drop k with
  | cons c rest =>
      rw [hcs] at h
      have hc : c = b := by simpa using h
      rw [← hc]
      exact ⟨rest, rfl⟩
  | nil =>
      rw [hcs] at h
      cases h

theorem drop_cons_of_byteAtPanic_ok {bytes : List Nat} {k b line : Nat}
    (h : Midfall.Generator.QuotientValidator.byteAtPanic bytes k line = .ok b) :
    ∃ rest, bytes.drop k = b :: rest := by
  unfold Midfall.Generator.QuotientValidator.byteAtPanic at h
  cases hcs : bytes.drop k with
  | cons c rest =>
      rw [hcs] at h
      have hc : c = b := by simpa using h
      rw [← hc]
      exact ⟨rest, rfl⟩
  | nil =>
      rw [hcs] at h
      cases h

theorem byteAt_iff_byteAtPanic {bytes : List Nat} {k b line : Nat} :
    Midfall.Generator.byteAt bytes k = .ok b ↔
      Midfall.Generator.QuotientValidator.byteAtPanic bytes k line = .ok b := by
  constructor
  · intro h
    obtain ⟨rest, heq⟩ := drop_cons_of_byteAt_ok h
    unfold Midfall.Generator.QuotientValidator.byteAtPanic
    rw [heq]
  · intro h
    obtain ⟨rest, heq⟩ := drop_cons_of_byteAtPanic_ok h
    unfold Midfall.Generator.byteAt
    rw [heq]

theorem readU16_iff_readU16 {bytes : List Nat} {k v : Nat} :
    Midfall.Generator.readU16 bytes k = .ok v ↔
      Midfall.Generator.QuotientValidator.readU16 bytes k = .ok v := by
  constructor
  · intro h
    unfold Midfall.Generator.readU16 at h
    obtain ⟨b0, hb0, hrest⟩ := peel_bind h
    obtain ⟨b1, hb1, hv⟩ := peel_bind hrest
    have hv' : v = b0 * 256 + b1 := (Except.ok.inj hv).symm
    obtain ⟨r, hr⟩ := drop_cons_of_byteAt_ok hb0
    obtain ⟨r2, hr2⟩ := drop_cons_of_byteAt_ok hb1
    have hmid : r = b1 :: r2 := by
      have hq : bytes.drop (k+1) = (bytes.drop k).tail := @drop_succ_tail bytes k
      rw [hr] at hq
      rw [hq] at hr2
      exact hr2
    unfold Midfall.Generator.QuotientValidator.readU16
    rw [hv', hr, hmid]
  · intro h
    unfold Midfall.Generator.QuotientValidator.readU16 at h
    cases hcs : bytes.drop k with
    | cons b0 rest =>
        cases hrest : rest with
        | cons b1 rest2 =>
            rw [hcs, hrest] at h
            have hv : v = b0 * 256 + b1 := (Except.ok.inj h).symm
            have h1 : bytes.drop k = b0 :: b1 :: rest2 := by rw [hcs, hrest]
            have h2 : bytes.drop (k+1) = b1 :: rest2 := by
              have := @drop_succ_tail bytes k
              rwa [h1] at this
            have hb0 : Midfall.Generator.byteAt bytes k = .ok b0 := by
              unfold Midfall.Generator.byteAt
              rw [h1]
            have hb1 : Midfall.Generator.byteAt bytes (k+1) = .ok b1 := by
              unfold Midfall.Generator.byteAt
              rw [h2]
            rw [hv]
            unfold Midfall.Generator.readU16
            rw [hb0, hb1]
            rfl
        | nil => rw [hcs, hrest] at h; cases h
    | nil => rw [hcs] at h; cases h

/-! #### Membership -/

theorem mem_walkerKonstSlots_narrow {bytes : List Nat} {idx op slot : Nat}
    (h : QuotientOperand.konst slot false ∈ operandList bytes idx op) :
    slot ∈ walkerKonstSlots bytes idx op := by
  unfold walkerKonstSlots
  refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
  simp

theorem mem_walkerKonstSlots_wide {bytes : List Nat} {idx op slot : Nat}
    (h : QuotientOperand.konst slot true ∈ operandList bytes idx op) :
    slot ∈ walkerKonstSlots bytes idx op := by
  unfold walkerKonstSlots
  refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
  simp


/-! #### The 19 non-folded static arms -/

theorem affineProductTerm_namesSlot {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {k : Nat} {S : List Nat}
    (h : ∀ b, Midfall.Generator.byteAt bytes (k + 4) = .ok b → b ∈ S) :
    NamesSlot (Midfall.Generator.affineProductTerm bytes consts mem k) S := by
  unfold Midfall.Generator.affineProductTerm
  refine NamesSlot.bind (readU16_namesSlot bytes k S) (fun _ =>
    NamesSlot.bind (readU16_namesSlot bytes (k+2) S) (fun _ =>
      NamesSlot.bind2 (Midfall.Generator.byteAt bytes (k+4)) _
        (byteAt_namesSlot bytes (k+4) S) (fun b hb =>
          NamesSlot.bind (constAt_namesSlot b k S (h b hb)) (fun _ => NamesSlot.ok _ S))))

theorem affineLinearTerm_namesSlot {bytes : List Nat} {consts : List Midfall.Word256}
    {mem : QuotientRefMemory} {k : Nat} {S : List Nat}
    (h : ∀ b, Midfall.Generator.byteAt bytes (k + 2) = .ok b → b ∈ S) :
    NamesSlot (Midfall.Generator.affineLinearTerm bytes consts mem k) S := by
  unfold Midfall.Generator.affineLinearTerm
  refine NamesSlot.bind (readU16_namesSlot bytes k S) (fun _ =>
    NamesSlot.bind2 (Midfall.Generator.byteAt bytes (k+2)) _
      (byteAt_namesSlot bytes (k+2) S) (fun b hb =>
        NamesSlot.bind (constAt_namesSlot b k S (h b hb)) (fun _ => NamesSlot.ok _ S)))

/-- The walker-side extraction: a single narrow slot read at position p. -/
theorem walk_one_narrow {bytes : List Nat} {idx p line op : Nat}
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os)
    (hw' : Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op =
      (Midfall.Generator.QuotientValidator.byteAtPanic bytes p line >>= fun s =>
        .ok [QuotientOperand.konst s false])) :
    ∃ s, Midfall.Generator.QuotientValidator.byteAtPanic bytes p line = .ok s ∧
      walkerKonstSlots bytes idx op = [s] := by
  obtain ⟨os, hos⟩ := hw
  rw [hw'] at hos
  obtain ⟨s, hs, hos'⟩ := peel_bind hos
  refine ⟨s, hs, ?_⟩
  unfold walkerKonstSlots
  have : operandList bytes idx op = [QuotientOperand.konst s false] := by
    unfold operandList
    rw [hw', hos]
    exact (Except.ok.inj hos').symm
  rw [this]
  rfl

/-- The walker-side extraction: a single wide slot read at position p. -/
theorem walk_one_wide {bytes : List Nat} {idx p op : Nat}
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os)
    (hw' : Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op =
      (Midfall.Generator.QuotientValidator.readU16 bytes p >>= fun s =>
        .ok [QuotientOperand.konst s true])) :
    ∃ s, Midfall.Generator.QuotientValidator.readU16 bytes p = .ok s ∧
      walkerKonstSlots bytes idx op = [s] := by
  obtain ⟨os, hos⟩ := hw
  rw [hw'] at hos
  obtain ⟨s, hs, hos'⟩ := peel_bind hos
  refine ⟨s, hs, ?_⟩
  unfold walkerKonstSlots
  have : operandList bytes idx op = [QuotientOperand.konst s true] := by
    unfold operandList
    rw [hw', hos]
    exact (Except.ok.inj hos').symm
  rw [this]
  rfl

/-- The walker-side extraction: two u16 reads then one narrow slot. -/
theorem walk_two_mem_one_narrow {bytes : List Nat} {idx p1 p2 p3 line op : Nat}
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os)
    (hw' : Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op =
      (Midfall.Generator.QuotientValidator.readU16 bytes p1 >>= fun lhs =>
        Midfall.Generator.QuotientValidator.readU16 bytes p2 >>= fun rhs =>
          .ok [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
               QuotientOperand.konst p3 false])) :
    walkerKonstSlots bytes idx op = [p3] := by
  obtain ⟨os, hos⟩ := hw
  rw [hw'] at hos
  obtain ⟨lhs, hl, h1⟩ := peel_bind hos
  obtain ⟨rhs, hr, hos'⟩ := peel_bind h1
  unfold walkerKonstSlots
  have : operandList bytes idx op =
      [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
       QuotientOperand.konst p3 false] := by
    unfold operandList
    rw [hw', hos]
    exact (Except.ok.inj hos').symm
  rw [this]
  rfl

theorem evalQuotientIdentityStep_constSlot_namedByWalker
    (bytes : List Nat) (consts : List Midfall.Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory)
    (hop : op = qOpPushConst \/ op = qOpPushMemLiteral \/ op = qOpPushMemToken \/ op = qOpPushMemTokenOffset \/ op = qOpPushMemU16 \/ op = qOpAdd \/ op = qOpMul \/ op = qOpNeg \/ op = qOpPushConstU8 \/ op = qOpAddConstU8 \/ op = qOpMulConstU8 \/ op = qOpAddConst \/ op = qOpMulConst \/ op = qOpAddMemU16 \/ op = qOpMulMemU16 \/ op = qOpAddMulMemMemConstU8 \/ op = qOpAddMulConstU8MemU16 \/ op = qOpAddMulMemMem \/ op = qOpPow5)
    (hw : ∃ os, Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx op = .ok os) :
    NamesSlot (Midfall.Generator.evalQuotientIdentityStep bytes consts idx op stack mem)
      (walkerKonstSlots bytes idx op) := by
  rcases hop with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
  · subst h
    obtain ⟨s', hs', hslots⟩ := walk_one_wide (p := idx+1) hw (by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte])
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rw [hslots]
    refine NamesSlot.bind2 (Midfall.Generator.readU16 bytes (idx+1)) _ (readU16_namesSlot bytes (idx+1) [s'])
      (fun a ha => ?_)
    have h2 : Midfall.Generator.readU16 bytes (idx+1) = .ok s' := readU16_iff_readU16.mpr hs'
    have : a = s' := Except.ok.inj (ha.symm.trans h2)
    subst this
    exact NamesSlot.bind (constAt_namesSlot a idx [a] (by simp)) (fun _ => NamesSlot.ok _ [a])
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (readU32_namesSlot bytes (idx+1) _) (fun _ => NamesSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (byteAt_namesSlot bytes (idx+1) _) (fun _ => NamesSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (byteAt_namesSlot bytes (idx+1) _) (fun _ =>
      NamesSlot.bind (readU32_namesSlot bytes (idx+2) _) (fun _ => NamesSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (readU16_namesSlot bytes (idx+1) _) (fun _ => NamesSlot.ok _ _)
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (popStack_namesSlot stack idx _) (fun x =>
      NamesSlot.bind (popStack_namesSlot x.2 idx _) (fun _ => NamesSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (popStack_namesSlot stack idx _) (fun x =>
      NamesSlot.bind (popStack_namesSlot x.2 idx _) (fun _ => NamesSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ => NamesSlot.ok _ _)
  · subst h
    obtain ⟨s', hs', hslots⟩ := walk_one_narrow (p := idx+1) (line := 2369) hw (by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte])
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rw [hslots]
    refine NamesSlot.bind2 (Midfall.Generator.byteAt bytes (idx+1)) _ (byteAt_namesSlot bytes (idx+1) [s'])
      (fun a ha => ?_)
    have h2 : Midfall.Generator.byteAt bytes (idx+1) = .ok s' := byteAt_iff_byteAtPanic.mpr hs'
    have : a = s' := Except.ok.inj (ha.symm.trans h2)
    subst this
    exact NamesSlot.bind (constAt_namesSlot a idx [a] (by simp)) (fun _ => NamesSlot.ok _ [a])
  · subst h
    obtain ⟨s', hs', hslots⟩ := walk_one_narrow (p := idx+1) (line := 2369) hw (by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte])
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rw [hslots]
    refine NamesSlot.bind2 (Midfall.Generator.byteAt bytes (idx+1)) _ (byteAt_namesSlot bytes (idx+1) [s'])
      (fun a ha => ?_)
    have h2 : Midfall.Generator.byteAt bytes (idx+1) = .ok s' := byteAt_iff_byteAtPanic.mpr hs'
    have : a = s' := Except.ok.inj (ha.symm.trans h2)
    subst this
    exact NamesSlot.bind (constAt_namesSlot a idx [a] (by simp)) (fun _ =>
      NamesSlot.bind (popStack_namesSlot stack idx [a]) (fun _ => NamesSlot.ok _ [a]))
  · subst h
    obtain ⟨s', hs', hslots⟩ := walk_one_narrow (p := idx+1) (line := 2369) hw (by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte])
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rw [hslots]
    refine NamesSlot.bind2 (Midfall.Generator.byteAt bytes (idx+1)) _ (byteAt_namesSlot bytes (idx+1) [s'])
      (fun a ha => ?_)
    have h2 : Midfall.Generator.byteAt bytes (idx+1) = .ok s' := byteAt_iff_byteAtPanic.mpr hs'
    have : a = s' := Except.ok.inj (ha.symm.trans h2)
    subst this
    exact NamesSlot.bind (constAt_namesSlot a idx [a] (by simp)) (fun _ =>
      NamesSlot.bind (popStack_namesSlot stack idx [a]) (fun _ => NamesSlot.ok _ [a]))
  · subst h
    obtain ⟨s', hs', hslots⟩ := walk_one_wide (p := idx+1) hw (by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte])
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rw [hslots]
    refine NamesSlot.bind2 (Midfall.Generator.readU16 bytes (idx+1)) _ (readU16_namesSlot bytes (idx+1) [s'])
      (fun a ha => ?_)
    have h2 : Midfall.Generator.readU16 bytes (idx+1) = .ok s' := readU16_iff_readU16.mpr hs'
    have : a = s' := Except.ok.inj (ha.symm.trans h2)
    subst this
    exact NamesSlot.bind (constAt_namesSlot a idx [a] (by simp)) (fun _ =>
      NamesSlot.bind (popStack_namesSlot stack idx [a]) (fun _ => NamesSlot.ok _ [a]))
  · subst h
    obtain ⟨s', hs', hslots⟩ := walk_one_wide (p := idx+1) hw (by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte])
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    rw [hslots]
    refine NamesSlot.bind2 (Midfall.Generator.readU16 bytes (idx+1)) _ (readU16_namesSlot bytes (idx+1) [s'])
      (fun a ha => ?_)
    have h2 : Midfall.Generator.readU16 bytes (idx+1) = .ok s' := readU16_iff_readU16.mpr hs'
    have : a = s' := Except.ok.inj (ha.symm.trans h2)
    subst this
    exact NamesSlot.bind (constAt_namesSlot a idx [a] (by simp)) (fun _ =>
      NamesSlot.bind (popStack_namesSlot stack idx [a]) (fun _ => NamesSlot.ok _ [a]))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (readU16_namesSlot bytes (idx+1) _) (fun _ =>
      NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ => NamesSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (readU16_namesSlot bytes (idx+1) _) (fun _ =>
      NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ => NamesSlot.ok _ _))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ =>
      NamesSlot.bind (affineProductTerm_namesSlot (fun b hb => ?_)) (fun _ => NamesSlot.ok _ _))
    obtain ⟨os, hos⟩ := hw
    have hw' : Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx qOpAddMulMemMemConstU8 =
        (Midfall.Generator.QuotientValidator.readU16 bytes (idx+1) >>= fun lhs =>
          Midfall.Generator.QuotientValidator.readU16 bytes (idx+3) >>= fun rhs =>
            Midfall.Generator.QuotientValidator.byteAtPanic bytes (idx+5) 2393 >>= fun slot =>
              .ok [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
                   QuotientOperand.konst slot false]) := by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte]
    rw [hw'] at hos
    obtain ⟨lhs, hl, h1⟩ := peel_bind hos
    obtain ⟨rhs, hr, h2⟩ := peel_bind h1
    obtain ⟨s', hs', hos'⟩ := peel_bind h2
    have hos2 : os = [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
        QuotientOperand.konst s' false] := (Except.ok.inj hos').symm
    have hmem : QuotientOperand.konst s' false ∈ operandList bytes idx qOpAddMulMemMemConstU8 := by
      unfold operandList
      rw [hw', hos, hos2]
      simp
    have h2b : Midfall.Generator.byteAt bytes (idx+5) = .ok s' := byteAt_iff_byteAtPanic.mpr hs'
    have h3 : Midfall.Generator.byteAt bytes (idx + 1 + 4) = .ok b := hb
    have h4 : idx + 1 + 4 = idx + 5 := by ring
    rw [h4] at h3
    have hb : b = s' := Except.ok.inj (h3.symm.trans h2b)
    rw [hb]
    unfold walkerKonstSlots
    exact List.mem_filterMap.mpr ⟨_, hmem, by simp⟩
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ =>
      NamesSlot.bind (affineLinearTerm_namesSlot (fun b hb => ?_)) (fun _ => NamesSlot.ok _ _))
    obtain ⟨os, hos⟩ := hw
    have hw' : Midfall.Generator.QuotientValidator.visitQuotientOperands bytes idx qOpAddMulConstU8MemU16 =
        (Midfall.Generator.QuotientValidator.readU16 bytes (idx+1) >>= fun ptr =>
          Midfall.Generator.QuotientValidator.byteAtPanic bytes (idx+3) 2398 >>= fun slot =>
            .ok [QuotientOperand.mem "u16" ptr, QuotientOperand.konst slot false]) := by
      unfold Midfall.Generator.QuotientValidator.visitQuotientOperands
      simp (config := {decide := true}) only [reduceIte]
    rw [hw'] at hos
    obtain ⟨ptr, hp, h1⟩ := peel_bind hos
    obtain ⟨s', hs', hos'⟩ := peel_bind h1
    have hos2 : os = [QuotientOperand.mem "u16" ptr, QuotientOperand.konst s' false] :=
      (Except.ok.inj hos').symm
    have hmem : QuotientOperand.konst s' false ∈ operandList bytes idx qOpAddMulConstU8MemU16 := by
      unfold operandList
      rw [hw', hos, hos2]
      simp
    have h2b : Midfall.Generator.byteAt bytes (idx+3) = .ok s' := byteAt_iff_byteAtPanic.mpr hs'
    have h3 : Midfall.Generator.byteAt bytes (idx + 1 + 2) = .ok b := hb
    have h4 : idx + 1 + 2 = idx + 3 := by ring
    rw [h4] at h3
    have hb : b = s' := Except.ok.inj (h3.symm.trans h2b)
    rw [hb]
    unfold walkerKonstSlots
    exact List.mem_filterMap.mpr ⟨_, hmem, by simp⟩
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (readU16_namesSlot bytes (idx+1) _) (fun _ =>
      NamesSlot.bind (readU16_namesSlot bytes (idx+3) _) (fun _ =>
        NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ => NamesSlot.ok _ _)))
  · subst h
    unfold Midfall.Generator.evalQuotientIdentityStep
    simp (config := {decide := true}) only [reduceIte]
    refine NamesSlot.bind (popStack_namesSlot stack idx _) (fun _ => NamesSlot.ok _ _)

/-- D-P23 SATISFIABILITY HALF, as a theorem. The correspondence lemma's hypotheses are
    satisfiable at a witness where its conclusion is not vacuous: PUSH_CONST_U8 over a two-byte
    program and an EMPTY constant table really does fault 'constSlotOutOfRange 3 0', the byte
    at index 1 is 3 and the table has no entry 3 - and the walker really does name slot 3, so
    the membership the lemma claims is a claim about a fault that actually happens. -/
theorem const_slot_correspondence_hypotheses_satisfiable :
    Midfall.Generator.evalQuotientIdentityStep [qOpPushConstU8, 3] ([] : List Midfall.Word256)
        0 qOpPushConstU8 ([] : List QVMFr) armsWitnessMem
        = .error (QVMFault.constSlotOutOfRange 3 0)
      ∧ walkerKonstSlots [qOpPushConstU8, 3] 0 qOpPushConstU8 = [3] := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- D-P23 FALSIFICATION HALF, as a theorem. The 'hw' hypothesis is load-bearing, and the
    conclusion is a real exclusion rather than an unfalsifiable one. LIN7 on a FOUR-byte
    program with an empty table faults 'constSlotOutOfRange 0 1' at limb term 0 - the byte at
    index 1 is 0 and the table is empty - while the walker PANICS at term 1, whose u16 pointer
    runs off the end, and so names no slot at all. There 'slot ∈ walkerKonstSlots' is FALSE,
    so the lemma is not satisfied by a vacuous membership: the walker-success hypothesis is
    exactly what separates the hole's reach (a validated program, where phase 2 walked every
    instruction) from this case. Third time the same asymmetry appears from a new direction:
    section 7 met the interpreter refusing shapes the walker walks, section 8 the reads, here
    the walker refusing bytes the interpreter never reaches. -/
theorem const_slot_correspondence_needs_walker_success :
    Midfall.Generator.evalQuotientIdentityStep (qOpLin7 :: List.replicate 3 0)
        ([] : List Midfall.Word256) 0 qOpLin7 ([] : List QVMFr) armsWitnessMem
        = .error (QVMFault.constSlotOutOfRange 0 1)
      ∧ walkerKonstSlots (qOpLin7 :: List.replicate 3 0) 0 qOpLin7 = [] := by
  refine ⟨?_, ?_⟩ <;> rfl

/-! ### VALP2: the whole-to-part fact for a segment, and the alignment it secretly needs

    THE QUESTION THE ROW ASKS. 'operands_ok_of_validated' gives 'checkQuotientOperand' at every
    instruction of the WHOLE program bytes; the row needs it on the SEGMENT
    '((bytes.drop cursor).take (exprEnd - cursor))'. THE INDEX ARITHMETIC, ON PAPER FIRST: the segment
    is a 'take' of a 'drop', so instruction 'j' of the SEGMENT is instruction 'cursor + j' of the
    WHOLE - never 'j'. Every read of the segment at position 'p' is a read of the whole at position
    'cursor + p' ('byteAtPanic_drop', 'quotientReadU16_drop', 'quotientReadU32_drop', all PROVED with
    no hypothesis), which is the same shift and the reason the offset in the statement below is
    'cursor + i'. -/

/-- The two spellings of the program bytes the row has to reconcile: 'supportedQvm' validates
    'bytesToList q.build.bytes' while the segment is cut out of 'qvmBytesToNats q.build.bytes'. Same
    definition, so the bridge is 'rfl' - but it has to be NAMED, or the first card that tries the
    whole-to-part step loses an hour to a mismatch that is not a mismatch. -/
theorem valp2_bytesToList_eq_qvmBytesToNats (bs : Midfall.Bytes) :
    Midfall.Generator.bytesToList bs = qvmBytesToNats bs := rfl

/-- **THE NATURAL WHOLE-TO-PART STATEMENT, AND IT IS FALSE** (card VALP2). Stated here in full, with
    the correct 'cursor + i' offset, so that the record contains the shape someone would otherwise
    prove: from 'checkQuotientOperand' passing on every instruction of the whole bytes, every operand
    of every instruction of the drop-take segment passes at its shifted cursor.

    REFUTED, not weakened. 'valp2_heredityFails_measure' (VmValidator.lean) measures a four-byte program
    that validates, a cursor of 1 in the middle of its first instruction, and a segment that decodes
    'PUSH_CONST_U8 0x80' - a slot outside the model's 100-entry constant table. The segment's operand
    fails at BOTH cursors 0 and 1 ('valp2_segmentOperandFails',
    'valp2_segmentOperandFails_atWholeIndex'), so no choice of offset rescues the statement. The
    reason is structural and it is a CONTRACT FACT about 'supportedQvm': phase 1 walks from offset 0
    and phase 2 checks the instructions THAT walk names, so 'supportedQvm' says nothing at all about
    a buffer cut at an arbitrary cursor. -/
def PG_valp2_naturalWholeToPart : Prop :=
  ∀ (bytes : List Nat) (model : QuotientOperandModel) (cursor exprEnd : Nat),
    validateQuotientProgramOperands bytes model = .ok () →
    ∀ (i : Nat) (op : Nat),
      (i, op) ∈ bytecodeOpList ((bytes.drop cursor).take (exprEnd - cursor)) →
      ∀ operand ∈ operandList ((bytes.drop cursor).take (exprEnd - cursor)) i op,
        checkQuotientOperand model (cursor + i) operand = .ok ()

/-- **WHAT THE SEGMENT ACTUALLY NEEDS: ALIGNMENT.** The missing hypothesis is not about the operand
    check at all, it is about the WALK: the segment's instructions have to be instructions the whole
    program's phase-1 walk also names, at the shifted cursors. Two conjuncts, both about the walk and
    the operand reads and neither about any bound:

      * 'shift' - every '(i, op)' the segment walk names has its whole-program twin '(cursor + i, op)';
      * 'reads' - the operand list of that instruction is the SAME LIST of operands in both buffers.

    'reads' is where the 'take' bites: a segment instruction whose operand reads run past 'exprEnd'
    reads 'none' in the segment and a real byte in the whole. It is harmless here only because every
    validator reader is panic-class, so a truncated read errors and 'operandList' - the TOTAL reading -
    is then empty and the obligation is vacuous. The drop-congruence lemmas in 'VmValidator.lean' are
    exactly the ingredients of 'reads' for the drop; the 'take' leg and the 'shift' leg are both
    inductions over 'quotientBytecodeOpsGo', and 'shift' additionally needs the boundary fact that the
    whole-program walk passes through 'cursor' - which NOTHING in the tree connects to 'itemStarts'. -/
def PG_valp2_walkAlignment (bytes seg : List Nat) (cursor : Nat) : Prop :=
  (∀ i op, (i, op) ∈ bytecodeOpList seg → (cursor + i, op) ∈ bytecodeOpList bytes) ∧
    (∀ i op, (i, op) ∈ bytecodeOpList seg →
        operandList seg i op = operandList bytes (cursor + i) op)

/-- **THE WHOLE-TO-PART FACT, PROVED, WITH THE OFFSET.** Given the alignment - which is a hypothesis on
    THIS LEMMA, never on the row, on a bundle, on 'ValidV3' or on the root (RULES) - the operand check
    that 'supportedQvm' bought on the whole program transfers to every operand of every instruction of
    the segment, at the shifted cursor 'cursor + i'. The proof is eight lines: it is a reindexing, and
    all of the work is in 'PG_valp2_walkAlignment'. -/
theorem operands_ok_of_validated_segment {bytes seg : List Nat}
    {model : QuotientOperandModel} {cursor : Nat}
    (hval : validateQuotientProgramOperands bytes model = .ok ())
    (halign : PG_valp2_walkAlignment bytes seg cursor) :
    ∀ i op, (i, op) ∈ bytecodeOpList seg →
      ∀ operand ∈ operandList seg i op,
        checkQuotientOperand model (cursor + i) operand = .ok () := by
  obtain ⟨hmem, hreads⟩ := halign
  obtain ⟨ops, ho, hall⟩ := operands_ok_of_validated hval
  have hlist : bytecodeOpList bytes = ops.map (fun (idx, op, _len) => (idx, op)) := by
    simp [bytecodeOpList, ho]
  intro i op hi operand hop
  have hmem' : (cursor + i, op) ∈ ops.map (fun (idx, op, _len) => (idx, op)) :=
    hlist ▸ hmem i op hi
  have hgoal := hall (cursor + i, op) hmem'
  rw [← hreads i op hi] at hgoal
  exact hgoal operand hop

/-- The same fact in the row's own vocabulary: 'supportedQvm' really does buy the whole-program
    operand check for the model the plan builds, with no 'Bool' in sight. The unfolding is the one
    'qvm_validated_windows' performs; only the tail differs. -/
theorem operands_ok_of_supported {Program Layout : Type}
    (model : QuotientOperandModel)
    (L : Midfall.Generator.LoweringPlan Program Layout)
    (hvm : L.lowering = Midfall.Generator.QuotientLowering.vm)
    (q : Midfall.Generator.PlannedQuotient) (hq : L.quotient = some q)
    (hmodel : Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
      q.build q.plan.selectorFold = .ok model)
    (hvalidated : Midfall.Generator.LoweringPlan.supportedQvm L) :
    validateQuotientProgramOperands (Midfall.Generator.bytesToList q.build.bytes) model = .ok () := by
  have hsup : L.supportedQvmBool = true := hvalidated
  have hsb : L.supportedQvmBool =
      match L.quotient with
      | none => false
      | some q =>
          match Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
              q.build q.plan.selectorFold with
          | .error _ => false
          | .ok model =>
              match validateQuotientProgramOperands (bytesToList q.build.bytes) model with
              | .ok _ => true
              | .error _ => false := by
    unfold LoweringPlan.supportedQvmBool
    rw [hvm]
    rfl
  rw [hsb] at hsup
  rw [hq] at hsup
  dsimp only at hsup
  rw [hmodel] at hsup
  cases hx : validateQuotientProgramOperands (bytesToList q.build.bytes) model with
  | ok u =>
      cases u
      rfl
  | error f => simp [hx] at hsup

#print axioms Midfall.Lowering.operands_ok_of_validated_segment
#print axioms Midfall.Lowering.operands_ok_of_supported
#print axioms Midfall.Lowering.valp2_bytesToList_eq_qvmBytesToNats

/-! ### (A1) THE ALIGNMENT BRIDGE: the itemStarts cursors and the validator walk offsets

    THE JOB (card ALIGN, blocker (A1) of the 'qvm_validated_noBoundsFault' row, QvmNoBounds.lean:102).
    VALP2 proved the naive whole-to-part lemma FALSE and named what replaces it:
    'PG_valp2_walkAlignment' (Qvm.lean:2882), whose first leg says that every instruction the segment
    walk names is an instruction the WHOLE program's phase-1 walk names at the shifted cursor. That leg
    is only statable once the segment's cursor is known to be an offset the validator's walk visits.
    (A1) is that bridge.

    THE FINDING, FIRST, BECAUSE IT CHANGES WHAT (A1) IS. The two walks do NOT step by the same function.
    'quotientBytecodeOpsGo' (VmValidator.lean:681) steps by 'QuotientValidator.quotientOpLen'
    (VmValidator.lean:651, error type 'VResult = Except QuotientValidationFault'), while 'itemStartsGo'
    (Qvm.lean:659) and 'identitySegment' (VmCertify.lean:409) step by 'QuotientBuilder.quotientOpLen'
    (VmBuilder.lean:1287, error type 'M = Except QVMFault') - P-09c's COMPACT-SCOPED COPY, the duplicate
    that VmValidator.lean:646 says "P-09d owns the general walker and should absorb". Before this card
    the only evidence the two agreed was the corpus Bool 'quotientOpLen_agreesWithScopedCopy_ok'
    (VmValidator.lean:2153), which measures fixtures and proves nothing. So (A1) as briefed was not
    merely unproved: with 'itemStarts' naming the cursors of one walk and 'bytecodeOpList' the offsets of
    another, it was not statable. 'align_opLen_toOption' below turns the agreement into a THEOREM (all
    five arms, both error monads, no axioms beyond propext and Quot.sound), and that is what makes the
    bridge expressible at all. The copies differ in their error PAYLOADS and in nothing a stride can see,
    which is why the right form is agreement of '.toOption' and not equality.

    THE SECOND FINDING: THE ALIGNMENT IS AN INCLUSION, NOT AN EQUALITY. Measured on the certifier's
    three-identity fixture ('align_fixture_measure'): the validator names
    [0, 3, 6, 7, 10, 12, 16, 19, 21, 22] and 'itemStarts' names [0, 7, 16]. Every item start IS a
    validator offset - the alignment is true, and the row needs exactly this direction - but the
    validator names strictly more (every intra-segment instruction and every fold opcode), and
    'itemStartsGo' records a cursor whose step errored even when that cursor is past the end of the
    buffer ('align_reverse_inclusion_fails_measure'), which is why every statement carries the
    in-bounds guard. Anyone who reads (A1) as "the two offset sets are equal" is reading a false
    statement.

    WHAT IS PROVED HERE: the hazard-3 agreement (all five 'quotientOpLen' arms plus the three reader
    pairs), the walk primitives 'align_go_succ'/'align_go_out'/'align_go_fuel0', and the predicate
    'align_names' with its totalised walk 'align_walkFrom'. WHAT IS NAMED, not proved: the one induction
    the bridge reduces to - 'PG_align_walkClosed', closure of the named-offset set under one more step
    of the walk's own length function - and the accumulator identity it needs, 'PG_align_goAccEq'. Both
    are 'def : Prop', so nothing here adds a hole to the register and nothing adds a hypothesis to the
    row, to a bundle, to 'ValidV3' or to the root (RULES). -/

theorem align_tO_ok {α β : Type} (a : α) : (Except.ok a : Except β α).toOption = some a := rfl
theorem align_tO_err {α β : Type} (e : β) : (Except.error e : Except β α).toOption = none := rfl
theorem align_tO_some {α β : Type} {x : Except β α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | ok b => have : b = a := Option.some.inj h; subst this; rfl
  | error e => rw [align_tO_err] at h; exact absurd h (by simp)

/-- Binding two reads in DIFFERENT error monads whose results agree as options, and continuing with
    continuations that agree on the ok value, agrees as options. This is the only way the two
    'quotientOpLen' copies can be compared at all: their error payloads have different types. -/
theorem align_bind_toOption {α β ε δ : Type} {x : Except ε α} {y : Except δ α}
    {f : α → Except ε β} {g : α → Except δ β}
    (h : x.toOption = y.toOption)
    (hag : ∀ a, x = .ok a → (f a).toOption = (g a).toOption) :
    (x >>= f).toOption = (y >>= g).toOption := by
  cases x with
  | ok a =>
      cases y with
      | ok b =>
          rw [align_tO_ok, align_tO_ok] at h
          have hab : a = b := Option.some.inj h
          subst hab
          show (f a).toOption = (g a).toOption
          exact hag a rfl
      | error e' =>
          rw [align_tO_ok, align_tO_err] at h
          exact absurd h (by simp)
  | error e =>
      cases y with
      | ok b =>
          rw [align_tO_err, align_tO_ok] at h
          exact absurd h (by simp)
      | error e' => rfl

/-- **HAZARD 3, PART ONE, PROVED.** The two panic-class byte readers agree as options at every index:
    both are 'bytes.drop idx' read one element and differ only in the site string they put in the
    payload. -/
theorem align_byteReader_toOption (bytes : List Nat) (idx line : Nat) :
    (Midfall.Generator.QuotientValidator.byteAtPanic bytes idx line).toOption =
      (Midfall.Generator.QuotientBuilder.walkByte bytes idx).toOption := by
  cases h : bytes.drop idx with
  | cons b rest =>
      simp only [Midfall.Generator.QuotientValidator.byteAtPanic,
        Midfall.Generator.QuotientBuilder.walkByte, h, align_tO_ok]
  | nil =>
      simp only [Midfall.Generator.QuotientValidator.byteAtPanic,
        Midfall.Generator.QuotientBuilder.walkByte, Midfall.Generator.QuotientValidator.vPanic,
        Midfall.Generator.QuotientBuilder.panicAt, h, align_tO_err]

/-- The two panic-class 'u16' readers agree as options: the builder reads two bytes at 'idx' and
    'idx + 1', the validator matches two elements off 'bytes.drop idx', and those are the same
    in-bounds condition with the same value. -/
theorem align_readU16_toOption (bytes : List Nat) (idx : Nat) :
    (Midfall.Generator.QuotientValidator.readU16 bytes idx).toOption =
      (Midfall.Generator.QuotientBuilder.walkReadU16 bytes idx).toOption := by
  have hd1 : bytes.drop (idx+1) = (bytes.drop idx).drop 1 := by rw [List.drop_drop]
  cases h : bytes.drop idx with
  | nil =>
      simp only [Midfall.Generator.QuotientValidator.readU16,
        Midfall.Generator.QuotientBuilder.walkReadU16, Midfall.Generator.QuotientBuilder.walkByte,
        Midfall.Generator.QuotientBuilder.panicAt, Midfall.Generator.QuotientValidator.vPanic,
        h, align_tO_err]
      rfl
  | cons b rest =>
      cases hrest : rest with
      | nil =>
          have hb : bytes.drop (idx+1) = [] := by rw [hd1, h, hrest]; rfl
          simp only [Midfall.Generator.QuotientValidator.readU16,
            Midfall.Generator.QuotientBuilder.walkReadU16, Midfall.Generator.QuotientBuilder.walkByte,
            Midfall.Generator.QuotientBuilder.panicAt, Midfall.Generator.QuotientValidator.vPanic,
            hd1, h, hrest, hb, align_tO_err]
          rfl
      | cons b0 b1 =>
          have hb : bytes.drop (idx+1) = b0 :: b1 := by rw [hd1, h, hrest]; rfl
          simp only [Midfall.Generator.QuotientValidator.readU16,
            Midfall.Generator.QuotientBuilder.walkReadU16, Midfall.Generator.QuotientBuilder.walkByte,
            Midfall.Generator.QuotientValidator.byteAtPanic, hd1, h, hrest, hb, align_tO_ok]
          rfl

/-- The AFFINE_SUM stride agrees between the two copies. -/
theorem align_affineSum_toOption (bytes : List Nat) (idx : Nat) :
    (Midfall.Generator.QuotientValidator.quotientAffineSumOpLen bytes idx).toOption =
      (Midfall.Generator.QuotientBuilder.quotientAffineSumOpLen bytes idx).toOption := by
  unfold Midfall.Generator.QuotientValidator.quotientAffineSumOpLen
    Midfall.Generator.QuotientBuilder.quotientAffineSumOpLen
  refine align_bind_toOption (align_readU16_toOption bytes (idx+1)) ?_
  intro a ha
  refine align_bind_toOption (align_readU16_toOption bytes (idx+3)) ?_
  intro p hp
  rw [align_tO_ok, align_tO_ok]
  simp only [Midfall.Generator.quotientVmByteU16Bytes]

/-- The MODARITH7 stride agrees between the two copies: five count bytes behind two optional fields,
    spelled with 'quotientVmByteU16Bytes' in one copy and the literal 2 in the other. -/
theorem align_modarith7_toOption (bytes : List Nat) (idx : Nat) :
    (Midfall.Generator.QuotientValidator.quotientModarith7OpLen bytes idx).toOption =
      (Midfall.Generator.QuotientBuilder.quotientModarith7OpLen bytes idx).toOption := by
  unfold Midfall.Generator.QuotientValidator.quotientModarith7OpLen
    Midfall.Generator.QuotientBuilder.quotientModarith7OpLen
  refine align_bind_toOption (align_byteReader_toOption bytes (idx+1) 3038) ?_
  intro flags hflags
  refine align_bind_toOption (align_byteReader_toOption bytes _ 3046) ?_
  intro lin hlin
  refine align_bind_toOption (align_byteReader_toOption bytes _ 3047) ?_
  intro row hrow
  refine align_bind_toOption (align_byteReader_toOption bytes _ 3048) ?_
  intro pw hw
  refine align_bind_toOption (align_byteReader_toOption bytes _ 3049) ?_
  intro mem hm
  refine align_bind_toOption (align_byteReader_toOption bytes _ 3050) ?_
  intro prod hp
  rw [align_tO_ok, align_tO_ok]
  simp only [Midfall.Generator.quotientVmByteU16Bytes]

/-- **HAZARD 3 DISCHARGED AS A THEOREM.** The general walker (VmValidator.lean:651, which is what
    'quotientBytecodeOps' steps by) and P-09c's compaction-scoped copy (VmBuilder.lean:1287, which is
    what 'identitySegment' and 'itemStartsGo' step by) return the same length whenever either returns
    one, at every index of every byte list, and both error otherwise. Until this card the only evidence
    was the corpus Bool 'quotientOpLen_agreesWithScopedCopy_ok'. -/
theorem align_opLen_toOption (bytes : List Nat) (idx : Nat) :
    (Midfall.Generator.QuotientValidator.quotientOpLen bytes idx).toOption =
      (Midfall.Generator.QuotientBuilder.quotientOpLen bytes idx).toOption := by
  unfold Midfall.Generator.QuotientValidator.quotientOpLen
    Midfall.Generator.QuotientBuilder.quotientOpLen
  refine align_bind_toOption (align_byteReader_toOption bytes idx 3009) ?_
  intro op hop
  by_cases h1 : op = Midfall.Generator.qOpRunAddMulMemMemConstU8
  · subst h1
    refine align_bind_toOption (align_readU16_toOption bytes (idx+1)) ?_
    intro a _
    rw [align_tO_ok, align_tO_ok]
    simp only [Midfall.Generator.quotientVmByteU16Bytes]
  · by_cases h2 : op = Midfall.Generator.qOpRunAddMulConstU8MemU16
    · subst h2
      refine align_bind_toOption (align_readU16_toOption bytes (idx+1)) ?_
      intro a _
      rw [align_tO_ok, align_tO_ok]
      simp only [Midfall.Generator.quotientVmByteU16Bytes]
    · by_cases h3 : op = Midfall.Generator.qOpAffineSum
      · subst h3
        exact align_affineSum_toOption bytes idx
      · by_cases h4 : op = Midfall.Generator.qOpModarith7
        · subst h4
          exact align_modarith7_toOption bytes idx
        · cases hq : Midfall.Generator.quotientOpcodeByteLen op with
          | some len => simp [hq, h1, h2, h3, h4]; rw [align_tO_ok, align_tO_ok]
          | none =>
              simp [hq, h1, h2, h3, h4, Midfall.Generator.QuotientValidator.vPanic,
                Midfall.Generator.QuotientBuilder.panicAt]
              rw [align_tO_err, align_tO_err]

/-- A successful 'quotientOpLen' in either copy means the index is inside the buffer: both copies open
    with a panic-class read of the opcode byte. -/
theorem align_validatorOpLen_ok_lt (bytes : List Nat) (idx n : Nat)
    (h : Midfall.Generator.QuotientValidator.quotientOpLen bytes idx = .ok n) :
    idx < bytes.length := by
  by_contra hlt
  have hdrop : bytes.drop idx = [] := List.drop_eq_nil_of_le (by omega : bytes.length ≤ idx)
  have h1 : (Midfall.Generator.QuotientValidator.quotientOpLen bytes idx).toOption = none := by
    unfold Midfall.Generator.QuotientValidator.quotientOpLen
      Midfall.Generator.QuotientValidator.byteAtPanic
    rw [hdrop]
    rfl
  rw [h] at h1
  exact absurd h1 (by simp [align_tO_ok])

/-- The builder copy's twin, via hazard 3. -/
theorem align_builderOpLen_ok_lt (bytes : List Nat) (idx n : Nat)
    (h : Midfall.Generator.QuotientBuilder.quotientOpLen bytes idx = .ok n) :
    idx < bytes.length := by
  have h1 : (Midfall.Generator.QuotientBuilder.quotientOpLen bytes idx).toOption = some n := by
    rw [h]; rfl
  have h2 : (Midfall.Generator.QuotientValidator.quotientOpLen bytes idx).toOption = some n := by
    rw [align_opLen_toOption, h1]
  exact align_validatorOpLen_ok_lt bytes idx n (align_tO_some h2)

/-- The builder copy's step length is the validator copy's step length. -/
theorem align_builderOpLen_eq_validator (bytes : List Nat) (idx len : Nat)
    (h : Midfall.Generator.QuotientBuilder.quotientOpLen bytes idx = .ok len) :
    Midfall.Generator.QuotientValidator.quotientOpLen bytes idx = .ok len := by
  have h1 : (Midfall.Generator.QuotientBuilder.quotientOpLen bytes idx).toOption = some len := by
    rw [h]; rfl
  have h2 : (Midfall.Generator.QuotientValidator.quotientOpLen bytes idx).toOption = some len := by
    rw [align_opLen_toOption bytes idx, h1]
  exact align_tO_some h2

/-- The validator's opcode walk started at 'idx' with an explicit fuel, totalised to '[]' where it
    errors. -/
def align_walkFrom (bytes : List Nat) (idx : Nat) : List QuotientBytecodeOp :=
  match quotientBytecodeOpsGo bytes bytes.length idx [] with
  | .ok ops => ops
  | .error _ => []

theorem align_walkFrom_go (bytes : List Nat) (idx : Nat)
    (ops : List QuotientBytecodeOp)
    (h : quotientBytecodeOpsGo bytes bytes.length idx [] = .ok ops) :
    align_walkFrom bytes idx = ops := by
  rw [align_walkFrom, h]

/-- **THE PREDICATE (A1) IS ABOUT.** 'c' is an offset the validator's phase-1 walk names: it read an
    instruction there. Under a successful walk this is exactly membership in 'bytecodeOpList'. -/
def align_names (bytes : List Nat) (c : Nat) : Prop :=
  ∃ t ∈ align_walkFrom bytes 0, t.1 = c

theorem align_go_succ (bytes : List Nat) (k idx : Nat) (acc : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp)
    (hlt : idx < bytes.length) :
    quotientBytecodeOpsGo bytes (k+1) idx acc =
      (Midfall.Generator.QuotientValidator.byteAtPanic bytes idx 3084 >>= fun op =>
       Midfall.Generator.QuotientValidator.quotientOpLen bytes idx >>= fun len =>
       quotientBytecodeOpsGo bytes k (idx + len) ((idx, op, len) :: acc)) := by
  simp [quotientBytecodeOpsGo, hlt]

theorem align_go_out (bytes : List Nat) (fuel idx : Nat)
    (acc : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp)
    (hlt : ¬ (idx < bytes.length)) :
    quotientBytecodeOpsGo bytes fuel idx acc = .ok acc.reverse := by
  cases fuel with
  | zero => simp [quotientBytecodeOpsGo, hlt]
  | succ k => simp [quotientBytecodeOpsGo, hlt]

theorem align_go_fuel0 (bytes : List Nat) (idx : Nat)
    (acc : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp)
    (hlt : idx < bytes.length) :
    quotientBytecodeOpsGo bytes 0 idx acc =
      Midfall.Generator.QuotientValidator.vPanic
        (Midfall.Generator.QuotientValidator.siteIndex 3082) := by
  simp [quotientBytecodeOpsGo, hlt]

theorem align_bind_err {α β ε : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl
theorem align_bind_ok {α β ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-! #### (A1) THE BRIDGE: what it says, and the one fact that is left -/

/-- **(A1), THE BRIDGE, IN THE FORM THE ROW NEEDS.** Every in-bounds cursor that 'itemStarts' names is
    an offset the validator's phase-1 walk names, so the phase-2 operand check that 'supportedQvm'
    bought covers the instruction the segment starts with. Stated as a 'def : Prop' so the obligation
    has ONE address in the tree (the 'QvmNoBounds.lean' shape), and so nothing is hidden behind a
    'sorry'. The in-bounds guard is load-bearing: 'itemStartsGo' records the cursor whose step ERRORED
    before it stops, and such a cursor can be past the end of the buffer - see
    'align_reverse_inclusion_fails_measure'. -/
def PG_align_itemStartsNamed : Prop :=
  ∀ (bytes : List Nat) (ops : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp)
      (plan : QuotientProgramPlan) (build : QuotientProgramBuild),
    quotientBytecodeOps bytes = .ok ops →
    qvmBytesToNats build.bytes = bytes →
    ∀ cursor, cursor ∈ itemStarts plan build → cursor < bytes.length →
      ∃ op, (cursor, op) ∈ bytecodeOpList bytes

/-- The OTHER cursor the row cuts at: the fold opcode that ends the segment is a validator offset too.
    This is what makes 'identitySegment' the right notion of "where the segment ends" for a validator
    statement at all. -/
def PG_align_exprEndNamed : Prop :=
  ∀ (bytes : List Nat) (ops : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp)
      (cursor exprEnd foldOp : Nat),
    quotientBytecodeOps bytes = .ok ops →
    cursor < bytes.length →
    Midfall.Generator.QuotientCertify.identitySegment bytes cursor = .ok (exprEnd, foldOp) →
      ∃ op, (exprEnd, op) ∈ bytecodeOpList bytes

/-- **THE SINGLE FACT BOTH OF THE ABOVE REDUCE TO.** The set of offsets the phase-1 walk names is
    closed under one more step of its own length function: if the walk from 0 succeeds, names 'c',
    'c' is in bounds, and the validator's 'quotientOpLen' steps 'c' to 'c + len' inside the buffer,
    then it names 'c + len' as well. Everything else in (A1) is bookkeeping over 'itemStartsGo' and
    'identitySegment.go', both of which step by the SAME length after 'align_opLen_toOption'.

    WHY IT WAS NOT YET PROVED, exactly: it is an induction over the fuel-indexed
    'quotientBytecodeOpsGo', and the induction has to carry the accumulator - the walk conses onto
    'acc' and reverses it at the end, so a step at depth 'k' hands its successor
    '((idx, op, len) :: acc)', and reading the head triple back out of a result needs
    'go bytes f i acc = match go bytes f i [] with ok r => ok (acc.reverse ++ r) | error e => error e'.
    That equation is stated as 'PG_align_goAccEq' below; the pieces that do NOT need it
    ('align_go_succ', 'align_go_out', 'align_go_fuel0') are PROVED above.

    **WALKC: THIS IS NOW PROVED**, as 'align_walkClosed' below, from 'align_go_closed' over the walk
    history relation 'align_chain'. The statement is untouched: what was missing was the theorem, and the
    in-bounds guard 'c + len < bytes.length' is load-bearing exactly as ALIGN warned - it is what kills
    the arm where a recorded offset's successor is the terminal cursor. -/
def PG_align_walkClosed : Prop :=
  ∀ (bytes : List Nat) (ops : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp)
      (c len : Nat),
    quotientBytecodeOpsGo bytes bytes.length 0 [] = .ok ops →
    (∃ t ∈ ops, t.1 = c) →
    c < bytes.length →
    Midfall.Generator.QuotientValidator.quotientOpLen bytes c = .ok len →
    c + len < bytes.length →
      ∃ t ∈ ops, t.1 = c + len

/-- The accumulator identity 'PG_align_walkClosed' needs, stated exactly. Proved by induction on
    'fuel' after 'align_go_succ'/'align_go_out'; the two error arms of the successor case are the only
    place where the 'do' blocks have to be reduced by hand.

    **WALKC: THIS IS NOW PROVED**, as 'align_goAccEq' below, with no change to the statement. The do
    blocks are NOT reduced by hand and never needed to be: both sides of the equation contain the SAME do
    block, so the accumulator case goes by case-splitting the two actions it binds over
    ('cases h : byteAtPanic bytes idx 3084', 'cases h : quotientOpLen bytes idx') and letting
    'align_bind_ok'/'align_bind_err' - both 'rfl' - do the reduction. -/
def PG_align_goAccEq : Prop :=
  ∀ (bytes : List Nat) (fuel idx : Nat)
      (acc : List Midfall.Generator.QuotientValidator.QuotientBytecodeOp),
    quotientBytecodeOpsGo bytes fuel idx acc =
      match quotientBytecodeOpsGo bytes fuel idx [] with
      | .ok r => .ok (acc.reverse ++ r)
      | .error e => .error e

/-- **THE INCLUSION IS STRICT, BOTH WAYS - MEASURED.** Lines 1-3: on the certifier's three-identity
    fixture the validator's phase-1 walk names ten offsets and 'itemStarts' names three, and the three
    ARE among the ten - that is (A1) holding on a real program, and it is the first time the two walks
    have been put side by side in this tree. Line 4: the seven extra offsets (every intra-segment
    instruction and every fold opcode) are validator offsets that are NOT item starts, so anyone who
    reads (A1) as an EQUALITY of the two offset sets is reading a false statement; the row needs the
    inclusion, and only the inclusion. Hand-measured under 'lake env lean' on this base; deliberately
    NOT a '#eval' gate, because 'kat_gate.py' asserts an exact pin (RULES). -/
def align_fixture_measure : Bool :=
  match Midfall.Generator.QuotientCertifyKats.threeIdentityBuild with
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      let v := (bytecodeOpList bytes).map Prod.fst
      let s := itemStarts Midfall.Generator.QuotientCertifyKats.threeIdentityPlan build
      v == [0, 3, 6, 7, 10, 12, 16, 19, 21, 22] &&
        s == [0, 7, 16] &&
        (s.all fun c => c ∈ v) &&
        (v.filter fun o => ! (o ∈ s)) == [3, 6, 10, 12, 19, 21, 22]
  | .error _ => false

/-- The out-of-bounds arm on its own: an empty program has NO validator offset, but 'itemStartsGo'
    still records the cursor whose step errored. So the guard in 'PG_align_itemStartsNamed' cannot be
    dropped. Measured: 'itemStartsGo [] [nativePermutation] 0 [] = [0]' while 'bytecodeOpList [] = []'. -/
def align_reverse_inclusion_fails_measure : Bool :=
  itemStartsGo ([] : List Nat) [QuotientProgramItem.nativePermutation] 0 [] == [0] &&
    (bytecodeOpList ([] : List Nat)).map Prod.fst == []

/-- **THE FINDING, AS A MEASUREMENT.** The two walks do NOT step by the same function: 'itemStartsGo'
    and 'identitySegment' step by 'QuotientBuilder.quotientOpLen' (VmBuilder.lean:1287, error type
    'M = Except QVMFault' - P-09c's compaction-scoped copy), while 'quotientBytecodeOpsGo' steps by
    'QuotientValidator.quotientOpLen' (VmValidator.lean:651, error type 'VResult = Except
    QuotientValidationFault'). Before this card the ONLY evidence they agreed was the corpus Bool
    'quotientOpLen_agreesWithScopedCopy_ok', which measures fixtures and proves nothing: the two copies
    differ in their error PAYLOADS (different site strings, different fault types) and in nothing a
    stride can see. 'align_opLen_toOption' above turns that into a theorem. Without it (A1) is not
    merely unproved, it is not statable: 'itemStarts' would name the cursors of one walk and
    'bytecodeOpList' the offsets of another. -/
def align_twoCoplanMeasure : Bool :=
    (Midfall.Generator.QuotientBuilder.quotientOpLen [0x05, 0x09, 0x80, 0x0a] 0).toOption =
      (Midfall.Generator.QuotientValidator.quotientOpLen [0x05, 0x09, 0x80, 0x0a] 0).toOption &&
    (Midfall.Generator.QuotientBuilder.quotientOpLen [0x05, 0x09, 0x80, 0x0a] 1).toOption =
      (Midfall.Generator.QuotientValidator.quotientOpLen [0x05, 0x09, 0x80, 0x0a] 1).toOption &&
    (Midfall.Generator.QuotientBuilder.quotientOpLen [0x05, 0x09, 0x80, 0x0a] 3).toOption =
      (Midfall.Generator.QuotientValidator.quotientOpLen [0x05, 0x09, 0x80, 0x0a] 3).toOption

#print axioms Midfall.Lowering.align_opLen_toOption
#print axioms Midfall.Lowering.align_byteReader_toOption
#print axioms Midfall.Lowering.align_readU16_toOption
#print axioms Midfall.Lowering.align_modarith7_toOption
#print axioms Midfall.Lowering.align_builderOpLen_eq_validator

/-! #### WALKC: THE INDUCTION OVER THE FUEL-INDEXED WALK - (A1') CLOSED

    ALIGN named exactly one missing theorem between its primitives and the bridge: the closure of the
    validator's named-offset set under one more step of its own length function, plus the accumulator
    identity that induction needs. Both are PROVED below, so 'PG_align_goAccEq' and 'PG_align_walkClosed'
    are now discharged theorems ('align_goAccEq', 'align_walkClosed'), not named Props. Nothing here
    adds a hypothesis to the row, to a bundle, to 'ValidV3' or to the root (RULES): the Props keep their
    committed statements verbatim and are discharged by a term of exactly that type, so a statement
    drift would stop the file elaborating.

    HOW THE INDUCTION GOES, since this is the fight ALIGN lost. The accumulator identity
    'align_goAccEq_aux' is an induction on 'fuel' with 'idx' and 'acc' generalized, and it needs NOTHING
    that was not already in ALIGN's hands: 'align_go_succ'/'align_go_out'/'align_go_fuel0' split every
    case on the in-bounds test, and the two 'do' blocks on the two sides of the equation are the SAME do
    block, so the accumulator cases never have to be reduced symbolically at all - it is enough to
    'cases h : byteAtPanic bytes idx 3084' and 'cases h : quotientOpLen bytes idx', which substitutes
    into the goal and leaves 'align_bind_ok'/'align_bind_err' to kill the binds, both 'rfl'. THAT is the
    whole way through the do-block fight: never rewrite a do-block, case-split the actions it binds
    over. The two error arms of the successor case are then 'simp only [align_bind_err]' and nothing
    else, and the ok arm is two instances of the IH plus 'reverse_cons' and 'nil_append'.

    'PG_align_walkClosed' then needs one ingredient that is NOT about accumulators: a triple in the
    result carries the length the validator itself assigned at its own offset, so the hypothesis
    'quotientOpLen bytes c = .ok len' pins WHICH triple of offset 'c' it is. That is 'align_go_genuine',
    proved over the inductive relation 'align_chain' - the walk's history, recording that every triple
    was read in bounds with its own correct length and that the cursor after the head triple is the
    current one. 'align_chain_succ' is the one-step-on property of that history: the successor of a
    recorded offset is either recorded too or is the current cursor. With those two the closure
    induction is three lines per case, and the out-of-bounds arm is where the in-bounds guard of the
    Prop pays for itself: a successor equal to the terminal cursor would be past the end, contradicting
    the guard. 'align_go_succ_ok' is the one new peel lemma the in-bounds arm needs, and it is the same
    case-split-the-actions trick.

    AXIOM HYGIENE, AND A FINDING. These theorems depend on [propext, Classical.choice, Quot.sound], and
    the 'Classical.choice' is NOT introduced here: it is in the DEFINITION 'quotientBytecodeOpsGo'
    (VmValidator.lean:681) itself, so EVERY theorem about the walk inherits it - including this row the
    moment it cites one, and including 'align_walkFrom' which ALIGN already committed. The source is the
    redundant 'termination_by fuel => fuel' clause (VmValidator.lean:694) on an already-structural
    recursion: the identical definition with that clause deleted depends on no axioms at all (measured
    both ways in this worktree). Deleting the clause is a one-line change that would make the whole walk
    cone constructive; it is NOT made here because it re-forges a generated port definition that every
    other card's proofs reduce through, and because a killed concurrent rebuild of it is exactly the
    false-KAT-red hazard in RULES. -/

theorem align_goAccEq_aux (bytes : List Nat) :
    ∀ (fuel idx : Nat) (acc : List QuotientBytecodeOp),
      quotientBytecodeOpsGo bytes fuel idx acc =
        match quotientBytecodeOpsGo bytes fuel idx [] with
        | .ok r => .ok (acc.reverse ++ r)
        | .error e => .error e := by
  intro fuel
  induction fuel with
  | zero =>
      intro idx acc
      by_cases hlt : idx < bytes.length
      · rw [align_go_fuel0 bytes idx acc hlt, align_go_fuel0 bytes idx [] hlt]
        unfold Midfall.Generator.QuotientValidator.vPanic
        rfl
      · rw [align_go_out bytes 0 idx acc hlt, align_go_out bytes 0 idx [] hlt]
        simp only [List.reverse_nil, List.append_nil]
  | succ k ih =>
      intro idx acc
      by_cases hlt : idx < bytes.length
      · rw [align_go_succ bytes k idx acc hlt, align_go_succ bytes k idx [] hlt]
        cases h1 : Midfall.Generator.QuotientValidator.byteAtPanic bytes idx 3084 with
        | error e => simp only [align_bind_err]
        | ok op =>
            cases h2 : Midfall.Generator.QuotientValidator.quotientOpLen bytes idx with
            | error e => simp only [align_bind_ok, align_bind_err]
            | ok len =>
                simp only [align_bind_ok]
                rw [ih (idx + len) ((idx, op, len) :: acc), ih (idx + len) ((idx, op, len) :: [])]
                cases h3 : quotientBytecodeOpsGo bytes k (idx + len) [] with
                | ok r =>
                    simp only [List.reverse_cons, List.reverse_nil, List.cons_append,
                      List.append_assoc, List.nil_append]
                | error e => rfl
      · rw [align_go_out bytes (k + 1) idx acc hlt, align_go_out bytes (k + 1) idx [] hlt]
        simp only [List.reverse_nil, List.append_nil]

theorem align_goAccEq : PG_align_goAccEq := fun bytes fuel idx acc => align_goAccEq_aux bytes fuel idx acc

/-! #### WALKC: the walk history, and closure under one more step -/

inductive align_chain : List Nat → List QuotientBytecodeOp → Nat → Prop
  | nil : ∀ (bytes : List Nat) (idx : Nat), align_chain bytes [] idx
  | step : ∀ (bytes : List Nat) (t : QuotientBytecodeOp) (rest : List QuotientBytecodeOp)
      (idx : Nat),
      align_chain bytes rest t.1 →
        idx = t.1 + t.2.2 →
        t.1 < bytes.length →
        Midfall.Generator.QuotientValidator.quotientOpLen bytes t.1 = .ok t.2.2 →
        align_chain bytes (t :: rest) idx

theorem align_chain_succ {bytes : List Nat} {acc : List QuotientBytecodeOp} {idx : Nat}
    (hchain : align_chain bytes acc idx) {t : QuotientBytecodeOp} (ht : t ∈ acc) :
    (∃ t' ∈ acc, t'.1 = t.1 + t.2.2) ∨ t.1 + t.2.2 = idx := by
  induction hchain with
  | nil _ => cases ht
  | step u rest jidx hrec hidx hlt hlen hih =>
      simp only [List.mem_cons] at ht
      cases ht with
      | inl heq =>
          subst heq
          right
          exact hidx.symm
      | inr hrest =>
          cases hih hrest with
          | inl hex =>
              obtain ⟨w, hw, hw1⟩ := hex
              left
              exact ⟨w, List.mem_cons.mpr (Or.inr hw), hw1⟩
          | inr hsucc =>
              left
              exact ⟨u, List.mem_cons.mpr (Or.inl rfl), hsucc.symm⟩

theorem align_chain_genuine {bytes : List Nat} {acc : List QuotientBytecodeOp} {idx : Nat}
    (hchain : align_chain bytes acc idx) {t : QuotientBytecodeOp} (ht : t ∈ acc) :
    t.1 < bytes.length ∧
      Midfall.Generator.QuotientValidator.quotientOpLen bytes t.1 = .ok t.2.2 := by
  induction hchain with
  | nil _ => cases ht
  | step u rest jidx hrec hidx hlt hlen hih =>
      simp only [List.mem_cons] at ht
      cases ht with
      | inl heq =>
          subst heq
          exact ⟨hlt, hlen⟩
      | inr hrest => exact hih hrest

theorem align_go_succ_ok {bytes : List Nat} {k idx : Nat}
    {acc ops : List QuotientBytecodeOp}
    (hlt : idx < bytes.length)
    (h : quotientBytecodeOpsGo bytes (k + 1) idx acc = .ok ops) :
    ∃ op len, quotientBytecodeOpsGo bytes k (idx + len) ((idx, op, len) :: acc) = .ok ops ∧
      Midfall.Generator.QuotientValidator.quotientOpLen bytes idx = .ok len ∧
        Midfall.Generator.QuotientValidator.byteAtPanic bytes idx 3084 = .ok op := by
  rw [align_go_succ bytes k idx acc hlt] at h
  cases h1 : Midfall.Generator.QuotientValidator.byteAtPanic bytes idx 3084 with
  | error e =>
      rw [h1] at h
      simp only [align_bind_err] at h
      exact absurd h (by simp)
  | ok op =>
      cases h2 : Midfall.Generator.QuotientValidator.quotientOpLen bytes idx with
      | error e =>
          rw [h1, h2] at h
          simp only [align_bind_ok, align_bind_err] at h
          exact absurd h (by simp)
      | ok len =>
          rw [h1, h2] at h
          simp only [align_bind_ok] at h
          exact ⟨op, len, h, rfl, rfl⟩

theorem align_go_genuine (bytes : List Nat) :
    ∀ (fuel idx : Nat) (acc ops : List QuotientBytecodeOp),
      align_chain bytes acc idx →
      quotientBytecodeOpsGo bytes fuel idx acc = .ok ops →
      ∀ t ∈ ops, t.1 < bytes.length ∧
        Midfall.Generator.QuotientValidator.quotientOpLen bytes t.1 = .ok t.2.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro idx acc ops hchain hgo t ht
      by_cases hlt : idx < bytes.length
      · rw [align_go_fuel0 bytes idx acc hlt] at hgo
        exact absurd hgo (by simp [Midfall.Generator.QuotientValidator.vPanic])
      · rw [align_go_out bytes 0 idx acc hlt] at hgo
        simp only [Except.ok.injEq] at hgo
        subst hgo
        exact align_chain_genuine hchain (List.mem_reverse.mp ht)
  | succ k ih =>
      intro idx acc ops hchain hgo t ht
      by_cases hlt : idx < bytes.length
      · obtain ⟨op, len, hrec, hlen, _hop⟩ := align_go_succ_ok hlt hgo
        have hchain' : align_chain bytes ((idx, op, len) :: acc) (idx + len) :=
          align_chain.step bytes (idx, op, len) acc (idx + len) hchain rfl hlt hlen
        exact ih (idx + len) ((idx, op, len) :: acc) ops hchain' hrec t ht
      · rw [align_go_out bytes (k + 1) idx acc hlt] at hgo
        simp only [Except.ok.injEq] at hgo
        subst hgo
        exact align_chain_genuine hchain (List.mem_reverse.mp ht)

theorem align_go_closed (bytes : List Nat) :
    ∀ (fuel idx : Nat) (acc ops : List QuotientBytecodeOp),
      align_chain bytes acc idx →
      quotientBytecodeOpsGo bytes fuel idx acc = .ok ops →
      ∀ t ∈ ops, t.1 + t.2.2 < bytes.length → ∃ t' ∈ ops, t'.1 = t.1 + t.2.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro idx acc ops hchain hgo t ht hlt
      by_cases hidx : idx < bytes.length
      · rw [align_go_fuel0 bytes idx acc hidx] at hgo
        exact absurd hgo (by simp [Midfall.Generator.QuotientValidator.vPanic])
      · rw [align_go_out bytes 0 idx acc hidx] at hgo
        simp only [Except.ok.injEq] at hgo
        subst hgo
        cases align_chain_succ hchain (List.mem_reverse.mp ht) with
        | inl hex =>
            obtain ⟨w, hw, hw1⟩ := hex
            exact ⟨w, List.mem_reverse.mpr hw, hw1⟩
        | inr hsucc =>
            have : idx < bytes.length := hsucc ▸ hlt
            exact absurd this hidx
  | succ k ih =>
      intro idx acc ops hchain hgo t ht hlt
      by_cases hidx : idx < bytes.length
      · obtain ⟨op, len, hrec, hlen, _hop⟩ := align_go_succ_ok hidx hgo
        have hchain' : align_chain bytes ((idx, op, len) :: acc) (idx + len) :=
          align_chain.step bytes (idx, op, len) acc (idx + len) hchain rfl hidx hlen
        exact ih (idx + len) ((idx, op, len) :: acc) ops hchain' hrec t ht hlt
      · rw [align_go_out bytes (k + 1) idx acc hidx] at hgo
        simp only [Except.ok.injEq] at hgo
        subst hgo
        cases align_chain_succ hchain (List.mem_reverse.mp ht) with
        | inl hex =>
            obtain ⟨w, hw, hw1⟩ := hex
            exact ⟨w, List.mem_reverse.mpr hw, hw1⟩
        | inr hsucc =>
            have : idx < bytes.length := hsucc ▸ hlt
            exact absurd this hidx

theorem align_walkClosed : PG_align_walkClosed := by
  intro bytes ops c len hgo hc hc_lt hlen hclt
  obtain ⟨t, ht, htc⟩ := hc
  have hgen := align_go_genuine bytes bytes.length 0 [] ops (align_chain.nil bytes 0) hgo t ht
  have hlen2 : t.2.2 = len := by
    have h1 : Midfall.Generator.QuotientValidator.quotientOpLen bytes t.1 = .ok t.2.2 := hgen.2
    rw [htc, hlen] at h1
    exact (Except.ok.inj h1).symm
  have hlt' : t.1 + t.2.2 < bytes.length := by
    rw [htc, hlen2]
    exact hclt
  obtain ⟨t', ht', ht'1⟩ :=
    align_go_closed bytes bytes.length 0 [] ops (align_chain.nil bytes 0) hgo t ht hlt'
  exact ⟨t', ht', by rw [← htc, ← hlen2]; exact ht'1⟩

#print axioms Midfall.Lowering.align_goAccEq
#print axioms Midfall.Lowering.align_walkClosed
#print axioms Midfall.Lowering.align_go_closed
#print axioms Midfall.Lowering.align_go_genuine

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


/-! #### D-P23 evidence for qvm_validated_windows

    Both halves as THEOREMS, per D-P23. THE LIMIT, stated rather than hidden: the witness
    below is CONDITIONAL on the pinned gate fact
    'validator_noOOB_onTheRealPlan_ok', because 'decide' cannot reach the fixture -
    'planBuild.bytes' is a ByteArray and ByteArray operations are '@[extern]' C++, and the
    phase-1 walk 'quotientBytecodeOpsGo' is a fuel-bounded recursion the kernel will not
    reduce (measured: 'rfl' proves 'quotientOpLen badBytes 0 = ok 5' but fails on
    'quotientBytecodeOps badBytes = ok [...]'). 'native_decide' is confined to
    Midfall/Instances/ by checks.sh and this file may not import Instances (D-P17). So the
    satisfiability half is discharged from the gate that kat_gate.py runs at every gate
    run, not from the kernel. Per the measured falsification-deletion gap (thirty times):
    deleting either theorem leaves the build green and no gate catches it, so no
    persistence coverage is claimed here, only truth. -/

/-- SATISFIABILITY WITNESS (D-P23, first half). P-11's VM fixture satisfies the hypothesis
    bundle of 'qvm_validated_windows' - the lowering arm, the quotient arm, the operand
    model built from it, and the validator predicate - provided the pinned gate holds. The
    'error' arm of the model match is refuted inside the proof, so the witness really names
    a model the validator accepted rather than an arbitrary one. -/
theorem windows_hypotheses_satisfiable
    (hgate : Midfall.Generator.LoweringPlanKats.planVM.supportedQvmBool = true) :
    ∃ (model : QuotientOperandModel) (q : Midfall.Generator.PlannedQuotient),
      Midfall.Generator.LoweringPlanKats.planVM.lowering = Midfall.Generator.QuotientLowering.vm ∧
      Midfall.Generator.LoweringPlanKats.planVM.quotient = some q ∧
      Midfall.Generator.quotientOperandModel Midfall.Generator.LoweringPlanKats.planVM.meta_ Midfall.Generator.LoweringPlanKats.planVM.data
        Midfall.Generator.LoweringPlanKats.planVM.vk Midfall.Generator.LoweringPlanKats.planVM.vkMptr Midfall.Generator.LoweringPlanKats.planVM.memory q.build q.plan.selectorFold = .ok model ∧
      Midfall.Generator.LoweringPlanKats.planVM.supportedQvm := by
  cases hm : Midfall.Generator.quotientOperandModel Midfall.Generator.LoweringPlanKats.planVM.meta_ Midfall.Generator.LoweringPlanKats.planVM.data
      Midfall.Generator.LoweringPlanKats.planVM.vk Midfall.Generator.LoweringPlanKats.planVM.vkMptr Midfall.Generator.LoweringPlanKats.planVM.memory
      Midfall.Generator.LoweringPlanKats.plannedQ.build Midfall.Generator.LoweringPlanKats.plannedQ.plan.selectorFold with
  | ok m =>
      exact ⟨m, Midfall.Generator.LoweringPlanKats.plannedQ, rfl, rfl, hm, hgate⟩
  | error f =>
      have hfalse : Midfall.Generator.LoweringPlanKats.planVM.supportedQvmBool = false := by
        unfold Midfall.Generator.LoweringPlan.supportedQvmBool
        rw [show Midfall.Generator.LoweringPlanKats.planVM.lowering = Midfall.Generator.QuotientLowering.vm from rfl,
            show Midfall.Generator.LoweringPlanKats.planVM.quotient = some Midfall.Generator.LoweringPlanKats.plannedQ from rfl]
        dsimp only
        rw [hm]
      exact absurd hgate (by rw [hfalse]; exact Bool.false_ne_true)

/-- THE FALSIFICATION (D-P23, second half). The window conclusion is not a tautology: on
    the empty-window model the aligned pointer 0xffffffe0 lies outside every window, and
    the validator's own operand check rejects that operand. So the property
    'qvm_validated_windows' concludes is one a program can fail, which is what makes the
    'hvalidated' hypothesis load-bearing rather than decorative. -/
theorem windows_conclusion_is_not_a_tautology :
    quotientOperandModelDefault.read.windowFor 0xffffffe0 = none ∧
      checkQuotientOperand quotientOperandModelDefault 0
        (QuotientOperand.mem "literal" 0xffffffe0) ≠ .ok () := by
  refine ⟨rfl, ?_⟩
  intro hh
  unfold checkQuotientOperand checkQuotientMemOperand at hh
  simp only [bind, Except.bind] at hh
  cases hh

/-! #### GATE - the differential enumeration re-run inside the build -/

/-- The operand environment the two differential gates run in: a constant table wide
    enough for every slot any fixture names (the pairwise block reaches slot 12), a
    stack deep enough for the deepest arm, and the reference PRNG memory. Not a Rust
    item. -/
def armsConsts : List Word256 := (List.range 300).map fun i => BitVec.ofNat 256 (i + 1)

/-- ditto. -/
def armsStack : List QVMFr := List.replicate 40 7

/-- ditto. -/
def armsMem : QuotientRefMemory := Midfall.Generator.quotientRefMemoryNew Midfall.Generator.QuotientVmRefKats.refSeedA

/-- The engineered operand payload. payload[0] = 0 keeps the MODARITH7 flag byte legal;
    the big-endian u16s at idx+1 and idx+3 are 4 and 2, both nonzero, so the RUN count
    and BOTH AFFINE_SUM counts pass their nonzero guards. That engineering is what makes
    the sweep exercise the dynamic arms instead of short-circuiting on their guards. -/
def armsPayload : List Nat := [0, 4, 0, 2] ++ List.replicate 600 0

/-- One (bytes, index, opcode) triple compared across the two walkers. True means the
    widths agree, or both sides refused, or the only disagreement is the documented
    stream-opcode domain boundary. -/
def armsAgreeAt (bytes : List Nat) (idx op : Nat) : Bool :=
  match (evalQuotientIdentityStep bytes armsConsts idx op armsStack armsMem,
         Midfall.Generator.QuotientValidator.quotientOpLen bytes idx) with
  | (.ok s, .ok n) => s.consumed == n
  | (.error _, .error _) => true
  | (.error (QVMFault.streamOpcodeInIdentity _ _), .ok _) => op ∈ streamIdentityExcluded
  | (.error _, .ok _) => false
  | (.ok _, .error _) => false

/-- GATE (P-QVMARMS, differential enumeration, half 1). Re-runs the ARMS ENUMERATION
    inside the build over all 31 opcodeFixtures - one complete phase-1-accepted program
    per table opcode, at each fixture own testIdx. The third conjunct is the non-vacuity
    half: exactly 26 of the 31 arms must reach a success on the interpreter side, so the
    gate cannot be satisfied by every arm erroring. Rules out: the enumeration in
    section 7 drifting from the code it enumerated - a new arm, a changed stride, a
    table edit - without a rebuild going red. -/
def arms_agreement_differential_fixtures_ok : Bool :=
  (QuotientVmValidatorKats.opcodeFixtures.all fun f => armsAgreeAt f.bytes f.testIdx f.op)
    && QuotientVmValidatorKats.opcodeFixtures.length == 31
    && (QuotientVmValidatorKats.opcodeFixtures.filter fun f =>
          match evalQuotientIdentityStep f.bytes armsConsts f.testIdx f.op armsStack armsMem with
          | .ok _ => true
          | .error _ => false).length == 26
#eval arms_agreement_differential_fixtures_ok -- expect true

/-- GATE (P-QVMARMS, differential enumeration, half 2). The same comparison over EVERY
    opcode byte 0..255 against the engineered payload, so an arm that exists in the
    interpreter but not in the table (or the reverse) cannot hide between fixtures. The
    second conjunct pins that the five stream opcodes are EXACTLY the set where the
    walker has a width and the step refuses; the third that exactly the 31 table opcodes
    have a width at all; the fourth and fifth that the reserved byte 0x1a is refused by
    BOTH sides, so the agreement is not being bought by a walker that accepts everything.
    Rules out: the agreement being an artifact of the fixture set, and the stream
    exclusion silently growing or shrinking. -/
def arms_stepErrors (op : Nat) : Bool :=
  match evalQuotientIdentityStep ([op] ++ armsPayload) armsConsts 0 op armsStack armsMem with
  | .ok _ => false
  | .error _ => true

/-- ditto, validator side -/
def arms_lenOk (op : Nat) : Bool :=
  match Midfall.Generator.QuotientValidator.quotientOpLen ([op] ++ armsPayload) 0 with
  | .ok _ => true
  | .error _ => false

/-- ditto -/
def arms_streamError (op : Nat) : Bool :=
  match evalQuotientIdentityStep ([op] ++ armsPayload) armsConsts 0 op armsStack armsMem with
  | .error (QVMFault.streamOpcodeInIdentity _ _) => true
  | _ => false

def arms_agreement_differential_sweep_ok : Bool :=
  (List.range 256).all fun op => armsAgreeAt ([op] ++ armsPayload) 0 op
    && List.Perm ((List.range 256).filter arms_streamError) streamIdentityExcluded
    && ((List.range 256).filter arms_lenOk).length == 31
    && arms_stepErrors 0x1a && ! arms_lenOk 0x1a
#eval arms_agreement_differential_sweep_ok -- expect true

/-! #### GATE - the read-extent enumeration re-run inside the build (P-READOFF) -/

/-- The step at idx, on the engineered environment: does it name a read fault? Not a Rust
    item - this is the measurement probe. -/
def armsStepFaultsRead (bytes : List Nat) (idx : Nat) (op : Nat) : Bool :=
  match evalQuotientIdentityStep bytes armsConsts idx op armsStack armsMem with
  | .error (QVMFault.readPastEnd _) => true
  | _ => false

/-- THE MEASURED READ EXTENT of one arm at one index: the shortest prefix of the payload on
    which the step stops faulting readPastEnd, relative to the instruction index. That is
    operationally "one past the largest byte index the arm actually reads", which is the
    only reading of "the arm reads byte k" that the port exposes - there is no read-effect
    model in the reference and none is invented here.

    999999 is the sentinel for "no prefix suffices": the instruction as claimed does not fit
    the payload at all, which is what a readPastEnd IS. The sentinel is kept distinct from 0
    so a truncated payload cannot be mistaken for a zero-operand arm. -/
def armsReadExtent (bytes : List Nat) (idx : Nat) (op : Nat) : Nat :=
  match (List.range (bytes.length + 1)).find?
      (fun n => ! armsStepFaultsRead (bytes.take n) idx op) with
  | some n => if n >= idx + 1 then n - idx else 0
  | none => 999999

/-- ditto, the interpreter's own stride -/
def armsStepConsumed (bytes : List Nat) (idx : Nat) (op : Nat) : Option Nat :=
  match evalQuotientIdentityStep bytes armsConsts idx op armsStack armsMem with
  | .ok s => some s.consumed
  | .error _ => none

/-- The four arms that read NO operand byte: their stride is the opcode byte alone, so the
    read extent is legitimately 0. Named as a set rather than left as an unexplained
    residue, so the 22/26 figure cannot silently decay to 26/26 if someone forces one of
    these four to claim a read. -/
def readsNothingArms : List Nat := [qOpAdd, qOpMul, qOpNeg, qOpPow5]

/-- GATE (P-READOFF, differential enumeration, half 1). The read-extent enumeration over
    all 31 opcodeFixtures at each fixture's own testIdx, re-run inside the build. Four
    conjuncts:
      * every arm's measured read extent is at most the stride the step reports;
      * exactly 26 of the 31 arms reach a success, so the sweep cannot be satisfied by
        every arm erroring (the non-vacuity half);
      * exactly 22 arms read to the stride and the four that read less are EXACTLY
        'readsNothingArms' at extent 0 - so the padding-free observation is pinned as a
        property of THIS payload, not claimed as a property of the arms;
      * the extent is also at most the VALIDATOR's stride, which is the form the hole needs.
    Rules out: an arm reading past its declared stride, and the no-read class silently
    changing membership. -/
def readsWithinStride_differential_fixtures_ok : Bool :=
  (QuotientVmValidatorKats.opcodeFixtures.all fun f =>
    match armsStepConsumed f.bytes f.testIdx f.op with
    | some c => armsReadExtent f.bytes f.testIdx f.op <= c
    | none => true)
    && (QuotientVmValidatorKats.opcodeFixtures.filter fun f =>
          (armsStepConsumed f.bytes f.testIdx f.op).isSome).length == 26
    && (QuotientVmValidatorKats.opcodeFixtures.filter fun f =>
          match armsStepConsumed f.bytes f.testIdx f.op with
          | some c => armsReadExtent f.bytes f.testIdx f.op == c
          | none => false).length == 22
    && List.Perm ((QuotientVmValidatorKats.opcodeFixtures.filter fun f =>
          match armsStepConsumed f.bytes f.testIdx f.op with
          | some c => armsReadExtent f.bytes f.testIdx f.op < c
          | none => false).map fun f => f.op) readsNothingArms
    && (QuotientVmValidatorKats.opcodeFixtures.all fun f =>
          match armsStepConsumed f.bytes f.testIdx f.op with
          | none => true
          | some _ =>
              readsNothingArms.contains f.op == (armsReadExtent f.bytes f.testIdx f.op == 0))
    && (QuotientVmValidatorKats.opcodeFixtures.all fun f =>
          match QuotientValidator.quotientOpLen f.bytes f.testIdx with
          | .ok n => armsReadExtent f.bytes f.testIdx f.op <= n
          | .error _ => true)
#eval readsWithinStride_differential_fixtures_ok -- expect true

/-- The three dynamic arms whose GUARD short-circuits on an un-engineered payload, named as
    a set so the trap conjunct cannot be quietly narrowed to the easy arms. MODARITH7 is not
    in this list: it does not error on a zero payload, it SUCCEEDS with every count zero,
    which is the more dangerous failure mode and gets its own conjunct below. -/
def guardShortCircuitArms : List Nat :=
  [qOpRunAddMulMemMemConstU8, qOpRunAddMulConstU8MemU16, qOpAffineSum]

/-- GATE (P-READOFF, differential enumeration, half 2). The same comparison over EVERY
    opcode byte 0..255 against the engineered payload, PLUS the negative controls that
    prove the enumeration has teeth. Five conjuncts:
      * no arm's read extent exceeds its stride, over all 256 opcode bytes;
      * exactly 26 arms reach a success on the engineered payload (the same 26 as the
        fixture half, so the two enumerations agree with each other);
      * TEETH: claiming every stride one byte too short is REJECTED for exactly 22 arms,
        and the four that survive are exactly 'readsNothingArms'. Without this conjunct a
        sweep that measured nothing could still report agreement;
      * THE PAYLOAD TRAP, pinned: on an all-zero payload the four dynamic arms
        short-circuit on their own guards (two zeroLengthRun, one affineSumZeroCounts, and
        MODARITH7 succeeding with every count zero), and each of their measured extents is
        STRICTLY SMALLER than on the engineered payload. This is the conjunct that makes
        the engineered payload load-bearing rather than decorative - delete the engineering
        and the gate goes red instead of silently measuring 3, 3, 5 and 7 bytes of
        instructions that read 13, 9, 13 and 148.
      * the MODARITH7 flag asymmetry on the READ side: an illegal flag byte makes the
        interpreter refuse at extent 2 while quotientOpLen still reports a stride, so the
        read bound is conditional on the walker's success exactly as the stride agreement
        is. -/
def readsWithinStride_differential_sweep_ok : Bool :=
  (List.range 256).all fun op =>
    match armsStepConsumed ([op] ++ armsPayload) 0 op with
    | some c => armsReadExtent ([op] ++ armsPayload) 0 op <= c
    | none => true
    && ((List.range 256).filter fun op =>
          (armsStepConsumed ([op] ++ armsPayload) 0 op).isSome).length == 26
    && ((List.range 256).filter fun op =>
          match armsStepConsumed ([op] ++ armsPayload) 0 op with
          | some c => !(armsReadExtent ([op] ++ armsPayload) 0 op <= c - 1)
          | none => false).length == 22
    && List.Perm ((List.range 256).filter fun op =>
          match armsStepConsumed ([op] ++ armsPayload) 0 op with
          | some c => armsReadExtent ([op] ++ armsPayload) 0 op < c
          | none => false) readsNothingArms
    && List.all guardShortCircuitArms fun op =>
         ! (armsStepConsumed ([op] ++ List.replicate 60 0) 0 op).isSome
    && armsReadExtent ([qOpModarith7] ++ List.replicate 60 0) 0 qOpModarith7
         < armsReadExtent ([qOpModarith7] ++ armsPayload) 0 qOpModarith7
    && (match evalQuotientIdentityStep ([qOpModarith7, 0x04] ++ armsPayload.tail.tail)
            armsConsts 0 qOpModarith7 armsStack armsMem with
        | .error (QVMFault.modarith7UnknownFlags _ _) => true
        | _ => false)
    && (match QuotientValidator.quotientOpLen ([qOpModarith7, 0x04] ++ armsPayload.tail.tail) 0 with
        | .ok _ => true
        | .error _ => false)
#eval readsWithinStride_differential_sweep_ok -- expect true


/-! #### GATE - the const-slot correspondence enumerated inside the build (P-CONTSLOT) -/

/-- The constant-table length the slot probe bounds against. A slot at or above it is out of
    range for BOTH sides, which is what makes an out-of-range slot observable: the interpreter
    answers 'constSlotOutOfRange', the walker returns a 'konst' whose slot fails
    'checkQuotientConstSlot'. Not a Rust item. -/
def slotProbeBound : Nat := 200

/-- The byte value written into the probed position: equal to the table length, so a side that
    reads that position AS A SLOT reports it out of range and a side that reads it as anything
    else (a count, a pointer byte, a flag) does not. Not a Rust item. -/
def slotProbeSentinel : Nat := 200

/-- ditto -/
def slotProbeTable : List Word256 := List.take slotProbeBound armsConsts

/-- THE ENGINEERED PAYLOAD, per arm. This is the part R-70 warned is easy to skip and
    impossible to fake: with an all-zero payload MODARITH7's five count bytes are all zero,
    AFFINE_SUM's two counts are zero and both RUN counts are zero, and every one of those arms
    then names NO const slot at all - MODARITH7's 30-slot block is simply never walked.
    'flags = 3' exercises BOTH header legs (the cond pointer and the const slot), and the five
    count bytes are 1 so all five blocks run. Not a Rust item. -/
def slotProbePayload (op : Nat) : List Nat :=
  let tail := List.replicate 90 0
  if op == qOpModarith7 then [op, 3, 0, 0, 0, 1, 1, 1, 1, 1] ++ tail
  else if op == qOpAffineSum then [op, 0, 1, 0, 1] ++ tail
  else if op == qOpRunAddMulMemMemConstU8 || op == qOpRunAddMulConstU8MemU16 then [op, 0, 2] ++ tail
  else [op] ++ tail

/-- ditto -/
def slotProbePerturb (bytes : List Nat) (p : Nat) : List Nat :=
  (bytes.take p) ++ [slotProbeSentinel] ++ (bytes.drop (p+1))

/-- THE INTERPRETER-SIDE PROBE: does the step read a const slot at position p? Measured, not
    defined - see the section-9 header. -/
def interpSlotAtP (bytes : List Nat) (idx op p : Nat) : Bool :=
  match evalQuotientIdentityStep (slotProbePerturb bytes p) slotProbeTable idx op armsStack armsMem with
  | .error (QVMFault.constSlotOutOfRange s _) => slotProbeBound ≤ s
  | _ => false

/-- THE WALKER-SIDE PROBE, the same question asked of 'visitQuotientOperands'. -/
def walkerSlotAtP (bytes : List Nat) (idx op p : Nat) : Bool :=
  (operandList (slotProbePerturb bytes p) idx op).any fun o => match o with
    | QuotientOperand.konst s _ => slotProbeBound ≤ s
    | _ => false

/-- How far the probe runs: the instruction's own declared width plus a margin, so a slot read
    OUTSIDE the stride would still be caught rather than silently out of range. -/
def slotProbeWidth (bytes : List Nat) (idx op : Nat) : Nat :=
  match QuotientValidator.quotientOpLen bytes idx with
  | .ok n => n + 4
  | .error _ => 12

/-- ditto -/
def interpSlotPositionsAt (bytes : List Nat) (idx op : Nat) : List Nat :=
  (List.range (slotProbeWidth bytes idx op)).filter (interpSlotAtP bytes idx op)

/-- ditto -/
def walkerSlotPositionsAt (bytes : List Nat) (idx op : Nat) : List Nat :=
  (List.range (slotProbeWidth bytes idx op)).filter (walkerSlotAtP bytes idx op)

/-- ditto, on the un-engineered payload, for the trap conjunct -/
def zeroSlotProbe (op : Nat) : List Nat := [op] ++ List.replicate 90 0

/-- The 15 arms that read at least one const slot and the 11 that read none, named as sets so
    the 15/26 figure cannot silently decay if an arm gains or loses a slot read. -/
def slotReadingArms : List Nat :=
  [qOpPushConst, qOpPushConstU8, qOpAddConstU8, qOpMulConstU8, qOpAddConst, qOpMulConst,
   qOpAddMulMemMemConstU8, qOpAddMulConstU8MemU16, qOpLin7, qOpBilin7Row, qOpBilin7Pairwise,
   qOpRunAddMulMemMemConstU8, qOpRunAddMulConstU8MemU16, qOpAffineSum, qOpModarith7]

/-- ditto -/
def noSlotArms : List Nat :=
  [qOpPushMemLiteral, qOpPushMemToken, qOpPushMemTokenOffset, qOpPushMemU16, qOpAdd, qOpMul,
   qOpNeg, qOpPow5, qOpAddMemU16, qOpMulMemU16, qOpAddMulMemMem]

/-- The 26 arms the slot probe runs over: the 22 static plus the 4 dynamic. -/
def slotProbeArms : List Nat := staticIdentityArms ++ dynamicIdentityArms

/-- The konst slots of a walker operand list. -/
def konstOf (os : List QuotientOperand) : List Nat :=
  os.filterMap fun o => match o with
    | QuotientOperand.konst s _ => some s
    | _ => none

/-- The slot the interpreter faults on at one table length, if it faults at all. -/
def interpSlotsAt (bytes : List Nat) (idx op L : Nat) : Option Nat :=
  match evalQuotientIdentityStep bytes (List.take L armsConsts) idx op armsStack armsMem with
  | .error (QVMFault.constSlotOutOfRange s _) => some s
  | _ => none

/-- GATE (P-CONTSLOT, differential enumeration, half 1). The correspondence measured on the
    31 REAL opcode fixtures - complete phase-1-accepted programs at each fixture's own
    testIdx - against a THIRD source: the fixture table's hand-transcribed 'operands' field,
    written independently of the walker. Four conjuncts: the walker's konst slots equal the
    transcription; every slot the interpreter faults on (sweeping the table length) is one the
    walker names; exactly 15 of the 31 fixtures read a slot, so the gate cannot be satisfied by
    an enumeration that finds nothing; and the five stream fixtures name none on either side.
    Rules out: the correspondence drifting from the code it enumerated, and the fixture
    transcription silently agreeing with the walker only because one was copied from the other.
    -/
def constSlots_differential_fixtures_ok : Bool :=
  let ws := QuotientVmValidatorKats.opcodeFixtures.map fun f =>
    (f.op, konstOf (operandList f.bytes f.testIdx f.op))
  (QuotientVmValidatorKats.opcodeFixtures.all fun f =>
      konstOf f.operands == konstOf (operandList f.bytes f.testIdx f.op))
    && (QuotientVmValidatorKats.opcodeFixtures.all fun f =>
        ((List.range 15).filterMap (interpSlotsAt f.bytes f.testIdx f.op)).all
          (fun s => s ∈ konstOf (operandList f.bytes f.testIdx f.op)))
    && (ws.filter fun (_, k) => k != []).length == 15
    && (ws.filter fun (op, _) => op ∈ streamIdentityExcluded).all fun (_, k) => k == []
    && (QuotientVmValidatorKats.opcodeFixtures.filter fun f =>
          (interpSlotsAt f.bytes f.testIdx f.op 0).isSome).length == 15
#eval constSlots_differential_fixtures_ok -- expect true

/-- GATE (P-CONTSLOT, differential enumeration, half 2). The position-level correspondence over
    all 26 identity arms against the engineered payload, plus the controls that give it teeth.
    Conjuncts:
      * per arm, the interpreter's slot positions EQUAL the walker's (not merely inside them);
      * the total is exactly 74 positions, so no arm can quietly stop reading slots;
      * the arms that read a slot are exactly 'slotReadingArms' and the rest exactly
        'noSlotArms';
      * TEETH: shifting the walker's positions one byte right is REJECTED for every arm that
        reads a slot - without this a probe that found nothing anywhere would still "agree";
      * THE PAYLOAD TRAP, pinned: on an all-zero payload the four dynamic arms name zero slot
        positions on both sides while the engineered payload makes them name 2, 2, 2 and 30 -
        36 of the 74 positions, and all of MODARITH7's. Delete the payload engineering and this
        conjunct reddens instead of silently narrowing what is measured;
      * the reserved byte 0x1a is named by neither side, so the agreement is not bought by a
        walker that accepts everything. -/
def constSlots_differential_sweep_ok : Bool :=
  let trips := slotProbeArms.map fun op =>
    (op, interpSlotPositionsAt (slotProbePayload op) 0 op,
         walkerSlotPositionsAt (slotProbePayload op) 0 op)
  trips.all fun (_, a, b) => a == b
    && (trips.map fun (_, a, _) => a.length).sum == 74
    && List.Perm ((trips.filter fun (_, a, _) => a != []).map fun (op, _, _) => op)
        slotReadingArms
    && List.Perm ((trips.filter fun (_, a, _) => a == []).map fun (op, _, _) => op)
        noSlotArms
    && trips.all fun (_, a, b) => a == [] || a != b.map (· + 1)
    && slotProbeArms.all fun op =>
         interpSlotPositionsAt (zeroSlotProbe op) 0 op
           == walkerSlotPositionsAt (zeroSlotProbe op) 0 op
    && slotProbeArms.all fun op => op ∈ dynamicIdentityArms →
         interpSlotPositionsAt (zeroSlotProbe op) 0 op == []
    && (trips.filter fun (op, _, _) => op ∈ dynamicIdentityArms).all fun (_, a, _) => a != []
    && interpSlotPositionsAt [0x1a] 0 0x1a == []
    && walkerSlotPositionsAt [0x1a] 0 0x1a == []
    && trips.all fun (_, a, _) => a.length ≤ 30
#eval constSlots_differential_sweep_ok -- expect true
end Midfall.Lowering.QvmKats


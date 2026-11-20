-- |
-- Midfall.Lowering.QvmWalk
--
-- Card QVMC - the per-arm facts 'qvm_validated_noBoundsFault' asks for and nothing supplies.
--
-- WHY THESE. Qvm.lean:768 excludes two fault classes from a segment that ERRORS, and its own
-- doc names the package it needs: "the per-opcode agreement between evalQuotientIdentityStep's
-- 'consumed' field and the validator's quotientOpLen across all ~25 opcode arms, plus the loop
-- induction over the fuel-bounded walk". The per-arm half is 80% landed and the gaps are named
-- in the files that left them:
--
--   * 'evalQuotientIdentityStep_consumed_agrees'   (Qvm.lean:1197) - the 22 static arms.
--     MISSING: the four dynamic arms (the two RUNs, AFFINE_SUM, MODARITH7), whose consumed is
--     a function of a count read mid-instruction and so cannot be a numeral in that
--     statement's case split.
--   * 'evalQuotientIdentityStep_readsWithinStride' (Qvm.lean:1864) - the 22 static arms, plus
--     'runAddMulMemMemConstU8_noRF' / 'runAddMulConstU8MemU16_noRF' (:2089, :2125).
--     MISSING: AFFINE_SUM and MODARITH7 - "measured-agreeing and not yet proved, for the
--     chaining reason in their own doc comments ... the two gaps are arithmetic depth, not a
--     missing idea" (Qvm.lean:1861-1863).
--
-- THE CHAINING REASON, named. 'NoRF.fold_blocks_noRF' and 'foldRangeIdxM_ok_advance' are each
-- about ONE counted block. AFFINE_SUM is two blocks and MODARITH7 is five, and the next block's
-- INIT CURSOR is the previous block's output - which is only known under the previous block's
-- success. So the missing tool is not arithmetic, it is a binder: 'fold_chain_step' below peels
-- one block and hands the continuation the equation 'init.2.1 + w * n = y.2.1' as a hypothesis,
-- which is exactly what the next block's fit obligation needs. With it the multi-block arms are
-- a chain of single-block applications rather than a new induction.
--
-- LANDED HERE: the chaining tool, the AFFINE_SUM read bound (the first of the two gaps at
-- Qvm.lean:1861), and the width agreement for both RUN arms. STILL OPEN after this file, named
-- precisely: the MODARITH7 read bound, the AFFINE_SUM and MODARITH7 width agreements, and the
-- seven missing const-slot correspondences (the three folded static arms LIN7 / BILIN7_ROW /
-- BILIN7_PAIRWISE plus the four dynamic ones) - see the package report.
--
-- CONDITIONAL BY CONSTRUCTION, exactly as section 7 and the RUN pair are. Each lemma takes the
-- arm's own decoded counts as reader equations ('readU16 bytes (idx+1) = .ok n') rather than
-- deriving them, because the arm's first action IS that read and the interpreter refuses shapes
-- the walker happily walks (a zero-length RUN, zero AFFINE_SUM counts, an illegal MODARITH7 flag
-- byte). Those refusals are not read faults and are discharged INSIDE the proofs, not hidden by
-- a hypothesis - cf. Qvm.lean:1854-1856.
--
-- NOTHING HERE ADDS A HYPOTHESIS TO A ROW, to 'ValidV3', a bundle or the root (RULES); no
-- statement names a fixture (D-P71); there is no 'native_decide' and no sorry in this file.
import Midfall.Lowering.Qvm

set_option autoImplicit false

namespace Midfall.Lowering.QvmWalk

open Midfall Midfall.Generator Midfall.Generator.QuotientValidator

/-! ### 1. The chaining tool -/

/-- One counted stride-'w' block, followed by an arbitrary continuation that only needs the
    block's END CURSOR. The continuation is a binder, not a second fold, which is what lets five
    blocks chain: each step hands the next the equation 'init.2.1 + w * n = y.2.1'. -/
theorem fold_chain_step {β β' : Type} (w L : Nat) : ∀ (n : Nat)
    (init : QVMFr × Nat × β)
    (f₁ : Nat → QVMFr × Nat × β → Except QVMFault (QVMFr × Nat × β))
    (k : QVMFr × Nat × β → Except QVMFault β'),
    init.2.1 + w * n ≤ L →
    (∀ i s, i < n → s.2.1 + w ≤ L → NoRF (f₁ i s)) →
    (∀ i s r, f₁ i s = .ok r → r.2.1 = s.2.1 + w) →
    (∀ y, init.2.1 + w * n = y.2.1 → NoRF (k y)) →
    NoRF (Midfall.Generator.foldRangeIdxM n init f₁ >>= k) := by
  intro n init f₁ k hinit hf₁ hadv hk
  refine NoRF.bind2 (Midfall.Generator.foldRangeIdxM n init f₁) k
    (NoRF.fold_blocks_noRF (β := β) w L n init f₁ hinit hf₁
      (fun i s r _ => hadv i s r)) (fun y hy => ?_)
  have hcur : y.2.1 = init.2.1 + w * n :=
    foldRangeIdxM_ok_advance w n f₁ init.1 init.2.1 init.2.2 y
      (fun i s r hr => hadv i s r hr) hy
  exact hk y hcur.symm

/-! ### 2. The first missing read bound: ARM AFFINE_SUM -/

/-- ARM AFFINE_SUM, READ-BOUNDED. The mixed run: '5 + 3·linCount + 5·productCount' bytes, the
    linear block first and the product block second in the source order the interpreter depends
    on (VmReference.lean:838-848). Two chained counted blocks, so this is the arm the single-fold
    lemma could not reach; the fit hypothesis is the validator's own stride for the arm
    ('quotientAffineSumOpLen' = 1 + 2·2 + linCount·3 + productCount·5).

    The zero-count refusal is discharged as a fault that names no read, NOT by a hypothesis: the
    walker walks a zero count happily and the interpreter does not, which is the asymmetry
    Qvm.lean:1854-1856 records. -/
theorem affineSum_noRF (bytes : List Nat) (idx l p : Nat)
    (hl : Midfall.Generator.readU16 bytes (idx + 1) = .ok l)
    (hp : Midfall.Generator.readU16 bytes (idx + 3) = .ok p)
    (hfit : idx + 5 + 3 * l + 5 * p ≤ bytes.length)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory) :
    NoRF (Midfall.Generator.evalQuotientIdentityStep bytes consts idx
      qOpAffineSum stack mem) := by
  unfold Midfall.Generator.evalQuotientIdentityStep
  simp (config := { decide := true }) only [reduceIte]
  rw [hl]
  simp only [bind, Except.bind]
  rw [hp]
  simp only [bind, Except.bind]
  by_cases hz : l = 0
  · rw [if_neg (by simp [hz])]
    exact NoRF.error (QVMFault.affineSumZeroCounts idx) (by intro i h; cases h)
  · by_cases hz2 : p = 0
    · rw [if_neg (by simp [hz2])]
      exact NoRF.error (QVMFault.affineSumZeroCounts idx) (by intro i h; cases h)
    · rw [if_pos (by simp [hz, hz2])]
      refine NoRF.bind (popStack_noRF stack idx) (fun px => ?_)
      refine fold_chain_step 3 (bytes.length - idx - 5) l (px.1, 0, mem) ?f₁ ?k ?_ ?_ ?_ ?_
      · show (0 : Nat) + 3 * l ≤ bytes.length - idx - 5
        omega
      · intro i s hi hs
        refine NoRF.bind (affineLinearTerm_noRF bytes (idx + 5 + s.2.1) ?_ consts s.2.2)
          (fun _ => NoRF.ok _)
        omega
      · intro i s r hr
        obtain ⟨acc, used, m⟩ := s
        obtain ⟨rv, rl, rm⟩ := r
        obtain ⟨lw, hlw, _⟩ := peel_bind hr
        have hl2 := affineLinearTerm_ok_mid hlw
        rcases lw with ⟨v, ln, mm⟩
        simp at *
        omega
      · intro y hy
        refine fold_chain_step 5 (bytes.length - idx - 5) p (y.1, y.2.1, y.2.2) ?f₂ ?k₂ ?_ ?_ ?_ ?_
        · show y.2.1 + 5 * p ≤ bytes.length - idx - 5
          simp only [Prod.snd, Prod.fst] at hy ⊢
          omega
        · intro i s hi hs
          refine NoRF.bind (affineProductTerm_noRF bytes (idx + 5 + s.2.1) ?_ consts s.2.2)
            (fun _ => NoRF.ok _)
          omega
        · intro i s r hr
          obtain ⟨acc, used, m⟩ := s
          obtain ⟨rv, rl, rm⟩ := r
          obtain ⟨pw, hpw, _⟩ := peel_bind hr
          have hl2 := affineProductTerm_ok_mid hpw
          rcases pw with ⟨v, ln, mm⟩
          simp at *
          omega
        · intro z hz3
          exact NoRF.ok _


/-! ### 3. The first two dynamic arms' WIDTH agreement -/

/-- The per-term body of the first RUN arm, named so the fold advance can be stated about it.
    Same convention as 'Qvm.lean:1197': the opcode is consed on at index 0, which is the general
    statement up to renaming the suffix. -/
def run1Body (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (term, len, mem') ← affineProductTerm bytes consts state.2.2 (0 + 3 + state.2.1)
    .ok (qvmFrAdd state.1 term, state.2.1 + len, mem')

/-- The per-term body of the second RUN arm: the LINEAR fused term, 3 bytes. -/
def run2Body (bytes : List Nat) (consts : List Word256) :
    Nat → QVMFr × Nat × QuotientRefMemory →
      Except QVMFault (QVMFr × Nat × QuotientRefMemory) :=
  fun _ state => do
    let (term, len, mem') ← affineLinearTerm bytes consts state.2.2 (0 + 3 + state.2.1)
    .ok (qvmFrAdd state.1 term, state.2.1 + len, mem')

theorem run1Body_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, run1Body bytes consts i s = .ok r → r.2.1 = s.2.1 + 5 := by
  intro i s r hr
  obtain ⟨acc, used, m⟩ := s
  obtain ⟨rv, rl, rm⟩ := r
  obtain ⟨pw, hpw, _⟩ := peel_bind hr
  have hl := affineProductTerm_ok_mid hpw
  rcases pw with ⟨v, ln, mm⟩
  simp at *
  omega

theorem run2Body_advance (bytes : List Nat) (consts : List Word256) :
    ∀ i s r, run2Body bytes consts i s = .ok r → r.2.1 = s.2.1 + 3 := by
  intro i s r hr
  obtain ⟨acc, used, m⟩ := s
  obtain ⟨rv, rl, rm⟩ := r
  obtain ⟨lw, hlw, _⟩ := peel_bind hr
  have hl := affineLinearTerm_ok_mid hlw
  rcases lw with ⟨v, ln, mm⟩
  simp at *
  omega

/-- ARM RUN_ADD_MUL_MEM_MEM_CONST_U8: the interpreter's consumed is 3 + 5n and the validator's
    stride for the same bytes is 1 + 2 + n·(2·2 + 1) = 3 + 5n. Both sides read the count with the
    SAME 'readU16', so no extra hypothesis is needed - which is what makes this the dynamic twin of
    'evalQuotientIdentityStep_consumed_agrees' rather than a weaker statement. -/
theorem consumed_agrees_runAddMulMemMemConstU8 (rest : List Nat)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep
        (qOpRunAddMulMemMemConstU8 :: rest) consts 0 qOpRunAddMulMemMemConstU8 stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen
        (qOpRunAddMulMemMemConstU8 :: rest) 0 = .ok len) :
    step.consumed = len := by
  unfold Midfall.Generator.evalQuotientIdentityStep at hstep
  simp (config := { decide := true }) only [reduceIte] at hstep
  obtain ⟨n, hn, hstep⟩ := peel_bind hstep
  by_cases hz : n = 0
  · rw [if_neg (by simp [hz])] at hstep
    cases hstep
  · rw [if_pos (by simp [hz])] at hstep
    obtain ⟨px, hpx, h1⟩ := peel_bind hstep
    obtain ⟨y, hy, h2⟩ := peel_bind h1
    have hrec := Except.ok.inj h2
    have hcur : y.2.1 = 0 + 5 * n :=
      foldRangeIdxM_ok_advance 5 n _ px.1 0 mem y (run1Body_advance (qOpRunAddMulMemMemConstU8 :: rest) consts) hy
    subst hrec
    show 3 + y.2.1 = len
    have hlen' : len = 3 + 5 * n := by
      unfold Midfall.Generator.QuotientValidator.quotientOpLen at hlen
      have hb : Midfall.Generator.QuotientValidator.byteAtPanic
          (qOpRunAddMulMemMemConstU8 :: rest) 0 3009 = .ok qOpRunAddMulMemMemConstU8 := rfl
      rw [hb] at hlen
      have hbridge : Midfall.Generator.QuotientValidator.readU16
          (qOpRunAddMulMemMemConstU8 :: rest) (0 + 1) = .ok n :=
        ((Midfall.Lowering.readU16_iff_readU16
            (bytes := qOpRunAddMulMemMemConstU8 :: rest) (k := 0 + 1)).mp hn)
      rw [hbridge] at hlen
      simp only [bind, Except.bind] at hlen
      rw [if_pos (show (qOpRunAddMulMemMemConstU8 == qOpRunAddMulMemMemConstU8) = true
          from by decide)] at hlen
      have hq : Midfall.Generator.quotientVmByteU16Bytes = 2 := rfl
      rw [hq] at hlen
      have h2 := Except.ok.inj hlen
      omega
    omega

/-- ARM RUN_ADD_MUL_CONST_U8_MEM_U16: consumed 3 + 3n against the validator's
    1 + 2 + n·(2+1) = 3 + 3n. Same mechanism, different stride - which is the point. -/
theorem consumed_agrees_runAddMulConstU8MemU16 (rest : List Nat)
    (consts : List Word256) (stack : List QVMFr) (mem : QuotientRefMemory)
    (step : IdentityStep) (len : Nat)
    (hstep : Midfall.Generator.evalQuotientIdentityStep
        (qOpRunAddMulConstU8MemU16 :: rest) consts 0 qOpRunAddMulConstU8MemU16 stack mem = .ok step)
    (hlen : Midfall.Generator.QuotientValidator.quotientOpLen
        (qOpRunAddMulConstU8MemU16 :: rest) 0 = .ok len) :
    step.consumed = len := by
  unfold Midfall.Generator.evalQuotientIdentityStep at hstep
  simp (config := { decide := true }) only [reduceIte] at hstep
  obtain ⟨n, hn, hstep⟩ := peel_bind hstep
  by_cases hz : n = 0
  · rw [if_neg (by simp [hz])] at hstep
    cases hstep
  · rw [if_pos (by simp [hz])] at hstep
    obtain ⟨px, hpx, h1⟩ := peel_bind hstep
    obtain ⟨y, hy, h2⟩ := peel_bind h1
    have hrec := Except.ok.inj h2
    have hcur : y.2.1 = 0 + 3 * n :=
      foldRangeIdxM_ok_advance 3 n _ px.1 0 mem y (run2Body_advance (qOpRunAddMulConstU8MemU16 :: rest) consts) hy
    subst hrec
    show 3 + y.2.1 = len
    have hlen' : len = 3 + 3 * n := by
      unfold Midfall.Generator.QuotientValidator.quotientOpLen at hlen
      have hb : Midfall.Generator.QuotientValidator.byteAtPanic
          (qOpRunAddMulConstU8MemU16 :: rest) 0 3009 = .ok qOpRunAddMulConstU8MemU16 := rfl
      rw [hb] at hlen
      have hbridge : Midfall.Generator.QuotientValidator.readU16
          (qOpRunAddMulConstU8MemU16 :: rest) (0 + 1) = .ok n :=
        ((Midfall.Lowering.readU16_iff_readU16
            (bytes := qOpRunAddMulConstU8MemU16 :: rest) (k := 0 + 1)).mp hn)
      rw [hbridge] at hlen
      simp only [bind, Except.bind] at hlen
      rw [if_pos (show (qOpRunAddMulConstU8MemU16 == qOpRunAddMulConstU8MemU16) = true
          from by decide)] at hlen
      have hq : Midfall.Generator.quotientVmByteU16Bytes = 2 := rfl
      rw [hq] at hlen
      have h2 := Except.ok.inj hlen
      omega
    omega


end Midfall.Lowering.QvmWalk
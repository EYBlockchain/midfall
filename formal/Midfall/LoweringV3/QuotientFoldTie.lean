-- |
-- Midfall.LoweringV3.QuotientFoldTie
--
-- FTIE - **THE FOLD-ARM REFERENCE TIE.** One file on the LoweringV3 side that imports BOTH the
-- emitted arm triples ('Midfall/LoweringV3/QuotientArms.lean') and the reference stream accumulator
-- ('Midfall/Generator/Quotient/VmReference.lean'), and states the two fold ties as plain
-- INSTANTIATIONS of the lemmas QSTREAM landed at VmReference.lean:1006 and VmReference.lean:1147.
-- The QSTREAM commit message at eb42b22 names this file as the whole of what remained: 'the missing
-- piece is ONE LoweringV3-side file importing both, whose two statements are instantiations of
-- those lemmas. Nothing else is owed.' This file is that piece and nothing more: two tie theorems,
-- two arm-post projections that make each tie a claim about the ARM's memory rather than about a
-- bare arithmetic expression, and the one word-level helper the addmod side needed.
--
-- WHY A NEW FILE, AND WHY NEITHER PARENT CAN HOLD THE TIE. 'VmReference' cannot state it:
-- 'QuotientArms -> QuotientFrame -> Lowering.Qvm (Qvm.lean:104) -> VmReference', and
-- 'WpX -> Qvm' (WpX.lean:49). So naming 'wAddmod'/'wMulmod' (WpX.lean:490-496) or
-- 'qArmValueAll_foldMain' (QuotientArms.lean:5867) from inside 'VmReference' is an import cycle.
-- QSTREAM therefore proved the ARITHMETIC half there - 'evalQuotientStreamStep_eq_emittedFoldMain'
-- spells the step as '(acc * y % r + value) % r' precisely because that is the '.toNat' of the word
-- this side can name and that side cannot - and left the NAMING half to this file.
--
-- THE TWO TIES, IN ONE LINE EACH.
--
--   * 'foldMainWord_eq_evalQuotientStreamStep' - the emitted FOLD_MAIN arm leaves
--     'wAddmod (wMulmod a y) x' at 'evalNumerMptr' (QuotientArms.lean:5861, repeated verbatim in
--     the 'StmtsContractAll' post at :5880), and that word's '.toNat' IS
--     'evalQuotientStreamStep a.toNat y.toNat x.toNat'.
--   * 'foldSelectorGapZeroWords_eq_evalQuotientStreamSelectorStep' - the emitted FOLD_SELECTOR arm
--     stores TWO words (QuotientArms.lean:6596): 'wMulmod a y' at 'evalNumerMptr' and
--     'wAddmod sv2 x' at the selector bucket. Both are reproduced, simultaneously, by
--     'evalQuotientStreamSelectorStep' at 'gap = 0'.
--
-- THE HONEST LABELS. These are load-bearing for what the project may CLAIM, and a reader who drops
-- them will overstate F1 coverage. They are stated here because the two theorems below cannot say
-- them about themselves.
--
-- 1. **FOLD_MAIN IS NOT IN THE F1 PROGRAM AT ALL.** F1's emitted opcode summary
--    (proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol:1877-1886) lists
--    '0x05 push_mem_u16, 0x06 add, 0x08 neg, 0x0b fold_selector, 0x0d mul_const_u8,
--    0x10 add_mem_u16, 0x11 mul_mem_u16, 0x19 native_permutation, 0x1f native_lookup,
--    0x1b native_identity' and **NO '0x0a'**. Re-derived at this HEAD rather than copied, and the
--    artifact is stronger than its own comment: the interpreter's dispatch contains 'case 0x0b {'
--    at :2256 and **no 'case 0x0a' anywhere in the file**, so a 0x0a byte falls to the 'default {
--    q_program_fail() }' arm. **So 'foldMainWord_eq_evalQuotientStreamStep' is a tie for an arm F1
--    does not emit.** It ties the template-level emitted triple 'qArmValueAll_foldMain' to the
--    reference step; it is NOT F1 coverage and must never be counted as such.
--
-- 2. **THE 'gap = 0' RESTRICTION IS A RESTRICTION OF THE EMITTED ARM, NOT A FACT ABOUT F1.** The
--    landed arm pins 'hgap : (pl &&& BitVec.ofNat 256 65535) = 0' (QuotientArms.lean:5898, and in
--    the contract pre at :6592), i.e. only the gap-zero branch was landed. At F1 the y^gap branch
--    IS live: the y-power table is emitted (:1739, 'lt q_y_power_i 22' -> selector_max_power = 21),
--    the emitted guard is 'if gt(q_sel_gap, 0x15)' (:2269, 0x15 = 21), four selector buckets are
--    zeroed (:1727, 'lt(q_sel_zero_off, 0x80)' at stride 0x20), and the branch itself is emitted at
--    :2283-2288 as 'if q_sel_gap { q_sel_acc := mulmod(q_sel_acc, mload(add(0x66a0, shl(5,
--    q_sel_gap))), r) }'. **So the foldSelector tie below covers a RESTRICTED CASE of an arm whose
--    FULL BEHAVIOUR F1 does exercise.** THE REMAINING WORK IS THE GENERAL-GAP VERSION: tie the
--    'gap <> 0' branch, i.e. the reference's 'qvmFrMul (buckets bucket) (evalQuotientStreamYPower y
--    gap)' (VmReference.lean:1123), against the emitted 'mulmod' at :2287 - which first needs the
--    emitted arm landed for a symbolic gap, and that is a QuotientArms card, not this one.
--    'evalQuotientStreamSelectorStep_bucket' (VmReference.lean:1128) already states the general-gap
--    reference side, so the reference owes nothing further; the emitted side owes the arm.
--
-- 3. WHAT THIS TIE IS NOT. It is not a 'qStepValue_X' refinement in the 'QuotientFrame' sense. The
--    reference has NO fold at all: QVR:325-333 REFUSES FOLD_MAIN and FOLD_SELECTOR inside an
--    identity expression and QVC:355-360 pushes 'Fq::ZERO' for a native marker, so the
--    'evalQuotientStream*' objects are a NEW port whose source of truth is the EMITTED Yul
--    (QNB = templates/partials/quotient_numerator/QuotientNumeratorBlock.yul), not reference.rs -
--    see the section header at VmReference.lean:940-968, which prints that finding rather than
--    hiding it. The tie therefore pins reference-port against emitted-Lean, both of which are our
--    own objects. Reading it as 'the Rust reference checks the fold' misreads it.
--
-- COUNTS, STATED AS REFERENCE-TIED AND NOT AS EMITTED-SIDE (the two have been conflated all
-- session). Before this file: 20 reference-tied arms. After: **21 with FOLD_SELECTOR** (a
-- restricted case of an arm F1 does emit) and **22 with FOLD_MAIN** (a full tie for an arm F1 does
-- NOT emit). The 22nd is real Lean but unreachable at F1, and is reported that way.
--
-- NO HYPOTHESIS WAS ADDED TO A ROW, to 'ValidV3', to a bundle or to the root (RULES). Both tie
-- theorems are UNCONDITIONAL at the word level - no canonicity side-condition, for the same reason
-- 'mulmod_toFr' (WpX.lean:533) and 'wMulmod_toNat' (QuotientFrame.lean:1022) carry none: the
-- 'addmod'/'mulmod' reduce by 'qvmFrModulus' BEFORE the 256-bit wrap, so the wrap loses nothing.
-- The two arm-post corollaries carry only the memory equation the arm itself concludes. No
-- 'native_decide', no fixture named in any statement (D-P71), no sorry in this file, and no new
-- '#eval' gate, so the KAT pin is untouched.
import Midfall.LoweringV3.QuotientArms
import Midfall.Generator.Quotient.VmReference
import Midfall.Yul.WpX
import Midfall.Tools.ConeSorries

open YulSemantics YulSemantics.EVM Midfall Midfall.Generator Midfall.Lowering
open Midfall.Yul Midfall.Yul.Bridge Midfall.Lowering.QuotientInterp
open Midfall.Lowering.GenAst
open Midfall.Yul.WpX
open Midfall.LoweringV3.QuotientFrame
open Midfall.LoweringV3.QuotientArms

set_option autoImplicit false

namespace Midfall.LoweringV3.QuotientFoldTie

/-! ## The word-level projection the ties need

    'wMulmod_toNat' is already proved in 'QuotientFrame' (QuotientFrame.lean:1022) and is reused
    unchanged. Its 'addmod' twin is NOT in the tree: 'QuotientFrame' has only the WORD-level
    'wAddmod_eq_qvmFrAdd' (:1336), which is not what a tie to a 'Nat'-level reference def can be
    rewritten with. So this file proves the missing twin, hypothesis-free for the same reason its
    mulmod parent is. -/

/-- EVM 'addmod(a, b, r)' at the scalar modulus, read as a natural: the field sum 'qvmFrAdd'. The
    'wMulmod_toNat' twin (QuotientFrame.lean:1022), whose mulmod side this file reuses rather than
    restates. No canonicity hypothesis - the reduction by 'qvmFrModulus < 2^256' makes the wrap
    lossless, exactly as in 'addmod_toFr' (WpX.lean:550). -/
theorem wAddmod_toNat (a b : U256) :
    (wAddmod a b).toNat = Midfall.Generator.qvmFrAdd a.toNat b.toNat := by
  have hlt : (a.toNat + b.toNat) % Midfall.Generator.qvmFrModulus < 2 ^ 256 :=
    Nat.lt_of_lt_of_le
      (Nat.mod_lt _ (by decide : 0 < Midfall.Generator.qvmFrModulus))
      (Nat.le_of_lt qvmFrModulus_lt256)
  show (BitVec.ofNat 256 ((a.toNat + b.toNat) % Midfall.Generator.qvmFrModulus)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rfl

/-! ## Tie 1 - FOLD_MAIN

    The instantiation QSTREAM's lemma was written to receive: 'evalQuotientStreamStep_eq_emittedFoldMain'
    (VmReference.lean:1006) states the step as '(acc * y % r + value) % r' and says in its own
    docstring that this is 'the .toNat of wAddmod (wMulmod acc y) value by WpX.lean:490-496' - a file
    it cannot import. Here is that naming step, discharged. -/

/-- **THE FOLD_MAIN REFERENCE TIE.** The word the emitted FOLD_MAIN arm stores at 'evalNumerMptr' -
    'wAddmod (wMulmod a y) x', QuotientArms.lean:5861 and :5880 - read as a natural IS the reference
    stream step 'evalQuotientStreamStep' (VmReference.lean:1000, QNB:1294-1298 'qn = qn*y + eval').
    Instantiation of 'evalQuotientStreamStep_eq_emittedFoldMain' at the three emitted words; the
    reference side is cited, not reproved. Unconditional: no canonicity hypothesis is needed on 'a',
    'y' or 'x', because both sides reduce by 'qvmFrModulus' before the 256-bit wrap.

    **F1 DOES NOT EMIT THIS ARM** - no '0x0a' in the opcode summary (:1877-1886) and no 'case 0x0a'
    in the dispatch (header note 1). This ties a template-level arm, not F1 coverage. -/
theorem foldMainWord_eq_evalQuotientStreamStep (a y x : U256) :
    (wAddmod (wMulmod a y) x).toNat =
      Midfall.Generator.evalQuotientStreamStep a.toNat y.toNat x.toNat := by
  rw [Midfall.Generator.evalQuotientStreamStep_eq_emittedFoldMain, wAddmod_toNat, wMulmod_toNat]
  show (Midfall.Generator.qvmFrMul a.toNat y.toNat + x.toNat) % Midfall.Generator.qvmFrModulus = _
  rfl

/-- **THE FOLD_MAIN TIE AT THE ARM'S OWN POST-STATE.** 'hmem' is exactly the memory conjunct the
    landed triple concludes: 'qArmValueAll_foldMain' (QuotientArms.lean:5867) ends with 'st' =
    '{ touchMemory (touchMemory st A 32) A 32 with memory := storeWord (storeWord st.memory A
    (wMulmod a y)) A (wAddmod (wMulmod a y) x) }' at :5880, from which 'hmem' follows by
    'congrArg EvmState.memory' alone - the record update overwrites the memory field, so the two
    'touchMemory' wrappers do not matter ('touchMemory_memory', Word.lean:104, is the same fact
    spelled the other way). Under that hypothesis the
    word the arm LEAVES IN MEMORY has '.toNat' equal to the reference step, so the tie is about the
    arm's post-state and not merely about an expression that happens to appear in its statement.
    Same caveat: **F1 does not emit FOLD_MAIN.** -/
theorem foldMain_armPost_eq_evalQuotientStreamStep {program : QuotientProgram}
    {st st' : EvmState} {a y x : U256}
    (hmem : st'.memory =
        storeWord (storeWord st.memory (BitVec.ofNat 256 program.evalNumerMptr).toNat (wMulmod a y))
          (BitVec.ofNat 256 program.evalNumerMptr).toNat (wAddmod (wMulmod a y) x)) :
    loadWord st'.memory (BitVec.ofNat 256 program.evalNumerMptr).toNat = wAddmod (wMulmod a y) x ∧
      (loadWord st'.memory (BitVec.ofNat 256 program.evalNumerMptr).toNat).toNat =
        Midfall.Generator.evalQuotientStreamStep a.toNat y.toNat x.toNat := by
  have h1 : loadWord st'.memory (BitVec.ofNat 256 program.evalNumerMptr).toNat
      = wAddmod (wMulmod a y) x := by
    rw [hmem, Midfall.Yul.Word.loadWord_storeWord_same]
  exact ⟨h1, by rw [h1, foldMainWord_eq_evalQuotientStreamStep]⟩

/-! ## Tie 2 - FOLD_SELECTOR at gap = 0

    'evalQuotientStreamSelectorStep_gapZero_matchesEmitted' (VmReference.lean:1147) reproduces BOTH
    words of the emitted ':6596' post for 'gap = 0'. The instantiation below feeds it the '.toNat' of
    the emitted accumulator word and a bucket array read off the emitted bucket words, and gets back
    the '.toNat' of both emitted words at once. -/

/-- **THE FOLD_SELECTOR REFERENCE TIE, AT 'gap = 0'.** The emitted FOLD_SELECTOR arm stores two
    words (QuotientArms.lean:6596): 'wMulmod a y' at 'evalNumerMptr' and 'wAddmod sv2 x' at the
    bucket. Instantiating 'evalQuotientStreamSelectorStep_gapZero_matchesEmitted'
    (VmReference.lean:1147) at the '.toNat' of the emitted words returns BOTH of them: the first
    component is the accumulator word and the bucket the step writes is the bucket word.
    'bucketWords' is the bucket array as the emitted side holds it - words, indexed by bucket - and
    the reference's 'Nat -> QVMFr' view of it is its '.toNat', which is the same bridge
    'wMulmod_toNat'/'wAddmod_toNat' supply. Unconditional, and a naming step plus one citation of the
    reference lemma.

    **THE 'gap = 0' IS A RESTRICTION OF THE EMITTED ARM, NOT OF F1.** The emitted arm pins
    'hgap : (pl &&& 65535) = 0' (QuotientArms.lean:5898), while F1 emits the general branch ('if
    q_sel_gap { ... mulmod ... }' at Halo2Verifier.sol:2283-2288, y-power table at :1739, guard
    'gt(q_sel_gap, 0x15)' at :2269). So this ties a RESTRICTED CASE of an arm whose full behaviour
    F1 does exercise. The general-gap version is the remaining work named in header note 2; the
    reference side of it already exists at 'evalQuotientStreamSelectorStep_bucket'. -/
theorem foldSelectorGapZeroWords_eq_evalQuotientStreamSelectorStep
    (a y x : U256) (bucketWords : Nat -> U256) (bucket : Nat) :
    (wMulmod a y).toNat =
      (Midfall.Generator.evalQuotientStreamSelectorStep y.toNat a.toNat
        (fun j => (bucketWords j).toNat) bucket 0 x.toNat).1 ∧
    (wAddmod (bucketWords bucket) x).toNat =
      (Midfall.Generator.evalQuotientStreamSelectorStep y.toNat a.toNat
        (fun j => (bucketWords j).toNat) bucket 0 x.toNat).2 bucket := by
  have h := Midfall.Generator.evalQuotientStreamSelectorStep_gapZero_matchesEmitted
    y.toNat a.toNat (fun j => (bucketWords j).toNat) bucket x.toNat
  refine ⟨?_, ?_⟩
  · rw [wMulmod_toNat]
    exact h.1.symm
  · rw [wAddmod_toNat]
    exact h.2.symm

/-- **THE FOLD_SELECTOR TIE AT THE ARM'S OWN POST-STATE.** 'hmem' is the memory conjunct of
    'qArmValueAll_foldSelector' (QuotientArms.lean:6576, post at :6596): the arm's final memory is
    'storeWord (storeWord st.memory A (wMulmod a y)) B (wAddmod sv2 x)' with 'A' the numerator slot
    and 'B = (sa + (si <<< 5)).toNat' the bucket address the arm computed. Under that hypothesis the
    BUCKET word the arm leaves in memory is the second component of the reference step, and the
    ACCUMULATOR word it leaves - 'wMulmod a y' - is tied as the step's first component.

    WHY THE ACCUMULATOR IS STATED AS A WORD AND NOT AS A MEMORY READ. Reading 'loadWord st'.memory A'
    back out of 'hmem' needs 'A ≠ B', i.e. that the numerator slot and the selector-bucket slot are
    distinct addresses in the render's layout. That is a LAYOUT fact about 'program' and
    'SELECTOR_ACC_MPTR', owned by 'QuotientFrame'/'QvmShift', not by this card - so it is named here
    as the one hypothesis this tie deliberately does NOT invent (RULES: if a fact is missing, name
    it). Note what the emitted arm does NOT already supply: its hypothesis 'hsacc'
    (QuotientArms.lean:5900) reads the bucket THROUGH the numerator store, which is a form that does
    not need 'A ≠ B' - so it is not a local proof of the distinctness either. Promoting the layout
    fact to a lemma is a separate card, owned by 'QuotientFrame'/'QvmShift'. -/
theorem foldSelector_armPost_eq_evalQuotientStreamSelectorStep {program : QuotientProgram}
    {st st' : EvmState} {a y x sv2 si sa : U256}
    (hmem : st'.memory =
        storeWord (storeWord st.memory (BitVec.ofNat 256 program.evalNumerMptr).toNat (wMulmod a y))
          (sa + (si <<< 5)).toNat (wAddmod sv2 x)) :
    (loadWord st'.memory (sa + (si <<< 5)).toNat).toNat =
      (Midfall.Generator.evalQuotientStreamSelectorStep y.toNat a.toNat
        (fun _ => sv2.toNat) si.toNat 0 x.toNat).2 si.toNat ∧
    (wMulmod a y).toNat =
      (Midfall.Generator.evalQuotientStreamSelectorStep y.toNat a.toNat
        (fun _ => sv2.toNat) si.toNat 0 x.toNat).1 := by
  have h := foldSelectorGapZeroWords_eq_evalQuotientStreamSelectorStep
    a y x (fun _ => sv2) si.toNat
  refine ⟨by rw [hmem, Midfall.Yul.Word.loadWord_storeWord_same, h.2], h.1⟩

/-! ## Gates -/

#print axioms Midfall.LoweringV3.QuotientFoldTie.wAddmod_toNat
#print axioms Midfall.LoweringV3.QuotientFoldTie.foldMainWord_eq_evalQuotientStreamStep
#print axioms Midfall.LoweringV3.QuotientFoldTie.foldMain_armPost_eq_evalQuotientStreamStep
#print axioms Midfall.LoweringV3.QuotientFoldTie.foldSelectorGapZeroWords_eq_evalQuotientStreamSelectorStep
#print axioms Midfall.LoweringV3.QuotientFoldTie.foldSelector_armPost_eq_evalQuotientStreamSelectorStep
#cone_sorries Midfall.LoweringV3.QuotientFoldTie.foldMainWord_eq_evalQuotientStreamStep
#cone_sorries Midfall.LoweringV3.QuotientFoldTie.foldMain_armPost_eq_evalQuotientStreamStep
#cone_sorries Midfall.LoweringV3.QuotientFoldTie.foldSelectorGapZeroWords_eq_evalQuotientStreamSelectorStep
#cone_sorries Midfall.LoweringV3.QuotientFoldTie.foldSelector_armPost_eq_evalQuotientStreamSelectorStep

end Midfall.LoweringV3.QuotientFoldTie

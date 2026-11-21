-- |
-- Midfall.LoweringV3.QuotientRows
--
-- ROW.Q (PLAN-V3 V3 row 40, ROUTE B): 'q_blockSim' and 'q_blockProgS' FOR EVERY RENDER, from named
-- leaves, with the builder's correctness in scope. STATEMENT card: the rows and their leaves land
-- typechecked, every hole carries a PROVED witness and a PROVED falsifier (W12), and the proofs are
-- ROW.Q.1/.3's, not this file's.
--
-- PROVENANCE. Sections 1, 3 and 5 are PORTED from
-- 'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean' section 7 (QuotientLin, ROW.Q): 'seg'
-- (:92), 'wMulmod' (:95), 'wSplit' (:869), 'qlinInner' (:860), 'qlin_split_loop' (:875),
-- 'identityCorrespondence_of_bridge_fixed' (:913, PROVED there - confirmed, and ported WITH its
-- proof rather than reproved, as the card instructs), 'q_blockSim' (:933) and 'q_blockProgS' (:939).
-- That file DOES NOT COMPILE (RECON.3 established it: 15 errors on the numInst/disjoint-residual
-- facts OBJ.4 proved are not table facts), so this is a copy, not an import. Statements are ported
-- VERBATIM; only names and the validity bundle are adapted, exactly as the evidence file's own
-- header (:31-33) prescribes. The three changes, and nothing else:
--
--   (a) THE VALIDITY HYPOTHESIS. The evidence file writes '(hR : R.Valid) (hpins : SimPins R)'.
--       'SimPins' is NOT a declaration in the tree: RECON.2 dissolved it and PROVED the projection
--       (Composition.lean:161 'pins_from_valid_and_headlineLaws' - three fields are conjuncts of
--       G1CodecHeadlineLaws, the fourth is ValidV3.program). So the rows take ValidV3 +
--       G1CodecHeadlineLaws, which is the bundle RECON.2's SimRowsV3/ProgRowsV3 ask for
--       (Composition.lean:140, :150). No clause was added to ValidV3 or to ValidW to close a leaf.
--   (b) THE SLICE. 'qlinInner' is the LINEARIZATION SCOPE, which after OBJ.2 is a SUFFIX of the
--       quotientLin slice and not the whole of it: see 'qlin_slice_widened' in section 2. The
--       evidence file's 'qlin_slice' (:855, marked PROVED) is no longer true of the tree, and the
--       card's section 7 header still describes the pre-OBJ.2 slice. Reported as a false premise.
--   (c) THE MULMOD NAME. The evidence file's 'wMulmod' takes the modulus as a third argument
--       because the loop's 'r' is a symbolic local; the tree already has a two-argument
--       'WpX.wMulmod' fixed at the field modulus. Different functions, so the port is renamed
--       'wMulmodAt' rather than shadowing the landed one. Same definition, same three binders.
--
-- T3.10'S TWO OPEN ITEMS, BOTH ANSWERED WITH PROOFS.
--   (i) 'cursor < exprEnd' IS the intended reading of 'QSegment.inWindow'. Section 5 proves BOTH
--       halves: the reference VM ERRORS on an empty segment ('evalQuotientIdentity_nil') and the
--       EMITTED loop exits NORMALLY on one ('qvmLoop_empty_segment', by the Step rules - no
--       unrolling of the interpreter's thirty-one arms, which is what makes it cheap). The
--       non-strict contract is then exhibited FALSE of the emitted loop
--       ('qinterpRefines_falsifier_empty_segment'), so the strictness is a correction and not a
--       preference. T3.10's reading is CONFIRMED and nothing in 'QuotientInterp.lean' is changed.
--   (ii) THE REDUCIBLE BRIDGE. 'evalQuotientIdentity' is not kernel-reducible ('rfl' fails even on
--       the empty program). Section 5 lands the two equations that DO reduce:
--       'evalQuotientIdentity_nil' (the empty program) and 'evalQuotientIdentityLoop_step' (the
--       general one-step unfolding, which is what lets a proof induct over bytes instead of trying
--       to compute a whole run). What remains is named at the end of section 5.
--
-- ROW.Q.5, NOW STATED AND NOW PROVED. ROW.Q reported this leaf UNSPEAKABLE: with all six generated
-- line families spliced through 'YulParse.parseLines' at 'GenAstQvm.lean:61-69' there was no block
-- producer to induct over (PG-Q-OBJECT). QEMIT (d835506) and QEMIT2 (f10aba9) landed AST twins of the
-- producers for all five in-scope families, so the leaf is statable, and section 10 states and PROVES
-- it: the value of each family's emitted block on a SYMBOLIC input list is the value the producer's
-- own recursion computes, by list induction over that list. The inductions live with the twins, in
-- 'Midfall/Lowering/GenAstQvmFamilies.lean'; section 10 is the consumer that cites them and adds the
-- slicing corollary in this file's own 'seg' vocabulary. No row's statement changed: the rows still
-- name ROW.Q.1/.3/.4 and the builder rows, and ROW.Q.5's leaves are now PROVED leaves rather than a
-- paragraph about a missing prerequisite.
--
-- NO FIXTURE (D-P71). Every statement is quantified over the render 'R : Render p G₁ G₂ Gₜ' and over
-- the program, table and window it reads. 'poseidonRender' appears nowhere in this file, and neither
-- does any constant of it. The witnesses and falsifiers are generic as well.
--
-- AXIOMS. Everything proved here is on [propext, Classical.choice, Quot.sound]; no 'native_decide'
-- (D-P17); nothing is added to the headline cone (this file is not imported by Instances/), and the
-- cone still prints exactly ONE REFUTED row (poseidon_valid).

import Midfall.LoweringV3.Statements
import Midfall.LoweringV2.Stages
import Midfall.Lowering.QuotientInterp
import Midfall.Lowering.GenAstQvmFamilies
import Midfall.Lowering.QvmFold
import Midfall.Yul.Contracts
import Midfall.Yul.WpTac
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.QuotientRows

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.QuotientInterp

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

variable {c : ExternalCalls} {g : ExternalGas}

open Lean Elab Tactic Meta in
/-- Close an equality by 'Eq.refl', leaving the definitional check to the KERNEL. VERBATIM port from
the evidence file's section 0 (:83-87): the elaborator's 'rfl' runs 'Meta.whnf', which exceeds the
default heartbeats on an inlined block; the kernel reducer does not. No axiom is added, and no
heartbeat or recursion limit is raised anywhere in this file. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, _, rhs) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  goal.assign (← mkEqRefl rhs)

/-! ### 1. VOCABULARY, PORTED VERBATIM (GeneratorRows.lean sections 0 and 7) -/

/-- Statements 'i .. i + j - 1' of a block. VERBATIM from the evidence file (:92). A child lemma is
about one segment of an inlined emitter output. -/
def seg (b : Block EVM.Op) (i j : Nat) : Block EVM.Op := (b.drop i).take j

/-- EVM 'mulmod' at an ARBITRARY modulus word, as the dialect computes it. The evidence file's
'wMulmod' (:95) verbatim, renamed 'wMulmodAt' because the tree's 'WpX.wMulmod' is the same function
fixed at the field modulus (header change (c)). -/
def wMulmodAt (a b n : U256) : U256 :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)

/-- The pair '(x^(2^i - 1), x^(2^i))' after 'i' iterations of the split loop. VERBATIM (:869-872). -/
def wSplit (r x : U256) : Nat → U256 × U256
  | 0 => (1, x)
  | i + 1 => (wMulmodAt (wMulmodAt (wSplit r x i).1 (wSplit r x i).1 r) x r,
              wMulmodAt (wSplit r x i).2 (wSplit r x i).2 r)

/-- The nine statements of the linearization scope, constants inlined (:860-863). After OBJ.2 this is
a SUFFIX of the quotientLin slice, not the slice: see 'qlin_slice_widened'. -/
def qlinInner (consts : Inline.Consts) (k : Nat) : Block EVM.Op :=
  match Inline.inlineContractConstants consts (GenAst.emitQuotientLinAt k) with
  | [Stmt.block body] => body
  | _ => []

/-- The scope has NINE statements, at every table and every exponent: PROVED by the kernel reducer,
on [propext] alone. This is what makes 'seg (qlinInner consts k) 4 1' a segment of a real block and
not an out-of-range slice, which would silently be the empty block and would make the leaf vacuous. -/
theorem qlinInner_length (consts : Inline.Consts) (k : Nat) :
    (qlinInner consts k).length = 9 := by kernel_rfl

/-- The scope binds its exponent as the second statement, from the literal the emitter interpolated:
PROVED by reduction at an arbitrary table and exponent, so the leaf's pre clause about 'k' is about a
name the emitted code really declares and not about a fixture value. -/
theorem qlinInner_binds_k (consts : Inline.Consts) (k : Nat) :
    (qlinInner consts k)[1]? = some (Stmt.letDecl ["k"] (some (ylit k))) := by
  kernel_rfl

/-! ### 2. THE SLICE, CORRECTED FOR OBJ.2 (port change (b)) -/

/-- **THE QUOTIENTLIN SLICE IS THE WIDENED REGION.** The evidence file's 'qlin_slice' (:855, marked
PROVED) says the slice is the linearization scope alone. That stopped being true at OBJ.2:
'GenAstDispatch.emitPartialM' puts the quotient helper definitions and the whole numerator block IN
FRONT of the scope, inside the same partial. This is the fact as the tree now is, and it is what
makes T3.10's contract at 'GenAst.qvmLoop' a LEAF of 'q_blockSim' rather than a statement about a
program the verifier does not run. PROVED by reduction. -/
theorem qlin_slice_widened (R : Render p G₁ G₂ Gₜ) :
    R.slice Partial.quotientLin =
      Inline.inlineContractConstants R.consts
        (GenAst.emitQuotientHelpersAt (partialCtxOfVerifier R.model).quotientPow5Helper ++
          GenAst.emitQuotientNumerator (partialCtxOfVerifier R.model) ++
          GenAst.emitQuotientLin R.pv) := rfl

/-! ### 3. THE ROWS (GeneratorRows.lean:933, :939) -/

/-- **THE GENERIC QUOTIENT ROW, SOUNDNESS SIDE, FOR EVERY RENDER.** Ported from
'GeneratorRows.lean:933-936' with the two changes the evidence file's own header prescribes (header
change (a)): 'R.Valid' becomes 'ValidV3 R' and 'SimPins R' becomes 'G1CodecHeadlineLaws R.E.g1',
which is what derives it. The conclusion, the partial, the permissive calls, the 'SoundSide'
hypothesis and the binder order are the evidence file's, verbatim.

NAMED LEAVES (card steps 3 and 4; a filled proof's cone is exactly these):
  * ROW.Q.1 - 'qlin_split_loop' below: the squaring walk of the linearization scope.
  * ROW.Q.3 - 'Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop': T3.10's contract at the
    emitted interpreter loop, for every context, every 'QuotientProgram' and every template table.
    Its own leaves are the eight 'QArmFamily' arms of that file's section 6.
  * ROW.Q.4 - the frame valuation: 'QuotientInterp.Agrees' is the windowed form T3.10 landed; the
    full 'QuotientReadModel' window list is this card's other named child.
  * the builder, IN SCOPE as cited rows and NOT restated here: 'Qvm.lean:631
    qvm_compile_correct_identity', :698 'qvm_compile_correct_certifier', :713
    'qvm_compile_correct_program', :768 'qvm_validated_noBoundsFault', :995
    'builder_segments_total'; 'QvmFold.lean:364 quotientFold_matches_linearization', :407
    'qvm_compile_correct_stream'. All six are registered rows of P-SE and are ROW.Q.6/.7/.8/.9's.
  * the glue: the eight statements of the scope around the loop, and the exit shape the scope hands
    to '.pcs.pre'.
  * ROW.Q.5 - the generated line families, ONE LEAF PER FAMILY, as a list induction over the family's
    block producer: 'qEmitInlineFamily_value' and 'qEmitNativeIdentityFamily_value' (inline and
    native identity), 'qEmitPostVmFamily_shape' (post-VM suffix), 'qEmitNativePermutationA_shape' and
    'qEmitNativeLookupA_shape' (the two native loop families), all in
    'Midfall.Lowering.GenAst', with the consumer corollaries in section 10 below. PROVED, not stated:
    the twins QEMIT and QEMIT2 landed are the induction targets. QEMIT3 CLOSED the two
    native loop families: their 'mapM' step functions and the compactor's inner 'let rec go' are
    top-level 'def's now, so 'qEmitNativeLookupA_shape' is the per-item value lemma ROW.Q.5 printed as
    unreachable and 'qPushMstoreMloadLiteralRunsA_rejected' and 'qPushMstoreMloadLiteralRunsA_run3' are the
    family-4 per-entry run decomposition (one store for a rejected entry, one loop for a run of
    three). WHAT IS NOT LANDED, NAMED: the accumulator split for an ARBITRARY running block - see
    'qMloadRunGoA_split_gap' in that file.

Q1 STATUS (this box: what landed, what is measured-blocked, and where the leaves now live - see
'Midfall/LoweringV3/QuotientFrame.lean'):
  * ROW.Q.4 is LANDED. The frame valuation is 'AgreesFrame_memOfρ' and its converse
    'AgreesFrame_memOfρ_only_if' - 'AgreesFrame' at a 'memOfρ' memory IS the ρ-clause, both ways -
    and 'Agrees_memOfρ_nonvacuous' exhibits all three agreement clauses on a NON-EMPTY frame window.
    The per-arm value equations are 'qStepValue_*' for 23 of the 26 identity arms (the 22 static arms of Qvm.lean:1197 plus MODARITH7); and the reference
    loop has an equational theory ('qLoop_go_live', 'qLoop_go_pos', 'qLoop_go_done') that yields
    'evalQuotientIdentity_one' - the first theorem in the tree to name the reference VM's output -
    including 'evalQuotientIdentity_empty', which is the exact equation QuotientInterp.lean:354
    records as FAILING by 'rfl'.
  * ROW.Q.3 IS LANDED ON THREE SIDES AND OPEN ON ONE. (i) DISPATCH: 'selectSwitch' does not reduce
    under 'simp' even at a literal label, because its 'decide' is on 'D.litValue (Literal.number n)';
    'qDialect_litValue_number' is 'rfl', and with 'decide_eq_true' the dispatch reduces at a SYMBOLIC
    template table ('qSwitch_arm', 'qSwitch_failClosed' - the latter is the prose fail-closed claim at
    QuotientInterp.lean:102, now a theorem). (ii) IDENTIFICATION: the emitter change Q1 named as the
    blocker was made by QEMIT4 - every one of the 31 arm bodies is a top-level 'def' 'qArmBodyX' in
    'GenAstQvm.lean' (a binding change, values untouched: the 'numA_*' reconstruction gates and the
    object fingerprint are unmoved), and ALL EIGHT 'QArmFamily' THEOREMS ARE PROVED
    ('qArmFamily_push/token/arith/fused/run/limb/fold/native', QuotientInterp.lean section 6.5): for
    every arm, the emitter's own arm list carries the named body at that arm's label. Q1's sentence
    "NONE of the eight 'QArmFamily' arms is closed" is STALE and is corrected here. (iii) VALUE, for
    the register-only arms: QVAL lands the first instances of the other half QEMIT4 declined to
    manufacture - 'qArmValue_neg' (QuotientFrame.lean section H) is a 'StmtsContract' whose proof is
    a 'Step' derivation EXECUTING the emitter's own 'qArmBodyNeg' and landing 'q_top' on the very
    'qvmFrNeg v' that 'qStepValue_neg' pushes. (iv) STILL OPEN, NAMED: the 'StmtsContractAll'
    every-run form of those arms (the halt case tree, or 'of_det' at oracle functionality); the 20
    arms that read memory (their pre must pin 'loadWord' against the reference reader - the operand
    decode bridge is now landed as 'Midfall/Yul.Word.loadWord_topByte' / '_mask', which also closes
    the F2 opcode-fetch gap); and the three count-prefixed arms of QuotientFrame.lean section F, whose
    value half is the 'foldRangeIdxM' <-> 'yfor' loop induction and is NOT landed.
  * ROW.Q.1 is UNTOUCHED. The invariant is 'x_pow_2i = x^(2^i)' and 'x_pow_2i_minus1 = x^(2^i - 1)'
    modulo 'r' after 'i' iterations of the two-statement body at GenAst.lean:1033-1036; it needs a
    'Step.forLoop' induction with a 'mulmod' arithmetic step over 'wSplit'. That is a loop-invariant
    proof, not a missing idea, and it did not fit this box alongside ROW.Q.4. -/
theorem q_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (hside : SoundSide R H cd) (g : ExternalGas) :
    BlockSim R Partial.quotientLin H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **THE GENERIC QUOTIENT ROW, PROGRESS SIDE, FOR EVERY RENDER.** Ported from
'GeneratorRows.lean:939-943' with the same two changes, and with the evidence file's seven-law
'G1CodecLaws' read as the four-law 'G1CodecHeadlineLaws' - RECON.2's step 3, "the rows are re-gated
on FOUR laws, not seven" (Composition.lean:42-45). NAMED LEAVES: the same ROW.Q.1/.3/.4, plus
existence of a run through the numerator (the QVM's own memory guards, 'qvm_validated_noBoundsFault'
at Qvm.lean:768) and 'CompleteSide' for the challenge values the scope reads. -/
theorem q_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.quotientLin H vkAddr product cd := by
  sorry

/-- **ROW.Q.1 - THE SPLIT LOOP.** VERBATIM from 'GeneratorRows.lean:875-887': binders, the 'hr'
hypothesis that the table does not pin 'r', the 'k < 2 ^ 256' bound, the pre and the post. Statement
4 of the linearization scope is the squaring walk that computes '(x^(2^k - 1), x^(2^k))' in ONE
loop; the bound is a literal in the emitted code but the test reads the LOCAL 'k', which is why the
pre pins it. The two body statements are ordered and not interchangeable (GenAst.lean:1024-1028). -/
theorem qlin_split_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k : Nat) (hk : k < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (qlinInner consts k) 4 1)
      (fun V _ => VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧
        VEnv.get V "x_pow_2i_minus1" = some 1 ∧
        (VEnv.get V "x").isSome ∧ VEnv.get V "x_pow_2i" = VEnv.get V "x" ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        ∃ x rw, VEnv.get V "x" = some x ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "x_pow_2i_minus1" (wSplit rw x k).1)
            "x_pow_2i" (wSplit rw x k).2) := by
  sorry

/-! ### 4. THE BRIDGE CORRECTION (card step 1) -/

/-- **'identityCorrespondence_of_bridge', CORRECTED** - PORTED VERBATIM, with its proof, from
'GeneratorRows.lean:913-930'. The card marks that lemma PROVED and tells this card to reuse it
rather than reprove it; confirmed, and it is ported with the proof unchanged. The added hypothesis is
'hsnd', the value half the refutation at 'QvmFold.lean:749 bridgeCounterexample_conclusion_fails'
shows cannot be derived from the other three. The refuted
'Midfall.Lowering.identityCorrespondence_of_bridge' (QvmFold.lean:327) is DELETED in this same
commit, which is card step 1 and W13's pairing requirement; its satisfiability witness
(QvmFold.lean:718) and its refutation (:749) stay, since they are what the deletion rests on. -/
theorem identityCorrespondence_of_bridge_fixed (plan : QuotientProgramPlan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) (ρ : Valuation)
    (horder : exprs.size = (globalIdentities plan).length)
    (hvals : vals = (globalIdentities plan).map
              fun id => (evalExprρ ρ id.expr).toOption.getD 0)
    (htags : ∀ i (h : i < (globalIdentities plan).length),
              (exprs[i]?.map Prod.fst) =
                some (match (globalIdentities plan)[i]'h |>.target with
                      | .main => (none : Option Nat)
                      | .selector s => plan.sortedSimple[s]?))
    (hsnd : ∀ i, i < (globalIdentities plan).length →
              exprs[i]?.map Prod.snd = some (qvmToFr (vals[i]?.getD 0))) :
    IdentityCorrespondence plan exprs vals := by
  refine ⟨horder, by rw [hvals, List.length_map], fun i h => ⟨hsnd i h, ?_⟩⟩
  have ht := htags i h
  cases htgt : ((globalIdentities plan)[i]'h).target with
  | main => rw [htgt] at ht; exact ht
  | selector s => rw [htgt] at ht; exact ht

/-! ### 5. THE EMPTY SEGMENT: T3.10'S 'cursor < exprEnd', CONFIRMED BOTH WAYS -/

/-- 'lt' at two equal words is zero: the one opcode fact both halves of the confirmation share. -/
theorem stepOp_lt_same (a : U256) (st : EvmState) :
    (Bridge.Dialect c g).Builtin Op.lt [a, a] st (.ok [0] st) := by
  show stepOp Op.lt [a, a] st = some (.ok [0] st)
  show bin (fun x y => b2w (x.ult y)) [a, a] st = some (.ok [0] st)
  simp [bin, b2w, BitVec.ult]

/-- The condition of a loop over two registers that hold the same word evaluates to zero. Built from
the vendored 'Step' rules, not from 'wp_run': no slice is unrolled. -/
theorem eval_lt_same (p₁ p₂ : String) (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (a : U256)
    (h₁ : VEnv.get V p₁ = some a) (h₂ : VEnv.get V p₂ = some a) :
    EvalExpr (Bridge.Dialect c g) funs V st (yop Op.lt [yvar p₁, yvar p₂]) (.vals [0] st) := by
  refine Step.builtinOk (D := Bridge.Dialect c g) (op := Op.lt) (args := [yvar p₁, yvar p₂])
    (argvals := [a, a]) (st1 := st) (rets := [0]) (st2 := st) ?_ ?_
  · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar p₂]) (e := yvar p₁)
      (restvals := [a]) (v := a) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (e := yvar p₂) (restvals := [])
        (v := a) (st1 := st) (st2 := st) (Step.argsNil (D := Bridge.Dialect c g))
        (Step.var (D := Bridge.Dialect c g) h₂))
      (Step.var (D := Bridge.Dialect c g) h₁)
  · exact stepOp_lt_same a st

/-- **A 'for' loop whose condition is zero exits normally, whatever its body.** Body-independent on
purpose: this is the one place in ROW.Q where the interpreter's thirty-one arms are NOT unrolled,
and it is what makes the empty-segment result cost nothing. A 'Step'-rule fact ('Step.forLoop' plus
'Step.loopDone'), not a 'wp' evaluation - so it cannot time out the way QPROBE's unrolling did. -/
theorem forLoop_false (p₁ p₂ : String) (funs : FunEnv (Bridge.Dialect c g))
    (body : Block EVM.Op) (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hcond : EvalExpr (Bridge.Dialect c g) ([] :: funs) V st
      (yop Op.lt [yvar p₁, yvar p₂]) (.vals [0] st)) :
    ExecStmts (Bridge.Dialect c g) funs V st
      [Stmt.forLoop [] (yop Op.lt [yvar p₁, yvar p₂]) [] body] V st .normal := by
  have hres : restore (D := Bridge.Dialect c g) V V = V := by simp [restore]
  have h₁ : ExecStmts (Bridge.Dialect c g) funs V st
      [Stmt.forLoop [] (yop Op.lt [yvar p₁, yvar p₂]) [] body] (restore V V) st .normal :=
    Step.seqCons (D := Bridge.Dialect c g)
      (Step.forLoop (D := Bridge.Dialect c g) (init := []) (c := yop Op.lt [yvar p₁, yvar p₂])
        (post := []) (body := body) (Vinit := V) (stinit := st) (Vend := V) (stend := st)
        (o := .normal) (Step.seqNil (D := Bridge.Dialect c g))
        (Step.loopDone (D := Bridge.Dialect c g) (c := yop Op.lt [yvar p₁, yvar p₂])
          (post := []) (body := body) (cv := 0) hcond (by rfl)))
      (Step.seqNil (D := Bridge.Dialect c g))
  rw [hres] at h₁
  exact h₁

/-- The five registers 'segmentV' writes, read back by name. 'AtSegment' is defined as five 'rfl's on
top of these, and the empty-segment exhibit below needs 'q_pc' and 'q_end' without unfolding the
emitter. -/
theorem segmentV_get_q_pc {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (s : QSegment) (top : U256) (hasTop : Bool) :
    VEnv.get (segmentV (c := c) (g := g) (program := program) s top hasTop) "q_pc" =
      some (BitVec.ofNat 256 (s.base + s.cursor)) := rfl

theorem segmentV_get_q_end {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (s : QSegment) (top : U256) (hasTop : Bool) :
    VEnv.get (segmentV (c := c) (g := g) (program := program) s top hasTop) "q_end" =
      some (BitVec.ofNat 256 (s.base + s.exprEnd)) := rfl

/-- The initial state is not a revert: needed by the empty-segment exhibit, since the loop that exits
normally on an empty segment leaves the state it was handed. -/
theorem not_Reverted_init : ¬ Midfall.Lowering.Reverted (EvmState.init) := by
  have h : (EvmState.init : EvmState).halted = none := rfl
  simp [Midfall.Lowering.Reverted, Midfall.Lowering.revertedOf, h]

/-- **HALF 1 OF THE CONFIRMATION: THE EMITTED LOOP EXITS NORMALLY ON AN EMPTY SEGMENT.** 'q_pc' and
'q_end' are two of the five registers 'AtSegment' pins, to 'base + cursor' and 'base + exprEnd'
('QuotientInterp.lean:200-201'), so 'cursor = exprEnd' IS 'q_pc = q_end', which is exactly the false
condition. PROVED for every context, every program and every template table - and with no fuel,
because 'forLoop_false' never looks at the body. -/
theorem qvmLoop_empty_segment (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (a : U256)
    (hpc : VEnv.get V "q_pc" = some a) (hend : VEnv.get V "q_end" = some a) :
    ExecStmts (Bridge.Dialect c g) funs V st [GenAst.qvmLoop ctx program tcq] V st .normal := by
  obtain ⟨body, hbody⟩ : ∃ body, GenAst.qvmLoop ctx program tcq =
      Stmt.forLoop [] (yop Op.lt [yvar "q_pc", yvar "q_end"]) [] body := ⟨_, rfl⟩
  rw [hbody]
  exact forLoop_false "q_pc" "q_end" funs body V st
    (eval_lt_same "q_pc" "q_end" ([] :: funs) V st a hpc hend)

/-- **HALF 2 OF THE CONFIRMATION, AND THE FIRST LANDED PIECE OF THE REDUCIBLE BRIDGE: THE REFERENCE
VM ERRORS ON AN EMPTY SEGMENT.** 'evalQuotientIdentity [] consts mem' ends in
'QVMFault.stackLengthMismatch 0' - the Rust pops a value it never pushed (VmReference.lean:904-907).
T3.10 recorded that this is NOT kernel-reducible ('rfl' fails) and that every reference-VM gate in
the tree is therefore an '#eval'. It is PROVABLE, and this is the proof: the 'where'-clause 'go' does
not unfold under 'rfl' but it does unfold under 'simp [evalQuotientIdentityLoop.go]', and the 'do'
block's 'Except.bind' unfolds with it. -/
theorem evalQuotientIdentity_nil (consts : List Midfall.Word256) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentity [] consts mem =
      .error (QVMFault.stackLengthMismatch 0) := by
  simp [Midfall.Generator.evalQuotientIdentity, Midfall.Generator.evalQuotientIdentityLoop,
    Midfall.Generator.evalQuotientIdentityLoop.go, bind, Except.bind]

/-- **THE ONE-STEP UNFOLDING EQUATION, FOR ANY PROGRAM.** The second landed piece of the bridge, and
the shape ROW.Q.3 needs: at any cursor inside the program the loop is one step of
'evalQuotientIdentityStep' followed by the loop at the advanced cursor. This is what lets a proof
about the reference VM induct over BYTES instead of trying to compute a whole run - the wall QPROBE
hit from the other side. PROVED, on the standard three axioms. -/
theorem evalQuotientIdentityLoop_step (bytes : List Nat) (consts : List Midfall.Word256)
    (fuel idx : Nat) (stack : List QVMFr) (mem : QuotientRefMemory) (h : idx < bytes.length) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts (fuel + 1) idx stack mem =
      (Midfall.Generator.evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem).bind
        (fun s => Midfall.Generator.evalQuotientIdentityLoop.go bytes consts fuel
          (idx + s.consumed) s.stack s.mem) := by
  simp [Midfall.Generator.evalQuotientIdentityLoop.go, bind, Except.bind, h]

/-- The contract with the NON-STRICT window: 'QInterpRefines' with 'cursor ≤ exprEnd' in place of
'cursor < exprEnd' and nothing else changed. Defined ONLY to be refuted below; the landed contract
keeps the strict reading, and this file does not touch it. -/
def QInterpRefinesLe {D : YulSemantics.Dialect} [DecidableEq D.Value]
    (funs : FunEnv D) (interp : Block D.Op)
    (reverts : D.State → Prop) (word : U256 → D.Value)
    (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : D.State → QuotientRefMemory → QSegment → Prop)
    (AtSegment : VEnv D → D.State → QSegment → Prop)
    (Top : VEnv D → D.State → D.Value → Prop) : Prop :=
  ∀ (s : QSegment) (mem : QuotientRefMemory), s.cursor ≤ s.exprEnd →
    StmtsContractAll (D := D) funs interp
      (fun V st => AtSegment V st s ∧ Agrees st mem s)
      (fun _ _ V' st' o => (o = .halt ∧ reverts st') ∨
        (o = .normal ∧ ∃ v mem',
          Midfall.Generator.evalQuotientIdentity
            ((bytes.drop s.cursor).take (s.exprEnd - s.cursor)) consts mem = .ok (v, mem') ∧
          Top V' st' (word (BitVec.ofNat 256 v)) ∧ AtSegment V' st' s.atEnd))

/-- **THE STRICT WINDOW IS A CORRECTION, NOT A PREFERENCE (T3.10 open item (i), ANSWERED: WE WENT
WITH 'cursor < exprEnd').** The non-strict contract is FALSE of the emitted interpreter loop, at
the real 'AtSegment', the real 'qinterpTop' and the real 'Midfall.Lowering.Reverted', for EVERY
context, program, table, program window and constant table. Take the empty segment '[cursor,
cursor)', which 'AtSegment' turns into 'q_pc = q_end': the loop exits normally there
('qvmLoop_empty_segment'), the exit is not a revert, and the reference VM errors on the empty
program ('evalQuotientIdentity_nil'), so neither disjunct of the post can hold. This is the exhibit
T3.10 asked ROW.Q to confirm, and it is why 'QSegment.inWindow' is strict. -/
theorem qinterpRefines_falsifier_empty_segment {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (bytes : List Nat) (consts : List Midfall.Word256) :
    ¬ QInterpRefinesLe (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun _ _ _ => True)
      funs [GenAst.qvmLoop ctx program tcq] bytes consts := by
  intro H
  set V₀ := segmentV (c := c) (g := g) (program := program) ⟨0, 0, 0, 0⟩ 0 false
  have hrun : ExecStmts (Bridge.Dialect c g) funs V₀ EvmState.init
      [GenAst.qvmLoop ctx program tcq] V₀ EvmState.init .normal :=
    qvmLoop_empty_segment ctx program tcq funs V₀ EvmState.init (BitVec.ofNat 256 0)
      (segmentV_get_q_pc program ⟨0, 0, 0, 0⟩ 0 false)
      (segmentV_get_q_end program ⟨0, 0, 0, 0⟩ 0 false)
  have h := H ⟨0, 0, 0, 0⟩ (quotientRefMemoryNew Midfall.Bytes.empty) (Nat.le_refl 0)
    V₀ EvmState.init ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩ V₀ EvmState.init .normal hrun
  cases h with
  | inl h => exact not_Reverted_init h.2
  | inr h =>
      obtain ⟨_, _, hv, _, _⟩ := h.2
      simp only [List.drop_zero, List.take_zero, Nat.zero_sub] at hv
      rw [evalQuotientIdentity_nil] at hv
      cases hv

/-- **WHAT THE BRIDGE STILL OWES, NAMED EXACTLY (T3.10 open item (ii)).** Three equations now
reduce: 'evalQuotientIdentity_nil' (the empty program), 'evalQuotientIdentityLoop_step' (one step at
a cursor inside the program) and 'evalQuotientIdentityLoop_atEnd' (the loop at the end cursor). They
are enough to refute the non-strict window, which is what this card needed. They are NOT enough for
the strongest falsifier T3.10 described (right cursor, right validity bit, WRONG constant slot),
because that one needs the reference VM's VALUE on a NON-EMPTY program. The exact remaining goal
state, for the shortest program that exercises the constant window, is

    evalQuotientIdentity [qOpPushConstU8, 1] consts mem = .ok (v, mem')

with 'v' named - i.e. 'v = consts.getD 1 0' once the arm is unfolded. Two things stand between here
and that, and both are finite: (1) the '¬ idx < bytes.length' branch of 'go' at a SUCCESOR fuel (the
'atEnd' lemma above is the fuel-zero case; the successor case is the same 'simp [go]' one-liner and
ROW.Q.3 should land it), and (2) a per-ARM VALUE equation for 'evalQuotientIdentityStep' - Qvm.lean
:1197 proves 22 arms agree with the validator on 'consumed', which is the length half, but nothing in
the tree states what the arm PUSHES. The push is 'mem.literal' at the constant slot, and for a
SYMBOLIC 'QuotientRefMemory' that is a function application the kernel cannot reduce: this is the
same wall as QPROBE's, on the reference side rather than the Yul side, and it is why every
reference-VM gate in 'VmReference.lean' is an '#eval'. Naming it here rather than working around it:
ROW.Q.3's first sub-lemma is the arm-value equation at a CONCRETE memory, and ROW.Q.4's frame
valuation is what makes a symbolic memory reduce. -/
theorem evalQuotientIdentityLoop_atEnd (bytes : List Nat) (consts : List Midfall.Word256)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Midfall.Generator.evalQuotientIdentityLoop.go bytes consts 0 bytes.length stack mem =
      .ok (stack, mem) := by
  simp [Midfall.Generator.evalQuotientIdentityLoop.go]

/-! ### 6. TWO SMALL FACTS THE WITNESS NEEDS -/

/-- The one 'Option.isSome' elimination the split-loop witness needs: a pre that says a name IS bound. -/
theorem isSome_elim {α : Type} {o : Option α} (h : Option.isSome o = true) : ∃ x, o = some x := by
  cases o with
  | none => simp [Option.isSome] at h
  | some x => exact ⟨x, rfl⟩

/-- **SETTING A BOUND VARIABLE TO ITS OWN VALUE IS THE IDENTITY.** The 'VEnv' fact the split-loop
witness needs and the vendored layer does not state (the tree has only the read-back form,
'VkLoading.lean:612 vk_get_set_of_some'). PROVED by induction on the environment, on the standard
three axioms. -/
theorem venv_set_eq_self {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {v : D.Value} (h : VEnv.get V x = some v) : VEnv.set V x v = V := by
  classical
  induction V with
  | nil => cases h
  | cons p rest ih =>
      cases p with
      | mk y u =>
      by_cases hy : y = x
      · subst hy
        have huv : u = v := Option.some.inj (by simpa [VEnv.get, List.find?] using h)
        subst huv
        simp [VEnv.set]
      · have hget : VEnv.get rest x = some v := by
          have h2 : VEnv.get ((y, u) :: rest) x = some v := h
          simpa [VEnv.get, List.find?, hy] using h2
        have hset := ih hget
        show VEnv.set ((y, u) :: rest) x v = (y, u) :: rest
        simp [VEnv.set, hy, hset]

/-! ### 7. WITNESSES (W12) -/

/-- **WITNESS FOR 'q_blockSim' - THE ROW'S POST IS SATISFIABLE WITH THE REAL PREDICATES.** The
row's conclusion is two 'StmtsContractAll' conjuncts over 'R.slice Partial.quotientLin' at the real
'StageInv' boundary, the real 'exitSimAt' and the real 'Poisoned'. A contract nothing can satisfy is
worth nothing, so this exhibits the SAME pair of conjuncts satisfied - by the always-reverting block,
whose only runs end in a revert, which is the first disjunct of the simulation post and the only one
the poisoned arm admits. PROVED by the tree's symbolic executor ('allRuns_of_wp' + 'wp_run'), not by
an '#eval', and generic in the render, hash, address, calldata, calls and gas.
NAMES ITS CLAUSE: the '(o = .halt ∧ Midfall.Lowering.Reverted st')' disjunct. -/
theorem q_blockSim_witness_reverting_block_satisfies_the_post
    (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g)
        [yexpr (yop Op.revert [ylit 0, ylit 0])]
        (fun V st => StageInv R H vkAddr cd Partial.quotientLin.pre V st)
        (fun _ _ V' st' o => (o = .halt ∧ Midfall.Lowering.Reverted st') ∨
          exitSimAt R H vkAddr cd (fun k V st => StageInv R H vkAddr cd k V st)
            Partial.quotientLin V' st' o ∨
          (Partial.quotientLin ≠ Partial.traceReturn ∧ o = .normal ∧
            Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g)
        [yexpr (yop Op.revert [ylit 0, ylit 0])]
        (fun V st => Poisoned R H vkAddr cd V st)
        (fun _ _ V' st' o => (o = .halt ∧ Midfall.Lowering.Reverted st') ∨
          (Partial.quotientLin ≠ Partial.traceReturn ∧ o = .normal ∧
            Poisoned R H vkAddr cd V' st')) := by
  have key : ∀ (V : VEnv (Bridge.Dialect c g)) (st : EvmState),
      Midfall.Yul.WpTac.AllRuns (R.scope c g) V st [yexpr (yop Op.revert [ylit 0, ylit 0])]
        (fun _ st' o => o = .halt ∧ Midfall.Lowering.Reverted st') := by
    intro V st
    refine Midfall.Yul.WpTac.allRuns_of_wp 20 ?_
    wp_run
    all_goals (first | exact ⟨rfl, rfl⟩ | rfl)
  refine ⟨fun V st _ V' st' o hrun => Or.inl (key V st V' st' o hrun),
    fun V st _ V' st' o hrun => Or.inl (key V st V' st' o hrun)⟩

/-- **WITNESS FOR 'q_blockProgS' - THE PROGRESS POST IS REACHED, NOT JUST CONSISTENT.**
'BlockProgS' is 'StmtsTotal': a run EXISTS and every run is good. The existence half is the half a
skeleton cannot fake, so this exhibits a block that has a run whose outcome is exactly what the
progress post of a non-terminal partial demands - '.normal' at the next boundary. PROVED from
'Step.seqNil' in both directions. NAMES ITS CLAUSE: 'exitProgAt''s 'o = .normal'. -/
theorem q_blockProgS_witness_empty_block_reaches_the_post
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (funs := []) [] (fun _ _ => True)
        (fun _ _ V' st' o => exitProgAt R H vkAddr cd
          (fun _ _ _ => True) Partial.quotientLin V' st' o) := by
  refine ⟨fun V st _ => ⟨V, st, .normal, Step.seqNil, ⟨rfl, trivial⟩⟩,
    fun V st _ V' st' o hrun => ?_⟩
  cases hrun with
  | seqNil => exact ⟨rfl, trivial⟩

/-- **WITNESS FOR 'qlin_split_loop' (ROW.Q.1) - THE POST IS FORCED BY THE PRE AT THE BASE CASE.**
At 'k = 0' the split loop does not run: its condition is 'idx < k' with 'idx' initialised to 0, and
'forLoop_false' (section 5) is the general fact that such a loop exits normally and unchanged. What
the leaf's post then demands is exactly what its pre already says, because 'wSplit rw x 0 = (1, x)'.
PROVED, and it is the base case of the induction the leaf will carry, so the registered hole is the
inductive step and not a misunderstanding of the vocabulary. NAMES ITS CLAUSES: the post's 'wSplit'
pair and the pre's 'x_pow_2i = x'. -/
theorem qlin_split_loop_witness_base_case
    {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs []
      (fun V _ => VEnv.get V "k" = some 0 ∧ VEnv.get V "x_pow_2i_minus1" = some 1 ∧
        (VEnv.get V "x").isSome ∧ VEnv.get V "x_pow_2i" = VEnv.get V "x" ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        ∃ x rw, VEnv.get V "x" = some x ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "x_pow_2i_minus1" (wSplit rw x 0).1)
            "x_pow_2i" (wSplit rw x 0).2) := by
  intro V st hpre V' st' o hrun
  obtain ⟨x, hx⟩ := isSome_elim hpre.2.2.1
  obtain ⟨rw, hrw⟩ := isSome_elim hpre.2.2.2.2
  have key : Midfall.Yul.WpTac.AllRuns funs V st []
      (fun V' st' o => V' = V ∧ st' = st ∧ o = .normal) := by
    refine Midfall.Yul.WpTac.allRuns_of_wp 1 ?_
    wp_run
    all_goals (first | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl⟩ | rfl)
  obtain ⟨hV', hst', ho⟩ := key V' st' o hrun
  refine ⟨ho, hst', x, rw, hx, hrw, ?_⟩
  rw [hV']
  have h1 : VEnv.get V "x_pow_2i_minus1" = some (wSplit rw x 0).1 := hpre.2.1
  have h2 : VEnv.get V "x_pow_2i" = some (wSplit rw x 0).2 := by
    rw [show (wSplit rw x 0).2 = x from rfl]
    exact hpre.2.2.2.1.trans hx
  have e1 : VEnv.set V "x_pow_2i_minus1" (wSplit rw x 0).1 = V := venv_set_eq_self h1
  have e2 : VEnv.set (VEnv.set V "x_pow_2i_minus1" (wSplit rw x 0).1) "x_pow_2i"
      (wSplit rw x 0).2 = VEnv.set V "x_pow_2i" (wSplit rw x 0).2 := by rw [e1]
  rw [e2, venv_set_eq_self h2]


/-- **FALSIFIER FOR 'qlin_split_loop' - THE PRE'S 'x_pow_2i = x' CLAUSE IS LOAD-BEARING.** Delete
that one clause from the pre and the same no-op run refutes the post: at 'k = 0' the loop leaves the
environment alone, while the post installs '(wSplit rw x 0).2 = x' into 'x_pow_2i'. Exhibited at a
concrete environment in which 'x = 3' and 'x_pow_2i = 9'. PROVED, and it is the clause a
"simplified" pre would lose. -/
theorem qlin_split_loop_falsifier_pre_pins_x_pow_2i :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) (funs := []) []
      (fun (V : VEnv (Bridge.Dialect c g)) _ =>
        VEnv.get V "k" = some (0 : U256) ∧ VEnv.get V "x_pow_2i_minus1" = some (1 : U256) ∧
          VEnv.get V "x" = some (3 : U256) ∧ VEnv.get V "r" = some (7 : U256))
      (fun (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (V' : VEnv (Bridge.Dialect c g))
          (st' : EvmState) (o : Outcome) => o = .normal ∧
        ∃ x rw, VEnv.get V "x" = some x ∧ VEnv.get V "r" = some rw ∧
          VEnv.get V' "x_pow_2i" = some (wSplit rw x 0).2) := by
  intro H
  set W : VEnv (Bridge.Dialect c g) :=
    [("k", (0 : U256)), ("x_pow_2i_minus1", (1 : U256)), ("x", (3 : U256)),
     ("x_pow_2i", (9 : U256)), ("r", (7 : U256))] with hW
  have hpre : VEnv.get W "k" = some (0 : U256) ∧
      VEnv.get W "x_pow_2i_minus1" = some (1 : U256) ∧
      VEnv.get W "x" = some (3 : U256) ∧
      VEnv.get W "r" = some (7 : U256) := by
    rw [hW]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hpost := H W EvmState.init hpre W EvmState.init .normal Step.seqNil
  obtain ⟨x, rw, hx, hrw, hget⟩ := hpost.2
  have hx3 : x = (3 : U256) := Option.some.inj hx.symm
  have hr7 : rw = (7 : U256) := Option.some.inj hrw.symm
  rw [hx3, hr7] at hget
  rw [hW] at hget
  simp only [VEnv.get, List.find?] at hget
  exact absurd hget (by decide : ¬ ((some (9 : U256)) = some (3 : U256)))

/-! ### 8. FALSIFIERS (W12) -/

/-- **FALSIFIER FOR 'q_blockSim' - THE REVERT DISJUNCT IS THE ONLY HALT THE ROW ALLOWS.** Put a
block that RETURNS instead of reverting in the row's slice position and the contract is false: a
'ret' is a halt, it is not a revert, it is not 'exitSimAt' at a non-terminal partial (which demands
'.normal'), and it is not the poisoned arm (which also demands '.normal'). So the row is not
satisfied by a program that stops early with a success payload - the v1 defect class, at the row
rather than at the chain. PROVED with the run built from the vendored 'Step' rules. -/
theorem q_blockSim_falsifier_return_is_not_a_halt_arm
    (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g)
        [yexpr (yop Op.ret [ylit 0, ylit 0])] (fun _ _ => True)
        (fun _ _ V' st' o => (o = .halt ∧ Midfall.Lowering.Reverted st') ∨
          exitSimAt R H vkAddr cd (fun k V st => StageInv R H vkAddr cd k V st)
            Partial.quotientLin V' st' o ∨
          (Partial.quotientLin ≠ Partial.traceReturn ∧ o = .normal ∧
            Poisoned R H vkAddr cd V' st')) := by
  intro Hc
  have hargs : Step (Bridge.Dialect c g) (R.scope c g) ([] : VEnv (Bridge.Dialect c g)) EvmState.init
      (.args [ylit 0, ylit 0]) (.eres (.vals [0, 0] EvmState.init)) := by
    exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  have hbi : (Bridge.Dialect c g).Builtin Op.ret [0, 0] EvmState.init
      (.halt { EvmState.init with halted := some (.ret, []) }) := by
    show stepOp Op.ret [0, 0] EvmState.init = some _
    rfl
  have hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] EvmState.init
      [yexpr (yop Op.ret [ylit 0, ylit 0])] [] retState .halt :=
    Step.seqStop (D := Bridge.Dialect c g) (rest := [])
      (Step.exprStmtHalt (D := Bridge.Dialect c g) (e := yop Op.ret [ylit 0, ylit 0])
        (st1 := retState)
        (Step.builtinHalt (D := Bridge.Dialect c g) (args := [ylit 0, ylit 0]) (argvals := [0, 0])
          (st1 := EvmState.init) (st2 := retState) hargs hbi))
      (by decide)
  have hpost := Hc [] EvmState.init trivial [] retState .halt hrun
  rcases hpost with hrev | hsim | hpo
  · exact retState_not_Reverted hrev.2
  · exact absurd hsim.1 (by decide : ¬ ((Outcome.halt : Outcome) = Outcome.normal))
  · exact absurd hpo.2.1 (by decide : ¬ ((Outcome.halt : Outcome) = Outcome.normal))

/-- **FALSIFIER FOR 'q_blockProgS' - TOTALITY IS NOT THE REVERT ARM.** A block that only reverts has
no normal run, so it fails the progress contract while satisfying the simulation one. That is
exactly why the headline needs BOTH rows and why conjunct 2 cannot be read off conjunct 1: the row
this file registers on the progress side is refused by a program the soundness row accepts. PROVED. -/
theorem q_blockProgS_falsifier_reverting_block_is_not_total
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    ¬ StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (funs := []) [yexpr (yop Op.revert [ylit 0, ylit 0])] (fun _ _ => True)
        (fun _ _ V' st' o => exitProgAt R H vkAddr cd
          (fun _ _ _ => True) Partial.quotientLin V' st' o) := by
  intro Ht
  obtain ⟨hex, _⟩ := Ht
  obtain ⟨V', st', o, hrun, hpost⟩ := hex [] EvmState.init trivial
  have key : Midfall.Yul.WpTac.AllRuns [] ([] : VEnv (Bridge.Dialect (callsOf product)
      (ExternalGas.ofFun fun _ => 0))) EvmState.init [yexpr (yop Op.revert [ylit 0, ylit 0])]
      (fun _ st' o => o = .halt) := by
    refine Midfall.Yul.WpTac.allRuns_of_wp 20 ?_
    wp_run
    all_goals (first | exact ⟨rfl, rfl⟩ | rfl)
  have ho := key V' st' o hrun
  rw [ho] at hpost
  exact absurd hpost.1 (by decide : ¬ ((Outcome.halt : Outcome) = Outcome.normal))

/-! ### 9. THE ACCEPTANCE PRINTS -/

/-! **THE ROWS QUANTIFY OVER THE RENDER AND NAME NO FIXTURE.** 'R : Render p G₁ G₂ Gₜ' is a binder of
both rows; the only partial named is 'Partial.quotientLin', which is a clause of the program and not
a fixture value; the exponent, the constant table, the window and the program are all binders of the
leaf. 'poseidonRender' does not appear in this file. -/
#check @Midfall.LoweringV3.QuotientRows.q_blockSim
#check @Midfall.LoweringV3.QuotientRows.q_blockProgS
#check @Midfall.LoweringV3.QuotientRows.qlin_split_loop
#check @Midfall.LoweringV3.QuotientRows.QInterpRefinesLe
#check @Midfall.LoweringV3.QuotientRows.qvmLoop_empty_segment
#check @Midfall.LoweringV3.QuotientRows.evalQuotientIdentity_nil
#check @Midfall.LoweringV3.QuotientRows.identityCorrespondence_of_bridge_fixed

-- THE THREE REGISTERED HOLES, one per named leaf.
#cone_sorries Midfall.LoweringV3.QuotientRows.q_blockSim
#cone_sorries Midfall.LoweringV3.QuotientRows.q_blockProgS
#cone_sorries Midfall.LoweringV3.QuotientRows.qlin_split_loop
-- ROW.Q.3, T3.10's registered leaf, cited here because this card's rows name it.
#cone_sorries Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop

#assert_axioms Midfall.LoweringV3.QuotientRows.identityCorrespondence_of_bridge_fixed [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qvmLoop_empty_segment [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.evalQuotientIdentity_nil [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.evalQuotientIdentityLoop_step [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.evalQuotientIdentityLoop_atEnd [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_falsifier_empty_segment [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qlin_slice_widened [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qlinInner_length [propext] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qlinInner_binds_k [propext] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_blockSim_witness_reverting_block_satisfies_the_post [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_blockProgS_witness_empty_block_reaches_the_post [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qlin_split_loop_witness_base_case [propext, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_blockSim_falsifier_return_is_not_a_halt_arm [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_blockProgS_falsifier_reverting_block_is_not_total [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qlin_split_loop_falsifier_pre_pins_x_pow_2i [propext, Quot.sound] native []


/-! ### 10. ROW.Q.5 - THE GENERATED-FAMILY VALUE LEAVES, CONSUMED HERE -/

/-- **THE INLINE FAMILY SLICES BY IDENTITY INDEX.** 'seg' is this file's own slicing vocabulary
(section 1), and the inline family's region of the quotientLin slice is a flat statement run, so what a
proof about it needs is the ADDRESS of identity 'i' inside that run.
'Midfall.Lowering.GenAst.qEmitInlineFamily_take_drop' supplies the split and 'qEmitInlineFamily_length'
the offset; this is the two read together: the first 'i' identities occupy exactly the first
'i * stride' statements, and what follows them is the family of the remaining identities. PROVED, no
fixture, for every identity list, fold plan, scratch slot, state-slot triple and trace flag. -/
theorem q_rowQ5_inline_seg (ids : List QuotientIdentity) (i : Nat) (hi : i ≤ ids.length)
    (fold : SelectorFoldPlan) (evalScratchSlot : Nat)
    (slots : Midfall.Generator.QuotientFold.QuotientStateSlots) (trace : Bool) :
    seg (qEmitInlineFamily ids fold evalScratchSlot slots trace) 0
        (i * qFamilyStride trace) =
      qEmitInlineFamily (ids.take i) fold evalScratchSlot slots trace := by
  have hlen : (qEmitInlineFamily (ids.take i) fold evalScratchSlot slots trace).length =
      i * qFamilyStride trace := by
    rw [qEmitInlineFamily_length, List.length_take_of_le hi]
  show ((qEmitInlineFamily ids fold evalScratchSlot slots trace).drop 0).take
        (i * qFamilyStride trace) = _
  rw [List.drop_zero, qEmitInlineFamily_take_drop]
  rw [List.take_append_of_le_length (Nat.le_of_eq hlen.symm), ← hlen, List.take_length]

/-- **THE NATIVE-IDENTITY SWITCH HAS AT LEAST ONE CASE WHENEVER THE PLAN CARRIES AN IDENTITY.** The
render spells the family as '(case index0 => ...)' per identity; a plan whose native list were empty
would render a switch with no cases at all, which is a different statement - the fail-closed default
would then be the only arm. PROVED from 'qEmitNativeIdentityCases_length'. -/
theorem q_rowQ5_native_identity_switch_nonempty (ids : List QuotientIdentity)
    (h : ids ≠ []) (fold : SelectorFoldPlan) (evalScratchSlot : Nat)
    (slots : Midfall.Generator.QuotientFold.QuotientStateSlots) (trace : Bool) :
    qEmitNativeIdentityCases ids fold evalScratchSlot slots trace ≠ [] := by
  intro hnil
  have hl : (qEmitNativeIdentityCases ids fold evalScratchSlot slots trace).length = 0 := by
    rw [hnil]; rfl
  rw [qEmitNativeIdentityCases_length] at hl
  exact h (List.eq_nil_of_length_eq_zero hl)

/-- **THE POST-VM REGION IS ONE BRACED BLOCK.** What the rows need from the post-VM family is where the
region begins and ends in the emitted run: one 'Stmt.block', whatever the trashcan list and whatever
the abort-free per-trashcan walk inside it. PROVED from 'qEmitPostVmFamily_shape'. -/
theorem q_rowQ5_postvm_one_block (slots : Midfall.Generator.QuotientFold.QuotientStateSlots)
    (trace : Bool) {F : Type} [BEq F]
    (ev ev' : Midfall.Generator.QuotientEvaluator.Evaluator F) (b : Block EVM.Op)
    (h : (qEmitTrashBlock slots trace).run ev = .ok (some b, ev')) :
    b.length = 1 := by
  obtain ⟨blocks, hb, _⟩ := qEmitPostVmFamily_shape slots trace ev b ev' h
  rw [hb]
  rfl

/-- **THE TWO STATEMENT-RUN FAMILIES AGREE STATEMENT FOR STATEMENT**, in this file's slicing
vocabulary: the 'k'-th statement of the inline family is the 'k'-th statement of the native-identity
family, for every 'k' and every plan. This is what lets ROW.Q's step-2 restatement of
'qvm_compile_correct_stream' fold the two families as ONE walk instead of two. PROVED from the two
value lemmas via 'qEmitNativeIdentityFamily_eq_qEmitInlineFamily'. -/
theorem q_rowQ5_families_agree (ids : List QuotientIdentity) (k : Nat) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : Midfall.Generator.QuotientFold.QuotientStateSlots)
    (trace : Bool) :
    seg (qEmitNativeIdentityFamily ids fold evalScratchSlot slots trace) k 1 =
      seg (qEmitInlineFamily ids fold evalScratchSlot slots trace) k 1 := by
  show ((qEmitNativeIdentityFamily ids fold evalScratchSlot slots trace).drop k).take 1 = _
  rw [qEmitNativeIdentityFamily_eq_qEmitInlineFamily]
  rfl


-- ROW.Q.5: the five family value leaves, proved in 'Midfall/Lowering/GenAstQvmFamilies.lean' and
-- consumed by the four theorems of section 10. Every cone below is EMPTY: no registered hole is a
-- premise of any of them, which is what makes them leaves rather than skeletons.
#cone_sorries Midfall.LoweringV3.QuotientRows.q_rowQ5_inline_seg
#cone_sorries Midfall.LoweringV3.QuotientRows.q_rowQ5_native_identity_switch_nonempty
#cone_sorries Midfall.LoweringV3.QuotientRows.q_rowQ5_postvm_one_block
#cone_sorries Midfall.LoweringV3.QuotientRows.q_rowQ5_families_agree
#assert_axioms Midfall.LoweringV3.QuotientRows.q_rowQ5_inline_seg [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_rowQ5_native_identity_switch_nonempty [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_rowQ5_postvm_one_block [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.q_rowQ5_families_agree [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitDirectBlock_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitInlineFamily_value [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitInlineFamily_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitInlineFamily_append [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitInlineFamily_take_drop [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitInlineFamily_eq_nil_iff [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeIdentityFamily_value [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeIdentityFamily_eq_qEmitInlineFamily [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeIdentityCases_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeIdentityCases_nth [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeIdentitySwitch_shape [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeIdentityFamily_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qMapM_length_stateT [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitPostVmFamily_none [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitPostVmFamily_shape [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativePermutationA_none [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeLookupA_none [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qPushMstoreMloadLiteralRunsA_nil [propext] native []

-- QEMIT3: the family-4 and family-5 per-item leaves, proved in 'GenAstQvmFamilies.lean' once the lift
-- made the inner steps top-level defs. Empty cones again: these are leaves, not skeletons.
#cone_sorries Midfall.Lowering.GenAst.qEmitNativeLookupA_shape
#cone_sorries Midfall.Lowering.GenAst.qPushMstoreMloadLiteralRunsA_rejected
#cone_sorries Midfall.Lowering.GenAst.qPushMstoreMloadLiteralRunsA_run3
#assert_axioms Midfall.Lowering.GenAst.qMloadRunGoA_zero [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qMloadRunGoA_out_of_range [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qPushMstoreMloadLiteralRunsA_rejected [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qPushMstoreMloadLiteralRunsA_run3 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitPermutationStagingA_empty [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qMapM_all_stateT [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qFlatten_length_of_singleton [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qStateT_run_bind_ok [propext, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitLookupRegionA_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitLookupPerItemStepA_shape [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitLookupRegionA_items [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.GenAst.qEmitNativeLookupA_shape [propext, Classical.choice, Quot.sound] native []

/-! ### 11. THE ROW 'qinterpRefines_qvmLoop' IS FALSE AS STATED (BOXD)

QLOOP recorded at 'QuotientLoopCompose.lean:47-62' that the row LOOKS false for a symbolic template
table and did NOT exhibit it, because the sketched route needs a concrete NORMAL RUN of the emitted
loop - one iteration of the switch over the emitter's own 31-entry case list, which is ROW.Q's
induction. This section lands a PROVED refutation of the row. It is NOT QLOOP's sketch: it is cheaper,
and it bites harder, because it needs no table disagreement at all and no arm body.

THE DEFECT, IN ONE SENTENCE. 'AtSegment' writes the loop's two cursor registers as
'BitVec.ofNat 256 (s.base + s.cursor)' and 'BitVec.ofNat 256 (s.base + s.exprEnd)', and NOTHING in the
contract requires 's.base + s.exprEnd < 2^256'. At 's.base = 2^256 - 1' the two words WRAP, to
'allOnes' and to '0', so the loop guard 'q_pc < q_end' is FALSE: the body never runs, the loop exits
NORMALLY at the segment's own start, and the state is the state it was handed. Meanwhile the segment is
non-empty and inside the window, and the reference VM has no opcode 200, so 'evalQuotientIdentity'
errors. NEITHER disjunct of the post holds: the exit is not a halt, so it is not a revert, and the
reference returns no '.ok', so the second disjunct's witness does not exist. The row is therefore FALSE
as stated - for EVERY context, EVERY program and EVERY template table, the default one included.

SAME ROOT FAMILY AS QLOOP'S SKETCH, AND THAT IS THE POINT. Both come from the post being satisfied by
ANY revert: the contract is sound only if the emitted loop runs an arm for every segment the reference
rejects. QLOOP's route makes the loop run the WRONG ARM (a table agreeing with some opcode labels and
not others); this route makes the loop run NO ARM at all (a window base that overflows the 256-bit word
the registers hold). Either one refutes the row. In particular the sentence the tree relies on -
'QuotientInterp.lean:99-102', "every non-empty garbage segment is fine, because every emitted switch is
fail-closed on an unknown opcode" - is FALSE as written: fail-closure needs the switch to be REACHED,
and the loop guard decides before the switch is.

WHAT A HUMAN MUST DECIDE, AND WHAT THIS FILE DOES NOT DO. The repair is a hypothesis on the window
('s.base + s.exprEnd < 2^256', or 'AtSegment' carrying the un-wrapped pair), or a hypothesis on the
table ('tcq.op = the reference's opcode constants', QLOOP's repair hypothesis, of which
'PG_limbCountAgrees' is the limb-count member). RULES forbid adding a hypothesis to a row, to
'ValidV3', to a bundle or to the root, so NOTHING HERE CHANGES THE ROW: 'qinterpRefines_qvmLoop' is
untouched, still at 'QuotientInterp.lean:253', still one sorry. W13 says a sorry whose negation is
proved must be DELETED and the row restated; that is a human ruling, and moving it also moves the sorry
register, the statement-fingerprint pin and the 'kat_gate.py' note that names this row as the card's one
named hole - none of which a worker may move. LOUDLY: **ROW.Q.3 IS REFUTED, NOT OPEN.**

NO AXIOM BEYOND THE THREE, NO 'native_decide', NO RAISED HEARTBEAT OR RECURSION LIMIT. The emitted run
is built from the vendored 'Step' rules through 'forLoop_false' (section 4), which never looks at the
body - so nothing here unrolls the interpreter's arms. The reference side is the same
'simp [evalQuotientIdentityLoop.go]' reduction 'evalQuotientIdentity_nil' (section 5) already used. -/

/-- **THE WRAPPING WINDOW BASE**: '2^256 - 1', the largest word the interpreter's 256-bit 'q_pc' can
    hold. 'q_pc' is 'BitVec.ofNat 256 (base + cursor)' and 'q_end' is 'BitVec.ofNat 256 (base +
    exprEnd)', so at this base the two wrap to 'allOnes' and '0' for ANY legal non-empty segment. -/
def qWrapBase : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

/-- A one-byte program window whose only byte is 200. No reference opcode is 200 - the 'qOpX' family
    runs 0x01-0x22 - so 'evalQuotientIdentity' refuses it as 'unknownOpcode'. -/
def qBadBytes : List Nat := [200]

/-- The legal non-empty segment at the wrapping base: 'cursor < exprEnd <= len' holds as NATURAL
    numbers, which is all 'QSegment.inWindow' asks. -/
def qBadSegment : QSegment :=
  { base := qWrapBase, len := 1, cursor := 0, exprEnd := 1 }

/-- Yul memory that agrees with 'qBadBytes' at that window. Addresses are 'Nat' and unbounded, so the
    address space and the interpreter's 256-bit registers disagree - which is exactly the gap the
    contract leaves open. -/
def qBadState : EvmState := { EvmState.init with memory := fun a => if a = qWrapBase then 200 else 0 }

/-- The reference memory: an empty frame, which makes 'AgreesFrame' vacuous. -/
def qBadMemory : QuotientRefMemory := quotientRefMemoryNew Midfall.Bytes.empty

/-- The environment 'AtSegment' pins at the wrapping window: the five registers the prologue writes,
    with the two cursor registers already wrapped. -/
def qBadV {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram) :
    VEnv (Bridge.Dialect c g) :=
  segmentV (c := c) (g := g) (program := program) qBadSegment 0 false

theorem qBadSegment_inWindow : QSegment.inWindow qBadSegment := ⟨Nat.zero_lt_one, Nat.le_refl 1⟩

/-- The three agreement clauses hold at the wrapping window: the program window by construction, the
    constant and frame windows vacuously ('consts = []', 'frameWords = 0'). -/
theorem qBad_Agrees (program : QuotientProgram) :
    Agrees [] program.constMptr 0 0 qBadBytes qBadState qBadMemory qBadSegment := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by simpa [qBadSegment] using hi
    subst this
    rfl
  · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · intro a ha; exact absurd ha (Nat.not_lt_zero a)

/-- **THE GUARD IS FALSE AT THE WRAPPING WINDOW.** 'q_pc' holds 'allOnes' and 'q_end' holds '0', so
    'lt' yields zero - the single fact the refutation turns on. Built from the vendored 'Step' rules
    exactly as 'eval_lt_same' (section 4) is; this is the 'hcond' 'forLoop_false' consumes. -/
theorem qvmLoop_guard_wraps {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (funs : FunEnv (Bridge.Dialect c g)) :
    EvalExpr (Bridge.Dialect c g) ([] :: funs) (qBadV (c := c) (g := g) (program := program))
      qBadState (yop Op.lt [yvar "q_pc", yvar "q_end"]) (.vals [0] qBadState) := by
  refine Step.builtinOk (D := Bridge.Dialect c g) (op := Op.lt)
      (args := [yvar "q_pc", yvar "q_end"]) (argvals := [BitVec.ofNat 256 qWrapBase, 0])
      (st1 := qBadState) (rets := [0]) (st2 := qBadState) ?_ ?_
  · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [yvar "q_end"]) (e := yvar "q_pc")
      (restvals := [0]) (v := BitVec.ofNat 256 qWrapBase) (st2 := qBadState)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (e := yvar "q_end") (restvals := [])
        (v := (0 : U256)) (st1 := qBadState) (st2 := qBadState)
        (Step.argsNil (D := Bridge.Dialect c g)) (Step.var (D := Bridge.Dialect c g) rfl))
      (Step.var (D := Bridge.Dialect c g) rfl)
  · show stepOp Op.lt [BitVec.ofNat 256 qWrapBase, 0] qBadState = some (.ok [0] qBadState)
    rfl

/-- **THE EMITTED LOOP EXITS NORMALLY WITHOUT RUNNING A SINGLE ITERATION** at the wrapping window, for
    EVERY context, program and table. 'forLoop_false' is body-independent, so this says nothing about
    the thirty-one arms and costs no unrolling: the guard is false, so the loop's only run is the one
    that returns the state it was handed, with outcome 'normal'. -/
theorem qvmLoop_no_iteration {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) :
    ExecStmts (Bridge.Dialect c g) funs (qBadV (c := c) (g := g) (program := program)) qBadState
      [GenAst.qvmLoop ctx program tcq]
      (qBadV (c := c) (g := g) (program := program)) qBadState .normal := by
  obtain ⟨body, hbody⟩ : ∃ body, GenAst.qvmLoop ctx program tcq =
      Stmt.forLoop [] (yop Op.lt [yvar "q_pc", yvar "q_end"]) [] body := ⟨_, rfl⟩
  rw [hbody]
  exact forLoop_false "q_pc" "q_end" funs body _ qBadState (qvmLoop_guard_wraps program funs)

/-- **THE REFERENCE VM REFUSES THE SEGMENT.** 'evalQuotientIdentity [200] [] mem' ends in
    'QVMFault.unknownOpcode 200 0'. PROVABLE, not just computable: the 'where'-clause 'go' does not
    unfold under 'rfl' but does under 'simp [evalQuotientIdentityLoop.go]', exactly as
    'evalQuotientIdentity_nil' (section 5) established for the empty program. -/
theorem evalQuotientIdentity_badBytes :
    Midfall.Generator.evalQuotientIdentity qBadBytes [] qBadMemory =
      .error (QVMFault.unknownOpcode 200 0) := by
  have hloop : Midfall.Generator.evalQuotientIdentityLoop qBadBytes [] 0 [] qBadMemory
      = .error (QVMFault.unknownOpcode 200 0) := by
    show Midfall.Generator.evalQuotientIdentityLoop.go qBadBytes [] 1 0 [] qBadMemory = _
    simp only [Midfall.Generator.evalQuotientIdentityLoop.go]
    rfl
  unfold Midfall.Generator.evalQuotientIdentity
  rw [hloop]
  rfl

/-- **THE ROW 'qinterpRefines_qvmLoop' IS FALSE AS STATED.** At the row's OWN instantiation of the
    contract - the real 'Midfall.Lowering.Reverted', the real 'AtSegment program', the real
    'qinterpTop', the real windowed 'Agrees' - the emitted loop has a run whose post fails. Generic in
    the context, the program and the table (D-P71: no fixture in the statement), so it refutes the row
    at EVERY table, the default one included: the defect is the window, not the table. The window is
    'qBadSegment', the program bytes are 'qBadBytes', and the constant table, frame base and frame
    length are the vacuous '[]', '0', '0' the row quantifies over. -/
theorem qinterpRefines_qvmLoop_row_is_false {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) :
    ¬ QInterpRefines (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun st mem s => Agrees [] program.constMptr 0 0 qBadBytes st mem s)
      funs [GenAst.qvmLoop ctx program tcq] qBadBytes [] := by
  intro H
  have hrun : ExecStmts (Bridge.Dialect c g) funs (qBadV (c := c) (g := g) (program := program))
      qBadState [GenAst.qvmLoop ctx program tcq]
      (qBadV (c := c) (g := g) (program := program)) qBadState .normal :=
    qvmLoop_no_iteration ctx program tcq funs
  have h := H qBadSegment qBadMemory qBadSegment_inWindow
    (qBadV (c := c) (g := g) (program := program)) qBadState
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, qBad_Agrees program⟩
    (qBadV (c := c) (g := g) (program := program)) qBadState .normal hrun
  cases h with
  | inl h => exact absurd h.1 (by decide : ¬ ((Outcome.normal : Outcome) = Outcome.halt))
  | inr h =>
      obtain ⟨v, mem', hv, _, _⟩ := h.2
      have hseg : ((qBadBytes.drop qBadSegment.cursor).take
          (qBadSegment.exprEnd - qBadSegment.cursor)) = qBadBytes := rfl
      rw [hseg, evalQuotientIdentity_badBytes] at hv
      cases hv

/-- The same refutation in the shape a reader checks against the row: the row's universal closure,
    verbatim, is FALSE. The witnesses 'quotientCtx' and 'quotientDeployedProgram' appear in the PROOF
    only - the statement is the row's own quantifier prefix, negated. -/
theorem qinterpRefines_qvmLoop_is_false_as_stated {c : ExternalCalls} {g : ExternalGas} :
    ¬ (∀ (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
        (funs : FunEnv (Bridge.Dialect c g)) (bytes : List Nat) (consts : List Midfall.Word256)
        (frameBase frameWords : Nat),
        QInterpRefines (D := Bridge.Dialect c g)
          (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
          (AtSegment := AtSegment program) (Top := qinterpTop)
          (Agrees := fun st mem s => Agrees consts program.constMptr frameBase frameWords bytes st mem s)
          funs [GenAst.qvmLoop ctx program tcq] bytes consts) := by
  intro Hall
  have H := Hall Midfall.Generator.quotientCtx Midfall.Generator.quotientDeployedProgram
    templateConstantsDefault.quotientVm [] qBadBytes [] 0 0
  exact qinterpRefines_qvmLoop_row_is_false (c := c) (g := g) Midfall.Generator.quotientCtx
    Midfall.Generator.quotientDeployedProgram templateConstantsDefault.quotientVm [] H

#print axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_row_is_false
#print axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_is_false_as_stated
#cone_sorries Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_row_is_false
#assert_axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_row_is_false [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_is_false_as_stated [propext, Classical.choice, Quot.sound] native []


/-! ### 12. AND QLOOP'S SKETCH IS CONSTRUCTIBLE: AN ARM RUNS, THE REFERENCE REFUSES IT (BOXD)

Section 11 refutes the row without running an arm. QLOOP's sketch (recorded at
'QuotientLoopCompose.lean:47-62' and NOT exhibited there) makes the loop RUN an arm whose reference
step fails, and said exhibiting it needs 'a concrete normal run of the emitted loop, which is ROW.Q's
loop induction'. THIS SECTION EXHIBITS SUCH A RUN, PROVED FROM THE 'Step' RULES - so the sketch is
constructible, and the obstacle QLOOP named is not a barrier, just work: about ninety lines of vendored
'Step' terms, no fuel, no 'wp_run', no 'native_decide', no raised heartbeat or recursion limit.

THE WITNESS. A program whose 'opUsage' is all OFF except 'neg' - so the emitter's case list is the
SINGLETON neg arm and no selection inequality is needed - the DEFAULT template table, and the one-byte
segment '[qOpNeg]' at an ordinary window base '0x1000'. The emitted loop takes one iteration: the pre
fetches 'q_op = byte(0, mload q_pc) = qOpNeg', advances 'q_pc' by one, the switch selects the neg arm,
and the arm rewrites the cached top ('q_top := addmod(0, r - q_top, r)') without touching 'q_pc' again -
so 'q_pc = q_end' and the loop exits NORMALLY. The reference's 'qOpNeg' step POPS THE STACK, which is
empty, and returns '.error (QVMFault.stackUnderflow 0)'. Neither disjunct of the post holds.

NOTE WHAT THIS DOES AND DOES NOT SHOW. It does NOT need a disagreeing table: the arm and the reference
agree on the OPCODE and still diverge, because the contract's pre pins 'q_pc', 'q_end' and the two
window bases but says NOTHING about the emitted cached top ('q_has_top = 0', 'q_top' arbitrary)
corresponding to the reference's stack. QLOOP's moved-label variant (set 'tcq.op.neg' to a byte the
reference does not know, e.g. 'op.neg := qOpAdd' and read the segment '[qOpAdd]') is the same shape
again - it was CHECKED by running the vendored interpreter at fuel 18 on both variants, and it needs
this same derivation with the label swapped. So the row is refuted on THREE independent axes: the
window bound (section 11), the unpinned operand stack (this section), and the disagreeing table
(QLOOP's sketch, same machinery). All three are the same human ruling: what hypothesis on the window,
the table and the start state makes the row true. NONE is added here.

The emitted run is built at 'Bridge.Dialect c g' for ARBITRARY oracles, so it refutes the row's own
'funs := []' instantiation without naming a fixture (D-P71). -/

def qNegUsage : QuotientVmOpcodeUsage :=
  { pushConst := false, pushMemLiteral := false, pushMemToken := false, pushMemTokenOffset := false,
    pushMemU16 := false, add := false, mul := false, neg := true, pushConstU8 := false,
    foldMain := false, foldSelector := false, addConstU8 := false, mulConstU8 := false,
    addConst := false, mulConst := false, addMemU16 := false, mulMemU16 := false,
    addMulMemMemConstU8 := false, addMulConstU8MemU16 := false, addMulMemMem := false,
    runAddMulMemMemConstU8 := false, runAddMulConstU8MemU16 := false, affineSum := false,
    nativePermutation := false, nativeLookup := false, nativeIdentity := false,
    lin7 := false, bilin7Row := false, bilin7Pairwise := false, modarith7 := false, pow5 := false }

def qNegProgram : QuotientProgram :=
  { len := 1, opUsage := qNegUsage, memUsage := memUsageAllOn,
    constMptr := 0x4000, evalNumerMptr := 0, traceIdMptr := 0,
    selectorPowerMptr := 0, selectorMaxPower := 0, selectorTailUpdates := [],
    stackMptr := 0x2000, programMptr := 0x1000,
    guards := { constMax := 7, numSelectorBuckets := 0, stackLast := 0x2000 } }
def qNegTable : QuotientVmTemplateConstants := templateConstantsDefault.quotientVm

def qNegCases : List (Literal × Block EVM.Op) :=
  GenAst.qvmOpcodeArms quotientCtx qNegProgram qNegTable ++ GenAst.qvmNativeArms quotientCtx qNegProgram qNegTable
    ++ GenAst.qvmFoldArms quotientCtx qNegProgram qNegTable
def qNegDflt : Option (Block EVM.Op) := some [yexpr (ycall "q_program_fail" [])]
def qNegArm : Block EVM.Op := qArmBodyNeg quotientCtx qNegProgram qNegTable
def qNegFetch : Expr EVM.Op := yop Op.byte [(ylit 0), (yop Op.mload [(yvar "q_pc")])]
def qNegInc : Expr EVM.Op := yop Op.add [(yvar "q_pc"), (ylit 1)]
def qNegNegE : Expr EVM.Op := yop Op.addmod [(ylit 0), (yop Op.sub [yvar "r", yvar "q_top"]), yvar "r"]
def qNegBody : Block EVM.Op := [ylet "q_op" qNegFetch, yset "q_pc" qNegInc, Stmt.switch (yvar "q_op") qNegCases qNegDflt]

def qNegState : EvmState := { EvmState.init with memory := fun a => if a = 0x1000 then 0x08 else 0 }
def qNegWord : U256 := loadWord qNegState.memory 0x1000
def qNegTouched : EvmState := touchMemory qNegState 0x1000 32
def qNegV0 : VEnv (Bridge.Dialect c g) :=
  [("q_pc", (0x1000 : U256)), ("q_end", (0x1001 : U256)), ("q_program_mptr", (0x1000 : U256)),
   ("q_const_mptr", (0x4000 : U256)), ("q_sp", (0x2000 : U256)), ("q_top", (0 : U256)),
   ("q_has_top", (0 : U256)), ("r", (7 : U256))]
def qNegV1 : VEnv (Bridge.Dialect c g) := (("q_op", (0x08 : U256)) :: qNegV0)
def qNegV2 : VEnv (Bridge.Dialect c g) := VEnv.setMany qNegV1 ["q_pc"] [(0x1001 : U256)]
def qNegV3 : VEnv (Bridge.Dialect c g) := VEnv.setMany qNegV2 ["q_top"] [(0 : U256)]
def qNegVb : VEnv (Bridge.Dialect c g) :=
  [("q_pc", (0x1001 : U256)), ("q_end", (0x1001 : U256)), ("q_program_mptr", (0x1000 : U256)),
   ("q_const_mptr", (0x4000 : U256)), ("q_sp", (0x2000 : U256)), ("q_top", (0 : U256)),
   ("q_has_top", (0 : U256)), ("r", (7 : U256))]

def qNegF0 : FunEnv (Bridge.Dialect c g) := []
def qNegFLoop : FunEnv (Bridge.Dialect c g) := hoist (Bridge.Dialect c g) [] :: qNegF0
def qNegFBody : FunEnv (Bridge.Dialect c g) := hoist (Bridge.Dialect c g) qNegBody :: qNegFLoop
def qNegFArm : FunEnv (Bridge.Dialect c g) := hoist (Bridge.Dialect c g) qNegArm :: qNegFBody
def qNegCond : Expr EVM.Op := yop Op.lt [yvar "q_pc", yvar "q_end"]


def qNegSegment : QSegment := { base := 0x1000, len := 1, cursor := 0, exprEnd := 1 }
theorem qNegSegment_inWindow : QSegment.inWindow qNegSegment := ⟨Nat.zero_lt_one, Nat.le_refl 1⟩

theorem qvmLoop_neg_arm_runs :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState), ExecStmts (Bridge.Dialect c g) [] qNegV0 qNegState
      [GenAst.qvmLoop quotientCtx qNegProgram qNegTable] V' st' .normal := by
  have hMload : Step (Bridge.Dialect c g) qNegFBody qNegV0 qNegState (.expr (yop Op.mload [yvar "q_pc"])) (.eres (.vals [qNegWord] qNegTouched)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.mload) (args := [yvar "q_pc"]) (argvals := [0x1000])
      (st1 := qNegState) (rets := [qNegWord]) (st2 := qNegTouched)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := yvar "q_pc") (restvals := []) (v := (0x1000 : U256))
        (st1 := qNegState) (st2 := qNegState) (Step.argsNil (D := (Bridge.Dialect c g))) (Step.var (D := (Bridge.Dialect c g)) rfl))
      (by show stepOp Op.mload [0x1000] qNegState = some (.ok [qNegWord] qNegTouched); rfl)
  have hByte : Step (Bridge.Dialect c g) qNegFBody qNegV0 qNegState (.expr qNegFetch) (.eres (.vals [0x08] qNegTouched)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.byte) (args := [ylit 0, yop Op.mload [yvar "q_pc"]])
      (argvals := [0, qNegWord]) (st1 := qNegTouched) (rets := [0x08]) (st2 := qNegTouched)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [yop Op.mload [yvar "q_pc"]]) (e := ylit 0) (restvals := [qNegWord])
        (v := (0 : U256)) (st1 := qNegTouched) (st2 := qNegTouched)
        (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := yop Op.mload [yvar "q_pc"]) (restvals := [])
          (v := qNegWord) (st1 := qNegState) (st2 := qNegTouched) (Step.argsNil (D := (Bridge.Dialect c g))) hMload)
        (Step.lit (D := (Bridge.Dialect c g)) (l := Literal.number 0)))
      (by show stepOp Op.byte [0, qNegWord] qNegTouched = some (.ok [0x08] qNegTouched); rfl)
  have hLet : Step (Bridge.Dialect c g) qNegFBody qNegV0 qNegState (.stmt (ylet "q_op" qNegFetch)) (.sres qNegV1 qNegTouched .normal) :=
    Step.letVal hByte rfl
  have hAddpc : Step (Bridge.Dialect c g) qNegFBody qNegV1 qNegTouched (.expr qNegInc) (.eres (.vals [0x1001] qNegTouched)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.add) (args := [yvar "q_pc", ylit 1]) (argvals := [0x1000, 1])
      (st1 := qNegTouched) (rets := [0x1001]) (st2 := qNegTouched)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [ylit 1]) (e := yvar "q_pc") (restvals := [1])
        (v := (0x1000 : U256)) (st1 := qNegTouched) (st2 := qNegTouched)
        (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := ylit 1) (restvals := []) (v := (1 : U256))
          (st1 := qNegTouched) (st2 := qNegTouched) (Step.argsNil (D := (Bridge.Dialect c g))) (Step.lit (D := (Bridge.Dialect c g)) (l := Literal.number 1)))
        (Step.var (D := (Bridge.Dialect c g)) rfl))
      (by show stepOp Op.add [0x1000, 1] qNegTouched = some (.ok [0x1001] qNegTouched); rfl)
  have hSetpc : Step (Bridge.Dialect c g) qNegFBody qNegV1 qNegTouched (.stmt (yset "q_pc" qNegInc)) (.sres qNegV2 qNegTouched .normal) :=
    Step.assignVal hAddpc rfl
  have hVarop : Step (Bridge.Dialect c g) qNegFBody qNegV2 qNegTouched (.expr (yvar "q_op")) (.eres (.vals [0x08] qNegTouched)) :=
    Step.var (D := (Bridge.Dialect c g)) rfl
  have hSub : Step (Bridge.Dialect c g) qNegFArm qNegV2 qNegTouched (.expr (yop Op.sub [yvar "r", yvar "q_top"])) (.eres (.vals [7] qNegTouched)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.sub) (args := [yvar "r", yvar "q_top"]) (argvals := [7, 0])
      (st1 := qNegTouched) (rets := [7]) (st2 := qNegTouched)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [yvar "q_top"]) (e := yvar "r") (restvals := [0])
        (v := (7 : U256)) (st1 := qNegTouched) (st2 := qNegTouched)
        (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := yvar "q_top") (restvals := []) (v := (0 : U256))
          (st1 := qNegTouched) (st2 := qNegTouched) (Step.argsNil (D := (Bridge.Dialect c g))) (Step.var (D := (Bridge.Dialect c g)) rfl))
        (Step.var (D := (Bridge.Dialect c g)) rfl))
      (by show stepOp Op.sub [7, 0] qNegTouched = some (.ok [7] qNegTouched); rfl)
  have hAddmod : Step (Bridge.Dialect c g) qNegFArm qNegV2 qNegTouched (.expr qNegNegE) (.eres (.vals [0] qNegTouched)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.addmod)
      (args := [ylit 0, yop Op.sub [yvar "r", yvar "q_top"], yvar "r"]) (argvals := [0, 7, 7])
      (st1 := qNegTouched) (rets := [0]) (st2 := qNegTouched)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [yop Op.sub [yvar "r", yvar "q_top"], yvar "r"]) (e := ylit 0)
        (restvals := [7, 7]) (v := (0 : U256)) (st1 := qNegTouched) (st2 := qNegTouched)
        (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [yvar "r"]) (e := yop Op.sub [yvar "r", yvar "q_top"])
          (restvals := [7]) (v := (7 : U256)) (st1 := qNegTouched) (st2 := qNegTouched)
          (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := yvar "r") (restvals := []) (v := (7 : U256))
            (st1 := qNegTouched) (st2 := qNegTouched) (Step.argsNil (D := (Bridge.Dialect c g))) (Step.var (D := (Bridge.Dialect c g)) rfl))
          hSub)
        (Step.lit (D := (Bridge.Dialect c g)) (l := Literal.number 0)))
      (by show stepOp Op.addmod [0, 7, 7] qNegTouched = some (.ok [0] qNegTouched); rfl)
  have hSettop : Step (Bridge.Dialect c g) qNegFArm qNegV2 qNegTouched (.stmt (yset "q_top" qNegNegE)) (.sres qNegV3 qNegTouched .normal) :=
    Step.assignVal hAddmod rfl
  have hArmSS : Step (Bridge.Dialect c g) qNegFArm qNegV2 qNegTouched (.stmts qNegArm) (.sres qNegV3 qNegTouched .normal) :=
    Step.seqCons hSettop Step.seqNil
  have hArmBlk : Step (Bridge.Dialect c g) qNegFBody qNegV2 qNegTouched (.stmt (.block qNegArm)) (.sres (restore qNegV2 qNegV3) qNegTouched .normal) :=
    Step.block hArmSS
  have hSwitch : Step (Bridge.Dialect c g) qNegFBody qNegV2 qNegTouched (.stmt (Stmt.switch (yvar "q_op") qNegCases qNegDflt))
      (.sres (restore qNegV2 qNegV3) qNegTouched .normal) := Step.switchExec hVarop hArmBlk
  have hBodySS : Step (Bridge.Dialect c g) qNegFBody qNegV0 qNegState (.stmts qNegBody) (.sres (restore qNegV2 qNegV3) qNegTouched .normal) :=
    Step.seqCons hLet (Step.seqCons hSetpc (Step.seqCons hSwitch Step.seqNil))
  have hBodyBlk : Step (Bridge.Dialect c g) qNegFLoop qNegV0 qNegState (.stmt (.block qNegBody)) (.sres qNegVb qNegTouched .normal) :=
    Step.block hBodySS
  have hC1 : Step (Bridge.Dialect c g) qNegFLoop qNegV0 qNegState (.expr qNegCond) (.eres (.vals [1] qNegState)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.lt) (args := [yvar "q_pc", yvar "q_end"])
      (argvals := [0x1000, 0x1001]) (st1 := qNegState) (rets := [1]) (st2 := qNegState)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [yvar "q_end"]) (e := yvar "q_pc") (restvals := [0x1001])
        (v := (0x1000 : U256)) (st1 := qNegState) (st2 := qNegState)
        (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := yvar "q_end") (restvals := []) (v := (0x1001 : U256))
          (st1 := qNegState) (st2 := qNegState) (Step.argsNil (D := (Bridge.Dialect c g))) (Step.var (D := (Bridge.Dialect c g)) rfl))
        (Step.var (D := (Bridge.Dialect c g)) rfl))
      (by show stepOp Op.lt [0x1000, 0x1001] qNegState = some (.ok [1] qNegState); rfl)
  have hC2 : Step (Bridge.Dialect c g) qNegFLoop qNegVb qNegTouched (.expr qNegCond) (.eres (.vals [0] qNegTouched)) :=
    Step.builtinOk (D := (Bridge.Dialect c g)) (op := Op.lt) (args := [yvar "q_pc", yvar "q_end"])
      (argvals := [0x1001, 0x1001]) (st1 := qNegTouched) (rets := [0]) (st2 := qNegTouched)
      (Step.argsCons (D := (Bridge.Dialect c g)) (rest := [yvar "q_end"]) (e := yvar "q_pc") (restvals := [0x1001])
        (v := (0x1001 : U256)) (st1 := qNegTouched) (st2 := qNegTouched)
        (Step.argsCons (D := (Bridge.Dialect c g)) (rest := []) (e := yvar "q_end") (restvals := []) (v := (0x1001 : U256))
          (st1 := qNegTouched) (st2 := qNegTouched) (Step.argsNil (D := (Bridge.Dialect c g))) (Step.var (D := (Bridge.Dialect c g)) rfl))
        (Step.var (D := (Bridge.Dialect c g)) rfl))
      (by show stepOp Op.lt [0x1001, 0x1001] qNegTouched = some (.ok [0] qNegTouched); rfl)
  have hPost : Step (Bridge.Dialect c g) qNegFLoop qNegVb qNegTouched (.stmt (.block [])) (.sres qNegVb qNegTouched .normal) :=
    Step.block (D := (Bridge.Dialect c g)) (Vb := qNegVb) (Step.seqNil (D := (Bridge.Dialect c g)))
  have hDone : Step (Bridge.Dialect c g) qNegFLoop qNegVb qNegTouched (.loop qNegCond [] qNegBody) (.sres qNegVb qNegTouched .normal) :=
    Step.loopDone hC2 rfl
  have hLoop : Step (Bridge.Dialect c g) qNegFLoop qNegV0 qNegState (.loop qNegCond [] qNegBody) (.sres qNegVb qNegTouched .normal) :=
    Step.loopStep hC1 (by show (1 : U256) ≠ 0; decide) hBodyBlk (Or.inl rfl) hPost hDone
  have hFor : Step (Bridge.Dialect c g) qNegF0 qNegV0 qNegState (.stmt (Stmt.forLoop [] qNegCond [] qNegBody))
      (.sres (restore qNegV0 qNegVb) qNegTouched .normal) :=
    Step.forLoop (Step.seqNil (D := (Bridge.Dialect c g))) hLoop
  have hfinal : ExecStmts (Bridge.Dialect c g) [] qNegV0 qNegState [GenAst.qvmLoop quotientCtx qNegProgram qNegTable]
      (restore qNegV0 qNegVb) qNegTouched .normal :=
    Step.seqCons hFor Step.seqNil
  exact ⟨_, _, hfinal⟩

theorem qNeg_Agrees (program : QuotientProgram) :
    Agrees [] program.constMptr 0 0 [qOpNeg] qNegState qBadMemory qNegSegment := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by simpa [qNegSegment] using hi
    subst this
    rfl
  · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · intro a ha; exact absurd ha (Nat.not_lt_zero a)

theorem evalQuotientIdentity_negEmptyStack :
    Midfall.Generator.evalQuotientIdentity [qOpNeg] [] qBadMemory =
      .error (QVMFault.stackUnderflow 0) := by
  have hloop : Midfall.Generator.evalQuotientIdentityLoop [qOpNeg] [] 0 [] qBadMemory
      = .error (QVMFault.stackUnderflow 0) := by
    show Midfall.Generator.evalQuotientIdentityLoop.go [qOpNeg] [] 1 0 [] qBadMemory = _
    simp only [Midfall.Generator.evalQuotientIdentityLoop.go]
    rfl
  unfold Midfall.Generator.evalQuotientIdentity
  rw [hloop]
  rfl

theorem qinterpRefines_qvmLoop_row_is_false_at_a_valid_label :
    ¬ QInterpRefines (D := (Bridge.Dialect c g))
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment qNegProgram) (Top := qinterpTop)
      (Agrees := fun st mem s => Agrees [] qNegProgram.constMptr 0 0 [qOpNeg] st mem s)
      [] [GenAst.qvmLoop quotientCtx qNegProgram qNegTable] [qOpNeg] [] := by
  intro H
  obtain ⟨V', st', hrun⟩ := qvmLoop_neg_arm_runs
  have h := H qNegSegment qBadMemory qNegSegment_inWindow qNegV0 qNegState
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, qNeg_Agrees qNegProgram⟩ V' st' .normal hrun
  cases h with
  | inl h => exact absurd h.1 (by decide : ¬ ((Outcome.normal : Outcome) = Outcome.halt))
  | inr h =>
      obtain ⟨v, mem', hv, _, _⟩ := h.2
      have hseg : (([qOpNeg].drop qNegSegment.cursor).take (qNegSegment.exprEnd - qNegSegment.cursor))
          = [qOpNeg] := rfl
      rw [hseg, evalQuotientIdentity_negEmptyStack] at hv
      cases hv

#print axioms Midfall.LoweringV3.QuotientRows.qvmLoop_neg_arm_runs
#print axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_row_is_false_at_a_valid_label
#cone_sorries Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_row_is_false_at_a_valid_label
#assert_axioms Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_row_is_false_at_a_valid_label [propext, Classical.choice, Quot.sound] native []


/-! ### 13. THE REPAIRED CONTRACT (QFIX): WHAT THE FOUR WITNESSES DO TO THE GUARDS

Section 11 and section 12 refute the committed row at four concrete divergences. This section does
NOT repair the row - the row is untouched, still one sorry at 'QuotientInterp.lean:270', and W13's
deletion is a human ruling. It tests the repaired contract that section 10 of 'QuotientInterp.lean'
states ('QInterpRefinesRepaired', with guards 'QWindowNoWrap', 'QTableAgrees', 'QHeadNoPop',
'QPreCachedTop') against those four witnesses, by COMPUTATION on the guards themselves: each witness
violates at least one guard, so none of them is a counterexample to the repaired form. That is the
evidence the repair is targeted and not cosmetic - and the attribution matters, so each theorem says
which guard fails and, for the two witnesses that pass guards 1 and 2, the fact that they pass them.

  WITNESS 1, section 11's 'qBadSegment' at base '2^256 - 1': GUARD 1 FAILS, GUARD 3b FAILS, guard 2 holds.
  WITNESS 2, section 12's 'qNegSegment' at the DEFAULT table: guards 1, 2 and 3a ALL HOLD, GUARD 3b FAILS.
  WITNESS 3, QLOOP's moved label 'tcq.op.neg := qOpAdd': GUARD 2 FAILS, GUARD 3b FAILS.
  WITNESS 4, QLOOP's 'tcq.op.pushConst := 200' on '[200,0,0]': GUARD 2 FAILS, GUARD 3b FAILS, guard 1 holds.

**AND THE ANSWER TO 'ARE THE GUARDS ENOUGH?' IS NO - FOUR PROOF OBLIGATIONS REMAIN, NAMED IN 13.4.**
They are not further hypotheses: the guards are a complete answer to the four witnesses. What the
guards cannot do is make the LOOP true, because three of the four obligations are inside the loop
induction rather than in its pre. -/

/-- **THE REPAIRED CONTRACT AT THE EMITTER'S LOOP** - the exact restatement the human would adopt in
    place of the refuted row, as a NAMED 'Prop' and NOT as a row: it carries no proof and no sorry, so
    nothing here pre-empts the W13 ruling on 'qinterpRefines_qvmLoop'. Binders are the refuted row's,
    verbatim ('ctx', 'program', 'tcq', 'funs', 'bytes', 'consts', 'frameBase', 'frameWords'), and so is
    the instantiation of 'reverts', 'Agrees', 'AtSegment' and 'Top'; the only addition is 'tcq', which
    the repaired form needs to state guard 2. -/
def QInterpRefinesRepaired_qvmLoop {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (bytes : List Nat) (consts : List Midfall.Word256)
    (frameBase frameWords : Nat) : Prop :=
  QInterpRefinesRepaired (c := c) (g := g) tcq funs [GenAst.qvmLoop ctx program tcq]
    Midfall.Lowering.Reverted bytes consts
    (fun st mem s => Agrees consts program.constMptr frameBase frameWords bytes st mem s)
    (AtSegment (c := c) (g := g) (program := program)) qinterpTop

/-! #### 13.1 WITNESS 1 (section 11): the wrapping window -/

/-- **WITNESS 1 VIOLATES GUARD 1.** 'qBadSegment' has 'base = 2^256 - 1' and 'exprEnd = 1', so
    'base + exprEnd = 2^256' and the window wraps. COMPUTED, not argued: the refutation is one
    'decide' on the two literals, which is exactly the fact 'AtSegment' leaves unsaid. -/
theorem qfix_witness1_violates_windowNoWrap : ¬ QWindowNoWrap qBadSegment := by
  intro h
  exact absurd h (by decide : ¬ (qWrapBase + 1 < 2 ^ 256))

/-- **AND ALSO GUARD 3b**: its head byte is 200, which is no reference opcode at all - the 'qOpX'
    family runs '0x01'-'0x22' - so the reference's first step on the segment is a refusal. Two guards
    exclude this witness, which is why the repair does not depend on getting either one exactly right. -/
theorem qfix_witness1_violates_headNoPop : ¬ QHeadNoPop qBadBytes qBadSegment := by
  intro h
  exact absurd h (by decide : ¬ (200 ∈ qNoPopOpcodes))

/-- **GUARD 1 IS THE ONE THAT MATTERS HERE**: the same witness satisfies guard 2 at the default table
    (which is the table section 11's refutation is generic in), so table agreement alone would not have
    repaired the row - ROWFALSE's stated consequence, confirmed by computation. -/
theorem qfix_witness1_passes_tableAgreement : QTableAgrees templateConstantsDefault.quotientVm :=
  QTableAgrees_default

/-! #### 13.2 WITNESS 2 (section 12): the neg arm at the DEFAULT table -/

/-- **WITNESS 2 SATISFIES GUARD 1**: '0x1000 + 1 < 2^256'. The wrap is not what breaks this one. -/
theorem qfix_witness2_satisfies_windowNoWrap : QWindowNoWrap qNegSegment :=
  show (0x1000 : Nat) + 1 < 2 ^ 256 from by decide

/-- **WITNESS 2 SATISFIES GUARD 2**: 'qNegTable' IS the default table, and guard 2 holds of it. -/
theorem qfix_witness2_satisfies_tableAgreement : QTableAgrees qNegTable := QTableAgrees_default

/-- **WITNESS 2 SATISFIES GUARD 3a**: its environment 'qNegV0' really does pin the cached top empty
    ('q_has_top = 0'), so the correspondence between the emitted cached top and the reference's stack
    DEPTH is not what fails either. -/
theorem qfix_witness2_satisfies_preCachedTop : QPreCachedTop (c := c) (g := g) qNegV0 :=
  ⟨rfl, 0, rfl⟩

/-- **WITNESS 2 VIOLATES GUARD 3b, AND THAT IS THE ONLY GUARD IT VIOLATES.** The segment is
    '[qOpNeg]' and 'neg' pops: 'evalQuotientIdentityStep' calls 'popStack stack idx' on the empty
    stack the identity starts with ('VmReference.lean:766-768'), which is the '.error
    (stackUnderflow 0)' section 12 computed. The emitted neg arm does not pop anything - it rewrites
    'q_top' in place - so it runs to a normal exit on a garbage cached top. Guard 3b is the clause
    that says the head byte must be one the reference can execute from an empty stack, and it is what
    makes the repaired form immune to this witness. -/
theorem qfix_witness2_violates_headNoPop : ¬ QHeadNoPop [qOpNeg] qNegSegment := by
  intro h
  exact absurd h (by decide : ¬ (qOpNeg ∈ qNoPopOpcodes))

/-! #### 13.3 WITNESS 3 (QLOOP's moved label) AND WITNESS 4 (QLOOP's own words) -/

/-- **WITNESS 3: A MOVED LABEL.** 'tcq.op.neg := qOpAdd' (6), read on the segment '[qOpAdd]'. The
    emitted switch finds the neg arm at byte 6 - no earlier label collides, so it is reachable - and
    runs it; the reference reads byte 6 as 'add', pops TWO values from an empty stack and errors. This
    is the variant section 12 checked by running the vendored interpreter at fuel 18. -/
def qfix_movedTable : QuotientVmTemplateConstants :=
  { qNegTable with op := { qNegTable.op with neg := qOpAdd } }

/-- **WITNESS 3 VIOLATES GUARD 2**: the pair '(qOpAdd, qOpNeg)' is in the agreement list and its two
    components differ. Computed. -/
theorem qfix_witness3_violates_tableAgreement : ¬ QTableAgrees qfix_movedTable := by
  intro H
  have h1 : (qOpAdd, qOpNeg) ∈ qOpcodeAgreementPairs qfix_movedTable := by decide
  exact absurd (H _ h1) (by decide : ¬ (qOpAdd = qOpNeg))

/-- **AND GUARD 3b as well**: byte 6 is 'add', which pops two operands. -/
theorem qfix_witness3_violates_headNoPop : ¬ QHeadNoPop [qOpAdd] qNegSegment := by
  intro h
  exact absurd h (by decide : ¬ (qOpAdd ∈ qNoPopOpcodes))

/-- **WITNESS 4: QLOOP'S OWN WORDS.** 'tcq.op.pushConst := 200' on the segment '[200, 0, 0]' - the
    example 'QuotientLoopCompose.lean:47-62' gives in prose. The switch is REACHED (the window is
    ordinary) and selects the pushConst arm at byte 200, while the reference has no opcode 200 and
    refuses it as 'unknownOpcode'. -/
def qfix_qloopTable : QuotientVmTemplateConstants :=
  { qNegTable with op := { qNegTable.op with pushConst := 200 } }

/-- The ordinary three-byte window '[200, 0, 0]' the prose witness describes. -/
def qfix_qloopSegment : QSegment := { base := 0, len := 3, cursor := 0, exprEnd := 3 }

/-- **WITNESS 4 VIOLATES GUARD 2**: '(200, qOpPushConst)' is a pair whose components differ. -/
theorem qfix_witness4_violates_tableAgreement : ¬ QTableAgrees qfix_qloopTable := by
  intro H
  have h1 : (200, qOpPushConst) ∈ qOpcodeAgreementPairs qfix_qloopTable := by decide
  exact absurd (H _ h1) (by decide : ¬ (200 = qOpPushConst))

/-- **AND GUARD 3b**: 200 is not a reference opcode at all, so it is certainly not a no-pop one. -/
theorem qfix_witness4_violates_headNoPop : ¬ QHeadNoPop [200, 0, 0] qfix_qloopSegment := by
  intro h
  exact absurd h (by decide : ¬ (200 ∈ qNoPopOpcodes))

/-- **WITNESS 4 SATISFIES GUARD 1** - the window is at base 0, so nothing wraps. Recorded to show the
    four witnesses are not all the same defect: this one is purely a table defect. -/
theorem qfix_witness4_satisfies_windowNoWrap : QWindowNoWrap qfix_qloopSegment :=
  show (0 : Nat) + 3 < 2 ^ 256 from by decide

/-- **THE SUMMARY THE CARD ASKS FOR: EVERY ONE OF ROWFALSE'S FOUR WITNESSES VIOLATES AT LEAST ONE
    GUARD OF THE REPAIRED FORM.** Stated as one proposition conjoining the four exclusions, so a
    reader checks the claim once. -/
theorem qfix_all_four_witnesses_are_excluded :
    (¬ QWindowNoWrap qBadSegment) ∧ (¬ QHeadNoPop qBadBytes qBadSegment)
      ∧ (¬ QHeadNoPop [qOpNeg] qNegSegment)
      ∧ (¬ QTableAgrees qfix_movedTable) ∧ (¬ QHeadNoPop [qOpAdd] qNegSegment)
      ∧ (¬ QTableAgrees qfix_qloopTable) ∧ (¬ QHeadNoPop [200, 0, 0] qfix_qloopSegment) :=
  ⟨qfix_witness1_violates_windowNoWrap, qfix_witness1_violates_headNoPop,
    qfix_witness2_violates_headNoPop, qfix_witness3_violates_tableAgreement,
    qfix_witness3_violates_headNoPop, qfix_witness4_violates_tableAgreement,
    qfix_witness4_violates_headNoPop⟩

/-! #### 13.4 ARE THE GUARDS JOINTLY SUFFICIENT? NO - AND HERE IS THE RESIDUE, NAMED

**VERDICT: THE GUARDS CLOSE THE FOUR WITNESSES AND THEY DO NOT CLOSE THE LOOP.** They are hypotheses
about a SEGMENT AND A START STATE, and the row quantifies over a LOOP. Four obligations survive; none
of them is a fifth hypothesis of the same kind, so the honest answer to the card's question is that
the three guards are necessary and jointly sufficient for the four refutations, not for the row.

**(O1) THE FETCH BRIDGE - 'qvmLoopPre' IS NOT YET A CONTRACT.** The arm lemmas are stated at the state
AFTER the loop's two-statement pre ('GenAstQvm.lean:382': 'q_op := byte(0, mload q_pc)', then
'q_pc := q_pc + 1'), while 'AtSegment' pins the state BEFORE it. The exact remaining goal is a
contract for those two statements:

    StmtsContractAll (D := Bridge.Dialect c g) funs GenAst.qvmLoopPre
      (fun V st => AtSegment program V st s ∧ Agrees ... st mem s ∧ QPreCachedTop V)
      (fun V st V' st' o => o = .normal
        ∧ VEnv.get V' "q_op" = some (BitVec.ofNat 256 (qHeadByte bytes s))
        ∧ VEnv.get V' "q_pc" = some (BitVec.ofNat 256 (s.base + s.cursor + 1)) ∧ ...)

and it needs guard 1 to turn 'q_pc.toNat' back into the true address 's.base + s.cursor' - which is
the first place the repair earns its keep: without guard 1 the fetch reads memory at the WRAPPED
address and the bridge is false. Nothing in the tree states this contract today: 'grep qvmLoopPre'
finds the definition, the two 'rfl' restatements of the loop body ('QuotientFrame.lean:780',
'QuotientLoopCompose.lean:109') and one KAT length gate. It is a proof obligation, not a hypothesis.

**(O2) THE STACK CORRESPONDENCE IS INDUCTIVE, NOT A PRE CONDITION.** Guard 3b pins the head byte; the
loop needs 'q_has_top = 1 iff the reference's stack is non-empty, and when non-empty q_top IS its
head' at EVERY iteration, carried through the invariant. That is ROW.Q's induction and no hypothesis
about the start state can discharge it. Named below as 'QStackInvariant' so the human sees what the
loop proof must add; it is NOT a hypothesis of the repaired contract.

**(O3) THE PER-ARM REFERENCE TIE IS STILL ZERO FOR THE ARMS.** QLOOP's finding (3)
('QuotientLoopCompose.lean:33-40') is untouched by this card: 'qArmValueAll_X' constrains the emitted
registers and 'qStepValue_X' constrains the reference step, and no theorem says the two words are
equal. Guard 2 makes the two sides read the SAME OPCODE; it does not make them COMPUTE the same word.
The limb arms additionally need 'PG_limbCountAgrees'.

**(O4) THE SEGMENT'S WIDTH AND THE EPILOGUE.** The contract's post asks for 'AtSegment V' st' s.atEnd'
- the END position - which the loop only reaches if the segment's byte length is exactly the sum of
the arms' consumed widths: the emitted arm's 'q_pc' advance must equal the reference's 'consumed'
field byte for byte. That is a fact about the SEGMENT that none of the four guards says. FALSIFIER 4
in 'QuotientInterp' section 8 is the same defect seen from the operand-width side, and section 13.5
lands the positive half of this obligation for the one arm that composes: the pushConst segment is
three bytes and BOTH sides advance three.

**WHAT THIS SECTION DOES NOT CLAIM.** It does not prove the repaired contract of the loop - that is
ROW.Q proper, and (O1)-(O4) are why. It proves the guards are individually decidable, jointly
satisfiable, true of the default table, and violated by each of the four witnesses. -/

/-- **(O2), NAMED.** The inductive form of the stack correspondence: at EVERY iteration, not just the
    first, the emitted cached top is live exactly when the reference's stack is non-empty and holds its
    head. The repaired contract does NOT assume this - it cannot, it is about a run and not about a
    start state - and no guard of the kind in section 10 can replace it. Recording it here is the
    answer to 'is a fourth gap left': yes, and it is this one, plus (O1), (O3) and (O4). -/
def QStackInvariant {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) : Prop :=
  (VEnv.get V "q_has_top" = some (0 : U256)
      ∧ VEnv.get V "q_sp" = some (BitVec.ofNat 256 program.stackMptr))
    ∨ (∃ x : U256, VEnv.get V "q_has_top" = some 1 ∧ VEnv.get V "q_top" = some x)

#print axioms Midfall.LoweringV3.QuotientRows.qfix_witness1_violates_windowNoWrap
#print axioms Midfall.LoweringV3.QuotientRows.qfix_witness2_violates_headNoPop
#print axioms Midfall.LoweringV3.QuotientRows.qfix_witness3_violates_tableAgreement
#print axioms Midfall.LoweringV3.QuotientRows.qfix_witness4_violates_tableAgreement
#print axioms Midfall.LoweringV3.QuotientRows.qfix_all_four_witnesses_are_excluded
#cone_sorries Midfall.LoweringV3.QuotientRows.qfix_all_four_witnesses_are_excluded
#assert_axioms Midfall.LoweringV3.QuotientRows.qfix_witness1_violates_windowNoWrap [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qfix_witness2_violates_headNoPop [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qfix_witness3_violates_tableAgreement [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qfix_witness4_violates_tableAgreement [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.QuotientRows.qfix_all_four_witnesses_are_excluded [propext, Classical.choice, Quot.sound] native []
end Midfall.LoweringV3.QuotientRows

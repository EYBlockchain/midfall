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
-- WHAT IS NOT HERE, AND WHY. ROW.Q.5 (one leaf per GENERATED LINE FAMILY, as a list induction over
-- its block producer's AST twin) CANNOT BE STATED: the twins do not exist and OBJ.15 decided they
-- must not - 'GenAstQvm.lean:61-69' splices all six families through 'qGenFlat'/'qGenNested', i.e.
-- through 'YulParse.parseLines', because an AST twin would be a SECOND implementation of the ported
-- Rust codegen, "the thing the whole package exists to avoid". The card's own "Stop if" line
-- anticipated this (PG-Q-OBJECT). It is reported, not worked around.
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
NOT STATED, WITH THE REASON: ROW.Q.5 (one leaf per generated line family) - see the header. -/
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

end Midfall.LoweringV3.QuotientRows

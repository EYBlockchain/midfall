-- |
-- Midfall.LoweringV3.TranscriptRows
--
-- ROW.TP (WP A6): the transcriptParser row's VOCABULARY, its NAMED LEAVES, and the PROVED GLUE
-- `tp_blockSim`. PORTED from 'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean' section 6
-- (:635-835), which does not compile (RECON.3) - a copy, not an import, exactly as
-- QuotientRows.lean does for ROW.Q and LagrangeRows.lean does for T3.9.
--
-- WHAT THIS FILE IS, AND WHAT IT IS NOT. It lands the ROW.TP statements at the ONE row shape
-- (D-P74 item 2: 'BlockSim'/'BlockProgS' over 'StageInv'), the schedule vocabulary the SEM
-- children are stated in ('TEv', 'tpWalk', 'tpEvents', 'TEv.slot?', 'Render.tpEvents',
-- 'XcriptSlots', 'TpPost'), the two children ROW.TP.1 ('inline_g1WalkLoop') and ROW.TP.6
-- ('tp_events_slots') - BOTH PROVED - the W12 witness/falsifier pair each remaining hole needs,
-- and the row glue 'tp_blockSim' which is PROVED from the three SEM/ALG leaves by the evidence's
-- own twelve-line argument. 'tp_blockProgS' is the tenth leaf and is stated, not proved.
--
-- THE ROWS ARE NOT WIRED IN. 'Midfall/LoweringV3/Rows.lean' still carries its two bare tp
-- 'sorry's, so this file moves NO root leaf, NO root cone and NO register ROOT row. When the
-- named leaves close, the two rows in Rows.lean become one-line applications of
-- 'TranscriptRows.tp_blockSim' / 'TranscriptRows.tp_blockProgS' - the consumer-first landing the
-- card asks for.
--
-- PORT CHANGES, and nothing else (the same three the ROW.Q port made):
--   (a) THE VALIDITY HYPOTHESIS. The evidence writes '(hR : R.Valid) (hpins : SimPins R)'.
--       'SimPins' is NOT a declaration in the tree: RECON.2 dissolved it and PROVED the projection
--       (Composition.lean:178 'pins_from_valid_and_headlineLaws'). So every leaf that read it takes
--       'ValidV3 R' plus 'G1CodecHeadlineLaws R.E.g1', which is the bundle SimRowsV3/ProgRowsV3
--       ask for. No clause was added to ValidV3 or Render.Valid.
--   (b) THE SCHEDULE is stated about the render's DERIVED plan view ('Render.pv', 'Render.plan',
--       'Render.model'), so 'tp_events_slots' is about the generated objects by construction.
--   (c) THE HELPERS: the evidence's 'inlineScan_append' (GEN.4) is NOT restated here - it is
--       PROVED in the tree at 'Midfall/Lowering/InlineConstants.lean:699' with the same statement
--       up to the namespace. ROW.TP.1's two companions ('g1WalkBody', 'g1AbsorbCopy') are not
--       stated: the row reads the loop only, and the absorb-copy sites are handled by the SEM
--       leaves' own frames.
--
-- W12, PER HOLE. Every new sorried statement below carries a PROVED witness that its conclusion is
-- not 'True' and a PROVED falsifier of the weakening a reader would otherwise assume:
--   * tp_events_slots - witness 'tp_events_slots_witness_nonempty' (the filtered schedule is
--     nonempty at every layout), falsifier
--     'tp_events_slots_falsifier_not_every_event_reads_a_slot' (the filterMap drops 'word', so the
--     equality is a schedule-to-slot relation and not the identity).
--   * g1walk_loop_sem - falsifier 'g1walk_loop_sem_falsifier_empty_block' (the empty block ends
--     normally leaving zeroed memory, while the post demands 128 walk bytes of
--     'cdSlice ByteArray.empty', so the post is not vacuous).
--   * tp_computes - falsifier 'tp_computes_falsifier_empty_block' (the empty block's normal exit
--     does not satisfy 'TpPost': 'success = 1' is not free).
--   * tp_agrees - falsifier 'tp_agrees_falsifier_no_success' ('StageInv .transcript' demands
--     'success = 1', so the implication has content).
--   * tp_poison - falsifier 'tp_poison_falsifier_empty_block' (the empty block ends normally, so
--     "every run reverts" is not free).
--   * tp_blockProgS - falsifier 'tp_blockProgS_falsifier_reverting_block_is_not_total' (a block
--     that only reverts has no normal run, so totality is not the soundness row).
--   * tp_blockSim is PROVED; its falsifier 'tp_blockSim_falsifier_return_is_not_the_post' shows
--     the post refuses a 'ret' (a halt that is not a revert and not 'exitSimAt'), the v1 defect
--     class at the row.
--
-- NO FIXTURE (D-P71). Every statement is quantified over the render, the program, the table, the
-- layout and the calldata. 'poseidonRender' appears nowhere.
--
-- AXIOMS. 'inline_g1WalkLoop', 'tp_blockSim', the vocabulary lemmas and every falsifier are on
-- [propext, Classical.choice, Quot.sound] (the last only where 'List.find?'/'decide' needs it);
-- no 'native_decide' (D-P17); no 'maxHeartbeats'/'maxRecDepth' raise.
import Midfall.LoweringV3.QuotientRows
import Midfall.Yul.VKP
import Midfall.Yul.LoopRule
import Midfall.LoweringV2.Blocks.EcPairing
import Midfall.LoweringV3.VkWindow
import Midfall.LoweringV3.MemoryPairs
import Midfall.Lowering.GenAst
import Midfall.Lowering.Calldata
import Midfall.Lowering.Stage
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.TranscriptRows

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. THE SCHEDULE VOCABULARY (evidence :645-704, VERBATIM) -/

/-- The parser's schedule as data: what it absorbs, copies and squeezes, in order. The emitter is
    a fold of this list; the SEM children prove the fold, the ALG child relates the list to the
    Lean transcript. VERBATIM (evidence :648-665). -/
inductive TEv
  /-- `common_word(buf, w)` of a word that is not calldata (the VK digest, the instance count). -/
  | word
  /-- The committed instance: 128 zero bytes. -/
  | zeros
  /-- One public input, range-folded into `success`. -/
  | inst
  /-- One 128-byte frame absorbed and copied to the walk or slot `dst`. -/
  | g1 (dst : String)
  /-- One scalar, range-checked, absorbed, and spilled to the evals window when `spill`. -/
  | fr (spill : Bool)
  /-- `squeeze_to(buf, add(slot, off))`. -/
  | squeeze (slot : String) (off : Nat)
  /-- The 128-bit mask on `X3_MPTR`. -/
  | mask
  /-- `mstore(Q_EVAL_CPTR_MPTR, proof_cptr)`. -/
  | saveCptr
  deriving DecidableEq, Repr

/-- One walk loop: a frame per 128 bytes. VERBATIM (:667-668). -/
def tpWalk (dst : String) (bytes : Nat) : List TEv := List.replicate (bytes / 128) (TEv.g1 dst)

/-- The schedule `emitTranscriptParserAt` prints, argument for argument. VERBATIM (:670-693). -/
def tpEvents (numInstances : Nat) (userPhases : List UserPhase)
    (numLookups numPermutationZs lookupHPlusAcc numTrashcans : Nat)
    (truncatedChallenges : Bool) (L : ProofCalldataLayout) : List TEv :=
  [TEv.word, TEv.zeros, TEv.word] ++ List.replicate numInstances TEv.inst ++
  (userPhases.flatMap fun ph => tpWalk "advice_walk" ph.adviceBytes ++
    (List.range ph.numChallenges).map fun j =>
      TEv.squeeze "CHALLENGE_MPTR" ((ph.challengeOffset + j) * 32)) ++
  [TEv.squeeze "THETA_MPTR" 0] ++
  (if numLookups != 0 then tpWalk "lookup_m_walk" L.lookupMultiplicities.byteLen else []) ++
  [TEv.squeeze "BETA_MPTR" 0, TEv.squeeze "GAMMA_MPTR" 0] ++
  (if numPermutationZs != 0 then tpWalk "perm_z_walk" L.permutationProducts.byteLen else []) ++
  (if lookupHPlusAcc != 0 then
    L.lookups.flatMap fun lk =>
      tpWalk "lookup_helper_walk" lk.helpers.byteLen ++ [TEv.g1 "lookup_z_walk"] else []) ++
  [TEv.squeeze "TRASH_CHALLENGE_MPTR" 0] ++
  (if numTrashcans != 0 then tpWalk "trashcan_walk" L.trash.byteLen else []) ++
  [TEv.squeeze "Y_MPTR" 0] ++ tpWalk "quotient_walk" L.quotientLimbs.byteLen ++
  [TEv.squeeze "X_MPTR" 0] ++ List.replicate (L.evals.byteLen / 32) (TEv.fr true) ++
  [TEv.squeeze "X1_MPTR" 0, TEv.squeeze "X2_MPTR" 0, TEv.g1 "F_COM_MPTR",
   TEv.squeeze "X3_MPTR" 0] ++
  (if truncatedChallenges then [TEv.mask] else []) ++ [TEv.saveCptr] ++
  List.replicate (L.qEvals.byteLen / 32) (TEv.fr false) ++
  [TEv.squeeze "X4_MPTR" 0, TEv.g1 "PI_MPTR"]

/-- The calldata slot an event reads, if any. VERBATIM (:695-699). -/
def TEv.slot? : TEv → Option WireSlot
  | .g1 _ => some WireSlot.g1
  | .fr _ => some WireSlot.fr
  | _ => none

@[simp] theorem TEv.slot?_g1 (dst : String) : TEv.slot? (.g1 dst) = some WireSlot.g1 := rfl
@[simp] theorem TEv.slot?_fr (spill : Bool) : TEv.slot? (.fr spill) = some WireSlot.fr := rfl
@[simp] theorem TEv.slot?_word : TEv.slot? .word = none := rfl
@[simp] theorem TEv.slot?_zeros : TEv.slot? .zeros = none := rfl
@[simp] theorem TEv.slot?_inst : TEv.slot? .inst = none := rfl
@[simp] theorem TEv.slot?_squeeze (slot : String) (off : Nat) :
    TEv.slot? (.squeeze slot off) = none := rfl
@[simp] theorem TEv.slot?_mask : TEv.slot? .mask = none := rfl
@[simp] theorem TEv.slot?_saveCptr : TEv.slot? .saveCptr = none := rfl

/-- A squeeze reads no calldata slot: the challenge-squeeze runs filter to nothing. -/
theorem filterMap_squeeze_eq_nil (l : List Nat) (slot : String) (f : Nat → Nat) :
    (l.filterMap (TEv.slot? ∘ fun j => TEv.squeeze slot (f j))) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro a _
  rfl

@[simp] theorem TEv.filterMap_cons_word (l : List TEv) :
    (TEv.word :: l).filterMap TEv.slot? = l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_zeros (l : List TEv) :
    (TEv.zeros :: l).filterMap TEv.slot? = l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_inst (l : List TEv) :
    (TEv.inst :: l).filterMap TEv.slot? = l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_squeeze (slot : String) (off : Nat) (l : List TEv) :
    (TEv.squeeze slot off :: l).filterMap TEv.slot? = l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_mask (l : List TEv) :
    (TEv.mask :: l).filterMap TEv.slot? = l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_saveCptr (l : List TEv) :
    (TEv.saveCptr :: l).filterMap TEv.slot? = l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_g1 (dst : String) (l : List TEv) :
    (TEv.g1 dst :: l).filterMap TEv.slot? = WireSlot.g1 :: l.filterMap TEv.slot? := rfl
@[simp] theorem TEv.filterMap_cons_fr (spill : Bool) (l : List TEv) :
    (TEv.fr spill :: l).filterMap TEv.slot? = WireSlot.fr :: l.filterMap TEv.slot? := rfl

example (l : List TEv) :
    (List.filterMap TEv.slot? (TEv.word :: TEv.zeros :: l)) = List.filterMap TEv.slot? l := by simp

/-- The schedule of a render: its DERIVED plan view's eleven parser values, read off `R.pv`
    (Statements.lean:162 `planViewOf R.plan R.model R.cfg.accumulator`) and the plan's own
    proof layout. VERBATIM (:701-704) with the plan view spelled through the render. -/
def _root_.Midfall.LoweringV2.Render.tpEvents (R : Render p G₁ G₂ Gₜ) : List TEv :=
  Midfall.LoweringV3.TranscriptRows.tpEvents R.pv.numInstances R.pv.userPhases R.pv.numLookups
    R.pv.numPermutationZs R.pv.lookupHPlusAcc R.pv.numTrashcans R.pv.truncatedChallenges
    R.pv.proofLayout

/-! ## 2. THE POST VOCABULARY (evidence :762-786, VERBATIM) -/

/-- The part of `Agree .transcript` that is about squeezed words: for every decoding, the ten
    challenge slots hold the transcript-only run's challenges. VERBATIM (:764-776). -/
def XcriptSlots (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (st : EvmState) : Prop :=
  ∀ ms instW inst, Decoded R cd ms instW inst →
    ∀ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x →
      holdsFr st (ptrAddr R.pv.memory.thetaMptr) x.trace.theta = true ∧
      holdsFr st (ptrAddr R.pv.memory.betaMptr) x.trace.beta = true ∧
      holdsFr st (ptrAddr R.pv.memory.gammaMptr) x.trace.gamma = true ∧
      holdsFr st (ptrAddr R.pv.memory.trashChallengeMptr) x.trace.trashChallenge = true ∧
      holdsFr st (ptrAddr R.pv.memory.yMptr) x.trace.y = true ∧
      holdsFr st (ptrAddr R.pv.memory.xMptr) x.alg.x = true ∧
      holdsFr st (ptrAddr R.pv.memory.x1Mptr) x.r.x1 = true ∧
      holdsFr st (ptrAddr R.pv.memory.x2Mptr) x.r.x2 = true ∧
      holdsFr st (ptrAddr R.pv.memory.x3Mptr) x.r.x3 = true ∧
      holdsFr st (ptrAddr R.pv.memory.x4Mptr) x.r.x4 = true

/-- **THE COMMITMENT HALF OF THE `Inv .transcript` ASSEMBLY.** For every decoding and
    every transcript-only run witness, the four G1 windows hold `toEip` of the run's OWN
    decoded points: the advice commitments, the quotient limbs, `fCom` and `pi`.

    This is the consumer side of A11's `runsAll_readAlgebra` value bridge: the read
    schedule identifies the run's arrays with the decoded calldata messages, and
    `G1CodecHeadlineLaws.eipRoundtrip` turns each calldata frame into `toEip` of that
    message. The `Inv .transcript` assembly below spends it; the parser's own `TpPost`
    carries the matching memory windows (`MirrorAt`). -/
def XcriptG1 (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (st : EvmState) : Prop :=
  ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
    Decoded R cd ms instW inst →
    ∀ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x →
      holdsG1s R.E st (ptrAddr R.pv.memory.adviceCommsMptrBase)
        (x.trace.adviceCommitments.getD 0 #[]) = true ∧
      holdsG1s R.E st (ptrAddr R.pv.memory.quotientLimbCommsMptrBase)
        x.alg.quotientLimbComs = true ∧
      holdsG1 R.E st (ptrAddr R.pv.memory.fComMptr) x.r.fCom = true ∧
      holdsG1 R.E st (ptrAddr R.pv.memory.piMptr) x.r.pi = true

/-- What a normal exit of the parser has established, with NO fact about a decoded point outside
    the `∀ decoding` of `XcriptSlots`. VERBATIM (:780-786). -/
def TpPost (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧
    BaseInv R Checkpoint.transcript V st ∧
    (rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd).isSome = true ∧
    MirrorAt R cd st ∧ XcriptSlots R H cd st

/-! ## 3. ROW.TP.1 - THE WALK LOOP IS CONSTANT-FREE -/

/-- **THE SLICE IS THE INLINED EMITTER OUTPUT.** The statement every SEM leaf starts from: the
    parser's slice is `emitTranscriptParserAt` at the render's own eleven values, constants
    inlined. PROVED by reduction (the evidence's rows assume this form; it is `lag_slice`'s
    parser twin and the reason `tp_computes`' pre can be about `R.slice`). -/
theorem tp_slice (R : Render p G₁ G₂ Gₜ) :
    R.slice Partial.transcriptParser =
      Inline.inlineContractConstants R.consts
        (GenAst.emitTranscriptParserAt R.pv.numInstances R.pv.userPhases R.pv.numLookups
          R.pv.numPermutationZs R.pv.lookupHPlusAcc R.pv.numTrashcans
          R.pv.truncatedChallenges R.pv.proofLayout) := rfl


/-- `shadowed` is monotone under appending on the right: if a name is owned by the enclosing
    binders, an inner binder added later cannot un-own it (the walk's shadow list is
    `sh ++ ["end"]`, the loop's own init binder). -/
theorem shadowed_append_right (sh more : List String) (x : String)
    (h : shadowed sh x = true) : shadowed (sh ++ more) x = true := by
  induction sh with
  | nil => simp [shadowed] at h
  | cons y ys ih =>
      rw [List.cons_append]
      simp only [shadowed] at h ⊢
      by_cases hyx : (y == x) = true
      · simp [hyx]
      · simp only [hyx] at h ⊢
        exact ih h

/-- A name is shadowed by the list that appends it: the loop's `end`. -/
theorem shadowed_append_self (sh : List String) (x : String) :
    shadowed (sh ++ [x]) x = true := by
  induction sh with
  | nil => simp [shadowed]
  | cons y ys ih =>
      rw [List.cons_append]
      simp only [shadowed]
      by_cases hyx : (y == x) = true
      · simp [hyx]
      · simp only [hyx]
        exact ih

/-- The variable occurrences of an expression, for the shadow side conditions of the inliner. -/
def tpExprVars : Expr EVM.Op → List String
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => args.flatMap tpExprVars
  | .call _ args => args.flatMap tpExprVars

theorem tpVars_call_two (f a b : String) :
    tpExprVars (Expr.call f [Expr.var a, Expr.var b]) = [a, b] := by simp [tpExprVars]

theorem tpVars_builtin_add_three (a b : String) (n : Nat) :
    tpExprVars (Expr.builtin Op.add [Expr.var a, Expr.var b, Expr.lit (.number n)]) = [a, b] := by simp [tpExprVars]

theorem tpVars_builtin_add_var (a : String) (n : Nat) :
    tpExprVars (Expr.builtin Op.add [Expr.var a, Expr.lit (.number n)]) = [a] := by simp [tpExprVars]

theorem tpVars_builtin_lt_two (a b : String) :
    tpExprVars (Expr.builtin Op.lt [Expr.var a, Expr.var b]) = [a, b] := by simp [tpExprVars]

theorem tpVars_builtin_calldatacopy (a b : String) (n : Nat) :
    tpExprVars (Expr.builtin Op.calldatacopy [Expr.var a, Expr.var b, Expr.lit (.number n)]) =
      [a, b] := by simp [tpExprVars]

mutual
/-- **THE USE-SITE RULE, ALL-VARIABLES FORM.** An expression every one of whose variable
    occurrences is shadowed is left alone by `inExpr`, at every fuel. -/
theorem tp_inExpr_eq_of_shadowed (consts : Inline.Consts) (sh : List String) :
    ∀ (f : Nat) (e : Expr EVM.Op),
      (∀ x ∈ tpExprVars e, Inline.shadowed sh x = true) →
      Inline.inExpr f e consts sh = e := by
  intro f e h
  cases f with
  | zero => rfl
  | succ m =>
      cases e with
      | lit l => rfl
      | var x =>
          have hx : Inline.shadowed sh x = true := h x (by simp [tpExprVars])
          simp [Inline.inExpr, hx]
      | builtin op args =>
          show Expr.builtin op (args.map (fun a => Inline.inExpr m a consts sh)) =
            Expr.builtin op args
          rw [tp_inExpr_args_eq consts sh m args (fun a ha x hx => h x (by
            simp only [tpExprVars, List.mem_flatMap]
            exact ⟨a, ha, hx⟩))]
      | call fn args =>
          show Expr.call fn (args.map (fun a => Inline.inExpr m a consts sh)) =
            Expr.call fn args
          rw [tp_inExpr_args_eq consts sh m args (fun a ha x hx => h x (by
            simp only [tpExprVars, List.mem_flatMap]
            exact ⟨a, ha, hx⟩))]

theorem tp_inExpr_args_eq (consts : Inline.Consts) (sh : List String) :
    ∀ (f : Nat) (args : List (Expr EVM.Op)),
      (∀ a ∈ args, ∀ x ∈ tpExprVars a, Inline.shadowed sh x = true) →
      args.map (fun a => Inline.inExpr f a consts sh) = args := by
  intro f args
  induction args with
  | nil => intro h; rfl
  | cons a rest ih =>
      intro h
      rw [List.map_cons,
        tp_inExpr_eq_of_shadowed consts sh f a (fun x hx => h a (by simp) x hx),
        ih (fun b hb x hx => h b (by simp [hb]) x hx)]
end

/-- Assignments whose expression is shadowed survive the inliner. -/
theorem inlineStmtStep_assign_shadowed (rec : List String → List (Stmt EVM.Op) → Inline.SRes)
    (consts : Inline.Consts) (sh : List String) (x : String) (e : Expr EVM.Op)
    (h : ∀ y ∈ tpExprVars e, Inline.shadowed sh y = true) :
    (Inline.inlineStmtStep rec consts sh (Stmt.assign [x] e)).1 = Stmt.assign [x] e := by
  simp only [Inline.inlineStmtStep]
  rw [tp_inExpr_eq_of_shadowed consts sh Inline.exprFuel e h]

/-- Expression statements whose expression is shadowed survive the inliner. -/
theorem inlineStmtStep_expr_shadowed (rec : List String → List (Stmt EVM.Op) → Inline.SRes)
    (consts : Inline.Consts) (sh : List String) (e : Expr EVM.Op)
    (h : ∀ y ∈ tpExprVars e, Inline.shadowed sh y = true) :
    (Inline.inlineStmtStep rec consts sh (Stmt.exprStmt e)).1 = Stmt.exprStmt e := by
  simp only [Inline.inlineStmtStep]
  rw [tp_inExpr_eq_of_shadowed consts sh Inline.exprFuel e h]

/-- A `let` whose expression is shadowed survives the inliner. -/
theorem inlineStmtStep_let_shadowed (rec : List String → List (Stmt EVM.Op) → Inline.SRes)
    (consts : Inline.Consts) (sh : List String) (x : String) (e : Expr EVM.Op)
    (h : ∀ y ∈ tpExprVars e, Inline.shadowed sh y = true) :
    (Inline.inlineStmtStep rec consts sh (Stmt.letDecl [x] (some e))).1 =
      Stmt.letDecl [x] (some e) := by
  simp only [Inline.inlineStmtStep, Option.map]
  rw [tp_inExpr_eq_of_shadowed consts sh Inline.exprFuel e h]

/-- The scan of a singleton block whose statement survives is the singleton block. -/
theorem inlineScan_single (fuel : Nat) (consts : Inline.Consts) (sh : List String)
    (s : Stmt EVM.Op)
    (hs : (Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts sh s).1 = s) :
    (Inline.inlineScan (fuel + 1) consts sh [s]).blks = [s] := by
  have hstep : (Inline.inlineStep (Inline.inlineScan fuel consts) consts sh [s]).blks =
      [(Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts sh s).1] := rfl
  rw [show Inline.inlineScan (fuel + 1) consts sh [s] =
    Inline.inlineStep (Inline.inlineScan fuel consts) consts sh [s] from rfl, hstep, hs]

/-- **ROW.TP.1, PORTED AND PROVED.** A walk loop is constant-free where its three cursors are
    bound: the inliner returns it unchanged. So a walk is FIXED TEXT plus one numeral, at every
    table. Evidence :728-735, statement verbatim.

    THE PROOF IS THE CARD'S THREE STEPS, and its only content is that every one of the eleven
    variable sites in the loop is shadowed. `inlineScan (fuel+2)` is one `inlineStep` (a singleton
    fold), `inlineStmtStep` at the `forLoop` descends into `init`, `cond`, `post` and `body` with
    `sh ++ ["end"]` (the init's `let end`), and each `inExpr` occurrence then hits
    `shadowed … = true` and is left alone; `inlineScan` at the empty post block is the empty block.
    No semantics is read. -/
theorem inline_g1WalkLoop (fuel : Nat) (consts : Inline.Consts) (sh : List String)
    (walk : String) (bytes : Nat) (hw : Inline.shadowed sh walk = true)
    (hp : Inline.shadowed sh "proof_cptr" = true) (hb : Inline.shadowed sh "buf_len" = true) :
    (Inline.inlineScan (fuel + 2) consts sh [GenAst.g1WalkLoop walk bytes]).blks =
      [GenAst.g1WalkLoop walk bytes] := by
  -- The loop's parts, as `g1WalkLoop` writes them (statements and their expressions).
  let eInit : Expr EVM.Op :=
    Expr.builtin Op.add [Expr.var "proof_cptr", Expr.lit (.number bytes)]
  let eCond : Expr EVM.Op := Expr.builtin Op.lt [Expr.var "proof_cptr", Expr.var "end"]
  let e1 : Expr EVM.Op :=
    Expr.call "common_uncompressed_g1" [Expr.var "buf_len", Expr.var "proof_cptr"]
  let e2 : Expr EVM.Op :=
    Expr.builtin Op.calldatacopy [Expr.var walk, Expr.var "proof_cptr", Expr.lit (.number 128)]
  let e3 : Expr EVM.Op := Expr.builtin Op.add [Expr.var walk, Expr.lit (.number 128)]
  let e4 : Expr EVM.Op :=
    Expr.builtin Op.add [Expr.var "proof_cptr", Expr.lit (.number 128)]
  let initStmt : Stmt EVM.Op := Stmt.letDecl ["end"] (some eInit)
  let s1 : Stmt EVM.Op := Stmt.assign ["buf_len"] e1
  let s2 : Stmt EVM.Op := Stmt.exprStmt e2
  let s3 : Stmt EVM.Op := Stmt.assign [walk] e3
  let s4 : Stmt EVM.Op := Stmt.assign ["proof_cptr"] e4
  -- The shadow facts after the loop's own `let end`.
  have hb' : Inline.shadowed (sh ++ ["end"]) "buf_len" = true :=
    shadowed_append_right sh ["end"] "buf_len" hb
  have hp' : Inline.shadowed (sh ++ ["end"]) "proof_cptr" = true :=
    shadowed_append_right sh ["end"] "proof_cptr" hp
  have hw' : Inline.shadowed (sh ++ ["end"]) walk = true :=
    shadowed_append_right sh ["end"] walk hw
  -- The init `let end := proof_cptr + bytes`.
  have hinit : (Inline.inlineScan (fuel + 1) consts sh [initStmt]).blks = [initStmt] := by
    apply inlineScan_single
    apply inlineStmtStep_let_shadowed
    intro y hy
    rw [show tpExprVars eInit = ["proof_cptr"] from
      tpVars_builtin_add_var "proof_cptr" bytes] at hy
    simp at hy
    rcases hy with h
    subst y
    exact hp
  -- The four body statements, each at the shadow list it is actually scanned with.
  have hs1 : (Inline.inlineStmtStep (Inline.inlineScan (fuel + 1) consts) consts
      (sh ++ ["end"]) s1).1 = s1 := by
    apply inlineStmtStep_assign_shadowed
    intro y hy
    rw [show tpExprVars e1 = ["buf_len", "proof_cptr"] from
      tpVars_call_two "common_uncompressed_g1" "buf_len" "proof_cptr"] at hy
    simp at hy
    rcases hy with h | h
    · subst y; exact hb'
    · subst y; exact hp'
  have hs2 : (Inline.inlineStmtStep (Inline.inlineScan (fuel + 1) consts) consts
      ((sh ++ ["end"]) ++ ["buf_len"]) s2).1 = s2 := by
    apply inlineStmtStep_expr_shadowed
    intro y hy
    rw [show tpExprVars e2 = [walk, "proof_cptr"] from
      tpVars_builtin_calldatacopy walk "proof_cptr" 128] at hy
    simp at hy
    rcases hy with h | h
    · subst y; exact shadowed_append_right (sh ++ ["end"]) ["buf_len"] walk hw'
    · subst y; exact shadowed_append_right (sh ++ ["end"]) ["buf_len"] "proof_cptr" hp'
  have hs3 : (Inline.inlineStmtStep (Inline.inlineScan (fuel + 1) consts) consts
      ((sh ++ ["end"]) ++ ["buf_len"]) s3).1 = s3 := by
    apply inlineStmtStep_assign_shadowed
    intro y hy
    rw [show tpExprVars e3 = [walk] from tpVars_builtin_add_var walk 128] at hy
    simp at hy
    rcases hy with h
    subst y
    exact shadowed_append_right (sh ++ ["end"]) ["buf_len"] walk hw'
  have hs4 : (Inline.inlineStmtStep (Inline.inlineScan (fuel + 1) consts) consts
      (((sh ++ ["end"]) ++ ["buf_len"]) ++ [walk]) s4).1 = s4 := by
    apply inlineStmtStep_assign_shadowed
    intro y hy
    rw [show tpExprVars e4 = ["proof_cptr"] from tpVars_builtin_add_var "proof_cptr" 128] at hy
    simp at hy
    rcases hy with h
    subst y
    have hp'' : Inline.shadowed ((sh ++ ["end"]) ++ ["buf_len"]) "proof_cptr" = true :=
      shadowed_append_right (sh ++ ["end"]) ["buf_len"] "proof_cptr" hp'
    exact shadowed_append_right ((sh ++ ["end"]) ++ ["buf_len"]) [walk] "proof_cptr" hp''
  -- The body scan, split three times at the threaded shadow lists.
  have hbody : (Inline.inlineScan (fuel + 1) consts (sh ++ ["end"]) [s1, s2, s3, s4]).blks =
      [s1, s2, s3, s4] := by
    rw [show [s1, s2, s3, s4] = [s1] ++ [s2, s3, s4] from rfl,
      Inline.inlineScan_append]
    rw [inlineScan_single fuel consts (sh ++ ["end"]) s1 hs1]
    rw [show [s2, s3, s4] = [s2] ++ [s3, s4] from rfl, Inline.inlineScan_append]
    rw [show (sh ++ ["end"]) ++ [s1].flatMap Inline.boundOf = (sh ++ ["end"]) ++ ["buf_len"]
      by
        show (sh ++ ["end"]) ++
          ([(Stmt.assign ["buf_len"] e1)] : List (Stmt EVM.Op)).flatMap Inline.boundOf =
            (sh ++ ["end"]) ++ ["buf_len"]
        simp [Inline.boundOf, List.flatMap_cons, List.flatMap_nil]]
    rw [inlineScan_single fuel consts ((sh ++ ["end"]) ++ ["buf_len"]) s2 hs2]
    rw [show [s3, s4] = [s3] ++ [s4] from rfl, Inline.inlineScan_append]
    rw [show ((sh ++ ["end"]) ++ ["buf_len"]) ++ [s2].flatMap Inline.boundOf =
      (sh ++ ["end"]) ++ ["buf_len"] by
        show ((sh ++ ["end"]) ++ ["buf_len"]) ++
          ([(Stmt.exprStmt e2)] : List (Stmt EVM.Op)).flatMap Inline.boundOf =
            (sh ++ ["end"]) ++ ["buf_len"]
        simp [Inline.boundOf, List.flatMap_cons, List.flatMap_nil]]
    rw [inlineScan_single fuel consts ((sh ++ ["end"]) ++ ["buf_len"]) s3 hs3]
    rw [show (((sh ++ ["end"]) ++ ["buf_len"]) ++ [s3].flatMap Inline.boundOf) =
      ((sh ++ ["end"]) ++ ["buf_len"]) ++ [walk] by
        show (((sh ++ ["end"]) ++ ["buf_len"]) ++
          ([(Stmt.assign [walk] e3)] : List (Stmt EVM.Op)).flatMap Inline.boundOf) =
            ((sh ++ ["end"]) ++ ["buf_len"]) ++ [walk]
        simp [Inline.boundOf, List.flatMap_cons, List.flatMap_nil]]
    rw [inlineScan_single fuel consts (((sh ++ ["end"]) ++ ["buf_len"]) ++ [walk]) s4 hs4]
  -- The condition, at the shadow list the init binder leaves.
  have hcond : Inline.inExpr Inline.exprFuel eCond consts (sh ++ ["end"]) = eCond := by
    apply tp_inExpr_eq_of_shadowed
    intro y hy
    rw [show tpExprVars eCond = ["proof_cptr", "end"] from
      tpVars_builtin_lt_two "proof_cptr" "end"] at hy
    simp at hy
    rcases hy with h | h
    · subst y; exact hp'
    · subst y; exact shadowed_append_self sh "end"
  -- One `inlineStep`, the singleton fold.
  show (Inline.inlineScan (fuel + 2) consts sh
    [Stmt.forLoop [initStmt] eCond [] [s1, s2, s3, s4]]).blks =
      [Stmt.forLoop [initStmt] eCond [] [s1, s2, s3, s4]]
  have hstep : (Inline.inlineScan (fuel + 2) consts sh
      [Stmt.forLoop [initStmt] eCond [] [s1, s2, s3, s4]]).blks =
      [(Inline.inlineStmtStep (Inline.inlineScan (fuel + 1) consts) consts sh
        (Stmt.forLoop [initStmt] eCond [] [s1, s2, s3, s4])).1] := rfl
  rw [hstep]
  congr 1
  have hfor : (Inline.inlineStmtStep (Inline.inlineScan (fuel + 1) consts) consts sh
      (Stmt.forLoop [initStmt] eCond [] [s1, s2, s3, s4])).1 =
      Stmt.forLoop (Inline.inlineScan (fuel + 1) consts sh [initStmt]).blks
        (Inline.inExpr Inline.exprFuel eCond consts
          (sh ++ (Inline.inlineScan (fuel + 1) consts sh [initStmt]).blks.flatMap
            Inline.boundOf))
        (Inline.inlineScan (fuel + 1) consts
          (sh ++ (Inline.inlineScan (fuel + 1) consts sh [initStmt]).blks.flatMap
            Inline.boundOf) []).blks
        (Inline.inlineScan (fuel + 1) consts
          (sh ++ (Inline.inlineScan (fuel + 1) consts sh [initStmt]).blks.flatMap
            Inline.boundOf) [s1, s2, s3, s4]).blks := rfl
  rw [hfor, hinit]
  have hbInit : ([initStmt] : List (Stmt EVM.Op)).flatMap Inline.boundOf = ["end"] := by
    show ([(Stmt.letDecl ["end"] (some eInit))] : List (Stmt EVM.Op)).flatMap
      Inline.boundOf = ["end"]
    simp [Inline.boundOf]
  rw [hbInit, hcond, hbody]
  rw [show (Inline.inlineScan (fuel + 1) consts (sh ++ ["end"]) []).blks = [] from rfl]

/-- **ROW.TP.3, THE CALL RESOLVES.** `R.scope` resolves `common_uncompressed_g1` to the
    emitted helper, with the two parameters and the single return slot. PROVED by `rfl` (the
    helper is the third `funDef` of `R.helpers`). This is the lookup the helper summary and the
    walk-loop body both start from. -/
theorem commonG1_lookup (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    ∃ decl, lookupFun (R.scope c g) "common_uncompressed_g1" = some (decl, R.scope c g) ∧
      decl.params = ["buf_len", "cptr"] ∧ decl.rets = ["ret"] := by
  exact ⟨_, rfl, rfl, rfl⟩

/-- **THE TRANSCRIPT READ STEP (a SIM.10 prerequisite).** A read whose bytes are present and
    whose repr decodes succeeds, advances the cursor by `width`, and leaves the buffer alone.
    PROVED by unfolding `Transcript.read`. -/
theorem transcript_read_ok {T : Type} (h : Midfall.Halo2.Hashable T) (t : Midfall.Halo2.Transcript)
    (repr : Bytes) (v : T)
    (hbt : bytesTake t.buffer t.pos h.width = some repr)
    (hr : h.readRepr? repr = some v) :
    ∃ t', t.read h = .ok (v, t') ∧ t'.pos = t.pos + h.width ∧ t'.buffer = t.buffer := by
  unfold Transcript.read
  rw [hbt]
  dsimp only
  rw [hr]
  exact ⟨_, rfl, rfl, rfl⟩

/-- The scalar wire in message order: the `Msg.fr` arm of `msgWire` concatenated. -/
def wireOf {p : Nat} [Fact (Nat.Prime p)] : List (Fr p) → Bytes
  | [] => Bytes.empty
  | q :: qs => frToRepr (p := p) q ++ wireOf qs

/-- The wire prepends the next scalar's repr. -/
theorem wireOf_cons {p : Nat} [Fact (Nat.Prime p)] (q : Fr p) (qs : List (Fr p)) :
    wireOf (p := p) (q :: qs) = frToRepr (p := p) q ++ wireOf (p := p) qs := rfl

/-- Reading the whole buffer is the identity. -/
theorem bytesTake_whole (b : Bytes) : bytesTake b 0 b.size = some b := by
  unfold bytesTake
  rw [ite_eq_left (by rw [Nat.zero_add] <;> omega)]
  rw [Nat.zero_add]
  have key : b.data.extract 0 (ByteArray.size b) = b.data :=
    @Array.extract_eq_self_of_le UInt8 (ByteArray.size b) b.data (Nat.le_refl _)
  rw [key]

/-- `tmSqueezeChallenge` never fails. -/
theorem tmSqueezeChallenge_run {p : Nat} [Fact (Nat.Prime p)] (t : Midfall.Halo2.Transcript) :
    ∃ x t', (Midfall.Halo2.tmSqueezeChallenge (p := p)).run t = .ok (x, t') := by
  refine ⟨(t.squeezeChallenge (p := p)).1, (t.squeezeChallenge (p := p)).2, ?_⟩
  unfold Midfall.Halo2.tmSqueezeChallenge
  simp only [StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, bind, Except.bind,
    pure, Except.pure]

/-- The squeeze's run, with the resulting state named. -/
theorem tmSqueezeChallenge_run_eq {p : Nat} [Fact (Nat.Prime p)]
    (t : Midfall.Halo2.Transcript) :
    (Midfall.Halo2.tmSqueezeChallenge (p := p)).run t =
      .ok ((t.squeezeChallenge (p := p)).1, (t.squeezeChallenge (p := p)).2) := by
  unfold Midfall.Halo2.tmSqueezeChallenge
  simp only [StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, bind, Except.bind,
    pure, Except.pure]

/-- `squeeze` only rewrites `state`: the cursor is untouched. -/
theorem squeeze_pos (t : Midfall.Halo2.Transcript) : t.squeeze.2.pos = t.pos := by
  unfold Transcript.squeeze
  rfl

/-- `squeeze` only rewrites `state`: the buffer is untouched. -/
theorem squeeze_buffer (t : Midfall.Halo2.Transcript) : t.squeeze.2.buffer = t.buffer := by
  unfold Transcript.squeeze
  rfl

/-- A squeezed challenge leaves the cursor alone. -/
theorem squeezeChallenge_pos {p : Nat} [Fact (Nat.Prime p)] (t : Midfall.Halo2.Transcript) :
    (t.squeezeChallenge (p := p)).2.pos = t.pos := by
  unfold Transcript.squeezeChallenge
  exact squeeze_pos t

/-- A squeezed challenge leaves the buffer alone. -/
theorem squeezeChallenge_buffer {p : Nat} [Fact (Nat.Prime p)] (t : Midfall.Halo2.Transcript) :
    (t.squeezeChallenge (p := p)).2.buffer = t.buffer := by
  unfold Transcript.squeezeChallenge
  exact squeeze_buffer t

/-- The squeeze never fails and moves neither the cursor nor the buffer. -/
theorem tmSqueezeChallenge_run_spec {p : Nat} [Fact (Nat.Prime p)]
    (t : Midfall.Halo2.Transcript) :
    ∃ x t', (Midfall.Halo2.tmSqueezeChallenge (p := p)).run t = .ok (x, t') ∧
      t'.pos = t.pos ∧ t'.buffer = t.buffer := by
  refine ⟨(t.squeezeChallenge (p := p)).1, (t.squeezeChallenge (p := p)).2,
    tmSqueezeChallenge_run_eq t, squeezeChallenge_pos t, squeezeChallenge_buffer t⟩

/-- `tmRead.run` is exactly the underlying transcript read. -/
theorem tmRead_run_eq {T : Type} (h : Midfall.Halo2.Hashable T) (t : Midfall.Halo2.Transcript) :
    (Midfall.Halo2.tmRead h).run t = t.read h := by
  unfold Midfall.Halo2.tmRead
  simp only [StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.set, StateT.pure, bind,
    Except.bind, pure, Except.pure]
  cases t.read h <;> rfl

/-- `tmRead` succeeds from a present, decodable repr. -/
theorem tmRead_run_ok {T : Type} (h : Midfall.Halo2.Hashable T) (t : Midfall.Halo2.Transcript)
    (repr : Bytes) (v : T)
    (hbt : bytesTake t.buffer t.pos h.width = some repr)
    (hr : h.readRepr? repr = some v) :
    ∃ t', (Midfall.Halo2.tmRead h).run t = .ok (v, t') ∧ t'.pos = t.pos + h.width ∧
      t'.buffer = t.buffer := by
  obtain ⟨t', hread, hpos, hbuf⟩ := transcript_read_ok h t repr v hbt hr
  exact ⟨t', (tmRead_run_eq h t).trans hread, hpos, hbuf⟩

/-- The Fr hashable's reader is `frOfRepr?` (stated at a variable byte string so the
    projection peels without reducing a concrete `frToRepr`). -/
theorem hashableFr_readRepr? {p : Nat} [Fact (Nat.Prime p)] (b : Bytes) :
    (Midfall.Halo2.hashableFr (p := p)).readRepr? b = frOfRepr? (p := p) b := rfl

/-- The G1 hashable's width is the compressed width. -/
theorem hashableG1_width {G₁ : Type} (g1 : G1Codec G₁) :
    (Midfall.Halo2.hashableG1 g1).width = g1CompressedWidth := rfl

/-- The Fr hashable's width is 32. -/
theorem hashableFr_width {p : Nat} [Fact (Nat.Prime p)] :
    (Midfall.Halo2.hashableFr (p := p)).width = 32 := rfl

/-- The G1 hashable's reader is the codec's `ofCompressed?`. -/
theorem hashableG1_readRepr? {G₁ : Type} (g1 : G1Codec G₁) (b : Bytes) :
    (Midfall.Halo2.hashableG1 g1).readRepr? b = g1.ofCompressed? b := rfl

/-- One G1 read from the exact wire tail. -/
theorem tmRead_g1_run {G₁ : Type} [Group G₁] (g1 : G1Codec G₁)
    (t : Midfall.Halo2.Transcript) (pref rest : Bytes) (Q : G₁)
    (hbuf : t.buffer = pref ++ g1.toCompressed Q ++ rest) (hpos : t.pos = pref.size)
    (henc : ∀ Q, g1.ofCompressed? (g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (g1.toCompressed Q).size = g1CompressedWidth) :
    ∃ t', (Midfall.Halo2.tmRead (hashableG1 g1)).run t = .ok (Q, t') ∧
      t'.pos = pref.size + g1CompressedWidth ∧ t'.buffer = t.buffer := by
  have hbt : bytesTake t.buffer t.pos g1CompressedWidth = some (g1.toCompressed Q) := by
    rw [hbuf, hpos, ← Nat.add_zero (ByteArray.size pref), ByteArray.append_assoc]
    rw [bytesTake_append_right pref (g1.toCompressed Q ++ rest) 0 g1CompressedWidth (by
      rw [ByteArray.size_append, hwidth]; omega)]
    rw [bytesTake_append_left (g1.toCompressed Q) rest 0 g1CompressedWidth (by rw [hwidth]; omega)]
    rw [← hwidth, bytesTake_whole]
  obtain ⟨t', hrun, hpos', hbuf'⟩ :=
    tmRead_run_ok (hashableG1 g1) t (g1.toCompressed Q) Q hbt
      (by rw [hashableG1_readRepr?]; exact henc Q)
  exact ⟨t', hrun, by rw [hpos', hashableG1_width, hpos], hbuf'⟩

/-- The scalar wire's length: 32 bytes per scalar. -/
theorem wireOf_size {p : Nat} [Fact (Nat.Prime p)] (qs : List (Fr p)) :
    (wireOf (p := p) qs).size = 32 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      rw [wireOf_cons, ByteArray.size_append, frToRepr_size, ih, List.length_cons]
      omega

/-- The scalar read run: a list of indices of the same length as `qs` reads `wireOf qs`
    from the cursor forward, leaving the buffer alone. -/
theorem tmRead_list_run {p : Nat} [Fact (Nat.Prime p)] :
    ∀ (idx : List Nat) (t : Midfall.Halo2.Transcript) (pref : Bytes) (qs : List (Fr p))
      (rest : Bytes), idx.length = qs.length →
      t.buffer = pref ++ wireOf (p := p) qs ++ rest →
      t.pos = pref.size → p ≤ 2 ^ 256 →
      ∃ t', (idx.mapM (fun _ => Midfall.Halo2.tmRead (Midfall.Halo2.hashableFr (p := p)))).run t
          = .ok (qs, t') ∧ t'.pos = pref.size + 32 * qs.length ∧ t'.buffer = t.buffer := by
  intro idx
  induction idx with
  | nil =>
      intro t pref qs rest hlen hbuf hpos hp
      have hqs : qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst hqs
      refine ⟨t, ?_, ?_, rfl⟩
      · rfl
      · simp [hpos]
  | cons i idx ih =>
      intro t pref qs rest hlen hbuf hpos hp
      obtain ⟨q, qs', hqs⟩ := List.exists_cons_of_length_pos (by rw [← hlen]; simp)
      subst hqs
      have hsize : (frToRepr (p := p) q).size = 32 := frToRepr_size q
      have hbuf' : t.buffer = pref ++ ((frToRepr (p := p) q) ++ (wireOf (p := p) qs' ++ rest)) := by
        rw [hbuf, wireOf_cons]
        simp only [ByteArray.append_assoc]
      have hbt : bytesTake t.buffer t.pos 32 = some (frToRepr (p := p) q) := by
        rw [hbuf', hpos, ← Nat.add_zero (ByteArray.size pref)]
        rw [bytesTake_append_right pref ((frToRepr (p := p) q) ++
          (wireOf (p := p) qs' ++ rest)) 0 32 (by
            rw [ByteArray.size_append, hsize]; omega)]
        rw [bytesTake_append_left (frToRepr (p := p) q)
          (wireOf (p := p) qs' ++ rest) 0 32 (by rw [hsize])]
        rw [← hsize, bytesTake_whole]
      obtain ⟨t1, hrun1, hpos1, hbuf1⟩ :=
        tmRead_run_ok (Midfall.Halo2.hashableFr (p := p)) t (frToRepr (p := p) q) q hbt
          (by rw [hashableFr_readRepr?]; exact frOfRepr_frToRepr hp q)
      have hbuf1' : t1.buffer =
          (pref ++ frToRepr (p := p) q) ++ wireOf (p := p) qs' ++ rest := by
        rw [hbuf1, hbuf']
        simp only [ByteArray.append_assoc]
      have hpos1' : t1.pos = (pref ++ frToRepr (p := p) q).size := by
        rw [hpos1, hpos, hashableFr_width, ByteArray.size_append, hsize]
      obtain ⟨t2, hrun2, hpos2, hbuf2⟩ :=
        ih t1 (pref ++ frToRepr (p := p) q) qs' rest (by simpa using hlen) hbuf1' hpos1' hp
      refine ⟨t2, ?_, ?_, hbuf2.trans hbuf1⟩
      · simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
        rw [hrun1]
        simp only [Except.bind, Except.pure, bind, pure]
        rw [hrun2]
      · rw [hpos2, ByteArray.size_append, hsize]
        simp only [List.length_cons]
        omega

/-- **THE DECODE SLOT SHAPE.** `decodeSlots` returns messages whose slots are exactly the
    layout slots it walked: the calldata decoder and the transcript schedule read the same
    list. This is the shape half of `readScheduleAgrees` at the `decodeCalldata` site. -/
theorem decodeSlots_map_slot {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁)
    (cd : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat) (ms : List (Msg (Fr p) G₁)) (cur' : Nat),
      decodeSlots (p := p) c cd slots cur = some (ms, cur') → ms.map Msg.slot = slots := by
  intro slots
  induction slots with
  | nil =>
      intro cur ms cur' h
      simp only [decodeSlots, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
  | cons s rest ih =>
      intro cur ms cur' h
      cases s with
      | g1 =>
          unfold decodeSlots at h
          simp only [guard] at h
          by_cases hg : g1WordsOk cd cur = true
          · rw [ite_eq_left hg] at h
            simp at h
            rw [Option.bind_eq_some_iff] at h
            obtain ⟨b, _hb, h⟩ := h
            rw [Option.bind_eq_some_iff] at h
            obtain ⟨Q, _hq, h⟩ := h
            rw [Option.bind_eq_some_iff] at h
            obtain ⟨⟨ms0, cur0⟩, hrec, hpair⟩ := h
            simp only [Option.some.injEq, Prod.mk.injEq] at hpair
            obtain ⟨rfl, rfl⟩ := hpair
            simp only [List.map_cons]
            rw [ih (cur + g1EipWidth) ms0 cur0 hrec]
            rfl
          · rw [ite_eq_right (by simpa using hg)] at h
            cases h
      | fr =>
          unfold decodeSlots at h
          simp only [guard] at h
          by_cases hlt : (cdWord cd cur).toNat < p
          · rw [ite_eq_left hlt] at h
            simp at h
            rw [Option.bind_eq_some_iff] at h
            obtain ⟨⟨ms0, cur0⟩, hrec, hpair⟩ := h
            simp only [Option.some.injEq, Prod.mk.injEq] at hpair
            obtain ⟨rfl, rfl⟩ := hpair
            simp only [List.map_cons]
            rw [ih (cur + 32) ms0 cur0 hrec]
            rfl
          · rw [ite_eq_right (by simpa using hlt)] at h
            cases h

/-- `assertEmpty` succeeds exactly when the cursor is at the buffer's end. -/
theorem assertEmpty_run_ok (t : Midfall.Halo2.Transcript) (h : t.pos = t.buffer.size) :
    t.assertEmpty = .ok () := by
  unfold Transcript.assertEmpty
  rw [← h]
  simp

/-- **THE PCS READ RUN (SIM.10 obligation 2).** From the exact wire tail — the fCom
    compression, the q-eval scalars, then the pi compression — `pcsReads.run` succeeds,
    returns those values, and leaves the cursor at the buffer's end. -/
theorem pcsReads_run_ok {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features) (nSets : Nat)
    (t : Midfall.Halo2.Transcript) (pref : Bytes) (fCom pi : G₁) (qs : List (Fr p))
    (hlen : qs.length = nSets)
    (hbuf : t.buffer = pref ++ g1.toCompressed fCom ++
      wireOf (p := p) qs ++ g1.toCompressed pi)
    (hpos : t.pos = pref.size)
    (henc : ∀ Q, g1.ofCompressed? (g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (g1.toCompressed Q).size = g1CompressedWidth)
    (hp : p ≤ 2 ^ 256) :
    ∃ r t', (pcsReads g1 fc feat nSets).run t = .ok (r, t') ∧ r.fCom = fCom ∧ r.pi = pi ∧
      r.qEvalsOnX3 = qs ∧ t'.pos = t.buffer.size ∧ t'.buffer = t.buffer := by
  unfold pcsReads
  simp only [StateT.run_bind, StateT.run_pure]
  -- x1
  obtain ⟨x1, t1, h1, hp1, hb1⟩ := tmSqueezeChallenge_run_spec (p := p) t
  rw [h1]
  simp only [Except.bind, Except.pure, bind, pure]
  -- x2
  obtain ⟨x2, t2, h2, hp2, hb2⟩ := tmSqueezeChallenge_run_spec (p := p) t1
  rw [h2]
  simp only [Except.bind, Except.pure, bind, pure]
  -- fCom
  obtain ⟨t3, h3, hp3, hb3⟩ :=
    tmRead_g1_run g1 t2 pref (wireOf (p := p) qs ++ g1.toCompressed pi) fCom
      (by rw [hb2, hb1, hbuf, ByteArray.append_assoc])
      (by rw [hp2, hp1]; exact hpos) henc hwidth
  rw [h3]
  simp only [Except.bind, Except.pure, bind, pure]
  -- x3raw
  obtain ⟨x3raw, t4, h4, hp4, hb4⟩ := tmSqueezeChallenge_run_spec (p := p) t3
  rw [h4]
  simp only [Except.bind, Except.pure, bind, pure]
  -- q evals
  obtain ⟨t5, h5, hp5, hb5⟩ :=
    tmRead_list_run (p := p) (List.range nSets) t4 (pref ++ g1.toCompressed fCom) qs
      (g1.toCompressed pi) (by simp [hlen])
      (by rw [hb4, hb3, hb2, hb1, hbuf])
      (by rw [hp4, hp3, ByteArray.size_append, hwidth fCom]) hp
  rw [h5]
  simp only [Except.bind, Except.pure, bind, pure]
  -- x4
  obtain ⟨x4, t6, h6, hp6, hb6⟩ := tmSqueezeChallenge_run_spec (p := p) t5
  rw [h6]
  simp only [Except.bind, Except.pure, bind, pure]
  -- pi
  obtain ⟨t7, h7, hp7, hb7⟩ :=
    tmRead_g1_run g1 t6 ((pref ++ g1.toCompressed fCom) ++ wireOf (p := p) qs)
      Bytes.empty pi
      (by rw [hb6, hb5, hb4, hb3, hb2, hb1, hbuf]; exact ByteArray.append_empty.symm)
      (by simp only [hp6, hp5, ByteArray.size_append, wireOf_size]) henc hwidth
  rw [h7]
  simp only [Except.bind, Except.pure, bind, pure]
  refine ⟨_, t7, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [hp7, hbuf]
    simp only [ByteArray.size_append, hwidth fCom, hwidth pi, wireOf_size, hlen]
  · rw [hb7, hb6, hb5, hb4, hb3, hb2, hb1]

/-- The wire encoding of a message list, in message order (the fold `transcriptOf` runs). -/
def wireMsgs {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) : List (Msg (Fr p) G₁) → Bytes
  | [] => Bytes.empty
  | m :: ms => msgWire E m ++ wireMsgs E ms

theorem bytes_append_empty_local (b : Bytes) : b ++ Bytes.empty = b := ByteArray.append_empty
theorem bytes_empty_append_local (b : Bytes) : Bytes.empty ++ b = b := ByteArray.empty_append

theorem foldl_wireMsgs_append {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (ms : List (Msg (Fr p) G₁)) (acc : Bytes) :
    ms.foldl (fun acc m => acc ++ msgWire E m) acc =
      acc ++ ms.foldl (fun acc m => acc ++ msgWire E m) Bytes.empty := by
  induction ms generalizing acc with
  | nil => rw [List.foldl_nil, List.foldl_nil, bytes_append_empty_local]
  | cons m ms ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (acc ++ msgWire E m),
        ih (Bytes.empty ++ msgWire E m), bytes_empty_append_local, ByteArray.append_assoc]

/-- `wireMsgs` is the body `transcriptOf` folds. -/
theorem wireMsgs_eq_fold {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (ms : List (Msg (Fr p) G₁)) :
    wireMsgs E ms = ms.foldl (init := Bytes.empty) (fun acc m => acc ++ msgWire E m) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      rw [wireMsgs, List.foldl_cons, foldl_wireMsgs_append, ih, bytes_empty_append_local]

theorem wireMsgs_cons {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (m : Msg (Fr p) G₁) (ms : List (Msg (Fr p) G₁)) :
    wireMsgs E (m :: ms) = msgWire E m ++ wireMsgs E ms := rfl

theorem wireMsgs_size {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (ms : List (Msg (Fr p) G₁)) :
    (wireMsgs E ms).size = (ms.map fun m => (msgWire E m).size).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      rw [wireMsgs_cons, ByteArray.size_append, ih, List.map_cons, List.sum_cons]

/-- Read one message and discard its value (only consumption matters). -/
def tmReadMsg {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) : Msg (Fr p) G₁ → TranscriptM Unit
  | .g1 _ => (tmRead (hashableG1 E.g1) : TranscriptM G₁) >>= fun _ => pure ()
  | .fr _ => (tmRead (hashableFr (p := p)) : TranscriptM (Fr p)) >>= fun _ => pure ()

/-- One message read from the wired tail. -/
theorem tmRead_msg_run {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (t : Midfall.Halo2.Transcript) (pref : Bytes)
    (m : Msg (Fr p) G₁) (rest : Bytes)
    (hbuf : t.buffer = pref ++ msgWire E m ++ rest) (hpos : t.pos = pref.size)
    (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) :
    ∃ t', (tmReadMsg E m).run t = .ok ((), t') ∧
      t'.pos = pref.size + (msgWire E m).size ∧ t'.buffer = t.buffer := by
  cases m with
  | g1 Q =>
      obtain ⟨t', hrun, hpos', hbuf'⟩ :=
        tmRead_g1_run E.g1 t pref rest Q hbuf hpos henc hwidth
      refine ⟨t', ?_, ?_, hbuf'⟩
      · show ((tmRead (hashableG1 E.g1)) >>= fun _ => pure ()).run t = .ok ((), t')
        simp only [StateT.run_bind, StateT.run_pure]
        rw [hrun]
        simp only [Except.bind, Except.pure, bind, pure]
      · rw [hpos']
        show pref.size + g1CompressedWidth = pref.size + (msgWire E (Msg.g1 Q)).size
        simp only [msgWire]
        rw [hwidth]
  | fr x =>
      have hbt : bytesTake t.buffer t.pos 32 = some (frToRepr (p := p) x) := by
        rw [hbuf, hpos, ← Nat.add_zero (ByteArray.size pref), ByteArray.append_assoc]
        simp only [msgWire]
        rw [bytesTake_append_right pref (frToRepr (p := p) x ++ rest) 0 32 (by
          rw [ByteArray.size_append, frToRepr_size]; omega)]
        rw [bytesTake_append_left (frToRepr (p := p) x) rest 0 32 (by
          rw [frToRepr_size])]
        rw [← frToRepr_size x, bytesTake_whole]
      obtain ⟨t', hrun, hpos', hbuf'⟩ :=
        tmRead_run_ok (hashableFr (p := p)) t (frToRepr (p := p) x) x hbt
          (by rw [hashableFr_readRepr?]; exact frOfRepr_frToRepr hp x)
      refine ⟨t', ?_, ?_, hbuf'⟩
      · show ((tmRead (hashableFr (p := p))) >>= fun _ => pure ()).run t = .ok ((), t')
        simp only [StateT.run_bind, StateT.run_pure]
        rw [hrun]
        simp only [Except.bind, Except.pure, bind, pure]
      · rw [hpos', hashableFr_width, hpos]
        show pref.size + 32 = pref.size + (msgWire E (Msg.fr x)).size
        simp only [msgWire]
        rw [frToRepr_size]

/-- **THE MESSAGE-WIRE ENGINE.** Reading a decoded message list one message at a time from
    the exact wired tail succeeds, consumes the list in order, advances the cursor by the
    wire length, and leaves the buffer alone. -/
theorem tmRead_msgs_run {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (ms : List (Msg (Fr p) G₁)) (t : Midfall.Halo2.Transcript) (pref rest : Bytes),
      t.buffer = pref ++ wireMsgs E ms ++ rest →
      t.pos = pref.size → p ≤ 2 ^ 256 →
      (∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q) →
      (∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) →
      ∃ (us : List Unit) (t' : Midfall.Halo2.Transcript),
        (ms.mapM (tmReadMsg E)).run t = .ok (us, t') ∧ us.length = ms.length ∧
        t'.pos = pref.size + (ms.map fun m => (msgWire E m).size).sum ∧
        t'.buffer = t.buffer := by
  intro ms
  induction ms with
  | nil =>
      intro t pref rest hbuf hpos hp henc hwidth
      refine ⟨[], t, ?_, ?_, ?_, rfl⟩
      · rfl
      · rfl
      · rw [hpos, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons m ms ih =>
      intro t pref rest hbuf hpos hp henc hwidth
      have hbuf' : t.buffer = pref ++ msgWire E m ++ (wireMsgs E ms ++ rest) := by
        rw [hbuf, wireMsgs_cons]
        simp only [ByteArray.append_assoc]
      obtain ⟨t1, hrun1, hpos1, hbuf1⟩ :=
        tmRead_msg_run E t pref m (wireMsgs E ms ++ rest) hbuf' hpos hp henc hwidth
      have hbuf1' : t1.buffer = (pref ++ msgWire E m) ++ wireMsgs E ms ++ rest := by
        rw [hbuf1, hbuf']
        simp only [ByteArray.append_assoc]
      have hpos1' : t1.pos = (pref ++ msgWire E m).size := by
        rw [hpos1, ByteArray.size_append]
      obtain ⟨us, t2, hrun2, hlen, hpos2, hbuf2⟩ :=
        ih t1 (pref ++ msgWire E m) rest hbuf1' hpos1' hp henc hwidth
      refine ⟨() :: us, t2, ?_, ?_, ?_, hbuf2.trans hbuf1⟩
      · simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
        rw [hrun1]
        simp only [Except.bind, Except.pure, bind, pure]
        rw [hrun2]
      · simp only [List.length_cons, hlen]
      · rw [hpos2, ByteArray.size_append, List.map_cons, List.sum_cons]
        omega

/-- `tmReadN.run` is the underlying `Transcript.readN`. -/
theorem tmReadN_run_eq {T : Type} (h : Midfall.Halo2.Hashable T) (n : Nat)
    (t : Midfall.Halo2.Transcript) :
    (Midfall.Halo2.tmReadN h n).run t = t.readN h n := by
  unfold Midfall.Halo2.tmReadN
  simp only [StateT.run, StateT.bind, StateT.get, StateT.set, StateT.lift, StateT.pure,
    Bind.bind, Pure.pure, Except.bind, Except.map, Except.pure]
  cases hr : t.readN h n with
  | error e => simp only [hr]
  | ok p => cases p with | mk vs t2 => simp only [hr]


/-- `readN.go` appends exactly `n` elements (`EndToEndAlgebra`'s proof, ported below `Totality`). -/
theorem readN_go_size {T : Type} (h : Midfall.Halo2.Hashable T) :
    ∀ (n : Nat) (t : Transcript) (acc : Array T) (acc' : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (acc', t') → acc'.size = acc.size + n := by
  intro n
  induction n with
  | zero =>
      intro t acc acc' t' hr
      rw [Transcript.readN.go.eq_1] at hr
      cases hr
      simp
  | succ m ih =>
      intro t acc acc' t' hr
      rw [Transcript.readN.go.eq_2] at hr
      simp only [Bind.bind, Except.bind] at hr
      split at hr
      · cases hr
      · rename_i x hx
        obtain ⟨v, t2⟩ := x
        have := ih t2 (acc.push v) acc' t' hr
        simp only [Array.size_push] at this
        omega

theorem readN_size {T : Type} (h : Midfall.Halo2.Hashable T) (t : Transcript) (n : Nat)
    {acc : Array T} {t' : Transcript} (hr : t.readN h n = .ok (acc, t')) :
    acc.size = n := by
  unfold Transcript.readN at hr
  have := readN_go_size h n t #[] acc t' hr
  simpa using this

/-- A successful `tmReadN` returns exactly `n` values. -/
theorem tmReadN_size {T : Type} (h : Midfall.Halo2.Hashable T) (n : Nat)
    {s : Transcript} {acc : Array T} {t' : Transcript}
    (hr : (Midfall.Halo2.tmReadN h n).run s = .ok (acc, t')) : acc.size = n := by
  rw [tmReadN_run_eq] at hr
  exact readN_size h s n hr

/-- `readN` of a list of G1 points from the exact wired tail. -/
theorem readN_g1_wire {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (n : Nat) (acc : Array G₁) (t : Midfall.Halo2.Transcript) (pref : Bytes)
      (qs : List G₁) (rest : Bytes),
      qs.length = n →
      t.buffer = pref ++ wireMsgs E (qs.map Msg.g1) ++ rest → t.pos = pref.size →
      p ≤ 2 ^ 256 →
      (∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q) →
      (∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) →
      ∃ (arr : Array G₁) (t' : Midfall.Halo2.Transcript),
        Midfall.Halo2.Transcript.readN.go (hashableG1 E.g1) t acc n = .ok (arr, t') ∧
        t'.pos = pref.size +
          (qs.map fun Q => (msgWire E (Msg.g1 Q)).size).sum ∧ t'.buffer = t.buffer := by
  intro n
  induction n with
  | zero =>
      intro acc t pref qs rest hlen hbuf hpos hp henc hwidth
      have hqs : qs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hqs
      refine ⟨acc, t, ?_, ?_, rfl⟩
      · simp only [Midfall.Halo2.Transcript.readN.go]
      · simp [hpos]
  | succ n ih =>
      intro acc t pref qs rest hlen hbuf hpos hp henc hwidth
      obtain ⟨Q, qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      have hsize : (msgWire E (Msg.g1 Q)).size = g1CompressedWidth := by
        show (E.g1.toCompressed Q).size = g1CompressedWidth
        exact hwidth Q
      have hbuf' : t.buffer = pref ++ msgWire E (Msg.g1 Q) ++
          (wireMsgs E (qs'.map Msg.g1) ++ rest) := by
        rw [hbuf, List.map_cons, wireMsgs_cons]
        simp only [ByteArray.append_assoc]
      have hbt : bytesTake t.buffer t.pos g1CompressedWidth = some (E.g1.toCompressed Q) := by
        rw [hbuf', hpos, ← Nat.add_zero (ByteArray.size pref), ByteArray.append_assoc]
        simp only [msgWire]
        rw [bytesTake_append_right pref (E.g1.toCompressed Q ++
          (wireMsgs E (qs'.map Msg.g1) ++ rest)) 0 g1CompressedWidth (by
            rw [ByteArray.size_append, hwidth]; omega)]
        rw [bytesTake_append_left (E.g1.toCompressed Q)
          (wireMsgs E (qs'.map Msg.g1) ++ rest) 0 g1CompressedWidth (by rw [hwidth]; omega)]
        rw [← hwidth Q, bytesTake_whole]
      obtain ⟨t1, hread, hpos1, hbuf1⟩ :=
        transcript_read_ok (hashableG1 E.g1) t (E.g1.toCompressed Q) Q hbt
          (by rw [hashableG1_readRepr?]; exact henc Q)
      have hpos1' : t1.pos = (pref ++ msgWire E (Msg.g1 Q)).size := by
        rw [hpos1, hpos, hashableG1_width, ByteArray.size_append, hsize]
      have hbuf1' : t1.buffer = (pref ++ msgWire E (Msg.g1 Q)) ++
          wireMsgs E (qs'.map Msg.g1) ++ rest := by
        rw [hbuf1, hbuf']
        simp only [ByteArray.append_assoc]
      obtain ⟨arr, t2, hrun2, hpos2, hbuf2⟩ :=
        ih (acc.push Q) t1 (pref ++ msgWire E (Msg.g1 Q)) qs' rest
          (by simpa using hlen) hbuf1' hpos1' hp henc hwidth
      refine ⟨arr, t2, ?_, ?_, hbuf2.trans hbuf1⟩
      · simp only [Midfall.Halo2.Transcript.readN.go]
        rw [hread]
        exact hrun2
      · rw [hpos2, ByteArray.size_append, List.map_cons, List.sum_cons]
        omega

/-- `readN` of a list of scalars from the exact wired tail. -/
theorem readN_fr_wire {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (n : Nat) (acc : Array (Fr p)) (t : Midfall.Halo2.Transcript) (pref : Bytes)
      (xs : List (Fr p)) (rest : Bytes),
      xs.length = n →
      t.buffer = pref ++ wireMsgs E (xs.map Msg.fr) ++ rest → t.pos = pref.size →
      p ≤ 2 ^ 256 →
      ∃ (arr : Array (Fr p)) (t' : Midfall.Halo2.Transcript),
        Midfall.Halo2.Transcript.readN.go (hashableFr (p := p)) t acc n = .ok (arr, t') ∧
        t'.pos = pref.size +
          (xs.map fun x => (msgWire E (Msg.fr x)).size).sum ∧ t'.buffer = t.buffer := by
  intro n
  induction n with
  | zero =>
      intro acc t pref xs rest hlen hbuf hpos hp
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hxs
      refine ⟨acc, t, ?_, ?_, rfl⟩
      · simp only [Midfall.Halo2.Transcript.readN.go]
      · simp [hpos]
  | succ n ih =>
      intro acc t pref xs rest hlen hbuf hpos hp
      obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      have hsize : (msgWire E (Msg.fr x)).size = 32 := by
        show (frToRepr (p := p) x).size = 32
        exact frToRepr_size x
      have hbuf' : t.buffer = pref ++ msgWire E (Msg.fr x) ++
          (wireMsgs E (xs'.map Msg.fr) ++ rest) := by
        rw [hbuf, List.map_cons, wireMsgs_cons]
        simp only [ByteArray.append_assoc]
      have hbt : bytesTake t.buffer t.pos 32 = some (frToRepr (p := p) x) := by
        rw [hbuf', hpos, ← Nat.add_zero (ByteArray.size pref), ByteArray.append_assoc]
        simp only [msgWire]
        rw [bytesTake_append_right pref (frToRepr (p := p) x ++
          (wireMsgs E (xs'.map Msg.fr) ++ rest)) 0 32 (by
            rw [ByteArray.size_append, frToRepr_size]; omega)]
        rw [bytesTake_append_left (frToRepr (p := p) x)
          (wireMsgs E (xs'.map Msg.fr) ++ rest) 0 32 (by rw [frToRepr_size])]
        rw [← frToRepr_size x, bytesTake_whole]
      obtain ⟨t1, hread, hpos1, hbuf1⟩ :=
        transcript_read_ok (hashableFr (p := p)) t (frToRepr (p := p) x) x hbt
          (by rw [hashableFr_readRepr?]; exact frOfRepr_frToRepr hp x)
      have hpos1' : t1.pos = (pref ++ msgWire E (Msg.fr x)).size := by
        rw [hpos1, hpos, hashableFr_width, ByteArray.size_append, hsize]
      have hbuf1' : t1.buffer = (pref ++ msgWire E (Msg.fr x)) ++
          wireMsgs E (xs'.map Msg.fr) ++ rest := by
        rw [hbuf1, hbuf']
        simp only [ByteArray.append_assoc]
      obtain ⟨arr, t2, hrun2, hpos2, hbuf2⟩ :=
        ih (acc.push x) t1 (pref ++ msgWire E (Msg.fr x)) xs' rest
          (by simpa using hlen) hbuf1' hpos1' hp
      refine ⟨arr, t2, ?_, ?_, hbuf2.trans hbuf1⟩
      · simp only [Midfall.Halo2.Transcript.readN.go]
        rw [hread]
        exact hrun2
      · rw [hpos2, ByteArray.size_append, List.map_cons, List.sum_cons]
        omega

/-- `tmReadN` of G1 points: the group reader of `parseTrace`'s advice/lookup/perm/trash loops. -/
theorem tmReadN_g1_wire {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (t : Midfall.Halo2.Transcript)
    (pref : Bytes) (qs : List G₁) (rest : Bytes) (hlen : qs.length = n)
    (hbuf : t.buffer = pref ++ wireMsgs E (qs.map Msg.g1) ++ rest)
    (hpos : t.pos = pref.size) (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) :
    ∃ (arr : Array G₁) (t' : Midfall.Halo2.Transcript),
      (tmReadN (hashableG1 E.g1) n).run t = .ok (arr, t') ∧
      t'.pos = pref.size + (qs.map fun Q => (msgWire E (Msg.g1 Q)).size).sum ∧
      t'.buffer = t.buffer := by
  obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
    readN_g1_wire E n #[] t pref qs rest hlen hbuf hpos hp henc hwidth
  refine ⟨arr, t', ?_, hpos', hbuf'⟩
  rw [tmReadN_run_eq]
  simpa only [Midfall.Halo2.Transcript.readN] using hrun

/-- `tmReadN` of scalars: the group reader of `readAlgebra`'s eval blocks. -/
theorem tmReadN_fr_wire {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (t : Midfall.Halo2.Transcript)
    (pref : Bytes) (xs : List (Fr p)) (rest : Bytes) (hlen : xs.length = n)
    (hbuf : t.buffer = pref ++ wireMsgs E (xs.map Msg.fr) ++ rest)
    (hpos : t.pos = pref.size) (hp : p ≤ 2 ^ 256) :
    ∃ (arr : Array (Fr p)) (t' : Midfall.Halo2.Transcript),
      (tmReadN (hashableFr (p := p)) n).run t = .ok (arr, t') ∧
      t'.pos = pref.size + (xs.map fun x => (msgWire E (Msg.fr x)).size).sum ∧
      t'.buffer = t.buffer := by
  obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
    readN_fr_wire E n #[] t pref xs rest hlen hbuf hpos hp
  refine ⟨arr, t', ?_, hpos', hbuf'⟩
  rw [tmReadN_run_eq]
  simpa only [Midfall.Halo2.Transcript.readN] using hrun

/-- Splitting the decoded messages at a slot prefix (the segment algebra of the schedule). -/
theorem exists_split_of_slot_prefix {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type}
    (ms : List (Msg (Fr p) G₁)) :
    ∀ (pre rest : List WireSlot), ms.map Msg.slot = pre ++ rest →
      ∃ ms₁ ms₂, ms = ms₁ ++ ms₂ ∧ ms₁.map Msg.slot = pre ∧ ms₂.map Msg.slot = rest := by
  induction ms with
  | nil =>
      intro pre rest h
      cases pre with
      | nil => simp only [List.nil_append] at h; subst h; exact ⟨[], [], rfl, rfl, rfl⟩
      | cons s pre => simp at h
  | cons m ms ih =>
      intro pre rest h
      cases pre with
      | nil =>
          simp only [List.nil_append] at h
          exact ⟨[], m :: ms, rfl, rfl, h⟩
      | cons s pre =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          obtain ⟨hms, hrest⟩ := h
          obtain ⟨ms₁, ms₂, hsplit, hpre, hpost⟩ := ih pre rest hrest
          refine ⟨m :: ms₁, ms₂, by rw [hsplit]; rfl, ?_, hpost⟩
          simp only [List.map_cons, hms, hpre]

/-- A message list all of whose slots are `g1` is a list of G1 messages. -/
theorem eq_map_g1_of_slots {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type} :
    ∀ (l : List (Msg (Fr p) G₁)) (n : Nat),
      l.map Msg.slot = List.replicate n WireSlot.g1 →
        ∃ Qs : List G₁, l = Qs.map Msg.g1 ∧ Qs.length = n := by
  intro l
  induction l with
  | nil =>
      intro n h
      cases n with
      | zero => exact ⟨[], rfl, rfl⟩
      | succ n => simp at h
  | cons m ms ih =>
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
          obtain ⟨hm, hrest⟩ := h
          cases m with
          | g1 Q =>
              obtain ⟨Qs, hms, hlen⟩ := ih n hrest
              exact ⟨Q :: Qs, by simp [hms], by simp [hlen]⟩
          | fr x => simp [Msg.slot] at hm
/-- A message list all of whose slots are `fr` is a list of scalars. -/
theorem eq_map_fr_of_slots {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type} :
    ∀ (l : List (Msg (Fr p) G₁)) (n : Nat),
      l.map Msg.slot = List.replicate n WireSlot.fr →
        ∃ xs : List (Fr p), l = xs.map Msg.fr ∧ xs.length = n := by
  intro l
  induction l with
  | nil =>
      intro n h
      cases n with
      | zero => exact ⟨[], rfl, rfl⟩
      | succ n => simp at h
  | cons m ms ih =>
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
          obtain ⟨hm, hrest⟩ := h
          cases m with
          | g1 Q => simp [Msg.slot] at hm
          | fr x =>
              obtain ⟨xs, hms, hlen⟩ := ih n hrest
              exact ⟨x :: xs, by simp [hms], by simp [hlen]⟩

/-- Splitting at `n` G1 slots. -/
theorem exists_split_g1_prefix {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type}
    (ms : List (Msg (Fr p) G₁)) (n : Nat) (rest : List WireSlot)
    (h : ms.map Msg.slot = List.replicate n WireSlot.g1 ++ rest) :
    ∃ (Qs : List G₁) (ms' : List (Msg (Fr p) G₁)),
      Qs.length = n ∧ ms = Qs.map Msg.g1 ++ ms' ∧ ms'.map Msg.slot = rest := by
  obtain ⟨ms₁, ms₂, hsplit, hpre, hpost⟩ := exists_split_of_slot_prefix ms _ rest h
  obtain ⟨Qs, hms₁, hlen⟩ := eq_map_g1_of_slots ms₁ n hpre
  exact ⟨Qs, ms₂, hlen, by rw [hsplit, hms₁], hpost⟩

theorem wireMsgs_append (E : VerifierEnv p G₁ G₂ Gₜ)
    (ms₁ ms₂ : List (Msg (Fr p) G₁)) :
    wireMsgs E (ms₁ ++ ms₂) = wireMsgs E ms₁ ++ wireMsgs E ms₂ := by
  induction ms₁ with
  | nil => rw [List.nil_append, wireMsgs, bytes_empty_append_local]
  | cons m ms ih => rw [List.cons_append, wireMsgs, ih, wireMsgs, ByteArray.append_assoc]

/-- `RunsAll E m ms`: from the exact wired tail of `ms`, `m` succeeds, consumes all of `ms`,
    advances the cursor by its wire length, and leaves the buffer alone. -/
def RunsAll (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} (m : TranscriptM α)
    (ms : List (Msg (Fr p) G₁)) : Prop :=
  ∀ (t : Transcript) (pref rest : Bytes),
    t.buffer = pref ++ (wireMsgs E ms ++ rest) → t.pos = pref.size →
    p ≤ 2 ^ 256 →
    (∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q) →
    (∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) →
    ∃ a t', m.run t = .ok (a, t') ∧ t'.buffer = t.buffer ∧
      t'.pos = pref.size + (ms.map fun m => (msgWire E m).size).sum

theorem RunsAll.pure (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} (a : α) :
    RunsAll E (pure a : TranscriptM α) [] := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨a, t, ?_, rfl, ?_⟩
  · rfl
  · rw [hpos, List.map_nil, List.sum_nil, Nat.add_zero]

theorem RunsAll.bind (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    {m : TranscriptM α} {f : α → TranscriptM β} {ms₁ ms₂ : List (Msg (Fr p) G₁)}
    (hm : RunsAll E m ms₁) (hf : ∀ a, RunsAll E (f a) ms₂) :
    RunsAll E (m >>= f) (ms₁ ++ ms₂) := by
  intro t pref rest hbuf hpos hp henc hwidth
  rw [wireMsgs_append] at hbuf
  simp only [ByteArray.append_assoc] at hbuf
  obtain ⟨a, t1, hrun1, hbuf1, hpos1⟩ :=
    hm t pref (wireMsgs E ms₂ ++ rest) hbuf hpos hp henc hwidth
  have hbuf1' : t1.buffer = (pref ++ wireMsgs E ms₁) ++ (wireMsgs E ms₂ ++ rest) := by
    rw [hbuf1, hbuf, ← ByteArray.append_assoc]
  have hpos1' : t1.pos = (pref ++ wireMsgs E ms₁).size := by
    rw [hpos1, ByteArray.size_append, wireMsgs_size]
  obtain ⟨b, t2, hrun2, hbuf2, hpos2⟩ :=
    hf a t1 (pref ++ wireMsgs E ms₁) rest hbuf1' hpos1' hp henc hwidth
  refine ⟨b, t2, ?_, hbuf2.trans hbuf1, ?_⟩
  · simp only [StateT.run_bind]
    rw [hrun1]
    exact hrun2
  · rw [hpos2, ByteArray.size_append, wireMsgs_size, List.map_append, List.sum_append]
    omega

theorem RunsAll.get (E : VerifierEnv p G₁ G₂ Gₜ) :
    RunsAll E (StateT.get : TranscriptM Transcript) [] := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨t, t, ?_, rfl, ?_⟩
  · rfl
  · simp [hpos]

theorem RunsAll.lift_ok (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} (a : α) :
    RunsAll E (StateT.lift (.ok a : Except Fault α)) [] := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨a, t, ?_, rfl, ?_⟩
  · rfl
  · rw [hpos, List.map_nil, List.sum_nil, Nat.add_zero]

theorem RunsAll.common (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (h : Midfall.Halo2.Hashable T)
    (x : T) : RunsAll E (tmCommon h x) [] := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨(), t.common h x, ?_, rfl, ?_⟩
  · unfold tmCommon
    rfl
  · rw [show (Transcript.common h t x).pos = t.pos from rfl, hpos, List.map_nil,
      List.sum_nil, Nat.add_zero]

theorem RunsAll.squeeze (E : VerifierEnv p G₁ G₂ Gₜ) :
    RunsAll E (tmSqueezeChallenge (p := p)) [] := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨x, t', hrun, hpos', hbuf'⟩ := tmSqueezeChallenge_run_spec (p := p) t
  refine ⟨x, t', hrun, hbuf', ?_⟩
  rw [hpos', hpos, List.map_nil, List.sum_nil, Nat.add_zero]


/-- `RunsAll` with a postcondition on the program's result: the composition needs the
    read arrays' LENGTHS, which plain `RunsAll` existentially hides. -/
def RunsAllP (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} (m : TranscriptM α)
    (ms : List (Msg (Fr p) G₁)) (P : α → Prop) : Prop :=
  ∀ (t : Transcript) (pref rest : Bytes),
    t.buffer = pref ++ (wireMsgs E ms ++ rest) → t.pos = pref.size →
    p ≤ 2 ^ 256 →
    (∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q) →
    (∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) →
    ∃ a t', m.run t = .ok (a, t') ∧ t'.buffer = t.buffer ∧
      t'.pos = pref.size + (ms.map fun m => (msgWire E m).size).sum ∧ P a

theorem RunsAllP.toRunsAll (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} {m : TranscriptM α}
    {ms : List (Msg (Fr p) G₁)} {P : α → Prop} (h : RunsAllP E m ms P) :
    RunsAll E m ms := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨a, t', hrun, hbuf', hpos', _⟩ := h t pref rest hbuf hpos hp henc hwidth
  exact ⟨a, t', hrun, hbuf', hpos'⟩

theorem RunsAllP.mono (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} {m : TranscriptM α}
    {ms : List (Msg (Fr p) G₁)} {P Q : α → Prop} (h : RunsAllP E m ms P)
    (hPQ : ∀ a, P a → Q a) : RunsAllP E m ms Q := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨a, t', hrun, hbuf', hpos', hP⟩ := h t pref rest hbuf hpos hp henc hwidth
  exact ⟨a, t', hrun, hbuf', hpos', hPQ a hP⟩

theorem RunsAllP.congr (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type}
    {m n : TranscriptM α} {ms : List (Msg (Fr p) G₁)} {P : α → Prop}
    (h : ∀ t, m.run t = n.run t) (hm : RunsAllP E m ms P) :
    RunsAllP E n ms P := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨a, t', hrun, hbuf', hpos', hP⟩ := hm t pref rest hbuf hpos hp henc hwidth
  exact ⟨a, t', (h t).symm ▸ hrun, hbuf', hpos', hP⟩

theorem RunsAllP.pure (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} (a : α) (P : α → Prop)
    (ha : P a) : RunsAllP E (pure a : TranscriptM α) [] P := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨a, t, rfl, rfl, ?_, ha⟩
  rw [hpos, List.map_nil, List.sum_nil, Nat.add_zero]

theorem RunsAllP.common (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type}
    (h : Midfall.Halo2.Hashable T) (x : T) :
    RunsAllP E (tmCommon h x) [] (fun _ => True) := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨(), t.common h x, ?_, rfl, ?_, trivial⟩
  · unfold tmCommon
    rfl
  · rw [show (Transcript.common h t x).pos = t.pos from rfl, hpos, List.map_nil,
      List.sum_nil, Nat.add_zero]

theorem RunsAllP.squeeze (E : VerifierEnv p G₁ G₂ Gₜ) :
    RunsAllP E (tmSqueezeChallenge (p := p)) [] (fun _ => True) := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨x, t', hrun, hpos', hbuf'⟩ := tmSqueezeChallenge_run_spec (p := p) t
  refine ⟨x, t', hrun, hbuf', ?_, trivial⟩
  rw [hpos', hpos, List.map_nil, List.sum_nil, Nat.add_zero]

theorem RunsAllP.lift_ok (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} (a : α) (P : α → Prop)
    (ha : P a) : RunsAllP E (StateT.lift (.ok a : Except Fault α)) [] P := by
  intro t pref rest hbuf hpos hp henc hwidth
  refine ⟨a, t, rfl, rfl, ?_, ha⟩
  rw [hpos, List.map_nil, List.sum_nil, Nat.add_zero]

theorem RunsAllP.bind (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    {m : TranscriptM α} {f : α → TranscriptM β} {ms₁ ms₂ : List (Msg (Fr p) G₁)}
    {P : α → Prop} {Q : β → Prop}
    (hm : RunsAllP E m ms₁ P) (hf : ∀ a, P a → RunsAllP E (f a) ms₂ Q) :
    RunsAllP E (m >>= f) (ms₁ ++ ms₂) Q := by
  intro t pref rest hbuf hpos hp henc hwidth
  rw [wireMsgs_append] at hbuf
  simp only [ByteArray.append_assoc] at hbuf
  obtain ⟨a, t1, hrun1, hbuf1, hpos1, hP⟩ := hm t pref (wireMsgs E ms₂ ++ rest) hbuf hpos hp henc hwidth
  have hbuf1' : t1.buffer = (pref ++ wireMsgs E ms₁) ++ (wireMsgs E ms₂ ++ rest) := by
    rw [hbuf1, hbuf, ← ByteArray.append_assoc]
  have hpos1' : t1.pos = (pref ++ wireMsgs E ms₁).size := by
    rw [hpos1, ByteArray.size_append, wireMsgs_size]
  obtain ⟨b, t2, hrun2, hbuf2, hpos2, hQ⟩ := hf a hP t1 (pref ++ wireMsgs E ms₁) rest hbuf1' hpos1' hp henc hwidth
  refine ⟨b, t2, ?_, hbuf2.trans hbuf1, ?_, hQ⟩
  · simp only [StateT.run_bind]
    rw [hrun1]
    exact hrun2
  · rw [hpos2, ByteArray.size_append, wireMsgs_size, List.map_append, List.sum_append]
    omega

/-- `RunsAllP.bind` with an empty second message list, stated at the first list. -/
theorem RunsAllP.bind_nil (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    {m : TranscriptM α} {f : α → TranscriptM β} {ms : List (Msg (Fr p) G₁)}
    {P : α → Prop} {Q : β → Prop}
    (hm : RunsAllP E m ms P) (hf : ∀ a, P a → RunsAllP E (f a) [] Q) :
    RunsAllP E (m >>= f) ms Q := by
  simpa only [List.append_nil] using RunsAllP.bind E (ms₁ := ms) (ms₂ := []) hm hf

/-- `RunsAll.bind` with an empty second message list, stated at the first list. -/
theorem RunsAll.bind_nil (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    {m : TranscriptM α} {f : α → TranscriptM β} {ms : List (Msg (Fr p) G₁)}
    (hm : RunsAll E m ms) (hf : ∀ a, RunsAll E (f a) []) :
    RunsAll E (m >>= f) ms := by
  simpa only [List.append_nil] using RunsAll.bind E (ms₁ := ms) (ms₂ := []) hm hf

/-- Read a list of homogeneous G1 groups in order. -/
def readG1Groups (E : VerifierEnv p G₁ G₂ Gₜ) : List Nat → TranscriptM Unit
  | [] => pure ()
  | n :: ns => (tmReadN (hashableG1 E.g1) n) >>= fun _ => readG1Groups E ns

theorem runsAll_readG1Groups (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (counts : List Nat) (Qs : List G₁),
      Qs.length = counts.sum →
      RunsAll E (readG1Groups E counts) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro counts
  induction counts with
  | nil =>
      intro Qs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      exact RunsAll.pure E ()
  | cons n ns ih =>
      intro Qs hlen
      have hle : n ≤ Qs.length := by rw [hlen, List.sum_cons]; omega
      have hlen₁ : (Qs.take n).length = n := by rw [List.length_take]; omega
      have hlen₂ : (Qs.drop n).length = ns.sum := by
        rw [List.length_drop, hlen, List.sum_cons]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      refine RunsAll.bind E ?_ ?_
      · -- the first group
        intro t pref rest hbuf hpos hp henc hwidth
        rw [← ByteArray.append_assoc] at hbuf
        obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
          tmReadN_g1_wire E n t pref (Qs.take n) rest hlen₁ hbuf hpos hp henc hwidth
        refine ⟨arr, t', hrun, hbuf', ?_⟩
        simpa only [List.map_map, Function.comp_def] using hpos'
      · intro _
        exact ih (Qs.drop n) hlen₂


/-- Read a list of homogeneous Fr groups in order. -/
def readFrGroups (E : VerifierEnv p G₁ G₂ Gₜ) : List Nat → TranscriptM Unit
  | [] => pure ()
  | n :: ns => (tmReadN (hashableFr (p := p)) n) >>= fun _ => readFrGroups E ns

/-- Concatenating group-count lists composes the group reader. -/
theorem runsAll_readG1Groups_append (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (counts₁ counts₂ : List Nat) (Qs₁ Qs₂ : List G₁),
      Qs₁.length = counts₁.sum → Qs₂.length = counts₂.sum →
      RunsAll E (readG1Groups E (counts₁ ++ counts₂))
        (Qs₁.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          Qs₂.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro counts₁
  induction counts₁ with
  | nil =>
      intro counts₂ Qs₁ Qs₂ h₁ h₂
      have hQs : Qs₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using h₁)
      subst hQs
      simpa only [List.nil_append, List.map_nil, List.nil_append] using
        runsAll_readG1Groups E counts₂ Qs₂ h₂
  | cons n ns ih =>
      intro counts₂ Qs₁ Qs₂ h₁ h₂
      have hle : n ≤ Qs₁.length := by rw [h₁, List.sum_cons]; omega
      have hlen₁ : (Qs₁.take n).length = n := by rw [List.length_take]; omega
      have hlen₂ : (Qs₁.drop n).length = ns.sum := by
        rw [List.length_drop, h₁, List.sum_cons]; omega
      have hsplit : Qs₁.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs₁.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs₁.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.cons_append, readG1Groups, hsplit]
      simp only [List.map_append, List.append_assoc]
      refine RunsAll.bind E ?_ ?_
      · intro t pref rest hbuf hpos hp henc hwidth
        rw [← ByteArray.append_assoc] at hbuf
        obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
          tmReadN_g1_wire E n t pref (Qs₁.take n) rest hlen₁ hbuf hpos hp henc hwidth
        refine ⟨arr, t', hrun, hbuf', ?_⟩
        simpa only [List.map_map, Function.comp_def] using hpos'
      · intro _
        exact ih counts₂ (Qs₁.drop n) Qs₂ hlen₂ h₂

theorem runsAll_readFrGroups (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (counts : List Nat) (Qs : List (Fr p)),
      Qs.length = counts.sum →
      RunsAll E (readFrGroups E counts) (Qs.map (fun Q => (Msg.fr Q : Msg (Fr p) G₁))) := by
  intro counts
  induction counts with
  | nil =>
      intro Qs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      exact RunsAll.pure E ()
  | cons n ns ih =>
      intro Qs hlen
      have hle : n ≤ Qs.length := by rw [hlen, List.sum_cons]; omega
      have hlen₁ : (Qs.take n).length = n := by rw [List.length_take]; omega
      have hlen₂ : (Qs.drop n).length = ns.sum := by
        rw [List.length_drop, hlen, List.sum_cons]; omega
      have hsplit : Qs.map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) =
          (Qs.take n).map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) ++
            (Qs.drop n).map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      refine RunsAll.bind E ?_ ?_
      · -- the first group
        intro t pref rest hbuf hpos hp henc hwidth
        rw [← ByteArray.append_assoc] at hbuf
        obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
          tmReadN_fr_wire E n t pref (Qs.take n) rest hlen₁ hbuf hpos hp
        refine ⟨arr, t', hrun, hbuf', ?_⟩
        simpa only [List.map_map, Function.comp_def] using hpos'
      · intro _
        exact ih (Qs.drop n) hlen₂


/-- Concatenating group-count lists composes the group reader. -/
theorem runsAll_readFrGroups_append (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (counts₁ counts₂ : List Nat) (Qs₁ Qs₂ : List (Fr p)),
      Qs₁.length = counts₁.sum → Qs₂.length = counts₂.sum →
      RunsAll E (readFrGroups E (counts₁ ++ counts₂))
        (Qs₁.map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) ++
          Qs₂.map (fun Q => (Msg.fr Q : Msg (Fr p) G₁))) := by
  intro counts₁
  induction counts₁ with
  | nil =>
      intro counts₂ Qs₁ Qs₂ h₁ h₂
      have hQs : Qs₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using h₁)
      subst hQs
      simpa only [List.nil_append, List.map_nil, List.nil_append] using
        runsAll_readFrGroups E counts₂ Qs₂ h₂
  | cons n ns ih =>
      intro counts₂ Qs₁ Qs₂ h₁ h₂
      have hle : n ≤ Qs₁.length := by rw [h₁, List.sum_cons]; omega
      have hlen₁ : (Qs₁.take n).length = n := by rw [List.length_take]; omega
      have hlen₂ : (Qs₁.drop n).length = ns.sum := by
        rw [List.length_drop, h₁, List.sum_cons]; omega
      have hsplit : Qs₁.map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) =
          (Qs₁.take n).map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) ++
            (Qs₁.drop n).map (fun Q => (Msg.fr Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.cons_append, readFrGroups, hsplit]
      simp only [List.map_append, List.append_assoc]
      refine RunsAll.bind E ?_ ?_
      · intro t pref rest hbuf hpos hp henc hwidth
        rw [← ByteArray.append_assoc] at hbuf
        obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
          tmReadN_fr_wire E n t pref (Qs₁.take n) rest hlen₁ hbuf hpos hp
        refine ⟨arr, t', hrun, hbuf', ?_⟩
        simpa only [List.map_map, Function.comp_def] using hpos'
      · intro _
        exact ih counts₂ (Qs₁.drop n) Qs₂ hlen₂ h₂

/-- `instanceShape` is exactly one proof row, so `parseTrace`'s `numProofs` is 1. -/
theorem instanceShape_numProofs {p : Nat} [Fact (Nat.Prime p)] (inst : Array (Fr p)) :
    (instanceShape inst).size = 1 := rfl

/-- The proof-index loop of `parseTrace` at this profile is the singleton `[0]`. -/
theorem instanceShape_range {p : Nat} [Fact (Nat.Prime p)] (inst : Array (Fr p)) :
    List.range (instanceShape inst).size = [0] := by
  simp [instanceShape]

/-- The parser's phase column filter: advice columns whose phase is `ph`, in index order. -/
def phaseCols {p : Nat} [Fact (Nat.Prime p)] (cs : Midfall.Halo2.ConstraintSystem (Fr p))
    (ph : Midfall.Halo2.Phase) : List Nat :=
  (List.range cs.numAdviceColumns).filterMap fun i =>
    if (cs.adviceColumnPhase[i]?.map (fun q => q.val)) == some ph.val then some i else none

/-- **THE PHASE-ORDER INTERFACE.** The phases, listed in `vk.cs.phases` order,
    enumerate the advice columns in column order. This is what the advice
    commitment array (`scatterIndexed`, column-indexed) and the calldata advice
    window (phase-indexed) need in order to agree; `WellFormed.advicePhaseTotal`
    only fixes the LENGTH of `adviceColumnPhase`, so it does not derive this. -/
def AdvicePhasesColumnOrder (vk : VerifyingKey (Fr p) G₁) : Prop :=
  vk.cs.phases.flatMap (fun ph => phaseCols vk.cs ph) = List.range vk.cs.numAdviceColumns

section AdvicePhaseOrderFalsifier
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- **THE ORDER IS NOT FREE.** A two-column key with phase vector `[1,0]` satisfies
    `adviceColumnPhase.size = numAdviceColumns` but its phase blocks flatten to
    `[1,0]`, not `[0,1]`. So `WellFormed.advicePhaseTotal` does NOT derive
    `AdvicePhasesColumnOrder`; the order is the named phase-order premise. -/
theorem advicePhaseTotal_not_columnOrder :
    ∃ cs : Midfall.Halo2.ConstraintSystem (Fr 17),
      cs.adviceColumnPhase.size = cs.numAdviceColumns ∧
        cs.phases.flatMap (fun ph => phaseCols cs ph) ≠ List.range cs.numAdviceColumns := by
  refine ⟨{ Midfall.Halo2.ConstraintSystem.default (F := Fr 17) with
      numAdviceColumns := 2, adviceColumnPhase := #[⟨1⟩, ⟨0⟩] }, ?_, ?_⟩
  · rfl
  · decide

end AdvicePhaseOrderFalsifier

/-- The advice-phase segment of the parser schedule: one G1 group per user phase. -/
def seqAdvice (userPhases : List UserPhase) : List (WireSlot × Nat) :=
  userPhases.map (fun ph => (WireSlot.g1, ph.adviceBytes / 128))

/-- A mixed schedule of homogeneous groups: one `(slot, count)` pair per group. -/
def readGroupSeq (E : VerifierEnv p G₁ G₂ Gₜ) : List (WireSlot × Nat) → TranscriptM Unit
  | [] => pure ()
  | (s, n) :: rest =>
      (match s with
       | .g1 => (tmReadN (hashableG1 E.g1) n : TranscriptM (Array G₁)) >>= fun _ => pure ()
       | .fr => (tmReadN (hashableFr (p := p)) n : TranscriptM (Array (Fr p))) >>= fun _ => pure ())
      >>= fun _ => readGroupSeq E rest

/-- The message groups match a group schedule: count and slot. -/
def GroupsMatch : List (WireSlot × Nat) → List (List (Msg (Fr p) G₁)) → Prop
  | [], [] => True
  | (s, n) :: ss, g :: gs => g.length = n ∧ (∀ m ∈ g, Msg.slot m = s) ∧ GroupsMatch ss gs
  | _, _ => False

theorem runsAll_readGroupSeq (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (seq : List (WireSlot × Nat)) (groups : List (List (Msg (Fr p) G₁))),
      GroupsMatch (p := p) (G₁ := G₁) seq groups →
      RunsAll E (readGroupSeq E seq) groups.flatten := by
  intro seq
  induction seq with
  | nil =>
      intro groups h
      cases groups with
      | nil => simpa only [readGroupSeq, List.flatten] using RunsAll.pure E ()
      | cons g gs => cases h
  | cons sn ss ih =>
      intro groups h
      obtain ⟨s, n⟩ := sn
      cases groups with
      | nil => cases h
      | cons g gs =>
          obtain ⟨hlen, hslot, hmatch⟩ := h
          cases s with
          | g1 =>
              have hmap : g.map Msg.slot = List.replicate n WireSlot.g1 := by
                rw [← hlen]
                calc g.map Msg.slot = g.map (fun _ => WireSlot.g1) :=
                      List.map_congr_left hslot
                  _ = List.replicate g.length WireSlot.g1 := List.map_const ..
              obtain ⟨Qs, hg, hQlen⟩ := eq_map_g1_of_slots g n hmap
              rw [readGroupSeq]
              show RunsAll E
                (((tmReadN (hashableG1 E.g1) n : TranscriptM (Array G₁)) >>= fun _ => pure ())
                  >>= fun _ => readGroupSeq E ss) ((g :: gs).flatten)
              refine RunsAll.bind E ?_ (fun _ => ih gs hmatch)
              rw [hg]
              have hstep : RunsAll E ((tmReadN (hashableG1 E.g1) n : TranscriptM (Array G₁)))
                  (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
                intro t pref rest hbuf hpos hp henc hwidth
                rw [← ByteArray.append_assoc] at hbuf
                obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
                  tmReadN_g1_wire E n t pref Qs rest hQlen hbuf hpos hp henc hwidth
                refine ⟨arr, t', hrun, hbuf', ?_⟩
                simpa only [List.map_map, Function.comp_def] using hpos'
              simpa only [List.append_nil] using
                (RunsAll.bind E hstep (fun _ => RunsAll.pure E ()))
          | fr =>
              have hmap : g.map Msg.slot = List.replicate n WireSlot.fr := by
                rw [← hlen]
                calc g.map Msg.slot = g.map (fun _ => WireSlot.fr) :=
                      List.map_congr_left hslot
                  _ = List.replicate g.length WireSlot.fr := List.map_const ..
              obtain ⟨xs, hg, hxlen⟩ := eq_map_fr_of_slots g n hmap
              rw [readGroupSeq]
              show RunsAll E
                (((tmReadN (hashableFr (p := p)) n : TranscriptM (Array (Fr p))) >>= fun _ => pure ())
                  >>= fun _ => readGroupSeq E ss) ((g :: gs).flatten)
              refine RunsAll.bind E ?_ (fun _ => ih gs hmatch)
              rw [hg]
              have hstep : RunsAll E ((tmReadN (hashableFr (p := p)) n : TranscriptM (Array (Fr p))))
                  (xs.map (fun x => (Msg.fr x : Msg (Fr p) G₁))) := by
                intro t pref rest hbuf hpos hp henc hwidth
                rw [← ByteArray.append_assoc] at hbuf
                obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
                  tmReadN_fr_wire E n t pref xs rest hxlen hbuf hpos hp
                refine ⟨arr, t', hrun, hbuf', ?_⟩
                simpa only [List.map_map, Function.comp_def] using hpos'
              simpa only [List.append_nil] using
                (RunsAll.bind E hstep (fun _ => RunsAll.pure E ()))

/-- `readGroupSeq` composes on schedule concatenation. -/
theorem readGroupSeq_append_run (E : VerifierEnv p G₁ G₂ Gₜ)
    (a b : List (WireSlot × Nat)) (t : Transcript) :
    (readGroupSeq E (a ++ b)).run t =
      (readGroupSeq E a >>= fun _ => readGroupSeq E b).run t := by
  induction a generalizing t with
  | nil => simp [readGroupSeq]
  | cons x a ih =>
      cases x with
      | mk s n =>
          have hih : readGroupSeq E (a ++ b) =
              (readGroupSeq E a >>= fun _ => readGroupSeq E b) := by
            funext t
            exact ih t
          simp only [List.cons_append, readGroupSeq]
          rw [hih]
          simp [bind_assoc]

/-- A list of schedules is read by the `foldlM` exactly as their flattening. -/
theorem readGroupSeq_flatMap_run (E : VerifierEnv p G₁ G₂ Gₜ)
    (l : List (List (WireSlot × Nat))) (t : Transcript) :
    (readGroupSeq E l.flatten).run t =
      (l.foldlM (fun _ g => readGroupSeq E g) ()).run t := by
  induction l generalizing t with
  | nil => simp [readGroupSeq]
  | cons g gs ih =>
      have hih : readGroupSeq E gs.flatten =
          (gs.foldlM (fun _ g => readGroupSeq E g) ()) := by
        funext t
        exact ih t
      have happ : readGroupSeq E (g ++ gs.flatten) =
          (readGroupSeq E g >>= fun _ => readGroupSeq E gs.flatten) := by
        funext t
        exact readGroupSeq_append_run E g gs.flatten t
      simp only [List.flatten_cons, List.foldlM_cons]
      rw [happ, hih]

/-- The advice-phase fragment: one homogeneous G1 group. -/
theorem runsAll_readGroupSeq_g1 (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (Qs : List G₁)
    (hlen : Qs.length = n) :
    RunsAll E (readGroupSeq E [(WireSlot.g1, n)])
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  have hmatch : GroupsMatch (p := p) (G₁ := G₁) [(WireSlot.g1, n)]
      [Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))] := by
    refine ⟨?_, ?_, trivial⟩
    · simpa using hlen
    · intro m hm
      rw [List.mem_map] at hm
      obtain ⟨Q, -, rfl⟩ := hm
      rfl
  simpa [List.flatten] using
    runsAll_readGroupSeq E [(WireSlot.g1, n)]
      [Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))] hmatch

/-- `RunsAll` is invariant under pointwise-equal runs. -/
theorem RunsAll.congr (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} {m n : TranscriptM α}
    {ms : List (Msg (Fr p) G₁)} (h : ∀ t, m.run t = n.run t) (hm : RunsAll E m ms) :
    RunsAll E n ms := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨a, t', hrun, hbuf', hpos'⟩ := hm t pref rest hbuf hpos hp henc hwidth
  exact ⟨a, t', ((h t).symm).trans hrun, hbuf', hpos'⟩

/-- The `foldlM` over schedules reads exactly the flattened schedule. -/
theorem runsAll_readGroupSeq_foldlM (E : VerifierEnv p G₁ G₂ Gₜ)
    (l : List (List (WireSlot × Nat))) (groups : List (List (Msg (Fr p) G₁)))
    (hm : GroupsMatch (p := p) (G₁ := G₁) l.flatten groups) :
    RunsAll E (l.foldlM (fun _ g => readGroupSeq E g) ()) groups.flatten :=
  RunsAll.congr E (fun t => readGroupSeq_flatMap_run E l t)
    (runsAll_readGroupSeq E l.flatten groups hm)

/-- Splitting a matching group list at a schedule prefix. -/
theorem groupsMatch_take_drop {p : Nat} [Fact (Nat.Prime p)] {G₁ : Type}
    (g rest : List (WireSlot × Nat)) (groups : List (List (Msg (Fr p) G₁)))
    (hm : GroupsMatch (p := p) (G₁ := G₁) (g ++ rest) groups) :
    GroupsMatch (p := p) (G₁ := G₁) g (groups.take g.length) ∧
    GroupsMatch (p := p) (G₁ := G₁) rest (groups.drop g.length) := by
  induction g generalizing groups with
  | nil =>
      simp only [List.nil_append, List.length_nil, List.take_nil, List.drop_nil]
      exact ⟨trivial, hm⟩
  | cons x g' ih =>
      cases groups with
      | nil => simp [GroupsMatch] at hm
      | cons group groups' =>
          simp only [List.cons_append, GroupsMatch] at hm
          obtain ⟨hlen, hslot, hmrest⟩ := hm
          obtain ⟨hhead, htail⟩ := ih groups' hmrest
          refine ⟨?_, ?_⟩
          · simp only [List.length_cons, List.take_succ_cons, GroupsMatch]
            exact ⟨hlen, hslot, hhead⟩
          · simpa only [List.length_cons, List.drop_succ_cons] using htail

/-- The state-threaded fold over schedules reads the flattened groups. -/
theorem runsAll_foldlM_readGroupSeq_state (E : VerifierEnv p G₁ G₂ Gₜ) {β : Type} :
    ∀ (l : List (List (WireSlot × Nat))) (upd : β → List (WireSlot × Nat) → β) (s : β)
      (groups : List (List (Msg (Fr p) G₁))),
      GroupsMatch (p := p) (G₁ := G₁) l.flatten groups →
      RunsAll E (l.foldlM (fun st g => readGroupSeq E g >>= fun _ => pure (upd st g)) s)
        groups.flatten := by
  intro l
  induction l with
  | nil =>
      intro upd s groups hm
      cases groups with
      | nil => simpa only [List.foldlM_nil, List.flatten_nil] using RunsAll.pure E s
      | cons group groups => simp [GroupsMatch] at hm
  | cons g gs ih =>
      intro upd s groups hm
      obtain ⟨hm₁, hm₂⟩ := groupsMatch_take_drop g gs.flatten groups hm
      rw [List.foldlM_cons]
      have hstep : RunsAll E (readGroupSeq E g >>= fun _ => pure (upd s g))
          (groups.take g.length).flatten := by
        simpa only [List.append_nil] using
          (RunsAll.bind E (runsAll_readGroupSeq E g (groups.take g.length) hm₁)
            (fun _ => RunsAll.pure E (upd s g)))
      have hbind := RunsAll.bind E hstep (fun st' => ih upd st' (groups.drop g.length) hm₂)
      rw [← List.flatten_append, List.take_append_drop] at hbind
      exact hbind

/-- `transcriptOf` starts at cursor 0 with exactly `wireMsgs` in the buffer. -/
theorem transcriptOf_buffer {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (ms : List (Msg (Fr p) G₁)) :
    (transcriptOf E H ms).buffer = wireMsgs E ms ∧ (transcriptOf E H ms).pos = 0 := by
  refine ⟨?_, rfl⟩
  unfold transcriptOf
  rw [wireMsgs_eq_fold]
  rfl

/-! ## 3c. `parseTrace`'S READ WALK — THE LOOP LEMMAS

SIM.10 obligation 1, smallest pieces first. Each `def` below is the corresponding fragment of
`Midfall.Halo2.Verifier.parseTrace` copied VERBATIM (the same `do` block, the same `hashableG1 E.g1`),
so the eventual whole-run composition can rewrite `parseTrace`'s subterms by `rfl`. Each
`runsAll_*_one` theorem pairs a fragment with a `RunsAll` over exactly the wire messages it
consumes at the deployed profile (`numProofs = instanceShape.size = 1`); the general message list is
the `Qs.map Msg.g1` shape the `RunsAll` toolbox already handles. -/

/-- One G1 read from the exact wire tail (`Msg.g1` singleton). -/
theorem runsAll_read_g1 (E : VerifierEnv p G₁ G₂ Gₜ) (Q : G₁) :
    RunsAll E (Midfall.Halo2.tmRead (hashableG1 E.g1))
      ([Msg.g1 Q] : List (Msg (Fr p) G₁)) := by
  intro t pref rest hbuf hpos hp henc hwidth
  have hbuf' : t.buffer = pref ++ E.g1.toCompressed Q ++ rest := by
    simpa only [wireMsgs_cons, wireMsgs, msgWire, ByteArray.append_empty,
      ByteArray.append_assoc, bytes_empty_append_local] using hbuf
  obtain ⟨t', hrun, hpos', hbuf'⟩ := tmRead_g1_run E.g1 t pref rest Q hbuf' hpos henc hwidth
  refine ⟨Q, t', hrun, hbuf', ?_⟩
  rw [hpos']
  show pref.size + g1CompressedWidth = pref.size + (([Msg.g1 Q] : List (Msg (Fr p) G₁)).map
    (fun m => (msgWire E m).size)).sum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, msgWire]
  rw [hwidth]
  omega

/-- The trashcan fragment of `parseTrace`, verbatim: one G1 read per trashcan, per proof. -/
def parseTraceTrashcans (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (numProofs : Nat) : TranscriptM (Array (Array (Trash.Committed G₁))) :=
  (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let row ← vk.cs.trashcans.toList.foldlM (init := #[]) fun acc' t => do
        let c ← Trash.readCommitted t (hashableG1 E.g1)
        pure (acc'.push c)
      pure (acc.push row)

/-- `Trash.readCommitted` is one G1 read followed by a pure record. -/
theorem runsAll_trash_readCommitted (E : VerifierEnv p G₁ G₂ Gₜ)
    (t : TrashArgument (Fr p)) (Q : G₁) :
    RunsAll E (Trash.readCommitted t (hashableG1 E.g1)) ([Msg.g1 Q] : List (Msg (Fr p) G₁)) := by
  show RunsAll E ((Midfall.Halo2.tmRead (hashableG1 E.g1)) >>= fun c =>
    (pure { trashCommitment := c } : TranscriptM (Trash.Committed G₁)))
    ([Msg.g1 Q] : List (Msg (Fr p) G₁))
  exact RunsAll.bind E (runsAll_read_g1 E Q) (fun _ => RunsAll.pure E _)

/-- The inner trashcan fold reads one G1 per trashcan. -/
theorem runsAll_trashcans_fold (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (ts : List (TrashArgument (Fr p))) (Qs : List G₁) (acc : Array (Trash.Committed G₁)),
      Qs.length = ts.length →
      RunsAll E (ts.foldlM (init := acc) fun acc' t => do
          let c ← Trash.readCommitted t (hashableG1 E.g1)
          pure (acc'.push c)) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro ts
  induction ts with
  | nil =>
      intro Qs acc hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using RunsAll.pure E acc
  | cons t ts ih =>
      intro Qs acc hlen
      obtain ⟨Q, Qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      rw [List.foldlM_cons]
      have hhead : RunsAll E ((fun acc => do
          let c ← Trash.readCommitted t (hashableG1 E.g1)
          pure (acc.push c)) acc) ([Msg.g1 Q] : List (Msg (Fr p) G₁)) := by
        have hb := RunsAll.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁))) (ms₂ := [])
          (runsAll_trash_readCommitted E t Q) (fun c => RunsAll.pure E (acc.push c))
        rw [List.append_nil] at hb
        exact hb
      have hb := RunsAll.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
        (ms₂ := Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        hhead (fun init => ih Qs' init (by simpa using hlen))
      exact hb

/-- **THE TRASHCAN RUN.** At the deployed profile (one proof) `parseTrace`'s trashcan pass reads
    one G1 commitment per trashcan, in order, and nothing else. -/
theorem runsAll_parseTraceTrashcans_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (Qs : List G₁)
    (hlen : Qs.length = vk.cs.trashcans.size) :
    RunsAll E (parseTraceTrashcans E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  rw [parseTraceTrashcans]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil]
  have hA : RunsAll E
      (List.foldlM (fun acc' t => do
        let c ← Trash.readCommitted t (hashableG1 E.g1)
        pure (acc'.push c)) #[] vk.cs.trashcans.toList >>= fun row => pure (#[].push row))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
    have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      (runsAll_trashcans_fold E vk.cs.trashcans.toList Qs #[] hlen)
      (fun row => RunsAll.pure E (#[].push row))
    rw [List.append_nil] at hb
    exact hb
  have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    hA (fun acc => RunsAll.pure E acc)
  rw [List.append_nil] at hb
  exact hb

theorem runsAll_tmReadN_g1 (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (Qs : List G₁)
    (hlen : Qs.length = n) :
    RunsAll E (tmReadN (hashableG1 E.g1) n)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro t pref rest hbuf hpos hp henc hwidth
  rw [← ByteArray.append_assoc] at hbuf
  obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
    tmReadN_g1_wire E n t pref Qs rest hlen hbuf hpos hp henc hwidth
  refine ⟨arr, t', hrun, hbuf', ?_⟩
  simpa only [List.map_map, Function.comp_def] using hpos'

/-- The group read, WITH the length postcondition the scatter step needs. -/
theorem runsAllP_tmReadN_g1 (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (Qs : List G₁)
    (hlen : Qs.length = n) :
    RunsAllP E (tmReadN (hashableG1 E.g1) n)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (fun arr => arr.size = n) := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨arr, t', hrun, hbuf', hpos'⟩ :=
    runsAll_tmReadN_g1 E n Qs hlen t pref rest hbuf hpos hp henc hwidth
  exact ⟨arr, t', hrun, hbuf', hpos', tmReadN_size (hashableG1 E.g1) n hrun⟩

/-- The permutation-product fragment of `parseTrace`, verbatim. -/
def parseTracePermutations (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (numProofs : Nat) : TranscriptM (Array (Permutation.Committed G₁)) :=
  (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
        (hashableG1 E.g1)
      pure (acc.push pc)

theorem runsAll_perm_readProductCommitments (E : VerifierEnv p G₁ G₂ Gₜ)
    (perm : PermutationArgument) (csDegree : Nat) (hdeg : 3 ≤ csDegree)
    (Qs : List G₁)
    (hlen : Qs.length = Permutation.numChunksOf perm.columns.size (csDegree - 2)) :
    RunsAll E (Permutation.readProductCommitments perm csDegree (hashableG1 E.g1))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  unfold Permutation.readProductCommitments
  have hpos : 2 < csDegree := by omega
  have hlen0 : csDegree - 2 > 0 := by omega
  simp only [hlen0, ↓reduceIte]
  have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    (runsAll_tmReadN_g1 E (Permutation.numChunksOf perm.columns.size (csDegree - 2)) Qs hlen)
    (fun arr => RunsAll.pure E ({ permutationProductCommitments := arr } : Permutation.Committed G₁))
  rw [List.append_nil] at hb
  exact hb

theorem runsAll_parseTracePermutations_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hdeg : 3 ≤ vk.csDegree) (Qs : List G₁)
    (hlen : Qs.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2)) :
    RunsAll E (parseTracePermutations E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  rw [parseTracePermutations]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil]
  have hA : RunsAll E
      ((fun acc => do
        let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
          (hashableG1 E.g1)
        pure (acc.push pc)) #[])
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
    have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      (runsAll_perm_readProductCommitments E vk.cs.permutation vk.csDegree hdeg Qs hlen)
      (fun pc => RunsAll.pure E (#[].push pc))
    rw [List.append_nil] at hb
    exact hb
  have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    hA (fun acc => RunsAll.pure E acc)
  rw [List.append_nil] at hb
  exact hb


/-- `Logup.readMultiplicities` is one G1 read followed by a pure record. -/
theorem runsAll_logup_readMultiplicities (E : VerifierEnv p G₁ G₂ Gₜ)
    (chunked : LogupChunkedArgument (Fr p)) (Q : G₁) :
    RunsAll E (Logup.readMultiplicities chunked (hashableG1 E.g1))
      ([Msg.g1 Q] : List (Msg (Fr p) G₁)) := by
  show RunsAll E ((Midfall.Halo2.tmRead (hashableG1 E.g1)) >>= fun c =>
    (pure { multiplicities := c } : TranscriptM (Logup.CommittedMultiplicities G₁)))
    ([Msg.g1 Q] : List (Msg (Fr p) G₁))
  exact RunsAll.bind E (runsAll_read_g1 E Q) (fun _ => RunsAll.pure E _)

/-- The lookup-multiplicity fragment of `parseTrace`, verbatim: chunk, then one G1 read per lookup,
    per proof. -/
def parseTraceLookupMultiplicities (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (numProofs : Nat) :
    TranscriptM (Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) :=
  (List.range numProofs).foldlM
    (init := #[]) fun acc _ => do
      let row ← vk.cs.lookups.toList.foldlM (init := #[]) fun acc' l => do
        let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
        let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
        pure (acc'.push (m, chunked))
      pure (acc.push row)

/-- The inner lookup fold: one G1 read per lookup, GIVEN that each lookup chunks successfully.
    `chunkByDegree` is not total: `logup.rs:237` panics when a lookup's input degree is `0`, and
    `rustChunks` panics when the chunk count is `0`. `WellFormed` does NOT pin either, so this is
    the first genuinely missing static fact of the walk, stated as the exact success hypothesis. -/
theorem runsAll_lookupMultiplicities_fold (E : VerifierEnv p G₁ G₂ Gₜ)
    (deg : Nat) :
    ∀ (ls : List (LogupBatchedArgument (Fr p)))
      (acc : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
      (Qs : List G₁),
      (∀ l ∈ ls, ∃ c, l.chunkByDegree deg = .ok c) →
      Qs.length = ls.length →
      RunsAll E (ls.foldlM (init := acc) fun acc' l => do
          let chunked ← StateT.lift (l.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc'.push (m, chunked))) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro ls
  induction ls with
  | nil =>
      intro acc Qs hs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using RunsAll.pure E acc
  | cons l ls ih =>
      intro acc Qs hs hlen
      obtain ⟨Q, Qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      obtain ⟨c, hc⟩ := hs l (by simp)
      rw [List.foldlM_cons]
      have hlift : RunsAll E ((fun acc => do
          let chunked ← StateT.lift (l.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc.push (m, chunked))) acc) ([Msg.g1 Q] : List (Msg (Fr p) G₁)) := by
        have hb := RunsAll.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
          (ms₂ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (RunsAll.lift_ok E c) (fun chunked =>
            RunsAll.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁))) (ms₂ := [])
              (runsAll_logup_readMultiplicities E chunked Q)
              (fun m => RunsAll.pure E (acc.push (m, chunked))))
        rw [List.nil_append] at hb
        simpa only [hc] using hb
      have hb := RunsAll.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
        (ms₂ := Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        hlift (fun init => ih init Qs' (fun l' hl' => hs l' (by simp [hl'])) (by simpa using hlen))
      exact hb

/-- **THE LOOKUP-MULTIPLICITY RUN.** At the deployed profile, `parseTrace`'s multiplicity pass
    reads one G1 commitment per lookup, in order. The chunkability hypothesis is the static fact
    `WellFormed` does not carry (see `runsAll_lookupMultiplicities_fold`). -/
theorem runsAll_parseTraceLookupMultiplicities_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (Qs : List G₁) (hlen : Qs.length = vk.cs.lookups.size) :
    RunsAll E (parseTraceLookupMultiplicities E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  rw [parseTraceLookupMultiplicities]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil]
  have hA : RunsAll E
      ((fun acc => do
        let row ← vk.cs.lookups.toList.foldlM (init := #[]) fun acc' l => do
          let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc'.push (m, chunked))
        pure (acc.push row)) #[])
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
    have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      (runsAll_lookupMultiplicities_fold E vk.csDegree vk.cs.lookups.toList #[] Qs hs hlen)
      (fun row => RunsAll.pure E (#[].push row))
    rw [List.append_nil] at hb
    exact hb
  have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    hA (fun acc => RunsAll.pure E acc)
  rw [List.append_nil] at hb
  exact hb

/-! #### D-GATE12 - the clause spent

`WellFormed.lookupChunkable` is the exact success+nonzero form; these two lemmas turn it into the
success of `nbParallelLookupsPerChunk` and of `chunkByDegree` itself, and the multiplicity run then
drops its hypothesis. -/

/-- **D-GATE12, EXISTENTIAL FORM.** The decidable clause gives the `∃ nb` with `0 < nb`. -/
theorem nbParallelLookupsPerChunk_ok_of_wf {vk : VerifyingKey (Fr p) G₁}
    (hf : vk.WellFormed Features.solidity) {l : LogupBatchedArgument (Fr p)}
    (hl : l ∈ vk.cs.lookups.toList) :
    ∃ nb, l.nbParallelLookupsPerChunk vk.csDegree = .ok nb ∧ 0 < nb := by
  have h := hf.lookupChunkable l hl
  cases hb : l.nbParallelLookupsPerChunk vk.csDegree with
  | error e => rw [hb] at h; cases h
  | ok nb =>
      rw [hb] at h
      exact ⟨nb, rfl, of_decide_eq_true h⟩

/-- `rustChunks` succeeds exactly when the chunk count is nonzero (`logup.rs:329` panics at zero). -/
theorem rustChunks_ok {α : Type} (n : Nat) (hn : 0 < n) (site : String) (xs : Array α) :
    ∃ ys, rustChunks n site xs = .ok ys := by
  unfold rustChunks
  rw [if_neg (Nat.ne_of_gt hn)]
  exact ⟨_, rfl⟩

/-- **`chunkByDegree` SUCCEEDS AT EVERY LOOKUP OF A WELL-FORMED KEY.** Both panic sites are
    excluded: the zero input degree by the `nbParallelLookupsPerChunk` success, the zero chunk
    count by its positivity. -/
theorem chunkByDegree_ok_of_wf {vk : VerifyingKey (Fr p) G₁}
    (hf : vk.WellFormed Features.solidity) {l : LogupBatchedArgument (Fr p)}
    (hl : l ∈ vk.cs.lookups.toList) :
    ∃ c, l.chunkByDegree vk.csDegree = .ok c := by
  obtain ⟨nb, hnb, hpos⟩ := nbParallelLookupsPerChunk_ok_of_wf hf hl
  unfold LogupBatchedArgument.chunkByDegree
  rw [hnb]
  simp only [Except.bind, bind, Except.pure, pure]
  obtain ⟨ys, hys⟩ := rustChunks_ok nb hpos _ l.inputExpressions
  rw [hys]
  exact ⟨_, rfl⟩

/-- **THE MULTIPLICITY RUN, UNCONDITIONAL.** Same statement as
    `runsAll_parseTraceLookupMultiplicities_one`, with the chunkability hypothesis discharged by
    `WellFormed.lookupChunkable`. -/
theorem runsAll_parseTraceLookupMultiplicities_one_of_wf (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (Qs : List G₁) (hlen : Qs.length = vk.cs.lookups.size) :
    RunsAll E (parseTraceLookupMultiplicities E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) :=
  runsAll_parseTraceLookupMultiplicities_one E vk
    (fun l hl => chunkByDegree_ok_of_wf hf hl) Qs hlen

theorem runsAll_logup_readCommitment (E : VerifierEnv p G₁ G₂ Gₜ)
    (cm : Logup.CommittedMultiplicities G₁) (n : Nat) (Qs : List G₁)
    (hlen : Qs.length = n + 1) :
    RunsAll E (cm.readCommitment n (hashableG1 E.g1))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  have hle : n ≤ Qs.length := by omega
  have hlen1 : (Qs.take n).length = n := by rw [List.length_take]; omega
  have hlen2 : (Qs.drop n).length = 1 := by rw [List.length_drop]; omega
  have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
      (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hsplit]
  unfold Logup.CommittedMultiplicities.readCommitment
  refine RunsAll.bind E (ms₁ := (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ?_ ?_
  · exact runsAll_tmReadN_g1 E n (Qs.take n) hlen1
  · intro helperPolys
    obtain ⟨Q, Qs', hQs'⟩ := List.exists_cons_of_length_pos (by rw [hlen2]; simp)
    have hQs'0 : Qs' = [] := List.eq_nil_of_length_eq_zero (by
      have := hlen2
      rw [hQs', List.length_cons] at this
      omega)
    subst hQs'0
    rw [hQs']
    have hb := RunsAll.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁))) (ms₂ := [])
      (runsAll_read_g1 E Q)
      (fun accumulator => RunsAll.pure E (Logup.Committed.mk cm.multiplicities helperPolys accumulator))
    rw [List.append_nil] at hb
    exact hb

/-- The per-proof lookup-commitment row: `numChunks + 1` reads per lookup. -/
theorem runsAll_lookupCommitments_row (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (row : List (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
      (acc : Array (Logup.Committed G₁)) (Qs : List G₁),
      Qs.length = (row.map (fun p => p.2.numChunks + 1)).sum →
      RunsAll E (row.foldlM (init := acc) fun acc' p => do
          let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
          pure (acc'.push c)) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro row
  induction row with
  | nil =>
      intro acc Qs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using RunsAll.pure E acc
  | cons p ps ih =>
      intro acc Qs hlen
      obtain ⟨m, chunked⟩ := p
      have hsum : Qs.length = (chunked.numChunks + 1) + (ps.map (fun p => p.2.numChunks + 1)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      have hle : chunked.numChunks + 1 ≤ Qs.length := by omega
      have hlen1 : (Qs.take (chunked.numChunks + 1)).length = chunked.numChunks + 1 := by
        rw [List.length_take]; omega
      have hlen2 : (Qs.drop (chunked.numChunks + 1)).length =
          (ps.map (fun p => p.2.numChunks + 1)).sum := by
        rw [List.length_drop, hsum]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      refine RunsAll.bind E (ms₁ := (Qs.take (chunked.numChunks + 1)).map
          (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (ms₂ := (Qs.drop (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        ?_ ?_
      · have hb := RunsAll.bind E
          (ms₁ := (Qs.take (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (ms₂ := [])
          (runsAll_logup_readCommitment E m chunked.numChunks
            (Qs.take (chunked.numChunks + 1)) hlen1)
          (fun c => RunsAll.pure E (acc.push c))
        rw [List.append_nil] at hb
        exact hb
      · intro init
        exact ih init (Qs.drop (chunked.numChunks + 1)) hlen2

/-- The outer lookup-commitment pass: one row per proof. -/
theorem runsAll_lookupCommitments_rows (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (rows : List (Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p))))
      (acc : Array (Array (Logup.Committed G₁))) (Qs : List G₁),
      Qs.length = (rows.map (fun row =>
        (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum →
      RunsAll E (rows.foldlM (init := acc) fun acc row => do
          let out ← row.toList.foldlM (init := #[]) fun acc' p => do
            let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
            pure (acc'.push c)
          pure (acc.push out)) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro rows
  induction rows with
  | nil =>
      intro acc Qs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using RunsAll.pure E acc
  | cons row rows ih =>
      intro acc Qs hlen
      have hsum : Qs.length = (row.toList.map (fun p => p.2.numChunks + 1)).sum +
          (rows.map (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      have hle : (row.toList.map (fun p => p.2.numChunks + 1)).sum ≤ Qs.length := by omega
      obtain ⟨rowLen, hrowLen⟩ : ∃ k, (row.toList.map (fun p => p.2.numChunks + 1)).sum = k :=
        ⟨_, rfl⟩
      have hlen1 : (Qs.take rowLen).length =
          (row.toList.map (fun p => p.2.numChunks + 1)).sum := by
        rw [List.length_take, hrowLen]; omega
      have hlen2 : (Qs.drop rowLen).length =
          (rows.map (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
        rw [List.length_drop, hsum, hrowLen]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      refine RunsAll.bind E (ms₁ := (Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (ms₂ := (Qs.drop rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ?_ ?_
      · have hb := RunsAll.bind E
          (ms₁ := (Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
          (runsAll_lookupCommitments_row E row.toList #[] (Qs.take rowLen) hlen1)
          (fun out => RunsAll.pure E (acc.push out))
        rw [List.append_nil] at hb
        exact hb
      · intro init
        exact ih init (Qs.drop rowLen) hlen2

def parseTraceLookupCommitments (E : VerifierEnv p G₁ G₂ Gₜ)
    (rows : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) :
    TranscriptM (Array (Array (Logup.Committed G₁))) :=
  rows.toList.foldlM (init := #[]) fun acc row => do
    let out ← row.toList.foldlM (init := #[]) fun acc' p => do
      let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
      pure (acc'.push c)
    pure (acc.push out)

/-- **THE LOOKUP-COMMITMENT RUN.** The message count is the chunk-count ledger
    `Σ (numChunks + 1)` over the multiplicities the previous pass produced. -/
theorem runsAll_parseTraceLookupCommitments (E : VerifierEnv p G₁ G₂ Gₜ)
    (rows : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))))
    (Qs : List G₁)
    (hlen : Qs.length = (rows.toList.map (fun row =>
      (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum) :
    RunsAll E (parseTraceLookupCommitments E rows)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  rw [parseTraceLookupCommitments]
  exact runsAll_lookupCommitments_rows E rows.toList #[] Qs hlen

/-- The per-proof advice read of `parseTrace`: one `tmReadN` group of the phase's column count. -/
def parseTraceAdviceProofRead (E : VerifierEnv p G₁ G₂ Gₜ)
    (cols : List Nat) (st1 : List (List (Nat × G₁))) :
    TranscriptM (List (List (Nat × G₁))) :=
  (List.range 1).foldlM (init := st1) fun acc k => do
    let reads ← tmReadN (hashableG1 E.g1) cols.length;
    pure ((acc.take k) ++
          [((acc[k]?.getD []) ++ (List.zip cols reads.toList))] ++
          (acc.drop (k + 1)))

/-- The advice-phase read: one group of `cols.length` G1 points. -/
theorem runsAll_parseTraceAdviceProofRead (E : VerifierEnv p G₁ G₂ Gₜ)
    (cols : List Nat) (st1 : List (List (Nat × G₁)))
    (Qs : List G₁) (hlen : Qs.length = cols.length) :
    RunsAll E (parseTraceAdviceProofRead E cols st1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  rw [parseTraceAdviceProofRead]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil]
  have hb1 := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    (runsAll_tmReadN_g1 E cols.length Qs hlen)
    (fun reads => RunsAll.pure E ((st1.take 0) ++
      [((st1[0]?.getD []) ++ (List.zip cols reads.toList))] ++
      (st1.drop (0 + 1))))
  rw [List.append_nil] at hb1
  have hb2 := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    hb1 (fun init => RunsAll.pure E init)
  rw [List.append_nil] at hb2
  exact hb2

/-- The phase body of `parseTrace`'s advice loop, with `cols` bound to the named `phaseCols`. -/
def parseTraceAdvicePhase (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) :
    (List (List (Nat × G₁)) × List (Nat × Fr p)) → Phase →
      TranscriptM (List (List (Nat × G₁)) × List (Nat × Fr p)) :=
  fun st ph => do
    let cols := phaseCols vk.cs ph
    let adv ← parseTraceAdviceProofRead E cols st.1
    let chalIdxPhase := List.zip (List.range vk.cs.numChallenges)
      vk.cs.challengePhase.toList
    let chals ← chalIdxPhase.foldlM (init := st.2) fun acc e =>
      if e.2.val == ph.val then do
        let c ← tmSqueezeChallenge
        pure (acc ++ [(e.1, c)])
      else pure acc
    pure (adv, chals)

/-- The whole advice-phase fold of `parseTrace`, one proof. -/
def parseTraceAdvicePhases (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) :
    TranscriptM (List (List (Nat × G₁)) × List (Nat × Fr p)) :=
  vk.cs.phases.foldlM
    (init := ((List.range 1).map (fun _ => ([] : List (Nat × G₁))),
              ([] : List (Nat × Fr p))))
    (parseTraceAdvicePhase E vk)

/-- Under `singlePhase` the challenge arm of the phase body is the empty fold. -/
theorem runsAll_parseTraceAdvicePhase (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0)
    (st : List (List (Nat × G₁)) × List (Nat × Fr p)) (ph : Phase)
    (Qs : List G₁) (hlen : Qs.length = (phaseCols vk.cs ph).length) :
    RunsAll E (parseTraceAdvicePhase E vk st ph)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  rw [parseTraceAdvicePhase]
  rw [hsp]
  simp only [List.range_zero, List.zip_nil_left, List.foldlM_nil]
  have hb := RunsAll.bind E (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
    (runsAll_parseTraceAdviceProofRead E (phaseCols vk.cs ph) st.1 Qs hlen)
    (fun adv => RunsAll.pure E (adv, st.2))
  rw [List.append_nil] at hb
  exact hb

/-- The advice-phase fold: each phase contributes one G1 group of its column count. -/
theorem runsAll_parseTraceAdvicePhases (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0) :
    ∀ (phs : List Phase) (acc : List (List (Nat × G₁)) × List (Nat × Fr p))
      (Qs : List G₁),
      Qs.length = (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum →
      RunsAll E (phs.foldlM (parseTraceAdvicePhase E vk) acc)
        (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  intro phs
  induction phs with
  | nil =>
      intro acc Qs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using RunsAll.pure E acc
  | cons ph phs ih =>
      intro acc Qs hlen
      have hsum : Qs.length = (phaseCols vk.cs ph).length +
          (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      set n := (phaseCols vk.cs ph).length with hn
      have hlen1 : (Qs.take n).length = n := by rw [List.length_take]; omega
      have hlen2 : (Qs.drop n).length =
          (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum := by
        rw [List.length_drop, hsum]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      have hb := RunsAll.bind E (ms₁ := (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (ms₂ := (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (runsAll_parseTraceAdvicePhase E vk hsp acc ph (Qs.take n) (by rw [hlen1, hn]))
        (fun st' => ih st' (Qs.drop n) hlen2)
      exact hb

/-- **THE ADVICE-PHASE RUN.** At the deployed profile the advice loop reads one G1 group per phase,
    its length the phase's column count. -/
theorem runsAll_parseTraceAdvicePhases_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0)
    (Qs : List G₁)
    (hlen : Qs.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum) :
    RunsAll E (parseTraceAdvicePhases E vk)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) :=
  runsAll_parseTraceAdvicePhases E vk hsp vk.cs.phases _ Qs hlen

theorem runsAll_fmap (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    {m : TranscriptM α} {f : α → β} {ms : List (Msg (Fr p) G₁)}
    (hm : RunsAll E m ms) :
    RunsAll E (f <$> m) ms := by
  have hb := RunsAll.bind E (ms₁ := ms) (ms₂ := []) hm (fun a => RunsAll.pure E (f a))
  rw [List.append_nil] at hb
  exact hb

theorem runsAll_hashInto (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) :
    RunsAll E vk.hashInto [] := by
  show RunsAll E (tmCommon hashableFr vk.transcriptRepr) []
  exact RunsAll.common E hashableFr _

theorem runsAll_tmCommon_yield (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type}
    (h : Midfall.Halo2.Hashable T) (x : T) (b : PUnit) :
    RunsAll E (do tmCommon h x; pure (ForInStep.yield b)) [] := by
  show RunsAll E (tmCommon h x >>= fun _ => pure (ForInStep.yield b)) []
  exact RunsAll.bind E (RunsAll.common E h x) (fun _ => RunsAll.pure E _)

theorem runsAll_fold_forIn (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} :
    ∀ (xs : List α) (g : α → β → TranscriptM (ForInStep β)),
      (∀ a b, RunsAll E (g a b) []) →
      ∀ (init : ForInStep β),
        RunsAll E (xs.foldlM (fun b a =>
          match b with
          | .yield b => g a b
          | .done b => (pure (.done b) : TranscriptM (ForInStep β))) init) [] := by
  intro xs
  induction xs with
  | nil =>
      intro g hg init
      simpa only [List.foldlM_nil] using RunsAll.pure E init
  | cons a as ih =>
      intro g hg init
      rw [List.foldlM_cons]
      cases init with
      | done b =>
          have hb : RunsAll E ((match (ForInStep.done b : ForInStep β) with
              | .yield b => g a b
              | .done b => (pure (.done b) : TranscriptM (ForInStep β)))) [] := by
            exact RunsAll.pure E _
          refine RunsAll.bind E hb (fun step => ?_)
          exact ih g hg step
      | yield b =>
          refine RunsAll.bind E (hg a b) (fun step => ?_)
          exact ih g hg step

theorem runsAll_list_forIn_nil (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    (xs : List α) (init : β) (g : α → β → TranscriptM (ForInStep β))
    (hg : ∀ a b, RunsAll E (g a b) []) :
    RunsAll E (forIn xs init g) [] := by
  rw [List.forIn_eq_foldlM]
  exact runsAll_fmap E (runsAll_fold_forIn E xs g hg (.yield init))

theorem runsAll_array_forIn_nil (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    (xs : Array α) (init : β) (g : α → β → TranscriptM (ForInStep β))
    (hg : ∀ a b, RunsAll E (g a b) []) :
    RunsAll E (forIn xs init g) [] := by
  rw [← Array.forIn_toList]
  exact runsAll_list_forIn_nil E xs.toList init g hg

theorem runsAll_absorb_g1_row (E : VerifierEnv p G₁ G₂ Gₜ) (Qs : Array G₁) :
    RunsAll E (forIn Qs PUnit.unit fun com __s => do
        tmCommon (hashableG1 E.g1) com
        pure (ForInStep.yield PUnit.unit)) [] :=
  runsAll_array_forIn_nil E Qs PUnit.unit _ (fun com _ => runsAll_tmCommon_yield E _ com _)

theorem runsAll_absorb_committed (E : VerifierEnv p G₁ G₂ Gₜ) (rows : Array (Array G₁)) :
    RunsAll E (forIn rows PUnit.unit fun row __s => do
        forIn row PUnit.unit fun com __s => do
          tmCommon (hashableG1 E.g1) com
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) [] :=
  runsAll_array_forIn_nil E rows PUnit.unit _ (fun row _ => by
    show RunsAll E ((forIn row PUnit.unit fun com __s => do
        tmCommon (hashableG1 E.g1) com
        pure (ForInStep.yield PUnit.unit)) >>= fun _ => pure (ForInStep.yield PUnit.unit)) []
    exact RunsAll.bind E (runsAll_absorb_g1_row E row)
      (fun _ => RunsAll.pure E _))

theorem runsAll_absorb_fr_row (E : VerifierEnv p G₁ G₂ Gₜ) (xs : Array (Fr p)) :
    RunsAll E (forIn xs PUnit.unit fun v __s => do
        tmCommon (hashableFr (p := p)) v
        pure (ForInStep.yield PUnit.unit)) [] :=
  runsAll_array_forIn_nil E xs PUnit.unit _ (fun v _ => runsAll_tmCommon_yield E _ v _)

theorem runsAll_absorb_instance_col (E : VerifierEnv p G₁ G₂ Gₜ) (col : Array (Fr p)) :
    RunsAll E (forIn col PUnit.unit fun v __s => do
        tmCommon (hashableFr (p := p)) v
        pure (ForInStep.yield PUnit.unit)) [] :=
  runsAll_array_forIn_nil E col PUnit.unit _ (fun v _ => runsAll_tmCommon_yield E _ v _)

theorem runsAll_absorb_instance_body (E : VerifierEnv p G₁ G₂ Gₜ) (col : Array (Fr p)) :
    RunsAll E (do
        tmCommon (hashableFr (p := p)) (Nat.cast col.size : Fr p)
        forIn col PUnit.unit fun v __s => do
          tmCommon (hashableFr (p := p)) v
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) [] := by
  have hb := RunsAll.bind E (ms₁ := []) (ms₂ := [])
    (RunsAll.common E (hashableFr (p := p)) (Nat.cast col.size : Fr p))
    (fun _ => RunsAll.bind E (ms₁ := []) (ms₂ := [])
      (runsAll_absorb_instance_col E col)
      (fun _ => RunsAll.pure E (ForInStep.yield PUnit.unit)))
  rw [List.append_nil] at hb
  exact hb

theorem runsAll_absorb_instance (E : VerifierEnv p G₁ G₂ Gₜ)
    (rows : Array (Array (Array (Fr p)))) :
    RunsAll E (forIn rows PUnit.unit fun row __s => do
        forIn row PUnit.unit fun col __s => do
          tmCommon (hashableFr (p := p)) (Nat.cast col.size)
          forIn col PUnit.unit fun v __s => do
            tmCommon (hashableFr (p := p)) v
            pure (ForInStep.yield PUnit.unit)
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) [] :=
  runsAll_array_forIn_nil E rows PUnit.unit _ (fun row _ => by
    have hb := RunsAll.bind E (ms₁ := []) (ms₂ := [])
      (runsAll_array_forIn_nil E row PUnit.unit _
        (fun col _ => runsAll_absorb_instance_body E col))
      (fun _ => RunsAll.pure E (ForInStep.yield PUnit.unit))
    rw [List.append_nil] at hb
    exact hb)



def scatStep {α : Type} (n : Nat) (acc : List (Option α)) (e : Nat × α) : List (Option α) :=
  if e.1 < n then acc.take e.1 ++ [some e.2] ++ acc.drop (e.1 + 1) else acc

theorem scatStep_length {α : Type} (n : Nat) (acc : List (Option α)) (e : Nat × α)
    (h : acc.length = n) : (scatStep n acc e).length = n := by
  unfold scatStep
  by_cases he : e.1 < n
  · rw [if_pos he]
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
      List.length_nil, h]
    omega
  · rw [if_neg he]; exact h

theorem scatStep_cover_self {α : Type} (n : Nat) (acc : List (Option α)) (e : Nat × α)
    (h : acc.length = n) (hi : e.1 < n) :
    ∃ a, (scatStep n acc e)[e.1]? = some (some a) := by
  refine ⟨e.2, ?_⟩
  unfold scatStep
  rw [if_pos hi]
  have htake : (acc.take e.1).length = e.1 := by
    rw [List.length_take, h]; omega
  have htake_le : (acc.take e.1).length ≤ e.1 := by omega
  have houter : e.1 < (acc.take e.1 ++ [some e.2]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, htake]; omega
  rw [List.getElem?_append_left houter]
  rw [List.getElem?_append_right htake_le]
  rw [show e.1 - (acc.take e.1).length = 0 by omega]
  rfl

theorem scatStep_cover_other {α : Type} (n : Nat) (acc : List (Option α)) (e : Nat × α)
    (h : acc.length = n) (hi : e.1 < n) {i : Nat} (hij : e.1 ≠ i)
    (hsome : ∃ a, acc[i]? = some (some a)) :
    ∃ a, (scatStep n acc e)[i]? = some (some a) := by
  obtain ⟨a, ha⟩ := hsome
  refine ⟨a, ?_⟩
  unfold scatStep
  rw [if_pos hi]
  have htake : (acc.take e.1).length = e.1 := by
    rw [List.length_take, h]; omega
  by_cases hlt : i < e.1
  · have houter : i < (acc.take e.1 ++ [some e.2]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, htake]; omega
    rw [List.getElem?_append_left houter]
    rw [List.getElem?_append_left (by omega)]
    rw [List.getElem?_take]
    rw [if_pos hlt]
    exact ha
  · have hgt : e.1 < i := by omega
    have houter : (acc.take e.1 ++ [some e.2]).length ≤ i := by
      simp only [List.length_append, List.length_cons, List.length_nil, htake]; omega
    rw [List.getElem?_append_right houter]
    rw [show i - (acc.take e.1 ++ [some e.2]).length = i - (e.1 + 1) by
      simp only [List.length_append, List.length_cons, List.length_nil, htake]]
    rw [List.getElem?_drop]
    rw [show e.1 + 1 + (i - (e.1 + 1)) = i by omega]
    exact ha

theorem scatterIndexed_placed_length {α : Type} (n : Nat) :
    ∀ (pairs : List (Nat × α)) (acc : List (Option α)),
      acc.length = n → (pairs.foldl (scatStep n) acc).length = n := by
  intro pairs
  induction pairs with
  | nil => intro acc h; exact h
  | cons p ps ih =>
      intro acc h
      exact ih (scatStep n acc p) (scatStep_length n acc p h)

theorem scatterIndexed_cover_fold {α : Type} (n : Nat) :
    ∀ (pairs : List (Nat × α)) (acc : List (Option α)),
      acc.length = n →
      ∀ i, i < n →
        ((∃ a, (i, a) ∈ pairs) ∨ (∃ a, acc[i]? = some (some a))) →
        ∃ a', (pairs.foldl (scatStep n) acc)[i]? = some (some a') := by
  intro pairs
  induction pairs with
  | nil =>
      intro acc hacc i hi h
      rcases h with ⟨a, ha⟩ | hsome
      · simp at ha
      · exact hsome
  | cons p ps ih =>
      intro acc hacc i hi h
      rw [List.foldl_cons]
      refine ih (scatStep n acc p) (scatStep_length n acc p hacc) i hi ?_
      by_cases hps : ∃ a, (i, a) ∈ ps
      · exact Or.inl hps
      · rcases h with ⟨a, ha⟩ | hsome
        · rcases List.mem_cons.mp ha with heq | hmem
          · have hp1 : p.1 = i := (congrArg Prod.fst heq).symm
            exact Or.inr (by
              simpa [hp1] using scatStep_cover_self n acc p hacc (by rw [hp1]; exact hi))
          · exact absurd ⟨a, hmem⟩ hps
        · by_cases hpi : p.1 = i
          · exact Or.inr (by
              simpa [hpi] using scatStep_cover_self n acc p hacc (by rw [hpi]; exact hi))
          · by_cases hp : p.1 < n
            · exact Or.inr (scatStep_cover_other n acc p hacc hp hpi hsome)
            · have hstep : scatStep n acc p = acc := by
                unfold scatStep
                rw [if_neg (by omega)]
              rw [hstep]
              exact Or.inr hsome

theorem mapM_id_ok {α : Type} :
    ∀ (l : List (Option α)), (∀ x ∈ l, x ≠ none) →
      ∃ ys, l.mapM (fun x => x) = some ys := by
  intro l
  induction l with
  | nil => intro h; exact ⟨[], rfl⟩
  | cons x xs ih =>
      intro h
      cases x with
      | none => exact absurd rfl (h none (by simp))
      | some a =>
          have hxs : ∀ y ∈ xs, y ≠ none := fun y hy => h y (by simp [hy])
          obtain ⟨ys, hys⟩ := ih hxs
          refine ⟨a :: ys, ?_⟩
          simp only [List.mapM_cons, hys]
          rfl

theorem scatterIndexed_ok_of_cover {α : Type} (n : Nat) (pairs : List (Nat × α))
    (site : String)
    (h : ∀ i, i < n → ∃ a, (i, a) ∈ pairs) :
    ∃ xs, Midfall.Halo2.scatterIndexed n pairs site = .ok xs := by
  unfold Midfall.Halo2.scatterIndexed
  change ∃ xs, (match List.mapM (fun x => x)
      (pairs.foldl (scatStep n) (List.replicate n (none : Option α))) with
    | some xs => Except.ok xs.toArray
    | none => Except.error (Midfall.Halo2.Fault.panic site)) = Except.ok xs
  have hlen0 : (List.replicate n (none : Option α)).length = n := by simp
  have hlen : (pairs.foldl (scatStep n) (List.replicate n none)).length = n :=
    scatterIndexed_placed_length n pairs _ hlen0
  have hsome : ∀ i, i < n →
      ∃ a, (pairs.foldl (scatStep n) (List.replicate n none))[i]? = some (some a) :=
    fun i hi => scatterIndexed_cover_fold n pairs _ hlen0 i hi (Or.inl (h i hi))
  have hnon : ∀ x ∈ pairs.foldl (scatStep n) (List.replicate n none), x ≠ none := by
    intro x hx
    rw [List.mem_iff_getElem?] at hx
    obtain ⟨i, hi⟩ := hx
    have hi' : i < n := by
      by_contra hge
      have hle : (pairs.foldl (scatStep n) (List.replicate n none)).length ≤ i := by omega
      rw [List.getElem?_eq_none_iff.mpr hle] at hi
      cases hi
    obtain ⟨a, ha⟩ := hsome i hi'
    rw [hi] at ha
    intro hx0
    rw [hx0] at ha
    cases ha
  obtain ⟨ys, hys⟩ := mapM_id_ok _ hnon
  rw [hys]
  exact ⟨ys.toArray, rfl⟩

/-- A column index of `cols` is paired with SOME read in `zip cols reads`, provided the read
    array is at least as long as `cols` (`tmReadN_size` supplies this at the advice site). -/
theorem mem_zip_of_mem {α : Type} (cols : List Nat) (reads : List α)
    (hlen : cols.length ≤ reads.length) {i : Nat} (hi : i ∈ cols) :
    ∃ a, (i, a) ∈ List.zip cols reads := by
  rw [List.mem_iff_getElem?] at hi
  obtain ⟨k, hk⟩ := hi
  have hklt : k < cols.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkreads : k < reads.length := by omega
  have hsome : reads[k]? = some reads[k] := List.getElem?_eq_getElem hkreads
  obtain ⟨a, ha⟩ : ∃ a, reads[k]? = some a := ⟨reads[k], hsome⟩
  refine ⟨a, ?_⟩
  rw [List.mem_iff_getElem?]
  exact ⟨k, by rw [List.getElem?_zip_eq_some]; exact ⟨hk, ha⟩⟩



/-! ## 3d. `readAlgebra`'S READ FRAGMENTS

    SIM.10 obligation 2, first pieces. `readFixedEvals`'s no-throw guard is D-GATE14's field;
    the read itself is a homogeneous fr group. -/

theorem runsAll_tmReadN_fr (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (qs : List (Fr p))
    (hlen : qs.length = n) :
    RunsAll E (tmReadN (hashableFr (p := p)) n)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  intro t pref rest hbuf hpos hp henc hwidth
  rw [← ByteArray.append_assoc] at hbuf
  obtain ⟨arr, t', hrun, hpos', hbuf'⟩ :=
    tmReadN_fr_wire E n t pref qs rest hlen hbuf hpos hp
  refine ⟨arr, t', hrun, hbuf', ?_⟩
  simpa only [List.map_map, Function.comp_def] using hpos'

theorem runsAllP_tmReadN_fr (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (qs : List (Fr p))
    (hlen : qs.length = n) :
    RunsAllP E (tmReadN (hashableFr (p := p)) n)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) (fun arr => arr.size = n) := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨arr, t', hrun, hbuf', hpos'⟩ :=
    runsAll_tmReadN_fr E n qs hlen t pref rest hbuf hpos hp henc hwidth
  exact ⟨arr, t', hrun, hbuf', hpos', tmReadN_size (hashableFr (p := p)) n hrun⟩

theorem readFixedEvals_guard (cs : ConstraintSystem (Fr p))
    (h : cs.numSimpleSelectors ≤ cs.numFixedColumns) :
    (if cs.numSimpleSelectors > cs.numFixedColumns then
        (throw (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) : TranscriptM Unit)
      else pure ()) = pure () := by
  rw [if_neg (by omega)]

def readFixedEvalsRead (cs : ConstraintSystem (Fr p)) : TranscriptM (Array (Fr p)) :=
  tmReadN (hashableFr (p := p)) (cs.numFixedColumns - cs.numSimpleSelectors)

theorem runsAllP_readFixedEvalsRead (E : VerifierEnv p G₁ G₂ Gₜ)
    (cs : ConstraintSystem (Fr p)) (qs : List (Fr p))
    (hlen : qs.length = cs.numFixedColumns - cs.numSimpleSelectors) :
    RunsAllP E (readFixedEvalsRead (p := p) cs)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
      (fun arr => arr.size = cs.numFixedColumns - cs.numSimpleSelectors) :=
  runsAllP_tmReadN_fr E _ qs hlen

theorem i32Abs_ok_of_ne_min (x : Int) (h : x ≠ -2147483648) (site : String) :
    ∃ y, Midfall.Halo2.Verifier.i32Abs x site = .ok y := by
  unfold Midfall.Halo2.Verifier.i32Abs
  rw [if_neg h]
  by_cases hx : x < 0
  · rw [if_pos hx]; exact ⟨_, rfl⟩
  · rw [if_neg hx]; exact ⟨_, rfl⟩


theorem listInsertAt_ok_of_le {α : Type} (xs : List α) (i : Nat) (v : α) (site : String)
    (h : i ≤ xs.length) : ∃ ys, Midfall.Halo2.Verifier.listInsertAt xs i v site = .ok ys := by
  unfold Midfall.Halo2.Verifier.listInsertAt
  rw [if_neg (by omega)]
  exact ⟨_, rfl⟩

theorem countP_take_le {α : Type} (l : List α) (p : α → Bool) (k : Nat) :
    (l.take k).countP p ≤ l.countP p := by
  have h : l.countP p = (l.take k).countP p + (l.drop k).countP p := by
    rw [← List.countP_append, List.take_append_drop]
  omega

theorem countP_not_add {α : Type} (l : List α) (p : α → Bool) :
    l.countP p + l.countP (fun x => !p x) = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.countP_cons]
      cases hp : p a <;> simp [hp] at * <;> omega

theorem i32Abs_zero (site : String) : Midfall.Halo2.Verifier.i32Abs 0 site = .ok 0 := by
  unfold Midfall.Halo2.Verifier.i32Abs
  rw [if_neg (by decide), if_neg (by decide)]

/-- The fold-step predicate of `readFixedEvals`. -/
def fpSimple? {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p))
    (s : Nat × (Column × Rotation)) : Bool :=
  cs.hasSimpleSelectorCol s.2.1.index

/-- The range-index property of the steps list. -/
theorem zip_range_fst {α : Type} (l : List α) {k : Nat} (hk : k < l.length) :
    (List.zip (List.range l.length) l)[k]?.map Prod.fst = some k := by
  have hzip : (List.zip (List.range l.length) l)[k]? = some (k, l[k]) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_range hk, List.getElem?_eq_getElem hk⟩
  rw [hzip]
  rfl

def fpInsertStep (cs : ConstraintSystem (Fr p)) (acc : List (Fr p))
    (s : Nat × (Column × Rotation)) : TranscriptM (List (Fr p)) :=
  if cs.hasSimpleSelectorCol s.2.1.index then
    StateT.lift (Midfall.Halo2.Verifier.listInsertAt acc s.1 1
      "proofs/src/plonk/verifier.rs:410")
  else pure acc

theorem fpInsertStep_length (cs : ConstraintSystem (Fr p)) (acc : List (Fr p))
    (s : Nat × (Column × Rotation)) :
    (if cs.hasSimpleSelectorCol s.2.1.index then 1 else 0) +
      acc.length ≤ acc.length + 1 := by
  by_cases h : cs.hasSimpleSelectorCol s.2.1.index <;> simp [h] <;> omega

theorem fpSimple_filter_cons (cs : ConstraintSystem (Fr p))
    (s : Nat × (Column × Rotation)) (ss : List (Nat × (Column × Rotation))) :
    ((s :: ss).filter (fpSimple? cs)).length =
      (if fpSimple? cs s then 1 else 0) + (ss.filter (fpSimple? cs)).length := by
  unfold fpSimple?
  by_cases h : cs.hasSimpleSelectorCol s.2.1.index
  · simp only [List.filter_cons, h, if_true, List.length_cons]; omega
  · simp only [List.filter_cons, h, Bool.false_eq_true, if_false, List.length_cons]; omega

theorem runsAllP_fixed_fold_aux (E : VerifierEnv p G₁ G₂ Gₜ) (cs : ConstraintSystem (Fr p))
    (init : List (Fr p)) (hinit : init.length = cs.numFixedColumns - cs.numSimpleSelectors) :
    ∀ (steps : List (Nat × (Column × Rotation))) (start done : Nat) (acc : List (Fr p)),
      acc.length = init.length + done →
      done ≤ start →
      (∀ k < steps.length, (steps[k]?).map Prod.fst = some (start + k)) →
      start + steps.length ≤ cs.numFixedColumns →
      done + (steps.filter (fpSimple? cs)).length ≥ cs.numSimpleSelectors →
      RunsAllP E (steps.foldlM (fpInsertStep cs) acc) []
        (fun out => out.length = acc.length + (steps.filter (fpSimple? cs)).length) := by
  intro steps
  induction steps with
  | nil =>
      intro start done acc hacc hdone hidx hbound hcount
      refine RunsAllP.pure E acc _ ?_
      simp only [List.foldlM_nil, List.filter_nil, List.length_nil, Nat.add_zero]
  | cons s ss ih =>
      intro start done acc hacc hdone hidx hbound hcount
      have hidx0 : s.1 = start := by
        have h := hidx 0 (by simp)
        simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at h
        exact h
      have hidx_tail : ∀ k < ss.length, (ss[k]?).map Prod.fst = some (start + 1 + k) := by
        intro k hk
        have h := hidx (k + 1) (by simpa using Nat.succ_lt_succ hk)
        rw [List.getElem?_cons_succ] at h
        rw [show start + (k + 1) = start + 1 + k by omega] at h
        exact h
      have hR : (ss.filter (fpSimple? cs)).length ≤ ss.length :=
        List.length_filter_le _ _
      have hcount' : done + (if fpSimple? cs s then 1 else 0) +
          (ss.filter (fpSimple? cs)).length ≥ cs.numSimpleSelectors := by
        have h := fpSimple_filter_cons cs s ss
        rw [h] at hcount
        omega
      have hbound' : start + 1 + ss.length ≤ cs.numFixedColumns := by
        have := hbound
        simp only [List.length_cons] at this
        omega
      have hj : (if fpSimple? cs s then 1 else 0) ≤ 1 := by split <;> omega
      have hstart : s.1 ≤ acc.length := by
        rw [hidx0, hacc, hinit]
        omega
      cases hs : cs.hasSimpleSelectorCol s.2.1.index
      · have hsimple0 : (if fpSimple? cs s then 1 else 0) = 0 := by
          unfold fpSimple?; rw [if_neg (by simp [hs])]
        rw [hsimple0, Nat.add_zero] at hcount'
        have hhead : RunsAllP E (fpInsertStep cs acc s) []
            (fun a => a.length = acc.length + 0) := by
          unfold fpInsertStep
          rw [if_neg (by simp [hs])]
          exact RunsAllP.pure E acc _ (by omega)
        have hdone' : done ≤ start + 1 := by omega
        rw [List.foldlM_cons]
        change RunsAllP E (fpInsertStep cs acc s >>= fun a => ss.foldlM (fpInsertStep cs) a) []
          (fun out => out.length = acc.length + ((s :: ss).filter (fpSimple? cs)).length)
        have hb := RunsAllP.bind E (ms₁ := []) (ms₂ := []) hhead
          (fun a ha => by
            have hacc_a : a.length = init.length + (done + 0) := by rw [ha, hacc]; omega
            have htail := ih (start + 1) (done + 0) a hacc_a hdone' hidx_tail hbound' hcount'
            simpa only [ha, hsimple0, fpSimple_filter_cons, Nat.add_zero, Nat.add_assoc,
              Nat.zero_add] using htail)
        rw [List.append_nil] at hb
        simpa only [hsimple0, fpSimple_filter_cons, Nat.add_zero, Nat.zero_add] using hb
      · have hsimple1 : (if fpSimple? cs s then 1 else 0) = 1 := by
          unfold fpSimple?; rw [if_pos hs]
        rw [hsimple1] at hcount'
        obtain ⟨ys, hys⟩ := listInsertAt_ok_of_le acc s.1 1 _ (by omega)
        have hyslen : ys.length = acc.length + 1 := by
          unfold Midfall.Halo2.Verifier.listInsertAt at hys
          split at hys
          · cases hys
          · rename_i hle
            injection hys with hys'
            rw [← hys']
            simp only [List.length_append, List.length_cons, List.length_nil,
              List.length_take, List.length_drop]
            omega
        have hhead : RunsAllP E (fpInsertStep cs acc s) []
            (fun a => a.length = acc.length + 1) := by
          unfold fpInsertStep
          rw [if_pos hs, hys]
          exact RunsAllP.lift_ok E ys (fun a => a.length = acc.length + 1) hyslen
        have hdone' : done + 1 ≤ start + 1 := by omega
        rw [List.foldlM_cons]
        change RunsAllP E (fpInsertStep cs acc s >>= fun a => ss.foldlM (fpInsertStep cs) a) []
          (fun out => out.length = acc.length + ((s :: ss).filter (fpSimple? cs)).length)
        have hb := RunsAllP.bind E (ms₁ := []) (ms₂ := []) hhead
          (fun a ha => by
            have hacc_a : a.length = init.length + (done + 1) := by rw [ha, hacc]; omega
            have htail := ih (start + 1) (done + 1) a hacc_a hdone' hidx_tail hbound' hcount'
            simpa only [ha, hsimple1, fpSimple_filter_cons, Nat.add_assoc] using htail)
        rw [List.append_nil] at hb
        simpa only [hsimple1, fpSimple_filter_cons, Nat.add_assoc] using hb

theorem filter_snd_zip_length {α β : Type} :
    ∀ (idx : List β) (l : List α), idx.length = l.length →
      ∀ p : α → Bool, ((idx.zip l).filter (fun s => p s.2)).length = (l.filter p).length
  | [], [], _, p => rfl
  | [], _ :: _, h, p => by simp at h
  | _ :: _, [], h, p => by simp at h
  | b :: bs, a :: as, h, p => by
      have hlen : bs.length = as.length := by simpa using h
      rw [List.zip_cons_cons, List.filter_cons, List.filter_cons]
      by_cases hp : p a
      · simp [hp, filter_snd_zip_length bs as hlen p]
      · simp [hp, filter_snd_zip_length bs as hlen p]

theorem runsAllP_fixed_fold (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (init : List (Fr p))
    (hinit : init.length = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors) :
    RunsAllP E
      ((List.zip (List.range vk.cs.fixedQueries.size) vk.cs.fixedQueries.toList).foldlM
        (fpInsertStep vk.cs) init) []
      (fun out => out.length = init.length +
        ((List.zip (List.range vk.cs.fixedQueries.size) vk.cs.fixedQueries.toList).filter
          (fpSimple? vk.cs)).length) := by
  have hlen : (List.zip (List.range vk.cs.fixedQueries.size)
      vk.cs.fixedQueries.toList).length = vk.cs.fixedQueries.toList.length := by
    rw [List.length_zip]; simp
  have hidx : ∀ k < (List.zip (List.range vk.cs.fixedQueries.size)
        vk.cs.fixedQueries.toList).length,
      ((List.zip (List.range vk.cs.fixedQueries.size) vk.cs.fixedQueries.toList)[k]?).map
        Prod.fst = some (0 + k) := by
    intro k hk
    have hk' : k < vk.cs.fixedQueries.toList.length := by rw [← hlen]; exact hk
    simpa using zip_range_fst vk.cs.fixedQueries.toList hk'
  have hbound : 0 + (List.zip (List.range vk.cs.fixedQueries.size)
      vk.cs.fixedQueries.toList).length ≤ vk.cs.numFixedColumns := by
    rw [hlen]
    simpa using hf.fixedQueriesBound
  have hcount : 0 + ((List.zip (List.range vk.cs.fixedQueries.size)
        vk.cs.fixedQueries.toList).filter (fpSimple? vk.cs)).length ≥
      vk.cs.numSimpleSelectors := by
    rw [show ((List.zip (List.range vk.cs.fixedQueries.size)
          vk.cs.fixedQueries.toList).filter (fpSimple? vk.cs)).length =
        (vk.cs.fixedQueries.toList.filter
          (fun q => vk.cs.hasSimpleSelectorCol q.1.index)).length from
      filter_snd_zip_length (List.range vk.cs.fixedQueries.size)
        vk.cs.fixedQueries.toList (by simp)
        (fun q => vk.cs.hasSimpleSelectorCol q.1.index)]
    simpa using hf.simpleSelectorQueriesBound
  exact runsAllP_fixed_fold_aux E vk.cs init hinit _ 0 0 init (by omega) (by omega)
    hidx hbound hcount

theorem runsAllP_readFixedEvals (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (qs : List (Fr p))
    (hlen : qs.length = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors) :
    RunsAllP E (Midfall.Halo2.Verifier.readFixedEvals (p := p) vk.cs)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
      (fun out => out.size = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors +
        ((List.zip (List.range vk.cs.fixedQueries.size) vk.cs.fixedQueries.toList).filter
          (fpSimple? vk.cs)).length) := by
  unfold Midfall.Halo2.Verifier.readFixedEvals
  rw [if_neg (by have := hf.fixedSelectorBound; omega)]
  dsimp only
  have hgrp : RunsAllP E (tmReadN (hashableFr (p := p))
      (vk.cs.numFixedColumns - vk.cs.numSimpleSelectors))
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
      (fun arr => arr.size = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors) :=
    runsAllP_tmReadN_fr E _ qs hlen
  have hb := RunsAllP.bind E (ms₁ := qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) (ms₂ := [])
    hgrp (fun arr ha => by
      have hinit : arr.toList.length =
          vk.cs.numFixedColumns - vk.cs.numSimpleSelectors := by
        rw [Array.length_toList]; exact ha
      have hfold := runsAllP_fixed_fold E vk hf arr.toList hinit
      have hb2 := RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := []) hfold
        (fun out hout => RunsAllP.pure E out.toArray
          (fun a : Array (Fr p) => a.size = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors +
            ((List.zip (List.range vk.cs.fixedQueries.size)
              vk.cs.fixedQueries.toList).filter (fpSimple? vk.cs)).length)
          (by rw [List.size_toArray, hout, hinit]))
      rw [List.nil_append] at hb2
      simpa using hb2)
  rw [List.append_nil] at hb
  exact hb

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem runsAll_readFixedEvals (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (qs : List (Fr p))
    (hlen : qs.length = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors) :
    RunsAll E (Midfall.Halo2.Verifier.readFixedEvals (p := p) vk.cs)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) :=
  (runsAllP_readFixedEvals E vk hf qs hlen).toRunsAll

theorem runsAll_read_fr (E : VerifierEnv p G₁ G₂ Gₜ) (q : Fr p) :
    RunsAll E (Midfall.Halo2.tmRead (Midfall.Halo2.hashableFr (p := p)))
      ([Msg.fr q] : List (Msg (Fr p) G₁)) := by
  intro t pref rest hbuf hpos hp henc hwidth
  have hbuf' : t.buffer = pref ++ msgWire E (Msg.fr q) ++ rest := by
    simpa only [wireMsgs_cons, wireMsgs, ByteArray.append_empty, bytes_empty_append_local,
      ByteArray.append_assoc] using hbuf
  have hbt : bytesTake t.buffer t.pos 32 = some (frToRepr (p := p) q) := by
    rw [hbuf', hpos, ← Nat.add_zero (ByteArray.size pref), ByteArray.append_assoc]
    simp only [msgWire]
    rw [bytesTake_append_right pref (frToRepr (p := p) q ++ rest) 0 32 (by
      rw [ByteArray.size_append, frToRepr_size]; omega)]
    rw [bytesTake_append_left (frToRepr (p := p) q) rest 0 32 (by
      rw [frToRepr_size])]
    rw [← frToRepr_size q, bytesTake_whole]
  obtain ⟨t', hrun, hpos', hbuf'⟩ :=
    tmRead_run_ok (Midfall.Halo2.hashableFr (p := p)) t (frToRepr (p := p) q) q hbt
      (by rw [hashableFr_readRepr?]; exact frOfRepr_frToRepr hp q)
  refine ⟨q, t', hrun, hbuf', ?_⟩
  rw [hpos', hashableFr_width, hpos]
  show pref.size + 32 = pref.size + (([Msg.fr q] : List (Msg (Fr p) G₁)).map
    (fun m => (msgWire E m).size)).sum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, msgWire,
    frToRepr_size]
  omega

theorem runsAll_permutationCommon (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : Midfall.Halo2.VerifyingKey (Fr p) G₁) (qs : List (Fr p))
    (hlen : qs.length = vk.permutation.commitments.size) :
    RunsAll E (Permutation.VerifyingKey.evaluate (p := p) vk.permutation)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  unfold Permutation.VerifyingKey.evaluate
  have hb := RunsAllP.toRunsAll E (runsAllP_tmReadN_fr E vk.permutation.commitments.size qs hlen)
  have hb2 := RunsAll.bind E (ms₁ := qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) (ms₂ := [])
    hb (fun arr => RunsAll.pure E ({ permutationEvals := arr } : Permutation.CommonEvaluated (Fr p)))
  rw [List.append_nil] at hb2
  exact hb2

theorem runsAll_trashEval (E : VerifierEnv p G₁ G₂ Gₜ) (t : Trash.Committed G₁)
    (q : Fr p) :
    RunsAll E (Trash.Committed.evaluate (p := p) t)
      ([Msg.fr q] : List (Msg (Fr p) G₁)) := by
  unfold Trash.Committed.evaluate
  have hb := RunsAll.bind E (ms₁ := ([Msg.fr q] : List (Msg (Fr p) G₁))) (ms₂ := [])
    (runsAll_read_fr E q)
    (fun e => RunsAll.pure E
      ({ committed := t, evaluated := { trashEval := e } } : Trash.Evaluated (Fr p) G₁))
  rw [List.append_nil] at hb
  exact hb

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem rotBounds_zero :
    ∀ (qs : List (Column × Rotation)), (∀ q ∈ qs, q.2.int = 0) →
      qs.foldl (init := ((0 : Int), (0 : Int))) (fun st q =>
        let r := q.2.int
        if r < st.1 then (r, st.2) else if r > st.2 then (st.1, r) else st) = (0, 0) := by
  intro qs
  induction qs with
  | nil => intro h; rfl
  | cons q qs ih =>
      intro h
      rw [List.foldl_cons]
      have hq : q.2.int = 0 := h q (by simp)
      have hqs : ∀ q' ∈ qs, q'.2.int = 0 := fun q' h' => h q' (by simp [h'])
      have hstate : (let r := q.2.int
          if r < ((0 : Int), (0 : Int)).1 then (r, ((0:Int),(0:Int)).2)
          else if r > ((0:Int),(0:Int)).2 then (((0:Int),(0:Int)).1, r)
          else ((0:Int),(0:Int))) = ((0:Int),(0:Int)) := by
        rw [hq]; rfl
      rw [hstate]
      exact ih hqs

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **D-GATE15(b) SPENT.** Under `WellFormed.instanceRotZero`, `readAlgebra`'s
    `rotBounds` fold is `(0, 0)`: `minRot = maxRot = 0` and `i32Abs 0` succeeds. -/
theorem readAlgebra_rotBounds_zero (vk : VerifyingKey (Fr p) G₁)
    (hf : vk.WellFormed Features.solidity) :
    vk.cs.instanceQueries.toList.foldl (init := ((0 : Int), (0 : Int))) (fun st q =>
      let r := q.2.int
      if r < st.1 then (r, st.2) else if r > st.2 then (st.1, r) else st) = (0, 0) :=
  rotBounds_zero _ (fun q hq => hf.instanceRotZero q hq)

theorem runsAll_logupEval (E : VerifierEnv p G₁ G₂ Gₜ) (cm : Logup.Committed G₁)
    (qs : List (Fr p)) (hlen : qs.length = cm.helperPolys.size + 3) :
    RunsAll E (Logup.Committed.evaluate (p := p) cm)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  unfold Logup.Committed.evaluate
  obtain ⟨q0, rest, rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; omega)
  have hrest : rest.length = cm.helperPolys.size + 2 := by simp at hlen; omega
  set nb := cm.helperPolys.size with hnb
  have htake : (rest.take nb).length = nb := by rw [List.length_take]; omega
  have hdrop : (rest.drop nb).length = 2 := by rw [List.length_drop]; omega
  obtain ⟨q1, q2', hq2⟩ := List.exists_cons_of_length_pos (by rw [hdrop]; omega)
  have hq2' : q2'.length = 1 := by
    rw [hq2, List.length_cons] at hdrop; omega
  obtain ⟨q2, hq2''⟩ := List.length_eq_one_iff.mp hq2'
  rw [hq2''] at hq2
  have hsplit : rest.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) =
      (rest.take nb).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ((rest.drop nb).map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
    rw [← List.map_append, List.take_append_drop]
  have hgrp := runsAll_tmReadN_fr E nb (rest.take nb) htake
  have htail : ∀ m : Fr p, RunsAll E
      (tmReadN (hashableFr (p := p)) nb >>= fun helperEvals =>
        Midfall.Halo2.tmRead (hashableFr (p := p)) >>= fun accumulatorEval =>
          Midfall.Halo2.tmRead (hashableFr (p := p)) >>= fun accumulatorNextEval =>
            (pure ({ committed := cm, evaluated :=
              { multiplicitiesEval := m, helperEvals := helperEvals,
                accumulatorEval := accumulatorEval,
                accumulatorNextEval := accumulatorNextEval } } :
              Logup.Evaluated (Fr p) G₁)))
      (rest.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
    intro m
    rw [hsplit, hq2]
    simp only [List.map_cons, List.map_nil]
    refine RunsAll.bind E (ms₁ := (rest.take nb).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
      (ms₂ := [Msg.fr q1, Msg.fr q2]) ?_ ?_
    · convert hgrp using 2
    · intro helperEvals
      refine RunsAll.bind E (ms₁ := ([Msg.fr q1] : List (Msg (Fr p) G₁))) (ms₂ := [Msg.fr q2]) ?_ ?_
      · exact runsAll_read_fr E q1
      · intro accumulatorEval
        refine RunsAll.bind E (ms₁ := ([Msg.fr q2] : List (Msg (Fr p) G₁))) (ms₂ := []) ?_ ?_
        · exact runsAll_read_fr E q2
        · intro accumulatorNextEval
          exact RunsAll.pure E _
  have hb := RunsAll.bind E (ms₁ := ([Msg.fr q0] : List (Msg (Fr p) G₁)))
    (ms₂ := rest.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) (runsAll_read_fr E q0)
    (fun m => htail m)
  simpa only [List.map_cons, List.map_nil, List.singleton_append] using hb

theorem RunsAll.toRunsAllP (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type}
    {m : TranscriptM α} {ms : List (Msg (Fr p) G₁)} (h : RunsAll E m ms) :
    RunsAllP E m ms (fun _ => True) := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨a, t', hrun, hbuf', hpos'⟩ := h t pref rest hbuf hpos hp henc hwidth
  exact ⟨a, t', hrun, hbuf', hpos', trivial⟩

theorem runsAllP_fold_forIn_yield (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} :
    ∀ (xs : List α) (f : α → β → TranscriptM (ForInStep β))
      (msOf : α → List (Msg (Fr p) G₁)),
      (∀ a ∈ xs, ∀ b, RunsAllP E (f a b) (msOf a)
        (fun step => ∃ b', step = ForInStep.yield b')) →
      ∀ (init : β),
        RunsAll E (xs.foldlM (fun b a =>
          match b with
          | ForInStep.yield b => f a b
          | ForInStep.done b => (pure (ForInStep.done b) : TranscriptM (ForInStep β)))
          (ForInStep.yield init))
          (xs.flatMap msOf) := by
  intro xs
  induction xs with
  | nil =>
      intro f msOf hf init
      simpa only [List.foldlM_nil, List.flatMap_nil] using RunsAll.pure E (ForInStep.yield init)
  | cons a as ih =>
      intro f msOf hf init
      rw [List.foldlM_cons, List.flatMap_cons]
      have hf' : ∀ a' ∈ as, ∀ b, RunsAllP E (f a' b) (msOf a')
          (fun step => ∃ b', step = ForInStep.yield b') :=
        fun a' ha' => hf a' (by simp [ha'])
      have hb : RunsAllP E (List.foldlM
          (fun b a =>
            match b with
            | ForInStep.yield b => f a b
            | ForInStep.done b => pure (ForInStep.done b))
          (ForInStep.yield init) (a :: as)) (msOf a ++ as.flatMap msOf) (fun _ => True) :=
        RunsAllP.bind E (ms₁ := msOf a) (ms₂ := as.flatMap msOf) (hf a (by simp) init)
          (fun step hstep => by
            obtain ⟨b', rfl⟩ := hstep
            exact RunsAll.toRunsAllP E (ih f msOf hf' b'))
      exact hb.toRunsAll

theorem runsAll_forIn_yield (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    (xs : List α) (init : β) (f : α → β → TranscriptM (ForInStep β))
    (msOf : α → List (Msg (Fr p) G₁))
    (hf : ∀ a ∈ xs, ∀ b, RunsAllP E (f a b) (msOf a)
      (fun step => ∃ b', step = ForInStep.yield b')) :
    RunsAll E (forIn xs init f) (xs.flatMap msOf) := by
  rw [List.forIn_eq_foldlM]
  exact runsAll_fmap E (runsAllP_fold_forIn_yield E xs f msOf hf init)



def permSeg {α : Type} (l : List α) (n i : Nat) : List α :=
  (l.drop (3 * i)).take (if i < n - 1 then 3 else 2)

theorem permSeg_succ {α : Type} (l : List α) (m j : Nat) :
    permSeg l (Nat.succ (Nat.succ m)) (Nat.succ j) =
      permSeg (l.drop 3) (Nat.succ m) j := by
  unfold permSeg
  have hdrop : l.drop (3 * Nat.succ j) = (l.drop 3).drop (3 * j) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hdrop]
  by_cases hj : j < Nat.succ m - 1
  · rw [if_pos hj, if_pos (by omega)]
  · rw [if_neg hj, if_neg (by omega)]

theorem flatMap_permSeg {α : Type} :
    ∀ (n : Nat) (l : List α), l.length = 3 * n - 1 →
      (List.range n).flatMap (permSeg l n) = l := by
  intro n
  induction n with
  | zero =>
      intro l hlen
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hl
      rfl
  | succ n ih =>
      intro l hlen
      cases n with
      | zero =>
          have hlen2 : l.length = 2 := by simpa using hlen
          rw [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          show List.take (if (0 : Nat) < 1 - 1 then 3 else 2) l = l
          rw [if_neg (by omega), List.take_of_length_le (by omega)]
      | succ m =>
          rw [List.range_succ_eq_map, List.flatMap_cons]
          show List.take (if (0 : Nat) < Nat.succ (Nat.succ m) - 1 then 3 else 2) l ++
            (List.map Nat.succ (List.range (Nat.succ m))).flatMap
              (permSeg l (Nat.succ (Nat.succ m))) = l
          rw [if_pos (by omega), List.flatMap_map]
          have hcongr : (List.range (Nat.succ m)).flatMap
                (fun j => permSeg l (Nat.succ (Nat.succ m)) (Nat.succ j)) =
              (List.range (Nat.succ m)).flatMap (permSeg (l.drop 3) (Nat.succ m)) := by
            apply List.flatMap_congr
            intro j _
            exact permSeg_succ l m j
          rw [hcongr]
          have hdrop : (l.drop 3).length = 3 * Nat.succ m - 1 := by
            rw [List.length_drop]
            omega
          rw [ih (l.drop 3) hdrop]
          rw [List.take_append_drop]



theorem runsAll_permutationEval (E : VerifierEnv p G₁ G₂ Gₜ)
    (coms : Permutation.Committed G₁) (qs : List (Fr p))
    (hlen : qs.length = 3 * coms.permutationProductCommitments.size - 1) :
    RunsAll E (Permutation.Committed.evaluate (p := p) coms)
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  unfold Permutation.Committed.evaluate
  set k := coms.permutationProductCommitments.size with hk
  dsimp only
  let msOf : Nat → List (Msg (Fr p) G₁) :=
    fun i => (permSeg qs k i).map (fun q => (Msg.fr q : Msg (Fr p) G₁))
  have hseg : ∀ i < k, (permSeg qs k i).length = (if i < k - 1 then 3 else 2) := by
    intro i hi
    unfold permSeg
    rw [List.length_take, List.length_drop]
    by_cases h : i < k - 1
    · rw [if_pos h]
      rw [Nat.min_eq_left]
      omega
    · rw [if_neg h]
      have hik : i = k - 1 := by omega
      rw [hik]
      rw [Nat.min_eq_right]
      · omega
      · omega
  have hbody : ∀ i ∈ List.range k, ∀ s : Array (Permutation.SetEvaluated (Fr p)),
      RunsAllP E (do
        let permutationProductEval ← tmRead (hashableFr (p := p))
        let permutationProductNextEval ← tmRead (hashableFr (p := p))
        if i < k - 1 then do
          let e ← tmRead (hashableFr (p := p))
          let permutationProductLastEval ← pure (some e)
          pure (ForInStep.yield (s.push
            { permutationProductEval := permutationProductEval,
              permutationProductNextEval := permutationProductNextEval,
              permutationProductLastEval := permutationProductLastEval }))
        else do
          let permutationProductLastEval ← pure none
          pure (ForInStep.yield (s.push
            { permutationProductEval := permutationProductEval,
              permutationProductNextEval := permutationProductNextEval,
              permutationProductLastEval := permutationProductLastEval })))
        (msOf i) (fun step => ∃ b', step = ForInStep.yield b') := by
    intro i hi s
    have hik : i < k := List.mem_range.mp hi
    by_cases h : i < k - 1
    · have h3 : (permSeg qs k i).length = 3 := by
        rw [hseg i hik, if_pos h]
      obtain ⟨a, b, c, hseg3⟩ := List.length_eq_three.mp h3
      dsimp only [msOf]
      rw [hseg3]
      simp only [List.map_cons, List.map_nil]
      simp only [if_pos h]
      simp only [pure_bind]
      refine RunsAllP.bind E (ms₁ := ([Msg.fr a] : List (Msg (Fr p) G₁)))
        (ms₂ := [Msg.fr b, Msg.fr c]) (RunsAll.toRunsAllP E (runsAll_read_fr E a)) ?_
      intro ppe _
      refine RunsAllP.bind E (ms₁ := ([Msg.fr b] : List (Msg (Fr p) G₁)))
        (ms₂ := [Msg.fr c]) (RunsAll.toRunsAllP E (runsAll_read_fr E b)) ?_
      intro ppn _
      refine RunsAllP.bind E (ms₁ := ([Msg.fr c] : List (Msg (Fr p) G₁)))
        (ms₂ := []) (RunsAll.toRunsAllP E (runsAll_read_fr E c)) ?_
      intro e _
      exact RunsAllP.pure E _ _ ⟨_, rfl⟩
    · have h2 : (permSeg qs k i).length = 2 := by
        rw [hseg i hik, if_neg h]
      obtain ⟨a, b, hseg2⟩ := List.length_eq_two.mp h2
      dsimp only [msOf]
      rw [hseg2]
      simp only [List.map_cons, List.map_nil]
      simp only [if_neg h]
      simp only [pure_bind]
      refine RunsAllP.bind E (ms₁ := ([Msg.fr a] : List (Msg (Fr p) G₁)))
        (ms₂ := [Msg.fr b]) (RunsAll.toRunsAllP E (runsAll_read_fr E a)) ?_
      intro ppe _
      refine RunsAllP.bind E (ms₁ := ([Msg.fr b] : List (Msg (Fr p) G₁)))
        (ms₂ := []) (RunsAll.toRunsAllP E (runsAll_read_fr E b)) ?_
      intro ppn _
      exact RunsAllP.pure E _ _ ⟨_, rfl⟩
  have hloop : RunsAll E
      (forIn (List.range k) (#[] : Array (Permutation.SetEvaluated (Fr p)))
        (fun i __s => do
          let permutationProductEval ← tmRead (hashableFr (p := p))
          let permutationProductNextEval ← tmRead (hashableFr (p := p))
          if i < k - 1 then do
            let e ← tmRead (hashableFr (p := p))
            let permutationProductLastEval ← pure (some e)
            pure (ForInStep.yield (__s.push
              { permutationProductEval := permutationProductEval,
                permutationProductNextEval := permutationProductNextEval,
                permutationProductLastEval := permutationProductLastEval }))
          else do
            let permutationProductLastEval ← pure none
            pure (ForInStep.yield (__s.push
              { permutationProductEval := permutationProductEval,
                permutationProductNextEval := permutationProductNextEval,
                permutationProductLastEval := permutationProductLastEval }))))
      ((List.range k).flatMap msOf) :=
    runsAll_forIn_yield E (List.range k) _ _ msOf hbody
  have hb := RunsAll.bind E (ms₁ := (List.range k).flatMap msOf) (ms₂ := []) hloop
    (fun s => RunsAll.pure E ({ coms := coms, sets := s } : Permutation.Evaluated (Fr p) G₁))
  rw [List.append_nil] at hb
  rw [show ((List.range k).flatMap msOf) = qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) from by
    rw [← List.map_flatMap, flatMap_permSeg k qs (by simpa using hlen)]] at hb
  exact hb



theorem runsAll_readAlgebraAdviceEvals (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) :
    ∀ (numProofs : Nat) (qs : List (Fr p)),
      qs.length = numProofs * vk.cs.adviceQueries.size →
      RunsAll E ((List.range numProofs).mapM (fun _ =>
        tmReadN (hashableFr (p := p)) vk.cs.adviceQueries.size))
        (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  intro numProofs
  induction numProofs with
  | zero =>
      intro qs hlen
      have h0 : qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      simpa only [List.range_zero, List.mapM_nil, List.map_nil] using
        RunsAll.pure E ([] : List (Array (Fr p)))
  | succ n ih =>
      intro qs hlen
      set sz := vk.cs.adviceQueries.size with hsz
      have hlen' : qs.length = sz + n * sz := by
        rw [hlen]; rw [Nat.succ_mul]; omega
      have htake : (qs.take sz).length = sz := by rw [List.length_take]; omega
      have hdrop : (qs.drop sz).length = n * sz := by rw [List.length_drop]; omega
      have hsplit : qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) =
          (qs.take sz).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (qs.drop sz).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
      have hcomp : ((fun _ => tmReadN (hashableFr (p := p)) sz) ∘ Nat.succ) =
          (fun _ => tmReadN (hashableFr (p := p)) sz) := rfl
      rw [hcomp]
      refine RunsAll.bind E (ms₁ := (qs.take sz).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (qs.drop sz).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (runsAll_tmReadN_fr E sz (qs.take sz) htake) ?_
      intro head
      have hb := RunsAll.bind E (ms₁ := (qs.drop sz).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := []) (ih (qs.drop sz) hdrop) (fun tail => RunsAll.pure E (head :: tail))
      rw [List.append_nil] at hb
      exact hb

theorem foldr_pair_snd_length {F : Type} [Mul F] [Zero F] [DecidableEq F]
    (l : List (F × F)) (a : F) :
    (l.foldr (fun q st => (if q.2 = 0 then st.1 else st.1 * q.2,
        (if q.2 = 0 then q.2 else q.1 * st.1) :: st.2)) (a, [])).2.length = l.length := by
  induction l with
  | nil => rfl
  | cons q l ih => simp only [List.foldr_cons, List.length_cons, ih]

theorem foldl_forward_snd_length {F : Type} [Mul F] [Zero F] [DecidableEq F]
    (xs : List F) (st : F × List (F × F)) :
    (xs.foldl (fun st p => (if p = 0 then st.1 else st.1 * p, st.2 ++ [(st.1, p)])) st).2.length =
      st.2.length + xs.length := by
  induction xs generalizing st with
  | nil => simp
  | cons a as ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem batchInvert_fst_size_direct {F : Type} [Field F] [DecidableEq F] (xs : List F) :
    (batchInvert xs.toArray).1.size = xs.length := by
  unfold batchInvert
  dsimp only
  rw [List.size_toArray, foldr_pair_snd_length]
  rw [foldl_forward_snd_length]
  simp

theorem lIRange_size (d : EvaluationDomain (Fr p)) (x xn : Fr p) (rots : List Int) :
    (d.lIRange x xn rots).size = rots.length := by
  unfold EvaluationDomain.lIRange
  dsimp only
  rw [List.size_toArray, List.length_zipWith]
  have hres : (batchInvert ((rots.map fun r => x - d.rotateOmega 1 (Rotation.value r)).toArray)).1.toList.length
      = rots.length := by
    rw [Array.length_toList, batchInvert_fst_size_direct (F := Fr p), List.length_map]
  rw [hres, Nat.min_eq_right (Nat.le_refl _)]

theorem asI32_eq_of_lt {n : Nat} (h : n < 2 ^ 31) :
    Permutation.asI32 n = (n : Int) := by
  unfold Permutation.asI32 Permutation.wrapI32
  dsimp only
  have h1 : (Int.ofNat n % 4294967296) = Int.ofNat n := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg n
    · show Int.ofNat n < Int.ofNat 4294967296
      exact Int.ofNat_lt.mpr (by omega)
  rw [h1]
  rw [if_pos (by
    show Int.ofNat n < Int.ofNat 2147483648
    exact Int.ofNat_lt.mpr (by omega))]
  rfl

theorem wrapI32_eq_of_nonneg_of_lt {x : Int} (hlo : 0 ≤ x) (hhi : x < 2147483648) :
    Permutation.wrapI32 x = x := by
  unfold Permutation.wrapI32
  have h1 : x % 4294967296 = x := by
    rw [Int.emod_eq_of_lt] <;> omega
  dsimp only
  rw [h1]
  rw [if_pos hhi]

theorem negI32_zero : Permutation.negI32 0 = 0 := by
  unfold Permutation.negI32 Permutation.wrapI32
  norm_num

theorem le_foldl_max_of_mem_or_le :
    ∀ (l : List Nat) (a x : Nat), x ≤ a ∨ x ∈ l → x ≤ l.foldl max a := by
  intro l
  induction l with
  | nil =>
      intro a x h
      rcases h with h | h
      · simpa using h
      · simp at h
  | cons b bs ih =>
      intro a x h
      rw [List.foldl_cons]
      apply ih (max a b) x
      rcases h with h | h
      · exact Or.inl (Nat.le_trans h (Nat.le_max_left a b))
      · rw [List.mem_cons] at h
        rcases h with hxb | hmem
        · rw [hxb]
          exact Or.inl (Nat.le_max_right a _)
        · exact Or.inr hmem

/-- `readAlgebra`'s `max_instance_len` (`verifier.rs:340-344`). -/
def maxInstanceLen {p : ℕ} (instances : Array (Array (Array (Fr p)))) : Nat :=
  (instances.toList.flatMap (fun row => row.toList.map (fun col => col.size))).foldl (init := 0) max

/-- The `l_i_range` window rotations at `minRot = maxRot = 0`. -/
def zeroRotations (n : Nat) : List Int := (List.range n).map (fun i => (i : Int))

theorem maxInstanceLen_bound (instances : Array (Array (Array (Fr p))))
    (row : Array (Array (Fr p))) (hrow : row ∈ instances.toList)
    (col : Array (Fr p)) (hcol : col ∈ row.toList) :
    col.size ≤ maxInstanceLen instances := by
  unfold maxInstanceLen
  apply le_foldl_max_of_mem_or_le
  right
  rw [List.mem_flatMap]
  exact ⟨row, hrow, List.mem_map.mpr ⟨col, hcol, rfl⟩⟩

theorem zeroRotations_length (n : Nat) : (zeroRotations n).length = n := by
  simp [zeroRotations]

theorem readAlgebra_rotations_zero (n : Nat) (hmax : n < 2 ^ 31) :
    (if Permutation.wrapI32 (Permutation.asI32 n + 0) > Permutation.negI32 0 then
      (List.range ((Permutation.wrapI32 (Permutation.asI32 n + 0) - Permutation.negI32 0).toNat)).map
        (fun i => Permutation.negI32 0 + (i : Int))
     else []) = zeroRotations n := by
  rw [negI32_zero, asI32_eq_of_lt hmax, Int.add_zero]
  have hw : Permutation.wrapI32 (n : Int) = (n : Int) :=
    wrapI32_eq_of_nonneg_of_lt (Int.natCast_nonneg n)
      (by show Int.ofNat n < Int.ofNat 2147483648; exact Int.ofNat_lt.mpr (by omega))
  rw [hw]
  split
  · rw [Int.sub_zero, Int.toNat_natCast]
    simp [zeroRotations, Int.zero_add]
  · rename_i hneg
    have hn : n = 0 := by
      have h : ¬ (0 < n) := fun h => hneg (Int.ofNat_lt.mpr h)
      omega
    subst hn
    simp [zeroRotations]

theorem lIS_slice_length (d : EvaluationDomain (Fr p)) (x xn : Fr p)
    (n : Nat) (hmax : n < 2 ^ 31) (col : Array (Fr p)) (hcol : col.size ≤ n) :
    (((d.lIRange x xn (zeroRotations n)).toList.drop ((0 : Int) - 0).toNat).take col.size).length
      = col.size := by
  have hlen : (d.lIRange x xn (zeroRotations n)).toList.length = n := by
    rw [Array.length_toList, lIRange_size, zeroRotations_length]
  rw [show ((0 : Int) - 0).toNat = 0 from rfl, List.drop_zero, List.length_take, hlen,
    Nat.min_eq_left hcol]



/-- **THE `lIS` SLICE GUARD, DISCHARGED.** Under D-GATE15 `instanceRotZero`, every
    instance query's rotation is `0`, so the `l_i_range` offset is `0`; the slice is
    `col.size` long because `col.size` is bounded by the fold-max over all instance
    column lengths and `l_i_range` keeps its rotation list's length. The runtime
    cast identity is `maxInstanceLen < 2^31` (the walk's `inst.size` bound). -/
theorem readAlgebra_instanceSlice_safe (vk : VerifyingKey (Fr p) G₁)
    (hf : vk.WellFormed Features.solidity) (nbCommitted : Nat)
    (instances : Array (Array (Array (Fr p))))
    (hmax : maxInstanceLen instances < 2 ^ 31) (x xn : Fr p)
    (row : Array (Array (Fr p))) (hrow : row ∈ instances.toList)
    (q : Column × Rotation) (hq : q ∈ vk.cs.instanceQueries.toList)
    (col : Array (Fr p)) (hcol : row[q.1.index - nbCommitted]? = some col) :
    (((vk.domain.lIRange x xn (zeroRotations (maxInstanceLen instances))).toList.drop
      (0 - q.2.int).toNat).take col.size).length = col.size := by
  have hq0 : q.2.int = 0 := hf.instanceRotZero q hq
  have hcolmem : col ∈ row.toList :=
    Array.mem_toList_iff.mpr ((Array.mem_iff_getElem?).mpr ⟨_, hcol⟩)
  have hle : col.size ≤ maxInstanceLen instances :=
    maxInstanceLen_bound instances row hrow col hcolmem
  rw [hq0]
  exact lIS_slice_length vk.domain x xn _ hmax col hle

def readAlgebraOneInstanceQuery (row : Array (Array (Fr p))) (nbCommitted : Nat)
    (maxRot : Int) (lIS : Array (Fr p)) (q : Column × Rotation) : TranscriptM (Fr p) := do
  if q.1.index < nbCommitted then
    tmRead (hashableFr (p := p))
  else
    let colIdx := q.1.index - nbCommitted
    match row[colIdx]? with
    | none => throw (Fault.panic "proofs/src/plonk/verifier.rs:366")
    | some col =>
      let offset := (maxRot - q.2.int).toNat
      let slice := (lIS.toList.drop offset).take col.size
      unless slice.length == col.size do
        throw (Fault.panic "proofs/src/plonk/verifier.rs:370")
      StateT.lift (computeInnerProduct col slice.toArray)

theorem computeInnerProduct_ok_of_size {F : Type} [Field F] (a b : Array F)
    (h : a.size = b.size) :
    ∃ x, computeInnerProduct a b = .ok x := by
  unfold computeInnerProduct
  have hb : (a.size == b.size) = true := by rw [beq_iff_eq]; exact h
  simp only [hb, if_true, pure_bind]
  exact ⟨_, rfl⟩

theorem runsAll_readAlgebraOneInstanceQuery_committed (E : VerifierEnv p G₁ G₂ Gₜ)
    (row : Array (Array (Fr p))) (nbCommitted : Nat) (maxRot : Int) (lIS : Array (Fr p))
    (q : Column × Rotation) (h : q.1.index < nbCommitted) (v : Fr p) :
    RunsAll E (readAlgebraOneInstanceQuery (p := p) row nbCommitted maxRot lIS q)
      ([Msg.fr v] : List (Msg (Fr p) G₁)) := by
  unfold readAlgebraOneInstanceQuery
  rw [if_pos h]
  exact runsAll_read_fr E v

theorem runsAll_readAlgebraOneInstanceQuery_notCommitted (E : VerifierEnv p G₁ G₂ Gₜ)
    (row : Array (Array (Fr p))) (nbCommitted : Nat) (maxRot : Int) (lIS : Array (Fr p))
    (q : Column × Rotation) (h : ¬ q.1.index < nbCommitted)
    (col : Array (Fr p)) (hrow : row[q.1.index - nbCommitted]? = some col)
    (hslice : ((lIS.toList.drop (maxRot - q.2.int).toNat).take col.size).length = col.size) :
    RunsAll E (readAlgebraOneInstanceQuery (p := p) row nbCommitted maxRot lIS q) [] := by
  unfold readAlgebraOneInstanceQuery
  rw [if_neg h]
  dsimp only
  rw [hrow]
  have hbool : (((lIS.toList.drop (maxRot - q.2.int).toNat).take col.size).length == col.size) = true := by
    rw [beq_iff_eq]; exact hslice
  simp only [hbool, if_true, pure_bind]
  obtain ⟨v, hv⟩ := computeInnerProduct_ok_of_size col
    ((lIS.toList.drop (maxRot - q.2.int).toNat).take col.size).toArray
    (by rw [List.size_toArray]; exact hslice.symm)
  rw [hv]
  exact RunsAll.lift_ok E v



theorem runsAll_instanceQueries_mapM (E : VerifierEnv p G₁ G₂ Gₜ)
    (row : Array (Array (Fr p))) (nbCommitted : Nat) (maxRot : Int) (lIS : Array (Fr p)) :
    ∀ (queries : List (Column × Rotation)) (qs : List (Fr p)),
      qs.length = (queries.filter (fun q => q.1.index < nbCommitted)).length →
      (∀ q ∈ queries, ¬ q.1.index < nbCommitted →
        ∃ col, row[q.1.index - nbCommitted]? = some col ∧
          ((lIS.toList.drop (maxRot - q.2.int).toNat).take col.size).length = col.size) →
      RunsAll E (queries.mapM (readAlgebraOneInstanceQuery (p := p) row nbCommitted maxRot lIS))
        (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  intro queries
  induction queries with
  | nil =>
      intro qs hlen hsafe
      have h0 : qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      simpa only [List.mapM_nil, List.map_nil] using RunsAll.pure E ([] : List (Fr p))
  | cons q rest ih =>
      intro qs hlen hsafe
      have hsafe' : ∀ q' ∈ rest, ¬ q'.1.index < nbCommitted →
          ∃ col, row[q'.1.index - nbCommitted]? = some col ∧
            ((lIS.toList.drop (maxRot - q'.2.int).toNat).take col.size).length = col.size :=
        fun q' hq' => hsafe q' (by simp [hq'])
      rw [List.mapM_cons]
      by_cases hq : q.1.index < nbCommitted
      · have hfil : List.filter (fun q' => decide (q'.1.index < nbCommitted)) (q :: rest) =
            q :: List.filter (fun q' => decide (q'.1.index < nbCommitted)) rest :=
          List.filter_cons_of_pos (decide_eq_true_iff.mpr hq)
        rw [hfil] at hlen
        obtain ⟨v, qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
        refine RunsAll.bind E (ms₁ := ([Msg.fr v] : List (Msg (Fr p) G₁)))
          (ms₂ := qs'.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) ?_ ?_
        · exact runsAll_readAlgebraOneInstanceQuery_committed E row nbCommitted maxRot lIS q hq v
        · intro head
          have hb := RunsAll.bind E (ms₁ := qs'.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
            (ms₂ := []) (ih qs' (by simpa using hlen) hsafe')
            (fun tail => RunsAll.pure E (head :: tail))
          rw [List.append_nil] at hb
          exact hb
      · have hfil : List.filter (fun q' => decide (q'.1.index < nbCommitted)) (q :: rest) =
            List.filter (fun q' => decide (q'.1.index < nbCommitted)) rest :=
          List.filter_cons_of_neg (fun h => hq (decide_eq_true_iff.mp h))
        rw [hfil] at hlen
        obtain ⟨col, hrow, hslice⟩ := hsafe q (by simp) hq
        refine RunsAll.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
          (ms₂ := qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
          (runsAll_readAlgebraOneInstanceQuery_notCommitted E row nbCommitted maxRot lIS q hq
            col hrow hslice) ?_
        intro head
        have hb := RunsAll.bind E (ms₁ := qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
          (ms₂ := []) (ih qs hlen hsafe') (fun tail => RunsAll.pure E (head :: tail))
        rw [List.append_nil] at hb
        exact hb



theorem runsAll_instanceEvals (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (nbCommitted : Nat) (maxRot : Int) (lIS : Array (Fr p)) :
    ∀ (rows : List (Array (Array (Fr p)))) (qs : List (Fr p)),
      qs.length = rows.length *
        (vk.cs.instanceQueries.toList.filter
          (fun q => decide (q.1.index < nbCommitted))).length →
      (∀ row ∈ rows, ∀ q ∈ vk.cs.instanceQueries.toList, ¬ q.1.index < nbCommitted →
        ∃ col, row[q.1.index - nbCommitted]? = some col ∧
          ((lIS.toList.drop (maxRot - q.2.int).toNat).take col.size).length = col.size) →
      RunsAll E (rows.mapM (fun row =>
        vk.cs.instanceQueries.toList.mapM
          (readAlgebraOneInstanceQuery (p := p) row nbCommitted maxRot lIS)))
        (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  intro rows
  induction rows with
  | nil =>
      intro qs hlen hsafe
      have h0 : qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      simpa only [List.mapM_nil, List.map_nil] using RunsAll.pure E ([] : List (List (Fr p)))
  | cons row rows ih =>
      intro qs hlen hsafe
      set m := (vk.cs.instanceQueries.toList.filter
        (fun q => decide (q.1.index < nbCommitted))).length with hm
      have hsafe' : ∀ row' ∈ rows, ∀ q ∈ vk.cs.instanceQueries.toList,
          ¬ q.1.index < nbCommitted → ∃ col, row'[q.1.index - nbCommitted]? = some col ∧
            ((lIS.toList.drop (maxRot - q.2.int).toNat).take col.size).length = col.size :=
        fun row' hr' => hsafe row' (by simp [hr'])
      have hlen' : qs.length = m + rows.length * m := by
        rw [hlen, List.length_cons, Nat.add_one, Nat.succ_mul, Nat.add_comm]
      have htake : (qs.take m).length = m := by rw [List.length_take]; omega
      have hdrop : (qs.drop m).length = rows.length * m := by rw [List.length_drop]; omega
      have hsplit : qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) =
          (qs.take m).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (qs.drop m).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.mapM_cons, hsplit]
      refine RunsAll.bind E
        (ms₁ := (qs.take m).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (qs.drop m).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (runsAll_instanceQueries_mapM E row nbCommitted maxRot lIS
          vk.cs.instanceQueries.toList (qs.take m) (by rw [htake, hm])
          (fun q hqmem => hsafe row (by simp) q hqmem)) ?_
      intro head
      have hb := RunsAll.bind E
        (ms₁ := (qs.drop m).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := []) (ih (qs.drop m) hdrop hsafe')
        (fun tail => RunsAll.pure E (head :: tail))
      rw [List.append_nil] at hb
      exact hb

theorem mem_phaseCols_of_adviceColumnPhase {p : Nat} [Fact (Nat.Prime p)]
    (cs : Midfall.Halo2.ConstraintSystem (Fr p)) (i : Nat) (ph : Midfall.Halo2.Phase)
    (hi : i < cs.numAdviceColumns)
    (hp : cs.adviceColumnPhase[i]? = some ph) :
    i ∈ phaseCols cs ph := by
  unfold phaseCols
  rw [List.mem_filterMap]
  refine ⟨i, by rw [List.mem_range]; omega, ?_⟩
  rw [hp]
  simp

theorem adviceCols_cover (vk : VerifyingKey (Fr p) G₁)
    (hf : vk.WellFormed Features.solidity) {i : Nat}
    (hi : i < vk.cs.numAdviceColumns) :
    ∃ ph ∈ vk.cs.phases, i ∈ phaseCols vk.cs ph := by
  have hsize : i < vk.cs.adviceColumnPhase.size := by
    rw [hf.advicePhaseTotal]; exact hi
  have hp : vk.cs.adviceColumnPhase[i]? = some vk.cs.adviceColumnPhase[i] :=
    Array.getElem?_eq_getElem hsize
  refine ⟨vk.cs.adviceColumnPhase[i], ?_, mem_phaseCols_of_adviceColumnPhase vk.cs i _ hi hp⟩
  unfold Midfall.Halo2.ConstraintSystem.phases
  rw [List.mem_map]
  refine ⟨vk.cs.adviceColumnPhase[i].val, ?_, ?_⟩
  · rw [List.mem_range]
    have hbound : ∀ x ∈ vk.cs.adviceColumnPhase.toList,
        x.val ≤ vk.cs.adviceColumnPhase.foldl (fun acc p => max acc p.val) 0 := by
      intro x hx
      rw [← Array.foldl_toList, ← List.foldl_map]
      have hx' : x.val ∈ vk.cs.adviceColumnPhase.toList.map (fun p => p.val) :=
        List.mem_map.mpr ⟨x, hx, rfl⟩
      exact le_foldl_max_of_mem_or_le _ _ _ (Or.inr hx')
    have hmem : vk.cs.adviceColumnPhase[i] ∈ vk.cs.adviceColumnPhase.toList :=
      Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨i, hp⟩)
    have := hbound _ hmem
    omega
  · rfl



theorem runsAllP_parseTraceAdviceProofRead_cover (E : VerifierEnv p G₁ G₂ Gₜ)
    (cols : List Nat) (row : List (Nat × G₁)) (Qs : List G₁)
    (hlen : Qs.length = cols.length) :
    RunsAllP E (parseTraceAdviceProofRead E cols [row])
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun st1' => ∀ pairs ∈ st1',
        (∀ i ∈ cols, ∃ v, (i, v) ∈ pairs) ∧
        (∀ (i : Nat) (v : G₁), (i, v) ∈ row → (i, v) ∈ pairs)) := by
  rw [parseTraceAdviceProofRead]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind]
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨reads, t', hrun, hbuf', hpos', hsize⟩ :=
    runsAllP_tmReadN_g1 E cols.length Qs hlen t pref rest hbuf hpos hp henc hwidth
  refine ⟨List.take 0 [row] ++
      [[row][0]?.getD [] ++ List.zip cols reads.toList] ++
      List.drop (0 + 1) [row], t', ?_, hbuf', hpos', ?_⟩
  · simp only [StateT.run_bind, hrun, StateT.run_pure]
    rfl
  · intro pairs hpairs
    have hpairs' : pairs = row ++ List.zip cols reads.toList := by
      simpa using hpairs
    subst hpairs'
    constructor
    · intro i hi
      have hle : cols.length ≤ reads.toList.length := by
        rw [Array.length_toList]
        exact le_of_eq hsize.symm
      obtain ⟨a, ha⟩ := mem_zip_of_mem cols reads.toList hle hi
      exact ⟨a, List.mem_append.mpr (Or.inr ha)⟩
    · intro i v hv
      exact List.mem_append.mpr (Or.inl hv)



theorem parseTraceAdviceProofRead_singleton (E : VerifierEnv p G₁ G₂ Gₜ)
    (cols : List Nat) (row : List (Nat × G₁)) :
    parseTraceAdviceProofRead E cols [row] =
      (do let reads ← tmReadN (hashableG1 E.g1) cols.length
          pure [row ++ List.zip cols reads.toList]) := by
  rw [parseTraceAdviceProofRead]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind]
  rfl

theorem parseTraceAdvicePhase_zero_eq (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0)
    (row : List (Nat × G₁)) (ph : Phase) :
    parseTraceAdvicePhase E vk ([row], []) ph =
      (do let reads ← tmReadN (hashableG1 E.g1) (phaseCols vk.cs ph).length
          pure ([row ++ List.zip (phaseCols vk.cs ph) reads.toList], [])) := by
  rw [parseTraceAdvicePhase, hsp]
  simp only [List.range_zero, List.zip_nil_left, List.foldlM_nil, bind_assoc, pure_bind]
  rw [parseTraceAdviceProofRead_singleton]
  simp only [bind_assoc, pure_bind]

theorem runsAllP_parseTraceAdvicePhase_cover (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0)
    (row : List (Nat × G₁)) (ph : Phase) (Qs : List G₁)
    (hlen : Qs.length = (phaseCols vk.cs ph).length) :
    RunsAllP E (parseTraceAdvicePhase E vk ([row], []) ph)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun st => ∃ row', st = ([row'], []) ∧
        (∀ (i : Nat) (v : G₁), (i, v) ∈ row → (i, v) ∈ row') ∧
        (∀ i ∈ phaseCols vk.cs ph, ∃ v, (i, v) ∈ row')) := by
  rw [parseTraceAdvicePhase_zero_eq E vk hsp row ph]
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨reads, t', hrun, hbuf', hpos', hsize⟩ :=
    runsAllP_tmReadN_g1 E (phaseCols vk.cs ph).length Qs hlen t pref rest hbuf hpos hp
      henc hwidth
  refine ⟨([row ++ List.zip (phaseCols vk.cs ph) reads.toList], []), t', ?_, hbuf', hpos', ?_⟩
  · simp only [StateT.run_bind, hrun, StateT.run_pure]
    rfl
  · refine ⟨row ++ List.zip (phaseCols vk.cs ph) reads.toList, rfl, ?_, ?_⟩
    · intro i v hv
      exact List.mem_append.mpr (Or.inl hv)
    · intro i hi
      have hle : (phaseCols vk.cs ph).length ≤ reads.toList.length := by
        rw [Array.length_toList]
        exact le_of_eq hsize.symm
      obtain ⟨a, ha⟩ := mem_zip_of_mem (phaseCols vk.cs ph) reads.toList hle hi
      exact ⟨a, List.mem_append.mpr (Or.inr ha)⟩

theorem runsAllP_parseTraceAdvicePhases_cover (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0) :
    ∀ (phs : List Phase) (row : List (Nat × G₁)) (Qs : List G₁),
      Qs.length = (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum →
      RunsAllP E (phs.foldlM (parseTraceAdvicePhase E vk) ([row], []))
        (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun st => ∃ row', st = ([row'], []) ∧
          (∀ (i : Nat) (v : G₁), (i, v) ∈ row → (i, v) ∈ row') ∧
          (∀ ph ∈ phs, ∀ i ∈ phaseCols vk.cs ph, ∃ v, (i, v) ∈ row')) := by
  intro phs
  induction phs with
  | nil =>
      intro row Qs hlen
      have h0 : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      simpa only [List.foldlM_nil, List.map_nil] using
        (RunsAllP.pure E ([row], []) _ ⟨row, rfl, fun _ _ h => h, by intro ph h; simp at h⟩)
  | cons ph phs ih =>
      intro row Qs hlen
      have hsum : Qs.length = (phaseCols vk.cs ph).length +
          (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      set n := (phaseCols vk.cs ph).length with hn
      have hlen1 : (Qs.take n).length = n := by rw [List.length_take]; omega
      have hlen2 : (Qs.drop n).length =
          (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum := by
        rw [List.length_drop, hsum]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      refine RunsAllP.bind E
        (ms₁ := (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (ms₂ := (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (runsAllP_parseTraceAdvicePhase_cover E vk hsp row ph (Qs.take n)
          (by rw [hlen1, hn])) ?_
      intro st hst
      obtain ⟨row1, rfl, hpres, hcov⟩ := hst
      refine RunsAllP.mono E (ih row1 (Qs.drop n) hlen2) ?_
      intro st2 hst2
      obtain ⟨row2, hst2eq, hpres2, hcov2⟩ := hst2
      subst hst2eq
      refine ⟨row2, rfl, ?_, ?_⟩
      · intro i v hv
        exact hpres2 i v (hpres i v hv)
      · intro ph' hph' i hi
        rw [List.mem_cons] at hph'
        rcases hph' with rfl | hph'
        · obtain ⟨v, hv⟩ := hcov i hi
          exact ⟨v, hpres2 i v hv⟩
        · exact hcov2 ph' hph' i hi



theorem runsAllP_parseTraceAdvicePhases_cover_all (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (hsp : vk.cs.numChallenges = 0) (Qs : List G₁)
    (hlen : Qs.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum) :
    RunsAllP E (parseTraceAdvicePhases E vk)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun st => ∀ i < vk.cs.numAdviceColumns, ∃ v, (i, v) ∈ st.1[0]?.getD []) := by
  refine RunsAllP.mono E
    (runsAllP_parseTraceAdvicePhases_cover E vk hsp vk.cs.phases [] Qs (by simpa using hlen)) ?_
  intro st hst
  obtain ⟨row', hst, _, hcov⟩ := hst
  subst hst
  intro i hi
  obtain ⟨ph, hph, hiph⟩ := adviceCols_cover vk hf hi
  simpa using hcov ph hph i hiph

theorem runsAll_adviceScatter (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) :
    ∀ (rows : List (List (Nat × G₁))) (acc : Array (Array G₁)),
      (∀ pairs ∈ rows, ∀ i < vk.cs.numAdviceColumns, ∃ a, (i, a) ∈ pairs) →
      RunsAll E (rows.foldlM (init := acc) fun acc pairs => do
        let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
          "proofs/src/plonk/verifier.rs:118")
        pure (acc.push row)) [] := by
  intro rows
  induction rows with
  | nil =>
      intro acc hcov
      simpa only [List.foldlM_nil] using RunsAll.pure E acc
  | cons pairs rest ih =>
      intro acc hcov
      have hcov' : ∀ pairs' ∈ rest, ∀ i < vk.cs.numAdviceColumns, ∃ a, (i, a) ∈ pairs' :=
        fun p hp => hcov p (by simp [hp])
      obtain ⟨xs, hxs⟩ := scatterIndexed_ok_of_cover vk.cs.numAdviceColumns pairs
        "proofs/src/plonk/verifier.rs:118" (fun i hi => hcov pairs (by simp) i hi)
      rw [List.foldlM_cons]
      have hstep : RunsAll E ((StateT.lift (Midfall.Halo2.scatterIndexed
          vk.cs.numAdviceColumns pairs "proofs/src/plonk/verifier.rs:118")) >>= fun row =>
            pure (acc.push row)) [] := by
        rw [hxs]
        exact RunsAll.bind E (RunsAll.lift_ok E xs) (fun row => RunsAll.pure E (acc.push row))
      have hb := RunsAll.bind E (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := [])
        hstep (fun acc' => ih acc' hcov')
      rw [List.append_nil] at hb
      exact hb

theorem runsAll_parseTraceAdviceBlock (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (hsp : vk.cs.numChallenges = 0) (Qs : List G₁)
    (hlen : Qs.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum) :
    RunsAll E
      (do let st ← parseTraceAdvicePhases E vk
          st.1.foldlM (init := (#[] : Array (Array G₁))) fun acc pairs => do
            let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
              "proofs/src/plonk/verifier.rs:118")
            pure (acc.push row))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) := by
  let f : List (List (Nat × G₁)) × List (Nat × Fr p) → TranscriptM (Array (Array G₁)) :=
    fun st => st.1.foldlM (init := (#[] : Array (Array G₁))) fun acc pairs => do
      let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
        "proofs/src/plonk/verifier.rs:118")
      pure (acc.push row)
  have hcont : ∀ st : List (List (Nat × G₁)) × List (Nat × Fr p),
      (∃ row', st = ([row'], []) ∧
        (∀ (i : Nat) (v : G₁), (i, v) ∈ ([] : List (Nat × G₁)) → (i, v) ∈ row') ∧
        (∀ ph ∈ vk.cs.phases, ∀ i ∈ phaseCols vk.cs ph, ∃ v, (i, v) ∈ row')) →
      RunsAllP E (f st) [] (fun _ => True) := by
    intro st hst
    obtain ⟨row', rfl, _, hcov⟩ := hst
    have hcov' : ∀ pairs ∈ ([row'] : List (List (Nat × G₁))),
        ∀ i < vk.cs.numAdviceColumns, ∃ a, (i, a) ∈ pairs := by
      intro pairs hp i hi
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨ph, hph, hiph⟩ := adviceCols_cover vk hf hi
      exact hcov ph hph i hiph
    exact RunsAll.toRunsAllP E (runsAll_adviceScatter E vk [row'] #[] hcov')
  have hph := runsAllP_parseTraceAdvicePhases_cover E vk hsp vk.cs.phases [] Qs
    (by simpa using hlen)
  have hb := RunsAllP.bind E (m := parseTraceAdvicePhases E vk) (f := f)
    (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := []) hph hcont
  rw [List.append_nil] at hb
  simpa only [f] using hb.toRunsAll

def lookupChunkNum (deg : Nat) (l : LogupBatchedArgument (Fr p)) : Nat :=
  match l.chunkByDegree deg with
  | .ok c => c.numChunks
  | .error _ => 0

def ledgerPairs (row : Array (Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p))) : Nat :=
  (row.toList.map (fun p => p.2.numChunks + 1)).sum

def ledgerRows (rows : Array (Array (Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p)))) : Nat :=
  (rows.toList.map ledgerPairs).sum

theorem ledgerPairs_push (row : Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) (x : Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)) :
    ledgerPairs (row.push x) = ledgerPairs row + (x.2.numChunks + 1) := by
  unfold ledgerPairs
  rw [Array.toList_push, List.map_append, List.sum_append]
  simp

theorem ledgerRows_push (rows : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) (row : Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) :
    ledgerRows (rows.push row) = ledgerRows rows + ledgerPairs row := by
  unfold ledgerRows
  rw [Array.toList_push, List.map_append, List.sum_append]
  simp

theorem chunkNum_eq (deg : Nat) (l : LogupBatchedArgument (Fr p))
    (c : LogupChunkedArgument (Fr p)) (hc : l.chunkByDegree deg = .ok c) :
    c.numChunks = lookupChunkNum deg l := by
  unfold lookupChunkNum
  rw [hc]

theorem runsAllP_lookupMultiplicities_fold (E : VerifierEnv p G₁ G₂ Gₜ)
    (deg : Nat) :
    ∀ (ls : List (LogupBatchedArgument (Fr p)))
      (acc : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
      (Qs : List G₁),
      (∀ l ∈ ls, ∃ c, l.chunkByDegree deg = .ok c) →
      Qs.length = ls.length →
      RunsAllP E (ls.foldlM (init := acc) fun acc' l => do
          let chunked ← StateT.lift (l.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc'.push (m, chunked))) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun row => ledgerPairs row = ledgerPairs acc +
          (ls.map (fun l => lookupChunkNum deg l + 1)).sum) := by
  intro ls
  induction ls with
  | nil =>
      intro acc Qs hs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      refine RunsAllP.pure E acc _ ?_
      simp
  | cons l ls ih =>
      intro acc Qs hs hlen
      obtain ⟨Q, Qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      obtain ⟨c, hc⟩ := hs l (by simp)
      rw [List.foldlM_cons]
      have hhead : RunsAllP E
          ((fun acc => do
            let chunked ← StateT.lift (l.chunkByDegree deg)
            let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
            pure (acc.push (m, chunked))) acc)
          ([Msg.g1 Q] : List (Msg (Fr p) G₁))
          (fun row => ledgerPairs row = ledgerPairs acc + (lookupChunkNum deg l + 1)) := by
        have hstep := RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
          (ms₂ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (RunsAllP.lift_ok E c (fun chunked => l.chunkByDegree deg = .ok chunked) hc)
          (fun chunked hchunked =>
            RunsAllP.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁))) (ms₂ := [])
              (RunsAll.toRunsAllP E (runsAll_logup_readMultiplicities E chunked Q))
              (fun m _ => RunsAllP.pure E (acc.push (m, chunked))
                (fun row => ledgerPairs row = ledgerPairs acc + (lookupChunkNum deg l + 1))
                (by
                  rw [ledgerPairs_push, chunkNum_eq deg l chunked hchunked])))
        simpa only [List.nil_append, hc] using hstep
      have hb : RunsAllP E
          ((fun acc => do
            let chunked ← StateT.lift (l.chunkByDegree deg)
            let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
            pure (acc.push (m, chunked))) acc >>= fun acc' =>
              ls.foldlM (init := acc') fun acc' l => do
                let chunked ← StateT.lift (l.chunkByDegree deg)
                let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
                pure (acc'.push (m, chunked)))
          ([Msg.g1 Q] ++ Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun row => ∃ acc', ledgerPairs acc' = ledgerPairs acc +
              (lookupChunkNum deg l + 1) ∧
            ledgerPairs row = ledgerPairs acc' +
              (ls.map (fun l => lookupChunkNum deg l + 1)).sum) :=
        RunsAllP.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (ms₂ := Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          hhead (fun acc' hacc' => by
            have hb2 := ih acc' Qs' (fun l' hl' => hs l' (by simp [hl'])) (by simpa using hlen)
            exact RunsAllP.mono E hb2 (fun row hrow => ⟨acc', hacc', hrow⟩))
      refine RunsAllP.mono E hb ?_
      intro row hrow
      obtain ⟨acc', hacc', hrow'⟩ := hrow
      rw [hrow', hacc', List.map_cons, List.sum_cons]
      omega

theorem runsAllP_parseTraceLookupMultiplicities_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (Qs : List G₁) (hlen : Qs.length = vk.cs.lookups.size) :
    RunsAllP E (parseTraceLookupMultiplicities E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun rows => ledgerRows rows =
        (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum) := by
  unfold parseTraceLookupMultiplicities
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil]
  let inner : TranscriptM (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) :=
    List.foldlM (init := #[]) (fun acc' l => do
      let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
      let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
      pure (acc'.push (m, chunked))) vk.cs.lookups.toList
  let Post : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) → Prop :=
    fun rows => ledgerRows rows =
      (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum
  have hinner : RunsAllP E inner (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun row => ledgerPairs row =
        (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum) := by
    simpa [inner, ledgerPairs] using
      runsAllP_lookupMultiplicities_fold E vk.csDegree vk.cs.lookups.toList #[] Qs hs hlen
  let f1 : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) →
      TranscriptM (Array (Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p)))) :=
    fun row => pure (#[].push row)
  have hstep : RunsAllP E (inner >>= f1) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) Post := by
    have hb := RunsAllP.bind E (m := inner) (f := f1)
      (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      hinner (fun row hrow => by
        refine RunsAllP.pure E (#[].push row) Post ?_
        dsimp only [Post]
        rw [ledgerRows_push]
        simp only [ledgerRows, List.map_nil, List.sum_nil, Nat.zero_add]
        exact hrow)
    rw [List.append_nil] at hb
    exact hb
  have hb : RunsAllP E ((inner >>= f1) >>= fun init => pure init)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) Post := by
    have hb2 := RunsAllP.bind E (m := inner >>= f1) (f := fun init => (pure init : TranscriptM _))
      (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      hstep (fun acc hacc => RunsAllP.pure E acc Post hacc)
    rw [List.append_nil] at hb2
    exact hb2
  simpa only [inner, f1, Post] using hb

def parseTraceWireBody (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) : TranscriptM (VerifierTrace (Fr p) G₁) := do
  vk.hashInto
  for row in (committedShape (G₁ := G₁)).toList do
    for com in row do
      tmCommon (hashableG1 E.g1) com
  for row in (instanceShape inst).toList do
    for col in row do
      tmCommon (hashableFr (p := p)) (Nat.cast col.size)
      for v in col do
        tmCommon (hashableFr (p := p)) v
  let (advPairs, chalPairs) ← vk.cs.phases.foldlM
      (init := ((List.range 1).map (fun _ => ([] : List (Nat × G₁))),
                ([] : List (Nat × Fr p))))
      (fun st ph => do
        let cols := (List.range vk.cs.numAdviceColumns).filterMap fun i =>
          if (vk.cs.adviceColumnPhase[i]?.map (fun q => q.val)) == some ph.val
          then some i else none;
        let adv ← (List.range 1).foldlM (init := st.1) fun acc k => do
          let reads ← tmReadN (hashableG1 E.g1) cols.length;
          pure ((acc.take k) ++
                [((acc[k]?.getD []) ++ (List.zip cols reads.toList))] ++
                (acc.drop (k + 1)))
        let chalIdxPhase := List.zip (List.range vk.cs.numChallenges)
          vk.cs.challengePhase.toList
        let chals ← chalIdxPhase.foldlM (init := st.2) fun acc e =>
          if e.2.val == ph.val then do
            let c ← tmSqueezeChallenge
            pure (acc ++ [(e.1, c)])
          else pure acc
        pure (adv, chals))
  let adviceCommitments ← advPairs.foldlM (init := #[]) fun acc pairs => do
    let row ← StateT.lift (scatterIndexed vk.cs.numAdviceColumns pairs
      "proofs/src/plonk/verifier.rs:118")
    pure (acc.push row)
  let challenges ← StateT.lift (scatterIndexed vk.cs.numChallenges chalPairs
    "proofs/src/plonk/verifier.rs:134")
  let theta ← tmSqueezeChallenge
  let lookupMultiplicities ← (List.range 1).foldlM
    (init := #[]) fun acc _ => do
      let row ← vk.cs.lookups.toList.foldlM (init := #[]) fun acc' l => do
        let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
        let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
        pure (acc'.push (m, chunked))
      pure (acc.push row)
  let beta ← tmSqueezeChallenge
  let gamma ← tmSqueezeChallenge
  let permutations ← (List.range 1).foldlM
    (init := #[]) fun acc _ => do
      let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
        (hashableG1 E.g1)
      pure (acc.push pc)
  let lookups ← lookupMultiplicities.toList.foldlM
    (init := #[]) fun acc row => do
      let out ← row.toList.foldlM (init := #[]) fun acc' (m, chunked) => do
        let c ← m.readCommitment chunked.numChunks (hashableG1 E.g1)
        pure (acc'.push c)
      pure (acc.push out)
  let trashChallenge ← tmSqueezeChallenge
  let trashcans ← (List.range 1).foldlM
    (init := #[]) fun acc _ => do
      let row ← vk.cs.trashcans.toList.foldlM (init := #[]) fun acc' t => do
        let c ← Trash.readCommitted t (hashableG1 E.g1)
        pure (acc'.push c)
      pure (acc.push row)
  let y ← tmSqueezeChallenge
  pure { adviceCommitments, lookups, trashcans, permutations, challenges,
         beta, gamma, theta, trashChallenge, y }

theorem runsAll_parseTraceTail (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (adviceCommitments : Array (Array G₁)) (challenges : Array (Fr p))
    (QMult QPerm QLook QTrash : List G₁)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E
      (do let theta ← tmSqueezeChallenge
          let lookupMultiplicities ← (List.range 1).foldlM
            (init := (#[] : Array (Array (Logup.CommittedMultiplicities G₁ ×
              LogupChunkedArgument (Fr p))))) fun acc _ => do
              let row ← vk.cs.lookups.toList.foldlM (init := #[]) fun acc' l => do
                let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
                let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
                pure (acc'.push (m, chunked))
              pure (acc.push row)
          let beta ← tmSqueezeChallenge
          let gamma ← tmSqueezeChallenge
          let permutations ← (List.range 1).foldlM
            (init := (#[] : Array (Permutation.Committed G₁))) fun acc _ => do
              let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
                (hashableG1 E.g1)
              pure (acc.push pc)
          let lookups ← lookupMultiplicities.toList.foldlM
            (init := #[]) fun acc row => do
              let out ← row.toList.foldlM (init := #[]) fun acc' (m, chunked) => do
                let c ← m.readCommitment chunked.numChunks (hashableG1 E.g1)
                pure (acc'.push c)
              pure (acc.push out)
          let trashChallenge ← tmSqueezeChallenge
          let trashcans ← (List.range 1).foldlM
            (init := (#[] : Array (Array (Trash.Committed G₁)))) fun acc _ => do
              let row ← vk.cs.trashcans.toList.foldlM (init := #[]) fun acc' t => do
                let c ← Trash.readCommitted t (hashableG1 E.g1)
                pure (acc'.push c)
              pure (acc.push row)
          let y ← tmSqueezeChallenge
          pure ({ adviceCommitments := adviceCommitments, lookups := lookups, trashcans := trashcans, permutations := permutations, challenges := challenges, beta := beta, gamma := gamma, theta := theta, trashChallenge := trashChallenge, y := y } : VerifierTrace (Fr p) G₁))
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))) (fun _ => True) := by
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAllP.squeeze E) ?_
  intro theta _
  trace_state
  change RunsAllP E
    (do let lookupMultiplicities ← parseTraceLookupMultiplicities E vk 1
        let beta ← tmSqueezeChallenge
        let gamma ← tmSqueezeChallenge
        let permutations ← parseTracePermutations E vk 1
        let lookups ← parseTraceLookupCommitments E lookupMultiplicities
        let trashChallenge ← tmSqueezeChallenge
        let trashcans ← parseTraceTrashcans E vk 1
        let y ← tmSqueezeChallenge
        pure ({ adviceCommitments := adviceCommitments, lookups := lookups, trashcans := trashcans, permutations := permutations, challenges := challenges, beta := beta, gamma := gamma, theta := theta, trashChallenge := trashChallenge, y := y } : VerifierTrace (Fr p) G₁))
    (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (fun _ => True)
  refine RunsAllP.bind E (m := parseTraceLookupMultiplicities E vk 1)
    (ms₁ := QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (runsAllP_parseTraceLookupMultiplicities_one E vk hs QMult hlenMult) ?_
  intro rows hledger
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (RunsAllP.squeeze E) ?_
  intro beta _
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (RunsAllP.squeeze E) ?_
  intro gamma _
  refine RunsAllP.bind E (m := parseTracePermutations E vk 1)
    (ms₁ := QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))
    (RunsAll.toRunsAllP E (runsAll_parseTracePermutations_one E vk hdeg QPerm hlenPerm)) ?_
  intro permutations _
  have hlenLook' : QLook.length = (rows.toList.map
      (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
    rw [hlenLook]
    exact hledger.symm
  refine RunsAllP.bind E (m := parseTraceLookupCommitments E rows)
    (ms₁ := QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])
    (RunsAll.toRunsAllP E (runsAll_parseTraceLookupCommitments E rows QLook hlenLook')) ?_
  intro lookups _
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])
    (RunsAllP.squeeze E) ?_
  intro trashChallenge _
  refine RunsAllP.bind E (m := parseTraceTrashcans E vk 1)
    (ms₁ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := ([] : List (Msg (Fr p) G₁)))
    (RunsAll.toRunsAllP E (runsAll_parseTraceTrashcans_one E vk QTrash hlenTrash)) ?_
  intro trashcans _
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := ([] : List (Msg (Fr p) G₁)))
    (RunsAllP.squeeze E) ?_
  intro y _
  exact RunsAllP.pure E _ _ trivial



theorem runsAllP_parseTraceWireBody (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hsp : vk.cs.numChallenges = 0)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E (parseTraceWireBody E vk inst)
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) (fun _ => True) := by
  unfold parseTraceWireBody
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (runsAll_hashInto E vk)) ?_
  intro _ _
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (by
      simpa only [Array.forIn_toList] using
        runsAll_absorb_committed E (committedShape (G₁ := G₁)))) ?_
  intro _ _
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (by
      simpa only [Array.forIn_toList] using
        runsAll_absorb_instance E (instanceShape inst))) ?_
  intro _ _
  refine RunsAllP.bind E (m := parseTraceAdvicePhases E vk)
    (ms₁ := QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (runsAllP_parseTraceAdvicePhases_cover E vk hsp vk.cs.phases [] QAdv
      (by simpa using hlenAdv)) ?_
  intro st hst
  obtain ⟨row', rfl, _, hcov⟩ := hst
  have hcov' : ∀ pairs ∈ ([row'] : List (List (Nat × G₁))),
      ∀ i < vk.cs.numAdviceColumns, ∃ a, (i, a) ∈ pairs := by
    intro pairs hp i hi
    simp only [List.mem_singleton] at hp
    subst hp
    obtain ⟨ph, hph, hiph⟩ := adviceCols_cover vk hf hi
    exact hcov ph hph i hiph
  refine RunsAllP.bind E (m := ([row'] : List (List (Nat × G₁))).foldlM
      (init := (#[] : Array (Array G₁))) fun acc pairs => do
        let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
          "proofs/src/plonk/verifier.rs:118")
        pure (acc.push row))
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAll.toRunsAllP E (runsAll_adviceScatter E vk [row'] #[] hcov')) ?_
  intro adviceCommitments _
  obtain ⟨xs, hxs⟩ := scatterIndexed_ok_of_cover 0 ([] : List (Nat × Fr p))
    "proofs/src/plonk/verifier.rs:134" (fun i hi => by omega)
  rw [hsp, hxs]
  refine RunsAllP.bind E (m := StateT.lift (.ok xs : Except Fault (Array (Fr p))))
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAllP.lift_ok E xs (fun _ => True) trivial) ?_
  intro challenges _
  exact runsAll_parseTraceTail E vk hdeg hs adviceCommitments challenges
    QMult QPerm QLook QTrash hlenMult hlenPerm hlenLook hlenTrash

theorem runsAll_parseTraceWireBody (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hsp : vk.cs.numChallenges = 0)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAll E (parseTraceWireBody E vk inst)
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) :=
  (runsAllP_parseTraceWireBody E vk inst hf hsp hdeg hs QAdv QMult QPerm QLook QTrash
    hlenAdv hlenMult hlenPerm hlenLook hlenTrash).toRunsAll



theorem runsAll_parseTrace_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity)
    (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAll E (parseTrace (p := p) E.g1 Features.solidity vk
        (committedShape (G₁ := G₁)) (instanceShape inst))
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) := by
  unfold parseTrace
  simp only [Features.solidity, ite_true]
  rw [if_neg (by simp [committedShape])]
  rw [if_neg (by simp [committedShape])]
  rw [if_neg (by simp [committedShape, instanceShape, hnc])]
  exact runsAll_parseTraceWireBody E vk inst hf hsp hdeg hs QAdv QMult QPerm QLook QTrash
    hlenAdv hlenMult hlenPerm hlenLook hlenTrash

theorem parseTrace_run_of_ms (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0) (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size)
    (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth)
    (ms : List (Msg (Fr p) G₁))
    (hms : ms = QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) :
    ∃ trace t1, (parseTrace (p := p) E.g1 Features.solidity vk
        (committedShape (G₁ := G₁)) (instanceShape inst)).run (transcriptOf E H ms) =
      .ok (trace, t1) := by
  subst hms
  obtain ⟨trace, t1, hrun, _, _⟩ :=
    runsAll_parseTrace_one E vk inst hf hnc hsp hdeg hs QAdv QMult QPerm QLook QTrash
      hlenAdv hlenMult hlenPerm hlenLook hlenTrash (transcriptOf E H (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
      ByteArray.empty ByteArray.empty (by
        rw [(transcriptOf_buffer E H _).1]
        simp) (by rw [(transcriptOf_buffer E H _).2]; rfl) hp henc hwidth
  exact ⟨trace, t1, hrun⟩



theorem snapshotTraceRun_ok_of_ms (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0) (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size)
    (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth)
    (ms : List (Msg (Fr p) G₁))
    (hms : ms = QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) :
    ∃ s t, snapshotTraceRun E H vk inst ms = .ok (s, t) := by
  obtain ⟨trace, t1, hrun⟩ := parseTrace_run_of_ms E H vk inst hf hnc hsp hdeg hs
    QAdv QMult QPerm QLook QTrash hlenAdv hlenMult hlenPerm hlenLook hlenTrash hp henc
    hwidth ms hms
  refine ⟨SnapTrace.mk trace, t1, ?_⟩
  unfold snapshotTraceRun snapshotTraceStep
  simp only [StateT.run_bind, StateT.run_pure, hrun]
  rfl

theorem runsAll_mapM_groups (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} :
    ∀ (xs : List α) (g : α → TranscriptM β) (lens : α → Nat) (qs : List (Fr p)),
      qs.length = (xs.map lens).sum →
      (∀ a ∈ xs, ∀ qs₁ : List (Fr p), qs₁.length = lens a →
        RunsAll E (g a) (qs₁.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))) →
      RunsAll E (xs.mapM g) (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  intro xs
  induction xs with
  | nil =>
      intro g lens qs hlen hg
      have h0 : qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      simpa only [List.mapM_nil, List.map_nil] using RunsAll.pure E ([] : List β)
  | cons a as ih =>
      intro g lens qs hlen hg
      have hsum : qs.length = lens a + (as.map lens).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      have hle : lens a ≤ qs.length := by omega
      have hlen1 : (qs.take (lens a)).length = lens a := by rw [List.length_take]; omega
      have hlen2 : (qs.drop (lens a)).length = (as.map lens).sum := by
        rw [List.length_drop, hsum]; omega
      have hsplit : qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) =
          (qs.take (lens a)).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (qs.drop (lens a)).map (fun q => (Msg.fr q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.mapM_cons, hsplit]
      refine RunsAll.bind E
        (ms₁ := (qs.take (lens a)).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (qs.drop (lens a)).map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (hg a (by simp) (qs.take (lens a)) hlen1) ?_
      intro head
      have hb := RunsAll.bind E
        (ms₁ := (qs.drop (lens a)).map (fun q => (Msg.fr q : Msg (Fr p) G₁))) (ms₂ := [])
        (ih g lens (qs.drop (lens a)) hlen2 (fun a' ha' => hg a' (by simp [ha'])))
        (fun tail => RunsAll.pure E (head :: tail))
      rw [List.append_nil] at hb
      exact hb

theorem runsAll_permutationsEvaluated (E : VerifierEnv p G₁ G₂ Gₜ)
    (permutations : Array (Permutation.Committed G₁)) (Qp : List (Fr p))
    (hlen : Qp.length = (permutations.toList.map
      (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum) :
    RunsAll E (permutations.toList.mapM (fun pc => Permutation.Committed.evaluate (p := p) pc))
      (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) :=
  runsAll_mapM_groups E permutations.toList (fun pc => Permutation.Committed.evaluate (p := p) pc)
    (fun pc => 3 * pc.permutationProductCommitments.size - 1) Qp hlen
    (fun pc _ qs hqs => runsAll_permutationEval E pc qs hqs)

theorem runsAll_rowsEvaluated (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type}
    (rows : Array (Array α)) (g : α → TranscriptM β) (lens : α → Nat) (qs : List (Fr p))
    (hlen : qs.length = (rows.toList.map (fun row => (row.toList.map lens).sum)).sum)
    (hg : ∀ a, ∀ qs₁ : List (Fr p), qs₁.length = lens a →
      RunsAll E (g a) (qs₁.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))) :
    RunsAll E (rows.toList.mapM (fun row => row.toList.mapM g))
      (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) :=
  runsAll_mapM_groups E rows.toList (fun row => row.toList.mapM g)
    (fun row => (row.toList.map lens).sum) qs hlen
    (fun row _ qs₁ hlen₁ => runsAll_mapM_groups E row.toList g lens qs₁ hlen₁ (fun a _ => hg a))

theorem runsAll_lookupsEvaluated (E : VerifierEnv p G₁ G₂ Gₜ)
    (lookups : Array (Array (Logup.Committed G₁))) (Ql : List (Fr p))
    (hlen : Ql.length = (lookups.toList.map
      (fun row => (row.toList.map (fun l => l.helperPolys.size + 3)).sum)).sum) :
    RunsAll E (lookups.toList.mapM (fun row =>
        row.toList.mapM (fun l => Logup.Committed.evaluate (p := p) l)))
      (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) :=
  runsAll_rowsEvaluated E lookups (fun l => Logup.Committed.evaluate (p := p) l)
    (fun l => l.helperPolys.size + 3) Ql hlen
    (fun l qs hqs => runsAll_logupEval E l qs hqs)

theorem runsAll_trashcansEvaluated (E : VerifierEnv p G₁ G₂ Gₜ)
    (trashcans : Array (Array (Trash.Committed G₁))) (Qt : List (Fr p))
    (hlen : Qt.length = (trashcans.toList.map (fun row => row.size)).sum) :
    RunsAll E (trashcans.toList.mapM (fun row =>
        row.toList.mapM (fun t => Trash.Committed.evaluate (p := p) t)))
      (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) := by
  apply runsAll_rowsEvaluated E trashcans (fun t => Trash.Committed.evaluate (p := p) t)
    (fun _ => 1) Qt ?_ ?_
  · simpa using hlen
  · intro t qs hqs
    obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp hqs
    simpa using runsAll_trashEval E t q

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem runsAll_readAlgebra (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p))))
    (hmax : maxInstanceLen instances < 2 ^ 31)
    (hrows : ∀ row ∈ instances.toList, ∀ q ∈ vk.cs.instanceQueries.toList,
      ¬ q.1.index < nbCommitted → ∃ col, row[q.1.index - nbCommitted]? = some col)
    (Qg : List G₁) (Qi Qa Qf Qc Qp Ql Qt : List (Fr p))
    (hlenQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else vk.domain.getQuotientPolyDegree))
    (hlenI : Qi.length = instances.size *
      (vk.cs.instanceQueries.toList.filter
        (fun q => decide (q.1.index < nbCommitted))).length)
    (hlenA : Qa.length = numProofs * vk.cs.adviceQueries.size)
    (hlenF : Qf.length = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
    (hlenC : Qc.length = vk.permutation.commitments.size)
    (hlenP : Qp.length = (permutations.toList.map
      (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum)
    (hlenL : Ql.length = (lookups.toList.map
      (fun row => (row.toList.map (fun l => l.helperPolys.size + 3)).sum)).sum)
    (hlenT : Qt.length = (trashcans.toList.map (fun row => row.size)).sum) :
    RunsAll E (Verifier.readAlgebra (p := p) E.g1 Features.solidity vk permutations lookups
      trashcans nbCommitted numProofs instances)
      (Qg.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                  (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                    (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))))))) := by
  unfold Verifier.readAlgebra
  dsimp only
  let rest : List (Msg (Fr p) G₁) :=
    Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
      (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))))
  refine RunsAll.bind E (ms₁ := Qg.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := rest) ?_ ?_
  · exact runsAll_tmReadN_g1 E vk.domain.getQuotientPolyDegree Qg
      (by simpa [show (if Features.solidity.outerSingleHCommitment = true then 1
        else vk.domain.getQuotientPolyDegree) = vk.domain.getQuotientPolyDegree from rfl] using hlenQ)
  · intro quotientLimbComs
    refine RunsAll.bind E (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := rest)
      (RunsAll.squeeze E) ?_
    intro x
    have hmin : (List.foldl
        (fun st q =>
          if q.2.int < st.1 then (q.2.int, st.2)
          else if q.2.int > st.2 then (st.1, q.2.int) else st)
        (0, 0) vk.cs.instanceQueries.toList).1 = 0 := by
      simpa only using congrArg Prod.fst (readAlgebra_rotBounds_zero vk hf)
    have hm : RunsAllP E
        (StateT.lift (Verifier.i32Abs
          (List.foldl
            (fun st q =>
              if q.2.int < st.1 then (q.2.int, st.2)
              else if q.2.int > st.2 then (st.1, q.2.int) else st)
            (0, 0) vk.cs.instanceQueries.toList).1
          "proofs/src/plonk/verifier.rs:348")) [] (fun a => a = 0) := by
      simpa only [hmin, i32Abs_zero] using
        (RunsAllP.lift_ok E (0 : Int) (fun a => a = 0) rfl)
    refine (RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
      (ms₂ := rest) (Q := fun _ => True) hm ?_).toRunsAll
    intro absMin habs
    subst habs
    set maxRot : Int := (List.foldl
      (fun st q =>
        if q.2.int < st.1 then (q.2.int, st.2)
        else if q.2.int > st.2 then (st.1, q.2.int) else st)
      (0, 0) vk.cs.instanceQueries.toList).2 with hmaxRot
    set lIS : Array (Fr p) :=
      vk.domain.lIRange x (powVartime x (vk.n - 1) * x) _ with hLIS
    have hmaxRot0 : maxRot = 0 := by
      rw [hmaxRot]
      simpa only using congrArg Prod.snd (readAlgebra_rotBounds_zero vk hf)
    have hlis0 : lIS = vk.domain.lIRange x (powVartime x (vk.n - 1) * x)
        (zeroRotations (maxInstanceLen instances)) := by
      have hfold : List.foldl max 0 (List.flatMap
          (fun row => List.map (fun col => col.size) row.toList) instances.toList) =
          maxInstanceLen instances := rfl
      rw [hLIS, hmaxRot0, hfold,
        readAlgebra_rotations_zero (maxInstanceLen instances) hmax]
    refine RunsAllP.bind E (ms₁ := Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
      (ms₂ := (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))))))
      (RunsAll.toRunsAllP E (runsAll_instanceEvals E vk nbCommitted maxRot lIS
        instances.toList Qi hlenI ?_)) ?_
    · intro row hrow q hq hnc
      obtain ⟨col, hcol⟩ := hrows row hrow q hq hnc
      refine ⟨col, hcol, ?_⟩
      rw [hlis0, hmaxRot0]
      exact readAlgebra_instanceSlice_safe vk hf nbCommitted instances hmax x
        (powVartime x (vk.n - 1) * x) row hrow q hq col hcol
    · intro instanceEvalsList _
      refine RunsAllP.bind E (ms₁ := Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))))
        (RunsAll.toRunsAllP E (runsAll_readAlgebraAdviceEvals E vk numProofs Qa hlenA)) ?_
      intro adviceEvalsList _
      refine RunsAllP.bind E (ms₁ := Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))))
        (RunsAll.toRunsAllP E (runsAll_readFixedEvals E vk hf Qf hlenF)) ?_
      intro fixedEvals _
      refine RunsAllP.bind E (ms₁ := Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))
        (RunsAll.toRunsAllP E (runsAll_permutationCommon E vk Qc hlenC)) ?_
      intro permutationsCommon _
      refine RunsAllP.bind E (ms₁ := Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))
        (RunsAll.toRunsAllP E (runsAll_permutationsEvaluated E permutations Qp hlenP)) ?_
      intro permutationsEvaluatedList _
      refine RunsAllP.bind E (ms₁ := Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))
        (RunsAll.toRunsAllP E (runsAll_lookupsEvaluated E lookups Ql hlenL)) ?_
      intro lookupsEvaluatedList _
      refine RunsAllP.bind E (ms₁ := Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := ([] : List (Msg (Fr p) G₁)))
        (RunsAll.toRunsAllP E (runsAll_trashcansEvaluated E trashcans Qt hlenT)) ?_
      intro trashcansEvaluatedList _
      exact RunsAllP.pure E _ _ trivial

theorem readN_g1_wire_values (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (n : Nat) (acc : Array G₁) (t : Midfall.Halo2.Transcript) (pref : Bytes)
      (qs : List G₁) (rest : Bytes),
      qs.length = n →
      t.buffer = pref ++ (wireMsgs E (qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ++ rest) →
      t.pos = pref.size →
      p ≤ 2 ^ 256 →
      (∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q) →
      (∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth) →
      ∃ (arr : Array G₁) (t' : Midfall.Halo2.Transcript),
        Midfall.Halo2.Transcript.readN.go (hashableG1 E.g1) t acc n = .ok (arr, t') ∧
        arr.toList = acc.toList ++ qs ∧
        t'.pos = pref.size + (qs.map fun Q => (msgWire E (Msg.g1 Q)).size).sum ∧
        t'.buffer = t.buffer := by
  intro n
  induction n with
  | zero =>
      intro acc t pref qs rest hlen hbuf hpos hp henc hwidth
      have hqs : qs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hqs
      refine ⟨acc, t, ?_, ?_, ?_, rfl⟩
      · simp only [Midfall.Halo2.Transcript.readN.go]
      · simp
      · simp [hpos]
  | succ n ih =>
      intro acc t pref qs rest hlen hbuf hpos hp henc hwidth
      obtain ⟨Q, qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      have hsize : (msgWire E (Msg.g1 Q)).size = g1CompressedWidth := by
        show (E.g1.toCompressed Q).size = g1CompressedWidth
        exact hwidth Q
      have hbuf' : t.buffer = pref ++ msgWire E (Msg.g1 Q) ++
          (wireMsgs E (qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ++ rest) := by
        rw [hbuf, List.map_cons, wireMsgs_cons]
        simp only [ByteArray.append_assoc]
      have hbt : bytesTake t.buffer t.pos g1CompressedWidth = some (E.g1.toCompressed Q) := by
        rw [hbuf', hpos, ← Nat.add_zero (ByteArray.size pref), ByteArray.append_assoc]
        simp only [msgWire]
        rw [bytesTake_append_right pref (E.g1.toCompressed Q ++
          (wireMsgs E (qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ++ rest)) 0 g1CompressedWidth (by
            rw [ByteArray.size_append, hwidth]; omega)]
        rw [bytesTake_append_left (E.g1.toCompressed Q)
          (wireMsgs E (qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ++ rest) 0 g1CompressedWidth (by rw [hwidth]; omega)]
        rw [← hwidth Q, bytesTake_whole]
      obtain ⟨t1, hread, hpos1, hbuf1⟩ :=
        transcript_read_ok (hashableG1 E.g1) t (E.g1.toCompressed Q) Q hbt
          (by rw [hashableG1_readRepr?]; exact henc Q)
      have hpos1' : t1.pos = (pref ++ msgWire E (Msg.g1 Q)).size := by
        rw [hpos1, hpos, hashableG1_width, ByteArray.size_append, hsize]
      have hbuf1' : t1.buffer = (pref ++ msgWire E (Msg.g1 Q)) ++
          wireMsgs E (qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ++ rest := by
        rw [hbuf1, hbuf']
        simp only [ByteArray.append_assoc]
      obtain ⟨arr, t2, hrun2, hval, hpos2, hbuf2⟩ :=
        ih (acc.push Q) t1 (pref ++ msgWire E (Msg.g1 Q)) qs' rest
          (by simpa using hlen) (by simpa only [ByteArray.append_assoc] using hbuf1') hpos1' hp henc hwidth
      refine ⟨arr, t2, ?_, ?_, ?_, hbuf2.trans hbuf1⟩
      · simp only [Midfall.Halo2.Transcript.readN.go]
        rw [hread]
        exact hrun2
      · rw [hval, Array.toList_push, List.append_assoc]
        rfl
      · rw [hpos2, ByteArray.size_append, List.map_cons, List.sum_cons]
        omega

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem runsAllP_tmReadN_g1_values (E : VerifierEnv p G₁ G₂ Gₜ) (n : Nat) (Qs : List G₁)
    (hlen : Qs.length = n) :
    RunsAllP E (tmReadN (hashableG1 E.g1) n)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (fun arr => arr.toList = Qs) := by
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨arr, t', hrun, hval, hpos', hbuf'⟩ :=
    readN_g1_wire_values E n #[] t pref Qs rest hlen (by simpa only [ByteArray.append_assoc] using hbuf) hpos hp henc hwidth
  refine ⟨arr, t', ?_, hbuf', ?_, ?_⟩
  · rw [tmReadN_run_eq]
    simpa only [Midfall.Halo2.Transcript.readN] using hrun
  · simpa only [List.map_map, Function.comp_def] using hpos'
  · simpa using hval

theorem runsAllP_parseTraceAdvicePhase_values (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0)
    (row : List (Nat × G₁)) (ph : Phase) (Qs : List G₁)
    (hlen : Qs.length = (phaseCols vk.cs ph).length) :
    RunsAllP E (parseTraceAdvicePhase E vk ([row], []) ph)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun st => st = ([row ++ List.zip (phaseCols vk.cs ph) Qs], [])) := by
  rw [parseTraceAdvicePhase_zero_eq E vk hsp row ph]
  intro t pref rest hbuf hpos hp henc hwidth
  obtain ⟨reads, t', hrun, hbuf', hpos', hval⟩ :=
    runsAllP_tmReadN_g1_values E (phaseCols vk.cs ph).length Qs hlen t pref rest hbuf
      hpos hp henc hwidth
  refine ⟨([row ++ List.zip (phaseCols vk.cs ph) reads.toList], []), t', ?_, hbuf', hpos', ?_⟩
  · simp only [StateT.run_bind, hrun, StateT.run_pure]
    rfl
  · rw [hval]

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem length_flatMap_phaseCols (cs : Midfall.Halo2.ConstraintSystem (Fr p)) (phs : List Phase) :
    (phs.flatMap (fun ph => phaseCols cs ph)).length =
      (phs.map (fun ph => (phaseCols cs ph).length)).sum := by
  induction phs with
  | nil => rfl
  | cons ph phs ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih]

theorem runsAllP_parseTraceAdvicePhases_values (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0) :
    ∀ (phs : List Phase) (row : List (Nat × G₁)) (Qs : List G₁),
      Qs.length = (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum →
      RunsAllP E (phs.foldlM (parseTraceAdvicePhase E vk) ([row], []))
        (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun st => st = ([row ++ List.zip (phs.flatMap (fun ph => phaseCols vk.cs ph)) Qs], [])) := by
  intro phs
  induction phs with
  | nil =>
      intro row Qs hlen
      have h0 : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      simpa only [List.foldlM_nil, List.flatMap_nil, List.zip_nil_right, List.map_nil] using
        (RunsAllP.pure E ([row], []) (fun st => st = ([row ++ []], [])) (by simp))
  | cons ph phs ih =>
      intro row Qs hlen
      have hsum : Qs.length = (phaseCols vk.cs ph).length +
          (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      set n := (phaseCols vk.cs ph).length with hn
      have hlen1 : (Qs.take n).length = n := by rw [List.length_take]; omega
      have hlen2 : (Qs.drop n).length =
          (phs.map (fun ph => (phaseCols vk.cs ph).length)).sum := by
        rw [List.length_drop, hsum]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      refine RunsAllP.bind E
        (ms₁ := (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (ms₂ := (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (runsAllP_parseTraceAdvicePhase_values E vk hsp row ph (Qs.take n)
          (by rw [hlen1, hn])) ?_
      intro st hst
      rw [hst]
      refine RunsAllP.mono E (ih (row ++ List.zip (phaseCols vk.cs ph) (Qs.take n))
        (Qs.drop n) hlen2) ?_
      intro st2 hst2
      rw [hst2]
      have hzip : List.zip ((phaseCols vk.cs ph) ++
          (phs.flatMap (fun ph => phaseCols vk.cs ph))) Qs =
          List.zip (phaseCols vk.cs ph) (Qs.take n) ++
            List.zip (phs.flatMap (fun ph => phaseCols vk.cs ph)) (Qs.drop n) := by
        conv_lhs => rw [show Qs = Qs.take n ++ Qs.drop n from
          (List.take_append_drop n Qs).symm]
        exact List.zip_append (l₁ := phaseCols vk.cs ph) (l₂ := Qs.take n)
          (r₁ := phs.flatMap (fun ph => phaseCols vk.cs ph)) (r₂ := Qs.drop n)
          (hn.symm.trans hlen1.symm)
      rw [List.flatMap_cons, hzip, List.append_assoc]

theorem runsAllP_readAlgebra_quotient_values (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p))))
    (hmax : maxInstanceLen instances < 2 ^ 31)
    (hrows : ∀ row ∈ instances.toList, ∀ q ∈ vk.cs.instanceQueries.toList,
      ¬ q.1.index < nbCommitted → ∃ col, row[q.1.index - nbCommitted]? = some col)
    (Qg : List G₁) (Qi Qa Qf Qc Qp Ql Qt : List (Fr p))
    (hlenQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else vk.domain.getQuotientPolyDegree))
    (hlenI : Qi.length = instances.size *
      (vk.cs.instanceQueries.toList.filter
        (fun q => decide (q.1.index < nbCommitted))).length)
    (hlenA : Qa.length = numProofs * vk.cs.adviceQueries.size)
    (hlenF : Qf.length = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
    (hlenC : Qc.length = vk.permutation.commitments.size)
    (hlenP : Qp.length = (permutations.toList.map
      (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum)
    (hlenL : Ql.length = (lookups.toList.map
      (fun row => (row.toList.map (fun l => l.helperPolys.size + 3)).sum)).sum)
    (hlenT : Qt.length = (trashcans.toList.map (fun row => row.size)).sum) :
    RunsAllP E (Verifier.readAlgebra (p := p) E.g1 Features.solidity vk permutations lookups
      trashcans nbCommitted numProofs instances)
      (Qg.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                  (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                    (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))))))
      (fun alg => alg.quotientLimbComs.toList = Qg) := by
  unfold Verifier.readAlgebra
  dsimp only
  let rest : List (Msg (Fr p) G₁) :=
    Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
      (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))))
  have hfirst : RunsAllP E
      (tmReadN (hashableG1 E.g1) (if Features.solidity.outerSingleHCommitment then 1
        else vk.domain.getQuotientPolyDegree))
      (Qg.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (fun arr => arr.toList = Qg) :=
    runsAllP_tmReadN_g1_values E vk.domain.getQuotientPolyDegree Qg
      (by simpa [show (if Features.solidity.outerSingleHCommitment = true then 1
        else vk.domain.getQuotientPolyDegree) = vk.domain.getQuotientPolyDegree from rfl] using hlenQ)
  refine RunsAllP.bind E (ms₁ := Qg.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := rest) hfirst ?_
  intro quotientLimbComs hq
  · refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := rest)
      (RunsAllP.squeeze E) ?_
    intro x _
    have hmin : (List.foldl
        (fun st q =>
          if q.2.int < st.1 then (q.2.int, st.2)
          else if q.2.int > st.2 then (st.1, q.2.int) else st)
        (0, 0) vk.cs.instanceQueries.toList).1 = 0 := by
      simpa only using congrArg Prod.fst (readAlgebra_rotBounds_zero vk hf)
    have hm : RunsAllP E
        (StateT.lift (Verifier.i32Abs
          (List.foldl
            (fun st q =>
              if q.2.int < st.1 then (q.2.int, st.2)
              else if q.2.int > st.2 then (st.1, q.2.int) else st)
            (0, 0) vk.cs.instanceQueries.toList).1
          "proofs/src/plonk/verifier.rs:348")) [] (fun a => a = 0) := by
      simpa only [hmin, i32Abs_zero] using
        (RunsAllP.lift_ok E (0 : Int) (fun a => a = 0) rfl)
    refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
      (ms₂ := rest) hm ?_
    intro absMin habs
    subst habs
    set maxRot : Int := (List.foldl
      (fun st q =>
        if q.2.int < st.1 then (q.2.int, st.2)
        else if q.2.int > st.2 then (st.1, q.2.int) else st)
      (0, 0) vk.cs.instanceQueries.toList).2 with hmaxRot
    set lIS : Array (Fr p) :=
      vk.domain.lIRange x (powVartime x (vk.n - 1) * x) _ with hLIS
    have hmaxRot0 : maxRot = 0 := by
      rw [hmaxRot]
      simpa only using congrArg Prod.snd (readAlgebra_rotBounds_zero vk hf)
    have hlis0 : lIS = vk.domain.lIRange x (powVartime x (vk.n - 1) * x)
        (zeroRotations (maxInstanceLen instances)) := by
      have hfold : List.foldl max 0 (List.flatMap
          (fun row => List.map (fun col => col.size) row.toList) instances.toList) =
          maxInstanceLen instances := rfl
      rw [hLIS, hmaxRot0, hfold,
        readAlgebra_rotations_zero (maxInstanceLen instances) hmax]
    refine RunsAllP.bind E (ms₁ := Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
      (ms₂ := (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))))))
      (RunsAll.toRunsAllP E (runsAll_instanceEvals E vk nbCommitted maxRot lIS
        instances.toList Qi hlenI ?_)) ?_
    · intro row hrow q hq hnc
      obtain ⟨col, hcol⟩ := hrows row hrow q hq hnc
      refine ⟨col, hcol, ?_⟩
      rw [hlis0, hmaxRot0]
      exact readAlgebra_instanceSlice_safe vk hf nbCommitted instances hmax x
        (powVartime x (vk.n - 1) * x) row hrow q hq col hcol
    · intro instanceEvalsList _
      refine RunsAllP.bind E (ms₁ := Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
                (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))))
        (RunsAll.toRunsAllP E (runsAll_readAlgebraAdviceEvals E vk numProofs Qa hlenA)) ?_
      intro adviceEvalsList _
      refine RunsAllP.bind E (ms₁ := Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
              (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))))
        (RunsAll.toRunsAllP E (runsAll_readFixedEvals E vk hf Qf hlenF)) ?_
      intro fixedEvals _
      refine RunsAllP.bind E (ms₁ := Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))))
        (RunsAll.toRunsAllP E (runsAll_permutationCommon E vk Qc hlenC)) ?_
      intro permutationsCommon _
      refine RunsAllP.bind E (ms₁ := Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))
        (RunsAll.toRunsAllP E (runsAll_permutationsEvaluated E permutations Qp hlenP)) ?_
      intro permutationsEvaluatedList _
      refine RunsAllP.bind E (ms₁ := Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ []))
        (RunsAll.toRunsAllP E (runsAll_lookupsEvaluated E lookups Ql hlenL)) ?_
      intro lookupsEvaluatedList _
      refine RunsAllP.bind E (ms₁ := Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
        (ms₂ := ([] : List (Msg (Fr p) G₁)))
        (RunsAll.toRunsAllP E (runsAll_trashcansEvaluated E trashcans Qt hlenT)) ?_
      intro trashcansEvaluatedList _
      exact RunsAllP.pure E _ (fun (alg : Verifier.AlgebraRead (Fr p) G₁) =>
        alg.quotientLimbComs.toList = Qg) (by
        simpa using hq)


theorem scatStep_fold_range_shift {α : Type} (n : Nat) :
    ∀ (k : Nat) (pref : List (Option α)) (Qs : List α),
      pref.length = k → k + Qs.length ≤ n →
      (List.zip ((List.range Qs.length).map (fun i => k + i)) Qs).foldl
        (scatStep n) (pref ++ List.replicate (n - k) none) =
      pref ++ Qs.map some ++ List.replicate (n - k - Qs.length) none := by
  intro k pref Qs
  induction Qs generalizing k pref with
  | nil =>
      intro hk hle
      simp
  | cons Q Qs ih =>
      intro hk hle
      simp only [List.length_cons] at hle
      have hklt : k < n := by omega
      have htake : (pref ++ List.replicate (n - k) none).take k = pref := by
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      have hdrop : (pref ++ List.replicate (n - k) none).drop (k + 1) =
          List.replicate (n - k - 1) none := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.drop_replicate,
          List.nil_append, hk]
        congr 1
        omega
      have hstep : scatStep n (pref ++ List.replicate (n - k) none) (k, Q) =
          (pref ++ [some Q]) ++ List.replicate (n - (k + 1)) none := by
        unfold scatStep
        rw [if_pos hklt, htake, hdrop, List.append_assoc,
          show n - k - 1 = n - (k + 1) by omega]
        simp only [List.append_assoc]
      have hzip : List.zip ((List.range (Qs.length + 1)).map (fun i => k + i)) (Q :: Qs) =
          (k, Q) :: List.zip ((List.range Qs.length).map (fun i => (k + 1) + i)) Qs := by
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, List.zip_cons_cons]
        congr 1
        rw [show ((fun i => k + i) ∘ Nat.succ) = (fun i => (k + 1) + i) by
          funext x
          simp only [Function.comp_apply]
          omega]
      rw [show (Q :: Qs).length = Qs.length + 1 by rfl]
      rw [hzip, List.foldl_cons, hstep]
      have hlenpref : (pref ++ [some Q]).length = k + 1 := by simp [hk]
      have hmain := ih (k + 1) (pref ++ [some Q]) hlenpref (by omega)
      rw [hmain, List.map_cons]
      simp only [List.append_assoc]
      rw [show n - (k + 1) - Qs.length = n - k - (Qs.length + 1) by omega]
      rfl

theorem scatStep_fold_zip_range {α : Type} (n : Nat) (Qs : List α)
    (hlen : Qs.length = n) :
    (List.zip (List.range n) Qs).foldl (scatStep n) (List.replicate n none) =
      Qs.map some := by
  have h := scatStep_fold_range_shift (α := α) n 0 [] Qs rfl (by omega)
  rw [hlen] at h
  simpa using h

theorem mapM_id_map_some {α : Type} (Qs : List α) :
    List.mapM (fun x => x) (Qs.map some) = some Qs := by
  induction Qs with
  | nil => rfl
  | cons q qs ih => simp [ih]

theorem scatterIndexed_zip_range {α : Type} (n : Nat) (Qs : List α)
    (hlen : Qs.length = n) (site : String) :
    Midfall.Halo2.scatterIndexed n (List.zip (List.range n) Qs) site = .ok Qs.toArray := by
  have hfold := scatStep_fold_zip_range n Qs hlen
  unfold Midfall.Halo2.scatterIndexed
  change (match (List.zip (List.range n) Qs).foldl (scatStep n)
      (List.replicate n (none : Option α)) with
    | placed =>
      match placed.mapM (fun x => x) with
      | some xs => Except.ok xs.toArray
      | none => Except.error (Midfall.Halo2.Fault.panic site)) = Except.ok Qs.toArray
  rw [hfold]
  simp only [mapM_id_map_some]

theorem runsAllP_adviceScatter_values (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (Qs : List G₁)
    (hlen : Qs.length = vk.cs.numAdviceColumns) :
    RunsAllP E
      (([(List.zip (List.range vk.cs.numAdviceColumns) Qs)] :
          List (List (Nat × G₁))).foldlM (init := (#[] : Array (Array G₁)))
        fun acc pairs => do
          let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
            "proofs/src/plonk/verifier.rs:118")
          pure (acc.push row))
      ([] : List (Msg (Fr p) G₁)) (fun acc => acc.toList = [Qs.toArray]) := by
  have hsingle :
      List.foldlM (fun acc pairs => (do
        let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
          "proofs/src/plonk/verifier.rs:118")
        pure (acc.push row) : TranscriptM (Array (Array G₁))))
        (#[] : Array (Array G₁))
        [(List.zip (List.range vk.cs.numAdviceColumns) Qs)] =
      ((StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns
          (List.zip (List.range vk.cs.numAdviceColumns) Qs)
          "proofs/src/plonk/verifier.rs:118")) >>= fun row => pure (#[].push row)) := by
    simp [List.foldlM_cons]
  rw [hsingle]
  rw [scatterIndexed_zip_range vk.cs.numAdviceColumns Qs hlen
    "proofs/src/plonk/verifier.rs:118"]
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := [])
    (RunsAllP.lift_ok E Qs.toArray (fun row => row = Qs.toArray) rfl) ?_
  intro row hrow
  subst hrow
  exact RunsAllP.pure E (#[].push Qs.toArray) (fun acc => acc.toList = [Qs.toArray]) (by simp)

theorem runsAllP_parseTraceAdviceBlock_values (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hsp : vk.cs.numChallenges = 0)
    (horder : AdvicePhasesColumnOrder vk) (Qs : List G₁)
    (hlen : Qs.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum) :
    RunsAllP E
      (do let st ← parseTraceAdvicePhases E vk
          st.1.foldlM (init := (#[] : Array (Array G₁))) fun acc pairs => do
            let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
              "proofs/src/plonk/verifier.rs:118")
            pure (acc.push row))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun acc => acc.toList = [Qs.toArray]) := by
  have hlen' : Qs.length = (vk.cs.phases.flatMap (fun ph => phaseCols vk.cs ph)).length := by
    rw [length_flatMap_phaseCols, hlen]
  have hlenN : Qs.length = vk.cs.numAdviceColumns := by
    rw [hlen', horder, List.length_range]
  have hph := runsAllP_parseTraceAdvicePhases_values E vk hsp vk.cs.phases [] Qs
    (by simpa using hlen)
  rw [show (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) =
      Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []
      from (List.append_nil _).symm]
  refine RunsAllP.bind E (m := parseTraceAdvicePhases E vk)
    (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := []) hph ?_
  intro st hst
  rw [hst, horder]
  simpa using runsAllP_adviceScatter_values E vk Qs hlenN

theorem wireMsgs_map_fr (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (qs : List (Fr p)),
      wireMsgs E (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) = wireOf (p := p) qs
  | [] => by simp [wireMsgs, wireOf]
  | q :: qs => by
      simp only [List.map_cons, wireMsgs, wireOf]
      rw [wireMsgs_map_fr E qs]
      simp [msgWire]

theorem wireMsgs_g1_singleton (E : VerifierEnv p G₁ G₂ Gₜ) (Q : G₁) :
    wireMsgs E ([Msg.g1 Q] : List (Msg (Fr p) G₁)) = E.g1.toCompressed Q := by
  rw [show wireMsgs E ([Msg.g1 Q] : List (Msg (Fr p) G₁)) = msgWire E (Msg.g1 Q) ++ Bytes.empty from rfl]
  rw [bytes_append_empty_local]
  rfl

theorem runsAllP_parseTracePermutations_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (hdeg : 3 ≤ vk.csDegree) (Qs : List G₁)
    (hlen : Qs.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2)) :
    RunsAllP E (parseTracePermutations E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun rows => (rows.toList.map (fun pc =>
        3 * pc.permutationProductCommitments.size - 1)).sum =
        3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1) := by
  have hread := runsAllP_tmReadN_g1 E (Permutation.numChunksOf vk.cs.permutation.columns.size
    (vk.csDegree - 2)) Qs hlen
  have hpc : RunsAllP E
      (Permutation.readProductCommitments vk.cs.permutation vk.csDegree (hashableG1 E.g1))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun pc => pc.permutationProductCommitments.size =
        Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2)) := by
    unfold Permutation.readProductCommitments
    simp only [show 2 < vk.csDegree from by omega, show vk.csDegree - 2 > 0 from by omega,
      ↓reduceIte]
    refine RunsAllP.bind_nil E (m := tmReadN (hashableG1 E.g1)
      (Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2)))
      (ms := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) hread ?_
    intro arr harr
    exact RunsAllP.pure E _ _ harr
  rw [parseTracePermutations]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind]
  refine RunsAllP.bind_nil E (m := Permutation.readProductCommitments vk.cs.permutation
    vk.csDegree (hashableG1 E.g1))
    (ms := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) hpc ?_
  intro pc hpc'
  refine RunsAllP.pure E _ _ ?_
  simp [hpc']

theorem runsAllP_trashcansFold (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (ts : List (TrashArgument (Fr p))) (Qs : List G₁) (acc : Array (Trash.Committed G₁)),
      Qs.length = ts.length →
      RunsAllP E (ts.foldlM (init := acc) fun acc' t => do
          let c ← Trash.readCommitted t (hashableG1 E.g1)
          pure (acc'.push c)) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun row => row.size = acc.size + ts.length) := by
  intro ts
  induction ts with
  | nil =>
      intro Qs acc hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using (RunsAllP.pure E acc _ (by simp))
  | cons t ts ih =>
      intro Qs acc hlen
      obtain ⟨Q, Qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      rw [List.foldlM_cons]
      have hstep : RunsAllP E ((fun acc => do
          let c ← Trash.readCommitted t (hashableG1 E.g1)
          pure (acc.push c)) acc) ([Msg.g1 Q] : List (Msg (Fr p) G₁))
          (fun row => row.size = acc.size + 1) := by
        refine RunsAllP.bind_nil E (m := Trash.readCommitted t (hashableG1 E.g1))
          (ms := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (RunsAll.toRunsAllP E (runsAll_trash_readCommitted E t Q)) ?_
        intro c _
        refine RunsAllP.pure E (acc.push c) _ ?_
        simp
      have hb : RunsAllP E
          (((fun acc => do
            let c ← Trash.readCommitted t (hashableG1 E.g1)
            pure (acc.push c)) acc) >>= fun acc' =>
              ts.foldlM (init := acc') fun acc' t => do
                let c ← Trash.readCommitted t (hashableG1 E.g1)
                pure (acc'.push c))
          ([Msg.g1 Q] ++ Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun row => ∃ acc' : Array (Trash.Committed G₁), acc'.size = acc.size + 1 ∧
            row.size = acc'.size + ts.length) :=
        RunsAllP.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (ms₂ := Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          hstep (fun acc' hacc' => by
            have hb2 := ih Qs' acc' (by simpa using hlen)
            exact RunsAllP.mono E hb2 (fun row hrow => ⟨acc', hacc', hrow⟩))
      refine RunsAllP.mono E hb ?_
      intro row hrow
      obtain ⟨acc', hacc', hrow'⟩ := hrow
      rw [List.length_cons, hrow', hacc']
      omega

theorem runsAllP_parseTraceTrashcans_one (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (Qs : List G₁)
    (hlen : Qs.length = vk.cs.trashcans.size) :
    RunsAllP E (parseTraceTrashcans E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun rows => (rows.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size) := by
  let step : TranscriptM (Array (Array (Trash.Committed G₁))) :=
    do let row ← vk.cs.trashcans.toList.foldlM (init := #[]) fun acc' t => do
          let c ← Trash.readCommitted t (hashableG1 E.g1)
          pure (acc'.push c)
       pure (#[].push row)
  have hstep : RunsAllP E step (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun rows => (rows.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size) := by
    refine RunsAllP.bind_nil E (m := vk.cs.trashcans.toList.foldlM (init := #[])
      fun acc' t => do
        let c ← Trash.readCommitted t (hashableG1 E.g1)
        pure (acc'.push c))
      (ms := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (runsAllP_trashcansFold E vk.cs.trashcans.toList Qs
        (#[] : Array (Trash.Committed G₁)) (by simpa using hlen)) ?_
    intro row hrow
    refine RunsAllP.pure E (#[].push row) _ ?_
    simp [hrow]
  rw [parseTraceTrashcans]
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil]
  refine RunsAllP.bind_nil E (m := step) (ms := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (by simpa only [step] using hstep) ?_
  intro acc hacc
  exact RunsAllP.pure E acc _ hacc

theorem runsAllP_logup_readCommitment (E : VerifierEnv p G₁ G₂ Gₜ)
    (cm : Logup.CommittedMultiplicities G₁) (n : Nat) (Qs : List G₁)
    (hlen : Qs.length = n + 1) :
    RunsAllP E (cm.readCommitment n (hashableG1 E.g1))
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun c => c.helperPolys.size = n) := by
  have hle : n ≤ Qs.length := by omega
  have hlen1 : (Qs.take n).length = n := by rw [List.length_take]; omega
  have hlen2 : (Qs.drop n).length = 1 := by rw [List.length_drop]; omega
  have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
      (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
    rw [← List.map_append, List.take_append_drop]
  unfold Logup.CommittedMultiplicities.readCommitment
  rw [hsplit]
  refine RunsAllP.bind E (ms₁ := (Qs.take n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (Qs.drop n).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (runsAllP_tmReadN_g1 E n (Qs.take n) hlen1) ?_
  intro helperPolys hsz
  obtain ⟨Q, Qs', hQs'⟩ := List.exists_cons_of_length_pos (by rw [hlen2]; simp)
  have hQs'0 : Qs' = [] := List.eq_nil_of_length_eq_zero
    (by have h := hlen2; rw [hQs', List.length_cons] at h; omega)
  subst hQs'0
  rw [hQs']
  simp only [List.map_cons, List.map_nil]
  refine RunsAllP.bind_nil E (m := tmRead (hashableG1 E.g1))
    (ms := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
    (RunsAll.toRunsAllP E (runsAll_read_g1 E Q)) ?_
  intro accumulator _
  refine RunsAllP.pure E _ _ ?_
  exact hsz

def logupEvalSum (out : Array (Logup.Committed G₁)) : Nat :=
  (out.toList.map (fun c => c.helperPolys.size + 3)).sum

theorem logupEvalSum_push (acc : Array (Logup.Committed G₁)) (c : Logup.Committed G₁) :
    logupEvalSum (acc.push c) = logupEvalSum acc + (c.helperPolys.size + 3) := by
  unfold logupEvalSum
  rw [Array.toList_push, List.map_append, List.sum_append]
  simp

theorem sum_map_add_three (l : List Nat) :
    (l.map (fun n => n + 3)).sum = (l.map (fun n => n + 1)).sum + 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem runsAllP_lookupCommitments_row_count (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (row : List (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
      (acc : Array (Logup.Committed G₁)) (Qs : List G₁),
      Qs.length = (row.map (fun p => p.2.numChunks + 1)).sum →
      RunsAllP E (row.foldlM (init := acc) fun acc' p => do
          let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
          pure (acc'.push c)) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun out => logupEvalSum out = logupEvalSum acc +
          (row.map (fun p => p.2.numChunks + 3)).sum) := by
  intro row
  induction row with
  | nil =>
      intro acc Qs hlen
      have h0 : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      refine RunsAllP.pure E acc _ ?_
      simp
  | cons p ps ih =>
      intro acc Qs hlen
      obtain ⟨m, chunked⟩ := p
      have hsum : Qs.length = (chunked.numChunks + 1) +
          (ps.map (fun p => p.2.numChunks + 1)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      have hlen1 : (Qs.take (chunked.numChunks + 1)).length = chunked.numChunks + 1 := by
        rw [List.length_take]; omega
      have hlen2 : (Qs.drop (chunked.numChunks + 1)).length =
          (ps.map (fun p => p.2.numChunks + 1)).sum := by
        rw [List.length_drop, hsum]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      have hhead : RunsAllP E ((fun acc => do
          let c ← m.readCommitment chunked.numChunks (hashableG1 E.g1)
          pure (acc.push c)) acc)
          ((Qs.take (chunked.numChunks + 1)).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun out => logupEvalSum out = logupEvalSum acc + (chunked.numChunks + 3)) := by
        refine RunsAllP.bind_nil E (m := m.readCommitment chunked.numChunks (hashableG1 E.g1))
          (ms := (Qs.take (chunked.numChunks + 1)).map
            (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (runsAllP_logup_readCommitment E m chunked.numChunks
            (Qs.take (chunked.numChunks + 1)) hlen1) ?_
        intro c hc
        refine RunsAllP.pure E (acc.push c) _ ?_
        rw [logupEvalSum_push, hc]
      have hb : RunsAllP E
          (((fun acc => do
            let c ← m.readCommitment chunked.numChunks (hashableG1 E.g1)
            pure (acc.push c)) acc) >>= fun acc' =>
              ps.foldlM (init := acc') fun acc' p => do
                let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
                pure (acc'.push c))
          ((Qs.take (chunked.numChunks + 1)).map
              (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop (chunked.numChunks + 1)).map
              (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun out => ∃ acc' : Array (Logup.Committed G₁),
            logupEvalSum acc' = logupEvalSum acc + (chunked.numChunks + 3) ∧
            logupEvalSum out = logupEvalSum acc' +
              (ps.map (fun p => p.2.numChunks + 3)).sum) :=
        RunsAllP.bind E
          (ms₁ := (Qs.take (chunked.numChunks + 1)).map
            (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (ms₂ := (Qs.drop (chunked.numChunks + 1)).map
            (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (Q := fun (out : Array (Logup.Committed G₁)) =>
            ∃ acc' : Array (Logup.Committed G₁),
            logupEvalSum acc' = logupEvalSum acc + (chunked.numChunks + 3) ∧
            logupEvalSum out = logupEvalSum acc' +
              (ps.map (fun p => p.2.numChunks + 3)).sum)
          hhead (fun acc' hacc' => by
            have hb2 := ih acc' (Qs.drop (chunked.numChunks + 1)) hlen2
            exact RunsAllP.mono E hb2 (fun out hout => ⟨acc', hacc', hout⟩))
      refine RunsAllP.mono E hb ?_
      intro out hout
      obtain ⟨acc' : Array (Logup.Committed G₁), hacc', hout'⟩ := hout
      rw [hout', hacc', List.map_cons, List.sum_cons]
      simp only [Prod.snd]
      omega

theorem runsAllP_lookupMultiplicities_fold_count (E : VerifierEnv p G₁ G₂ Gₜ)
    (deg : Nat) :
    ∀ (ls : List (LogupBatchedArgument (Fr p)))
      (acc : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
      (Qs : List G₁),
      (∀ l ∈ ls, ∃ c, l.chunkByDegree deg = .ok c) →
      Qs.length = ls.length →
      RunsAllP E (ls.foldlM (init := acc) fun acc' l => do
          let chunked ← StateT.lift (l.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc'.push (m, chunked))) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun row => row.size = acc.size + ls.length) := by
  intro ls
  induction ls with
  | nil =>
      intro acc Qs hs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      simpa only [List.foldlM_nil, List.map_nil] using (RunsAllP.pure E acc _ (by simp))
  | cons l ls ih =>
      intro acc Qs hs hlen
      obtain ⟨Q, Qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      obtain ⟨c, hc⟩ := hs l (by simp)
      rw [List.foldlM_cons]
      have hstep : RunsAllP E ((fun acc => do
          let chunked ← StateT.lift (l.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc.push (m, chunked))) acc) ([Msg.g1 Q] : List (Msg (Fr p) G₁))
          (fun row => row.size = acc.size + 1) := by
        have hlift : RunsAllP E
            (StateT.lift (l.chunkByDegree deg : Except Fault (LogupChunkedArgument (Fr p)))) []
            (fun v => v = c) :=
          RunsAllP.congr E (fun t => by rw [hc])
            (RunsAllP.lift_ok E c (fun v => v = c) rfl)
        refine RunsAllP.bind E (m := StateT.lift (l.chunkByDegree deg))
          (ms₁ := ([] : List (Msg (Fr p) G₁)))
          (ms₂ := ([Msg.g1 Q] : List (Msg (Fr p) G₁))) hlift ?_
        intro chunked hchunked
        subst hchunked
        refine RunsAllP.bind_nil E (m := Logup.readMultiplicities chunked (hashableG1 E.g1))
          (ms := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (RunsAll.toRunsAllP E (runsAll_logup_readMultiplicities E chunked Q)) ?_
        intro m _
        refine RunsAllP.pure E (acc.push (m, chunked)) _ ?_
        simp
      have hb : RunsAllP E
          (((fun acc => do
            let chunked ← StateT.lift (l.chunkByDegree deg)
            let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
            pure (acc.push (m, chunked))) acc) >>= fun acc' =>
              ls.foldlM (init := acc') fun acc' l => do
                let chunked ← StateT.lift (l.chunkByDegree deg)
                let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
                pure (acc'.push (m, chunked)))
          ((Msg.g1 Q : Msg (Fr p) G₁) :: Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun row => ∃ acc' : Array (Logup.CommittedMultiplicities G₁ ×
              LogupChunkedArgument (Fr p)),
            acc'.size = acc.size + 1 ∧ row.size = acc'.size + ls.length) := by
        refine RunsAllP.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (ms₂ := Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) hstep ?_
        intro acc' hacc'
        have hb2 := ih acc' Qs' (fun l' hl' => hs l' (by simp [hl'])) (by simpa using hlen)
        exact RunsAllP.mono E hb2 (fun row hrow => ⟨acc', hacc', hrow⟩)
      refine RunsAllP.mono E hb ?_
      intro row hrow
      obtain ⟨acc' : Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p)), hacc', hrow'⟩ := hrow
      rw [List.length_cons, hrow', hacc']
      omega

def rowEvalSum (row : Array (Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p))) : Nat :=
  (row.toList.map (fun p => p.2.numChunks + 3)).sum

def rowsEvalSum (rows : Array (Array (Logup.Committed G₁))) : Nat :=
  (rows.toList.map logupEvalSum).sum

theorem rowsEvalSum_push (acc : Array (Array (Logup.Committed G₁)))
    (row : Array (Logup.Committed G₁)) :
    rowsEvalSum (acc.push row) = rowsEvalSum acc + logupEvalSum row := by
  unfold rowsEvalSum
  rw [Array.toList_push, List.map_append, List.sum_append]
  simp

theorem runsAllP_lookupCommitments_rows_count (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (rows : List (Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p))))
      (acc : Array (Array (Logup.Committed G₁))) (Qs : List G₁),
      Qs.length = (rows.map (fun row => (row.toList.map
        (fun p => p.2.numChunks + 1)).sum)).sum →
      RunsAllP E (rows.foldlM (init := acc) fun acc row => do
          let out ← row.toList.foldlM (init := #[]) fun acc' p => do
            let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
            pure (acc'.push c)
          pure (acc.push out)) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun out => rowsEvalSum out = rowsEvalSum acc +
          (rows.map rowEvalSum).sum) := by
  intro rows
  induction rows with
  | nil =>
      intro acc Qs hlen
      have h0 : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst h0
      refine RunsAllP.pure E acc _ ?_
      simp [rowsEvalSum]
  | cons row rows ih =>
      intro acc Qs hlen
      have hsum : Qs.length = (row.toList.map (fun p => p.2.numChunks + 1)).sum +
          (rows.map (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
        simpa only [List.map_cons, List.sum_cons] using hlen
      obtain ⟨rowLen, hrowLen⟩ : ∃ k, (row.toList.map (fun p => p.2.numChunks + 1)).sum = k :=
        ⟨_, rfl⟩
      have hlen1 : (Qs.take rowLen).length =
          (row.toList.map (fun p => p.2.numChunks + 1)).sum := by
        rw [List.length_take]; omega
      have hlen2 : (Qs.drop rowLen).length =
          (rows.map (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
        rw [List.length_drop]; omega
      have hsplit : Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          (Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
        rw [← List.map_append, List.take_append_drop]
      rw [List.foldlM_cons, hsplit]
      have hhead : RunsAllP E ((fun acc => do
          let out ← row.toList.foldlM (init := #[]) fun acc' p => do
            let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
            pure (acc'.push c)
          pure (acc.push out)) acc)
          ((Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun out => rowsEvalSum out = rowsEvalSum acc + rowEvalSum row) := by
        refine RunsAllP.bind_nil E (m := row.toList.foldlM (init := #[])
          fun acc' p => do
            let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
            pure (acc'.push c))
          (ms := (Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (runsAllP_lookupCommitments_row_count E row.toList #[] (Qs.take rowLen) hlen1) ?_
        intro out hout
        refine RunsAllP.pure E (acc.push out) _ ?_
        rw [rowsEvalSum_push, hout]
        simp [logupEvalSum, rowEvalSum]
      have hb : RunsAllP E
          (((fun acc => do
            let out ← row.toList.foldlM (init := #[]) fun acc' p => do
              let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
              pure (acc'.push c)
            pure (acc.push out)) acc) >>= fun acc' =>
              rows.foldlM (init := acc') fun acc' row => do
                let out ← row.toList.foldlM (init := #[]) fun acc' p => do
                  let c ← p.1.readCommitment p.2.numChunks (hashableG1 E.g1)
                  pure (acc'.push c)
                pure (acc'.push out))
          ((Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (Qs.drop rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun out => ∃ acc' : Array (Array (Logup.Committed G₁)),
            rowsEvalSum acc' = rowsEvalSum acc + rowEvalSum row ∧
            rowsEvalSum out = rowsEvalSum acc' + (rows.map rowEvalSum).sum) := by
        refine RunsAllP.bind E
          (ms₁ := (Qs.take rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (ms₂ := (Qs.drop rowLen).map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) hhead ?_
        intro acc' hacc'
        have hb2 := ih acc' (Qs.drop rowLen) hlen2
        exact RunsAllP.mono E hb2 (fun out hout => ⟨acc', hacc', hout⟩)
      refine RunsAllP.mono E hb ?_
      intro out hout
      obtain ⟨acc' : Array (Array (Logup.Committed G₁)), hacc', hout'⟩ := hout
      rw [hout', hacc', List.map_cons, List.sum_cons]
      omega

theorem sum_rows_flatMap (rows : List (List (Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p)))) (f : Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p) → Nat) :
    (rows.map (fun row => (row.map f).sum)).sum = ((rows.flatMap (fun row => row)).map f).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append, ih]

theorem rowEvalSum_eq (row : Array (Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p))) :
    rowEvalSum row = (row.toList.map (fun p => p.2.numChunks + 1)).sum +
      2 * row.toList.length := by
  unfold rowEvalSum
  have h := sum_map_add_three (row.toList.map (fun p => p.2.numChunks))
  simpa only [List.map_map, Function.comp_def, List.length_map] using h

theorem sum_rows_rowEvalSum_eq (rows : List (Array (Logup.CommittedMultiplicities G₁ ×
    LogupChunkedArgument (Fr p)))) :
    (rows.map rowEvalSum).sum =
      (rows.map (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum +
      2 * (rows.map (fun row => row.toList.length)).sum := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      rw [List.map_cons, List.sum_cons, ih, rowEvalSum_eq]
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      omega

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem lookupChunkSum_add_three (l : List (LogupBatchedArgument (Fr p))) (deg : Nat) :
    (l.map (fun x => lookupChunkNum deg x + 3)).sum =
      (l.map (fun x => lookupChunkNum deg x + 1)).sum + 2 * l.length := by
  have h := sum_map_add_three (l.map (fun x => lookupChunkNum deg x))
  simpa only [List.map_map, Function.comp_def, List.length_map] using h

theorem runsAllP_parseTraceLookupCommitments_count (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (rows : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) (Qs : List G₁)
    (hlen : Qs.length = (rows.toList.map (fun row => (row.toList.map
      (fun p => p.2.numChunks + 1)).sum)).sum)
    (hledger : (rows.toList.map (fun row => (row.toList.map
      (fun p => p.2.numChunks + 1)).sum)).sum =
      (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hcount : (rows.toList.map (fun row => row.toList.length)).sum =
      vk.cs.lookups.size) :
    RunsAllP E (parseTraceLookupCommitments E rows)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun out => (out.toList.map (fun row => (row.toList.map
        (fun c => c.helperPolys.size + 3)).sum)).sum =
        (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum) := by
  rw [parseTraceLookupCommitments]
  have h := runsAllP_lookupCommitments_rows_count E rows.toList
    (#[] : Array (Array (Logup.Committed G₁))) Qs hlen
  refine RunsAllP.mono E h ?_
  intro out hout
  have hzero : rowsEvalSum (#[] : Array (Array (Logup.Committed G₁))) = 0 := rfl
  rw [hzero, Nat.zero_add] at hout
  change rowsEvalSum out = (vk.cs.lookups.toList.map
    (fun l => lookupChunkNum vk.csDegree l + 3)).sum
  rw [hout, sum_rows_rowEvalSum_eq, hledger, hcount, lookupChunkSum_add_three,
    Array.length_toList]

theorem runsAllP_lookupMultiplicities_fold_both (E : VerifierEnv p G₁ G₂ Gₜ)
    (deg : Nat) :
    ∀ (ls : List (LogupBatchedArgument (Fr p)))
      (acc : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
      (Qs : List G₁),
      (∀ l ∈ ls, ∃ c, l.chunkByDegree deg = .ok c) →
      Qs.length = ls.length →
      RunsAllP E (ls.foldlM (init := acc) fun acc' l => do
          let chunked ← StateT.lift (l.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
          pure (acc'.push (m, chunked))) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
        (fun row => ledgerPairs row = ledgerPairs acc +
          (ls.map (fun l => lookupChunkNum deg l + 1)).sum ∧
          row.size = acc.size + ls.length) := by
  intro ls
  induction ls with
  | nil =>
      intro acc Qs hs hlen
      have hQs : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hQs
      refine RunsAllP.pure E acc _ ⟨?_, ?_⟩ <;> simp
  | cons l ls ih =>
      intro acc Qs hs hlen
      obtain ⟨Q, Qs', rfl⟩ := List.exists_cons_of_length_pos (by rw [hlen]; simp)
      obtain ⟨c, hc⟩ := hs l (by simp)
      rw [List.foldlM_cons]
      have hhead : RunsAllP E
          ((fun acc => do
            let chunked ← StateT.lift (l.chunkByDegree deg)
            let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
            pure (acc.push (m, chunked))) acc)
          ([Msg.g1 Q] : List (Msg (Fr p) G₁))
          (fun row => ledgerPairs row = ledgerPairs acc + (lookupChunkNum deg l + 1) ∧
            row.size = acc.size + 1) := by
        have hstep := RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
          (ms₂ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (RunsAllP.lift_ok E c (fun chunked => l.chunkByDegree deg = .ok chunked) hc)
          (fun chunked hchunked =>
            RunsAllP.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁))) (ms₂ := [])
              (RunsAll.toRunsAllP E (runsAll_logup_readMultiplicities E chunked Q))
              (fun m _ => RunsAllP.pure E (acc.push (m, chunked))
                (fun row => ledgerPairs row = ledgerPairs acc + (lookupChunkNum deg l + 1) ∧
                  row.size = acc.size + 1)
                (by
                  refine ⟨?_, ?_⟩
                  · rw [ledgerPairs_push, chunkNum_eq deg l chunked hchunked]
                  · simp)))
        simpa only [List.nil_append, hc] using hstep
      have hb : RunsAllP E
          ((fun acc => do
            let chunked ← StateT.lift (l.chunkByDegree deg)
            let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
            pure (acc.push (m, chunked))) acc >>= fun acc' =>
              ls.foldlM (init := acc') fun acc' l => do
                let chunked ← StateT.lift (l.chunkByDegree deg)
                let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
                pure (acc'.push (m, chunked)))
          ([Msg.g1 Q] ++ Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (fun row => ∃ acc', ledgerPairs acc' = ledgerPairs acc +
              (lookupChunkNum deg l + 1) ∧ acc'.size = acc.size + 1 ∧
            ledgerPairs row = ledgerPairs acc' +
              (ls.map (fun l => lookupChunkNum deg l + 1)).sum ∧
            row.size = acc'.size + ls.length) :=
        RunsAllP.bind E (ms₁ := ([Msg.g1 Q] : List (Msg (Fr p) G₁)))
          (ms₂ := Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          hhead (fun acc' hacc' => by
            have hb2 := ih acc' Qs' (fun l' hl' => hs l' (by simp [hl'])) (by simpa using hlen)
            exact RunsAllP.mono E hb2 (fun row hrow =>
              ⟨acc', hacc'.1, hacc'.2, hrow.1, hrow.2⟩))
      refine RunsAllP.mono E hb ?_
      intro row hrow
      obtain ⟨acc', hled, hsz, hrowl, hrowsz⟩ := hrow
      refine ⟨?_, ?_⟩
      · rw [hrowl, hled, List.map_cons, List.sum_cons]; omega
      · rw [hrowsz, hsz, List.length_cons]
        omega

theorem runsAllP_parseTraceLookupMultiplicities_one_both (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (Qs : List G₁) (hlen : Qs.length = vk.cs.lookups.size) :
    RunsAllP E (parseTraceLookupMultiplicities E vk 1)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun rows => (rows.toList.map (fun row => (row.toList.map
        (fun p => p.2.numChunks + 1)).sum)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum ∧
        (rows.toList.map (fun row => row.toList.length)).sum = vk.cs.lookups.size) := by
  unfold parseTraceLookupMultiplicities
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind]
  let inner : TranscriptM (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) :=
    List.foldlM (init := #[]) (fun acc' l => do
      let chunked ← StateT.lift (l.chunkByDegree vk.csDegree)
      let m ← Logup.readMultiplicities chunked (hashableG1 E.g1)
      pure (acc'.push (m, chunked))) vk.cs.lookups.toList
  let Post : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) → Prop :=
    fun rows => (rows.toList.map (fun row => (row.toList.map
        (fun p => p.2.numChunks + 1)).sum)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum ∧
        (rows.toList.map (fun row => row.toList.length)).sum = vk.cs.lookups.size
  have hinner : RunsAllP E inner (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
      (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 1)).sum ∧
        row.size = vk.cs.lookups.size) := by
    simpa [inner, ledgerPairs] using
      runsAllP_lookupMultiplicities_fold_both E vk.csDegree vk.cs.lookups.toList #[] Qs hs hlen
  let f1 : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) →
      TranscriptM (Array (Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p)))) :=
    fun row => pure (#[].push row)
  have hstep : RunsAllP E (inner >>= f1) (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) Post := by
    have hb := RunsAllP.bind E (m := inner) (f := f1)
      (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      hinner (fun row hrow => by
        refine RunsAllP.pure E (#[].push row) Post ?_
        dsimp only [Post]
        refine ⟨?_, ?_⟩
        · simpa using hrow.1
        · simpa [hrow.2])
    rw [List.append_nil] at hb
    exact hb
  have hb : RunsAllP E ((inner >>= f1) >>= fun init => pure init)
      (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) Post := by
    have hb2 := RunsAllP.bind E (m := inner >>= f1) (f := fun init => (pure init : TranscriptM _))
      (ms₁ := Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) (ms₂ := [])
      hstep (fun acc hacc => RunsAllP.pure E acc Post hacc)
    rw [List.append_nil] at hb2
    exact hb2
  simpa only [inner, f1, Post, bind_assoc, pure_bind] using hb

theorem runsAllP_parseTraceTail (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (adviceCommitments : Array (Array G₁)) (challenges : Array (Fr p))
    (QMult QPerm QLook QTrash : List G₁)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E
      (do let theta ← tmSqueezeChallenge
          let lookupMultiplicities ← parseTraceLookupMultiplicities E vk 1
          let beta ← tmSqueezeChallenge
          let gamma ← tmSqueezeChallenge
          let permutations ← parseTracePermutations E vk 1
          let lookups ← parseTraceLookupCommitments E lookupMultiplicities
          let trashChallenge ← tmSqueezeChallenge
          let trashcans ← parseTraceTrashcans E vk 1
          let y ← tmSqueezeChallenge
          pure ({ adviceCommitments := adviceCommitments, lookups := lookups, trashcans := trashcans, permutations := permutations, challenges := challenges, beta := beta, gamma := gamma, theta := theta, trashChallenge := trashChallenge, y := y } : VerifierTrace (Fr p) G₁))
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
      (fun tr =>
        (tr.permutations.toList.map (fun pc =>
          3 * pc.permutationProductCommitments.size - 1)).sum =
          3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1 ∧
        (tr.lookups.toList.map (fun row => (row.toList.map
          (fun c => c.helperPolys.size + 3)).sum)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum ∧
        (tr.trashcans.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size) := by
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAllP.squeeze E) ?_
  intro theta _
  refine RunsAllP.bind E (m := parseTraceLookupMultiplicities E vk 1)
    (ms₁ := QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (runsAllP_parseTraceLookupMultiplicities_one_both E vk hs QMult hlenMult) ?_
  intro rows hrows
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (RunsAllP.squeeze E) ?_
  intro beta _
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (RunsAllP.squeeze E) ?_
  intro gamma _
  refine RunsAllP.bind E (m := parseTracePermutations E vk 1)
    (ms₁ := QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))
    (runsAllP_parseTracePermutations_one E vk hdeg QPerm hlenPerm) ?_
  intro permutations hperm
  have hlenLook' : QLook.length = (rows.toList.map
      (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
    rw [hlenLook]
    exact hrows.1.symm
  refine RunsAllP.bind E (m := parseTraceLookupCommitments E rows)
    (ms₁ := QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])
    (runsAllP_parseTraceLookupCommitments_count E vk rows QLook hlenLook' hrows.1 hrows.2) ?_
  intro lookups hlook
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])
    (RunsAllP.squeeze E) ?_
  intro trashChallenge _
  refine RunsAllP.bind E (m := parseTraceTrashcans E vk 1)
    (ms₁ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := ([] : List (Msg (Fr p) G₁)))
    (runsAllP_parseTraceTrashcans_one E vk QTrash hlenTrash) ?_
  intro trashcans htrash
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := ([] : List (Msg (Fr p) G₁)))
    (RunsAllP.squeeze E) ?_
  intro y _
  exact RunsAllP.pure E _ _ ⟨hperm, hlook, htrash⟩

theorem runsAllP_parseTraceTail_advice (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (adviceCommitments : Array (Array G₁)) (challenges : Array (Fr p))
    (QMult QPerm QLook QTrash : List G₁)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E
      (do let theta ← tmSqueezeChallenge
          let lookupMultiplicities ← parseTraceLookupMultiplicities E vk 1
          let beta ← tmSqueezeChallenge
          let gamma ← tmSqueezeChallenge
          let permutations ← parseTracePermutations E vk 1
          let lookups ← parseTraceLookupCommitments E lookupMultiplicities
          let trashChallenge ← tmSqueezeChallenge
          let trashcans ← parseTraceTrashcans E vk 1
          let y ← tmSqueezeChallenge
          pure ({ adviceCommitments := adviceCommitments, lookups := lookups, trashcans := trashcans, permutations := permutations, challenges := challenges, beta := beta, gamma := gamma, theta := theta, trashChallenge := trashChallenge, y := y } : VerifierTrace (Fr p) G₁))
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
      (fun tr =>
        tr.adviceCommitments = adviceCommitments ∧
        (tr.permutations.toList.map (fun pc =>
          3 * pc.permutationProductCommitments.size - 1)).sum =
          3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1 ∧
        (tr.lookups.toList.map (fun row => (row.toList.map
          (fun c => c.helperPolys.size + 3)).sum)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum ∧
        (tr.trashcans.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size) := by
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAllP.squeeze E) ?_
  intro theta _
  refine RunsAllP.bind E (m := parseTraceLookupMultiplicities E vk 1)
    (ms₁ := QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (runsAllP_parseTraceLookupMultiplicities_one_both E vk hs QMult hlenMult) ?_
  intro rows hrows
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (RunsAllP.squeeze E) ?_
  intro beta _
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))
    (RunsAllP.squeeze E) ?_
  intro gamma _
  refine RunsAllP.bind E (m := parseTracePermutations E vk 1)
    (ms₁ := QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))
    (runsAllP_parseTracePermutations_one E vk hdeg QPerm hlenPerm) ?_
  intro permutations hperm
  have hlenLook' : QLook.length = (rows.toList.map
      (fun row => (row.toList.map (fun p => p.2.numChunks + 1)).sum)).sum := by
    rw [hlenLook]
    exact hrows.1.symm
  refine RunsAllP.bind E (m := parseTraceLookupCommitments E rows)
    (ms₁ := QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])
    (runsAllP_parseTraceLookupCommitments_count E vk rows QLook hlenLook' hrows.1 hrows.2) ?_
  intro lookups hlook
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])
    (RunsAllP.squeeze E) ?_
  intro trashChallenge _
  refine RunsAllP.bind E (m := parseTraceTrashcans E vk 1)
    (ms₁ := QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := ([] : List (Msg (Fr p) G₁)))
    (runsAllP_parseTraceTrashcans_one E vk QTrash hlenTrash) ?_
  intro trashcans htrash
  refine RunsAllP.bind E (m := tmSqueezeChallenge)
    (ms₁ := ([] : List (Msg (Fr p) G₁))) (ms₂ := ([] : List (Msg (Fr p) G₁)))
    (RunsAllP.squeeze E) ?_
  intro y _
  exact RunsAllP.pure E _ _ ⟨rfl, hperm, hlook, htrash⟩

theorem runsAllP_parseTraceWireBody_sizes (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hsp : vk.cs.numChallenges = 0)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E (parseTraceWireBody E vk inst)
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) (fun tr =>
        (tr.permutations.toList.map (fun pc =>
          3 * pc.permutationProductCommitments.size - 1)).sum =
          3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1 ∧
        (tr.lookups.toList.map (fun row => (row.toList.map
          (fun c => c.helperPolys.size + 3)).sum)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum ∧
        (tr.trashcans.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size) := by
  unfold parseTraceWireBody
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (runsAll_hashInto E vk)) ?_
  intro _ _
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (by
      simpa only [Array.forIn_toList] using
        runsAll_absorb_committed E (committedShape (G₁ := G₁)))) ?_
  intro _ _
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (by
      simpa only [Array.forIn_toList] using
        runsAll_absorb_instance E (instanceShape inst))) ?_
  intro _ _
  refine RunsAllP.bind E (m := parseTraceAdvicePhases E vk)
    (ms₁ := QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (runsAllP_parseTraceAdvicePhases_cover E vk hsp vk.cs.phases [] QAdv
      (by simpa using hlenAdv)) ?_
  intro st hst
  obtain ⟨row', rfl, _, hcov⟩ := hst
  have hcov' : ∀ pairs ∈ ([row'] : List (List (Nat × G₁))),
      ∀ i < vk.cs.numAdviceColumns, ∃ a, (i, a) ∈ pairs := by
    intro pairs hp i hi
    simp only [List.mem_singleton] at hp
    subst hp
    obtain ⟨ph, hph, hiph⟩ := adviceCols_cover vk hf hi
    exact hcov ph hph i hiph
  refine RunsAllP.bind E (m := ([row'] : List (List (Nat × G₁))).foldlM
      (init := (#[] : Array (Array G₁))) fun acc pairs => do
        let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
          "proofs/src/plonk/verifier.rs:118")
        pure (acc.push row))
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAll.toRunsAllP E (runsAll_adviceScatter E vk [row'] #[] hcov')) ?_
  intro adviceCommitments _
  obtain ⟨xs, hxs⟩ := scatterIndexed_ok_of_cover 0 ([] : List (Nat × Fr p))
    "proofs/src/plonk/verifier.rs:134" (fun i hi => by omega)
  rw [hsp, hxs]
  refine RunsAllP.bind E (m := StateT.lift (.ok xs : Except Fault (Array (Fr p))))
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAllP.lift_ok E xs (fun _ => True) trivial) ?_
  intro challenges _
  exact runsAllP_parseTraceTail E vk hdeg hs adviceCommitments challenges
    QMult QPerm QLook QTrash hlenMult hlenPerm hlenLook hlenTrash

theorem runsAllP_parseTraceWireBody_advice (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hsp : vk.cs.numChallenges = 0)
    (horder : AdvicePhasesColumnOrder vk)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E (parseTraceWireBody E vk inst)
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
      (fun tr => tr.adviceCommitments.getD 0 #[] = QAdv.toArray) := by
  unfold parseTraceWireBody
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (runsAll_hashInto E vk)) ?_
  intro _ _
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (by
      simpa only [Array.forIn_toList] using
        runsAll_absorb_committed E (committedShape (G₁ := G₁)))) ?_
  intro _ _
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
    (RunsAll.toRunsAllP E (by
      simpa only [Array.forIn_toList] using
        runsAll_absorb_instance E (instanceShape inst))) ?_
  intro _ _
  -- advice phase values
  have hph := runsAllP_parseTraceAdvicePhases_values E vk hsp vk.cs.phases [] QAdv
    (by simpa using hlenAdv)
  refine RunsAllP.bind E (m := parseTraceAdvicePhases E vk)
    (ms₁ := QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    hph ?_
  intro st hst
  rw [hst, horder]
  have hlenN : QAdv.length = vk.cs.numAdviceColumns := by
    have hlen' : QAdv.length =
        (vk.cs.phases.flatMap (fun ph => phaseCols vk.cs ph)).length := by
      rw [length_flatMap_phaseCols, hlenAdv]
    rw [hlen', horder, List.length_range]
  -- advice scatter value
  have hscat : RunsAllP E
      (([(List.zip (List.range vk.cs.numAdviceColumns) QAdv)] :
          List (List (Nat × G₁))).foldlM (init := (#[] : Array (Array G₁)))
        fun acc pairs => do
          let row ← StateT.lift (Midfall.Halo2.scatterIndexed vk.cs.numAdviceColumns pairs
            "proofs/src/plonk/verifier.rs:118")
          pure (acc.push row))
      ([] : List (Msg (Fr p) G₁)) (fun acc => acc.toList = [QAdv.toArray]) :=
    runsAllP_adviceScatter_values E vk QAdv hlenN
  refine RunsAllP.bind E (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    hscat ?_
  intro acc hacc
  have hacc' : acc.getD 0 #[] = QAdv.toArray := by
    have haccEq : acc = #[QAdv.toArray] := by
      apply Array.toList_inj.mp
      rw [hacc]
    rw [haccEq]
    rfl
  -- challenges scatter (empty)
  obtain ⟨xs, hxs⟩ := scatterIndexed_ok_of_cover 0 ([] : List (Nat × Fr p))
    "proofs/src/plonk/verifier.rs:134" (fun i hi => by omega)
  rw [hsp, hxs]
  refine RunsAllP.bind E (m := StateT.lift (.ok xs : Except Fault (Array (Fr p))))
    (ms₁ := ([] : List (Msg (Fr p) G₁)))
    (ms₂ := (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
    (RunsAllP.lift_ok E xs (fun _ => True) trivial) ?_
  intro challenges _
  refine RunsAllP.mono E
    (runsAllP_parseTraceTail_advice E vk hdeg hs acc challenges QMult QPerm QLook QTrash
      hlenMult hlenPerm hlenLook hlenTrash) ?_
  intro tr htr
  rw [htr.1, hacc']


end Midfall.LoweringV3.TranscriptRows
namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem runsAllP_parseTrace_one_sizes (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity)
    (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E (parseTrace (p := p) E.g1 Features.solidity vk
        (committedShape (G₁ := G₁)) (instanceShape inst))
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
      (fun tr =>
        (tr.permutations.toList.map (fun pc =>
          3 * pc.permutationProductCommitments.size - 1)).sum =
          3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1 ∧
        (tr.lookups.toList.map (fun row => (row.toList.map
          (fun c => c.helperPolys.size + 3)).sum)).sum =
          (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum ∧
        (tr.trashcans.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size) := by
  unfold parseTrace
  simp only [Features.solidity, ite_true]
  rw [if_neg (by simp [committedShape])]
  rw [if_neg (by simp [committedShape])]
  rw [if_neg (by simp [committedShape, instanceShape, hnc])]
  exact runsAllP_parseTraceWireBody_sizes E vk inst hf hsp hdeg hs QAdv QMult QPerm QLook QTrash
    hlenAdv hlenMult hlenPerm hlenLook hlenTrash

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem runsAllP_parseTrace_advice (E : VerifierEnv p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity)
    (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0)
    (horder : AdvicePhasesColumnOrder vk)
    (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size) :
    RunsAllP E (parseTrace (p := p) E.g1 Features.solidity vk
        (committedShape (G₁ := G₁)) (instanceShape inst))
      (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))
      (fun tr => tr.adviceCommitments.getD 0 #[] = QAdv.toArray) := by
  unfold parseTrace
  simp only [Features.solidity, ite_true]
  rw [if_neg (by simp [committedShape])]
  rw [if_neg (by simp [committedShape])]
  rw [if_neg (by simp [committedShape, instanceShape, hnc])]
  exact runsAllP_parseTraceWireBody_advice E vk inst hf hsp horder hdeg hs
    QAdv QMult QPerm QLook QTrash hlenAdv hlenMult hlenPerm hlenLook hlenTrash

theorem parseTrace_run_of_ms_sizes (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0) (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size)
    (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth)
    (ms : List (Msg (Fr p) G₁))
    (hms : ms = QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) :
    ∃ trace t1,
      (parseTrace (p := p) E.g1 Features.solidity vk
        (committedShape (G₁ := G₁)) (instanceShape inst)).run (transcriptOf E H ms) =
        .ok (trace, t1) ∧
      (trace.permutations.toList.map (fun pc =>
        3 * pc.permutationProductCommitments.size - 1)).sum =
        3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1 ∧
      (trace.lookups.toList.map (fun row => (row.toList.map
        (fun c => c.helperPolys.size + 3)).sum)).sum =
        (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum ∧
      (trace.trashcans.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size := by
  subst hms
  obtain ⟨trace, t1, hrun, _, _, hP⟩ :=
    runsAllP_parseTrace_one_sizes E vk inst hf hnc hsp hdeg hs QAdv QMult QPerm QLook QTrash
      hlenAdv hlenMult hlenPerm hlenLook hlenTrash
      (transcriptOf E H (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))))
      ByteArray.empty ByteArray.empty (by
        rw [(transcriptOf_buffer E H _).1]
        simp) (by rw [(transcriptOf_buffer E H _).2]; rfl) hp henc hwidth
  exact ⟨trace, t1, hrun, hP⟩

theorem map_slot_split (s2 : List Midfall.Lowering.WireSlot) :
    ∀ (s1 : List Midfall.Lowering.WireSlot) (ms : List (Msg (Fr p) G₁)),
      ms.map Msg.slot = s1 ++ s2 →
      ∃ ms1 ms2, ms = ms1 ++ ms2 ∧ ms1.map Msg.slot = s1 ∧ ms2.map Msg.slot = s2
  | [], ms, h => ⟨[], ms, rfl, rfl, h⟩
  | s :: s1, ms, h => by
      rw [List.cons_append, List.map_eq_cons_iff] at h
      obtain ⟨m, ms', rfl, hm, htail⟩ := h
      obtain ⟨ms1, ms2, rfl, h1, h2⟩ := map_slot_split s2 s1 ms' htail
      exact ⟨m :: ms1, ms2, rfl, by simp [hm, h1], h2⟩

theorem map_slot_eq_replicate_g1 {n : Nat} :
    ∀ (ms : List (Msg (Fr p) G₁)),
      ms.map Msg.slot = List.replicate n Midfall.Lowering.WireSlot.g1 →
      ∃ P : List G₁, ms = P.map Msg.g1 ∧ P.length = n
  | [], h => by
      have hn : n = 0 := by
        by_contra hn
        have : List.replicate n Midfall.Lowering.WireSlot.g1 ≠ [] := by
          cases n with
          | zero => exact absurd rfl hn
          | succ k => simp
        exact this (by simpa using h.symm)
      subst hn
      exact ⟨[], rfl, rfl⟩
  | m :: ms, h => by
      rw [List.map_cons] at h
      cases n with
      | zero => simp at h
      | succ n' =>
          rw [List.replicate_succ] at h
          injection h with hm htail
          cases m with
          | g1 Q =>
              obtain ⟨P, rfl, hlen⟩ := map_slot_eq_replicate_g1 ms htail
              exact ⟨Q :: P, rfl, by simp [hlen]⟩
          | fr q => simp [Msg.slot] at hm

theorem map_slot_eq_replicate_fr {n : Nat} :
    ∀ (ms : List (Msg (Fr p) G₁)),
      ms.map Msg.slot = List.replicate n Midfall.Lowering.WireSlot.fr →
      ∃ R : List (Fr p), ms = R.map Msg.fr ∧ R.length = n
  | [], h => by
      have hn : n = 0 := by
        by_contra hn
        have : List.replicate n Midfall.Lowering.WireSlot.fr ≠ [] := by
          cases n with
          | zero => exact absurd rfl hn
          | succ k => simp
        exact this (by simpa using h.symm)
      subst hn
      exact ⟨[], rfl, rfl⟩
  | m :: ms, h => by
      rw [List.map_cons] at h
      cases n with
      | zero => simp at h
      | succ n' =>
          rw [List.replicate_succ] at h
          injection h with hm htail
          cases m with
          | g1 Q => simp [Msg.slot] at hm
          | fr q =>
              obtain ⟨R, rfl, hlen⟩ := map_slot_eq_replicate_fr ms htail
              exact ⟨q :: R, rfl, by simp [hlen]⟩

theorem map_slot_eq_singleton_g1 :
    ∀ (ms : List (Msg (Fr p) G₁)),
      ms.map Msg.slot = [Midfall.Lowering.WireSlot.g1] →
      ∃ Q : G₁, ms = [Msg.g1 Q]
  | [], h => by simp at h
  | m :: ms, h => by
      rw [List.map_cons] at h
      injection h with hm htail
      cases m with
      | g1 Q =>
          have : ms = [] := by simpa using htail
          subst this
          exact ⟨Q, rfl⟩
      | fr q => simp [Msg.slot] at hm

theorem decoded_coarse_split (ms : List (Msg (Fr p) G₁)) (a b c : Nat)
    (h : ms.map Msg.slot = List.replicate a Midfall.Lowering.WireSlot.g1 ++
      (List.replicate b Midfall.Lowering.WireSlot.fr ++
        ([Midfall.Lowering.WireSlot.g1] ++ (List.replicate c Midfall.Lowering.WireSlot.fr ++
          [Midfall.Lowering.WireSlot.g1])))) :
    ∃ (P : List G₁) (R : List (Fr p)) (fCom : G₁) (qs : List (Fr p)) (pi : G₁),
      ms = P.map Msg.g1 ++ R.map Msg.fr ++ [Msg.g1 fCom] ++ qs.map Msg.fr ++ [Msg.g1 pi] ∧
      P.length = a ∧ R.length = b ∧ qs.length = c := by
  obtain ⟨A, r1, rfl, hA, h1⟩ := map_slot_split (List.replicate b Midfall.Lowering.WireSlot.fr ++
    ([Midfall.Lowering.WireSlot.g1] ++ (List.replicate c Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1]))) (List.replicate a Midfall.Lowering.WireSlot.g1) ms h
  obtain ⟨P, rfl, hPlen⟩ := map_slot_eq_replicate_g1 A hA
  obtain ⟨B, r2, rfl, hB, h2⟩ := map_slot_split ([Midfall.Lowering.WireSlot.g1] ++
    (List.replicate c Midfall.Lowering.WireSlot.fr ++ [Midfall.Lowering.WireSlot.g1]))
    (List.replicate b Midfall.Lowering.WireSlot.fr) r1 h1
  obtain ⟨R, rfl, hRlen⟩ := map_slot_eq_replicate_fr B hB
  obtain ⟨F, r3, rfl, hF, h3⟩ := map_slot_split (List.replicate c Midfall.Lowering.WireSlot.fr ++ [Midfall.Lowering.WireSlot.g1]) [Midfall.Lowering.WireSlot.g1] r2 h2
  obtain ⟨fCom, rfl⟩ := map_slot_eq_singleton_g1 F hF
  obtain ⟨C, r4, rfl, hC, h4⟩ := map_slot_split [Midfall.Lowering.WireSlot.g1] (List.replicate c Midfall.Lowering.WireSlot.fr) r3 h3
  obtain ⟨qs, rfl, hClen⟩ := map_slot_eq_replicate_fr C hC
  obtain ⟨G, r5, rfl, hG, h5⟩ := map_slot_split [] [Midfall.Lowering.WireSlot.g1] r4 h4
  obtain ⟨pi, rfl⟩ := map_slot_eq_singleton_g1 G hG
  have h5' : r5 = [] := by simpa using h5
  subst h5'
  refine ⟨P, R, fCom, qs, pi, ?_, hPlen, hRlen, hClen⟩
  simp

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem decoded_split_of_plan (L : Midfall.Generator.ProofCalldataLayout)
    (ms : List (Msg (Fr p) G₁))
    (h : ms.map Msg.slot =
      (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).slots) :
    ∃ (P : List G₁) (R : List (Fr p)) (fCom : G₁) (qs : List (Fr p)) (pi : G₁),
      ms = P.map Msg.g1 ++ R.map Msg.fr ++ [Msg.g1 fCom] ++ qs.map Msg.fr ++ [Msg.g1 pi] ∧
      P.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count ∧
      R.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).numEvals ∧
      qs.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).numPointSets := by
  unfold Midfall.Generator.RepackedProofLayoutPlan.slots at h
  simp only [List.append_assoc] at h
  exact decoded_coarse_split ms _ _ _ h

theorem parseTrace_run_of_ms_sizes_rest (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity) (hnc : 2 = vk.cs.numInstanceColumns)
    (hsp : vk.cs.numChallenges = 0) (hdeg : 3 ≤ vk.csDegree)
    (hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c)
    (QAdv QMult QPerm QLook QTrash : List G₁)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size)
    (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth)
    (ms rest : List (Msg (Fr p) G₁))
    (hms : ms = QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))) ++ rest) :
    ∃ trace t1,
      (parseTrace (p := p) E.g1 Features.solidity vk
        (committedShape (G₁ := G₁)) (instanceShape inst)).run (transcriptOf E H ms) =
        .ok (trace, t1) ∧
      t1.buffer = (transcriptOf E H ms).buffer ∧
      t1.pos = (wireMsgs E (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))))).size ∧
      (trace.permutations.toList.map (fun pc =>
        3 * pc.permutationProductCommitments.size - 1)).sum =
        3 * Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) - 1 ∧
      (trace.lookups.toList.map (fun row => (row.toList.map
        (fun c => c.helperPolys.size + 3)).sum)).sum =
        (vk.cs.lookups.toList.map (fun l => lookupChunkNum vk.csDegree l + 3)).sum ∧
      (trace.trashcans.toList.map (fun row => row.size)).sum = vk.cs.trashcans.size := by
  subst hms
  obtain ⟨trace, t1, hrun, hbuf, hpos, hP⟩ :=
    runsAllP_parseTrace_one_sizes E vk inst hf hnc hsp hdeg hs QAdv QMult QPerm QLook QTrash
      hlenAdv hlenMult hlenPerm hlenLook hlenTrash
      (transcriptOf E H (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))) ++ rest))
      ByteArray.empty (wireMsgs E rest) (by
        rw [(transcriptOf_buffer E H _).1, wireMsgs_append]
        simp) (by rw [(transcriptOf_buffer E H _).2]; rfl) hp henc hwidth
  refine ⟨trace, t1, hrun, hbuf, ?_, hP.1, hP.2.1, hP.2.2⟩
  rw [hpos, wireMsgs_size]
  simp

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem wireMsgs_tail (E : VerifierEnv p G₁ G₂ Gₜ) (fCom pi : G₁) (qs : List (Fr p)) :
    wireMsgs E ([Msg.g1 fCom] ++ qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 pi]) =
      E.g1.toCompressed fCom ++ wireOf qs ++ E.g1.toCompressed pi := by
  rw [wireMsgs_append, wireMsgs_append, wireMsgs_g1_singleton, wireMsgs_map_fr,
    wireMsgs_g1_singleton]

def xcriptPt (QAdv QMult QPerm QLook QTrash : List G₁) : List (Msg (Fr p) G₁) :=
  QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
  (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
  (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
  (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
  (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))

def xcriptRa (Qg : List G₁) (Qi Qa Qf Qc Qp Ql Qt : List (Fr p)) : List (Msg (Fr p) G₁) :=
  Qg.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
  (Qi.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
  (Qa.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
  (Qf.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
  (Qc.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
  (Qp.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
  (Ql.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
  (Qt.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [])))))))

def xcriptTail (fCom : G₁) (qs : List (Fr p)) (pi : G₁) : List (Msg (Fr p) G₁) :=
  [Msg.g1 fCom] ++ qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 pi]

set_option maxHeartbeats 2000000 in
theorem snapshotAlgebraRun_ok_of_schedule (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (hf : vk.WellFormed Features.solidity)
    (hnc : 2 = vk.cs.numInstanceColumns)
    (hinstQ : ∀ q ∈ vk.cs.instanceQueries.toList, ¬ q.1.index < 1 → q.1.index = 1)
    (hinstSize : inst.size < 2 ^ 31)
    (hp : p ≤ 2 ^ 256)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth)
    (QAdv QMult QPerm QLook QTrash Qg : List G₁)
    (Qi Qa Qf Qc Qp Ql Qt qs : List (Fr p)) (fCom pi : G₁) (nSets : Nat)
    (ms : List (Msg (Fr p) G₁))
    (hms : ms = xcriptPt QAdv QMult QPerm QLook QTrash ++
      xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt ++ xcriptTail fCom qs pi)
    (hlenAdv : QAdv.length = (vk.cs.phases.map (fun ph => (phaseCols vk.cs ph).length)).sum)
    (hlenMult : QMult.length = vk.cs.lookups.size)
    (hlenPerm : QPerm.length = Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2))
    (hlenLook : QLook.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 1)).sum)
    (hlenTrash : QTrash.length = vk.cs.trashcans.size)
    (hlenQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else vk.domain.getQuotientPolyDegree))
    (hlenI : Qi.length = (instanceShape inst).size *
      (vk.cs.instanceQueries.toList.filter
        (fun q => decide (q.1.index < 1))).length)
    (hlenA : Qa.length = (instanceShape inst).size * vk.cs.adviceQueries.size)
    (hlenF : Qf.length = vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
    (hlenC : Qc.length = vk.permutation.commitments.size)
    (hlenP : Qp.length = 3 * Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2) - 1)
    (hlenL : Ql.length = (vk.cs.lookups.toList.map
      (fun l => lookupChunkNum vk.csDegree l + 3)).sum)
    (hlenT : Qt.length = vk.cs.trashcans.size)
    (hlenQs : qs.length = nSets) :
    ∃ s2 t2, snapshotAlgebraRun E H vk inst ms = .ok (s2, t2) ∧
      t2.buffer = wireMsgs E (xcriptPt QAdv QMult QPerm QLook QTrash ++
        xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt) ++
        E.g1.toCompressed fCom ++ wireOf qs ++ E.g1.toCompressed pi ∧
      t2.pos = (wireMsgs E (xcriptPt QAdv QMult QPerm QLook QTrash ++
        xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt)).size := by
  let Pt : List (Msg (Fr p) G₁) := xcriptPt QAdv QMult QPerm QLook QTrash
  let Ra : List (Msg (Fr p) G₁) := xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt
  let Tail : List (Msg (Fr p) G₁) := xcriptTail fCom qs pi
  have hms' : ms = Pt ++ (Ra ++ Tail) := by
    simpa only [Pt, Ra, Tail, List.append_assoc] using hms
  have hsp : vk.cs.numChallenges = 0 := hf.singlePhase
  have hdeg : 3 ≤ vk.csDegree := hf.chunkLenPositive
  have hs : ∀ l ∈ vk.cs.lookups.toList, ∃ c, l.chunkByDegree vk.csDegree = .ok c :=
    fun l hl => chunkByDegree_ok_of_wf hf hl
  obtain ⟨trace, t1, hrun, hbuf1, hpos1, hperm, hlook, htrash⟩ :=
    parseTrace_run_of_ms_sizes_rest E H vk inst hf hnc hsp hdeg hs
      QAdv QMult QPerm QLook QTrash hlenAdv hlenMult hlenPerm hlenLook hlenTrash hp henc
      hwidth ms (Ra ++ Tail) hms'
  have htrace : snapshotTraceRun E H vk inst ms = .ok (SnapTrace.mk trace, t1) := by
    unfold snapshotTraceRun snapshotTraceStep
    simp only [StateT.run_bind, StateT.run_pure, hrun]
    rfl
  have hmax : maxInstanceLen (instanceShape inst) < 2 ^ 31 := by
    simpa [maxInstanceLen, instanceShape] using hinstSize
  have hrows : ∀ row ∈ (instanceShape inst).toList,
      ∀ q ∈ vk.cs.instanceQueries.toList, ¬ q.1.index < 1 →
        ∃ col, row[q.1.index - 1]? = some col := by
    intro row hrow q hq hnc'
    have hrow' : row = #[inst] := by simpa [instanceShape] using hrow
    subst hrow'
    have hq1 := hinstQ q hq hnc'
    exact ⟨inst, by rw [hq1]; rfl⟩
  have hlenA' : Qa.length = 1 * vk.cs.adviceQueries.size := by
    simpa [instanceShape] using hlenA
  have hlenP' : Qp.length = (trace.permutations.toList.map (fun pc =>
      3 * pc.permutationProductCommitments.size - 1)).sum := by
    rw [hperm]; exact hlenP
  have hlenL' : Ql.length = (trace.lookups.toList.map (fun row =>
      (row.toList.map (fun c => c.helperPolys.size + 3)).sum)).sum := by
    rw [hlook]; exact hlenL
  have hlenT' : Qt.length = (trace.trashcans.toList.map (fun row => row.size)).sum := by
    rw [htrash]; exact hlenT
  have hbufW : (transcriptOf E H ms).buffer = wireMsgs E Pt ++
      (wireMsgs E Ra ++ wireMsgs E Tail) := by
    rw [(transcriptOf_buffer E H ms).1, hms']
    simp only [Pt, Ra, Tail, wireMsgs_append]
  obtain ⟨alg, t2, hread, hbuf2, hpos2⟩ :=
    runsAll_readAlgebra E vk hf trace.permutations trace.lookups trace.trashcans 1 1
      (instanceShape inst) hmax hrows Qg Qi Qa Qf Qc Qp Ql Qt hlenQ hlenI hlenA' hlenF
      hlenC hlenP' hlenL' hlenT' t1 (wireMsgs E Pt) (wireMsgs E Tail)
      (by rw [hbuf1, hbufW]; dsimp only [Pt, Ra, Tail, xcriptPt, xcriptRa, xcriptTail])
      (by rw [hpos1]; dsimp only [Pt, xcriptPt]) hp henc hwidth
  have hstep : snapshotAlgebraStep (G₁ := G₁) E.g1 Features.solidity vk trace 1 1
      (instanceShape inst) t1 =
      .ok (({ toSnapTrace := SnapTrace.mk trace, alg := alg } : SnapAlgebra p G₁), t2) := by
    unfold snapshotAlgebraStep
    simp only [StateT.run_bind, StateT.run_pure, hread]
    rfl
  refine ⟨({ toSnapTrace := SnapTrace.mk trace, alg := alg } : SnapAlgebra p G₁), t2, ?_, ?_, ?_⟩
  · unfold snapshotAlgebraRun
    simp only [StateT.run_bind, StateT.run_pure, htrace]
    rw [show (if Features.solidity.committedInstances then committedShape (G₁ := G₁)
      else arrayReplicate (instanceShape inst).size (#[] : Array G₁)) =
      committedShape (G₁ := G₁) from rfl]
    rw [show (committedShape (G₁ := G₁)).isEmpty = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    simpa [committedShape, hstep]
  · -- buffer
    have hbuf2' : t2.buffer = wireMsgs E Pt ++ (wireMsgs E Ra ++ wireMsgs E Tail) := by
      rw [hbuf2, hbuf1, hbufW]
    rw [hbuf2']
    dsimp only [Tail]
    rw [show xcriptTail fCom qs pi = [Msg.g1 fCom] ++
      qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 pi] from rfl]
    rw [wireMsgs_tail]
    dsimp only [Pt, Ra]
    simp only [wireMsgs_append, List.append_assoc]
    simp only [ByteArray.append_assoc]
  · -- pos
    rw [hpos2]
    dsimp only [Pt, Ra, xcriptPt, xcriptRa]
    rw [← wireMsgs_size]
    simp only [wireMsgs_append, ByteArray.size_append, List.append_assoc]
    omega


theorem mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → l'.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases h
      rfl
  | cons a as ih =>
      intro l' h
      simp only [List.mapM_cons] at h
      cases ha : f a with
      | none => rw [ha] at h; cases h
      | some b =>
          rw [ha] at h
          cases hrest : as.mapM f with
          | none => rw [hrest] at h; cases h
          | some l0 =>
              rw [hrest] at h
              injection h with h
              subst h
              simp only [List.length_cons]
              rw [ih l0 hrest]

theorem instOfWords?_size {p : ℕ} [Fact (Nat.Prime p)]
    {instW : Array Word256} {inst : Array (Fr p)}
    (h : Midfall.LoweringV2.instOfWords? (p := p) instW = some inst) : inst.size = instW.size := by
  unfold Midfall.LoweringV2.instOfWords? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, rfl⟩ := h
  rw [List.size_toArray, mapM_option_length (Midfall.LoweringV2.frOfWord? (p := p)) instW.toList l hl, Array.length_toList]

/-- **THE EXACT CALADATA BOUND THAT WOULD SUPPLY `hnum`.** `Decoded` fixes
    `cd.size = proofEnd + 32 + 32 * numInstances`; a calldata-size bound
    `cd.size < 2^36` therefore gives `numInstances < 2^31`. No such bound is in
    the tree: `EntryFrameV3.cdSize` is `< 2^256`, and
    `SupportedInput.sizeBound` is `< 2^64` on the generator input, not on `cd`. -/
theorem numInstances_lt_of_cd_size {R : Render p G₁ G₂ Gₜ} {cd : Bytes}
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    (h : Decoded R cd ms instW inst) (hcd : cd.size < 2 ^ 36) :
    R.cfg.numInstances < 2 ^ 31 := by
  obtain ⟨hdec, -⟩ := h
  obtain ⟨_, _, _, _, _, _, _, hsz, _, _⟩ :=
    decodeCalldata_facts R.plan.proofLayout R.cfg.numInstances R.E.g1 cd ms instW hdec
  omega

set_option maxHeartbeats 1000000 in
theorem decoded_inst_size {R : Render p G₁ G₂ Gₜ} {cd : Bytes} {ms : List (Msg (Fr p) G₁)}
    {instW : Array Word256} {inst : Array (Fr p)}
    (h : Decoded R cd ms instW inst) : inst.size = R.cfg.numInstances := by
  obtain ⟨hdec, hinst⟩ := h
  unfold decodeCalldata at hdec
  simp at hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec
  obtain ⟨⟨ms0, cur0⟩, hslots, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec
  obtain ⟨-, hinstWeq⟩ := hdec
  have hsize : inst.size = instW.size := instOfWords?_size hinst
  rw [hsize, ← hinstWeq]
  simp

/-- **THE DECODED-SLOT LINKAGE.** `decodeCalldata`'s messages have exactly the layout's
    slots: the calldata side of the read-schedule shape, independent of D1's
    `prepare_logSlots`. -/

theorem decodeCalldata_slots {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    {R : Render p G₁ G₂ Gₜ} {cd : Bytes} {ms : List (Msg (Fr p) G₁)}
    {instW : Array Word256} {inst : Array (Fr p)}
    (h : Decoded R cd ms instW inst) :
    ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots := by
  obtain ⟨hdec, -⟩ := h
  unfold decodeCalldata at hdec
  simp at hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec
  obtain ⟨⟨ms0, cur0⟩, hslots, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  rw [Option.bind_eq_some_iff] at hdec; obtain ⟨_, _, hdec⟩ := hdec
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec
  obtain ⟨hmseq, -⟩ := hdec
  subst hmseq
  exact decodeSlots_map_slot R.E.g1 cd _ _ ms0 cur0 hslots



theorem exists_split_fr_prefix (ms : List (Msg (Fr p) G₁)) (n : Nat)
    (rest : List Midfall.Lowering.WireSlot)
    (h : ms.map Msg.slot = List.replicate n Midfall.Lowering.WireSlot.fr ++ rest) :
    ∃ (xs : List (Fr p)) (ms' : List (Msg (Fr p) G₁)),
      xs.length = n ∧ ms = xs.map Msg.fr ++ ms' ∧ ms'.map Msg.slot = rest := by
  obtain ⟨ms₁, ms₂, hsplit, hpre, hpost⟩ := exists_split_of_slot_prefix ms _ rest h
  obtain ⟨xs, hms₁, hlen⟩ := eq_map_fr_of_slots ms₁ n hpre
  exact ⟨xs, ms₂, hlen, by rw [hsplit, hms₁], hpost⟩

theorem ms_split_plan (plan : Midfall.Generator.RepackedProofLayoutPlan)
    (ms : List (Msg (Fr p) G₁))
    (h : ms.map Msg.slot = plan.slots) :
    ∃ (QPre : List G₁) (QEv : List (Fr p)) (fCom : G₁) (qs : List (Fr p)) (pi : G₁),
      ms = QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          ([Msg.g1 fCom] ++
            (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 pi]))) ∧
      QPre.length = plan.prefixG1Count ∧
      QEv.length = plan.numEvals ∧ qs.length = plan.numPointSets := by
  rw [Midfall.Generator.RepackedProofLayoutPlan.slots] at h
  simp only [List.append_assoc] at h
  obtain ⟨QPre, ms1, hlenPre, hms1, h1⟩ :=
    exists_split_g1_prefix ms plan.prefixG1Count
      (List.replicate plan.numEvals Midfall.Lowering.WireSlot.fr ++
        ([Midfall.Lowering.WireSlot.g1] ++
          (List.replicate plan.numPointSets Midfall.Lowering.WireSlot.fr ++
            [Midfall.Lowering.WireSlot.g1]))) h
  obtain ⟨QEv, ms2, hlenEv, hms2, h2⟩ :=
    exists_split_fr_prefix ms1 plan.numEvals
      ([Midfall.Lowering.WireSlot.g1] ++
        (List.replicate plan.numPointSets Midfall.Lowering.WireSlot.fr ++
          [Midfall.Lowering.WireSlot.g1])) h1
  have h3 : ms2.map Msg.slot =
      List.replicate 1 Midfall.Lowering.WireSlot.g1 ++
        (List.replicate plan.numPointSets Midfall.Lowering.WireSlot.fr ++
          [Midfall.Lowering.WireSlot.g1]) := by
    simpa using h2
  obtain ⟨Qf, ms3, hlenF, hms3, h3'⟩ :=
    exists_split_g1_prefix ms2 1
      (List.replicate plan.numPointSets Midfall.Lowering.WireSlot.fr ++
        [Midfall.Lowering.WireSlot.g1]) h3
  obtain ⟨fCom, hfCom⟩ := List.length_eq_one_iff.mp hlenF
  subst hfCom
  simp only [List.map_cons, List.map_nil] at hms3
  obtain ⟨qs, ms4, hlenQs, hms4, h4⟩ :=
    exists_split_fr_prefix ms3 plan.numPointSets [Midfall.Lowering.WireSlot.g1] h3'
  have h5 : ms4.map Msg.slot = [Midfall.Lowering.WireSlot.g1] := by simpa using h4
  obtain ⟨Qpi, ms5, hlenPi, hms5, h5'⟩ :=
    exists_split_g1_prefix ms4 1 [] h5
  obtain ⟨pi, hpi⟩ := List.length_eq_one_iff.mp hlenPi
  subst hpi
  simp only [List.map_cons, List.map_nil] at hms5
  have hms5' : ms5 = [] := by
    have := h5'
    simpa using this
  subst hms5'
  refine ⟨QPre, QEv, fCom, qs, pi, ?_, hlenPre, hlenEv, hlenQs⟩
  rw [hms1, hms2, hms3, hms4, hms5]
  rfl

theorem decoded_ms_split (R : Render p G₁ G₂ Gₜ) {cd : Bytes}
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    (h : Decoded R cd ms instW inst) :
    ∃ (QPre : List G₁) (QEv : List (Fr p)) (fCom : G₁) (qs : List (Fr p)) (pi : G₁),
      ms = QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          ([Msg.g1 fCom] ++
            (qs.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 pi]))) ∧
      QPre.length = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count ∧
      QEv.length = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals ∧
      qs.length = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets :=
  ms_split_plan _ ms (decodeCalldata_slots h)

/-- **SIM.10 OBLIGATION 3, COMPOSED.** Once the algebra prefix succeeds on the exact wire
    tail, `pcsReads` and `assertEmpty` finish: the whole transcript-only run exists. The
    remaining input is obligation 1 (`snapshotAlgebraRun` on `transcriptOf E H ms`). -/
theorem snapshotXcriptRun_of_algebra {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (nSets : Nat)
    (s2 : SnapAlgebra p G₁) (t2 : Midfall.Halo2.Transcript)
    (hAlg : snapshotAlgebraRun E H vk inst ms = .ok (s2, t2))
    (pref : Bytes) (fCom pi : G₁) (qs : List (Fr p))
    (hlen : qs.length = nSets)
    (hbuf : t2.buffer = pref ++ E.g1.toCompressed fCom ++
      wireOf (p := p) qs ++ E.g1.toCompressed pi)
    (hpos : t2.pos = pref.size)
    (henc : ∀ Q, E.g1.ofCompressed? (E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (E.g1.toCompressed Q).size = g1CompressedWidth)
    (hp : p ≤ 2 ^ 256) :
    ∃ x, snapshotXcriptRun E H vk inst ms nSets = .ok x := by
  unfold snapshotXcriptRun
  simp only [StateT.run_bind, StateT.run_pure]
  rw [hAlg]
  simp only [Except.bind, Except.pure, bind, pure]
  obtain ⟨r, t5, hrun, _hf, _hpi, _hq, hpos5, hbuf5⟩ :=
    pcsReads_run_ok E.g1 E.field Features.solidity nSets t2 pref fCom pi qs hlen hbuf hpos
      henc hwidth hp
  rw [hrun]
  simp only [Except.bind, Except.pure, bind, pure]
  rw [assertEmpty_run_ok t5 (by rw [hbuf5, hpos5])]
  exact ⟨_, rfl⟩

/-! ### SIM.10 — `xcript_total`'s MISSING DATA CLAUSE, NAMED

`snapshotXcriptRun_of_algebra` reduces the transcript-only Lean prefix to ONE input: an
`snapshotAlgebraRun` success on the decoded wire, with the eval tail (`pref ++ fCom ++ qs ++ pi`)
exposed. That input is the parser-side analogue of D1's `prepare_logSlots`, and it is NOT a theorem
of `ValidV3` + `Decoded` today:

* the WIDTH SCHEDULE is pinned (`parseTraceSchedule` in `EndToEndAlgebra.lean`, the
  `readAlgebraEvalCount_parseTrace*` counts, and `prepareSlots_of_counts`), but all of those are
  CONDITIONAL on a successful run (`PresWidthSeq`/`ParseTraceWidths` say "if it runs, it reads
  these widths");
* the monadic READ WALK itself — `parseTrace`'s twenty steps (advice phases, lookup multiplicities
  and commitments, permutation products, trashcans, the scatters) and `readAlgebra`'s commitment /
  eval / q-eval reads — has no existence theorem in the tree (`grep` finds none: no
  `parseTrace_run`, no `readAlgebra_run`, no `snapshotAlgebraRun` totality);
* that is the same refinement `gap_readScheduleAgrees` (`EndToEnd.lean:967`) names for
  `decodeRust`: `ValidV3` pins the plan and the key's well-formedness, but nothing relates the
  verifier's read sequence to the generated slot list. `decodeSlots_map_slot` here gives the
  calldata side (`ms.map Msg.slot = plan.slots`); the Lean side is owed.

The two `def`s below are that clause, named rather than sorried (the `PrepareLogSlots` /
`KzgPartitionBridge` pattern): `XcriptAlgebraTail` is the run-and-tail statement at a FIXED decoded
message list, and `XcriptAlgebraRun` wraps it in the `∀ decoding` shape the boundary needs. The
theorems after them spend the clause exactly: `xcript_total_of_algebraRun` is `xcript_total`'s
existence conclusion, and `leanStage_transcript_exists_*` is the existence half of
`Agree .transcript` (`tp_agrees`'s only decode-relative obligation). -/

/-- **SIM.10's MISSING DATA CLAUSE, AT A DECODED MESSAGE LIST.** The algebra prefix succeeds on the
    wire of `ms`, and the bytes it leaves are the eval tail: a consumed prefix, `fCom`, the `nSets`
    q-eval scalars, and `pi`. The `pos`/`buffer` fields are what `snapshotXcriptRun_of_algebra`
    consumes verbatim. -/
theorem decodeSlots_g1_inv {c : G1Codec G₁} {cd : Bytes} (rest : List Midfall.Lowering.WireSlot)
    (cur : Nat) (ms : List (Msg (Fr p) G₁)) (cur' : Nat)
    (h : decodeSlots (p := p) c cd
        (Midfall.Lowering.WireSlot.g1 :: rest) cur = some (ms, cur')) :
    ∃ (b : Bytes) (Q : G₁) (ms0 : List (Msg (Fr p) G₁)) (cur0 : Nat),
      g1WordsOk cd cur = true ∧ bytesTake cd cur g1EipWidth = some b ∧
        c.ofEip? b = some Q ∧
        decodeSlots (p := p) c cd rest (cur + g1EipWidth) = some (ms0, cur0) ∧
        ms = Msg.g1 Q :: ms0 ∧ cur' = cur0 := by
  unfold decodeSlots at h
  simp only [guard] at h
  by_cases hg : g1WordsOk cd cur = true
  · rw [if_pos hg] at h
    cases hb : bytesTake cd cur g1EipWidth with
    | none =>
        simp [hb] at h
    | some b =>
        simp [hb] at h
        cases hq : c.ofEip? b with
        | none =>
            simp [hq] at h
        | some Q =>
            simp [hq] at h
            cases hrec : decodeSlots (p := p) c cd rest (cur + g1EipWidth) with
            | none =>
                simp [hrec] at h
            | some p =>
                obtain ⟨ms0, cur0⟩ := p
                simp [hrec] at h
                obtain ⟨hms, hcur⟩ := h
                exact ⟨b, Q, ms0, cur0, hg, rfl, hq, rfl, hms.symm, hcur.symm⟩
  · rw [if_neg hg] at h
    simp at h

theorem decodeSlots_append {c : G1Codec G₁} {cd : Bytes} :
    ∀ (s1 s2 : List Midfall.Lowering.WireSlot) (cur : Nat)
      (ms1 ms2 : List (Msg (Fr p) G₁)) (cur1 cur2 : Nat),
      decodeSlots (p := p) c cd s1 cur = some (ms1, cur1) →
      decodeSlots (p := p) c cd s2 cur1 = some (ms2, cur2) →
      decodeSlots (p := p) c cd (s1 ++ s2) cur = some (ms1 ++ ms2, cur2) := by
  intro s1
  induction s1 with
  | nil =>
      intro s2 cur ms1 ms2 cur1 cur2 h1 h2
      simp only [decodeSlots, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simpa using h2
  | cons sl rest ih =>
      intro s2 cur ms1 ms2 cur1 cur2 h1 h2
      cases sl with
      | g1 =>
          obtain ⟨b, Q, ms0, cur0, hg, hb, hq, hrec, hms, hcur⟩ :=
            decodeSlots_g1_inv rest cur ms1 cur1 h1
          rw [hcur] at h2
          have hrec2 := ih s2 (cur + g1EipWidth) ms0 ms2 cur0 cur2 hrec h2
          rw [List.cons_append]
          rw [decodeSlots_g1_step (p := p) c cd (rest ++ s2) cur b Q
            (ms0 ++ ms2) cur2 hg hb hq hrec2]
          rw [hms]
          rfl
      | fr =>
          -- invert the fr step
          unfold decodeSlots at h1
          simp only [guard] at h1
          by_cases hlt : (cdWord cd cur).toNat < p
          · rw [if_pos hlt] at h1
            cases hrec : decodeSlots (p := p) c cd rest (cur + 32) with
            | none => rw [hrec] at h1; simp at h1
            | some pair =>
                obtain ⟨ms0, cur0⟩ := pair
                rw [hrec] at h1
                simp at h1
                obtain ⟨hms, hcur⟩ := h1
                subst hms
                subst hcur
                have hrec2 := ih s2 (cur + 32) ms0 ms2 cur0 cur2 hrec h2
                rw [List.cons_append]
                rw [decodeSlots_fr_step (p := p) c cd (rest ++ s2) cur (ms0 ++ ms2) cur2
                  hlt hrec2]
                rfl
          · rw [if_neg hlt] at h1
            simp at h1

theorem decodeSlots_split {c : G1Codec G₁} {cd : Bytes} :
    ∀ (s1 s2 : List Midfall.Lowering.WireSlot) (cur : Nat)
      (ms : List (Msg (Fr p) G₁)) (cur' : Nat),
      decodeSlots (p := p) c cd (s1 ++ s2) cur = some (ms, cur') →
      ∃ (ms1 : List (Msg (Fr p) G₁)) (cur1 : Nat) (ms2 : List (Msg (Fr p) G₁)),
        decodeSlots (p := p) c cd s1 cur = some (ms1, cur1) ∧
          decodeSlots (p := p) c cd s2 cur1 = some (ms2, cur') ∧ ms = ms1 ++ ms2 := by
  intro s1
  induction s1 with
  | nil =>
      intro s2 cur ms cur' h
      exact ⟨[], cur, ms, rfl, h, rfl⟩
  | cons sl rest ih =>
      intro s2 cur ms cur' h
      rw [List.cons_append] at h
      cases sl with
      | g1 =>
          obtain ⟨b, Q, ms0, cur0, hg, hb, hq, hrec, hms, hcur⟩ :=
            decodeSlots_g1_inv (rest ++ s2) cur ms cur' h
          obtain ⟨ms1, cur1, ms2, h1, h2, rfl⟩ := ih s2 (cur + g1EipWidth) ms0 cur0 hrec
          rw [← hcur] at h2
          refine ⟨Msg.g1 Q :: ms1, cur1, ms2, ?_, h2, ?_⟩
          · rw [decodeSlots_g1_step (p := p) c cd rest cur b Q ms1 cur1 hg hb hq h1]
          · rw [hms]; rfl
      | fr =>
          unfold decodeSlots at h
          simp only [guard] at h
          by_cases hlt : (cdWord cd cur).toNat < p
          · rw [if_pos hlt] at h
            cases hrec : decodeSlots (p := p) c cd (rest ++ s2) (cur + 32) with
            | none => rw [hrec] at h; simp at h
            | some pair =>
                obtain ⟨ms0, cur0⟩ := pair
                rw [hrec] at h
                simp at h
                obtain ⟨hms, hcur⟩ := h
                subst hms
                subst hcur
                obtain ⟨ms1, cur1, ms2, h1, h2, rfl⟩ := ih s2 (cur + 32) ms0 cur0 hrec
                refine ⟨Msg.fr (Nat.cast (cdWord cd cur).toNat) :: ms1, cur1, ms2, ?_, h2, rfl⟩
                rw [decodeSlots_fr_step (p := p) c cd rest cur ms1 cur1 hlt h1]
          · rw [if_neg hlt] at h
            simp at h

theorem decodeSlots_g1_provenance {c : G1Codec G₁} {cd : Bytes} (n : Nat)
    (rest : List Midfall.Lowering.WireSlot) (cur : Nat)
    (Qs : List G₁) (ms' : List (Msg (Fr p) G₁)) (cur' : Nat)
    (hlen : Qs.length = n)
    (h : decodeSlots (p := p) c cd
        (List.replicate n Midfall.Lowering.WireSlot.g1 ++ rest) cur =
      some (Qs.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ ms', cur')) :
    ∀ i < n, ∃ (b : Bytes) (Q : G₁),
      bytesTake cd (cur + g1EipWidth * i) g1EipWidth = some b ∧
        c.ofEip? b = some Q ∧ Qs[i]? = some Q := by
  induction n generalizing cur Qs ms' cur' with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      cases Qs with
      | nil => simp at hlen
      | cons Q Qs' =>
          have hlen' : Qs'.length = n := by simpa using hlen
          have hslot : List.replicate (n + 1) Midfall.Lowering.WireSlot.g1 ++ rest =
              Midfall.Lowering.WireSlot.g1 ::
                (List.replicate n Midfall.Lowering.WireSlot.g1 ++ rest) := by
            rw [List.replicate_succ, List.cons_append]
          rw [hslot] at h
          obtain ⟨b, Q0, ms0, cur0, hg, hb, hq, hrec, hms, hcur⟩ :=
            decodeSlots_g1_inv (List.replicate n Midfall.Lowering.WireSlot.g1 ++ rest) cur ((Q :: Qs').map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ ms') cur' h
          have hms' : Msg.g1 Q0 :: ms0 =
              (Msg.g1 Q :: Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁))) ++ ms' := by
            simpa using hms.symm
          have hhead : Q0 = Q := by
            have h1 := congrArg (fun l => l.head?) hms'
            simp at h1
            exact h1
          have htail : ms0 = Qs'.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ ms' := by
            have h2 := congrArg List.tail hms'
            simpa using h2
          rw [htail] at hrec
          intro i hi
          cases i with
          | zero =>
              exact ⟨b, Q0, hb, hq, by rw [hhead]; rfl⟩
          | succ k =>
              have hk : k < n := by omega
              obtain ⟨b', Q', hb', hq', hidx⟩ :=
                ih (cur + g1EipWidth) Qs' ms' cur0 hlen' hrec k hk
              refine ⟨b', Q', ?_, hq', ?_⟩
              · rw [show cur + g1EipWidth * (k + 1) =
                    cur + g1EipWidth + g1EipWidth * k by ring]
                exact hb'
              · simpa using hidx

def XcriptAlgebraTail (R : Render p G₁ G₂ Gₜ) (H : Hash)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Prop :=
  ∃ (s2 : SnapAlgebra p G₁) (t2 : Transcript) (pref : Bytes) (fCom pi : G₁)
    (qs : List (Fr p)),
    snapshotAlgebraRun R.E H R.vk inst ms = .ok (s2, t2) ∧
      t2.buffer = pref ++ R.E.g1.toCompressed fCom ++ wireOf qs ++
        R.E.g1.toCompressed pi ∧
      t2.pos = pref.size ∧ qs.length = R.nSets

/-- **SIM.10's MISSING DATA CLAUSE, AT THE BOUNDARY.** For EVERY decoding of the calldata, the
    algebra prefix exists with the eval tail exposed. This is the parser-side `prepare_logSlots`
    analogue described in the section comment; it is a DATA clause, not a `ValidV3` theorem. -/
def XcriptAlgebraRun (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
    Decoded R cd ms instW inst → XcriptAlgebraTail R H inst ms

/-- **THE NAMED READ SCHEDULE.** For every decoding of `cd`, the decoded messages split
    into the parseTrace commitments, the readAlgebra evals, and the fCom/qs/pi tail,
    with the block lengths the VK's own read walk consumes. This is the named
    plan-count <-> VK-schedule link at payload granularity: the coarse split
    (`decoded_split_of_plan`) supplies the two coarse lengths, and these fields are
    the fine counts the walk needs. `H` is carried to match the consumer
    (`XcriptAlgebraRun`); the schedule itself is hash-free. -/
def XcriptSchedule (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
    Decoded R cd ms instW inst →
      ∃ (QAdv QMult QPerm QLook QTrash Qg : List G₁)
        (Qi Qa Qf Qc Qp Ql Qt qs : List (Fr p)) (fCom pi : G₁),
        ms = xcriptPt QAdv QMult QPerm QLook QTrash ++
          xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt ++ xcriptTail fCom qs pi ∧
        QAdv.length = (R.vk.cs.phases.map (fun ph => (phaseCols R.vk.cs ph).length)).sum ∧
        QMult.length = R.vk.cs.lookups.size ∧
        QPerm.length = Permutation.numChunksOf R.vk.cs.permutation.columns.size
          (R.vk.csDegree - 2) ∧
        QLook.length = (R.vk.cs.lookups.toList.map
          (fun l => lookupChunkNum R.vk.csDegree l + 1)).sum ∧
        QTrash.length = R.vk.cs.trashcans.size ∧
        Qg.length = (if Features.solidity.outerSingleHCommitment then 1
          else R.vk.domain.getQuotientPolyDegree) ∧
        Qi.length = (instanceShape inst).size *
          (R.vk.cs.instanceQueries.toList.filter
            (fun q => decide (q.1.index < 1))).length ∧
        Qa.length = (instanceShape inst).size * R.vk.cs.adviceQueries.size ∧
        Qf.length = R.vk.cs.numFixedColumns - R.vk.cs.numSimpleSelectors ∧
        Qc.length = R.vk.permutation.commitments.size ∧
        Qp.length = 3 * Permutation.numChunksOf R.vk.cs.permutation.columns.size
          (R.vk.csDegree - 2) - 1 ∧
        Ql.length = (R.vk.cs.lookups.toList.map
          (fun l => lookupChunkNum R.vk.csDegree l + 3)).sum ∧
        Qt.length = R.vk.cs.trashcans.size ∧
        qs.length = R.nSets

/-- The plan's G1 read count as the six blocks `parseTrace` and the quotient
    limb read consume. -/
def planPrefixG1Count (R : Render p G₁ G₂ Gₜ) : Nat :=
  (R.vk.cs.phases.map (fun ph => (phaseCols R.vk.cs ph).length)).sum
  + R.vk.cs.lookups.size
  + Permutation.numChunksOf R.vk.cs.permutation.columns.size (R.vk.csDegree - 2)
  + (R.vk.cs.lookups.toList.map (fun l => lookupChunkNum R.vk.csDegree l + 1)).sum
  + R.vk.cs.trashcans.size
  + (if Features.solidity.outerSingleHCommitment then 1
      else R.vk.domain.getQuotientPolyDegree)

/-- The plan's scalar read count as the seven blocks `readAlgebra` consumes. -/
def planNumEvals (R : Render p G₁ G₂ Gₜ) (inst : Array (Fr p)) : Nat :=
  (instanceShape inst).size *
    (R.vk.cs.instanceQueries.toList.filter (fun q => decide (q.1.index < 1))).length
  + (instanceShape inst).size * R.vk.cs.adviceQueries.size
  + (R.vk.cs.numFixedColumns - R.vk.cs.numSimpleSelectors)
  + R.vk.permutation.commitments.size
  + (3 * Permutation.numChunksOf R.vk.cs.permutation.columns.size (R.vk.csDegree - 2) - 1)
  + (R.vk.cs.lookups.toList.map (fun l => lookupChunkNum R.vk.csDegree l + 3)).sum
  + R.vk.cs.trashcans.size

/-- **THE PLAN-COUNT / VK-SCHEDULE LINK.** The two counts the generated plan's
    proof layout exposes, identified with the read walk's block lengths. The
    coarse split itself is proved from `Decoded` (`decodeCalldata_slots` +
    `decoded_split_of_plan`), and the point-set count is definitional
    (`plan_numPointSets_eq_nSets`); these two equations are the whole plan-side
    input, so naming them here names `hsched` at its smallest. -/
structure PlanReadCounts (R : Render p G₁ G₂ Gₜ) : Prop where
  prefixG1 : (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count =
    planPrefixG1Count R
  numEvals : ∀ (inst : Array (Fr p)),
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals =
      planNumEvals R inst

/-- The point-set count is definitional: `fromProofLayout`'s `numPointSets` is the
    layout's `qEvals.itemCount`, which is `R.nSets`. -/
theorem plan_numPointSets_eq_nSets (R : Render p G₁ G₂ Gₜ) :
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets = R.nSets := rfl

/-- Split a list at a list of block lengths whose sum is its length. -/
theorem exists_blocks_of_sum_length {α : Type} :
    ∀ (l : List α) (ns : List Nat), l.length = ns.sum →
      ∃ ls : List (List α), ls.length = ns.length ∧ ls.map List.length = ns ∧
        l = ls.flatten := by
  intro l ns
  induction ns generalizing l with
  | nil =>
      intro h
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      exact ⟨[], rfl, rfl, by simp [hl]⟩
  | cons n ns ih =>
      intro h
      have hn : n ≤ l.length := by simp only [List.sum_cons] at h; omega
      have htn : (l.take n).length = n := by rw [List.length_take]; omega
      have hdn : (l.drop n).length = ns.sum := by
        simp only [List.sum_cons] at h
        rw [List.length_drop]; omega
      obtain ⟨ls, hlen, hmap, hflat⟩ := ih (l.drop n) hdn
      refine ⟨l.take n :: ls, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [List.map_cons, List.length_cons, htn, hmap]
      · rw [List.flatten_cons, ← hflat]
        exact (List.take_append_drop n l).symm

/-- Cut a list into the six blocks of the given lengths (the lengths sum to its
    length). The blocks' contents are irrelevant; the schedule only reads counts. -/
theorem list_split_six {α : Type} (l : List α) (a b c d e f : Nat)
    (h : l.length = a + b + c + d + e + f) :
    ∃ l1 l2 l3 l4 l5 l6, l = l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ∧
      l1.length = a ∧ l2.length = b ∧ l3.length = c ∧ l4.length = d ∧
      l5.length = e ∧ l6.length = f := by
  have h' : l.length = [a, b, c, d, e, f].sum := by
    simp only [List.sum_cons, List.sum_nil]; omega
  obtain ⟨ls, hlen, hmap, hflat⟩ := exists_blocks_of_sum_length l [a, b, c, d, e, f] h'
  rcases ls with _ | ⟨l1, _ | ⟨l2, _ | ⟨l3, _ | ⟨l4, _ | ⟨l5, _ | ⟨l6, rest⟩⟩⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · rcases rest with _ | ⟨head, tail⟩
    · simp only [List.map_cons, List.map_nil] at hmap
      simp only [List.cons.injEq, and_true] at hmap
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hmap
      refine ⟨l1, l2, l3, l4, l5, l6, ?_, h1, h2, h3, h4, h5, h6⟩
      simpa using hflat
    · simp at hlen

/-- Cut a list into the seven scalar blocks of the given lengths. -/
theorem list_split_seven {α : Type} (l : List α) (a b c d e f g : Nat)
    (h : l.length = a + b + c + d + e + f + g) :
    ∃ l1 l2 l3 l4 l5 l6 l7, l = l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ∧
      l1.length = a ∧ l2.length = b ∧ l3.length = c ∧ l4.length = d ∧
      l5.length = e ∧ l6.length = f ∧ l7.length = g := by
  have h' : l.length = [a, b, c, d, e, f, g].sum := by
    simp only [List.sum_cons, List.sum_nil]; omega
  obtain ⟨ls, hlen, hmap, hflat⟩ := exists_blocks_of_sum_length l [a, b, c, d, e, f, g] h'
  rcases ls with _ | ⟨l1, _ | ⟨l2, _ | ⟨l3, _ | ⟨l4, _ | ⟨l5, _ | ⟨l6, _ | ⟨l7, rest⟩⟩⟩⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · rcases rest with _ | ⟨head, tail⟩
    · simp only [List.map_cons, List.map_nil] at hmap
      simp only [List.cons.injEq, and_true] at hmap
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmap
      refine ⟨l1, l2, l3, l4, l5, l6, l7, ?_, h1, h2, h3, h4, h5, h6, h7⟩
      simpa using hflat
    · simp at hlen

/-- **`XcriptSchedule` FROM THE TWO PLAN COUNTS.** The coarse split is the
    decoded-slot linkage; the fine blocks are cuts of its `P` and `R` at the
    VK's own lengths, so only the sums have to be provided. -/
theorem xcriptSchedule_of_planReadCounts (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (hc : PlanReadCounts R) : XcriptSchedule R H cd := by
  intro ms instW inst hdec
  have hslots : ms.map Msg.slot =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots :=
    decodeCalldata_slots hdec
  obtain ⟨P, Rb, fCom, qs, pi, hms, hPlen, hRlen, hqslen⟩ :=
    decoded_split_of_plan R.plan.proofLayout ms hslots
  have hPs : P.length = planPrefixG1Count R := by rw [hPlen, hc.prefixG1]
  have hRs : Rb.length = planNumEvals R inst := by rw [hRlen, hc.numEvals inst]
  obtain ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, hPeq, hA, hB, hC, hD, hE, hF⟩ :=
    list_split_six P
      ((R.vk.cs.phases.map (fun ph => (phaseCols R.vk.cs ph).length)).sum)
      R.vk.cs.lookups.size
      (Permutation.numChunksOf R.vk.cs.permutation.columns.size (R.vk.csDegree - 2))
      ((R.vk.cs.lookups.toList.map (fun l => lookupChunkNum R.vk.csDegree l + 1)).sum)
      R.vk.cs.trashcans.size
      (if Features.solidity.outerSingleHCommitment then 1
        else R.vk.domain.getQuotientPolyDegree)
      (by rw [hPs]; rfl)
  obtain ⟨Qi, Qa, Qf, Qc, Qp, Ql, Qt, hReq, hI, hJ, hK, hL, hM, hN, hO⟩ :=
    list_split_seven Rb
      ((instanceShape inst).size *
        (R.vk.cs.instanceQueries.toList.filter (fun q => decide (q.1.index < 1))).length)
      ((instanceShape inst).size * R.vk.cs.adviceQueries.size)
      (R.vk.cs.numFixedColumns - R.vk.cs.numSimpleSelectors)
      R.vk.permutation.commitments.size
      (3 * Permutation.numChunksOf R.vk.cs.permutation.columns.size (R.vk.csDegree - 2) - 1)
      ((R.vk.cs.lookups.toList.map (fun l => lookupChunkNum R.vk.csDegree l + 3)).sum)
      R.vk.cs.trashcans.size
      (by rw [hRs]; rfl)
  refine ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qs, fCom, pi,
    ?_, hA, hB, hC, hD, hE, hF, hI, hJ, hK, hL, hM, hN, hO, ?_⟩
  · rw [hms, hPeq, hReq]
    simp only [List.map_append, xcriptPt, xcriptRa, xcriptTail, List.append_assoc,
      List.append_nil]
  · exact hqslen.trans (plan_numPointSets_eq_nSets R)

/-- **THE INSTANCE-QUERY INDEX BOUND.** The key's own instance queries all name
    columns below `numInstanceColumns` (D-GATE15(c)); with the supported shape
    (`numInstanceColumns = 2`) a query that is not a committed one has index
    exactly `1`, which is what the `readAlgebra` matrix index needs. -/
theorem instanceQueries_index_eq_one {G₁ : Type} [Group G₁]
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (hnc : vk.cs.numInstanceColumns = 2)
    {q : Column × Rotation} (hq : q ∈ vk.cs.instanceQueries.toList)
    (hge : ¬ q.1.index < 1) : q.1.index = 1 := by
  have hlt := hf.instanceQueriesBound q hq
  omega

/-- **`XcriptAlgebraRun` FROM THE NAMED SCHEDULE.** Every decoding is fed to
    `snapshotAlgebraRun_ok_of_schedule`; the instance-shape facts are the supported
    key's (`WellFormed`, `numInstanceColumns = 2`), the query-index bound is
    `instanceQueries_index_eq_one`, and the only remaining runtime input is
    `hnum`. -/
theorem xcriptAlgebraRun_of_schedule (R : Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (cd : Bytes)
    (hsched : XcriptSchedule R H cd)
    (hnum : R.cfg.numInstances < 2 ^ 31) :
    XcriptAlgebraRun R H cd := by
  intro ms instW inst hdec
  obtain ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qs,
    fCom, pi, hms, hAdv, hMult, hPerm, hLook, hTrash, hQ, hI, hA, hF, hC, hP, hL, hT,
    hQs⟩ := hsched ms instW inst hdec
  have hf : R.vk.WellFormed Features.solidity := hR.supported.wf
  have hnc0 : R.vk.cs.numInstanceColumns = 2 := hR.supported.instShape.1
  have hnc : 2 = R.vk.cs.numInstanceColumns := hnc0.symm
  have hinstQ : ∀ q ∈ R.vk.cs.instanceQueries.toList, ¬ q.1.index < 1 → q.1.index = 1 :=
    fun q hq hge => instanceQueries_index_eq_one R.vk hf hnc0 hq hge
  have hinstSize : inst.size < 2 ^ 31 := by
    rw [decoded_inst_size hdec]; exact hnum
  have hp : p ≤ 2 ^ 256 := by
    rw [hR.env.modulus]; norm_num [frModulusConstant]
  obtain ⟨s2, t2, hrun, hbuf, hpos⟩ :=
    snapshotAlgebraRun_ok_of_schedule R.E H R.vk inst hf hnc hinstQ hinstSize hp
      hcodec.compressedEncoderFirst hcodec.compressedWidth
      QAdv QMult QPerm QLook QTrash Qg Qi Qa Qf Qc Qp Ql Qt qs fCom pi R.nSets ms hms
      hAdv hMult hPerm hLook hTrash hQ hI hA hF hC hP hL hT hQs
  exact ⟨s2, t2, wireMsgs R.E (xcriptPt QAdv QMult QPerm QLook QTrash ++
    xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt), fCom, pi, qs, hrun, hbuf, hpos, hQs⟩


/-- **`XcriptAlgebraRun` FROM THE TWO PLAN COUNTS.** The schedule is built from
    `Decoded`, so nothing per-decoding is assumed; the only extra runtime input
    is `hnum`. -/
theorem xcriptAlgebraRun_of_planReadCounts (R : Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (cd : Bytes)
    (hc : PlanReadCounts R) (hnum : R.cfg.numInstances < 2 ^ 31) :
    XcriptAlgebraRun R H cd :=
  xcriptAlgebraRun_of_schedule R hR hcodec H cd
    (xcriptSchedule_of_planReadCounts R H cd hc) hnum

/-- `xcript_total` at one fixed decoded message list, directly from the tail clause. -/
theorem bytes_prefix_cancel {A B C D : Bytes} (h : A ++ C = B ++ D)
    (hsize : A.size = B.size) : A = B := by
  have hL : bytesTake (A ++ C) 0 A.size = some A := by
    rw [Midfall.bytesTake_append_left A C 0 A.size (by omega), bytesTake_whole]
  have hR : bytesTake (B ++ D) 0 A.size = some B := by
    rw [Midfall.bytesTake_append_left B D 0 A.size (by omega)]
    exact Midfall.Lowering.bytesTake_whole_of_size (by omega)
  have := congrArg (fun x => bytesTake x 0 A.size) h
  rw [hL, hR] at this
  exact Option.some.inj this

theorem bytes_append_cancel_left {A C D : Bytes} (h : A ++ C = A ++ D) : C = D := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have hh := congrArg (fun x => x.data.toList) h
  rw [ByteArray.data_append, ByteArray.data_append,
    Array.toList_append, Array.toList_append] at hh
  exact List.append_cancel_left hh

theorem bytes_suffix_cancel {A B C D : Bytes} (h : A ++ C = B ++ D)
    (hsize : C.size = D.size) : C = D := by
  have htot : A.size + C.size = B.size + D.size := by
    have := congrArg ByteArray.size h
    rw [ByteArray.size_append, ByteArray.size_append] at this
    exact this
  have hpref : A.size = B.size := by omega
  have htake := congrArg (fun x => bytesTake x A.size C.size) h
  have hL : bytesTake (A ++ C) A.size C.size = some C := by
    rw [show A.size = A.size + 0 by omega]
    rw [Midfall.bytesTake_append_right A C 0 C.size (by omega)]
    exact bytesTake_whole C
  have hR : bytesTake (B ++ D) A.size C.size = some D := by
    rw [show A.size = B.size + 0 by omega]
    rw [Midfall.bytesTake_append_right B D 0 C.size (by omega)]
    exact Midfall.Lowering.bytesTake_whole_of_size (by omega)
  rw [hL, hR] at htake
  exact Option.some.inj htake

theorem snapshotAlgebraRun_buffer (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) (s2 : SnapAlgebra p G₁) (t2 : Transcript)
    (h : snapshotAlgebraRun E H vk inst ms = .ok (s2, t2)) :
    t2.buffer = (transcriptOf E H ms).buffer := by
  obtain ⟨t1, htrace, hread⟩ :=
    Midfall.Lowering.snapshotAlgebraRun_readAlgebra E H vk inst ms s2 t2 h
  obtain hparse :=
    Midfall.Lowering.snapshotTraceRun_parseTrace E H vk inst ms s2.toSnapTrace t1 htrace
  have hread1 : StateT.run
      (Midfall.Halo2.Verifier.readAlgebra (p := p) E.g1 Features.solidity vk
        s2.trace.permutations s2.trace.lookups s2.trace.trashcans 1
        (instanceShape inst).size (instanceShape inst)) t1 = .ok (s2.alg, t2) := by
    simpa [committedShape] using hread
  have hpresPT : Midfall.Halo2.Pres (Midfall.Halo2.parseTrace (p := p) E.g1
      Features.solidity vk (committedShape (G₁ := G₁)) (instanceShape inst)) :=
    Midfall.Halo2.pres_parseTrace (p := p) E.g1 Features.solidity vk
      (committedShape (G₁ := G₁)) (instanceShape inst)
  have ht0 : (transcriptOf E H ms).Tiled :=
    Transcript.tiled_initWithHash H _
  have ht1 : t1.Tiled := Midfall.Halo2.Pres.of_run hpresPT ht0 hparse
  have hb1 : t1.buffer = (transcriptOf E H ms).buffer :=
    Midfall.Halo2.Pres.buffer hpresPT ht0 hparse
  have hpresRA : Midfall.Halo2.Pres (Midfall.Halo2.Verifier.readAlgebra (p := p) E.g1
      Features.solidity vk s2.trace.permutations s2.trace.lookups s2.trace.trashcans 1
      (instanceShape inst).size (instanceShape inst)) :=
    Midfall.Halo2.pres_readAlgebra (p := p) E.g1 Features.solidity vk
      s2.trace.permutations s2.trace.lookups s2.trace.trashcans 1
      (instanceShape inst).size (instanceShape inst)
  have hb2 : t2.buffer = t1.buffer :=
    Midfall.Halo2.Pres.buffer hpresRA ht1 hread1
  exact hb2.trans hb1

theorem snapshotXcriptRun_fields_of_tail (R : Render p G₁ G₂ Gₜ) (H : Hash)
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)}
    (hTail : XcriptAlgebraTail R H inst ms)
    {x : SnapXcript p G₁}
    (hx : snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x)
    (henc : ∀ Q, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (R.E.g1.toCompressed Q).size = g1CompressedWidth)
    (hp : p ≤ 2 ^ 256) :
    ∃ (s2 : SnapAlgebra p G₁) (t2 : Transcript) (pref : Bytes) (fCom pi : G₁) (qs : List (Fr p)),
      snapshotAlgebraRun R.E H R.vk inst ms = .ok (s2, t2) ∧
      t2.buffer = pref ++ R.E.g1.toCompressed fCom ++ wireOf (p := p) qs ++
        R.E.g1.toCompressed pi ∧
      t2.pos = pref.size ∧ qs.length = R.nSets ∧
      x.trace = s2.trace ∧ x.alg = s2.alg ∧
      x.r.fCom = fCom ∧ x.r.pi = pi := by
  obtain ⟨s2, t2, pref, fCom, pi, qs, hAlg, hbuf, hpos, hlen⟩ := hTail
  obtain ⟨r, t5, hrun, hf, hpi, hq, hpos5, hbuf5⟩ :=
    pcsReads_run_ok R.E.g1 R.E.field Features.solidity R.nSets t2 pref fCom pi qs
      hlen hbuf hpos henc hwidth hp
  unfold snapshotXcriptRun at hx
  simp only [StateT.run_bind, StateT.run_pure] at hx
  rw [hAlg] at hx
  simp only [Except.bind, Except.pure, bind, pure] at hx
  rw [hrun] at hx
  simp only [Except.bind, Except.pure, bind, pure] at hx
  rw [assertEmpty_run_ok t5 (by rw [hbuf5, hpos5])] at hx
  simp only [Except.bind, Except.pure, bind, pure] at hx
  have hxeq : x = ({ toSnapAlgebra := s2, r := r } : SnapXcript p G₁) := (Except.ok.inj hx).symm
  subst hxeq
  exact ⟨s2, t2, pref, fCom, pi, qs, hAlg, hbuf, hpos, hlen, rfl, rfl, hf, hpi⟩

theorem xcript_advice_value (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    (horder : AdvicePhasesColumnOrder R.vk)
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)}
    (hTail : XcriptAlgebraTail R H inst ms)
    {x : SnapXcript p G₁}
    (hx : snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x)
    (QAdv QMult QPerm QLook QTrash : List G₁) (rest : List (Msg (Fr p) G₁))
    (hms : ms = QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))) ++ rest)
    (hAdv : QAdv.length = (R.vk.cs.phases.map (fun ph => (phaseCols R.vk.cs ph).length)).sum)
    (hMult : QMult.length = R.vk.cs.lookups.size)
    (hPerm : QPerm.length = Permutation.numChunksOf R.vk.cs.permutation.columns.size
      (R.vk.csDegree - 2))
    (hLook : QLook.length = (R.vk.cs.lookups.toList.map
      (fun l => lookupChunkNum R.vk.csDegree l + 1)).sum)
    (hTrash : QTrash.length = R.vk.cs.trashcans.size) :
    x.trace.adviceCommitments.getD 0 #[] = QAdv.toArray := by
  have hf : R.vk.WellFormed Features.solidity := hR.supported.wf
  have hnc : 2 = R.vk.cs.numInstanceColumns := hR.supported.instShape.1.symm
  have hsp : R.vk.cs.numChallenges = 0 := hf.singlePhase
  have hdeg : 3 ≤ R.vk.csDegree := hf.chunkLenPositive
  have hs : ∀ l ∈ R.vk.cs.lookups.toList, ∃ c, l.chunkByDegree R.vk.csDegree = .ok c :=
    fun l hl => chunkByDegree_ok_of_wf hf hl
  have hp : p ≤ 2 ^ 256 := by
    rw [hR.env.modulus]; norm_num [frModulusConstant]
  have henc : ∀ Q, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q :=
    hcodec.compressedEncoderFirst
  have hwidth : ∀ Q, (R.E.g1.toCompressed Q).size = g1CompressedWidth :=
    hcodec.compressedWidth
  obtain ⟨s2, t2, pref, fCom, pi, qs, hAlg, hbuf, hpos, hlen, hxtr, hxalg, hfcom, hpi⟩ :=
    snapshotXcriptRun_fields_of_tail R H hTail hx henc hwidth hp
  obtain ⟨t1, htrace, hread⟩ :=
    Midfall.Lowering.snapshotAlgebraRun_readAlgebra R.E H R.vk inst ms s2 t2 hAlg
  obtain hparse :=
    Midfall.Lowering.snapshotTraceRun_parseTrace R.E H R.vk inst ms s2.toSnapTrace t1 htrace
  have hAdvRun := runsAllP_parseTrace_advice R.E R.vk inst hf hnc hsp horder hdeg hs
    QAdv QMult QPerm QLook QTrash hAdv hMult hPerm hLook hTrash
  have hbuf0 : (transcriptOf R.E H ms).buffer =
      Bytes.empty ++ (wireMsgs R.E (QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
              (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ []))))) ++
        wireMsgs R.E rest) := by
    rw [(transcriptOf_buffer R.E H ms).1, hms, wireMsgs_append]
    simp [bytes_empty_append_local]
  have hpos0 : (transcriptOf R.E H ms).pos = Bytes.empty.size := by
    rw [(transcriptOf_buffer R.E H ms).2]
    rfl
  obtain ⟨tr, t1', hrun', hbuf', hpos', hadv'⟩ :=
    hAdvRun (transcriptOf R.E H ms) Bytes.empty (wireMsgs R.E rest) hbuf0 hpos0 hp henc hwidth
  have heq : (tr, t1') = (s2.trace, t1) := by
    rw [hrun'] at hparse
    exact Except.ok.inj hparse
  have htr : tr = s2.trace := congrArg Prod.fst heq
  rw [htr] at hadv'
  rw [hxtr]
  exact hadv'

theorem xcript_quotient_value (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)}
    (hTail : XcriptAlgebraTail R H inst ms)
    {x : SnapXcript p G₁}
    (hx : snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x)
    (QAdv QMult QPerm QLook QTrash Qg : List G₁)
    (Qi Qa Qf Qc Qp Ql Qt qs : List (Fr p)) (fCom pi : G₁)
    (hms : ms = xcriptPt QAdv QMult QPerm QLook QTrash ++
      xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt ++ xcriptTail fCom qs pi)
    (hAdv : QAdv.length = (R.vk.cs.phases.map (fun ph => (phaseCols R.vk.cs ph).length)).sum)
    (hMult : QMult.length = R.vk.cs.lookups.size)
    (hPerm : QPerm.length = Permutation.numChunksOf R.vk.cs.permutation.columns.size
      (R.vk.csDegree - 2))
    (hLook : QLook.length = (R.vk.cs.lookups.toList.map
      (fun l => lookupChunkNum R.vk.csDegree l + 1)).sum)
    (hTrash : QTrash.length = R.vk.cs.trashcans.size)
    (hQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else R.vk.domain.getQuotientPolyDegree))
    (hI : Qi.length = (instanceShape inst).size *
      (R.vk.cs.instanceQueries.toList.filter (fun q => decide (q.1.index < 1))).length)
    (hA : Qa.length = (instanceShape inst).size * R.vk.cs.adviceQueries.size)
    (hF : Qf.length = R.vk.cs.numFixedColumns - R.vk.cs.numSimpleSelectors)
    (hC : Qc.length = R.vk.permutation.commitments.size)
    (hP : Qp.length = (Permutation.numChunksOf R.vk.cs.permutation.columns.size
      (R.vk.csDegree - 2)) * 3 - 1)
    (hL : Ql.length = (R.vk.cs.lookups.toList.map
      (fun l => lookupChunkNum R.vk.csDegree l + 3)).sum)
    (hT : Qt.length = R.vk.cs.trashcans.size)
    (hinstQ : ∀ q ∈ R.vk.cs.instanceQueries.toList, ¬ q.1.index < 1 → q.1.index = 1)
    (hinstSize : inst.size < 2 ^ 31) :
    x.alg.quotientLimbComs.toList = Qg := by
  have hf : R.vk.WellFormed Features.solidity := hR.supported.wf
  have hnc : 2 = R.vk.cs.numInstanceColumns := hR.supported.instShape.1.symm
  have hsp : R.vk.cs.numChallenges = 0 := hf.singlePhase
  have hdeg : 3 ≤ R.vk.csDegree := hf.chunkLenPositive
  have hs : ∀ l ∈ R.vk.cs.lookups.toList, ∃ c, l.chunkByDegree R.vk.csDegree = .ok c :=
    fun l hl => chunkByDegree_ok_of_wf hf hl
  have hp : p ≤ 2 ^ 256 := by
    rw [hR.env.modulus]; norm_num [frModulusConstant]
  have henc : ∀ Q, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q :=
    hcodec.compressedEncoderFirst
  have hwidth : ∀ Q, (R.E.g1.toCompressed Q).size = g1CompressedWidth :=
    hcodec.compressedWidth
  obtain ⟨s2, t2, pref, fCom0, pi0, qs0, hAlg, hbuf, hpos, hlen, hxtr, hxalg, hfcom, hpi⟩ :=
    snapshotXcriptRun_fields_of_tail R H hTail hx henc hwidth hp
  obtain ⟨t1, htrace, hread⟩ :=
    Midfall.Lowering.snapshotAlgebraRun_readAlgebra R.E H R.vk inst ms s2 t2 hAlg
  obtain hparse :=
    Midfall.Lowering.snapshotTraceRun_parseTrace R.E H R.vk inst ms s2.toSnapTrace t1 htrace
  have hmax : maxInstanceLen (instanceShape inst) < 2 ^ 31 := by
    simpa [maxInstanceLen, instanceShape] using hinstSize
  have hrows : ∀ row ∈ (instanceShape inst).toList,
      ∀ q ∈ R.vk.cs.instanceQueries.toList, ¬ q.1.index < 1 →
        ∃ col, row[q.1.index - 1]? = some col := by
    intro row hrow q hq hnc'
    have hrow' : row = #[inst] := by simpa [instanceShape] using hrow
    subst hrow'
    have hq1 := hinstQ q hq hnc'
    exact ⟨inst, by rw [hq1]; rfl⟩
  let Ra := xcriptRa (p := p) Qg Qi Qa Qf Qc Qp Ql Qt
  let Tail := xcriptTail (p := p) fCom qs pi
  let Pt := xcriptPt (p := p) QAdv QMult QPerm QLook QTrash
  have hms' : ms = Pt ++ (Ra ++ Tail) := by
    simpa only [Pt, Ra, Tail, List.append_assoc] using hms
  have hmsP : ms = Pt ++ (Ra ++ Tail) := hms'
  obtain ⟨trace, t1', hrun', hbuf1, hpos1, hperm, hlook, htrash⟩ :=
    parseTrace_run_of_ms_sizes_rest R.E H R.vk inst hf hnc hsp hdeg hs
      QAdv QMult QPerm QLook QTrash hAdv hMult hPerm hLook hTrash hp henc hwidth ms
      (Ra ++ Tail) hmsP
  have heq : (trace, t1') = (s2.trace, t1) := by
    rw [hrun'] at hparse
    exact Except.ok.inj hparse
  have htr : trace = s2.trace := congrArg Prod.fst heq
  have ht1 : t1' = t1 := congrArg Prod.snd heq
  rw [ht1] at hbuf1 hpos1
  -- readAlgebra value at t1
  have hbufRead : t1.buffer = wireMsgs R.E Pt ++ (wireMsgs R.E Ra ++ wireMsgs R.E Tail) := by
    rw [hbuf1, (transcriptOf_buffer R.E H ms).1, hms']
    simp only [Pt, Ra, Tail, wireMsgs_append, ByteArray.append_assoc]
  have hposRead : t1.pos = (wireMsgs R.E Pt).size := hpos1
  have hlenA' : Qa.length = 1 * R.vk.cs.adviceQueries.size := by
    simpa [instanceShape] using hA
  have hlenP' : Qp.length = (trace.permutations.toList.map (fun pc =>
      3 * pc.permutationProductCommitments.size - 1)).sum := by
    rw [hperm]; omega
  have hlenL' : Ql.length = (trace.lookups.toList.map (fun row =>
      (row.toList.map (fun c => c.helperPolys.size + 3)).sum)).sum := by
    rw [hlook]; exact hL
  have hlenT' : Qt.length = (trace.trashcans.toList.map (fun row => row.size)).sum := by
    rw [htrash]; exact hT
  obtain ⟨alg, t2', hread', hbuf2, hpos2, hquot⟩ :=
    runsAllP_readAlgebra_quotient_values R.E R.vk hf trace.permutations trace.lookups trace.trashcans
      1 1 (instanceShape inst) hmax hrows Qg Qi Qa Qf Qc Qp Ql Qt hQ hI hlenA' hF hC hlenP' hlenL' hlenT'
      t1 (wireMsgs R.E Pt) (wireMsgs R.E Tail) (by
        rw [hbufRead]; dsimp only [Pt, Ra, Tail, xcriptPt, xcriptRa])
      (by rw [hposRead]) hp henc hwidth
  have hread1 : StateT.run
      (Midfall.Halo2.Verifier.readAlgebra (p := p) R.E.g1 Features.solidity R.vk
        trace.permutations trace.lookups trace.trashcans 1 1 (instanceShape inst)) t1 =
      .ok (s2.alg, t2) := by
    -- s2.trace is trace, and the actual readAlgebra uses the same arguments
    subst htr
    simpa [committedShape, instanceShape] using hread
  have heq2 : (alg, t2') = (s2.alg, t2) := by
    rw [hread'] at hread1
    exact Except.ok.inj hread1
  have halg : alg = s2.alg := congrArg Prod.fst heq2
  rw [halg] at hquot
  rw [hxalg]
  exact hquot

theorem xcript_tail_fCom_pi (R : Render p G₁ G₂ Gₜ) (H : Hash)
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)}
    (hTail : XcriptAlgebraTail R H inst ms)
    {x : SnapXcript p G₁}
    (hx : snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x)
    (henc : ∀ Q, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q)
    (hwidth : ∀ Q, (R.E.g1.toCompressed Q).size = g1CompressedWidth)
    (hp : p ≤ 2 ^ 256)
    {QPre : List G₁} {QEv : List (Fr p)} {fComD : G₁} {qsD : List (Fr p)} {piD : G₁}
    (hsplit : ms = QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ([Msg.g1 fComD] ++
          (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD]))))
    (hlenD : qsD.length = R.nSets) :
    x.r.fCom = fComD ∧ x.r.pi = piD := by
  obtain ⟨s2, t2, pref, fCom, pi, qs, hAlg, hbuf, hpos, hlen, hxtr, hxalg, hf, hpi⟩ :=
    snapshotXcriptRun_fields_of_tail R H hTail hx henc hwidth hp
  have hbufFull : t2.buffer = wireMsgs R.E ms := by
    rw [snapshotAlgebraRun_buffer R.E H R.vk inst ms s2 t2 hAlg]
    exact (transcriptOf_buffer R.E H ms).1
  have hwire : wireMsgs R.E ms =
      wireMsgs R.E (QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁))) ++
      R.E.g1.toCompressed fComD ++ wireOf (p := p) qsD ++ R.E.g1.toCompressed piD := by
    rw [hsplit]
    simp [List.append_assoc, ByteArray.append_assoc, wireMsgs, wireMsgs_append,
      wireMsgs_cons, msgWire, wireMsgs_g1_singleton, wireMsgs_map_fr,
      bytes_append_empty_local]
  let prefD := wireMsgs R.E (QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
    QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)))
  let X := wireOf (p := p) qs
  let XD := wireOf (p := p) qsD
  let C := R.E.g1.toCompressed fCom
  let D := R.E.g1.toCompressed fComD
  let Z := R.E.g1.toCompressed pi
  let W := R.E.g1.toCompressed piD
  have hEq : pref ++ C ++ X ++ Z = prefD ++ D ++ XD ++ W := by
    calc
      pref ++ C ++ X ++ Z = t2.buffer := hbuf.symm
      _ = wireMsgs R.E ms := hbufFull
      _ = prefD ++ D ++ XD ++ W := hwire
  have hXsize : X.size = XD.size := by
    simp only [X, XD, wireOf_size, hlen, hlenD]
  have hZsize : Z.size = W.size := by
    simp only [Z, W]
    rw [hwidth pi, hwidth piD]
  have hCsize : C.size = D.size := by
    simp only [C, D]
    rw [hwidth fCom, hwidth fComD]
  have hAsize : (pref ++ C).size = (prefD ++ D).size := by
    have hL : (pref ++ C ++ X ++ Z).size =
        pref.size + C.size + X.size + Z.size := by
      simp only [ByteArray.size_append]
    have hR : (prefD ++ D ++ XD ++ W).size =
        prefD.size + D.size + XD.size + W.size := by
      simp only [ByteArray.size_append]
    have h := congrArg ByteArray.size hEq
    rw [hL, hR] at h
    rw [ByteArray.size_append, ByteArray.size_append]
    omega
  have hEq' : (pref ++ C) ++ (X ++ Z) = (prefD ++ D) ++ (XD ++ W) := by
    simpa only [ByteArray.append_assoc] using hEq
  have hA : pref ++ C = prefD ++ D := bytes_prefix_cancel hEq' hAsize
  have htailEq : X ++ Z = XD ++ W := by
    rw [hA] at hEq'
    exact bytes_append_cancel_left hEq'
  have hX : X = XD := bytes_prefix_cancel htailEq hXsize
  have hZ : Z = W := by
    rw [hX] at htailEq
    exact bytes_append_cancel_left htailEq
  have hCD : C = D := bytes_suffix_cancel hA hCsize
  have hfcom : fCom = fComD := by
    have h := congrArg R.E.g1.ofCompressed? hCD
    rw [henc fCom, henc fComD] at h
    exact Option.some.inj h
  have hpi' : pi = piD := by
    have h := congrArg R.E.g1.ofCompressed? hZ
    rw [henc pi, henc piD] at h
    exact Option.some.inj h
  exact ⟨hf.trans hfcom, hpi.trans hpi'⟩

theorem xcript_total_at (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)}
    (h : XcriptAlgebraTail R H inst ms) :
    ∃ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x := by
  obtain ⟨s2, t2, pref, fCom, pi, qs, hAlg, hbuf, hpos, hlen⟩ := h
  exact snapshotXcriptRun_of_algebra R.E H R.vk inst ms R.nSets s2 t2 hAlg pref fCom pi qs
    hlen hbuf hpos hcodec.compressedEncoderFirst hcodec.compressedWidth
    (by rw [hR.env.modulus]; norm_num [frModulusConstant])

/-- **`xcript_total`'s EXISTENCE CONCLUSION, FROM THE NAMED CLAUSE.** The codec laws are the
    headline's (`compressedEncoderFirst`, `compressedWidth`), and `p ≤ 2^256` is
    `EnvAgrees.modulus` on the literal `FR_MODULUS`. No other hypothesis is spent. -/
theorem xcript_total_of_algebraRun (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (cd : Bytes)
    (h : XcriptAlgebraRun R H cd) :
    ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
        ∃ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x := by
  intro ms instW inst hdec
  exact xcript_total_at R hR hcodec H (h ms instW inst hdec)

/-- **THE EXISTENCE HALF OF `Agree .transcript`, AT A FIXED DECODE.** The Lean stage is
    `snapshotXcriptRun` followed by `padSnap`, so the witness is `padSnap x` at the run's `x`. -/
theorem leanStage_transcript_exists_at (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)}
    (h : XcriptAlgebraTail R H inst ms) :
    ∃ S, leanStage R H inst ms Checkpoint.transcript = .ok S := by
  obtain ⟨x, hx⟩ := xcript_total_at R hR hcodec H h
  refine ⟨padSnap x ⟨0, 0, 0⟩ none #[], ?_⟩
  unfold leanStage
  rw [hx]
  rfl

/-- **THE EXISTENCE HALF OF `Agree .transcript`, FOR EVERY DECODING.** This is what
    `tp_agrees` needs from the Lean side; the `Inv` half is the separate slot/mirror assembly. -/
theorem leanStage_transcript_exists_of_algebraRun (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (cd : Bytes)
    (h : XcriptAlgebraRun R H cd) :
    ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
        ∃ S, leanStage R H inst ms Checkpoint.transcript = .ok S := by
  intro ms instW inst hdec
  exact leanStage_transcript_exists_at R hR hcodec H (h ms instW inst hdec)


/-! ## 4. ROW.TP.6'S BRIDGE — THE MODEL'S PARSER FACTS AND THE PLAN'S LAYOUT -/

/-- `metaDataForVk` rewrites only `numEvals`, `numDummyEvals` and `numPointSets`: the seven fields
    the parser schedule reads are conserved. PROVED by peeling the seven binds. -/
theorem metaDataForVk_conserves (feat : Features) (env : VkBuildEnv QuotientProgramPlan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    {m : ConstraintSystemMeta} {d : Midfall.Generator.Data} {mem : VerifierMemoryLayout}
    (h : metaDataForVk feat env meta_ numInstances vk vkMptr = .ok (m, d, mem)) :
    m.protocol = meta_.protocol ∧ m.numLookups = meta_.numLookups ∧
      m.lookupChunks = meta_.lookupChunks ∧ m.numPermutationZs = meta_.numPermutationZs ∧
      m.numTrashcans = meta_.numTrashcans ∧ m.numQuotients = meta_.numQuotients ∧
      m.numUserAdvices = meta_.numUserAdvices ∧ m.numUserChallenges = meta_.numUserChallenges := by
  cases hf : feat.outerFewerPointSets
  · simp only [metaDataForVk, Bind.bind, Except.bind, hf] at h
    obtain ⟨rawMemory, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨rawData, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨memory, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨data0, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨nSets, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨memory2, _, h⟩ := except_bind_ok _ _ h
    cases h
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [metaDataForVk, Bind.bind, Except.bind, hf] at h
    obtain ⟨rawMemory, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨rawData, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨nDummy, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨memory, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨data0, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨nSets, _, h⟩ := except_bind_ok _ _ h
    obtain ⟨memory2, _, h⟩ := except_bind_ok _ _ h
    cases h
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `metaDataForStableStaticLayout` loop's state. -/
abbrev TpStableState :=
  Option (Ptr × ConstraintSystemMeta × Midfall.Generator.Data × VerifierMemoryLayout) × Ptr

/-- The seven parser fields conserved by one iteration of the stable-layout loop. -/
def TpMetaConserves (base m : ConstraintSystemMeta) : Prop :=
  m.protocol = base.protocol ∧ m.numLookups = base.numLookups ∧
    m.lookupChunks = base.lookupChunks ∧ m.numPermutationZs = base.numPermutationZs ∧
    m.numTrashcans = base.numTrashcans ∧ m.numQuotients = base.numQuotients ∧
    m.numUserAdvices = base.numUserAdvices ∧ m.numUserChallenges = base.numUserChallenges

theorem tpMetaConserves_of_vk (feat : Features) (env : VkBuildEnv QuotientProgramPlan)
    (base : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    {m : ConstraintSystemMeta} {d : Midfall.Generator.Data} {mem : VerifierMemoryLayout}
    {vkMptr : Ptr}
    (h : metaDataForVk feat env base numInstances vk vkMptr = .ok (m, d, mem)) :
    TpMetaConserves base m :=
  metaDataForVk_conserves feat env base numInstances vk vkMptr h

/-- The stable-layout loop's step, named so the fold can be reasoned about. -/
def tpStableStep (feat : Features) (env : VkBuildEnv QuotientProgramPlan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    (st : TpStableState) : Except Fault TpStableState :=
  if st.1.isSome then Except.ok st else
    let vkMptr := st.2
    do
      let (metaOut, dat, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
      let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
      let cur ← Value.asUsize vkMptr.value
      if planned == cur then
        Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
      else
        Except.ok (none, ptrMemory (valueFromNat planned))

theorem tpStableStep_conserves (feat : Features) (env : VkBuildEnv QuotientProgramPlan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    {st res : TpStableState}
    (hInv : ∀ (ptr : Ptr) (m : ConstraintSystemMeta) (d : Midfall.Generator.Data)
      (mem : VerifierMemoryLayout), st.1 = some (ptr, m, d, mem) → TpMetaConserves meta_ m)
    (h : tpStableStep feat env meta_ numInstances vk st = .ok res) :
    ∀ (ptr : Ptr) (m : ConstraintSystemMeta) (d : Midfall.Generator.Data)
      (mem : VerifierMemoryLayout), res.1 = some (ptr, m, d, mem) → TpMetaConserves meta_ m := by
  intro ptr m d mem hres
  unfold tpStableStep at h
  by_cases hs : st.1.isSome = true
  · rw [if_pos hs] at h
    cases h
    exact hInv ptr m d mem hres
  · rw [if_neg hs] at h
    obtain ⟨⟨metaOut, dat, memory⟩, h1, h2⟩ := except_bind_ok _ _ h
    obtain ⟨planned, _, h3⟩ := except_bind_ok _ _ h2
    obtain ⟨cur, _, h4⟩ := except_bind_ok _ _ h3
    split at h4
    · cases h4
      simp only [Option.some.injEq, Prod.mk.injEq] at hres
      obtain ⟨_, hm, _, _⟩ := hres
      rw [← hm]
      exact tpMetaConserves_of_vk feat env meta_ numInstances vk h1
    · cases h4
      simp at hres

theorem tpFold_meta_conserves (feat : Features) (env : VkBuildEnv QuotientProgramPlan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey) :
    ∀ (l : List Nat) (st res : TpStableState),
      (∀ (ptr : Ptr) (m : ConstraintSystemMeta) (d : Midfall.Generator.Data)
        (mem : VerifierMemoryLayout), st.1 = some (ptr, m, d, mem) → TpMetaConserves meta_ m) →
      l.foldlM (fun st (_ : Nat) => tpStableStep feat env meta_ numInstances vk st) st = .ok res →
      ∀ (ptr : Ptr) (m : ConstraintSystemMeta) (d : Midfall.Generator.Data)
        (mem : VerifierMemoryLayout), res.1 = some (ptr, m, d, mem) → TpMetaConserves meta_ m := by
  intro l
  induction l with
  | nil =>
      intro st res hinv h
      simp only [List.foldlM_nil] at h
      cases h
      exact hinv
  | cons a l ih =>
      intro st res hinv h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      exact ih st1 res (tpStableStep_conserves feat env meta_ numInstances vk hinv h1) h2

/-- `metaDataForStableStaticLayout` conserves the seven parser fields: every iteration's meta is
    `metaDataForVk` applied to the same base. PROVED. -/
theorem metaDataForStableStaticLayout_conserves (feat : Features)
    (env : VkBuildEnv QuotientProgramPlan) (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    (vk : Halo2VerifyingKey)
    {ptr : Ptr} {m : ConstraintSystemMeta} {d : Midfall.Generator.Data}
    {mem : VerifierMemoryLayout}
    (h : metaDataForStableStaticLayout feat env meta_ numInstances vk = .ok (ptr, m, d, mem)) :
    TpMetaConserves meta_ m := by
  unfold metaDataForStableStaticLayout at h
  obtain ⟨start, _, h⟩ := except_bind_ok _ _ h
  obtain ⟨⟨result, ptr2⟩, hfold, h⟩ := except_bind_ok _ _ h
  cases result with
  | none => simp at h
  | some r =>
      simp only at h
      cases h
      have hfold' : (List.range 3).foldlM
          (fun st (_ : Nat) => tpStableStep feat env meta_ numInstances vk st)
          (none, ptrMemory (valueFromNat start)) =
          .ok (some (ptr, m, d, mem), ptr2) := hfold
      exact tpFold_meta_conserves feat env meta_ numInstances vk (List.range 3)
        (none, ptrMemory (valueFromNat start)) (some (ptr, m, d, mem), ptr2)
        (fun _ _ _ _ hnone => by simp at hnone) hfold' ptr m d mem rfl

/-- Tuple form of `metaDataForStableStaticLayout_conserves`: the `newFromVk` peel gets the four
    components as one `Except.ok q`. -/
theorem metaDataForStableStaticLayout_conserves' (feat : Features)
    (env : VkBuildEnv QuotientProgramPlan) (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    (vk : Halo2VerifyingKey)
    {q : Ptr × ConstraintSystemMeta × Midfall.Generator.Data × VerifierMemoryLayout}
    (h : metaDataForStableStaticLayout feat env meta_ numInstances vk = .ok q) :
    TpMetaConserves meta_ q.2.1 := by
  obtain ⟨ptr, m, d, mem⟩ := q
  exact metaDataForStableStaticLayout_conserves feat env meta_ numInstances vk h

/-- **THE `newFromVk` PEEL, WITH THE META AND THE PROOF LAYOUT.** `plan.meta_` is the converged
    meta, `plan.proofLayout` is `fromProtocol`'s output, and the seven parser fields are the ones
    `rawMeta` carried. PROVED by the same peel `pfx_newFromVk_proofLayout` does, plus the loop
    conservation above. -/
theorem tp_newFromVk_facts {R : Render p G₁ G₂ Gₜ} (rawMeta : ConstraintSystemMeta)
    (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk Features.solidity
      (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk = .ok plan) :
    ∃ (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout),
      ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr meta_.numEvals
        meta_.numPointSets = .ok L ∧ plan.meta_ = meta_ ∧ plan.proofLayout = L ∧
      TpMetaConserves rawMeta meta_ := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, hq, h1⟩ := except_bind_ok _ _ h
  obtain ⟨proofLayout, hpl, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨_qplan, _, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨_build, _, h4⟩ := except_bind_ok _ _ h3
  obtain ⟨_nw, _, h5⟩ := except_bind_ok _ _ h4
  obtain ⟨_pcs, _, h6⟩ := except_bind_ok _ _ h5
  obtain ⟨_acc, _, h7⟩ := except_bind_ok _ _ h6
  obtain ⟨_memory, _, h8⟩ := except_bind_ok _ _ h7
  obtain ⟨_op, _, h9⟩ := except_bind_ok _ _ h8
  obtain ⟨_trip, _, h10⟩ := except_bind_ok _ _ h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals
    exact ⟨q.2.1, proofLayout, hpl, rfl, rfl,
      metaDataForStableStaticLayout_conserves' Features.solidity
        (Midfall.Generator.PlanNew.envOf (Midfall.Generator.PlanNew.frFieldCtx R.E.delta)
          R.vk.cs) rawMeta R.cfg.numInstances R.plan.vk hq⟩

/-- **THE ROW.TP.6 BRIDGE.** All the facts `tp_events_slots` needs, from `ValidV3.generated`
    alone: the plan's meta and layout are the generator's, the model's parser facts are computed
    from them, and the seven meta fields are the protocol's. PROVED (no new hypothesis). -/
theorem tp_planFacts {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ∃ (rawMeta meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout)
      (userPhases : List UserPhase),
      ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok rawMeta ∧
      R.plan.meta_ = meta_ ∧ R.plan.proofLayout = L ∧
      ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr meta_.numEvals
        meta_.numPointSets = .ok L ∧
      meta_.protocol = rawMeta.protocol ∧
      meta_.numLookups = rawMeta.numLookups ∧ meta_.lookupChunks = rawMeta.lookupChunks ∧
      meta_.numPermutationZs = rawMeta.numPermutationZs ∧
      meta_.numTrashcans = rawMeta.numTrashcans ∧ meta_.numQuotients = rawMeta.numQuotients ∧
      meta_.numUserAdvices = rawMeta.numUserAdvices ∧
      meta_.numUserChallenges = rawMeta.numUserChallenges ∧
      userPhasesOf meta_ L = .ok userPhases ∧
      R.model.userPhases = userPhases ∧
      R.model.numInstances = R.inputs.numInstances ∧
      R.model.truncatedChallenges = R.inputs.truncatedChallenges ∧
      R.model.numLookups = meta_.numLookups ∧
      R.model.numPermutationZs = meta_.numPermutationZs ∧
      R.model.numTrashcans = meta_.numTrashcans ∧
      R.model.lookupHPlusAcc = lookupHPlusAccOf meta_ := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := Midfall.LoweringV3.MemoryPairs.plan_of_generated
    hR.generated
  obtain ⟨meta_, L, hL, hpm, hpL, hcons⟩ := tp_newFromVk_facts rawMeta plan hpl
  have hmeta : R.plan.meta_ = meta_ := by rw [hp]; exact hpm
  have hlay : R.plan.proofLayout = L := by rw [hp]; exact hpL
  have hg := Midfall.LoweringV3.MemoryPairs.gvfp_of_generated hR.generated
  simp only [generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  · cases hg
  · cases hg
  · obtain ⟨_vd, _, h1⟩ := except_bind_ok _ _ hg
    obtain ⟨rendering, hrender, h2⟩ := except_bind_ok _ _ h1
    obtain ⟨_pcs, _, h3⟩ := except_bind_ok _ _ h2
    obtain ⟨_up, hup, h4⟩ := except_bind_ok _ _ h3
    obtain ⟨_afb, _, h5⟩ := except_bind_ok _ _ h4
    obtain ⟨_cg, _, h6⟩ := except_bind_ok _ _ h5
    obtain ⟨_ar, _, h7⟩ := except_bind_ok _ _ h6
    have hrec := Except.ok.inj h7
    have huser : R.model.userPhases = _up := by rw [← hrec]
    have hup' : userPhasesOf meta_ L = .ok _up := by
      rw [← hmeta, ← hlay]
      exact hup
    have hnInst : R.model.numInstances = R.inputs.numInstances := by rw [← hrec]
    have htrunc : R.model.truncatedChallenges = R.inputs.truncatedChallenges := by rw [← hrec]
    have hnLook : R.model.numLookups = meta_.numLookups := by
      rw [← hrec, ← hmeta]
    have hnPerm : R.model.numPermutationZs = meta_.numPermutationZs := by
      rw [← hrec, ← hmeta]
    have hnTrash : R.model.numTrashcans = meta_.numTrashcans := by
      rw [← hrec, ← hmeta]
    have hLH : R.model.lookupHPlusAcc = lookupHPlusAccOf meta_ := by
      rw [← hrec, ← hmeta]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := hcons
    exact ⟨rawMeta, meta_, L, _up, hraw, hmeta, hlay, hL, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc8, hup', huser, hnInst, htrunc, hnLook, hnPerm, hnTrash, hLH⟩

/-- `bumpAt` preserves the read-index vector's length. -/
theorem bumpAt_length (xs : List Nat) (i : Nat) (site : String) {ys : List Nat}
    (h : bumpAt xs i site = .ok ys) : ys.length = xs.length := by
  unfold bumpAt at h
  split at h
  · cases h
    rw [List.length_append, List.length_cons, List.length_drop, List.length_take]
    omega
  · cases h

/-- The phase fold's read-index vector keeps its length. -/
theorem foldlM_bumpAt_length (site : String) (phase : List Nat) :
    ∀ (init res : List Nat),
      phase.foldlM (fun xs p => bumpAt xs p site) init = .ok res → res.length = init.length := by
  induction phase with
  | nil =>
      intro init res h
      have h' : Except.ok init = (Except.ok res : Except Fault (List Nat)) := h
      cases h'
      rfl
  | cons p rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨mid, h1, h2⟩ := except_bind_ok _ _ h
      rw [ih mid res h2, bumpAt_length init p site h1]

/-- `sumNat` after replacing entry `i` by itself plus one: the sum rises by one. -/
theorem sumNat_take_bump (xs : List Nat) (i : Nat) :
    i < xs.length →
      sumNat (xs.take i ++ (xs.getD i 0 + 1) :: xs.drop (i + 1)) = sumNat xs + 1 := by
  induction xs generalizing i with
  | nil => intro h; simp at h
  | cons a as ih =>
      intro h
      cases i with
      | zero => simp [sumNat_cons]; omega
      | succ k =>
          have hk : k < as.length := by simpa using h
          simp only [List.take_succ_cons, List.drop_succ_cons, List.getD_cons_succ,
            List.cons_append, sumNat_cons, Nat.succ_eq_add_one]
          rw [ih k hk]
          omega

/-- `bumpAt` raises the sum by one. -/
theorem bumpAt_sumNat (xs : List Nat) (i : Nat) (site : String) {ys : List Nat}
    (h : bumpAt xs i site = .ok ys) : sumNat ys = sumNat xs + 1 := by
  unfold bumpAt at h
  split at h
  · cases h
    exact sumNat_take_bump xs i (by assumption)
  · cases h

/-- The phase fold's read-index vector sums to the phase count. -/
theorem foldlM_bumpAt_sumNat (site : String) (phase : List Nat) :
    ∀ (init res : List Nat),
      phase.foldlM (fun xs p => bumpAt xs p site) init = .ok res →
      sumNat res = sumNat init + phase.length := by
  induction phase with
  | nil =>
      intro init res h
      have h' : Except.ok init = (Except.ok res : Except Fault (List Nat)) := h
      cases h'
      simp
  | cons p rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨mid, h1, h2⟩ := except_bind_ok _ _ h
      rw [ih mid res h2, bumpAt_sumNat init p site h1]
      simp only [List.length_cons]
      omega

/-- `sumNat` of a list of zeros is zero. -/
theorem sumNat_replicate_zero (n : Nat) : sumNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, sumNat_cons, ih]

/-- `ProtocolPlan.remapping`'s per-phase counts sum to the phase-vector length. -/
theorem remapping_nums_sum (numPhase : Nat) (phase : List Nat) {nums idxs : List Nat}
    (h : ProtocolPlan.remapping numPhase phase = .ok (nums, idxs)) :
    sumNat nums = phase.length := by
  unfold ProtocolPlan.remapping at h
  obtain ⟨nums0, hnums, h⟩ := except_bind_ok _ _ h
  obtain ⟨offsets, _, h⟩ := except_bind_ok _ _ h
  obtain ⟨res, _, h⟩ := except_bind_ok _ _ h
  cases h
  rw [foldlM_bumpAt_sumNat _ phase _ _ hnums, sumNat_replicate_zero]
  omega

/-- `ProtocolPlan.remapping`'s read-index vector has length `numPhase`, whatever the phase list. -/
theorem remapping_nums_length (numPhase : Nat) (phase : List Nat) {nums idxs : List Nat}
    (h : ProtocolPlan.remapping numPhase phase = .ok (nums, idxs)) :
    nums.length = numPhase := by
  unfold ProtocolPlan.remapping at h
  obtain ⟨nums0, hnums, h⟩ := except_bind_ok _ _ h
  obtain ⟨offsets, _, h⟩ := except_bind_ok _ _ h
  obtain ⟨res, _, h⟩ := except_bind_ok _ _ h
  have hlen : nums0.length = numPhase := by
    rw [foldlM_bumpAt_length _ phase _ nums0 hnums, List.length_replicate]
  cases h
  simpa using hlen

/-- The section `takeCommitmentSection` reserves: its count, width and byte length, all from the
    `ProofSection.new` it constructs BEFORE the read-index checks. -/
theorem takeCommitmentSection_shape (protocol : ProtocolPlan) (readIdx cursor : Nat)
    (expected : CommitmentRead) (count : Nat) (label : String)
    {sect : ProofSection} {ri cur : Nat}
    (h : ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor expected count label
      = .ok (sect, ri, cur)) :
    sect.itemCount = count ∧ sect.itemBytes = Midfall.Generator.g1Bytes ∧
      sect.byteLen = count * Midfall.Generator.g1Bytes := by
  unfold ProofCalldataLayout.takeCommitmentSection at h
  obtain ⟨ri', _, h⟩ := except_bind_ok _ _ h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- The advice fold appends one section per count. -/
theorem foldlM_take_length (protocol : ProtocolPlan) (expected : CommitmentRead) (label : String) :
    ∀ (counts : List Nat) (init res : List ProofSection × Nat × Nat),
      counts.foldlM
        (fun st count =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2 expected count label).bind
            fun x => Except.ok (st.1 ++ [x.1], x.2.1, x.2.2)) init = .ok res →
      res.1.length = init.1.length + counts.length := by
  intro counts
  induction counts with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      rfl
  | cons c rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst⟩ := except_bind_ok _ _ h1
      have hst1 : st1.1 = init.1 ++ [x.1] := by cases hst; rfl
      rw [ih st1 res h2, hst1, List.length_append, List.length_singleton]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The `takeCommitmentSection` fold only appends sections: its result list is the
    initial list plus a fresh suffix of the fold's length. -/
theorem foldlM_take_prefix (protocol : ProtocolPlan) (expected : CommitmentRead)
    (label : String) :
    ∀ (counts : List Nat) (init res : List ProofSection × Nat × Nat),
      counts.foldlM
        (fun st count =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2 expected count label).bind
            fun x => Except.ok (st.1 ++ [x.1], x.2.1, x.2.2)) init = .ok res →
      ∃ extra, res.1 = init.1 ++ extra ∧ extra.length = counts.length := by
  intro counts
  induction counts with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      exact ⟨[], by simp, rfl⟩
  | cons c rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst⟩ := except_bind_ok _ _ h1
      have hst1 : st1.1 = init.1 ++ [x.1] := by cases hst; rfl
      obtain ⟨extra, hres, hlen⟩ := ih st1 res h2
      refine ⟨x.1 :: extra, ?_, ?_⟩
      · simp [hres, hst1, List.append_assoc]
      · simp [hlen]

/-- The i-th section of the fold has the i-th count (with the initial-list offset). -/
theorem takeCommitmentSection_cursor (protocol : ProtocolPlan) (readIdx cursor : Nat)
    (expected : CommitmentRead) (count : Nat) (label : String)
    {sect : ProofSection} {ri cur : Nat}
    (h : ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor expected count label
      = .ok (sect, ri, cur)) :
    cur = cursor + sect.byteLen := by
  unfold ProofCalldataLayout.takeCommitmentSection at h
  obtain ⟨ri', _, h⟩ := except_bind_ok _ _ h
  cases h
  rfl

theorem foldlM_take_cursor (protocol : ProtocolPlan) (expected : CommitmentRead) (label : String) :
    ∀ (counts : List Nat) (init res : List ProofSection × Nat × Nat),
      counts.foldlM
        (fun st count =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2 expected count label).bind
            fun x => Except.ok (st.1 ++ [x.1], x.2.1, x.2.2)) init = .ok res →
      res.2.2 = init.2.2 +
        Midfall.Lowering.sumNat ((res.1.drop init.1.length).map ProofSection.byteLen) := by
  intro counts
  induction counts with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      simp [Midfall.Lowering.sumNat]
  | cons c rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst⟩ := except_bind_ok _ _ h1
      have hst_eq : st1 = (init.1 ++ [x.1], x.2.1, x.2.2) := by cases hst; rfl
      have hcur : x.2.2 = init.2.2 + x.1.byteLen :=
        takeCommitmentSection_cursor protocol init.2.1 init.2.2 expected c label hx
      obtain ⟨suffix, hres, _⟩ := foldlM_take_prefix protocol expected label rest st1 res h2
      have hst_snd : st1.2.2 = x.2.2 := by cases hst; rfl
      have hdrop : res.1.drop init.1.length = [x.1] ++ suffix := by
        rw [hres, hst_eq, List.append_assoc, List.drop_append,
          List.drop_eq_nil_of_le (Nat.le_refl _), Nat.sub_self, List.drop_zero,
          List.nil_append]
      have hdrop2 : (st1.1 ++ suffix).drop st1.1.length = suffix := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.sub_self, List.drop_zero]
      rw [hdrop, List.map_append, List.map_cons, List.map_nil,
        Midfall.Lowering.sumNat_append, Midfall.Lowering.sumNat_cons,
        Midfall.Lowering.sumNat_nil]
      have ih' := ih st1 res h2
      rw [hres, hdrop2] at ih'
      rw [ih', hst_snd, hcur]
      omega

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]


theorem foldlM_lookups_prefix (protocol : ProtocolPlan) :
    ∀ (pairs : List (Nat × Nat))
      (init res : List ProofLookupCommitmentsLayout × Nat × Nat),
      pairs.foldlM
        (fun st pair =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2
              CommitmentRead.lookupHelper pair.2 "lookup helper").bind
            fun x =>
          (ProofCalldataLayout.takeCommitmentSection protocol x.2.1 x.2.2
              CommitmentRead.lookupAccumulator 1 "lookup accumulator").bind
            fun y =>
          Except.ok (st.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
            y.2.1, y.2.2)) init = .ok res →
      ∃ extra, res.1 = init.1 ++ extra ∧ extra.length = pairs.length := by
  intro pairs
  induction pairs with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      exact ⟨[], by simp, rfl⟩
  | cons pair rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, h1'⟩ := except_bind_ok _ _ h1
      obtain ⟨y, hy, hst⟩ := except_bind_ok _ _ h1'
      have hst1 : st1.1 = init.1 ++
          [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }] := by cases hst; rfl
      obtain ⟨extra, hres, hlen⟩ := ih st1 res h2
      refine ⟨{ lookup := pair.1, helpers := x.1, accumulator := y.1 } :: extra, ?_, ?_⟩
      · simp [hres, hst1, List.append_assoc]
      · simp [hlen]

theorem foldlM_lookups_cursor (protocol : ProtocolPlan) :
    ∀ (pairs : List (Nat × Nat))
      (init res : List ProofLookupCommitmentsLayout × Nat × Nat),
      pairs.foldlM
        (fun st pair =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2
              CommitmentRead.lookupHelper pair.2 "lookup helper").bind
            fun x =>
          (ProofCalldataLayout.takeCommitmentSection protocol x.2.1 x.2.2
              CommitmentRead.lookupAccumulator 1 "lookup accumulator").bind
            fun y =>
          Except.ok (st.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
            y.2.1, y.2.2)) init = .ok res →
      res.2.2 = init.2.2 +
        Midfall.Lowering.sumNat ((res.1.drop init.1.length).map
          (fun lk => lk.helpers.byteLen + lk.accumulator.byteLen)) := by
  intro pairs
  induction pairs with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      simp [Midfall.Lowering.sumNat]
  | cons pair rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, h1'⟩ := except_bind_ok _ _ h1
      obtain ⟨y, hy, hst⟩ := except_bind_ok _ _ h1'
      have hst_eq : st1 = (init.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
          y.2.1, y.2.2) := by cases hst; rfl
      have hcur1 : x.2.2 = init.2.2 + x.1.byteLen :=
        takeCommitmentSection_cursor protocol init.2.1 init.2.2
          CommitmentRead.lookupHelper pair.2 "lookup helper" hx
      have hcur2 : y.2.2 = x.2.2 + y.1.byteLen :=
        takeCommitmentSection_cursor protocol x.2.1 x.2.2
          CommitmentRead.lookupAccumulator 1 "lookup accumulator" hy
      obtain ⟨suffix, hres, _⟩ := foldlM_lookups_prefix protocol rest st1 res h2
      have hst_snd : st1.2.2 = y.2.2 := by cases hst; rfl
      have hdrop : res.1.drop init.1.length =
          [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }] ++ suffix := by
        rw [hres, hst_eq, List.append_assoc, List.drop_append,
          List.drop_eq_nil_of_le (Nat.le_refl _), Nat.sub_self, List.drop_zero,
          List.nil_append]
      have hdrop2 : (st1.1 ++ suffix).drop st1.1.length = suffix := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          Nat.sub_self, List.drop_zero]
      rw [hdrop, List.map_append, List.map_cons, List.map_nil,
        Midfall.Lowering.sumNat_append, Midfall.Lowering.sumNat_cons,
        Midfall.Lowering.sumNat_nil]
      have ih' := ih st1 res h2
      rw [hres, hdrop2] at ih'
      rw [ih', hst_snd, hcur2, hcur1]
      simp
      omega

theorem foldlM_take_sum_byteLen (protocol : ProtocolPlan) (expected : CommitmentRead)
    (label : String) :
    ∀ (counts : List Nat) (init res : List ProofSection × Nat × Nat),
      counts.foldlM
        (fun st count =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2 expected count label).bind
            fun x => Except.ok (st.1 ++ [x.1], x.2.1, x.2.2)) init = .ok res →
      Midfall.Lowering.sumNat
          ((res.1.drop init.1.length).map ProofSection.byteLen) =
        Midfall.Lowering.sumNat
          ((res.1.drop init.1.length).map
            (fun s => s.itemCount * Midfall.Generator.g1Bytes)) := by
  intro counts
  induction counts with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      simp
  | cons c rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst⟩ := except_bind_ok _ _ h1
      have hst_eq : st1 = (init.1 ++ [x.1], x.2.1, x.2.2) := by cases hst; rfl
      have hshape := takeCommitmentSection_shape protocol init.2.1 init.2.2 expected c label hx
      obtain ⟨suffix, hres, _⟩ := foldlM_take_prefix protocol expected label rest st1 res h2
      have hdrop : res.1.drop init.1.length = [x.1] ++ suffix := by
        rw [hres, hst_eq, List.append_assoc, List.drop_append,
          List.drop_eq_nil_of_le (Nat.le_refl _), Nat.sub_self, List.drop_zero,
          List.nil_append]
      have hdrop2 : (st1.1 ++ suffix).drop st1.1.length = suffix := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          Nat.sub_self, List.drop_zero]
      rw [hdrop]
      simp only [List.singleton_append, List.map_cons, List.map_nil,
        Midfall.Lowering.sumNat_cons, Midfall.Lowering.sumNat_nil]
      simp only [hshape.2.2]
      have ih' := ih st1 res h2
      rw [hres, hdrop2] at ih'
      rw [ih']
      have hc : x.1.itemCount = c := hshape.1
      rw [hc]
end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem foldlM_lookups_sum_byteLen (protocol : ProtocolPlan) :
    ∀ (pairs : List (Nat × Nat))
      (init res : List ProofLookupCommitmentsLayout × Nat × Nat),
      pairs.foldlM
        (fun st pair =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2
              CommitmentRead.lookupHelper pair.2 "lookup helper").bind
            fun x =>
          (ProofCalldataLayout.takeCommitmentSection protocol x.2.1 x.2.2
              CommitmentRead.lookupAccumulator 1 "lookup accumulator").bind
            fun y =>
          Except.ok (st.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
            y.2.1, y.2.2)) init = .ok res →
      Midfall.Lowering.sumNat
          ((res.1.drop init.1.length).map
            (fun lk => lk.helpers.byteLen + lk.accumulator.byteLen)) =
        Midfall.Lowering.sumNat
          ((res.1.drop init.1.length).map
            (fun lk => lk.helpers.itemCount * Midfall.Generator.g1Bytes +
              lk.accumulator.itemCount * Midfall.Generator.g1Bytes)) := by
  intro pairs
  induction pairs with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      simp
  | cons pair rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, h1'⟩ := except_bind_ok _ _ h1
      obtain ⟨y, hy, hst⟩ := except_bind_ok _ _ h1'
      have hst_eq : st1 = (init.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
          y.2.1, y.2.2) := by cases hst; rfl
      have hxshape := takeCommitmentSection_shape protocol init.2.1 init.2.2
        CommitmentRead.lookupHelper pair.2 "lookup helper" hx
      have hyshape := takeCommitmentSection_shape protocol x.2.1 x.2.2
        CommitmentRead.lookupAccumulator 1 "lookup accumulator" hy
      obtain ⟨suffix, hres, _⟩ := foldlM_lookups_prefix protocol rest st1 res h2
      have hdrop : res.1.drop init.1.length =
          [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }] ++ suffix := by
        rw [hres, hst_eq, List.append_assoc, List.drop_append,
          List.drop_eq_nil_of_le (Nat.le_refl _), Nat.sub_self, List.drop_zero,
          List.nil_append]
      have hdrop2 : (st1.1 ++ suffix).drop st1.1.length = suffix := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          Nat.sub_self, List.drop_zero]
      rw [hdrop]
      simp only [List.singleton_append, List.map_cons, List.map_nil,
        Midfall.Lowering.sumNat_cons, Midfall.Lowering.sumNat_nil, hxshape.2.2, hyshape.2.2]
      simp only [hxshape.1, hyshape.1]
      have ih' := ih st1 res h2
      rw [hres, hdrop2] at ih'
      rw [ih']

theorem takeCommitmentSection_start (protocol : ProtocolPlan) (readIdx cursor : Nat)
    (expected : CommitmentRead) (count : Nat) (label : String)
    {sect : ProofSection} {ri cur : Nat}
    (h : ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor expected count label
      = .ok (sect, ri, cur)) :
    sect.start = cursor := by
  unfold ProofCalldataLayout.takeCommitmentSection at h
  obtain ⟨ri', _, h⟩ := except_bind_ok _ _ h
  cases h
  rfl

theorem wordSection_start_end (cursor itemCount : Nat) :
    (ProofCalldataLayout.wordSection cursor itemCount).1.start = cursor ∧
      (ProofCalldataLayout.wordSection cursor itemCount).2 =
        cursor + (ProofCalldataLayout.wordSection cursor itemCount).1.byteLen := by
  unfold ProofCalldataLayout.wordSection ProofSection.new ProofSection.end
  simp [ProofSection.byteLen, ProofSection.start]

theorem fromProtocol_starts (protocol : ProtocolPlan) (numEvals numPointSets : Nat)
    {L : ProofCalldataLayout}
    (hL : ProofCalldataLayout.fromProtocol protocol abiVerifyProofProofCptr numEvals numPointSets
      = .ok L) :
    L.quotientLimbs.start = L.quotientCommCptr ∧
    L.evalCptr = L.quotientCommCptr + L.quotientLimbs.byteLen ∧
    L.evals.start = L.evalCptr ∧
    L.wCptr = L.evalCptr + L.evals.byteLen ∧
    L.fCom.start = L.wCptr ∧
    L.qEvalCptr = L.wCptr + L.fCom.byteLen ∧
    L.qEvals.start = L.qEvalCptr ∧
    L.pi.start = L.qEvalCptr + L.qEvals.byteLen ∧
    L.fCom.byteLen = Midfall.Generator.g1Bytes ∧
    L.pi.byteLen = Midfall.Generator.g1Bytes ∧
    L.fCom.itemCount = 1 ∧ L.pi.itemCount = 1 := by
  unfold ProofCalldataLayout.fromProtocol at hL
  simp only [Bind.bind, Except.bind] at hL
  obtain ⟨adv, hAdv, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lm, hLM, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨pp, hPP, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lks, hLksFold, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨tr, hTr, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨ql, hQl, hL⟩ := except_bind_ok _ _ hL
  split at hL
  · cases hL
  cases hL
  have hQlStart := takeCommitmentSection_start protocol tr.2.1 tr.2.2
    CommitmentRead.quotient protocol.numQuotients "quotient limb" hQl
  have hQlCur := takeCommitmentSection_cursor protocol tr.2.1 tr.2.2
    CommitmentRead.quotient protocol.numQuotients "quotient limb" hQl
  have hEv := wordSection_start_end ql.2.2 numEvals
  have hQE := wordSection_start_end (ProofSection.new (ProofCalldataLayout.wordSection ql.2.2 numEvals).2 1 Midfall.Generator.g1Bytes).end numPointSets
  refine ⟨hQlStart, hQlCur, hEv.1, ?_, ?_, ?_, hQE.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact hEv.2
  · rfl
  · rfl
  · exact hQE.2
  · rfl
  · rfl
  · rfl
  · rfl

theorem fromProtocol_quotientComm (protocol : ProtocolPlan) (numEvals numPointSets : Nat)
    {L : ProofCalldataLayout}
    (hL : ProofCalldataLayout.fromProtocol protocol abiVerifyProofProofCptr numEvals numPointSets
      = .ok L) :
    L.quotientCommCptr = L.proofCptr + Midfall.Generator.g1Bytes * L.nonQuotientG1Count := by
  unfold ProofCalldataLayout.fromProtocol at hL
  simp only [Bind.bind, Except.bind] at hL
  obtain ⟨adv, hAdv, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lm, hLM, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨pp, hPP, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lks, hLksFold, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨tr, hTr, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨ql, hQl, hL⟩ := except_bind_ok _ _ hL
  split at hL
  · cases hL
  cases hL
  have hAdvCur := foldlM_take_cursor protocol CommitmentRead.advice "advice phase"
    protocol.numUserAdvices ([], 0, abiVerifyProofProofCptr) adv hAdv
  have hAdvShape := foldlM_take_sum_byteLen protocol CommitmentRead.advice "advice phase"
    protocol.numUserAdvices ([], 0, abiVerifyProofProofCptr) adv hAdv
  have hLMCur := takeCommitmentSection_cursor protocol adv.2.1 adv.2.2
    CommitmentRead.lookupMultiplicity protocol.numLookups "lookup multiplicity" hLM
  have hLMShape := takeCommitmentSection_shape protocol adv.2.1 adv.2.2
    CommitmentRead.lookupMultiplicity protocol.numLookups "lookup multiplicity" hLM
  have hPPCur := takeCommitmentSection_cursor protocol lm.2.1 lm.2.2
    CommitmentRead.permutationProduct protocol.numPermutationZs "permutation product" hPP
  have hPPShape := takeCommitmentSection_shape protocol lm.2.1 lm.2.2
    CommitmentRead.permutationProduct protocol.numPermutationZs "permutation product" hPP
  have hLksCur := foldlM_lookups_cursor protocol
    ((List.range protocol.lookupChunks.length).zip protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold
  have hLksShape := foldlM_lookups_sum_byteLen protocol
    ((List.range protocol.lookupChunks.length).zip protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold
  have hTrCur := takeCommitmentSection_cursor protocol lks.2.1 lks.2.2
    CommitmentRead.trash protocol.numTrashcans "trash" hTr
  have hTrShape := takeCommitmentSection_shape protocol lks.2.1 lks.2.2
    CommitmentRead.trash protocol.numTrashcans "trash" hTr
  simp only [Midfall.Generator.g1Bytes, ProofCalldataLayout.nonQuotientG1Count]
  rw [hTrCur, hLksCur, hPPCur, hLMCur, hAdvCur]
  simp only [Prod.fst, List.length_nil, List.drop_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, Midfall.Lowering.sumNat_nil,
    Midfall.Lowering.sumNat_cons, Midfall.Lowering.sumNat_append]
  simp only [Prod.fst, List.length_nil, List.drop_zero] at hAdvShape hLksShape
  rw [hAdvShape, hLksShape]
  have hAdvFactor : Midfall.Lowering.sumNat
      (List.map (fun s => s.itemCount * Midfall.Generator.g1Bytes) adv.1) =
      Midfall.Generator.g1Bytes *
        Midfall.Lowering.sumNat (List.map (fun s => s.itemCount) adv.1) := by
    rw [show (fun s : ProofSection => s.itemCount * Midfall.Generator.g1Bytes) =
        (fun c : Nat => c * Midfall.Generator.g1Bytes) ∘
          (fun s : ProofSection => s.itemCount) by rfl]
    rw [← List.map_map, Midfall.Lowering.sumNat_map_mul]
  have hLkFactor : Midfall.Lowering.sumNat
      (List.map (fun lk => lk.helpers.itemCount * Midfall.Generator.g1Bytes +
        lk.accumulator.itemCount * Midfall.Generator.g1Bytes) lks.1) =
      Midfall.Generator.g1Bytes *
        Midfall.Lowering.sumNat
          (List.map (fun lk => lk.helpers.itemCount + lk.accumulator.itemCount) lks.1) := by
    rw [show (fun lk : ProofLookupCommitmentsLayout =>
        lk.helpers.itemCount * Midfall.Generator.g1Bytes +
          lk.accumulator.itemCount * Midfall.Generator.g1Bytes) =
      (fun c : Nat => c * Midfall.Generator.g1Bytes) ∘
        (fun lk : ProofLookupCommitmentsLayout =>
          lk.helpers.itemCount + lk.accumulator.itemCount) by
      funext lk
      simp only [Function.comp_apply]
      ring]
    rw [← List.map_map, Midfall.Lowering.sumNat_map_mul]
  rw [hAdvFactor, hLkFactor]
  rw [hLMShape.2.2, hPPShape.2.2, hTrShape.2.2]
  rw [hLMShape.1, hPPShape.1, hTrShape.1]
  simp only [Midfall.Generator.g1Bytes, Midfall.Generator.g1WordsCount, Midfall.Generator.wordBytes,
    Midfall.Lowering.sumNat]
  ring

theorem foldlM_take_nth (protocol : ProtocolPlan) (expected : CommitmentRead) (label : String) :
    ∀ (counts : List Nat) (init res : List ProofSection × Nat × Nat) (i : Nat)
      (s : ProofSection),
      counts.foldlM
        (fun st count =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2 expected count label).bind
            fun x => Except.ok (st.1 ++ [x.1], x.2.1, x.2.2)) init = .ok res →
      init.1.length ≤ i →
      res.1[i]? = some s →
      ∃ c, counts[i - init.1.length]? = some c ∧ s.itemCount = c := by
  intro counts
  induction counts with
  | nil =>
      intro init res i s h hle hs
      simp only [List.foldlM_nil] at h
      cases h
      have hnone : init.1[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [hnone] at hs
      cases hs
  | cons c rest ih =>
      intro init res i s h hle hs
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst⟩ := except_bind_ok _ _ h1
      have hst1 : st1.1 = init.1 ++ [x.1] := by cases hst; rfl
      have hxc : x.1.itemCount = c :=
        (takeCommitmentSection_shape protocol init.2.1 init.2.2 expected c label hx).1
      obtain ⟨extra, hres, hlen⟩ := foldlM_take_prefix protocol expected label rest st1 res h2
      by_cases hi : i = init.1.length
      · subst hi
        have hget : res.1[init.1.length]? = some x.1 := by
          rw [hres, hst1, List.getElem?_append]
          simp
        rw [hget] at hs
        have hseq : s = x.1 := (Option.some.inj hs).symm
        subst hseq
        exact ⟨c, by simp, hxc⟩
      · have hlt : init.1.length < i := lt_of_le_of_ne hle (Ne.symm hi)
        have hle' : st1.1.length ≤ i := by
          rw [hst1, List.length_append]
          simp
          omega
        obtain ⟨c', hc', hsc'⟩ := ih st1 res i s h2 hle' hs
        have hst1len : st1.1.length = init.1.length + 1 := by rw [hst1]; simp
        rw [hst1len] at hc'
        refine ⟨c', ?_, hsc'⟩
        have hidx : i - init.1.length = (i - (init.1.length + 1)) + 1 := by omega
        rw [hidx]
        rw [List.getElem?_cons_succ]
        exact hc'

/-- The lookup fold appends one row per `(lookup, chunks)` pair. -/
theorem foldlM_lookups_length (protocol : ProtocolPlan) :
    ∀ (pairs : List (Nat × Nat))
      (init res : List ProofLookupCommitmentsLayout × Nat × Nat),
      pairs.foldlM
        (fun st pair =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2
              CommitmentRead.lookupHelper pair.2 "lookup helper").bind
            fun x =>
          (ProofCalldataLayout.takeCommitmentSection protocol x.2.1 x.2.2
              CommitmentRead.lookupAccumulator 1 "lookup accumulator").bind
            fun y =>
          Except.ok (st.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
            y.2.1, y.2.2)) init = .ok res →
      res.1.length = init.1.length + pairs.length := by
  intro pairs
  induction pairs with
  | nil =>
      intro init res h
      simp only [List.foldlM_nil] at h
      cases h
      rfl
  | cons pr rest ih =>
      intro init res h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst1⟩ := except_bind_ok _ _ h1
      obtain ⟨y, hy, hst2⟩ := except_bind_ok _ _ hst1
      have hst1' : st1.1 = init.1 ++ [{ lookup := pr.1, helpers := x.1, accumulator := y.1 }] := by
        cases hst2; rfl
      rw [ih st1 res h2, hst1', List.length_append, List.length_singleton]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Every accumulator section the lookup fold reserves is ONE G1 frame. -/
theorem foldlM_lookups_accOne (protocol : ProtocolPlan) :
    ∀ (pairs : List (Nat × Nat))
      (init res : List ProofLookupCommitmentsLayout × Nat × Nat),
      pairs.foldlM
        (fun st pair =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2
              CommitmentRead.lookupHelper pair.2 "lookup helper").bind
            fun x =>
          (ProofCalldataLayout.takeCommitmentSection protocol x.2.1 x.2.2
              CommitmentRead.lookupAccumulator 1 "lookup accumulator").bind
            fun y =>
          Except.ok (st.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
            y.2.1, y.2.2)) init = .ok res →
      (∀ r, r ∈ init.1 → r.accumulator.itemCount = 1) →
      ∀ r, r ∈ res.1 → r.accumulator.itemCount = 1 := by
  intro pairs
  induction pairs with
  | nil =>
      intro init res h hinv r hr
      simp only [List.foldlM_nil] at h
      cases h
      exact hinv r hr
  | cons pr rest ih =>
      intro init res h hinv r hr
      rw [List.foldlM_cons] at h
      obtain ⟨st1, h1, h2⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst1⟩ := except_bind_ok _ _ h1
      obtain ⟨y, hy, hst2⟩ := except_bind_ok _ _ hst1
      have hst1' : st1.1 = init.1 ++ [{ lookup := pr.1, helpers := x.1, accumulator := y.1 }] := by
        cases hst2; rfl
      have hinv' : ∀ r, r ∈ st1.1 → r.accumulator.itemCount = 1 := by
        intro r hr
        rw [hst1'] at hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hinv r hr
        · exact (takeCommitmentSection_shape protocol x.2.1 x.2.2
            CommitmentRead.lookupAccumulator 1 "lookup accumulator" hy).1
      exact ih st1 res h2 hinv' r hr

/-- The second projections of `(range l.length).zip l` are `l` itself. -/
theorem zip_range_snd (l : List Nat) :
    ((List.range l.length).zip l).map (fun p => p.2) = l := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons]
      rw [List.zip_map_left, List.map_map]
      simp only [Function.comp_def, Prod.map, id_eq]
      rw [ih]

/-- The section facts `fromProtocol` gives, in one record so the row's algebra can take them as a
    single hypothesis. -/
structure TpLayoutFacts (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout) : Prop where
  adviceItemBytes : ∀ s, s ∈ L.advicePhases → s.itemBytes = Midfall.Generator.g1Bytes
  adviceByteLen : ∀ s, s ∈ L.advicePhases →
    s.byteLen = s.itemCount * Midfall.Generator.g1Bytes
  adviceLen : L.advicePhases.length = meta_.protocol.numUserAdvices.length
  adviceSum : sumNat (L.advicePhases.map (fun s => s.itemCount)) =
    sumNat meta_.protocol.numUserAdvices
  lookupM : L.lookupMultiplicities.itemCount = meta_.protocol.numLookups
  lookupMByte : L.lookupMultiplicities.byteLen =
    meta_.protocol.numLookups * Midfall.Generator.g1Bytes
  permZ : L.permutationProducts.itemCount = meta_.protocol.numPermutationZs
  permZByte : L.permutationProducts.byteLen =
    meta_.protocol.numPermutationZs * Midfall.Generator.g1Bytes
  lookupsLen : L.lookups.length = meta_.protocol.lookupChunks.length
  lookupsByte : ∀ lk, lk ∈ L.lookups →
    lk.helpers.itemBytes = Midfall.Generator.g1Bytes ∧
      lk.helpers.byteLen = lk.helpers.itemCount * Midfall.Generator.g1Bytes ∧
      lk.accumulator.itemBytes = Midfall.Generator.g1Bytes ∧
      lk.accumulator.byteLen = Midfall.Generator.g1Bytes
  lookupsAcc : ∀ lk, lk ∈ L.lookups → lk.accumulator.itemCount = 1
  lookupSum : sumNat (L.lookups.map (fun lk =>
    lk.helpers.itemCount + lk.accumulator.itemCount)) =
    sumNat (((List.range meta_.protocol.lookupChunks.length).zip
      meta_.protocol.lookupChunks).map (fun p => p.2 + 1))
  trash : L.trash.itemCount = meta_.protocol.numTrashcans
  trashByte : L.trash.byteLen = meta_.protocol.numTrashcans * Midfall.Generator.g1Bytes
  quotient : L.quotientLimbs.itemCount = meta_.protocol.numQuotients
  quotientByte : L.quotientLimbs.byteLen =
    meta_.protocol.numQuotients * Midfall.Generator.g1Bytes
  evals : L.evals.itemCount = meta_.numEvals
  evalsByte : L.evals.byteLen = meta_.numEvals * Midfall.Generator.wordBytes
  qEvals : L.qEvals.itemCount = meta_.numPointSets
  qEvalsByte : L.qEvals.byteLen = meta_.numPointSets * Midfall.Generator.wordBytes

/-- **THE `fromProtocol` PEEL.** Every section `fromProtocol` reserves has the count the protocol
    says, one G1 frame per commitment, and a `wordBytes` frame per scalar. PROVED. -/
theorem tp_fromProtocol {meta_ : ConstraintSystemMeta} {L : ProofCalldataLayout}
    (hL : ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr
      meta_.numEvals meta_.numPointSets = .ok L) :
    TpLayoutFacts meta_ L := by
  unfold ProofCalldataLayout.fromProtocol at hL
  simp only [Bind.bind, Except.bind] at hL
  obtain ⟨adv, hAdv, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lm, hLM, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨pp, hPP, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨lks, hLksFold, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨tr, hTr, hL⟩ := except_bind_ok _ _ hL
  obtain ⟨ql, hQl, hL⟩ := except_bind_ok _ _ hL
  split at hL
  · cases hL
  cases hL
  have hadv := foldlM_take_ok meta_.protocol CommitmentRead.advice "advice phase"
    meta_.protocol.numUserAdvices ([], 0, abiVerifyProofProofCptr) adv hAdv (by simp)
  have hadvLen := foldlM_take_length meta_.protocol CommitmentRead.advice "advice phase"
    meta_.protocol.numUserAdvices ([], 0, abiVerifyProofProofCptr) adv hAdv
  have hlm := takeCommitmentSection_shape meta_.protocol adv.2.1 adv.2.2
    CommitmentRead.lookupMultiplicity meta_.protocol.numLookups "lookup multiplicity" hLM
  have hpp := takeCommitmentSection_shape meta_.protocol lm.2.1 lm.2.2
    CommitmentRead.permutationProduct meta_.protocol.numPermutationZs "permutation product" hPP
  have hLks := foldlM_lookups_ok meta_.protocol
    ((List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold (by simp)
  have hLksLen := foldlM_lookups_length meta_.protocol
    ((List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold
  have hLksAcc := foldlM_lookups_accOne meta_.protocol
    ((List.range meta_.protocol.lookupChunks.length).zip meta_.protocol.lookupChunks)
    ([], pp.2.1, pp.2.2) lks hLksFold (by simp)
  have htr := takeCommitmentSection_shape meta_.protocol lks.2.1 lks.2.2
    CommitmentRead.trash meta_.protocol.numTrashcans "trash" hTr
  have hql := takeCommitmentSection_shape meta_.protocol tr.2.1 tr.2.2
    CommitmentRead.quotient meta_.protocol.numQuotients "quotient limb" hQl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hadv.2.1 s hs).1
  · intro s hs
    exact (hadv.2.1 s hs).2
  · rw [hadvLen]
    simp
  · simpa [sumNat_nil] using hadv.2.2
  · exact hlm.1
  · exact hlm.2.2
  · exact hpp.1
  · exact hpp.2.2
  · rw [hLksLen, List.length_zip, List.length_range]
    simp
  · intro lk hlk
    obtain ⟨hg, ha⟩ := hLks.2.1 lk hlk
    have ha2 := ha.2
    rw [hLksAcc lk hlk] at ha2
    exact ⟨hg.1, hg.2, ha.1, by simpa using ha2⟩
  · exact hLksAcc
  · simpa [sumNat_nil] using hLks.2.2
  · exact htr.1
  · exact htr.2.2
  · exact hql.1
  · exact hql.2.2
  · rfl
  · rfl
  · rfl
  · rfl

/-- `listNth` is list indexing. -/
theorem listNth_eq_getElem? {α : Type} (l : List α) (i : Nat) : listNth l i = l[i]? := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ k => exact ih k

/-- `mapM` preserves the list length. -/
theorem mapM_length {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (res : List β), l.mapM f = .ok res → res.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro res h
      have h' : Except.ok ([] : List β) = Except.ok res := h
      cases h'
      rfl
  | cons x xs ih =>
      intro res h
      simp only [List.mapM_cons, Bind.bind] at h
      obtain ⟨b0, _, h1⟩ := except_bind_ok _ _ h
      obtain ⟨bs, hbs, hres⟩ := except_bind_ok _ _ h1
      have hres' : res = b0 :: bs := by cases hres; rfl
      rw [hres', List.length_cons, ih bs hbs]
      rfl

/-- One step of `userPhasesOf`, named so the index argument is readable. -/
def tpUserPhaseStep (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout)
    (p : (Nat × Nat) × Nat) : Except Fault UserPhase :=
  match p with
  | ((_, nC), idx) =>
      match listNth L.advicePhases idx with
      | some ph =>
          Except.ok { adviceBytes := ph.byteLen, numChallenges := nC, challengeOffset := (meta_.numUserChallenges.take idx).foldl Nat.add 0 }
      | none => Except.error (artifactPanic
          "proofs/solidity-verifier/src/lowering/artifacts.rs:164")

/-- The per-phase table `userPhasesOf` builds, index for index: the phase at `i` reads
    `L.advicePhases[n + i]`, so its `adviceBytes` is that section's `byteLen`. -/
theorem userPhasesOf_aux (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout) :
    ∀ (pairs : List (Nat × Nat)) (n : Nat) (ups : List UserPhase),
      (pairs.zipIdx n).mapM (tpUserPhaseStep meta_ L) = .ok ups →
      ∀ (i : Nat) (ph : UserPhase) (s : ProofSection), ups[i]? = some ph →
        L.advicePhases[n + i]? = some s → ph.adviceBytes = s.byteLen := by
  intro pairs
  induction pairs with
  | nil =>
      intro n ups h i ph s hph hs
      simp only [List.zipIdx_nil, List.mapM_nil] at h
      cases h
      simp at hph
  | cons pr rest ih =>
      intro n ups h i ph s hph hs
      obtain ⟨p1, p2⟩ := pr
      simp only [List.zipIdx_cons, List.mapM_cons, Bind.bind] at h
      obtain ⟨ph0, hstep, h1⟩ := except_bind_ok _ _ h
      obtain ⟨restUps, hrest, hfin⟩ := except_bind_ok _ _ h1
      have hups : ups = ph0 :: restUps := by cases hfin; rfl
      have hstep1 : (match listNth L.advicePhases n with
          | some ph => Except.ok ({ adviceBytes := ph.byteLen, numChallenges := p2, challengeOffset := (meta_.numUserChallenges.take n).foldl Nat.add 0 } : UserPhase)
          | none => Except.error (artifactPanic
              "proofs/solidity-verifier/src/lowering/artifacts.rs:164")) = .ok ph0 := hstep
      cases hln : listNth L.advicePhases n with
      | none =>
          rw [hln] at hstep1
          cases hstep1
      | some s0 =>
          rw [hln] at hstep1
          cases hstep1
          cases i with
          | zero =>
              rw [hups] at hph
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hph
              subst hph
              rw [Nat.add_zero] at hs
              rw [listNth_eq_getElem?] at hln
              rw [hln] at hs
              have hs' : s0 = s := Option.some.inj hs
              rw [hs']
          | succ i =>
              rw [hups] at hph
              simp only [List.getElem?_cons_succ] at hph
              exact ih (n + 1) restUps hrest i ph s hph (by
                rwa [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc])

/-- **`userPhasesOf`, INDEXWISE.** Its length is the zip's and each phase's `adviceBytes` is the
    `byteLen` of the advice section at the same index. PROVED. -/
theorem userPhasesOf_advice (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout)
    {ups : List UserPhase} (h : userPhasesOf meta_ L = .ok ups) :
    ups.length = (List.zip meta_.numUserAdvices meta_.numUserChallenges).length ∧
      ∀ (i : Nat) (ph : UserPhase) (s : ProofSection), ups[i]? = some ph →
        L.advicePhases[i]? = some s → ph.adviceBytes = s.byteLen := by
  unfold userPhasesOf at h
  change ((List.zip meta_.numUserAdvices meta_.numUserChallenges).zipIdx 0).mapM
    (tpUserPhaseStep meta_ L) = .ok ups at h
  constructor
  · rw [mapM_length _ _ _ h, List.length_zipIdx]
  · intro i ph s hph hs
    exact userPhasesOf_aux meta_ L
      (List.zip meta_.numUserAdvices meta_.numUserChallenges) 0 ups h i ph s hph
      (by simpa using hs)

/-- The two per-phase lists `fromConstraintSystem` builds both come from `remapping numPhase`, so
    they have the same length. The final `if` is the I-6 fixed-eval check and the `match` is
    `plan.validate`; both are gated off by the `Except.ok` result, so `p` is the record. -/
theorem fromConstraintSystem_phase_lengths {F : Type} [BEq F] (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) {p : ProtocolPlan}
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok p) :
    p.numUserAdvices.length = p.numUserChallenges.length := by
  unfold ProtocolPlan.fromConstraintSystem at h
  obtain ⟨csDegree, _, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨lk, _, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨⟨adv, advIdx⟩, hAdv, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨⟨ch, chIdx⟩, hCh, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨bl, _, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  dsimp only [] at h
  split at h
  all_goals try cases h
  split at h
  all_goals try cases h
  rw [remapping_nums_length _ _ hAdv, remapping_nums_length _ _ hCh]

/-- The same for the assembled meta. -/
theorem ConstraintSystemMeta.new_phase_lengths {F : Type} [BEq F] (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) {m : ConstraintSystemMeta}
    (h : ConstraintSystemMeta.new feat cs nb = .ok m) :
    m.numUserAdvices.length = m.numUserChallenges.length := by
  unfold ConstraintSystemMeta.new at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨p, hp, h⟩ := except_bind_ok _ _ h
  injection h with hm
  rw [← hm]
  exact fromConstraintSystem_phase_lengths feat cs nb hp

/-- `sumNat` ignores the zero entries: the schedule's `!= 0` guards do not change a group sum. -/
theorem sumNat_filter_ne_zero (l : List Nat) :
    sumNat (l.filter (fun n => n != 0)) = sumNat l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x = 0
      · subst hx
        simp [sumNat_cons, ih]
      · have hx' : (x != 0) = true := by simp [hx]
        simp [sumNat_cons, hx', ih]

/-- A flatMap of `replicate` counts is one `replicate` of the sum. -/
theorem flatMap_replicate_eq {α β : Type} (l : List α) (f : α → Nat) (x : β) :
    l.flatMap (fun a => List.replicate (f a) x) =
      List.replicate (sumNat (l.map f)) x := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.flatMap_cons, ih, List.map_cons, sumNat_cons]
      simp only [List.replicate_append_replicate]

/-- The per-lookup pair of walks as one `replicate`. -/
theorem flatMap_lookups_replicate {β : Type} (l : List ProofLookupCommitmentsLayout) (x : β) :
    l.flatMap (fun lk => List.replicate (lk.helpers.itemCount) x ++
        List.replicate (lk.accumulator.itemCount) x) =
      List.replicate (sumNat (l.map (fun lk =>
        lk.helpers.itemCount + lk.accumulator.itemCount))) x := by
  induction l with
  | nil => rfl
  | cons lk rest ih =>
      rw [List.flatMap_cons, ih, List.map_cons, sumNat_cons]
      simp only [List.replicate_append_replicate]

/-- `g1Bytes` is 128, the width every G1 section uses. -/
theorem generator_g1Bytes_eq : Midfall.Generator.g1Bytes = 128 := rfl

/-- `wordBytes` is 32, the width every scalar section uses. -/
theorem generator_wordBytes_eq : Midfall.Generator.wordBytes = 32 := rfl

/-- The advice walks as one `replicate`: the phase table and the layout's advice sections are
    aligned index for index, and each section's byte length is its item count times 128. -/
theorem flatMap_advice_replicate (ups : List UserPhase) (adv : List ProofSection)
    (hlen : ups.length = adv.length)
    (hbytes : ∀ (i : Nat) (ph : UserPhase) (s : ProofSection), ups[i]? = some ph →
      adv[i]? = some s → ph.adviceBytes = s.byteLen ∧ s.byteLen = s.itemCount * 128) :
    ups.flatMap (fun ph => List.replicate (ph.adviceBytes / 128) WireSlot.g1) =
      List.replicate (sumNat (adv.map (fun s => s.itemCount))) WireSlot.g1 := by
  induction ups generalizing adv with
  | nil =>
      cases adv with
      | nil => rfl
      | cons s rest => simp at hlen
  | cons ph rest ih =>
      cases adv with
      | nil => simp at hlen
      | cons s advRest =>
          rw [List.flatMap_cons, List.map_cons, sumNat_cons]
          have h0 := hbytes 0 ph s (by simp) (by simp)
          have hdiv : s.byteLen / 128 = s.itemCount := by
            rw [h0.2, Nat.mul_div_cancel _ (by decide : 0 < 128)]
          have hlen' : rest.length = advRest.length := by simpa using hlen
          have hbytes' : ∀ (i : Nat) (ph : UserPhase) (s : ProofSection),
              rest[i]? = some ph → advRest[i]? = some s →
              ph.adviceBytes = s.byteLen ∧ s.byteLen = s.itemCount * 128 := by
            intro i ph' s' hp hs
            exact hbytes (i + 1) ph' s' (by simpa using hp) (by simpa using hs)
          rw [h0.1, hdiv, ih advRest hlen' hbytes']
          simp only [List.replicate_append_replicate]

/-- `fromConstraintSystem`'s plan has `numLookups = lookupChunks.length` by construction. -/
theorem fromConstraintSystem_numLookups {F : Type} [BEq F] (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) {p : ProtocolPlan}
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok p) :
    p.numLookups = p.lookupChunks.length := by
  unfold ProtocolPlan.fromConstraintSystem at h
  obtain ⟨csDegree, _, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨lk, _, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨⟨adv, advIdx⟩, hAdv, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨⟨ch, chIdx⟩, hCh, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨bl, _, h⟩ := (Midfall.LoweringV3.MemoryPairs.match_ok_iff _ _).mp h
  dsimp only [] at h
  split at h
  all_goals try cases h
  split at h
  all_goals try cases h
  rfl

/-- `ConstraintSystemMeta.new` copies six fields from the protocol verbatim. -/
theorem ConstraintSystemMeta.new_protocol_fields {F : Type} [BEq F] (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) {m : ConstraintSystemMeta}
    (h : ConstraintSystemMeta.new feat cs nb = .ok m) :
    m.numLookups = m.protocol.numLookups ∧ m.lookupChunks = m.protocol.lookupChunks ∧
      m.numPermutationZs = m.protocol.numPermutationZs ∧
      m.numTrashcans = m.protocol.numTrashcans ∧
      m.numUserAdvices = m.protocol.numUserAdvices ∧
      m.numUserChallenges = m.protocol.numUserChallenges ∧
      m.numQuotients = m.protocol.numQuotients := by
  unfold ConstraintSystemMeta.new at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨p, hp, h⟩ := except_bind_ok _ _ h
  injection h with hm
  rw [← hm]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The protocol of a `ConstraintSystemMeta.new` result carries the phase lengths, so the meta's
    two per-phase lists have equal length AND `numLookups = lookupChunks.length`. -/
theorem ConstraintSystemMeta.new_numLookups {F : Type} [BEq F] (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) {m : ConstraintSystemMeta}
    (h : ConstraintSystemMeta.new feat cs nb = .ok m) :
    m.numLookups = m.lookupChunks.length := by
  unfold ConstraintSystemMeta.new at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨p, hp, h⟩ := except_bind_ok _ _ h
  injection h with hm
  rw [← hm]
  exact fromConstraintSystem_numLookups feat cs nb hp

/-- A `replicate` guard is vacuous: the zero case is the empty list. -/
theorem tp_guard_replicate {α : Type} (n : Nat) (x : α) :
    (if n != 0 then List.replicate n x else []) = List.replicate n x := by
  by_cases h : n = 0
  · subst h
    simp
  · have h' : (n != 0) = true := by simp [h]
    rw [if_pos h']

/-- A flatMap guard is vacuous when the guard is false only on the empty list. -/
theorem tp_guard_flatMap {α β : Type} (n : Nat) (l : List α) (f : α → List β)
    (h : n ≠ 0 ∨ l = []) :
    (if n != 0 then l.flatMap f else []) = l.flatMap f := by
  rcases h with h | rfl
  · have h' : (n != 0) = true := by simp [h]
    rw [if_pos h']
  · simp

/-- A flatMap/replicate guard is vacuous when the guard is false only on the empty list. -/
theorem tp_guard_replicate_of_empty {α β : Type} (g : Nat) (l : List α) (f : α → Nat) (x : β)
    (h : g ≠ 0 ∨ l = []) :
    (if g != 0 then List.replicate (sumNat (l.map f)) x else []) =
      List.replicate (sumNat (l.map f)) x := by
  rcases h with h | rfl
  · rw [if_pos (by simp [h])]
  · simp [sumNat_nil]

/-- The per-lookup walks with the raw `byteLen / 128` counts. -/
theorem flatMap_lookups_byteLen {β : Type} (l : List ProofLookupCommitmentsLayout) (x : β)
    (h : ∀ lk, lk ∈ l → lk.helpers.byteLen / 128 = lk.helpers.itemCount ∧
      lk.accumulator.byteLen / 128 = lk.accumulator.itemCount) :
    l.flatMap (fun lk => List.replicate (lk.helpers.byteLen / 128) x ++
        List.replicate (lk.accumulator.byteLen / 128) x) =
      List.replicate (sumNat (l.map (fun lk =>
        lk.helpers.itemCount + lk.accumulator.itemCount))) x := by
  induction l with
  | nil => rfl
  | cons lk rest ih =>
      rw [List.flatMap_cons, List.map_cons, sumNat_cons]
      have h0 := h lk (by simp)
      rw [h0.1, h0.2, ih (fun x hx => h x (by simp [hx]))]
      simp only [List.replicate_append_replicate]

/-- The sum of the per-lookup `[helpers, accumulator]` pair list. -/
theorem sumNat_flatMap_pair (l : List ProofLookupCommitmentsLayout) :
    sumNat (l.flatMap (fun lk => [lk.helpers.itemCount, lk.accumulator.itemCount])) =
      sumNat (l.map (fun lk => lk.helpers.itemCount + lk.accumulator.itemCount)) := by
  induction l with
  | nil => rfl
  | cons lk rest ih =>
      rw [List.flatMap_cons, List.map_cons, sumNat_append, ih]
      have hpair : sumNat [lk.helpers.itemCount, lk.accumulator.itemCount] =
          lk.helpers.itemCount + lk.accumulator.itemCount := by
        rw [sumNat_cons, sumNat_cons, sumNat_nil]
        omega
      rw [hpair, sumNat_cons]

/-- The sum of the trash group, present or absent. -/
theorem sumNat_trash_if (g : List Nat) (n : Nat) :
    sumNat (if n != 0 then g ++ [n] else g) = sumNat g + n := by
  by_cases h : n = 0
  · subst h
    simp [sumNat_append, sumNat_cons, sumNat_nil]
  · have h' : (n != 0) = true := by simp [h]
    simp [h', sumNat_append, sumNat_cons, sumNat_nil]

/-- The sum of a guarded cons. -/
theorem sumNat_cons_guard (n : Nat) (l : List Nat) :
    sumNat (if n != 0 then n :: l else l) = n + sumNat l := by
  by_cases h : n = 0
  · subst h
    simp [sumNat_nil]
  · have h' : (n != 0) = true := by simp [h]
    simp [h', sumNat_cons]

/-- The sum of the one-element trash group. -/
theorem sumNat_guard_singleton (n : Nat) :
    sumNat (if n != 0 then [n] else []) = n := by
  by_cases h : n = 0
  · subst h
    simp [sumNat_nil]
  · have h' : (n != 0) = true := by simp [h]
    simp [h', sumNat_cons, sumNat_nil]

/-! ## 5. THE NAMED LEAVES -/

/-- Grouping two adjacent `replicate`s under an associative tail. -/
theorem replicate_append_replicate_assoc {α : Type} (n m : Nat) (a : α) (l : List α) :
    List.replicate n a ++ (List.replicate m a ++ l) = List.replicate (n + m) a ++ l := by
  rw [← List.append_assoc, List.replicate_append_replicate]

/-- The per-lookup helper walk, folded: when each accumulator section is one 128-byte frame, the
    explicit `[g1]` after the helper walk is `replicate (accumulator.byteLen / 128) g1`. -/
theorem flatMap_lookup_replicate (l : List ProofLookupCommitmentsLayout)
    (hAcc : ∀ lk, lk ∈ l → lk.accumulator.byteLen / 128 = 1) :
    l.flatMap (fun lk => List.replicate (lk.helpers.byteLen / 128) WireSlot.g1 ++ [WireSlot.g1]) =
      l.flatMap (fun lk => List.replicate (lk.helpers.byteLen / 128) WireSlot.g1 ++
        List.replicate (lk.accumulator.byteLen / 128) WireSlot.g1) := by
  induction l with
  | nil => rfl
  | cons lk rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, hAcc lk (by simp),
        ih (fun x hx => hAcc x (by simp [hx]))]
      simp

/-- **THE SCHEDULE'S SLOT LIST, SEGMENT BY SEGMENT.** Unfolds `tpEvents` and applies the
    `slot?` filter to each segment: the words, zeros, instances, squeezes, mask and
    `saveCptr` contribute nothing, the g1 walks contribute `replicate (byteLen / 128) g1`,
    the scalars `replicate (byteLen / 32) fr`, and the two absorb-copy sites one `g1` each.
    PROVED by reduction and the four `List.filterMap_*` lemmas. -/
theorem tpEvents_filterMap_eq (numInstances : Nat) (userPhases : List UserPhase)
    (numLookups numPermutationZs lookupHPlusAcc numTrashcans : Nat)
    (truncatedChallenges : Bool) (L : ProofCalldataLayout)
    (hAcc : ∀ lk, lk ∈ L.lookups → lk.accumulator.byteLen / 128 = 1) :
    (tpEvents numInstances userPhases numLookups numPermutationZs lookupHPlusAcc numTrashcans
      truncatedChallenges L).filterMap TEv.slot? =
      (userPhases.flatMap fun ph =>
        List.replicate (ph.adviceBytes / 128) WireSlot.g1) ++
      (if numLookups != 0 then
        List.replicate (L.lookupMultiplicities.byteLen / 128) WireSlot.g1 else []) ++
      (if numPermutationZs != 0 then
        List.replicate (L.permutationProducts.byteLen / 128) WireSlot.g1 else []) ++
      (if lookupHPlusAcc != 0 then
        L.lookups.flatMap fun lk =>
          List.replicate (lk.helpers.byteLen / 128) WireSlot.g1 ++
            List.replicate (lk.accumulator.byteLen / 128) WireSlot.g1 else []) ++
      (if numTrashcans != 0 then
        List.replicate (L.trash.byteLen / 128) WireSlot.g1 else []) ++
      List.replicate (L.quotientLimbs.byteLen / 128) WireSlot.g1 ++
      List.replicate (L.evals.byteLen / 32) WireSlot.fr ++ [WireSlot.g1] ++
      List.replicate (L.qEvals.byteLen / 32) WireSlot.fr ++ [WireSlot.g1] := by
  have hlook := flatMap_lookup_replicate L.lookups hAcc
  by_cases h1 : numLookups != 0 <;> by_cases h2 : numPermutationZs != 0 <;>
    by_cases h3 : lookupHPlusAcc != 0 <;> by_cases h4 : numTrashcans != 0 <;>
    by_cases h5 : truncatedChallenges
  all_goals
    simp [tpEvents, tpWalk, h1, h2, h3, h4, h5, hlook, List.filterMap_flatMap,
      List.filterMap_map, List.filterMap_replicate, List.filterMap_eq_nil_iff,
      filterMap_squeeze_eq_nil, replicate_append_replicate_assoc]
  all_goals omega

/-- **THE READ SCHEDULE IS THE LAYOUT'S SLOT LIST.** The parser reads, in order, exactly the slots
    `rawSlots` walks. LEAF ROW.TP.6 (ALG, list induction, no Yul). Evidence :706-715, statement
    verbatim with `R.Valid` -> `ValidV3 R`.

    **PROVED.** PG-PARSER is not a gap: `tp_planFacts` (the plan's meta and layout are the
    generator's and the model's parser facts are computed from them), `tp_fromProtocol` (every
    section's count, width and byte length), `userPhasesOf_advice` (the phase table index for
    index), the `fromConstraintSystem`/`remapping` phase-length projection
    (`fromConstraintSystem_phase_lengths`, `ConstraintSystemMeta.new_phase_lengths`), and the
    schedule algebra (`tpEvents_filterMap_eq`, `flatMap_advice_replicate`,
    `flatMap_lookups_byteLen`, `sumNat_filter_ne_zero`, `sumNat_trash_if`, the guard lemmas).
    The F1 witness/falsifier pair is `tp_events_slots_witness_nonempty` /
    `tp_events_slots_falsifier_not_every_event_reads_a_slot` (section 5 below). -/
theorem tp_events_slots (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.tpEvents.filterMap TEv.slot? =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots := by
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hL, hc1, hc2, hc3, hc4, hc5, hc6,
    hc7, hc8, hup, huser, hnInst, htrunc, hnLook, hnPerm, hnTrash, hLH⟩ := tp_planFacts hR
  have hfacts := tp_fromProtocol hL
  have hupAdv := userPhasesOf_advice meta_ L hup
  have hnewProtocol := ConstraintSystemMeta.new_protocol_fields Features.solidity R.vk.cs
    R.cfg.numCommittedInstances hraw
  have hnewLook := ConstraintSystemMeta.new_numLookups Features.solidity R.vk.cs
    R.cfg.numCommittedInstances hraw
  have hnewLen := ConstraintSystemMeta.new_phase_lengths Features.solidity R.vk.cs
    R.cfg.numCommittedInstances hraw
  have hmetaLen : meta_.numUserAdvices.length = meta_.numUserChallenges.length := by
    rw [hc7, hc8]
    exact hnewLen
  have hrawProtoLen :
      rawMeta.protocol.numUserAdvices.length = rawMeta.protocol.numUserChallenges.length := by
    rw [← hnewProtocol.2.2.2.2.1, ← hnewProtocol.2.2.2.2.2.1]
    exact hnewLen
  have hlenChallenges : meta_.numUserChallenges.length = meta_.protocol.numUserAdvices.length := by
    rw [hc8, hnewProtocol.2.2.2.2.2.1, hc1]
    exact hrawProtoLen.symm
  have hupsLen : userPhases.length = L.advicePhases.length := by
    rw [hupAdv.1, List.length_zip, hmetaLen, hlenChallenges, ← hfacts.adviceLen,
      Nat.min_self]
  -- the schedule's guards agree with the section counts
  have hmetaLook : meta_.numLookups = meta_.protocol.numLookups := by
    rw [hc2, hnewProtocol.1, hc1]
  have hmetaPerm : meta_.numPermutationZs = meta_.protocol.numPermutationZs := by
    rw [hc4, hnewProtocol.2.2.1, hc1]
  have hmetaTrash : meta_.numTrashcans = meta_.protocol.numTrashcans := by
    rw [hc5, hnewProtocol.2.2.2.1, hc1]
  have hGuardLM : meta_.numLookups = L.lookupMultiplicities.itemCount := by
    rw [hmetaLook, ← hfacts.lookupM]
  have hGuardPerm : meta_.numPermutationZs = L.permutationProducts.itemCount := by
    rw [hmetaPerm, ← hfacts.permZ]
  have hGuardTrash : meta_.numTrashcans = L.trash.itemCount := by
    rw [hmetaTrash, ← hfacts.trash]
  -- the section widths
  have hLMdiv : L.lookupMultiplicities.byteLen / 128 = L.lookupMultiplicities.itemCount := by
    rw [hfacts.lookupMByte, generator_g1Bytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 128), ← hfacts.lookupM]
  have hPermDiv : L.permutationProducts.byteLen / 128 =
      L.permutationProducts.itemCount := by
    rw [hfacts.permZByte, generator_g1Bytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 128), ← hfacts.permZ]
  have hTrashDiv : L.trash.byteLen / 128 = L.trash.itemCount := by
    rw [hfacts.trashByte, generator_g1Bytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 128), ← hfacts.trash]
  have hQuotDiv : L.quotientLimbs.byteLen / 128 = L.quotientLimbs.itemCount := by
    rw [hfacts.quotientByte, generator_g1Bytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 128), ← hfacts.quotient]
  have hEvalsDiv : L.evals.byteLen / 32 = L.evals.itemCount := by
    rw [hfacts.evalsByte, generator_wordBytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 32), ← hfacts.evals]
  have hQEvalsDiv : L.qEvals.byteLen / 32 = L.qEvals.itemCount := by
    rw [hfacts.qEvalsByte, generator_wordBytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 32), ← hfacts.qEvals]
  have hAdvDiv : ∀ s, s ∈ L.advicePhases → s.byteLen / 128 = s.itemCount := by
    intro s hs
    rw [hfacts.adviceByteLen s hs, generator_g1Bytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 128)]
  have hHelpDiv : ∀ lk, lk ∈ L.lookups →
      lk.helpers.byteLen / 128 = lk.helpers.itemCount := by
    intro lk hlk
    rw [(hfacts.lookupsByte lk hlk).2.1, generator_g1Bytes_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 128)]
  have hAccDiv : ∀ lk, lk ∈ L.lookups →
      lk.accumulator.byteLen / 128 = lk.accumulator.itemCount := by
    intro lk hlk
    rw [(hfacts.lookupsByte lk hlk).2.2.2, hfacts.lookupsAcc lk hlk,
      generator_g1Bytes_eq]
  have hAccOne : ∀ lk, lk ∈ L.lookups → lk.accumulator.byteLen / 128 = 1 := by
    intro lk hlk
    rw [hAccDiv lk hlk, hfacts.lookupsAcc lk hlk]
  -- the lookup guard is false only on the empty lookup list
  have hmetaLookLen : meta_.numLookups = meta_.lookupChunks.length := by
    rw [hc2, hc3]
    exact hnewLook
  have hGuardLook : lookupHPlusAccOf meta_ ≠ 0 ∨ L.lookups = [] := by
    by_cases h0 : lookupHPlusAccOf meta_ = 0
    · right
      have hsum : meta_.lookupChunks.foldl (fun a b => a + b) 0 + meta_.numLookups = 0 := h0
      have hnum : meta_.numLookups = 0 := by omega
      have hnumRaw : rawMeta.numLookups = 0 := by rw [← hc2]; exact hnum
      have hchunksRaw : rawMeta.lookupChunks = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← hnewLook]
        exact hnumRaw
      have hlkLen : L.lookups.length = 0 := by
        rw [hfacts.lookupsLen, hc1, ← hnewProtocol.2.1, hchunksRaw]
        rfl
      exact List.eq_nil_of_length_eq_zero hlkLen
    · left
      exact h0
  -- the goal, rewritten to the schedule form
  rw [Render.tpEvents]
  simp only [Render.pv, planViewOf, planViewWithAccumulator, parserFactsOfPlan,
    PlanView.numLookups, PlanView.numPermutationZs, PlanView.numTrashcans,
    huser, hnInst, hnLook, hnPerm, hnTrash, htrunc, hLH, hmeta, hlay]
  rw [tpEvents_filterMap_eq _ _ _ _ _ _ _ _ hAccOne]
  rw [flatMap_advice_replicate userPhases L.advicePhases hupsLen (by
    intro i ph s hp hs
    exact ⟨hupAdv.2 i ph s hp hs, hfacts.adviceByteLen s (List.mem_of_getElem? hs)⟩)]
  rw [hLMdiv, hPermDiv, hTrashDiv, hQuotDiv, hEvalsDiv, hQEvalsDiv]
  rw [flatMap_lookups_byteLen L.lookups WireSlot.g1
    (fun lk hlk => ⟨hHelpDiv lk hlk, hAccDiv lk hlk⟩)]
  rw [hGuardLM, hGuardPerm, hGuardTrash]
  rw [tp_guard_replicate, tp_guard_replicate, tp_guard_replicate]
  rw [tp_guard_replicate_of_empty _ _ _ _ hGuardLook]
  -- the RHS: the slot list and its group sums
  rw [Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout,
    Midfall.Generator.RepackedProofLayoutPlan.slots,
    Midfall.Generator.RepackedProofLayoutPlan.prefixG1Count]
  rw [show (ProofCalldataLayout.commitmentReadGroups L).foldl (fun acc n => acc + n) 0 =
      sumNat (ProofCalldataLayout.commitmentReadGroups L) from rfl]
  simp only [ProofCalldataLayout.commitmentReadGroups, sumNat_filter_ne_zero,
    sumNat_append, sumNat_cons, sumNat_nil, sumNat_flatMap_pair, sumNat_guard_singleton,
    sumNat_trash_if, sumNat_cons_guard, List.filter_append, List.filter_cons, List.filter_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, List.cons_append, List.map_append, List.map_cons, List.map_nil,
    List.replicate_append_replicate, List.append_cancel_right_eq, List.replicate_inj]
  constructor
  · omega
  · right
    trivial

set_option maxRecDepth 100000 in
/-- **THE ENVELOPE'S CALldata SIZE.** `envelopeOk` pins `cd.size = proofEnd + 32 +
    32*numInstances` (`Stage.lean:91-95`), which is the length the proof-wire slices live
    in; `StageInv .vk` carries it as `LeanRaw .vk`. -/
theorem cdSize_of_envelope (L : Midfall.Generator.ProofCalldataLayout) (numInstances : Nat)
    (cd : Bytes) (h : Midfall.Lowering.Stage.envelopeOk L numInstances cd = true) :
    cd.data.toList.length = L.proofEnd + 32 + 32 * numInstances := by
  unfold Midfall.Lowering.Stage.envelopeOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, hsz⟩ := h
  have := beq_iff_eq.mp hsz
  rw [← this]
  simp

/-- **THE PROOF-WIRE LENGTH, FROM THE ENVELOPE.** Every 128-byte proof-wire frame ending
    inside `proofEnd` is inside the calldata, so `calldatacopy`'s window is the exact
    `cdSlice` (not a zero-padded one). This is the premise the `common_uncompressed_g1`
    contract needs on its normal path; no new clause. -/
theorem cdSlice_length_of_envelope (L : Midfall.Generator.ProofCalldataLayout)
    (numInstances : Nat) (cd : Bytes)
    (h : Midfall.Lowering.Stage.envelopeOk L numInstances cd = true)
    (cptr : Nat) (hsec : cptr + 128 ≤ L.proofEnd) :
    cptr + 128 ≤ cd.data.toList.length := by
  rw [cdSize_of_envelope L numInstances cd h]
  omega

/-- **THE `calldatacopy` WINDOW IS THE CALLDATA SLICE.** `calldatacopy(dst, src, n)`
    writes exactly `cdSlice cd src n` when the source window is inside the calldata
    (`src + n ≤ cd.size`); past the end it zero-pads, which is why the normal path of
    `common_uncompressed_g1` carries that length bound (from the envelope / the walk's
    `a + 128*j ≤ cd.size`, not a new clause). -/
theorem bytesAt_calldatacopy_cdSlice (st : EvmState) (cd : Bytes) (dst src n : Nat)
    (hcd : st.env.calldata = cd.data.toList)
    (hlen : src + n ≤ cd.data.toList.length) :
    bytesAt { touchMemory st dst n with
        memory := copyInto st.memory dst src n st.env.calldata } dst n
      = cdSlice cd src n := by
  unfold bytesAt cdSlice
  rw [hcd]
  show ByteArray.mk (readBytes (copyInto st.memory dst src n cd.data.toList) dst n).toArray
      = ByteArray.mk ((cd.data.toList.drop src).take n).toArray
  rw [Midfall.LoweringV3.VkWindow.readBytes_copyInto_window st.memory dst src n dst n cd.data.toList
    (Nat.le_refl _) (by omega) (by omega : src + (dst - dst) + n ≤ cd.data.toList.length)]
  congr 1
  rw [show src + (dst - dst) = src from by omega]

/-- **A MEMORY WINDOW SPLITS AT AN ADJACENT OFFSET.** `bytesAt` is a `readBytes`, so a window of
    `n + m` bytes is the `n`-byte window followed by the `m`-byte window at `a + n`. -/
theorem bytesAt_append (st : EvmState) (a n m : Nat) :
    bytesAt st a (n + m) = bytesAt st a n ++ bytesAt st (a + n) m := by
  unfold bytesAt
  rw [Midfall.LoweringV2.Blocks.EcPairing.readBytes_append]
  apply ByteArray.ext
  simp

/-- **A CALLDATA SLICE SPLITS AT AN ADJACENT OFFSET.** Same split for `cdSlice` (`drop`/`take`). -/
theorem cdSlice_append (cd : Bytes) (a n m : Nat) :
    cdSlice cd a (n + m) = cdSlice cd a n ++ cdSlice cd (a + n) m := by
  unfold cdSlice
  rw [List.take_add, List.drop_drop]
  apply ByteArray.ext
  simp

theorem cdSlice_eq_of_bytesTake {cd b : Bytes} {a n : Nat}
    (h : bytesTake cd a n = some b) : cdSlice cd a n = b := by
  unfold bytesTake at h
  split at h
  · rename_i hle
    injection h with hb
    subst hb
    unfold cdSlice
    apply ByteArray.ext
    apply Array.toList_inj.mp
    show (ByteArray.mk ((cd.data.toList.drop a).take n).toArray).data.toList
      = (ByteArray.mk (cd.data.extract a (a + n))).data.toList
    rw [Array.toList_extract, List.extract_eq_take_drop,
      show a + n - a = n by omega]
  · cases h

end Midfall.LoweringV3.TranscriptRows

namespace Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem holdsG1_of_mirrorsSection (E : VerifierEnv p G₁ G₂ Gₜ) {st : EvmState} {cd : Bytes}
    {a : Nat} {s : Midfall.Generator.ProofSection} {Q : G₁}
    (hm : mirrorsSection st a cd s) (hlen : s.byteLen = g1EipWidth)
    {b : Bytes} (hb : bytesTake cd s.start g1EipWidth = some b)
    (hq : E.g1.ofEip? b = some Q) (hc : E.g1.eipRoundtrip) :
    holdsG1 E st a Q = true := by
  unfold holdsG1
  have hlen' : s.byteLen = 128 := by simpa [g1EipWidth] using hlen
  have hb' : bytesTake cd s.start 128 = some b := by simpa [g1EipWidth] using hb
  have hm' : bytesAt st a 128 = cdSlice cd s.start 128 := by
    simpa [mirrorsSection, hlen'] using hm
  have hbytes : bytesAt st a 128 = E.g1.toEip Q := by
    rw [hm', cdSlice_eq_of_bytesTake hb']
    exact (hc b Q hq).symm
  rw [hbytes]
  exact beq_self_eq_true _

theorem bytesAt_size_local (st : EvmState) (a n : Nat) : (bytesAt st a n).size = n := by
  unfold bytesAt
  show (List.map (fun i => st.memory (a + i)) (List.range n)).toArray.size = n
  simp [List.size_toArray, List.length_map, List.length_range]

theorem cdSlice_size_of_le {cd : Bytes} {a n : Nat} (h : a + n ≤ cd.size) :
    (cdSlice cd a n).size = n := by
  unfold cdSlice
  show (List.take n (List.drop a cd.data.toList)).toArray.size = n
  simp [List.size_toArray, List.length_take, List.length_drop]
  omega

theorem bytesAt_frame_eq_of_window (st : EvmState) (cd : Bytes) (base start n : Nat)
    (h : bytesAt st base (g1EipWidth * n) = cdSlice cd start (g1EipWidth * n))
    (hcd : start + g1EipWidth * n ≤ cd.size) :
    ∀ i < n, bytesAt st (base + g1EipWidth * i) g1EipWidth =
      cdSlice cd (start + g1EipWidth * i) g1EipWidth := by
  induction n generalizing base start with
  | zero => intro i hi; omega
  | succ n ih =>
      have h128 : g1EipWidth * (n + 1) = g1EipWidth + g1EipWidth * n := by ring
      rw [h128] at h hcd
      have hsplit : bytesAt st base (g1EipWidth + g1EipWidth * n) =
          bytesAt st base g1EipWidth ++ bytesAt st (base + g1EipWidth) (g1EipWidth * n) :=
        bytesAt_append st base g1EipWidth (g1EipWidth * n)
      have hcdsplit : cdSlice cd start (g1EipWidth + g1EipWidth * n) =
          cdSlice cd start g1EipWidth ++
            cdSlice cd (start + g1EipWidth) (g1EipWidth * n) :=
        cdSlice_append cd start g1EipWidth (g1EipWidth * n)
      rw [hsplit, hcdsplit] at h
      have hstart : start + g1EipWidth ≤ cd.size := by omega
      have hX : bytesAt st base g1EipWidth = cdSlice cd start g1EipWidth :=
        bytes_prefix_cancel h (by rw [bytesAt_size_local, cdSlice_size_of_le hstart])
      have hY : bytesAt st (base + g1EipWidth) (g1EipWidth * n) =
          cdSlice cd (start + g1EipWidth) (g1EipWidth * n) := by
        rw [hX] at h
        exact bytes_append_cancel_left h
      have hcd' : start + g1EipWidth + g1EipWidth * n ≤ cd.size := by omega
      intro i hi
      cases i with
      | zero => simpa using hX
      | succ k =>
          have hk : k < n := by omega
          have := ih (base + g1EipWidth) (start + g1EipWidth) hY hcd' k hk
          simpa [show base + g1EipWidth * (k + 1) = base + g1EipWidth + g1EipWidth * k by ring,
            show start + g1EipWidth * (k + 1) = start + g1EipWidth + g1EipWidth * k by ring]
            using this

theorem holdsG1s_section (E : VerifierEnv p G₁ G₂ Gₜ) (st : EvmState) (cd : Bytes)
    (base start : Nat) (Qs : List G₁)
    (h : bytesAt st base (g1EipWidth * Qs.length) = cdSlice cd start (g1EipWidth * Qs.length))
    (hcd : start + g1EipWidth * Qs.length ≤ cd.size)
    (hprov : ∀ i (hi : i < Qs.length), ∃ b : Bytes,
      bytesTake cd (start + g1EipWidth * i) g1EipWidth = some b ∧
        E.g1.ofEip? b = some (Qs[i]'hi))
    (hc : E.g1.eipRoundtrip) :
    holdsG1s E st base Qs.toArray = true := by
  have hframes := bytesAt_frame_eq_of_window st cd base start Qs.length h hcd
  unfold holdsG1s
  rw [List.all_eq_true]
  intro pair hp
  obtain ⟨Q, i⟩ := pair
  have hmem : (Q, i) ∈ Qs.toArray.toList.zipIdx 0 := by
    simpa using hp
  have hinfo := List.mem_zipIdx hmem
  have hi : i < Qs.length := by
    simpa using hinfo.2.1
  have hQ : Q = Qs[i] := by simpa using hinfo.2.2
  subst hQ
  have hframe := hframes i hi
  obtain ⟨b, hb, hq⟩ := hprov i hi
  have hslice : cdSlice cd (start + g1EipWidth * i) g1EipWidth =
      E.g1.toEip (Qs[i]'hi) := by
    rw [cdSlice_eq_of_bytesTake hb]
    exact (hc b (Qs[i]'hi) hq).symm
  change (bytesAt st (base + g1EipWidth * i) g1EipWidth ==
    E.g1.toEip (Qs[i]'hi)) = true
  rw [hframe, hslice]
  exact beq_self_eq_true _

/-- **THE COORDINATE RANGE CHECK AS A `Nat` FACT.** `common_uncompressed_g1` writes
    its two coordinate checks as `iszero(or(lt(hi, BLS_P_HI), and(eq(hi, BLS_P_HI),
    iszero(gt(lo, BLS_P_MINUS_ONE_LO)))))`; at `BitVec 256` the *passing* check (the
    `iszero` value being zero) is this `b2w (decide (b2w or = 0)) = 0`, and it holds
    exactly when `hi.toNat < BLS_P_HI ∨ (hi.toNat = BLS_P_HI ∧ lo.toNat ≤
    BLS_P_MINUS_ONE_LO)`. -/
theorem coordCheck_to_nat (xh xl hi lo : U256) :
    (b2w (decide (b2w (xh.ult hi || ((xh == hi) && !(lo.ult xl))) = 0))) = (0 : U256) ↔
      (xh.toNat < hi.toNat ∨ (xh.toNat = hi.toNat ∧ xl.toNat ≤ lo.toNat)) := by
  rw [Midfall.Yul.WpTac.b2w_eq_zero_iff, decide_eq_false_iff_not,
    Midfall.Yul.WpTac.b2w_eq_zero_iff]
  have hiff : (¬((xh.ult hi || ((xh == hi) && !(lo.ult xl))) = false))
      ↔ (xh.ult hi || ((xh == hi) && !(lo.ult xl))) = true := by
    cases hb : (xh.ult hi || ((xh == hi) && !(lo.ult xl))) <;> simp
  rw [hiff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    BitVec.ult_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not, BitVec.toNat_eq]
  omega

set_option maxRecDepth 100000

theorem nat_lor_mul_two_pow (X b : Nat) (hb : b < 2 ^ 8) :
    X * 2 ^ 8 ||| b = X * 2 ^ 8 + b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
  by_cases hk : k < 8
  · have h8 : ¬ (8 ≤ k) := by omega
    have hsum : (X * 2 ^ 8 + b).testBit k = b.testBit k := by
      have hmod : (X * 2 ^ 8 + b) % 2 ^ 8 = b := by omega
      conv_rhs => rw [← hmod]
      rw [Nat.testBit_mod_two_pow]
      simp [hk]
    rw [hsum]
    simp [h8]
  · have h8 : 8 ≤ k := by omega
    have hk' : k = (k - 8) + 8 := by omega
    have hsum : (X * 2 ^ 8 + b).testBit k = X.testBit (k - 8) := by
      conv_lhs => rw [hk']
      rw [Nat.testBit_add]
      have hdiv : (X * 2 ^ 8 + b) / 2 ^ 8 = X := by omega
      rw [hdiv]
    have hb0 : b.testBit k = false := by
      conv_lhs => rw [hk']
      rw [Nat.testBit_add]
      have hdiv : b / 2 ^ 8 = 0 := by omega
      rw [hdiv, Nat.zero_testBit]
    rw [hsum, hb0]
    simp [h8]

theorem bv_shift_or_step (X b : Nat) (hX : X < 2 ^ 248) (hb : b < 256) :
    (BitVec.ofNat 256 X <<< 8) ||| BitVec.ofNat 256 b = BitVec.ofNat 256 (X * 256 + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hXmod : X % 2 ^ 256 = X := Nat.mod_eq_of_lt (by omega)
  have hbmod : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (by omega)
  have hsh : X <<< 8 % 2 ^ 256 = X * 2 ^ 8 := by
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hsummod : (X * 256 + b) % 2 ^ 256 = X * 256 + b := by
    apply Nat.mod_eq_of_lt; omega
  rw [hXmod, hbmod, hsh, hsummod]
  exact nat_lor_mul_two_pow X b (by omega)


theorem foldl_shift_or_eq_gen (l : List Nat) (N X : Nat) (hN : N ≤ 32)
    (hlen : l.length ≤ N) (hb : ∀ b ∈ l, b < 256) (hX : X < 256 ^ (N - l.length)) :
    List.foldl (fun (acc : BitVec 256) (b : Nat) => (acc <<< 8) ||| BitVec.ofNat 256 b)
        (BitVec.ofNat 256 X) l
      = BitVec.ofNat 256
          (List.foldl (fun (acc : Nat) (b : Nat) => acc * 256 + b) X l) := by
  induction l generalizing N X with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons] at hX hlen
      have ha : a < 256 := hb a (by simp)
      have hbas : ∀ b ∈ as, b < 256 := fun b hbm => hb b (by simp [hbm])
      have hlen1 : as.length + 1 ≤ N := by simpa using hlen
      have hlen' : as.length ≤ N := by omega
      have hX248 : X < 2 ^ 248 := by
        have hle : N - (as.length + 1) ≤ 31 := by omega
        have h1 : (256 : Nat) ^ (N - (as.length + 1)) ≤ 256 ^ 31 :=
          Nat.pow_le_pow_right (by decide) hle
        have h2 : (256 : Nat) ^ 31 = 2 ^ 248 := by norm_num
        omega
      rw [List.foldl_cons, bv_shift_or_step X a hX248 ha]
      refine ih N (X * 256 + a) hN hlen' hbas ?_
      have hm : N - as.length = (N - (as.length + 1)) + 1 := by omega
      have hpows : (256 : Nat) ^ (N - as.length) = 256 ^ (N - (as.length + 1)) * 256 := by
        rw [hm, Nat.pow_succ]
      have hXle : X + 1 ≤ 256 ^ (N - (as.length + 1)) := by omega
      have hmult : (X + 1) * 256 ≤ 256 ^ (N - (as.length + 1)) * 256 :=
        Nat.mul_le_mul_right _ hXle
      have ha' : a ≤ 255 := by omega
      nlinarith

theorem wordFrom_eq_cdWord (cd : Bytes) (p : Nat) :
    wordFrom cd.data.toList p = cdWord cd p := by
  have hbyte : ∀ i, (byteFrom cd.data.toList i).toNat
      = ((cd.data.toList.drop i).head?.map UInt8.toNat).getD 0 := by
    intro i
    unfold byteFrom
    rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
    cases (cd.data.toList.drop i).head? <;> rfl
  show (List.range 32).foldl (fun (acc : BitVec 256) (i : Nat) =>
      (acc <<< 8) ||| BitVec.ofNat 256 (byteFrom cd.data.toList (p + i)).toNat) (0 : BitVec 256)
    = BitVec.ofNat 256 (List.foldl (fun (acc : Nat) (j : Nat) =>
        acc * 256 + (Option.map UInt8.toNat (List.drop (p + j) cd.data.toList).head?).getD 0)
        0 (List.range 32))
  rw [← List.foldl_map (f := fun i => (byteFrom cd.data.toList (p + i)).toNat)
    (g := fun (acc : BitVec 256) (b : Nat) => (acc <<< 8) ||| BitVec.ofNat 256 b)]
  change List.foldl (fun (acc : BitVec 256) (b : Nat) => (acc <<< 8) ||| BitVec.ofNat 256 b)
      (BitVec.ofNat 256 0) (List.map (fun i => (byteFrom cd.data.toList (p + i)).toNat) (List.range 32))
    = _
  rw [foldl_shift_or_eq_gen ((List.range 32).map (fun i => (byteFrom cd.data.toList (p + i)).toNat))
    32 0 (by decide) (by simp)
    (by intro b hb; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb; exact UInt8.toNat_lt _)
    (by norm_num)]
  congr 1
  have hcongr : ∀ (l : List Nat) (i : Nat),
      l.foldl (fun acc j => acc * 256 + (byteFrom cd.data.toList (p + j)).toNat) i
        = l.foldl (fun acc j =>
            acc * 256 + (Option.map UInt8.toNat (List.drop (p + j) cd.data.toList).head?).getD 0) i := by
    intro l
    induction l with
    | nil => intro i; rfl
    | cons a as ih =>
        intro i
        rw [List.foldl_cons, List.foldl_cons, hbyte (p + a), ih]
  exact hcongr (List.range 32) 0

/-- **THE WALK'S RANGE CHECK, PURE.** A coordinate whose high word is below `2^128`
    and whose `(hi, lo)` split passes `common_uncompressed_g1`'s range check is
    below `pBase`: `hi * 2^256 + lo + 1 = pBase` (the contract's `BLS_P_HI |
    BLS_P_MINUS_ONE_LO` split) and `lo` is a proper 256-bit residue. This is the
    arithmetic `g1WordsOk` needs from the helper's two `shr 128` guards and two
    coordinate checks; it takes the `(hi, lo)` split as a hypothesis so no numeral
    is computed here. -/
theorem coordLt_pBase (xh xl hi lo : Nat) (hxlw : xl < 2 ^ 256)
    (hkey : hi * 2 ^ 256 + lo + 1 = Midfall.Assumptions.pBase)
    (hx : xh < hi ∨ (xh = hi ∧ xl ≤ lo)) :
    xh * 2 ^ 256 + xl < Midfall.Assumptions.pBase := by
  rcases hx with hx | ⟨hx, hxl⟩ <;> omega

set_option maxRecDepth 100000 in
/-- **`g1WordsOk` FROM THE HELPER'S GUARDS.** The four calldata words, the two
    high-word fits and the two `(hi, lo)` range checks imply the `g1WordsOk` gate
    `common_uncompressed_g1` enforces. `cdWord` is the four-word read; the caller
    supplies the words and the split identity. -/
theorem g1WordsOk_of_checks (cd : Bytes) (cptr : Nat) (xh xl yh yl hi lo : Nat)
    (h1 : (cdWord cd cptr).toNat = xh) (h2 : (cdWord cd (cptr + 32)).toNat = xl)
    (h3 : (cdWord cd (cptr + 64)).toNat = yh) (h4 : (cdWord cd (cptr + 96)).toNat = yl)
    (hxh : xh < 2 ^ 128) (hyh : yh < 2 ^ 128)
    (hxlw : xl < 2 ^ 256) (hylw : yl < 2 ^ 256)
    (hkey : hi * 2 ^ 256 + lo + 1 = Midfall.Assumptions.pBase)
    (hx : xh < hi ∨ (xh = hi ∧ xl ≤ lo))
    (hy : yh < hi ∨ (yh = hi ∧ yl ≤ lo)) :
    g1WordsOk cd cptr = true := by
  have hxp := coordLt_pBase xh xl hi lo hxlw hkey hx
  have hyp := coordLt_pBase yh yl hi lo hylw hkey hy
  unfold g1WordsOk
  dsimp only
  rw [h1, h2, h3, h4]
  all_goals
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hxh, hyh⟩, hxp⟩, hyp⟩

set_option maxRecDepth 100000

def commonG1Inline (err hi lo : Nat) : Block EVM.Op :=
  [ ylet "x_hi_word" (yop EVM.Op.calldataload [yvar "cptr"])
  , ylet "x_lo" (yop EVM.Op.calldataload [yop EVM.Op.add [yvar "cptr", ylit 0x20]])
  , ylet "y_hi_word" (yop EVM.Op.calldataload [yop EVM.Op.add [yvar "cptr", ylit 0x40]])
  , ylet "y_lo" (yop EVM.Op.calldataload [yop EVM.Op.add [yvar "cptr", ylit 0x60]])
  , yif (yop EVM.Op.shr [ylit 128, yvar "x_hi_word"]) [yexpr (ycall "fail" [ylit err])]
  , yif (yop EVM.Op.shr [ylit 128, yvar "y_hi_word"]) [yexpr (ycall "fail" [ylit err])]
  , ylet "x_hi" (yop EVM.Op.and [yvar "x_hi_word", ylit 0xffffffffffffffffffffffffffffffff])
  , ylet "y_hi" (yop EVM.Op.and [yvar "y_hi_word", ylit 0xffffffffffffffffffffffffffffffff])
  , yif (yop EVM.Op.iszero [yop EVM.Op.or
      [ yop EVM.Op.lt [yvar "x_hi", ylit hi]
      , yop EVM.Op.and [yop EVM.Op.eq [yvar "x_hi", ylit hi],
          yop EVM.Op.iszero [yop EVM.Op.gt [yvar "x_lo", ylit lo]]] ]])
      [yexpr (ycall "fail" [ylit err])]
  , yif (yop EVM.Op.iszero [yop EVM.Op.or
      [ yop EVM.Op.lt [yvar "y_hi", ylit hi]
      , yop EVM.Op.and [yop EVM.Op.eq [yvar "y_hi", ylit hi],
          yop EVM.Op.iszero [yop EVM.Op.gt [yvar "y_lo", ylit lo]]] ]])
      [yexpr (ycall "fail" [ylit err])]
  , yexpr (yop EVM.Op.calldatacopy [yvar "buf_len", yvar "cptr", ylit 0x80])
  , yset "ret" (yop EVM.Op.add [yvar "buf_len", ylit 0x80]) ]

theorem commonG1_inline (consts : Inline.Consts) (err hi lo : Nat)
    (he : consts.lookup "ERR_BAD_POINT_ENCODING" = some err)
    (hh : consts.lookup "BLS_P_HI" = some hi)
    (hl : consts.lookup "BLS_P_MINUS_ONE_LO" = some lo) :
    Inline.inlineContractConstants consts GenAst.emitCommonUncompressedG1 =
      [Stmt.funDef "common_uncompressed_g1" ["buf_len", "cptr"] ["ret"]
        (commonG1Inline err hi lo)] := by
  rw [show Inline.inlineContractConstants consts GenAst.emitCommonUncompressedG1 =
      (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
        GenAst.emitCommonUncompressedG1).blks from rfl]
  simp only [GenAst.emitCommonUncompressedG1, commonG1Inline, GenAst.ylet, GenAst.ylit,
    GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.yset, GenAst.yif, GenAst.yfun, GenAst.ycall,
    GenAst.g1CoordRangeCheck,
    Inline.inlineStep, Inline.exprFuel, Inline.shadowed, Inline.boundOf, List.foldl_cons, List.foldl_nil, List.append_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_5,
    Inline.inlineStmtStep.eq_4, Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_5,
    he, hh, hl, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 63 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 62 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons, List.foldl_nil, List.append_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
    Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_5, Inline.inlineStmtStep.eq_4,
    Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_5,
    he, hh, hl, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 62 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 61 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons,
    List.foldl_nil, List.nil_append, List.append_nil, List.singleton_append,
    List.cons_append, Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    he, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 62 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 61 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons,
    List.foldl_nil, List.nil_append, List.append_nil, List.singleton_append,
    List.cons_append, Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    he, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]

section CommonG1InlineRuns

open Midfall.Yul.WpTac Midfall.Yul.VKP Midfall.LoweringV2.Blocks Midfall.Yul.Word

/-- A 256-bit right shift by 128 is zero exactly when the word fits in 128 bits. -/
theorem ushr128_eq_zero_iff (x : U256) : x >>> 128 = (0 : U256) ↔ x.toNat < 2 ^ 128 := by
  constructor
  · intro h
    have h2 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.zero_mod] at h2
    rcases Nat.div_eq_zero_iff.mp h2 with hz | hlt
    · exact absurd hz (by norm_num)
    · exact hlt
  · intro h
    rw [BitVec.toNat_eq]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
    rfl

/-- Masking with the low 128 bits is the identity on a word below `2^128`. -/
theorem and_mask128_eq_self (x : U256) (h : x.toNat < 2 ^ 128) :
    x &&& BitVec.ofNat 256 (2 ^ 128 - 1) = x := by
  rw [BitVec.toNat_eq]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by norm_num : 2 ^ 128 - 1 < 2 ^ 256)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow h

/-- Pointer-plus-literal at the word level: `(p + ofNat k).toNat = p.toNat + k` below the wrap. -/
theorem toNat_add_ofNat (p : U256) (k : Nat) (hk : p.toNat + k < 2 ^ 256) :
    (p + BitVec.ofNat 256 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 256), Nat.mod_eq_of_lt hk]

/-- The `iszero(or(lt, and(eq, iszero(gt))))` guard in the exact redex form the wp engine
    leaves it in equals the `b2w`-Bool form `coordCheck_to_nat` reads. -/
theorem guard_bridge {xh xl hi lo : U256} :
    (fun a => b2w (decide (a = 0)))
      ((fun x1 x2 => x1 ||| x2)
        ((fun a b => b2w (BitVec.ult a b)) xh hi)
        ((fun x1 x2 => x1 &&& x2)
          ((fun a b => b2w (decide (a = b))) xh hi)
          ((fun a => b2w (decide (a = 0)))
            ((fun a b => b2w (BitVec.ult b a)) xl lo))))
    = b2w (decide (b2w (xh.ult hi || ((xh == hi) && !(lo.ult xl))) = 0)) := by
  have hnot : decide (b2w (lo.ult xl) = 0) = !(lo.ult xl) := by
    cases lo.ult xl <;> rfl
  have hbeq : decide (xh = hi) = (xh == hi) := by
    rw [show (xh == hi) = decide (xh = hi) from rfl]
  dsimp only
  simp only [b2w_and_b2w, b2w_or_b2w, hnot, hbeq]

/-- The coordinate range check as the word the helper's `if` tests. -/
def coordGuard (xh xl hi lo : U256) : U256 :=
  b2w (decide (b2w (xh.ult hi || ((xh == hi) && !(lo.ult xl))) = 0))

/-- The coordinate-check guard at `(hi, lo)`, lifted from the 256-bit literals back to the
    `Nat` split the range-check arithmetic uses. -/
theorem coordCheck_lift (xh xl : U256) (hi lo : Nat) :
    (xh.toNat < (BitVec.ofNat 256 hi).toNat ∨
        (xh.toNat = (BitVec.ofNat 256 hi).toNat ∧ xl.toNat ≤ (BitVec.ofNat 256 lo).toNat)) →
      (xh.toNat < hi ∨ (xh.toNat = hi ∧ xl.toNat ≤ lo)) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  intro h
  rcases h with h | ⟨h1, h2⟩
  · rcases Nat.lt_or_ge hi (2 ^ 256) with hlt | hge
    · exact Or.inl (by rwa [Nat.mod_eq_of_lt hlt] at h)
    · have hmod : hi % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by norm_num)
      exact Or.inl (by omega)
  · rcases Nat.lt_or_ge hi (2 ^ 256) with hlt | hge
    · have hhi : hi % 2 ^ 256 = hi := Nat.mod_eq_of_lt hlt
      have hlo : lo % 2 ^ 256 ≤ lo := Nat.mod_le _ _
      rw [hhi] at h1
      exact Or.inr ⟨h1, by omega⟩
    · have hmod : hi % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by norm_num)
      exact Or.inl (by omega)

set_option maxRecDepth 100000 in
/-- **THE `common_uncompressed_g1` HELPER'S RUN CONTRACT.** Every run of the inlined helper
    body, from the CALLEE environment `params ++ [ret := 0]`, either halts reverted or exits
    normally having returned `buf_len + 128`, copied the 128-byte calldata frame to `buf_len`,
    passed the `g1WordsOk` range gate, and left `env`/`halted`/memory outside the frame alone.
    The `(hi, lo)` split identity is the caller's `hkey`; `cd.size < 2^256` keeps the helper's
    word-pointer additions from wrapping. -/
theorem commonG1Inline_runs {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState) (cd : Bytes)
    (buf cptr : U256) (err hi lo : Nat)
    (hfail : ∃ cenv, lookupFun funs "fail" = some (TraceReturn.failFDecl, cenv))
    (hcd : st.env.calldata = cd.data.toList)
    (hlen : cptr.toNat + 128 ≤ cd.data.toList.length)
    (hcdsize : cd.size < 2 ^ 256)
    (hkey : hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase) :
    AllRuns funs [("buf_len", buf), ("cptr", cptr), ("ret", (0 : U256))] st
      (commonG1Inline err hi lo)
      (fun V' st' o => Hold (
        (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "ret" = some (buf + 128) ∧
          VEnv.get (restore [("buf_len", buf), ("cptr", cptr), ("ret", (0 : U256))] V')
            "ret" = some (buf + 128) ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧
          bytesAt st' buf.toNat 128 = cdSlice cd cptr.toNat 128 ∧
          (∀ x, (x < buf.toNat ∨ buf.toNat + 128 ≤ x) → st'.memory x = st.memory x) ∧
          g1WordsOk cd cptr.toNat = true))) := by
  obtain ⟨cenv, hc⟩ := hfail
  -- the calldata is shorter than a machine word, so the four pointer additions do not wrap
  have hlenLt : cd.data.toList.length < 2 ^ 256 := by
    have h : cd.data.toList.length = cd.size := by
      show cd.data.toList.length = cd.data.size
      exact Array.length_toList
    omega
  have h32 : cptr.toNat + 32 < 2 ^ 256 := by omega
  have h64 : cptr.toNat + 64 < 2 ^ 256 := by omega
  have h96 : cptr.toNat + 96 < 2 ^ 256 := by omega
  refine allRuns_of_wp_fail 100 ?_
  set_option wpLets false in
  wp_run
  -- the normal exit
  · rename_i hxshr hyshr hxcc hycc
    refine Hold.intro (Or.inr ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · show bytesAt { touchMemory st buf.toNat 128 with
          memory := copyInto st.memory buf.toNat cptr.toNat 128 st.env.calldata }
          buf.toNat 128 = cdSlice cd cptr.toNat 128
      rw [bytesAt_calldatacopy_cdSlice st cd buf.toNat cptr.toNat 128 hcd hlen]
    · intro x hx
      show copyInto st.memory buf.toNat cptr.toNat 128 st.env.calldata x = st.memory x
      simp only [copyInto]
      rw [if_neg]
      omega
    · -- the four helper words are the four calldata words
      have hword1 : (cdWord cd cptr.toNat).toNat
          = (wordFrom st.env.calldata (BitVec.toNat cptr)).toNat := by
        rw [hcd, wordFrom_eq_cdWord]
      have hword2 : (cdWord cd (cptr.toNat + 32)).toNat
          = (wordFrom st.env.calldata
              (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 32)))).toNat := by
        rw [hcd, wordFrom_eq_cdWord, litValue_number_nat, toNat_add_ofNat cptr 32 h32]
      have hword3 : (cdWord cd (cptr.toNat + 64)).toNat
          = (wordFrom st.env.calldata
              (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 64)))).toNat := by
        rw [hcd, wordFrom_eq_cdWord, litValue_number_nat, toNat_add_ofNat cptr 64 h64]
      have hword4 : (cdWord cd (cptr.toNat + 96)).toNat
          = (wordFrom st.env.calldata
              (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 96)))).toNat := by
        rw [hcd, wordFrom_eq_cdWord, litValue_number_nat, toNat_add_ofNat cptr 96 h96]
      -- the two high words fit in 128 bits (the `shr 128` guards)
      have hxh : (wordFrom st.env.calldata (BitVec.toNat cptr)).toNat < 2 ^ 128 :=
        ushr128_eq_zero_iff _ |>.mp hxshr
      have hyh : (wordFrom st.env.calldata
          (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 64)))).toNat
            < 2 ^ 128 :=
        ushr128_eq_zero_iff _ |>.mp hyshr
      -- masking the low 128 bits does not change a fitting word
      have hmaskX : (fun x1 x2 : U256 => x1 &&& x2) (wordFrom st.env.calldata (BitVec.toNat cptr))
          ((Bridge.Dialect c g).litValue
            (Literal.number 340282366920938463463374607431768211455))
          = wordFrom st.env.calldata (BitVec.toNat cptr) := by
        rw [show (Bridge.Dialect c g).litValue
          (Literal.number 340282366920938463463374607431768211455) =
            BitVec.ofNat 256 (2 ^ 128 - 1) from rfl]
        exact and_mask128_eq_self _ hxh
      have hmaskY : (fun x1 x2 : U256 => x1 &&& x2)
          (wordFrom st.env.calldata
            (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 64))))
          ((Bridge.Dialect c g).litValue
            (Literal.number 340282366920938463463374607431768211455))
          = wordFrom st.env.calldata
              (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 64))) := by
        rw [show (Bridge.Dialect c g).litValue
          (Literal.number 340282366920938463463374607431768211455) =
            BitVec.ofNat 256 (2 ^ 128 - 1) from rfl]
        exact and_mask128_eq_self _ hyh
      -- the two coordinate range checks, at the raw high words
      have hxcoord : coordGuard (wordFrom st.env.calldata (BitVec.toNat cptr))
          (wordFrom st.env.calldata
            (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 32))))
          (BitVec.ofNat 256 hi) (BitVec.ofNat 256 lo) = (0 : U256) := by
        rw [show (Bridge.Dialect c g).litValue (Literal.number hi) =
              BitVec.ofNat 256 hi from rfl,
            show (Bridge.Dialect c g).litValue (Literal.number lo) =
              BitVec.ofNat 256 lo from rfl,
            show (Bridge.Dialect c g).zero = (0 : U256) from rfl] at hxcc
        rw [guard_bridge] at hxcc
        rw [hmaskX] at hxcc
        simpa only [coordGuard] using hxcc
      have hycoord : coordGuard (wordFrom st.env.calldata
          (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 64))))
          (wordFrom st.env.calldata
            (BitVec.toNat (cptr + (Bridge.Dialect c g).litValue (Literal.number 96))))
          (BitVec.ofNat 256 hi) (BitVec.ofNat 256 lo) = (0 : U256) := by
        rw [show (Bridge.Dialect c g).litValue (Literal.number hi) =
              BitVec.ofNat 256 hi from rfl,
            show (Bridge.Dialect c g).litValue (Literal.number lo) =
              BitVec.ofNat 256 lo from rfl,
            show (Bridge.Dialect c g).zero = (0 : U256) from rfl] at hycc
        rw [guard_bridge] at hycc
        rw [hmaskY] at hycc
        simpa only [coordGuard] using hycc
      have hxcheck := coordCheck_lift _ _ hi lo
        ((coordCheck_to_nat _ _ (BitVec.ofNat 256 hi) (BitVec.ofNat 256 lo)).mp
          (by simpa only [coordGuard] using hxcoord))
      have hycheck := coordCheck_lift _ _ hi lo
        ((coordCheck_to_nat _ _ (BitVec.ofNat 256 hi) (BitVec.ofNat 256 lo)).mp
          (by simpa only [coordGuard] using hycoord))
      exact g1WordsOk_of_checks cd cptr.toNat _ _ _ _ hi lo
        hword1 hword2 hword3 hword4 hxh hyh
        (BitVec.isLt _) (BitVec.isLt _) hkey hxcheck hycheck
  -- the four guarded `fail` sites: the scope obligation, then the revert arm
  all_goals
    first
    | exact ⟨cenv, by
        change lookupFun funs "fail" = some (TraceReturn.failFDecl, cenv)
        exact hc⟩
    | exact Hold.intro (Or.inl ⟨rfl, by assumption⟩)


end CommonG1InlineRuns

section G1Walk

open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac Midfall.Yul.VKP
open Midfall.LoweringV2.Blocks Midfall.LoweringV2.Blocks.TraceReturn Midfall.Yul.Word
open Midfall.Yul.LoopRule

/-! ### VEnv algebra (the tree's LagrangeRows copies, kept local to this file) -/

theorem t_venv_set_length {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (a : D.Value) : (VEnv.set V x a).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

theorem t_venv_set_set {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {a b : D.Value} : VEnv.set (VEnv.set V x a) x b = VEnv.set V x b := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

theorem t_venv_set_comm {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {a b : D.Value} (h : x ≠ y) :
    VEnv.set (VEnv.set V x a) y b = VEnv.set (VEnv.set V y b) x a := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨z, u⟩ := p
      by_cases hzx : z = x
      · subst hzx
        have hzy : ¬ (z = y) := fun h' => h h'
        simp [VEnv.set, hzy]
      · by_cases hzy : z = y
        · subst hzy
          have hzx' : ¬ (z = x) := fun h' => hzx h'
          simp [VEnv.set, hzx']
        · simp [VEnv.set, hzx, hzy, ih]

theorem t_venv_get_set_same {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {v w : D.Value} (h : VEnv.get V x = some v) :
    VEnv.get (VEnv.set V x w) x = some w := by
  induction V with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x
      · subst hy
        simp [VEnv.set, VEnv.get]
      · have hget : VEnv.get rest x = some v := by
          have h2 : VEnv.get ((y, u) :: rest) x = some v := h
          simpa [VEnv.get, List.find?, hy] using h2
        have h3 := ih hget
        simpa [VEnv.set, VEnv.get, List.find?, hy] using h3

theorem t_venv_get_set_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get (VEnv.set V x v) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y', u⟩ := p
      by_cases hyx : y' = x
      · subst hyx
        have hyy : ¬ (y' = y) := fun h' => h h'.symm
        simp [VEnv.set, VEnv.get, List.find?, hyy]
      · have hset : VEnv.set ((y', u) :: rest) x v = (y', u) :: VEnv.set rest x v := by
          simp [VEnv.set, hyx]
        rw [hset]
        by_cases hyy : y' = y
        · subst hyy
          simp [VEnv.get, List.find?]
        · simpa [VEnv.get, List.find?, hyy] using ih

theorem t_venv_get_cons_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get ((x, v) :: V) y = VEnv.get V y := by
  have hd : decide (x = y) = false := decide_eq_false (fun h' => h h'.symm)
  simp only [VEnv.get, List.find?, hd]

theorem t_venv_set_self {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {v : D.Value} (h : VEnv.get V x = some v) : VEnv.set V x v = V := by
  induction V with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x
      · subst hy
        simp [VEnv.set, VEnv.get] at h ⊢
        rw [h]
      · have hget : VEnv.get rest x = some v := by
          have h2 : VEnv.get ((y, u) :: rest) x = some v := h
          simpa [VEnv.get, List.find?, hy] using h2
        simp [VEnv.set, hy, ih hget]

theorem t_venv_set_overwrite {D : YulSemantics.Dialect} [DecidableEq D.Value]
    (V : VEnv D) (x y z : Ident) (a b c a' b' c' : D.Value)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    VEnv.set (VEnv.set (VEnv.set (VEnv.set (VEnv.set (VEnv.set V x a) y b) z c)
        x a') y b') z c'
      = VEnv.set (VEnv.set (VEnv.set V x a') y b') z c' := by
  rw [t_venv_set_comm (x := z) (y := x) (a := c) (b := a') (h := Ne.symm hxz)]
  rw [t_venv_set_comm (x := y) (y := x) (a := b) (b := a') (h := Ne.symm hxy)]
  rw [t_venv_set_set]
  rw [t_venv_set_comm (x := z) (y := y) (a := c) (b := b') (h := Ne.symm hyz)]
  rw [t_venv_set_set]
  rw [t_venv_set_set]

theorem t_restore_cons {D : YulSemantics.Dialect} [DecidableEq D.Value]
    (V₀ V : VEnv D) (E : D.Value) (h : V.length = V₀.length) :
    restore V₀ (("end", E) :: V) = V := by
  rw [restore, List.length_cons, h]
  simp

/-! ### The walk's environment family -/

/-- `List.append`'s compiled worker at the empty list: the kernel leaves this form in goals
    that have been through `whnf`, where `List.nil_append` no longer matches syntactically. -/
theorem list_append_nil_f {α : Type} (l : List α) : List.append._f [] PUnit.unit l = l := rfl

/-- The walk loop's pre: the calldata and the three cursors. -/
def g1WalkPre {c : ExternalCalls} {g : ExternalGas} (cd : Bytes) (walk : String)
    (a w b : Nat) : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
  fun V st => st.env.calldata = cd.data.toList ∧
    VEnv.get V "proof_cptr" = some (BitVec.ofNat 256 a) ∧
    VEnv.get V walk = some (BitVec.ofNat 256 w) ∧
    VEnv.get V "buf_len" = some (BitVec.ofNat 256 b)

/-- The walk loop's post: every run reverts, or absorbs the `j` frames into both windows, advances
    the three cursors, and leaves memory outside both windows alone. -/
def g1WalkPost {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g))
    (st : EvmState) (cd : Bytes) (walk : String) (j a w b : Nat) :
    VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
  fun V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
    (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
      V' = VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * j)))
        walk (BitVec.ofNat 256 (w + 128 * j))) "proof_cptr" (BitVec.ofNat 256 (a + 128 * j)) ∧
      bytesAt st' w (128 * j) = cdSlice cd a (128 * j) ∧
      bytesAt st' b (128 * j) = cdSlice cd a (128 * j) ∧
      (∀ i, i < j → g1WordsOk cd (a + 128 * i) = true) ∧
      (∀ x, (x < w ∨ w + 128 * j ≤ x) → (x < b ∨ b + 128 * j ≤ x) →
        st'.memory x = st.memory x))

/-- The loop-head environment at `k` frames: `end` at the head, the three cursors updated in
    place on the caller's environment. -/
def g1WalkEnv {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g))
    (endv : U256) (walk : String) (a w b : Nat) (k : Nat) : VEnv (Bridge.Dialect c g) :=
  ("end", endv) :: VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * k)))
    walk (BitVec.ofNat 256 (w + 128 * k))) "proof_cptr" (BitVec.ofNat 256 (a + 128 * k))

/-- **THE `common_uncompressed_g1` CALL SUMMARY, in continuation-passing form.** Besides the
    helper's own post facts it requires the call-site facts the helper contract needs (calldata,
    bounds, the `(hi, lo)` split), and - because the row runs at an arbitrary function scope - the
    declaration resolution: the looked-up body IS `commonG1Inline err hi lo` and its scope resolves
    `fail`. -/
def g1Summary {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    (cd : Bytes) (st1 : EvmState) (buf cptr : U256) (err hi lo : Nat) :
    (EResult (Bridge.Dialect c g) → Prop) → Prop :=
  fun Q =>
    (∀ (decl : FDecl (Bridge.Dialect c g)) (cenv : FunEnv (Bridge.Dialect c g)),
        lookupFun funs "common_uncompressed_g1" = some (decl, cenv) →
        decl.body = commonG1Inline err hi lo ∧ decl.params = ["buf_len", "cptr"] ∧
        decl.rets = ["ret"] ∧
        (∃ cf, lookupFun cenv "fail" = some (TraceReturn.failFDecl, cf))) ∧
    st1.env.calldata = cd.data.toList ∧
    cptr.toNat + 128 ≤ cd.data.toList.length ∧
    cd.size < 2 ^ 256 ∧
    hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase ∧
    (∀ st2, Midfall.LoweringV2.Reverted st2 → Q (.halt st2)) ∧
    (∀ st2, st2.env = st1.env → st2.halted = st1.halted →
      bytesAt st2 buf.toNat 128 = cdSlice cd cptr.toNat 128 →
      (∀ x, (x < buf.toNat ∨ buf.toNat + 128 ≤ x) → st2.memory x = st1.memory x) →
      Q (.vals [buf + 128] st2))

/-- The call table the walk loop runs under: `fail` and `common_uncompressed_g1`. -/
def g1WalkCT {c : ExternalCalls} {g : ExternalGas} (cd : Bytes) (err hi lo : Nat) :
    CT (Bridge.Dialect c g) :=
  fun funs fn args st =>
    match args with
    | [_] => if fn = "fail" then some (failT funs) else none
    | [buf, cptr] =>
        if fn = "common_uncompressed_g1" then
          some (g1Summary funs cd st buf cptr err hi lo)
        else none
    | _ => none

theorem g1WalkCT_sound {c : ExternalCalls} {g : ExternalGas} (cd : Bytes) (err hi lo : Nat) :
    CSound (Bridge.Dialect c g) (g1WalkCT (c := c) (g := g) cd err hi lo) := by
  intro funs fn argvals st1 T hT Q hTQ decl cenv hlook hlenV Vend st2 o hbody
  unfold g1WalkCT at hT
  cases argvals with
  | nil => cases hT
  | cons a1 rest =>
    cases rest with
    | nil =>
      dsimp only at hT
      by_cases hfn : fn = "fail"
      · rw [if_pos hfn] at hT
        cases hT
        obtain ⟨⟨cenv', hl⟩, hQ⟩ := hTQ
        subst hfn
        rw [hl] at hlook
        cases hlook
        cases hbody with
        | block hstmts =>
            obtain ⟨ho, hrev⟩ := tr_fail_body hstmts
            subst ho
            refine ⟨fun h => ?_, fun _ => hQ _ hrev⟩
            rcases h with h | h <;> cases h
      · rw [if_neg hfn] at hT
        cases hT
    | cons a2 rest2 =>
      cases rest2 with
      | nil =>
        dsimp only at hT
        by_cases hfn : fn = "common_uncompressed_g1"
        · rw [if_pos hfn] at hT
          cases hT
          subst hfn
          obtain ⟨hdecl, hcd1, hlen, hsz, hkey, hhalt, hnorm⟩ := hTQ
          obtain ⟨hbodyEq, hparams, hrets, hfailC⟩ := hdecl decl cenv hlook
          rw [hbodyEq] at hbody
          have hcallee : (decl.params.zip [a1, a2]) ++
              bindZeros (Bridge.Dialect c g) decl.rets =
              [("buf_len", a1), ("cptr", a2), ("ret", (Bridge.Dialect c g).zero)] := by
            rw [hparams, hrets]
            simp [bindZeros]
          rw [hcallee] at hbody
          cases hbody with
          | block hstmts =>
              have hfuns : ∃ cf, lookupFun (hoist (Bridge.Dialect c g)
                  (commonG1Inline err hi lo) :: cenv) "fail" =
                  some (TraceReturn.failFDecl, cf) := by
                obtain ⟨cf, hcf⟩ := hfailC
                exact ⟨cf, by
                  change lookupFun cenv "fail" = some (TraceReturn.failFDecl, cf)
                  exact hcf⟩
              have hsum := commonG1Inline_runs (hoist (Bridge.Dialect c g)
                (commonG1Inline err hi lo) :: cenv) st1 cd a1 a2 err hi lo hfuns hcd1 hlen hsz hkey
              have hres := hsum _ _ _ hstmts
              rcases hres.elim with ⟨ho, hrev⟩ | ⟨ho, hret', hretR, henv', hhalt', hbytes, hmem', hwords⟩
              · subst ho
                refine ⟨fun hcon => ?_, fun _ => hhalt _ hrev⟩
                rcases hcon with h | h <;> cases h
              · subst ho
                refine ⟨fun _ => ?_, fun h => (by cases h)⟩
                rw [hrets]
                simp only [List.map_cons, List.map_nil]
                rw [show (Bridge.Dialect c g).zero = (0 : U256) from rfl]
                rw [hretR]
                simp only [Option.getD_some]
                exact hnorm _ henv' hhalt' hbytes hmem'
        · rw [if_neg hfn] at hT
          cases hT
      | cons a3 rest3 => cases hT
theorem stepOp_add_evm (a b : U256) (st : EvmState) :
    stepOp Op.add [a, b] st = some (.ok [a + b] st) := rfl

theorem stepOp_calldatacopy_evm (dst src n : U256) (st : EvmState) :
    stepOp Op.calldatacopy [dst, src, n] st =
      some (.ok [] { touchMemory st dst.toNat n.toNat with
        memory := copyInto st.memory dst.toNat src.toNat n.toNat st.env.calldata }) := rfl

theorem t_setMany_one {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (v : D.Value) : VEnv.setMany V [x] [v] = VEnv.set V x v := rfl

/-- A `calldatacopy` window disjoint from a read leaves the read alone. -/
theorem bytesAt_calldatacopy_outside (st : EvmState) (dat : List UInt8)
    (dst src n a m : Nat) (h : a + m ≤ dst ∨ dst + n ≤ a) :
    bytesAt { touchMemory st dst n with memory := copyInto st.memory dst src n dat } a m
      = bytesAt st a m := by
  unfold bytesAt readBytes
  apply ByteArray.ext
  apply congrArg List.toArray
  apply List.map_congr_left
  intro i hi
  have him : i < m := List.mem_range.mp hi
  show (if dst ≤ a + i ∧ a + i < dst + n then byteFrom dat (src + (a + i - dst))
      else st.memory (a + i)) = st.memory (a + i)
  have hc : ¬ (dst ≤ a + i ∧ a + i < dst + n) := by omega
  rw [if_neg hc]

/-- A `bytesAt` window is unchanged where the memory is pointwise unchanged. -/
theorem bytesAt_congr_mem {st st' : EvmState} {a m : Nat}
    (h : ∀ x, a ≤ x → x < a + m → st'.memory x = st.memory x) :
    bytesAt st' a m = bytesAt st a m := by
  unfold bytesAt readBytes
  apply ByteArray.ext
  apply congrArg List.toArray
  apply List.map_congr_left
  intro i hi
  have him : i < m := List.mem_range.mp hi
  exact h (a + i) (by omega) (by omega)

set_option maxHeartbeats 20000000 in
theorem g1WalkTail_contract (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (cd : Bytes) (walk : String) (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end")
    (j a w b : Nat) (ha : a + 128 * j ≤ cd.size) (hcds : cd.size < 2 ^ 256)
    (hw : w + 128 * j < 2 ^ 256) (hb : b + 128 * j < 2 ^ 256)
    (hdisj : w + 128 * j ≤ b ∨ b + 128 * j ≤ w)
    (st0 : EvmState) (k : Nat) (hklt : k < j) :
    StmtsContractAll (D := Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g) (GenAst.g1WalkBody walk) ::
        hoist (Bridge.Dialect c g) [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
          [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] ::
        R.scope c g)
      [GenAst.yexpr (GenAst.yop Op.calldatacopy
          [GenAst.yvar walk, GenAst.yvar "proof_cptr", GenAst.ylit 128]),
        GenAst.yset walk (GenAst.yop Op.add [GenAst.yvar walk, GenAst.ylit 128]),
        GenAst.yset "proof_cptr" (GenAst.yop Op.add [GenAst.yvar "proof_cptr", GenAst.ylit 128])]
      (fun V st =>
        VEnv.get V walk = some (BitVec.ofNat 256 (w + 128 * k)) ∧
        VEnv.get V "proof_cptr" = some (BitVec.ofNat 256 (a + 128 * k)) ∧
        st.env.calldata = cd.data.toList ∧ st.halted = st0.halted ∧
        bytesAt st b (128 * k) = cdSlice cd a (128 * k) ∧
        bytesAt st w (128 * k) = cdSlice cd a (128 * k) ∧
        bytesAt st (b + 128 * k) 128 = cdSlice cd (a + 128 * k) 128 ∧
        g1WordsOk cd (a + 128 * k) = true ∧
        (∀ i, i < k → g1WordsOk cd (a + 128 * i) = true) ∧
        (∀ x, (x < w ∨ w + 128 * k ≤ x) → (x < b ∨ b + 128 * (k + 1) ≤ x) →
          st.memory x = st0.memory x))
      (fun V st V' st' o => Hold (
        (o = .normal ∧
          V' = VEnv.set (VEnv.set V walk (BitVec.ofNat 256 (w + 128 * (k + 1))))
            "proof_cptr" (BitVec.ofNat 256 (a + 128 * (k + 1))) ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧
          bytesAt st' b (128 * (k + 1)) = cdSlice cd a (128 * (k + 1)) ∧
          bytesAt st' w (128 * (k + 1)) = cdSlice cd a (128 * (k + 1)) ∧
          (∀ i, i < k + 1 → g1WordsOk cd (a + 128 * i) = true) ∧
          (∀ x, (x < w ∨ w + 128 * (k + 1) ≤ x) → (x < b ∨ b + 128 * (k + 1) ≤ x) →
            st'.memory x = st0.memory x)) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st'))) := by
  intro V st hpre
  obtain ⟨hwv, hpc, hcd, hhalt, hbB, hbW, hBframe, hBwords, hwords, hmem⟩ := hpre
  have hk_le : k ≤ j := Nat.le_of_lt hklt
  have hmul : 128 * k ≤ 128 * j := Nat.mul_le_mul_left 128 hk_le
  have hwlt : w + 128 * k < 2 ^ 256 := by omega
  have hblt : b + 128 * k < 2 ^ 256 := by omega
  have hal : a + 128 * k < 2 ^ 256 := by omega
  have hszEq : cd.data.toList.length = cd.size := by
    show cd.data.toList.length = cd.data.size
    exact Array.length_toList
  have hcdlen : (a + 128 * k) + 128 ≤ cd.data.toList.length := by
    have := hszEq
    omega
  refine allRuns_of_wp (c := c) (g := g) (n := 40) ?_
  set_option wpLets false in
  wp_run
  rw [hpc]
  set_option wpLets false in
  wp_run
  rw [hwv]
  set_option wpLets false in
  wp_run
  rw [hwv]
  set_option wpLets false in
  wp_run
  have hpc2 : VEnv.get (VEnv.setMany V [walk]
      [(fun x1 x2 : U256 => x1 + x2) (BitVec.ofNat 256 (w + 128 * k))
        ((Bridge.Dialect c g).litValue (Literal.number 128))]) "proof_cptr" =
      some (BitVec.ofNat 256 (a + 128 * k)) := by
    rw [t_setMany_one (D := Bridge.Dialect c g)]
    rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := walk) (y := "proof_cptr") (by
      obtain ⟨h1, h2, h3⟩ := hwalk
      exact Ne.symm h1)]
    exact hpc
  rw [hpc2]
  set_option wpLets false in
  wp_run
  have hWk1 : (fun x1 x2 : U256 => x1 + x2) (BitVec.ofNat 256 (w + 128 * k))
      ((Bridge.Dialect c g).litValue (Literal.number 128)) =
      BitVec.ofNat 256 (w + 128 * (k + 1)) := by
    change BitVec.ofNat 256 (w + 128 * k) + BitVec.ofNat 256 128 =
      BitVec.ofNat 256 (w + 128 * (k + 1))
    calc BitVec.ofNat 256 (w + 128 * k) + BitVec.ofNat 256 128
        = BitVec.ofNat 256 ((w + 128 * k) + 128) := (BitVec.ofNat_add _ _).symm
      _ = BitVec.ofNat 256 (w + 128 * (k + 1)) := by
          rw [show (w + 128 * k) + 128 = w + 128 * (k + 1) from by omega]
  have hPk1 : (fun x1 x2 : U256 => x1 + x2) (BitVec.ofNat 256 (a + 128 * k))
      ((Bridge.Dialect c g).litValue (Literal.number 128)) =
      BitVec.ofNat 256 (a + 128 * (k + 1)) := by
    change BitVec.ofNat 256 (a + 128 * k) + BitVec.ofNat 256 128 =
      BitVec.ofNat 256 (a + 128 * (k + 1))
    calc BitVec.ofNat 256 (a + 128 * k) + BitVec.ofNat 256 128
        = BitVec.ofNat 256 ((a + 128 * k) + 128) := (BitVec.ofNat_add _ _).symm
      _ = BitVec.ofNat 256 (a + 128 * (k + 1)) := by
          rw [show (a + 128 * k) + 128 = a + 128 * (k + 1) from by omega]
  refine Hold.intro (Or.inl ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · -- environment: the two assignments, with the normalized add results
    rw [t_setMany_one (D := Bridge.Dialect c g), t_setMany_one (D := Bridge.Dialect c g)]
    rw [hWk1, hPk1]
  · rfl
  · rfl
  · -- buffer window: the k-window is untouched, the new frame is the helper's copy
    rw [show 128 * (k + 1) = 128 * k + 128 by omega, bytesAt_append]
    dsimp only
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal,
      show (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number 128))) = 128 from rfl]
    rw [bytesAt_calldatacopy_outside st st.env.calldata (w + 128 * k) (a + 128 * k) 128
      b (128 * k) (by omega)]
    rw [bytesAt_calldatacopy_outside st st.env.calldata (w + 128 * k) (a + 128 * k) 128
      (b + 128 * k) 128 (by omega)]
    rw [hbB, hBframe, cdSlice_append]
  · -- walk window: the k-window is untouched, the new frame is the loop's copy
    rw [show 128 * (k + 1) = 128 * k + 128 by omega, bytesAt_append]
    dsimp only
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal,
      show (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number 128))) = 128 from rfl]
    rw [bytesAt_calldatacopy_outside st st.env.calldata (w + 128 * k) (a + 128 * k) 128
      w (128 * k) (by omega)]
    rw [bytesAt_calldatacopy_cdSlice st cd (w + 128 * k) (a + 128 * k) 128 hcd hcdlen]
    rw [hbW, cdSlice_append]
  · -- the frame's range check
    intro i hi
    by_cases hik : i < k
    · exact hwords i hik
    · have hik' : i = k := by omega
      subst i
      exact hBwords
  · -- memory outside both windows
    intro x hxw hxb
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal,
      show (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number 128))) = 128 from rfl]
    show copyInto st.memory (w + 128 * k) (a + 128 * k) 128 st.env.calldata x = st0.memory x
    have hxc : copyInto st.memory (w + 128 * k) (a + 128 * k) 128 st.env.calldata x = st.memory x := by
      unfold copyInto
      rw [if_neg]
      omega
    rw [hxc]
    exact hmem x (by omega) (by omega)

set_option maxHeartbeats 20000000 in
theorem g1Call_contract (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (cd : Bytes) (walk : String) (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end")
    (j a w b : Nat) (ha : a + 128 * j ≤ cd.size) (hcds : cd.size < 2 ^ 256)
    (hb : b + 128 * j < 2 ^ 256)
    (err hi lo : Nat)
    (hcommon : lookupFun (R.scope c g) "common_uncompressed_g1" =
      some ({ params := ["buf_len", "cptr"], rets := ["ret"],
              body := commonG1Inline err hi lo }, R.scope c g))
    (hkey : hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase)
    (st0 : EvmState) (k : Nat) (hklt : k < j) :
    StmtContractAll (D := Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g) (GenAst.g1WalkBody walk) ::
        hoist (Bridge.Dialect c g) [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
          [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] ::
        R.scope c g)
      (Stmt.assign ["buf_len"] (Expr.call "common_uncompressed_g1"
        [Expr.var "buf_len", Expr.var "proof_cptr"]))
      (fun V st =>
        VEnv.get V "proof_cptr" = some (BitVec.ofNat 256 (a + 128 * k)) ∧
        VEnv.get V walk = some (BitVec.ofNat 256 (w + 128 * k)) ∧
        VEnv.get V "buf_len" = some (BitVec.ofNat 256 (b + 128 * k)) ∧
        st.env.calldata = cd.data.toList ∧ st.halted = st0.halted)
      (fun V st V' st' o => Hold (
        (o = .normal ∧
          V' = VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * (k + 1))) ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧
          bytesAt st' (b + 128 * k) 128 = cdSlice cd (a + 128 * k) 128 ∧
          g1WordsOk cd (a + 128 * k) = true ∧
          (∀ x, (x < b + 128 * k ∨ b + 128 * k + 128 ≤ x) → st'.memory x = st.memory x)) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st'))) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hpc, hwv, hbuf, hcd, hhalt⟩ := hpre
  have hk_le : k ≤ j := Nat.le_of_lt hklt
  have hmul : 128 * k ≤ 128 * j := Nat.mul_le_mul_left 128 hk_le
  have hclt : a + 128 * k < 2 ^ 256 := by omega
  have hszEq : cd.data.toList.length = cd.size := by
    show cd.data.toList.length = cd.data.size
    exact Array.length_toList
  have hlen : (BitVec.ofNat 256 (a + 128 * k)).toNat + 128 ≤ cd.data.toList.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclt, hszEq]
    omega
  have hfail : ∃ cenv, lookupFun (R.scope c g) "fail" =
      some (TraceReturn.failFDecl, cenv) := by
    have h := fail_lookupV3 (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) R (c := c) (g := g)
    rw [show scopeV3 R c g = R.scope c g from rfl] at h
    exact ⟨R.scope c g, h⟩
  have hhB : hoist (Bridge.Dialect c g) (GenAst.g1WalkBody walk) = [] := rfl
  have hhI : hoist (Bridge.Dialect c g) [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
      [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] = [] := rfl
  have hlook0 : lookupFun (hoist (Bridge.Dialect c g) (GenAst.g1WalkBody walk) ::
      hoist (Bridge.Dialect c g) [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
        [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] ::
      R.scope c g) "common_uncompressed_g1" =
      some ({ params := ["buf_len", "cptr"], rets := ["ret"],
              body := commonG1Inline err hi lo }, R.scope c g) := by
    rw [hhB, hhI]
    change lookupFun (R.scope c g) "common_uncompressed_g1" = _
    exact hcommon
  have hfail' : ∃ cf, lookupFun (hoist (Bridge.Dialect c g) (commonG1Inline err hi lo) ::
      R.scope c g) "fail" = some (TraceReturn.failFDecl, cf) := by
    have hhC : hoist (Bridge.Dialect c g) (commonG1Inline err hi lo) = [] := rfl
    obtain ⟨cf, hcf⟩ := hfail
    refine ⟨cf, ?_⟩
    rw [hhC]
    change lookupFun (R.scope c g) "fail" = some (TraceReturn.failFDecl, cf)
    exact hcf
  have hcallee : ((["buf_len", "cptr"] : List String).zip
      [BitVec.ofNat 256 (b + 128 * k), BitVec.ofNat 256 (a + 128 * k)]) ++
      bindZeros (Bridge.Dialect c g) ["ret"] =
      [("buf_len", BitVec.ofNat 256 (b + 128 * k)),
        ("cptr", BitVec.ofNat 256 (a + 128 * k)),
        ("ret", (Bridge.Dialect c g).zero)] := by
    simp [bindZeros]
  cases hrun with
  | assignVal he hlenV =>
      cases he with
      | callOk hargs hlook harglen hbodyrun hnorm =>
          cases hargs with
          | argsCons hrest hhead2 =>
            cases hrest with
            | argsCons hrest2 hhead1 =>
              cases hrest2 with
              | argsNil =>
                cases hhead2 with
                | var hget2 =>
                  cases hhead1 with
                  | var hget1 =>
                    rename_i v2 v1
                    have hv2 : v2 = BitVec.ofNat 256 (b + 128 * k) := by
                      have h := hget2
                      rw [hbuf] at h
                      exact (Option.some.inj h).symm
                    have hv1 : v1 = BitVec.ofNat 256 (a + 128 * k) := by
                      have h := hget1
                      rw [hpc] at h
                      exact (Option.some.inj h).symm
                    rw [hlook0] at hlook
                    cases hlook
                    rw [hv2, hv1] at hbodyrun
                    rw [hcallee] at hbodyrun
                    cases hbodyrun with
                    | block hstmts =>
                      have hsum := commonG1Inline_runs
                        (hoist (Bridge.Dialect c g) (commonG1Inline err hi lo) :: R.scope c g)
                        st cd (BitVec.ofNat 256 (b + 128 * k)) (BitVec.ofNat 256 (a + 128 * k))
                        err hi lo hfail' hcd hlen hcds hkey
                      have hres := hsum _ _ _ hstmts
                      rcases hres.elim with ⟨hobh, hrev⟩ |
                          ⟨hobn, hret, hretR, henv, hhalt', hbytes, hmem', hwords⟩
                      · rcases hnorm with h | h <;> rw [h] at hobh <;> cases hobh
                      · have hBk1 : BitVec.ofNat 256 (b + 128 * k) + 128 =
                            BitVec.ofNat 256 (b + 128 * (k + 1)) := by
                          calc BitVec.ofNat 256 (b + 128 * k) + BitVec.ofNat 256 128
                              = BitVec.ofNat 256 ((b + 128 * k) + 128) :=
                                (BitVec.ofNat_add _ _).symm
                            _ = BitVec.ofNat 256 (b + 128 * (k + 1)) := by
                                rw [show (b + 128 * k) + 128 = b + 128 * (k + 1) from by omega]
                        have hBkNat : (BitVec.ofNat 256 (b + 128 * k)).toNat = b + 128 * k := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        have hPkNat : (BitVec.ofNat 256 (a + 128 * k)).toNat = a + 128 * k := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclt]
                        refine Hold.intro (Or.inl ⟨rfl, ?_, henv, hhalt', ?_, ?_, ?_⟩)
                        · simp only [List.map_cons, List.map_nil]
                          rw [show (Bridge.Dialect c g).zero = (0 : U256) from rfl]
                          rw [t_setMany_one (D := Bridge.Dialect c g), hretR]
                          simp only [Option.getD_some]
                          rw [hBk1]
                        · rw [hBkNat, hPkNat] at hbytes
                          exact hbytes
                        · rw [hPkNat] at hwords
                          exact hwords
                        · intro x hx
                          exact hmem' x (by simpa [hBkNat] using hx)
  | assignHalt he =>
      cases he with
      | callHalt hargs hlook harglen hbodyrun =>
          cases hargs with
          | argsCons hrest hhead2 =>
            cases hrest with
            | argsCons hrest2 hhead1 =>
              cases hrest2 with
              | argsNil =>
                cases hhead2 with
                | var hget2 =>
                  cases hhead1 with
                  | var hget1 =>
                    rename_i v2 v1
                    have hv2 : v2 = BitVec.ofNat 256 (b + 128 * k) := by
                      have h := hget2
                      rw [hbuf] at h
                      exact (Option.some.inj h).symm
                    have hv1 : v1 = BitVec.ofNat 256 (a + 128 * k) := by
                      have h := hget1
                      rw [hpc] at h
                      exact (Option.some.inj h).symm
                    rw [hlook0] at hlook
                    cases hlook
                    rw [hv2, hv1] at hbodyrun
                    rw [hcallee] at hbodyrun
                    cases hbodyrun with
                    | block hstmts =>
                      have hsum := commonG1Inline_runs
                        (hoist (Bridge.Dialect c g) (commonG1Inline err hi lo) :: R.scope c g)
                        st cd (BitVec.ofNat 256 (b + 128 * k)) (BitVec.ofNat 256 (a + 128 * k))
                        err hi lo hfail' hcd hlen hcds hkey
                      have hres := hsum _ _ _ hstmts
                      rcases hres.elim with ⟨hobh, hrev⟩ |
                          ⟨hobn, hret, hretR, henv, hhalt', hbytes, hmem', hwords⟩
                      · exact Hold.intro (Or.inr ⟨rfl, hrev⟩)
                      · cases hobn
      | callArgsHalt hargs =>
          exact (Midfall.LoweringV2.Blocks.EcPairing.args_vars_ne_halt
            (D := Bridge.Dialect c g) ["buf_len", "proof_cptr"] hargs).elim



end G1Walk


open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac Midfall.Yul.VKP
open Midfall.LoweringV2.Blocks Midfall.LoweringV2.Blocks.TraceReturn Midfall.Yul.Word
open Midfall.Yul.LoopRule

set_option maxHeartbeats 20000000 in
theorem g1WalkBody_step (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (cd : Bytes) (walk : String) (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end")
    (j a w b : Nat) (ha : a + 128 * j ≤ cd.size) (hcds : cd.size < 2 ^ 256)
    (hw : w + 128 * j < 2 ^ 256) (hb : b + 128 * j < 2 ^ 256)
    (hdisj : w + 128 * j ≤ b ∨ b + 128 * j ≤ w)
    (err hi lo : Nat)
    (hcommon : lookupFun (R.scope c g) "common_uncompressed_g1" =
      some ({ params := ["buf_len", "cptr"], rets := ["ret"],
              body := commonG1Inline err hi lo }, R.scope c g))
    (hkey : hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase)
    (st0 : EvmState) (k : Nat) (hklt : k < j) :
    StmtsContractAll (D := Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g) (GenAst.g1WalkBody walk) ::
        hoist (Bridge.Dialect c g) [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
          [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] ::
        R.scope c g)
      (GenAst.g1WalkBody walk)
      (fun V st =>
        VEnv.get V "proof_cptr" = some (BitVec.ofNat 256 (a + 128 * k)) ∧
        VEnv.get V walk = some (BitVec.ofNat 256 (w + 128 * k)) ∧
        VEnv.get V "buf_len" = some (BitVec.ofNat 256 (b + 128 * k)) ∧
        st.env.calldata = cd.data.toList ∧ st.halted = st0.halted ∧
        bytesAt st b (128 * k) = cdSlice cd a (128 * k) ∧
        bytesAt st w (128 * k) = cdSlice cd a (128 * k) ∧
        (∀ i, i < k → g1WordsOk cd (a + 128 * i) = true) ∧
        (∀ x, (x < w ∨ w + 128 * k ≤ x) → (x < b ∨ b + 128 * k ≤ x) →
          st.memory x = st0.memory x))
      (fun V st V' st' o =>
        (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧
          V' = VEnv.set (VEnv.set (VEnv.set V "buf_len"
              (BitVec.ofNat 256 (b + 128 * (k + 1)))) walk
              (BitVec.ofNat 256 (w + 128 * (k + 1)))) "proof_cptr"
              (BitVec.ofNat 256 (a + 128 * (k + 1))) ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧
          bytesAt st' b (128 * (k + 1)) = cdSlice cd a (128 * (k + 1)) ∧
          bytesAt st' w (128 * (k + 1)) = cdSlice cd a (128 * (k + 1)) ∧
          (∀ i, i < k + 1 → g1WordsOk cd (a + 128 * i) = true) ∧
          (∀ x, (x < w ∨ w + 128 * (k + 1) ≤ x) → (x < b ∨ b + 128 * (k + 1) ≤ x) →
            st'.memory x = st.memory x))) := by
  let Mid : VEnv (Bridge.Dialect c g) → EvmState →
      VEnv (Bridge.Dialect c g) → EvmState → Prop := fun V0 st1 Vm stm =>
    Vm = VEnv.set V0 "buf_len" (BitVec.ofNat 256 (b + 128 * (k + 1))) ∧
    stm.env = st1.env ∧ stm.halted = st1.halted ∧
    bytesAt stm (b + 128 * k) 128 = cdSlice cd (a + 128 * k) 128 ∧
    g1WordsOk cd (a + 128 * k) = true ∧
    (∀ x, (x < b + 128 * k ∨ b + 128 * k + 128 ≤ x) → stm.memory x = st1.memory x)
  refine StmtsContractAll.head_tail_ex (D := Bridge.Dialect c g) (Mid := Mid) ?_ ?_
  · -- the helper call
    intro V0 st1 hpre0 V1 st1' o1 h1
    obtain ⟨hpc0, hwv0, hbuf0, hcd0, hhalt0, _⟩ := hpre0
    have hc := g1Call_contract (R := R) (c := c) (g := g) cd walk hwalk j a w b ha hcds hb
      err hi lo hcommon hkey st0 k hklt V0 st1 ⟨hpc0, hwv0, hbuf0, hcd0, hhalt0⟩ V1 st1' o1 h1
    rcases hc.elim with ⟨ho, hmid⟩ | ⟨hoh, hrev⟩
    · exact Or.inl ⟨ho, hmid⟩
    · refine Or.inr ⟨?_, Or.inl ⟨hoh, hrev⟩⟩
      intro h
      rw [hoh] at h
      cases h
  · -- the copy and the two cursor updates
    intro V0 st1 Vm stm hpre0 hmid
    obtain ⟨hpc0, hwv0, hbuf0, hcd0, hhalt0, hbB0, hbW0, hwords0, hmem0⟩ := hpre0
    obtain ⟨hVm, hmEnv, hmHalt, hmBytes, hmWords, hmFrame⟩ := hmid
    intro Vm' stm' hpre' V' st' o hrun'
    obtain ⟨hVmeq, hstmeq⟩ := hpre'
    rw [hVmeq, hstmeq] at hrun'
    have hwalkM : VEnv.get Vm walk = some (BitVec.ofNat 256 (w + 128 * k)) := by
      rw [hVm]
      rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "buf_len") (y := walk)
        (by obtain ⟨h1, h2, h3⟩ := hwalk; exact h2)]
      exact hwv0
    have hpcM : VEnv.get Vm "proof_cptr" = some (BitVec.ofNat 256 (a + 128 * k)) := by
      rw [hVm]
      rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "buf_len") (y := "proof_cptr")
        (by decide)]
      exact hpc0
    have hmemTail : ∀ x, (x < w ∨ w + 128 * k ≤ x) → (x < b ∨ b + 128 * (k + 1) ≤ x) →
        stm.memory x = st1.memory x := by
      intro x hx1 hx2
      exact hmFrame x (by omega)
    have hbBTail : bytesAt stm b (128 * k) = cdSlice cd a (128 * k) :=
      (bytesAt_congr_mem (fun x h1 h2 => by rw [hmFrame x (by omega)])).trans hbB0
    have hbWTail : bytesAt stm w (128 * k) = cdSlice cd a (128 * k) :=
      (bytesAt_congr_mem (fun x h1 h2 => by rw [hmFrame x (by omega)])).trans hbW0
    have hp := g1WalkTail_contract (R := R) (c := c) (g := g) cd walk hwalk j a w b
      ha hcds hw hb hdisj st1 k hklt Vm stm
      ⟨hwalkM, hpcM, by simpa [hmEnv] using hcd0, by simpa [hmHalt] using hhalt0,
        hbBTail, hbWTail, hmBytes, hmWords, hwords0, hmemTail⟩
    have hp' := hp V' st' o hrun'
    rcases hp'.elim with ⟨ho, henvEq, hse, hsh, hbB', hbW', hwords', hmem'⟩ |
        ⟨hoh, hrev⟩
    · refine Or.inr ⟨ho, ?_, ?_, ?_, hbB', hbW', hwords', hmem'⟩
      · rw [henvEq, hVm]
      · rw [hse, hmEnv]
      · rw [hsh, hmHalt]
    · exact Or.inl ⟨hoh, hrev⟩


/-! ### Local inversions for the walk loop's guard and init -/

theorem g1Walk_list_length_one {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => exact ⟨a, rfl⟩
      | cons b rest => simp at h

theorem g1Walk_eval_var_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : Ident} {av : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var x) (.vals [av] st')) :
    VEnv.get V x = some av ∧ st' = st := by
  cases h with
  | var hget => exact ⟨hget, rfl⟩

theorem g1Walk_eval_lit_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {n : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n)) (.vals [cv] st')) :
    cv = BitVec.ofNat 256 n ∧ st' = st := by
  cases h
  exact ⟨rfl, rfl⟩

theorem g1Walk_eval_builtin_vals_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {op : EVM.Op} {args : List (Expr EVM.Op)}
    {vals : List U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op args) (.vals vals st')) :
    ∃ argvals st1, EvalArgs (Bridge.Dialect c g) funs V st args (.vals argvals st1) ∧
      (Bridge.Dialect c g).Builtin op argvals st1 (.ok vals st') := by
  cases h with
  | builtinOk hargs hbi => exact ⟨_, _, hargs, hbi⟩

theorem g1Walk_eval_add_var_lit_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : String} {k : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.add [Expr.var x, Expr.lit (Literal.number k)]) (.vals [cv] st')) :
    ∃ a, VEnv.get V x = some a ∧ cv = a + BitVec.ofNat 256 k ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := g1Walk_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil hlit =>
          cases hnil with
          | argsNil =>
              obtain ⟨hk, rfl⟩ := g1Walk_eval_lit_inv hlit
              obtain ⟨ha, rfl⟩ := g1Walk_eval_var_inv hhead
              simp only [Bridge.Dialect, builtinWithExternal, stepOp, bin, hk] at hbi
              cases hbi
              exact ⟨_, ha, rfl, rfl⟩

theorem g1Walk_eval_lt_vars_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x y : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.lt [Expr.var x, Expr.var y]) (.vals [cv] st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      cv = b2w (xv.ult yv) ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := g1Walk_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil htail =>
          cases hnil with
          | argsNil =>
              obtain ⟨hyv, rfl⟩ := g1Walk_eval_var_inv htail
              obtain ⟨hxv, rfl⟩ := g1Walk_eval_var_inv hhead
              simp only [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, hxv, hyv, rfl, rfl⟩

theorem g1Walk_eval_add_var_lit_halt_false {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : String} {k : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.add [Expr.var x, Expr.lit (Literal.number k)]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := Op.add)
    (fun a b st r hr => by
      simp only [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh)
    h

theorem g1Walk_eval_lt_vars_halt_false {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x y : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.lt [Expr.var x, Expr.var y]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := Op.lt)
    (fun a b st r hr => by
      simp only [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    h

theorem g1Walk_exec_block_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {body : Block EVM.Op} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.block body) V' st' o) :
    ∃ Vb stb, ExecStmts (Bridge.Dialect c g) (hoist (Bridge.Dialect c g) body :: funs)
      V st body Vb stb o ∧ V' = restore V Vb ∧ st' = stb := by
  cases h with
  | block hb => exact ⟨_, _, hb, rfl, rfl⟩

theorem t_venv_set_cons_ne {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {V : VEnv D} {x y : Ident} {v a : D.Value} (h : x ≠ y) :
    VEnv.set ((x, v) :: V) y a = (x, v) :: VEnv.set V y a := by
  simp [VEnv.set, h]

theorem stmtsContractAll_single {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {s : Stmt D.Op} {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtContractAll funs s pre post) : StmtsContractAll funs [s] pre post := by
  intro V st hpre V' st' o hrun
  cases hrun with
  | seqCons h1 h2 =>
      cases h2 with
      | seqNil => exact h V st hpre V' st' .normal h1
  | seqStop h1 _ => exact h V st hpre V' st' o h1

/-- The init run of the walk loop: `let end := proof_cptr + 128*j`. -/
theorem g1WalkInit_run {c : ExternalCalls} {g : ExternalGas} (j : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V Vinit : VEnv (Bridge.Dialect c g)}
    {st stinit : EvmState}
    (h : Step (Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
            [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] :: funs)
      V st
      (.stmts [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
        [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))])
      (.sres Vinit stinit .normal)) :
    ∃ ev, VEnv.get V "proof_cptr" = some ev ∧
      Vinit = ("end", ev + BitVec.ofNat 256 (128 * j)) :: V ∧ stinit = st := by
  cases h with
  | seqCons h1 h2 =>
      cases h2 with
      | seqNil =>
          cases h1 with
          | letVal he hlen =>
              obtain ⟨v, rfl⟩ := g1Walk_list_length_one hlen
              obtain ⟨ev, hget, hv, hst⟩ := g1Walk_eval_add_var_lit_inv he
              exact ⟨ev, hget, by simp [hv], hst⟩
  | seqStop h1 hne =>
      cases h1 with
      | letVal _ _ => exact absurd rfl hne

set_option maxHeartbeats 20000000 in
/-- **THE WALK LOOP (all runs), ONE LEMMA FOR SIX SECTIONS.** Bound = `j`, the section's frame
    count. Every run reverts (a frame fails the range check), or ends normally having absorbed the
    `j` frames, copied them to the walk window, and advanced the three cursors; every frame passed
    `g1WordsOk`. LEAF ROW.TP.2 (loop rule GEN.3 + the `common_uncompressed_g1` summary).

    RESTATED AT THE CONSUMER BOUNDARY (A6 follow-up). The helper is the INLINED function of
    `R.scope`, so the loop cannot execute its call without knowing the declaration at `R.scope`:
    the two added facts are (a) `hcommon`, the resolution of `common_uncompressed_g1` to the
    three-parameter inlined body, and (b) `hkey`, its `BLS_P_HI`/`BLS_P_MINUS_ONE_LO` split.
    These are consumer-side, not row weakenings: `tp_computes` has `hR : ValidV3 R` and discharges
    them from `programOkB` (`constsCoherent`) + `expectedConsts` + `commonG1_inline`, with
    `err`/`hi`/`lo` the table's `ERR_BAD_POINT_ENCODING`/`BLS_P_HI`/`BLS_P_MINUS_ONE_LO`.

    PROOF PLAN (rest of the row). `allRuns_for_cons_wp_count` under `g1WalkCT` (already sound,
    `g1WalkCT_sound`) with the invariant `g1WalkEnv V end walk a w b k` + the three cursor reads +
    the two `bytesAt` windows + `g1WordsOk` below `k` + the outside-window memory clause + `k ≤ j`;
    the body is `commonG1Inline_runs` at `(ofNat (a+128k))` with `hh = hcommon`; the windows are
    `bytesAt_append`/`cdSlice_append`; the exit is `t_restore_cons`/`t_venv_set_overwrite`. -/
theorem g1walk_loop_sem (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (cd : Bytes) (walk : String) (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end")
    (j a w b : Nat) (ha : a + 128 * j ≤ cd.size) (hcd : cd.size < 2 ^ 256)
    (hw : w + 128 * j < 2 ^ 256) (hb : b + 128 * j < 2 ^ 256)
    (hdisj : w + 128 * j ≤ b ∨ b + 128 * j ≤ w)
    (err hi lo : Nat)
    (hcommon : lookupFun (R.scope c g) "common_uncompressed_g1" =
      some ({ params := ["buf_len", "cptr"], rets := ["ret"],
              body := commonG1Inline err hi lo }, R.scope c g))
    (hkey : hi * 2^256 + lo + 1 = Midfall.Assumptions.pBase) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) [GenAst.g1WalkLoop walk (128 * j)]
      (g1WalkPre cd walk a w b)
      (fun V st V' st' o => g1WalkPost V st cd walk j a w b V' st' o) := by
  apply stmtsContractAll_single
  intro V st hpre V' st' o hrun
  obtain ⟨hcdat, hpc0, hwv0, hbuf0⟩ := hpre
  let init : Block EVM.Op :=
    [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
      [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))]
  let cond : Expr EVM.Op := Expr.builtin Op.lt [Expr.var "proof_cptr", Expr.var "end"]
  let body : Block EVM.Op := GenAst.g1WalkBody walk
  let funsI : FunEnv (Bridge.Dialect c g) := hoist (Bridge.Dialect c g) init :: R.scope c g
  have hinitEx : init = [Stmt.letDecl ["end"] (some (Expr.builtin Op.add
      [Expr.var "proof_cptr", Expr.lit (Literal.number (128 * j))]))] := rfl
  let endv : U256 := BitVec.ofNat 256 (a + 128 * j)
  let Ve : Nat → VEnv (Bridge.Dialect c g) := fun k =>
    VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * k)))
      walk (BitVec.ofNat 256 (w + 128 * k))) "proof_cptr" (BitVec.ofNat 256 (a + 128 * k))
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop := fun Vh sth =>
    ∃ k, k ≤ j ∧ Vh = ("end", endv) :: Ve k ∧
      VEnv.get Vh "proof_cptr" = some (BitVec.ofNat 256 (a + 128 * k)) ∧
      VEnv.get Vh walk = some (BitVec.ofNat 256 (w + 128 * k)) ∧
      VEnv.get Vh "buf_len" = some (BitVec.ofNat 256 (b + 128 * k)) ∧
      VEnv.get Vh "end" = some endv ∧
      sth.env = st.env ∧ sth.halted = st.halted ∧
      bytesAt sth b (128 * k) = cdSlice cd a (128 * k) ∧
      bytesAt sth w (128 * k) = cdSlice cd a (128 * k) ∧
      (∀ i, i < k → g1WordsOk cd (a + 128 * i) = true) ∧
      (∀ x, (x < w ∨ w + 128 * k ≤ x) → (x < b ∨ b + 128 * k ≤ x) →
        sth.memory x = st.memory x)
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop := fun Vend stend o =>
    g1WalkPost V st cd walk j a w b (restore V Vend) stend o
  change ExecStmt (Bridge.Dialect c g) (R.scope c g) V st
    (Stmt.forLoop init cond [] body) V' st' o at hrun
  have hVe0 : Ve 0 = V := by
    have hg : VEnv.get (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * 0)))
        walk (BitVec.ofNat 256 (w + 128 * 0))) "proof_cptr" =
        some (BitVec.ofNat 256 (a + 128 * 0)) := by
      rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := walk)
        (h := fun h => hwalk.1 h.symm)]
      rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "buf_len") (h := by decide)]
      simpa using hpc0
    show VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * 0)))
      walk (BitVec.ofNat 256 (w + 128 * 0))) "proof_cptr" (BitVec.ofNat 256 (a + 128 * 0)) = V
    have hgw : VEnv.get (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * 0)))
        walk = some (BitVec.ofNat 256 (w + 128 * 0)) := by
      rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "buf_len") (h := hwalk.2.1)]
      exact hwv0
    have hgb : VEnv.get V "buf_len" = some (BitVec.ofNat 256 (b + 128 * 0)) := by
      simpa using hbuf0
    rw [t_venv_set_self hg]
    rw [t_venv_set_self hgw]
    rw [t_venv_set_self hgb]
  have hVeLen : ∀ k, (Ve k).length = V.length := by
    intro k
    show (VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * k)))
      walk (BitVec.ofNat 256 (w + 128 * k))) "proof_cptr"
      (BitVec.ofNat 256 (a + 128 * k))).length = V.length
    rw [t_venv_set_length (D := Bridge.Dialect c g),
      t_venv_set_length (D := Bridge.Dialect c g),
      t_venv_set_length (D := Bridge.Dialect c g)]
  have hstep : ∀ Vh sth, Inv Vh sth →
      IterAll (D := Bridge.Dialect c g) funsI cond [] body Inv Q Vh sth := by
    intro Vh sth hInv
    obtain ⟨k, hk_le, hVh, hpc, hwv, hbuf, hend, hEnv, hHalt, hbB, hbW, hWords, hMem⟩ := hInv
    refine ⟨?condHalt, ?exit, ?iter⟩
    · intro st1 hc
      exact (g1Walk_eval_lt_vars_halt_false hc).elim
    · intro cv st1 hc hz
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := g1Walk_eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (a + 128 * k) :=
        Option.some.inj (hxget.symm.trans hpc)
      have hyv : yv = endv := Option.some.inj (hyget.symm.trans hend)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (a + 128 * k)).ult
          (BitVec.ofNat 256 (a + 128 * j))) = (0 : U256) := by
        rw [← hcv]; exact hz
      have hipos : a + 128 * k < 2 ^ 256 := by omega
      have hnpos : a + 128 * j < 2 ^ 256 := by omega
      have hkj : j ≤ k := by
        have := lt_guard_false (i := a + 128 * k) (n := a + 128 * j) hipos hnpos h0
        omega
      have hkeq : k = j := Nat.le_antisymm hk_le hkj
      rw [hkeq] at hVh hpc hwv hbuf hbB hbW hWords hMem
      have hlen : (Ve j).length = V.length := hVeLen j
      have hrest : restore V Vh = Ve j := by
        rw [hVh]
        exact t_restore_cons V (Ve j) endv hlen
      change g1WalkPost V st cd walk j a w b (restore V Vh) st1 .normal
      rw [hst1, hrest]
      refine Or.inr ⟨rfl, hEnv, hHalt, rfl, hbW, hbB, hWords, ?_⟩
      intro x hx1 hx2
      exact hMem x hx1 hx2
    · intro cv st1 hc hnz Vb stb ob hbody
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := g1Walk_eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (a + 128 * k) :=
        Option.some.inj (hxget.symm.trans hpc)
      have hyv : yv = endv := Option.some.inj (hyget.symm.trans hend)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (a + 128 * k)).ult
          (BitVec.ofNat 256 (a + 128 * j))) ≠ (0 : U256) := by
        rw [← hcv]; exact hnz
      have hipos : a + 128 * k < 2 ^ 256 := by omega
      have hnpos : a + 128 * j < 2 ^ 256 := by omega
      have hklt : k < j := by
        have := lt_guard_true (i := a + 128 * k) (n := a + 128 * j) hipos hnpos h0
        omega
      obtain ⟨Vbin, stbb, hbrun, hVbEq, hstbEq⟩ := g1Walk_exec_block_inv hbody
      rw [hVbEq, hstbEq]
      have hbp := g1WalkBody_step (R := R) (c := c) (g := g) cd walk hwalk j a w b
        ha hcd hw hb hdisj err hi lo hcommon hkey (st0 := st) k hklt Vh st1
        ⟨hpc, hwv, hbuf, by rw [hst1, hEnv]; exact hcdat, by rw [hst1]; exact hHalt,
          by rw [hst1]; exact hbB, by rw [hst1]; exact hbW, hWords,
          by intro x hx1 hx2; rw [hst1]; exact hMem x hx1 hx2⟩
      rcases hbp Vbin stbb ob hbrun with ⟨hob, hrev⟩ | ⟨hob, hVbin, hse, hsh, hbB', hbW', hWords', hMem'⟩
      · subst hob
        change g1WalkPost V st cd walk j a w b (restore V (restore Vh Vbin)) stbb .halt
        exact Or.inl ⟨rfl, hrev⟩
      · subst hob
        have hVbin' : Vbin = ("end", endv) :: Ve (k + 1) := by
          rw [hVbin, hVh]
          rw [t_venv_set_cons_ne (D := Bridge.Dialect c g) (h := by decide)]
          rw [t_venv_set_cons_ne (D := Bridge.Dialect c g)
            (h := fun h' => hwalk.2.2 h'.symm)]
          rw [t_venv_set_cons_ne (D := Bridge.Dialect c g) (h := by decide)]
          show ("end", endv) :: VEnv.set (VEnv.set (VEnv.set (VEnv.set (VEnv.set (VEnv.set V
              "buf_len" (BitVec.ofNat 256 (b + 128 * k)))
              walk (BitVec.ofNat 256 (w + 128 * k)))
              "proof_cptr" (BitVec.ofNat 256 (a + 128 * k)))
              "buf_len" (BitVec.ofNat 256 (b + 128 * (k + 1))))
              walk (BitVec.ofNat 256 (w + 128 * (k + 1))))
              "proof_cptr" (BitVec.ofNat 256 (a + 128 * (k + 1))) =
            ("end", endv) :: Ve (k + 1)
          rw [t_venv_set_overwrite V "buf_len" walk "proof_cptr"
            (BitVec.ofNat 256 (b + 128 * k)) (BitVec.ofNat 256 (w + 128 * k))
            (BitVec.ofNat 256 (a + 128 * k))
            (BitVec.ofNat 256 (b + 128 * (k + 1)))
            (BitVec.ofNat 256 (w + 128 * (k + 1)))
            (BitVec.ofNat 256 (a + 128 * (k + 1)))
            (fun h => hwalk.2.1 h.symm) (by decide) (fun h => hwalk.1 h)]
        have hlenVbin : Vbin.length = Vh.length := by
          rw [hVbin', hVh]
          simp [hVeLen]
        have hVb : restore Vh Vbin = ("end", endv) :: Ve (k + 1) := by
          rw [hVbin', hVh]
          simp [restore, hVeLen]
        have hpc1 : VEnv.get (("end", endv) :: Ve (k + 1)) "proof_cptr" =
            some (BitVec.ofNat 256 (a + 128 * (k + 1))) := by
          rw [t_venv_get_cons_ne (D := Bridge.Dialect c g) (h := by decide)]
          change VEnv.get (VEnv.set (VEnv.set (VEnv.set V "buf_len"
              (BitVec.ofNat 256 (b + 128 * (k + 1)))) walk (BitVec.ofNat 256 (w + 128 * (k + 1))))
              "proof_cptr" (BitVec.ofNat 256 (a + 128 * (k + 1)))) "proof_cptr" =
            some (BitVec.ofNat 256 (a + 128 * (k + 1)))
          rw [t_venv_get_set_same (D := Bridge.Dialect c g)]
          rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := walk) (h := fun h => hwalk.1 h.symm)]
          rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "buf_len") (h := by decide)]
          exact hpc0
        have hwv1 : VEnv.get (("end", endv) :: Ve (k + 1)) walk =
            some (BitVec.ofNat 256 (w + 128 * (k + 1))) := by
          rw [t_venv_get_cons_ne (D := Bridge.Dialect c g) (h := fun h => hwalk.2.2 h)]
          change VEnv.get (VEnv.set (VEnv.set (VEnv.set V "buf_len"
              (BitVec.ofNat 256 (b + 128 * (k + 1)))) walk (BitVec.ofNat 256 (w + 128 * (k + 1))))
              "proof_cptr" (BitVec.ofNat 256 (a + 128 * (k + 1)))) walk =
            some (BitVec.ofNat 256 (w + 128 * (k + 1)))
          rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "proof_cptr") (h := fun h => hwalk.1 h)]
          rw [t_venv_get_set_same (D := Bridge.Dialect c g)]
          rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "buf_len") (h := hwalk.2.1)]
          exact hwv0
        have hbuf1 : VEnv.get (("end", endv) :: Ve (k + 1)) "buf_len" =
            some (BitVec.ofNat 256 (b + 128 * (k + 1))) := by
          rw [t_venv_get_cons_ne (D := Bridge.Dialect c g) (h := by decide)]
          change VEnv.get (VEnv.set (VEnv.set (VEnv.set V "buf_len"
              (BitVec.ofNat 256 (b + 128 * (k + 1)))) walk (BitVec.ofNat 256 (w + 128 * (k + 1))))
              "proof_cptr" (BitVec.ofNat 256 (a + 128 * (k + 1)))) "buf_len" =
            some (BitVec.ofNat 256 (b + 128 * (k + 1)))
          rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := "proof_cptr") (h := by decide)]
          rw [t_venv_get_set_ne (D := Bridge.Dialect c g) (x := walk) (h := fun h => hwalk.2.1 h.symm)]
          rw [t_venv_get_set_same (D := Bridge.Dialect c g)]
          exact hbuf0
        have hend1 : VEnv.get (("end", endv) :: Ve (k + 1)) "end" = some endv := by
          simp [VEnv.get, List.find?]
        have hmem1 : ∀ x, (x < w ∨ w + 128 * (k + 1) ≤ x) →
            (x < b ∨ b + 128 * (k + 1) ≤ x) →
            stbb.memory x = st.memory x := by
          intro x hx1 hx2
          have hx1' : x < w ∨ w + 128 * k ≤ x := by
            rcases hx1 with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          have hx2' : x < b ∨ b + 128 * k ≤ x := by
            rcases hx2 with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          rw [hMem' x hx1 hx2, hst1]
          exact hMem x hx1' hx2'
        have hInvNext : Inv (restore Vh Vbin) stbb := by
          refine ⟨k + 1, by omega, hVb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hWords', hmem1⟩
          · rw [hVb]; exact hpc1
          · rw [hVb]; exact hwv1
          · rw [hVb]; exact hbuf1
          · rw [hVb]; exact hend1
          · rw [hse, hst1]; exact hEnv
          · rw [hsh, hst1]; exact hHalt
          · exact hbB'
          · exact hbW'
        intro Vp stp op hpost
        obtain ⟨Vpb, stpb, hpb, hVpEq, hstpEq⟩ := g1Walk_exec_block_inv hpost
        cases hpb with
        | seqNil =>
            constructor
            · intro _
              rw [hVpEq, hstpEq]
              rw [show restore (restore Vh Vbin) (restore Vh Vbin) =
                  restore Vh Vbin from by simp [restore]]
              exact hInvNext
            · intro hop
              cases hop
  cases hrun with
  | forLoop hinit hloop =>
      rw [hinitEx] at hinit
      obtain ⟨ev, hget, hVinit, hstinit⟩ := g1WalkInit_run (c := c) (g := g) j
        (funs := R.scope c g) hinit
      have hev : ev = BitVec.ofNat 256 a := Option.some.inj (hget.symm.trans hpc0)
      have hendv : ev + BitVec.ofNat 256 (128 * j) = endv := by
        rw [hev]
        exact (BitVec.ofNat_add _ _).symm
      rw [hVinit, hstinit] at hloop
      have hInv0 : Inv (("end", ev + BitVec.ofNat 256 (128 * j)) :: V) st := by
        refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hendv, hVe0]
        · rw [hendv]
          rw [t_venv_get_cons_ne (D := Bridge.Dialect c g) (h := by decide)]
          simpa using hpc0
        · rw [hendv]
          rw [t_venv_get_cons_ne (D := Bridge.Dialect c g) (h := fun h => hwalk.2.2 h)]
          simpa using hwv0
        · rw [hendv]
          rw [t_venv_get_cons_ne (D := Bridge.Dialect c g) (h := by decide)]
          simpa using hbuf0
        · rw [hendv]
          simp [VEnv.get, List.find?]
        · rfl
        · rfl
        · simp [bytesAt, readBytes, cdSlice]
        · simp [bytesAt, readBytes, cdSlice]
        · intro i hi; omega
        · intro x _ _; rfl
      exact allRuns_loop (D := Bridge.Dialect c g) (funs := funsI) (c := cond)
        (post := []) (body := body) Inv Q hstep (("end", ev + BitVec.ofNat 256 (128 * j)) :: V)
        st hInv0 _ _ _ hloop
  | forInitHalt hinit =>
      rw [hinitEx] at hinit
      exfalso
      cases hinit with
      | seqCons h1 h2 => cases h2
      | seqStop h1 hne =>
          cases h1 with
          | letHalt he => exact g1Walk_eval_add_var_lit_halt_false he

def transcriptInitBody (tm : Nat) : Block EVM.Op :=
  [yset "buf_len" (ylit tm)]

def transcriptInitInline (tm : Nat) : Block EVM.Op :=
  [yfun "transcript_init" [] ["buf_len"] (transcriptInitBody tm)]

def commonWordBody : Block EVM.Op :=
  [yexpr (yop Op.mstore [yvar "buf_len", yvar "word"]),
   yset "ret" (yop Op.add [yvar "buf_len", ylit 32])]

def commonWordInline : Block EVM.Op :=
  [yfun "common_word" ["buf_len", "word"] ["ret"] commonWordBody]

def squeezeToBody (tm fr : Nat) : Block EVM.Op :=
  [ ylet "h0" (yop Op.keccak256 [ylit tm, yop Op.sub [yvar "buf_len", ylit tm]])
  , yexpr (yop Op.mstore [ylit tm, yvar "h0"])
  , ylet "r" (ylit fr)
  , yexpr (yop Op.mstore [yvar "mptr", yop Op.mod [yvar "h0", yvar "r"]])
  , yset "ret" (yop Op.add [ylit tm, ylit 32]) ]

def squeezeToInline (tm fr : Nat) : Block EVM.Op :=
  [yfun "squeeze_to" ["buf_len", "mptr"] ["ret"] (squeezeToBody tm fr)]

theorem transcriptInit_inline (consts : Inline.Consts) (tm : Nat)
    (h : consts.lookup "TRANSCRIPT_MPTR" = some tm) :
    Inline.inlineContractConstants consts GenAst.emitTranscriptInit =
      transcriptInitInline tm := by
  rw [show Inline.inlineContractConstants consts GenAst.emitTranscriptInit =
      (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
        GenAst.emitTranscriptInit).blks from rfl]
  simp only [GenAst.emitTranscriptInit, transcriptInitInline, transcriptInitBody, GenAst.yfun,
    GenAst.yset, GenAst.ylit, GenAst.yvar, Inline.inlineStep, Inline.exprFuel, Inline.boundOf,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.singleton_append,
    Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3, Inline.inExpr.eq_2,
    h, Option.map_some, List.map_cons, List.map_nil]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 63 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 62 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons, List.foldl_nil,
    List.nil_append, List.singleton_append, Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3,
    Inline.inlineStmtStep.eq_4, Inline.inExpr.eq_2, h, Option.map_some, List.map_cons, List.map_nil]
  rfl

theorem commonWord_inline (consts : Inline.Consts) :
    Inline.inlineContractConstants consts GenAst.emitCommonWord = commonWordInline := by
  rw [show Inline.inlineContractConstants consts GenAst.emitCommonWord =
      (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
        GenAst.emitCommonWord).blks from rfl]
  simp only [GenAst.emitCommonWord, commonWordInline, commonWordBody, GenAst.yfun,
    GenAst.ylet, GenAst.yset, GenAst.ylit, GenAst.yvar, GenAst.yexpr, GenAst.yop,
    Inline.inlineStep, Inline.exprFuel, Inline.boundOf,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.singleton_append, List.cons_append,
    Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_5,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4, Inline.exprFuel, Inline.boundOf,
    Option.map_some, List.map_cons, List.map_nil]
  rfl

theorem squeezeTo_inline (consts : Inline.Consts) (tm fr : Nat)
    (hT : consts.lookup "TRANSCRIPT_MPTR" = some tm)
    (hF : consts.lookup "FR_MODULUS" = some fr) :
    Inline.inlineContractConstants consts GenAst.emitSqueezeTo = squeezeToInline tm fr := by
  rw [show Inline.inlineContractConstants consts GenAst.emitSqueezeTo =
      (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
        GenAst.emitSqueezeTo).blks from rfl]
  simp only [GenAst.emitSqueezeTo, squeezeToInline, squeezeToBody, GenAst.yfun,
    GenAst.ylet, GenAst.yset, GenAst.ylit, GenAst.yvar, GenAst.yexpr, GenAst.yop,
    Inline.inlineStep, Inline.exprFuel, Inline.boundOf,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.singleton_append, List.cons_append,
    Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_4,
    Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    hT, hF, Option.map_some, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 63 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 62 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons, List.foldl_nil,
    List.nil_append, List.singleton_append, List.cons_append,
    Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_4,
    Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    hT, hF, Option.map_some, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rfl

-- the three declarations resolve in R.scope
theorem transcriptInit_lookup (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    ∃ decl, lookupFun (R.scope c g) "transcript_init" = some (decl, R.scope c g) ∧
      decl.params = [] ∧ decl.rets = ["buf_len"] := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem commonWord_lookup (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    ∃ decl, lookupFun (R.scope c g) "common_word" = some (decl, R.scope c g) ∧
      decl.params = ["buf_len", "word"] ∧ decl.rets = ["ret"] := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem squeezeTo_lookup (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    ∃ decl, lookupFun (R.scope c g) "squeeze_to" = some (decl, R.scope c g) ∧
      decl.params = ["buf_len", "mptr"] ∧ decl.rets = ["ret"] := by
  exact ⟨_, rfl, rfl, rfl⟩

set_option maxHeartbeats 2000000 in
theorem transcriptInitBody_runs {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState) (tm : Nat) (htm : tm < 2 ^ 256) :
    AllRuns funs [("buf_len", (0 : U256))] st (transcriptInitBody tm)
      (fun V' st' o => o = .normal ∧
        VEnv.get V' "buf_len" = some (BitVec.ofNat 256 tm) ∧ st' = st) := by
  refine allRuns_of_wp 20 ?_
  set_option wpLets false in
  wp_run
  all_goals
    first
    | rfl
    | (dsimp only []; rfl)
    | (dsimp only []; simp only [touchMemory, litValue_number_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt htm]; rfl)
    | (dsimp only []; simp [VEnv.get, List.find?, litValue_number_nat])
    | (dsimp only []; simp [VEnv.get, List.find?, litValue_number_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt htm])

set_option maxHeartbeats 2000000 in
theorem commonWordBody_runs {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState) (buf word : U256) :
    AllRuns funs [("buf_len", buf), ("word", word), ("ret", (0 : U256))] st commonWordBody
      (fun V' st' o => o = .normal ∧
        VEnv.get V' "ret" = some (buf + BitVec.ofNat 256 32) ∧
        st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, st'.memory x = storeWord st.memory buf.toNat word x)) := by
  refine allRuns_of_wp 20 ?_
  set_option wpLets false in
  wp_run
  all_goals
    first
    | rfl
    | (dsimp only []; rfl)
    | (dsimp only []; simp only [touchMemory, litValue_number_nat, BitVec.toNat_ofNat]; rfl)
    | (dsimp only []; simp [VEnv.get, List.find?, litValue_number_nat])
    | (dsimp only []; simp [VEnv.get, List.find?, litValue_number_nat, BitVec.toNat_ofNat])


/-- The fail call expression halts with a revert for ANY non-halting selector expression. -/
theorem failExpr_any_halt {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {e : Expr EVM.Op}
    {r : EResult (Bridge.Dialect c g)}
    (hlookup : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (hne : ∀ st₀ st₁, EvalExpr (Bridge.Dialect c g) funs V st₀ e (.halt st₁) → False)
    (h : Step (Bridge.Dialect c g) funs V st
      (Code.expr (Expr.call "fail" [e])) (.eres r)) :
    ∃ st₂, r = .halt st₂ ∧ Midfall.LoweringV2.Reverted st₂ := by
  cases h with
  | callOk hargs hlookup' hlen hbody ho =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts =>
          obtain ⟨ho', hrev⟩ := TraceReturn.tr_fail_body hstmts
          rcases ho with hn | hl
          · exact absurd (hn.symm.trans ho') (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
          · exact absurd (hl.symm.trans ho') (by decide : (Outcome.leave : Outcome) ≠ Outcome.halt)
  | callHalt hargs hlookup' hlen hbody =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts =>
          exact ⟨_, rfl, (TraceReturn.tr_fail_body hstmts).2⟩
  | callArgsHalt hargs =>
      exact (TraceReturn.trArgs1_halt_inv hargs (fun st₁ => hne st₁ _)).elim

/-- The fail statement halts with a revert for any non-halting selector. -/
theorem failStmt_reverts {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {e : Expr EVM.Op} {o : Outcome}
    (hlookup : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (hne : ∀ st₀ st₁, EvalExpr (Bridge.Dialect c g) funs V st₀ e (.halt st₁) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.call "fail" [e])) V' st' o) :
    o = .halt ∧ Midfall.LoweringV2.Reverted st' := by
  cases h with
  | exprStmt hex =>
      obtain ⟨st₂, hr, hrev⟩ := failExpr_any_halt hlookup hne hex
      cases hr
  | exprStmtHalt hex =>
      obtain ⟨st₂, hr, hrev⟩ := failExpr_any_halt hlookup hne hex
      cases hr
      exact ⟨rfl, hrev⟩


theorem tp_eval_iszero_lt_vars_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x y : String} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
      (.vals [cv] st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      cv = b2w (b2w (xv.ult yv) = 0) ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := g1Walk_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hlt =>
      cases hnil with
      | argsNil =>
          obtain ⟨xv, yv, hxv, hyv, hcv, hst⟩ := g1Walk_eval_lt_vars_inv hlt
          subst hst
          simp only [Bridge.Dialect, builtinWithExternal, stepOp, un, hcv] at hbi
          cases hbi
          exact ⟨_, _, hxv, hyv, rfl, rfl⟩

theorem tp_eval_iszero_lt_vars_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x y : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
      (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := .iszero)
    (by
      intro a st r hr
      simp only [Bridge.Dialect, builtinWithExternal, stepOp, un] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => g1Walk_eval_lt_vars_halt_false hh) h

theorem tp_eval_iszero_var_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x : String} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var x]) (.vals [cv] st')) :
    ∃ rv, VEnv.get V x = some rv ∧ st' = st ∧ cv = b2w (rv = 0) := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := g1Walk_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hvar =>
      cases hnil with
      | argsNil =>
          cases hvar with
          | var hget =>
              simp only [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
              cases hbi
              exact ⟨_, hget, rfl, rfl⟩

theorem tp_eval_iszero_var_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var x]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := .iszero)
    (by
      intro a st r hr
      simp only [Bridge.Dialect, builtinWithExternal, stepOp, un] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h

theorem lookupFun_nil_scope {D : YulSemantics.Dialect} (funs : FunEnv D) (f : Ident) :
    lookupFun ([] :: funs) f = lookupFun funs f := rfl

/-- The fail body block always halts with a revert (variable selector). -/
theorem tp_failBlock_var_reverts {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {sel : String} {o : Outcome}
    (hlook : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block [Stmt.exprStmt (Expr.call "fail" [Expr.var sel])]) V' st' o) :
    o = .halt ∧ Midfall.LoweringV2.Reverted st' := by
  cases h with
  | block hb =>
      have hlook' : lookupFun (hoist (Bridge.Dialect c g)
            [Stmt.exprStmt (Expr.call "fail" [Expr.var sel])] :: funs) "fail" =
          some (TraceReturn.failFDecl, funs') := by
        rw [show hoist (Bridge.Dialect c g) [Stmt.exprStmt (Expr.call "fail" [Expr.var sel])] = []
          from rfl, lookupFun_nil_scope]
        exact hlook
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
        ⟨V₁, st₁, h₁, _⟩ | ⟨h₁, _⟩
      · obtain ⟨hoh, _⟩ := failStmt_reverts (e := Expr.var sel) hlook' (fun _ _ hh =>
          Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h₁
        exfalso
        exact absurd hoh (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
      · exact failStmt_reverts (e := Expr.var sel) hlook' (fun _ _ hh =>
          Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h₁

/-- The fail body block always halts with a revert (literal selector). -/
theorem tp_failBlock_lit_reverts {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {err : Nat} {o : Outcome}
    (hlook : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number err)])]) V' st' o) :
    o = .halt ∧ Midfall.LoweringV2.Reverted st' := by
  cases h with
  | block hb =>
      have hlook' : lookupFun (hoist (Bridge.Dialect c g)
            [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number err)])] :: funs) "fail" =
          some (TraceReturn.failFDecl, funs') := by
        rw [show hoist (Bridge.Dialect c g)
            [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number err)])] = [] from rfl,
          lookupFun_nil_scope]
        exact hlook
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
        ⟨V₁, st₁, h₁, _⟩ | ⟨h₁, _⟩
      · obtain ⟨hoh, _⟩ := failStmt_reverts (e := Expr.lit (Literal.number err)) hlook'
          (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h₁
        exfalso
        exact absurd hoh (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
      · exact failStmt_reverts (e := Expr.lit (Literal.number err)) hlook' (fun _ _ hh =>
          Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h₁

/-- `if iszero(lt(x, y)) { fail(sel) }`: true `x < y` skips, false runs the fail body. -/
theorem tp_guard_iszero_lt_fail_var {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y sel : String} {xv yv : U256}
    (hlook : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (hx : VEnv.get V x = some xv) (hy : VEnv.get V y = some yv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero
        [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.var sel])]) V' st' o) :
    (xv.ult yv = true → o = .normal ∧ V' = V ∧ st' = st) ∧
      (xv.ult yv = false → o = .halt ∧ Midfall.LoweringV2.Reverted st') := by
  constructor
  · intro hlt
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨x0, y0, hx0, hy0, hcv, -⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        rw [hx] at hx0; rw [hy] at hy0
        injection hx0 with h1; injection hy0 with h2
        subst h1 h2
        rw [hcv, hlt] at hnz
        change (0 : U256) ≠ 0 at hnz
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨-, -, -, -, -, hst⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (tp_eval_iszero_lt_vars_no_halt (x := x) (y := y) hc).elim
  · intro hlt
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨-, -, -, -, -, hst⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        subst hst
        exact tp_failBlock_var_reverts hlook hbody
    | ifFalse hc hz =>
        obtain ⟨x0, y0, hx0, hy0, hcv, hst⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        rw [hx] at hx0; rw [hy] at hy0
        injection hx0 with h1; injection hy0 with h2
        subst h1 h2
        subst hst
        rw [hcv, hlt] at hz
        change (1 : U256) = (0 : U256) at hz
        exact absurd hz (by decide)
    | ifHalt hc => exact (tp_eval_iszero_lt_vars_no_halt (x := x) (y := y) hc).elim

/-- `if iszero(lt(x, y)) { fail(err) }`: literal-selector form. -/
theorem tp_guard_iszero_lt_fail_lit {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y : String} {xv yv : U256} {err : Nat}
    (hlook : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (hx : VEnv.get V x = some xv) (hy : VEnv.get V y = some yv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero
        [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number err)])]) V' st' o) :
    (xv.ult yv = true → o = .normal ∧ V' = V ∧ st' = st) ∧
      (xv.ult yv = false → o = .halt ∧ Midfall.LoweringV2.Reverted st') := by
  constructor
  · intro hlt
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨x0, y0, hx0, hy0, hcv, -⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        rw [hx] at hx0; rw [hy] at hy0
        injection hx0 with h1; injection hy0 with h2
        subst h1 h2
        rw [hcv, hlt] at hnz
        change (0 : U256) ≠ 0 at hnz
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨-, -, -, -, -, hst⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (tp_eval_iszero_lt_vars_no_halt (x := x) (y := y) hc).elim
  · intro hlt
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨-, -, -, -, -, hst⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        subst hst
        exact tp_failBlock_lit_reverts hlook hbody
    | ifFalse hc hz =>
        obtain ⟨x0, y0, hx0, hy0, hcv, hst⟩ := tp_eval_iszero_lt_vars_inv (x := x) (y := y) hc
        rw [hx] at hx0; rw [hy] at hy0
        injection hx0 with h1; injection hy0 with h2
        subst h1 h2
        subst hst
        rw [hcv, hlt] at hz
        change (1 : U256) = (0 : U256) at hz
        exact absurd hz (by decide)
    | ifHalt hc => exact (tp_eval_iszero_lt_vars_no_halt (x := x) (y := y) hc).elim

/-- `if iszero(x) { fail(sel) }`: `x = 0` runs the fail body, nonzero skips. -/
theorem tp_guard_iszero_var_fail_var {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x sel : String} {rv : U256}
    (hlook : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (hx : VEnv.get V x = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var x])
        [Stmt.exprStmt (Expr.call "fail" [Expr.var sel])]) V' st' o) :
    (rv = 0 → o = .halt ∧ Midfall.LoweringV2.Reverted st') ∧
      (rv ≠ 0 → o = .normal ∧ V' = V ∧ st' = st) := by
  constructor
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        subst hst
        exact tp_failBlock_var_reverts hlook hbody
    | ifFalse hc hz =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        rw [hcv, hrv] at hz
        change (1 : U256) = (0 : U256) at hz
        exact absurd hz (by decide)
    | ifHalt hc => exact (tp_eval_iszero_var_no_halt (x := x) hc).elim
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        rw [hcv] at hnz
        rw [show decide (rv = 0) = false from decide_eq_false hrv] at hnz
        exact (hnz rfl).elim
    | ifFalse hc hz =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (tp_eval_iszero_var_no_halt (x := x) hc).elim

/-- `if iszero(x) { fail(err) }`: literal-selector form. -/
theorem tp_guard_iszero_var_fail_lit {c : ExternalCalls} {g : ExternalGas}
    {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {rv : U256} {err : Nat}
    (hlook : lookupFun funs "fail" = some (TraceReturn.failFDecl, funs'))
    (hx : VEnv.get V x = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var x])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number err)])]) V' st' o) :
    (rv = 0 → o = .halt ∧ Midfall.LoweringV2.Reverted st') ∧
      (rv ≠ 0 → o = .normal ∧ V' = V ∧ st' = st) := by
  constructor
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        subst hst
        exact tp_failBlock_lit_reverts hlook hbody
    | ifFalse hc hz =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        rw [hcv, hrv] at hz
        change (1 : U256) = (0 : U256) at hz
        exact absurd hz (by decide)
    | ifHalt hc => exact (tp_eval_iszero_var_no_halt (x := x) hc).elim
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        rw [hcv] at hnz
        rw [show decide (rv = 0) = false from decide_eq_false hrv] at hnz
        exact (hnz rfl).elim
    | ifFalse hc hz =>
        obtain ⟨v0, hx0, hst, hcv⟩ := tp_eval_iszero_var_inv (x := x) hc
        rw [hx] at hx0
        injection hx0 with hv
        subst hv
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (tp_eval_iszero_var_no_halt (x := x) hc).elim


def tpSqueezeAbsorbed {c : ExternalCalls} {g : ExternalGas}
    (st : EvmState) (tm : Nat) (buf : U256) : List UInt8 :=
  readBytes st.memory (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number tm)))
    (BitVec.toNat (buf - (Bridge.Dialect c g).litValue (Literal.number tm)))

def tpSqueezeH0 {c : ExternalCalls} {g : ExternalGas}
    (st : EvmState) (tm : Nat) (buf : U256) : U256 :=
  st.env.keccakOf (tpSqueezeAbsorbed (c := c) (g := g) st tm buf)

def tpSqueezeState {c : ExternalCalls} {g : ExternalGas}
    (st : EvmState) (tm fr : Nat) (buf mptr : U256) : EvmState :=
  let st1 := touchMemory st (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number tm)))
    (BitVec.toNat (buf - (Bridge.Dialect c g).litValue (Literal.number tm)))
  let h0 := tpSqueezeH0 (c := c) (g := g) st tm buf
  let st2 := { touchMemory st1 (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number tm))) 32 with
    memory := storeWord st1.memory (BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number tm))) h0 }
  { touchMemory st2 mptr.toNat 32 with
    memory := storeWord st2.memory mptr.toNat
      (if (Bridge.Dialect c g).litValue (Literal.number fr) = (0 : U256) then (0 : U256)
       else h0 % (Bridge.Dialect c g).litValue (Literal.number fr)) }

set_option maxHeartbeats 4000000 in
theorem squeezeToBody_runs (c : ExternalCalls) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState) (tm fr : Nat) (buf mptr : U256) :
    AllRuns funs [("buf_len", buf), ("mptr", mptr), ("ret", (0 : U256))] st (squeezeToBody tm fr)
      (fun V' st' o => o = .normal ∧
        VEnv.get V' "ret" = some ((Bridge.Dialect c g).litValue (Literal.number tm) +
          (Bridge.Dialect c g).litValue (Literal.number 32)) ∧
        st' = tpSqueezeState (c := c) (g := g) st tm fr buf mptr) := by
  refine allRuns_of_wp 20 ?_
  set_option wpLets false in
  wp_run
  all_goals
    first
    | rfl
    | (dsimp only []; rfl)
    | (dsimp only []; simp [VEnv.get, List.find?, tpSqueezeState, tpSqueezeH0, tpSqueezeAbsorbed,
        touchMemory]; try rfl)

theorem toNat_sub_ofNat_of_le (p : U256) (k : Nat) (hk : k < 2 ^ 256) (hle : k ≤ p.toNat) :
    (p - BitVec.ofNat 256 k).toNat = p.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have h : 2 ^ 256 - k + p.toNat = (p.toNat - k) + 2 ^ 256 := by omega
  rw [h, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem tpSqueezeState_memory (c : ExternalCalls) (g : ExternalGas)
    (st : EvmState) (tm fr : Nat) (buf mptr : U256)
    (htm : tm < 2 ^ 256) (hbuf : buf.toNat < 2 ^ 256) (hle : tm ≤ buf.toNat) :
    (tpSqueezeState (c := c) (g := g) st tm fr buf mptr).memory =
      storeWord
        (storeWord st.memory tm
          (st.env.keccakOf (readBytes st.memory tm (buf.toNat - tm))))
        mptr.toNat
        (if (BitVec.ofNat 256 fr) = (0 : U256) then (0 : U256)
         else st.env.keccakOf (readBytes st.memory tm (buf.toNat - tm)) %
           BitVec.ofNat 256 fr) := by
  have htmv : BitVec.toNat ((Bridge.Dialect c g).litValue (Literal.number tm)) = tm := by
    rw [show (Bridge.Dialect c g).litValue (Literal.number tm) = BitVec.ofNat 256 tm from rfl,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt htm]
  have hfrv : (Bridge.Dialect c g).litValue (Literal.number fr) = BitVec.ofNat 256 fr := rfl
  have hsubmod : (2 ^ 256 - tm + buf.toNat) % 2 ^ 256 = buf.toNat - tm := by
    have h := toNat_sub_ofNat_of_le buf tm htm hle
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htm] at h
    exact h
  dsimp [tpSqueezeState, tpSqueezeH0, tpSqueezeAbsorbed]
  rw [htmv]
  have hpow : (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 := rfl
  rw [hpow]
  rw [hsubmod]
  simp only [touchMemory]
  rfl


theorem t_restore_set {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {V : VEnv D} {x : Ident} {a : D.Value} :
    restore V (VEnv.set V x a) = VEnv.set V x a := by
  unfold restore
  rw [t_venv_set_length]
  simp

set_option maxHeartbeats 4000000 in
theorem commonWordBody_runs_env {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState) (buf word : U256) :
    AllRuns funs [("buf_len", buf), ("word", word), ("ret", (0 : U256))] st commonWordBody
      (fun V' st' o => o = .normal ∧
        V' = VEnv.set [("buf_len", buf), ("word", word), ("ret", (0 : U256))] "ret"
          (buf + BitVec.ofNat 256 32) ∧
        VEnv.get V' "ret" = some (buf + BitVec.ofNat 256 32) ∧
        st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, st'.memory x = storeWord st.memory buf.toNat word x)) := by
  refine allRuns_of_wp 20 ?_
  set_option wpLets false in
  wp_run
  all_goals
    first
    | rfl
    | (dsimp only []; rfl)
    | (dsimp only []; simp [VEnv.get, List.find?, touchMemory])

theorem eval_args_two_vars_exists {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x y : String} {vals : List U256}
    (h : EvalArgs (Bridge.Dialect c g) funs V st
      [Expr.var x, Expr.var y] (.vals vals st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      vals = [xv, yv] ∧ st' = st := by
  cases h with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil htail =>
          cases hnil with
          | argsNil =>
              cases hhead with
              | var hxv =>
                  cases htail with
                  | var hyv =>
                      exact ⟨_, _, hxv, hyv, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
theorem commonWord_stmt_var_contract {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {decl : FDecl (Bridge.Dialect c g)}
    {cenv : FunEnv (Bridge.Dialect c g)} {name : String} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {buf word : U256}
    (hlook : lookupFun funs "common_word" = some (decl, cenv))
    (hbody : decl.body = commonWordBody)
    (hparams : decl.params = ["buf_len", "word"])
    (hrets : decl.rets = ["ret"])
    (hbuf : VEnv.get V "buf_len" = some buf)
    (hword : VEnv.get V name = some word) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.assign ["buf_len"] (Expr.call "common_word" [Expr.var "buf_len", Expr.var name]))
      (fun V0 st0 => V0 = V ∧ st0 = st)
      (fun V0 st0 V' st' o => o = .normal ∧
        V' = VEnv.set V "buf_len" (buf + BitVec.ofNat 256 32) ∧
        st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, st'.memory x = storeWord st.memory buf.toNat word x)) := by
  intro V0 st0 hpre V' st' o hrun
  obtain ⟨hV0, hst0⟩ := hpre
  cases hrun with
  | assignVal he hlen =>
      cases he with
      | callOk hargs hlook' harglen hbodyrun ho =>
          rw [hlook] at hlook'
          cases hlook'
          obtain ⟨buf0, word0, hbuf0, hword0, hvals, hst1⟩ :=
            eval_args_two_vars_exists hargs
          subst hvals
          have hbuf0' : buf0 = buf := by
            rw [hV0] at hbuf0
            exact Option.some.inj (hbuf0.symm.trans hbuf)
          have hword0' : word0 = word := by
            rw [hV0] at hword0
            exact Option.some.inj (hword0.symm.trans hword)
          obtain ⟨Vb, stb, hstmts, hVend, hstb⟩ := g1Walk_exec_block_inv hbodyrun
          rw [hparams, hrets] at hVend
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hVend
          have hb := commonWordBody_runs_env (c := c) (g := g)
            (funs := hoist (Bridge.Dialect c g) commonWordBody :: cenv) st0 buf0 word0
          rw [hbody, hparams, hrets] at hstmts
          rw [hst1] at hstmts
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hstmts
          obtain ⟨-, hVb, hret, henv, hhalt, hmem⟩ := hb Vb stb _ hstmts
          rw [hst0] at henv hhalt hmem
          rw [← hstb] at henv hhalt hmem
          have hVb' : Vb = VEnv.set [("buf_len", buf0), ("word", word0),
              ("ret", (Bridge.Dialect c g).zero)] "ret" (buf0 + BitVec.ofNat 256 32) := hVb
          have hrestore : restore [("buf_len", buf0), ("word", word0),
              ("ret", (Bridge.Dialect c g).zero)] Vb = Vb := by
            rw [hVb']
            exact t_restore_set
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · rw [hV0, hVend, hrestore, hrets]
            simp only [List.map_cons, List.map_nil]
            rw [hret]
            simp only [Option.getD_some]
            rw [hbuf0']
            exact t_setMany_one (D := Bridge.Dialect c g) V "buf_len" _
          · exact henv
          · exact hhalt
          · rw [← hbuf0', ← hword0']
            exact hmem
  | assignHalt he =>
      cases he with
      | callHalt hargs hlook' harglen hbodyrun =>
          rw [hlook] at hlook'
          cases hlook'
          obtain ⟨buf0, word0, hbuf0, hword0, hvals, hst1⟩ :=
            eval_args_two_vars_exists hargs
          subst hvals
          obtain ⟨Vb, stb, hstmts, hVend, hstb⟩ := g1Walk_exec_block_inv hbodyrun
          rw [hparams, hrets] at hVend
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hVend
          have hb := commonWordBody_runs_env (c := c) (g := g)
            (funs := hoist (Bridge.Dialect c g) commonWordBody :: cenv) st0 buf0 word0
          rw [hbody, hparams, hrets] at hstmts
          rw [hst1] at hstmts
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hstmts
          obtain ⟨hon, -⟩ := hb Vb stb Outcome.halt hstmts
          cases hon
      | callArgsHalt hargs =>
          exact (Midfall.LoweringV2.Blocks.EcPairing.args_vars_ne_halt
            (D := Bridge.Dialect c g) ["buf_len", name] hargs).elim


theorem args_var_lit_ne_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x : String} {n : Nat}
    (h : Step (Bridge.Dialect c g) funs V st
      (.args [Expr.var x, Expr.lit (Literal.number n)]) (.eres (.halt st'))) : False := by
  cases h with
  | argsRestHalt h' =>
      cases h' with
      | argsRestHalt h'' => cases h''
      | argsHeadHalt _ hh => cases hh
  | argsHeadHalt _ hh => cases hh

theorem eval_args_var_lit_exists {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x : String} {n : Nat} {vals : List U256}
    (h : EvalArgs (Bridge.Dialect c g) funs V st
      [Expr.var x, Expr.lit (Literal.number n)] (.vals vals st')) :
    ∃ xv, VEnv.get V x = some xv ∧ vals = [xv, BitVec.ofNat 256 n] ∧ st' = st := by
  cases h with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil hlit =>
          cases hnil with
          | argsNil =>
              cases hhead with
              | var hxv =>
                  cases hlit with
                  | lit =>
                      exact ⟨_, hxv, rfl, rfl⟩

theorem commonWord_stmt_lit_contract {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {decl : FDecl (Bridge.Dialect c g)}
    {cenv : FunEnv (Bridge.Dialect c g)} {n : Nat} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {buf : U256}
    (hlook : lookupFun funs "common_word" = some (decl, cenv))
    (hbody : decl.body = commonWordBody)
    (hparams : decl.params = ["buf_len", "word"])
    (hrets : decl.rets = ["ret"])
    (hbuf : VEnv.get V "buf_len" = some buf) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.assign ["buf_len"] (Expr.call "common_word" [Expr.var "buf_len", Expr.lit (Literal.number n)]))
      (fun V0 st0 => V0 = V ∧ st0 = st)
      (fun V0 st0 V' st' o => o = .normal ∧
        V' = VEnv.set V "buf_len" (buf + BitVec.ofNat 256 32) ∧
        st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, st'.memory x = storeWord st.memory buf.toNat (BitVec.ofNat 256 n) x)) := by
  intro V0 st0 hpre V' st' o hrun
  obtain ⟨hV0, hst0⟩ := hpre
  cases hrun with
  | assignVal he hlen =>
      cases he with
      | callOk hargs hlook' harglen hbodyrun ho =>
          rw [hlook] at hlook'
          cases hlook'
          obtain ⟨buf0, hbuf0, hvals, hst1⟩ :=
            eval_args_var_lit_exists hargs
          subst hvals
          have hbuf0' : buf0 = buf := by
            rw [hV0] at hbuf0
            exact Option.some.inj (hbuf0.symm.trans hbuf)
          obtain ⟨Vb, stb, hstmts, hVend, hstb⟩ := g1Walk_exec_block_inv hbodyrun
          rw [hparams, hrets] at hVend
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hVend
          have hb := commonWordBody_runs_env (c := c) (g := g)
            (funs := hoist (Bridge.Dialect c g) commonWordBody :: cenv) st0 buf0 (BitVec.ofNat 256 n)
          rw [hbody, hparams, hrets] at hstmts
          rw [hst1] at hstmts
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hstmts
          obtain ⟨-, hVb, hret, henv, hhalt, hmem⟩ := hb Vb stb _ hstmts
          rw [hst0] at henv hhalt hmem
          rw [← hstb] at henv hhalt hmem
          have hVb' : Vb = VEnv.set [("buf_len", buf0), ("word", (BitVec.ofNat 256 n)),
              ("ret", (Bridge.Dialect c g).zero)] "ret" (buf0 + BitVec.ofNat 256 32) := hVb
          have hrestore : restore [("buf_len", buf0), ("word", (BitVec.ofNat 256 n)),
              ("ret", (Bridge.Dialect c g).zero)] Vb = Vb := by
            rw [hVb']
            exact t_restore_set
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · rw [hV0, hVend, hrestore, hrets]
            simp only [List.map_cons, List.map_nil]
            rw [hret]
            simp only [Option.getD_some]
            rw [hbuf0']
            exact t_setMany_one (D := Bridge.Dialect c g) V "buf_len" _
          · exact henv
          · exact hhalt
          · rw [← hbuf0']
            exact hmem
  | assignHalt he =>
      cases he with
      | callHalt hargs hlook' harglen hbodyrun =>
          rw [hlook] at hlook'
          cases hlook'
          obtain ⟨buf0, hbuf0, hvals, hst1⟩ :=
            eval_args_var_lit_exists hargs
          subst hvals
          obtain ⟨Vb, stb, hstmts, hVend, hstb⟩ := g1Walk_exec_block_inv hbodyrun
          rw [hparams, hrets] at hVend
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hVend
          have hb := commonWordBody_runs_env (c := c) (g := g)
            (funs := hoist (Bridge.Dialect c g) commonWordBody :: cenv) st0 buf0 (BitVec.ofNat 256 n)
          rw [hbody, hparams, hrets] at hstmts
          rw [hst1] at hstmts
          simp only [List.zip_cons_cons, List.zip_nil_left, bindZeros, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append] at hstmts
          obtain ⟨hon, -⟩ := hb Vb stb Outcome.halt hstmts
          cases hon
      | callArgsHalt hargs =>
          exact (args_var_lit_ne_halt hargs).elim




/-! ### ROW.TP.4 - scalar-loop vocabulary -/

/-- The instance loop's `success` fold: `and`-accumulate the canonicality bits. -/
def g1SuccessFold (rv s : U256) (ws : List U256) : U256 :=
  ws.foldl (fun acc w => acc &&& b2w (w.ult rv)) s

theorem g1SuccessFold_nil (rv s : U256) : g1SuccessFold rv s [] = s := rfl

theorem g1SuccessFold_cons (rv s w : U256) (ws : List U256) :
    g1SuccessFold rv s (w :: ws) = g1SuccessFold rv (s &&& b2w (w.ult rv)) ws := rfl

/-- The words appended into the transcript buffer, starting at `buf + 32*j`. -/
def g1AppendWords (mem : Nat → UInt8) (buf : Nat) : List U256 → Nat → (Nat → UInt8)
  | [], _ => mem
  | w :: ws, j => g1AppendWords (storeWord mem (buf + 32 * j) w) buf ws (j + 1)

theorem g1AppendWords_nil (mem : Nat → UInt8) (buf j : Nat) :
    g1AppendWords mem buf [] j = mem := rfl

theorem g1AppendWords_cons (mem : Nat → UInt8) (buf j : Nat) (w : U256) (ws : List U256) :
    g1AppendWords mem buf (w :: ws) j =
      g1AppendWords (storeWord mem (buf + 32 * j) w) buf ws (j + 1) := rfl

/-- The instance loop's source words: one calldata word per instance, stride 32. -/
def g1InstanceWords (cd : Bytes) (start N : Nat) : List U256 :=
  (List.range N).map (fun j => cdWord cd (start + 32 * j))

theorem g1InstanceWords_length (cd : Bytes) (start N : Nat) :
    (g1InstanceWords cd start N).length = N := by
  simp [g1InstanceWords]

theorem g1InstanceWords_get? (cd : Bytes) (start N j : Nat) (hj : j < N) :
    (g1InstanceWords cd start N)[j]? = some (cdWord cd (start + 32 * j)) := by
  simp [g1InstanceWords, hj]

/-- **THE SEM LEAF.** From a staged boundary at `.vk` every run reverts or exits normally in
    `TpPost`. LEAF ROW.TP.7 (glue of ROW.TP.2-5 along `tpEvents`). Evidence :788-796, statement
    verbatim with `hpins : SimPins R` -> `hcodec : G1CodecHeadlineLaws R.E.g1`.

    DEPENDENCY, NAMED AND OPEN: ROW.TP.3 (four helper summaries), ROW.TP.4 (three scalar loops),
    ROW.TP.5 (the fold), ROW.TP.2 and ROW.TP.6 - all unissued (QUEUE 95h/95i/95j). -/
theorem tp_computes (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.transcriptParser)
      (fun V st => StageInv R H vkAddr cd Checkpoint.vk V st)
      (fun _ _ V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ TpPost R H vkAddr cd V' st')) := by
  sorry

/-- **`tp_agrees` MINUS `Agree`.** Five of the six `StageInv .transcript` conjuncts are the
    projections of `TpPost` (`LeanRaw .transcript` is `rawDecode … |>.isSome = true` and
    `Mirror .transcript` is `MirrorAt`, both definitionally). Only `Agree` — the existence of
    the Lean prefix for every decoding and `Inv` at it — is left. -/
theorem tp_agrees_of_agree (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (h : TpPost R H vkAddr cd V st)
    (hagree : Agree R H cd Checkpoint.transcript V st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st := by
  obtain ⟨hframe, hsucc, hbase, hraw, hmirror, hslots⟩ := h
  exact ⟨hframe, hsucc, hbase, hraw, hmirror, hagree⟩

/-- **`Agree .transcript` FROM ITS TWO HALVES.** The existence half is
    `leanStage_transcript_exists_of_algebraRun` (the named SIM.10 clause); the second argument is
    the `Inv .transcript` assembly at the stage's own `padSnap` witness. This is exactly the shape
    `tp_agrees` consumes, with the two remaining obligations named. -/
theorem agree_transcript_of_exists_and_inv (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hx : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
        ∃ S, leanStage R H inst ms Checkpoint.transcript = .ok S)
    (hinv : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
        ∀ S, leanStage R H inst ms Checkpoint.transcript = .ok S →
          Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params
            Checkpoint.transcript R.pv S V st) :
    Agree R H cd Checkpoint.transcript V st := by
  intro ms instW inst hdec
  obtain ⟨S, hS⟩ := hx ms instW inst hdec
  exact ⟨S, hS, hinv ms instW inst hdec S hS⟩

/-- **THE `Inv .transcript` ASSEMBLY.** Given the parser post (`BaseInv`, `MirrorAt`,
    `XcriptSlots`) and the commitment half `XcriptG1`, the invariant at the stage's own
    `padSnap` witness holds: `XcriptSlots` supplies the ten scalar slots, `MirrorAt`
    supplies the q-eval pointer, `XcriptG1` supplies the four G1 windows, and
    `BaseInv .transcript` supplies the earlier checkpoints. No other fact is used. -/
theorem invAt_transcript_of_xcriptG1
    (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hpost : TpPost R H vkAddr cd V st)
    (hG1 : XcriptG1 R H cd st)
    (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (hdec : Decoded R cd ms instW inst)
    (S : Snapshot p G₁ G₂ Gₜ)
    (hS : leanStage R H inst ms Checkpoint.transcript = .ok S) :
    Inv R.E R.params Checkpoint.transcript R.pv S V st := by
  obtain ⟨hframe, hsucc, hbase, hraw, hmirror, hslots⟩ := hpost
  unfold leanStage at hS
  change (snapshotXcriptRun R.E H R.vk inst ms R.nSets >>=
    (fun x => Except.ok (padSnap x { lLast := 0, lBlind := 0, l0 := 0 } none #[]))) =
      Except.ok S at hS
  obtain ⟨x, hx, hS'⟩ := except_bind_ok _ _ hS
  have hseq : S = padSnap x { lLast := 0, lBlind := 0, l0 := 0 } none #[] :=
    (Except.ok.inj hS').symm
  rw [hseq]
  obtain ⟨hθ, hβ, hγ, htr, hy, hx0, hx1, hx2, hx3, hx4⟩ := hslots ms instW inst hdec x hx
  obtain ⟨hadv, hquot, hfcom, hpi⟩ := hG1 ms instW inst hdec x hx
  have hadv' : holdsG1s R.E st (ptrAddr R.pv.memory.adviceCommsMptrBase)
      (x.trace.adviceCommitments[0]?.getD #[]) = true := by
    simpa using hadv
  have hq := hmirror.qEvalCptr
  have hacc : (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)).acc.isSome = false := rfl
  have hpairvk : (Checkpoint.vk == Checkpoint.pairing) = false := by decide
  have hbase' := hbase
  unfold BaseInv at hbase'
  rw [show baseCk Checkpoint.transcript = Checkpoint.vk from rfl] at hbase'
  have checkpoint_le_def : ∀ a b : Checkpoint, (a ≤ b) = (a.idx ≤ b.idx) := fun a b => rfl
  simp [Midfall.Lowering.Inv, Midfall.Lowering.InvAt, checkpoint_le_def, Checkpoint.idx,
    padSnap, hacc, hpairvk] at hbase' ⊢
  have hlag : ¬ Checkpoint.lagrange ≤ Checkpoint.transcript := by decide
  have hqck : ¬ Checkpoint.quotient ≤ Checkpoint.transcript := by decide
  have hpcs : ¬ Checkpoint.pcs ≤ Checkpoint.transcript := by decide
  have hpair : (Checkpoint.transcript == Checkpoint.pairing) = false := by decide
  have hvk : Checkpoint.vk ≤ Checkpoint.transcript := by decide
  have hstart : Checkpoint.start ≤ Checkpoint.transcript := by decide
  simp only [hlag, hqck, hpcs, hpair, hvk, hstart,
    hθ, hβ, hγ, htr, hy, hx0, hx1, hx2, hx3, hx4, hadv', hquot, hfcom, hpi, hq] at ⊢
  simpa [Midfall.Lowering.Inv, Midfall.Lowering.InvAt, checkpoint_le_def, Checkpoint.idx,
    padSnap, BaseInv, baseCk, hacc] using hbase'

/-- **ROW.TP.8 SHARPENED: `tp_agrees` FROM THE NAMED SIM.10 CLAUSE + THE `Inv` ASSEMBLY.** The
    first hypothesis is the missing parser-side `prepare_logSlots` analogue
    (`XcriptAlgebraRun`); the second is `Inv .transcript` at the stage's own witness, i.e. the
    slot/mirror assembly the evidence attributes to `XcriptSlots` + `MirrorAt` + `SimPins.eipRt`.
    Nothing else stands between `TpPost` and `StageInv .transcript`. -/
theorem tp_agrees_of_xcript_of_inv (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (hpost : TpPost R H vkAddr cd V st)
    (h : XcriptAlgebraRun R H cd)
    (hinv : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
        ∀ S, leanStage R H inst ms Checkpoint.transcript = .ok S →
          Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params
            Checkpoint.transcript R.pv S V st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st :=
  tp_agrees_of_agree R H vkAddr cd V st hpost
    (agree_transcript_of_exists_and_inv R H cd V st
      (leanStage_transcript_exists_of_algebraRun R hR hcodec H cd h) hinv)

/-- **`tp_agrees_of_xcript` WITH ITS `hinv` DISCHARGED FROM THE COMMITMENT HALF.**
    The existence half is `leanStage_transcript_exists_of_algebraRun`; the `Inv` half is
    `invAt_transcript_of_xcriptG1`, so the only decode-relative extra datum is
    `XcriptG1` (the four G1 windows' decode→`toEip` assembly). This is the consumer
    `tp_agrees_of_xcript`'s `hinv` was waiting for. -/
theorem tp_agrees_of_xcriptG1 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (hpost : TpPost R H vkAddr cd V st)
    (h : XcriptAlgebraRun R H cd) (hG1 : XcriptG1 R H cd st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st :=
  tp_agrees_of_agree R H vkAddr cd V st hpost
    (agree_transcript_of_exists_and_inv R H cd V st
      (leanStage_transcript_exists_of_algebraRun R hR hcodec H cd h)
      (fun ms instW inst hdec S hS =>
        invAt_transcript_of_xcriptG1 R H vkAddr cd V st hpost hG1
          ms instW inst hdec S hS))

/-- **`tp_agrees` FROM THE NAMED SCHEDULE AND THE COMMITMENT HALF.** The fixed `tp_agrees`
    has no room for the schedule or `XcriptG1`; this is its schedule-carrying consumer.
    `XcriptAlgebraRun` is produced by `xcriptAlgebraRun_of_schedule` and spent by
    `tp_agrees_of_xcriptG1`. -/
theorem tp_agrees_of_schedule (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (hpost : TpPost R H vkAddr cd V st)
    (hsched : XcriptSchedule R H cd)
    (hnum : R.cfg.numInstances < 2 ^ 31)
    (hG1 : XcriptG1 R H cd st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st :=
  tp_agrees_of_xcriptG1 R hR hcodec H vkAddr cd V st hpost
    (xcriptAlgebraRun_of_schedule R hR hcodec H cd hsched hnum) hG1


/-- **`tp_agrees` FROM THE TWO PLAN COUNTS AND THE COMMITMENT HALF.** The
    schedule is now derived from `PlanReadCounts` and `Decoded`; the only other
    named inputs are `hnum` and Calldata's `XcriptG1`. -/
theorem tp_agrees_of_planReadCounts (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (hpost : TpPost R H vkAddr cd V st)
    (hc : PlanReadCounts R) (hnum : R.cfg.numInstances < 2 ^ 31)
    (hG1 : XcriptG1 R H cd st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st :=
  tp_agrees_of_xcriptG1 R hR hcodec H vkAddr cd V st hpost
    (xcriptAlgebraRun_of_planReadCounts R hR hcodec H cd hc hnum) hG1

/-- **`tp_agrees_of_xcript` WITH `hinv` DISCHARGED.** The whole-`Inv` hypothesis is
    replaced by `XcriptG1`, the four commitment holds; the scalar slots, q-eval
    pointer and earlier checkpoints are proved by `invAt_transcript_of_xcriptG1`.
    `tp_agrees_of_xcript_of_inv` keeps the older whole-`Inv` form for callers that
    already have it. -/
theorem tp_agrees_of_xcript (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (hpost : TpPost R H vkAddr cd V st)
    (h : XcriptAlgebraRun R H cd) (hG1 : XcriptG1 R H cd st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st :=
  tp_agrees_of_xcriptG1 R hR hcodec H vkAddr cd V st hpost h hG1

/-- **THE ALG LEAF.** `TpPost` is the staged boundary at `.transcript`: `Agree` follows from
    `xcript_total` (the Lean prefix exists), `MirrorAt` with `SimPins.eipRt` (the commitment
    windows hold `toEip` of the decoded points) and `XcriptSlots`. LEAF ROW.TP.8. No Yul.
    Evidence :798-805, statement verbatim with the same hypothesis move.

    THE REDUCTION IS LANDED: `tp_agrees_of_xcript` proves this row from `XcriptAlgebraRun` (the
    named SIM.10 parser-side clause, §3b) plus the `Inv .transcript` assembly, and
    `tp_agrees_of_agree` isolates the latter. THE SCHEDULE LAYER IS NOW LANDED:
    `xcriptSchedule_of_planReadCounts` derives the fine read schedule from the coarse
    decoded split and `PlanReadCounts` (the two plan-count/VK-schedule equations), and
    `xcriptAlgebraRun_of_planReadCounts` spends it. The key-side instance-query bound is
    now `WellFormed.instanceQueriesBound` (D-GATE15(c)), so the old `hinstQ` premise is
    gone, and `PlanReadCounts` itself is PROVED downstream in
    `EndToEndAlgebra.planReadCounts_of_valid` (`planPrefixG1_eq` + `planNumEvals_eq`).
    THE FIXED STATEMENT'S RESIDUAL is therefore exactly the calldata bound `hnum` and
    Calldata's `XcriptG1`; `EndToEndAlgebra.tp_agrees_of_valid` is the fixed row's fully
    wired consumer (`ValidV3` + `hnum` + `XcriptG1`). `Decoded` gives
    `cd.size = proofEnd + 32 + 32 * numInstances` (`numInstances_lt_of_cd_size`), so a
    calldata-size bound `cd.size < 2^36` would supply `hnum`; no such bound is in the
    tree (`EntryFrameV3.cdSize` is `< 2^256`; `SupportedInput.sizeBound` is `< 2^64` on
    the generator input, not on `cd`). The proof of the fixed statement itself cannot be
    imported here: `EndToEndAlgebra` imports this file.
    THE `Inv .transcript` HALF IS LANDED as `invAt_transcript_of_xcriptG1`, and
    `tp_agrees_of_xcriptG1` replaces `hinv` by the exact commitment datum `XcriptG1` (the
    decode→`toEip` assembly: advice/quotient-limb `holdsG1s`, `fCom`/`pi` `holdsG1`). Its
    producer is the value half of A11's `runsAll_readAlgebra` plus `MirrorAt`/`eipRoundtrip`;
    ROW.TP.6's `MirrorAt` half is `tp_events_slots` above. -/
theorem tp_agrees (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    (vkAddr : U256) (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (h : TpPost R H vkAddr cd V st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st := by
  sorry

/-- **THE POISONED HALF.** No statement raises `success`; the last statement reverts on
    `success = 0`. LEAF ROW.TP.9. Evidence :807-814, statement verbatim.

    DEPENDENCY, NAMED AND OPEN: ROW.TP.4's three scalar loops and ROW.TP.2's walk loops, which say
    every loop ends normally from a poisoned boundary (their preconditions do not read the loop's
    computed values). Both unissued. -/
theorem tp_poison (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.transcriptParser)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ _ st' o => o = .halt ∧ Midfall.LoweringV2.Reverted st') := by
  sorry

/-- **THE GENERIC ROW, PROVED from the three leaves.** Evidence :816-827, proof VERBATIM (the
    twelve-line argument the evidence marks PROVED). Nothing is added: the row is the two
    `StmtsContractAll` conjuncts of `BlockSim`, the soundness one split into revert / `TpPost` /
    (never offered) poisoned, the poisoned one discharged by `tp_poison`. At
    `q = .transcriptParser` the boundary is `.transcript` definitionally, so `tp_agrees` hands
    over exactly `exitSimAt`'s second disjunct. -/
theorem tp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (_hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.transcriptParser H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    rcases tp_computes R hR hcodec H vkAddr cd _ g V st hpre V' st' o hrun with hrev | ⟨ho, hpost⟩
    · exact Or.inl hrev
    · exact Or.inr (Or.inl ⟨ho, tp_agrees R hR hcodec H vkAddr cd V' st' hpost⟩)
  · intro V st hpre V' st' o hrun
    exact Or.inl (tp_poison R hR H vkAddr cd _ g V st hpre V' st' o hrun)

/-- **THE GENERIC PROGRESS ROW.** LEAF ROW.TP.10. Evidence :829-835, statement verbatim with the
    same hypothesis move: `R.Valid` -> `ValidV3 R`, `SimPins R` -> `G1CodecHeadlineLaws R.E.g1`
    and the seven-law `G1CodecLaws` read as the four-law headline (RECON.2 step 3).

    DEPENDENCY, NAMED AND OPEN: every ROW.TP child above, plus the existence half of the walk
    loops (ROW.TP.2's loop rule with a normal arm). -/
theorem tp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.transcriptParser H vkAddr product cd := by
  sorry

/-! ## 5. W12 - THE WITNESSES AND FALSIFIERS -/

/-- **W12 WITNESS FOR `tp_events_slots` - THE FILTERED SCHEDULE IS NONEMPTY AT EVERY LAYOUT.** The
    final `g1 "PI_MPTR"` event is in the schedule at every layout and every count, and `TEv.slot?`
    maps it to a slot, so the left side of ROW.TP.6 is a nonempty list and the equality is not the
    empty-list tautology. PROVED. -/
theorem tp_events_slots_witness_nonempty (L : ProofCalldataLayout) :
    (tpEvents 0 [] 0 0 0 0 false L).filterMap TEv.slot? ≠ [] := by
  intro h
  have hmem : TEv.g1 "PI_MPTR" ∈ tpEvents 0 [] 0 0 0 0 false L := by
    simp [tpEvents]
  have hb : WireSlot.g1 ∈ (tpEvents 0 [] 0 0 0 0 false L).filterMap TEv.slot? :=
    List.mem_filterMap.mpr ⟨TEv.g1 "PI_MPTR", hmem, rfl⟩
  rw [h] at hb
  exact List.not_mem_nil hb

/-- **W12 FALSIFIER FOR `tp_events_slots` - THE FILTERMAP IS NOT THE IDENTITY.** `TEv.slot?` drops
    the three `word` events and all squeezes, so the equality is a relation between a schedule and
    a slot list and not `List.map some`. A reading that skipped the filter would be refuted by the
    first event of the schedule. PROVED. -/
theorem tp_events_slots_falsifier_not_every_event_reads_a_slot :
    ¬ (∀ e : TEv, (TEv.slot? e).isSome = true) := by
  intro h
  exact Bool.false_ne_true (h TEv.word)

/-- **W12 FALSIFIER FOR `g1walk_loop_sem` - THE POST DEMANDS THE WALK'S BYTES.** The empty block
    ends normally from `V = []` and leaves the (initial, zeroed) memory alone, while the walk's
    post says the walk window holds `cdSlice cd 0 128`. At `cd = ByteArray.empty` the right side
    is empty and the left is 128 bytes, so the post fails; the walk post is not satisfied by
    fall-through and the leaf is not vacuous. PROVED by SIZE (the `ByteArray` equality itself is
    opaque). The walk's own side condition `hwalk` is assumed, so this is a falsifier under the
    leaf's own hypotheses. -/
theorem g1walk_loop_sem_falsifier_empty_block (R : Render p G₁ G₂ Gₜ)
    {c : ExternalCalls} {g : ExternalGas} (walk : String)
    (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end") :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) (funs := R.scope c g) ([] : Block EVM.Op)
      (fun _ _ => True)
      (fun V st V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          V' = VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (0 + 128 * 1)))
            walk (BitVec.ofNat 256 (1 + 128 * 1))) "proof_cptr"
              (BitVec.ofNat 256 (0 + 128 * 1)) ∧
          bytesAt st' 1 (128 * 1) = cdSlice ByteArray.empty 0 (128 * 1) ∧
          bytesAt st' 0 (128 * 1) = cdSlice ByteArray.empty 0 (128 * 1) ∧
          (∀ i, i < 1 → g1WordsOk ByteArray.empty (0 + 128 * i) = true) ∧
          (∀ x, (x < 1 ∨ 1 + 128 * 1 ≤ x) → (x < 0 ∨ 0 + 128 * 1 ≤ x) →
            st'.memory x = st.memory x))) := by
  intro Hc
  have hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) ([] : VEnv (Bridge.Dialect c g))
      EvmState.init [] [] EvmState.init .normal := Step.seqNil
  have hpost := Hc [] EvmState.init trivial [] EvmState.init .normal hrun
  rcases hpost with ⟨h1, _⟩ | ⟨_, _, _, _, hbytes, _⟩
  · exact absurd h1 (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  · have hsz1 : (bytesAt EvmState.init 1 128).size = 128 := by
      simp [bytesAt, readBytes, EvmState.init, ByteArray.size]
    have hsz2 : (cdSlice ByteArray.empty 0 128).size = 0 := by
      simp [cdSlice, ByteArray.size]
    have hne : bytesAt EvmState.init 1 128 ≠ cdSlice ByteArray.empty 0 128 := by
      intro h
      have hc := congrArg ByteArray.size h
      rw [hsz1, hsz2] at hc
      exact absurd hc (by decide)
    exact hne hbytes

/-- **W12 FALSIFIER FOR `tp_computes` - THE EMPTY BLOCK'S NORMAL EXIT IS NOT `TpPost`.**
    `TpPost` carries `success = 1`; the empty block from `V = []` ends normally with
    `VEnv.get [] "success" = none`. So the post is not `True` and the pre is load-bearing.
    PROVED. -/
theorem tp_computes_falsifier_empty_block (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas} :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) (funs := R.scope c g) ([] : Block EVM.Op)
      (fun _ _ => True)
      (fun _ _ V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ TpPost R H vkAddr cd V' st')) := by
  intro Hc
  have hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g)
      ([] : VEnv (Bridge.Dialect c g)) EvmState.init [] [] EvmState.init .normal := Step.seqNil
  have hpost := Hc [] EvmState.init trivial [] EvmState.init .normal hrun
  rcases hpost with ⟨h1, _⟩ | ⟨_, hpost⟩
  · exact absurd h1 (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  · have hsucc := hpost.2.1
    simp [VEnv.get] at hsucc

/-- **W12 FALSIFIER FOR `tp_agrees` - `StageInv .transcript` DEMANDS `success = 1`.** At
    `V = []` the conclusion is false whatever the premise, so the implication's conclusion is
    not `True`. PROVED. -/
theorem tp_agrees_falsifier_no_success (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas} :
    ¬ StageInv R H vkAddr cd Checkpoint.transcript
      ([] : VEnv (Bridge.Dialect c g)) EvmState.init := by
  intro h
  have hsucc := h.2.1
  simp [VEnv.get] at hsucc

/-- **W12 FALSIFIER FOR `tp_poison` - THE EMPTY BLOCK DOES NOT REVERT.** "Every run reverts" is
    false of fall-through, so the leaf is about the parser's own 44 statements. PROVED. -/
theorem tp_poison_falsifier_empty_block (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) (funs := R.scope c g) ([] : Block EVM.Op)
      (fun _ _ => True)
      (fun _ _ _ st' o => o = .halt ∧ Midfall.LoweringV2.Reverted st') := by
  intro Hc
  have hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g)
      ([] : VEnv (Bridge.Dialect c g)) EvmState.init [] [] EvmState.init .normal := Step.seqNil
  have hpost := Hc [] EvmState.init trivial [] EvmState.init .normal hrun
  exact absurd hpost.1 (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)

/-- **W12 FALSIFIER FOR `tp_blockSim` - A `ret` IS NOT ONE OF THE ROW'S ARMS.** A block that
    RETURNS is a halt, it is not a revert, it is not `exitSimAt` at a non-terminal partial (which
    demands `.normal`), and it is not the poisoned arm. So the row refuses a program that stops
    early with a success payload - the v1 defect class at the row. PROVED. -/
theorem tp_blockSim_falsifier_return_is_not_the_post
    (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} (H : Hash) (vkAddr : U256)
    (cd : Bytes) :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) (funs := R.scope c g)
        [yexpr (yop Op.ret [ylit 0, ylit 0])] (fun _ _ => True)
        (fun _ _ V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
          exitSimAt R H vkAddr cd (fun k V st => StageInv R H vkAddr cd k V st)
            Partial.transcriptParser V' st' o ∨
          (Partial.transcriptParser ≠ Partial.traceReturn ∧ o = .normal ∧
            Poisoned R H vkAddr cd V' st')) := by
  intro Hc
  have hargs : Step (Bridge.Dialect c g) (R.scope c g) ([] : VEnv (Bridge.Dialect c g))
      EvmState.init (.args [ylit 0, ylit 0]) (.eres (.vals [0, 0] EvmState.init)) := by
    exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  have hbi : (Bridge.Dialect c g).Builtin Op.ret [0, 0] EvmState.init
      (.halt { EvmState.init with halted := some (.ret, []) }) := by
    show stepOp Op.ret [0, 0] EvmState.init = some _
    rfl
  have hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] EvmState.init
      [yexpr (yop Op.ret [ylit 0, ylit 0])] [] Midfall.Lowering.QuotientInterp.retState
        .halt :=
    Step.seqStop (D := Bridge.Dialect c g) (rest := [])
      (Step.exprStmtHalt (D := Bridge.Dialect c g) (e := yop Op.ret [ylit 0, ylit 0])
        (st1 := Midfall.Lowering.QuotientInterp.retState)
        (Step.builtinHalt (D := Bridge.Dialect c g) (args := [ylit 0, ylit 0]) (argvals := [0, 0])
          (st1 := EvmState.init) (st2 := Midfall.Lowering.QuotientInterp.retState) hargs hbi))
      (by decide)
  have hpost := Hc [] EvmState.init trivial [] Midfall.Lowering.QuotientInterp.retState
    .halt hrun
  rcases hpost with hrev | hsim | hpo
  · exact Midfall.Lowering.QuotientInterp.retState_not_Reverted hrev.2
  · exact absurd hsim.1 (by decide : ¬ ((Outcome.halt : Outcome) = Outcome.normal))
  · exact absurd hpo.2.1 (by decide : ¬ ((Outcome.halt : Outcome) = Outcome.normal))

/-- **W12 FALSIFIER FOR `tp_blockProgS` - TOTALITY IS NOT THE REVERT ARM.** A block that only
    reverts has no normal run, so it fails the progress contract while satisfying the simulation
    one. PROVED. -/
theorem tp_blockProgS_falsifier_reverting_block_is_not_total
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    ¬ StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (funs := ([] : FunEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))))
        [yexpr (yop Op.revert [ylit 0, ylit 0])] (fun _ _ => True)
        (fun _ _ V' st' o => exitProgAt R H vkAddr cd
          (fun _ _ _ => True) Partial.transcriptParser V' st' o) := by
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

/-! ## 6. THE ACCEPTANCE PRINTS -/

/-! The rows quantify over the render and name no fixture: `R : Render p G₁ G₂ Gₜ` is a binder of
    every statement, the only partial named is `Partial.transcriptParser`, and the schedule, the
    layout and the table are binders. `poseidonRender` does not appear in this file. -/
#check @Midfall.LoweringV3.TranscriptRows.tp_blockSim
#check @Midfall.LoweringV3.TranscriptRows.tp_blockProgS
#check @Midfall.LoweringV3.TranscriptRows.tp_computes
#check @Midfall.LoweringV3.TranscriptRows.tp_agrees
#check @Midfall.LoweringV3.TranscriptRows.tp_poison
#check @Midfall.LoweringV3.TranscriptRows.xcript_total_of_algebraRun
#check @Midfall.LoweringV3.TranscriptRows.leanStage_transcript_exists_of_algebraRun
#check @Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcript
#check @Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcript_of_inv
#check @Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcriptG1
#check @Midfall.LoweringV3.TranscriptRows.xcriptAlgebraRun_of_schedule
#check @Midfall.LoweringV3.TranscriptRows.tp_agrees_of_schedule
#check @Midfall.LoweringV3.TranscriptRows.invAt_transcript_of_xcriptG1
#check @Midfall.LoweringV3.TranscriptRows.inline_g1WalkLoop

#cone_sorries Midfall.LoweringV3.TranscriptRows.tp_blockSim
#cone_sorries Midfall.LoweringV3.TranscriptRows.tp_blockProgS

#assert_axioms Midfall.LoweringV3.TranscriptRows.coordLt_pBase [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1WordsOk_of_checks [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.wordFrom_eq_cdWord [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.coordCheck_to_nat [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonG1_inline [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonG1Inline_runs [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.ushr128_eq_zero_iff [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.and_mask128_eq_self [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.toNat_add_ofNat [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.coordCheck_lift [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytesAt_calldatacopy_cdSlice [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytesAt_append [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.cdSlice_append [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.cdSlice_eq_of_bytesTake [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.holdsG1_of_mirrorsSection [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decodeSlots_g1_inv [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decodeSlots_append [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decodeSlots_split [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decodeSlots_g1_provenance [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.takeCommitmentSection_cursor [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.foldlM_take_cursor [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.foldlM_lookups_prefix [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.foldlM_lookups_cursor [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.foldlM_take_sum_byteLen [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.foldlM_lookups_sum_byteLen [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.takeCommitmentSection_start [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.wordSection_start_end [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.fromProtocol_starts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.fromProtocol_quotientComm [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytesAt_size_local [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.cdSlice_size_of_le [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytesAt_frame_eq_of_window [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.holdsG1s_section [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1WalkCT_sound [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1WalkTail_contract [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1Call_contract [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.t_venv_set_overwrite [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.t_restore_cons [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.cdSize_of_envelope [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.cdSlice_length_of_envelope [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_slice [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.inline_g1WalkLoop [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_inExpr_eq_of_shadowed [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.inlineScan_single [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.shadowed_append_right [propext] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.shadowed_append_self [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_events_slots_witness_nonempty [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_events_slots_falsifier_not_every_event_reads_a_slot [propext] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1walk_loop_sem_falsifier_empty_block [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_computes_falsifier_empty_block [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_falsifier_no_success [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_poison_falsifier_empty_block [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_blockSim_falsifier_return_is_not_the_post [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_blockProgS_falsifier_reverting_block_is_not_total [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_read_g1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_trash_readCommitted [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_trashcans_fold [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceTrashcans_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_tmReadN_g1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_perm_readProductCommitments [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTracePermutations_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_logup_readMultiplicities [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_lookupMultiplicities_fold [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceLookupMultiplicities_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.nbParallelLookupsPerChunk_ok_of_wf [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.rustChunks_ok [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.chunkByDegree_ok_of_wf [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readN_go_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readN_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tmReadN_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.scatterIndexed_ok_of_cover [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.mem_zip_of_mem [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_tmReadN_fr [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_tmReadN_fr [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readFixedEvals_guard [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_readFixedEvalsRead [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.i32Abs_ok_of_ne_min [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.listInsertAt_ok_of_le [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.countP_take_le [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.countP_not_add [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.i32Abs_zero [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.zip_range_fst [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.fpSimple_filter_cons [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_fixed_fold_aux [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.filter_snd_zip_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_fixed_fold [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_readFixedEvals [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_readFixedEvals [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_read_fr [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_permutationCommon [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_trashEval [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.rotBounds_zero [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readAlgebra_rotBounds_zero [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_logupEval [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.RunsAll.toRunsAllP [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_fold_forIn_yield [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_forIn_yield [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.permSeg [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.permSeg_succ [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.flatMap_permSeg [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_permutationEval [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_readAlgebraAdviceEvals [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.computeInnerProduct_ok_of_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readAlgebraOneInstanceQuery [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_readAlgebraOneInstanceQuery_committed [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_readAlgebraOneInstanceQuery_notCommitted [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_instanceQueries_mapM [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_instanceEvals [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.batchInvert_fst_size_direct [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.lIRange_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.asI32_eq_of_lt [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.wrapI32_eq_of_nonneg_of_lt [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.negI32_zero [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.le_foldl_max_of_mem_or_le [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.maxInstanceLen [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.zeroRotations [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.maxInstanceLen_bound [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.zeroRotations_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readAlgebra_rotations_zero [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.lIS_slice_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readAlgebra_instanceSlice_safe [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.mem_phaseCols_of_adviceColumnPhase [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.adviceCols_cover [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdviceProofRead_cover [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.parseTraceAdviceProofRead_singleton [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.parseTraceAdvicePhase_zero_eq [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdvicePhase_cover [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdvicePhases_cover [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdvicePhases_cover_all [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_adviceScatter [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceAdviceBlock [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.lookupChunkNum [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.ledgerPairs [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.ledgerRows [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.ledgerPairs_push [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.ledgerRows_push [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.chunkNum_eq [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_lookupMultiplicities_fold [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.RunsAllP.congr [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_lookupMultiplicities_fold_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_lookupMultiplicities_fold_both [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceLookupMultiplicities_one_both [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceTail [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceTail_advice [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceWireBody_advice [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTrace_advice [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceWireBody_sizes [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTrace_one_sizes [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.parseTrace_run_of_ms_sizes [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.map_slot_split [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.map_slot_eq_replicate_g1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.map_slot_eq_replicate_fr [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.map_slot_eq_singleton_g1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decoded_coarse_split [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decoded_split_of_plan [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.parseTrace_run_of_ms_sizes_rest [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.wireMsgs_tail [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.snapshotAlgebraRun_ok_of_schedule [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.mapM_option_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.instOfWords?_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decoded_inst_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.numInstances_lt_of_cd_size [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.XcriptSchedule [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcriptAlgebraRun_of_schedule [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_of_schedule [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.exists_blocks_of_sum_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.list_split_six [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.list_split_seven [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.planPrefixG1Count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.planNumEvals [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.plan_numPointSets_eq_nSets [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.instanceQueries_index_eq_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcriptSchedule_of_planReadCounts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcriptAlgebraRun_of_planReadCounts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_of_planReadCounts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceLookupMultiplicities_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.parseTraceWireBody [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceTail [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceWireBody [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceWireBody [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTrace_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.parseTrace_run_of_ms [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.snapshotTraceRun_ok_of_ms [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_mapM_groups [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_permutationsEvaluated [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_rowsEvaluated [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_lookupsEvaluated [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_trashcansEvaluated [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_readAlgebra [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.readN_g1_wire_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_tmReadN_g1_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.length_flatMap_phaseCols [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdvicePhase_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdvicePhases_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_readAlgebra_quotient_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.scatStep_fold_range_shift [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.scatStep_fold_zip_range [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.mapM_id_map_some [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.scatterIndexed_zip_range [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_adviceScatter_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceAdviceBlock_values [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.exists_split_fr_prefix [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.ms_split_plan [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.decoded_ms_split [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytes_prefix_cancel [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytes_append_cancel_left [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytes_suffix_cancel [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.snapshotAlgebraRun_buffer [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.snapshotXcriptRun_fields_of_tail [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcript_tail_fCom_pi [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcript_advice_value [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcript_quotient_value [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.advicePhaseTotal_not_columnOrder [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.wireMsgs_map_fr [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.wireMsgs_g1_singleton [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.RunsAllP.bind_nil [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.RunsAll.bind_nil [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTracePermutations_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_trashcansFold [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceTrashcans_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_logup_readCommitment [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.logupEvalSum [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.logupEvalSum_push [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.sum_map_add_three [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_lookupCommitments_row_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.rowEvalSum [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.rowsEvalSum [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.rowsEvalSum_push [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_lookupCommitments_rows_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.sum_rows_flatMap [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.rowEvalSum_eq [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.sum_rows_rowEvalSum_eq [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.lookupChunkSum_add_three [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_parseTraceLookupCommitments_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceLookupMultiplicities_one_of_wf [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_fmap [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.RunsAllP.toRunsAll [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.RunsAllP.bind [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAllP_tmReadN_g1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_hashInto [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_absorb_committed [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_absorb_instance [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_logup_readCommitment [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_lookupCommitments_row [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_lookupCommitments_rows [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceLookupCommitments [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceAdviceProofRead [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceAdvicePhase [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceAdvicePhases [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.runsAll_parseTraceAdvicePhases_one [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcript_total_at [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.xcript_total_of_algebraRun [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.leanStage_transcript_exists_at [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.leanStage_transcript_exists_of_algebraRun [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.agree_transcript_of_exists_and_inv [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcript_of_inv [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcript [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.invAt_transcript_of_xcriptG1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcriptG1 [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1WalkBody_step [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1walk_loop_sem [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.transcriptInit_inline [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonWord_inline [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.squeezeTo_inline [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.transcriptInit_lookup [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonWord_lookup [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.squeezeTo_lookup [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.transcriptInitBody_runs [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonWordBody_runs [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.failExpr_any_halt [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.failStmt_reverts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_eval_iszero_lt_vars_inv [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_eval_iszero_lt_vars_no_halt [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_eval_iszero_var_inv [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_eval_iszero_var_no_halt [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.lookupFun_nil_scope [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_failBlock_var_reverts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_failBlock_lit_reverts [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_guard_iszero_lt_fail_var [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_guard_iszero_lt_fail_lit [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_guard_iszero_var_fail_var [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_guard_iszero_var_fail_lit [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.squeezeToBody_runs [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.toNat_sub_ofNat_of_le [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.tpSqueezeState_memory [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.t_restore_set [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonWordBody_runs_env [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.eval_args_two_vars_exists [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonWord_stmt_var_contract [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.args_var_lit_ne_halt [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.eval_args_var_lit_exists [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonWord_stmt_lit_contract [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1SuccessFold_nil [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1SuccessFold_cons [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1AppendWords_nil [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1AppendWords_cons [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1InstanceWords_length [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1InstanceWords_get? [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.TranscriptRows

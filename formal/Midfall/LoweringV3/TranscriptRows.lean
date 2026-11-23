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

/-- `xcript_total` at one fixed decoded message list, directly from the tail clause. -/
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

/-- **THE WALK LOOP (all runs), ONE LEMMA FOR SIX SECTIONS.** Bound = `j`, the section's frame
    count. Every run reverts (a frame fails the range check), or ends normally having absorbed the
    `j` frames, copied them to the walk window, and advanced the three cursors; every frame passed
    `g1WordsOk`. LEAF ROW.TP.2 (loop rule GEN.3 + the `common_uncompressed_g1` summary). Evidence
    :737-760, statement verbatim.

    DEPENDENCY, NAMED AND OPEN: ROW.TP.3's `common_uncompressed_g1` helper summary (issued only by
    ROW.TP step 1, QUEUE row 95h) and T3.5's `cdSlice` arithmetic. Neither is in the tree. -/
theorem g1walk_loop_sem (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (cd : Bytes) (walk : String) (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end")
    (j a w b : Nat) (ha : a + 128 * j ≤ cd.size) (hcd : cd.size < 2 ^ 256)
    (hw : w + 128 * j < 2 ^ 256) (hb : b + 128 * j < 2 ^ 256)
    (hdisj : w + 128 * j ≤ b ∨ b + 128 * j ≤ w) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) [GenAst.g1WalkLoop walk (128 * j)]
      (fun V st => st.env.calldata = cd.data.toList ∧
        VEnv.get V "proof_cptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V walk = some (BitVec.ofNat 256 w) ∧
        VEnv.get V "buf_len" = some (BitVec.ofNat 256 b))
      (fun V st V' st' o => (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          V' = VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * j)))
            walk (BitVec.ofNat 256 (w + 128 * j))) "proof_cptr" (BitVec.ofNat 256 (a + 128 * j)) ∧
          bytesAt st' w (128 * j) = cdSlice cd a (128 * j) ∧
          bytesAt st' b (128 * j) = cdSlice cd a (128 * j) ∧
          (∀ i, i < j → g1WordsOk cd (a + 128 * i) = true) ∧
          (∀ x, (x < w ∨ w + 128 * j ≤ x) → (x < b ∨ b + 128 * j ≤ x) →
            st'.memory x = st.memory x))) := by
  sorry

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

/-- **ROW.TP.8 SHARPENED: `tp_agrees` FROM THE NAMED SIM.10 CLAUSE + THE `Inv` ASSEMBLY.** The
    first hypothesis is the missing parser-side `prepare_logSlots` analogue
    (`XcriptAlgebraRun`); the second is `Inv .transcript` at the stage's own witness, i.e. the
    slot/mirror assembly the evidence attributes to `XcriptSlots` + `MirrorAt` + `SimPins.eipRt`.
    Nothing else stands between `TpPost` and `StageInv .transcript`. -/
theorem tp_agrees_of_xcript (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
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

/-- **THE ALG LEAF.** `TpPost` is the staged boundary at `.transcript`: `Agree` follows from
    `xcript_total` (the Lean prefix exists), `MirrorAt` with `SimPins.eipRt` (the commitment
    windows hold `toEip` of the decoded points) and `XcriptSlots`. LEAF ROW.TP.8. No Yul.
    Evidence :798-805, statement verbatim with the same hypothesis move.

    THE REDUCTION IS LANDED: `tp_agrees_of_xcript` proves this row from `XcriptAlgebraRun` (the
    named SIM.10 parser-side clause, §3b) plus the `Inv .transcript` assembly, and
    `tp_agrees_of_agree` isolates the latter. DEPENDENCY, NAMED AND OPEN: `XcriptAlgebraRun` is a
    DATA clause, not a theorem of `ValidV3` + `Decoded` (no `parseTrace`/`readAlgebra`/`snapshotAlgebraRun`
    existence theorem exists; the width schedule is pinned but conditional, see §3b), and the
    `Inv .transcript` half still needs the decode→`toEip` commitment bridge. ROW.TP.6's `MirrorAt`
    half is `tp_events_slots` above. -/
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
#check @Midfall.LoweringV3.TranscriptRows.inline_g1WalkLoop

#cone_sorries Midfall.LoweringV3.TranscriptRows.tp_blockSim
#cone_sorries Midfall.LoweringV3.TranscriptRows.tp_blockProgS

#assert_axioms Midfall.LoweringV3.TranscriptRows.coordLt_pBase [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.g1WordsOk_of_checks [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.commonG1_inline [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.TranscriptRows.bytesAt_calldatacopy_cdSlice [propext, Classical.choice, Quot.sound] native []
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
#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcript [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.TranscriptRows

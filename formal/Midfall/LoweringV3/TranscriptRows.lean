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
-- 'XcriptSlots', 'TpPost'), the child ROW.TP.1 ('inline_g1WalkLoop', PROVED), the W12
-- witness/falsifier pair each new hole needs, and the row glue 'tp_blockSim' which is PROVED from
-- the three SEM/ALG leaves by the evidence's own twelve-line argument. 'tp_blockProgS' is the
-- tenth leaf and is stated, not proved.
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

/-- The section facts `fromProtocol` gives, in one record so the row's algebra can take them as a
    single hypothesis. -/
structure TpLayoutFacts (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout) : Prop where
  adviceItemBytes : ∀ s, s ∈ L.advicePhases → s.itemBytes = Midfall.Generator.g1Bytes
  adviceByteLen : ∀ s, s ∈ L.advicePhases →
    s.byteLen = s.itemCount * Midfall.Generator.g1Bytes
  adviceLen : L.advicePhases.length = meta_.protocol.numUserAdvices.length
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hadv.2.1 s hs).1
  · intro s hs
    exact (hadv.2.1 s hs).2
  · rw [hadvLen]
    simp
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

    PG-PARSER IS NOW PROVED, NOT A GAP: `tp_planFacts` (the plan's meta and layout are the
    generator's, and the model's parser facts are computed from them), `tp_fromProtocol` (every
    section's count, width and byte length) and `userPhasesOf_advice` (the phase table index for
    index) are all theorem of `ValidV3.generated` alone. WHAT IS LEFT, exactly: the two per-phase
    lists `meta_.numUserAdvices` and `meta_.numUserChallenges` both come from
    `ProtocolPlan.remapping numPhase` at the same `numPhase`, so they have equal length
    (`remapping_nums_length` is proved); extracting that equation from
    `ProtocolPlan.fromConstraintSystem` is the remaining peel, and then the `slots` sum algebra
    (`flatMap_replicate_eq`-style) finishes the leaf. The F1 witness and the falsifier are
    `docs/plans/V3-evidence/lean/soundness/GeneratorRowsWitness.lean:124,129`; the generic W12
    pair is section 5 below. -/
theorem tp_events_slots (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.tpEvents.filterMap TEv.slot? =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots := by
  sorry

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

/-- **THE ALG LEAF.** `TpPost` is the staged boundary at `.transcript`: `Agree` follows from
    `xcript_total` (the Lean prefix exists), `MirrorAt` with `SimPins.eipRt` (the commitment
    windows hold `toEip` of the decoded points) and `XcriptSlots`. LEAF ROW.TP.8. No Yul.
    Evidence :798-805, statement verbatim with the same hypothesis move.

    DEPENDENCY, NAMED AND OPEN: SIM.10's `xcript_total` is NOT IN THE TREE (grep finds it only in
    WideningStages.lean's prose), and ROW.TP.6's `MirrorAt` half is `tp_events_slots` above. The
    card's own VERIFY FIRST is SIM.10 closed; it is not. -/
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
#check @Midfall.LoweringV3.TranscriptRows.inline_g1WalkLoop

#cone_sorries Midfall.LoweringV3.TranscriptRows.tp_blockSim
#cone_sorries Midfall.LoweringV3.TranscriptRows.tp_blockProgS

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

end Midfall.LoweringV3.TranscriptRows

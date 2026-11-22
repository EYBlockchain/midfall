-- |
-- Midfall.LoweringV3.TranscriptRows
--
-- ROW.TP (WP A6): the transcriptParser row's VOCABULARY, its NAMED LEAVES, and the PROVED GLUE
-- `tp_blockSim`. PORTED from 'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean' section 6
-- (:635-835), which does not compile (RECON.3) - a copy, not an import, exactly as
-- QuotientRows.lean does for ROW.Q and LagrangeRows.lean does for T3.9.
--
-- WHAT THIS FILE IS, AND WHAT IT IS NOT. It lands the ROW.TP statements at the ONE row shape
-- (D-P74 item 2: 'BlockSim'/'BlockProgS' over 'StageInv'), the four-list schedule vocabulary the
-- SEM children are stated in ('TEv', 'tpWalk', 'tpEvents', 'TEv.slot?', 'Render.tpEvents',
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
--     normally without advancing the cursors, so the post is not vacuous).
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

/-! ## 4. THE NAMED LEAVES -/

/-- **THE READ SCHEDULE IS THE LAYOUT'S SLOT LIST.** The parser reads, in order, exactly the slots
    `rawSlots` walks. LEAF ROW.TP.6 (ALG, list induction, no Yul). Evidence :706-715, statement
    verbatim with `R.Valid` -> `ValidV3 R`.

    PREMISE GAP PG-PARSER. Nothing in `ValidV3` states the equation between the MODEL's parser
    facts (`R.model.userPhases`, `.lookupHPlusAcc`, the three meta counts, the flag) and the
    PLAN's `proofLayout`; the two are joined only through `generateVerifierFromPlan`, which no
    landed lemma unfolds at this shape. The card says: write it as one lemma statement with its F1
    witness and STOP; do not add a hypothesis. This is that statement. The F1 witness and the
    falsifier are `docs/plans/V3-evidence/lean/soundness/GeneratorRowsWitness.lean:124,129`; the
    generic W12 pair is section 5 below. -/
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

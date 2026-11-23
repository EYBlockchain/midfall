/-
  Midfall.LoweringV3.PcsRows

  ROW.PCS (WP A9/A10) - THE FIRST PROVED CHILD, `decode_exists` (ROW.PCS.9 / SIM.12), ported from
  `docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean:1005` at the V3 reading. This file lands
  ONLY proved material; it adds no `sorry`, no hypothesis to a row/bundle/root/ValidV3, and it does
  NOT touch `Rows.lean`'s two pcs leaves.

  ## The A9 -> A8/QVM dependency: NOT LOGICAL (measured, not inferred)

  The QUEUE lists A9 after A8. For the PCS BLOCK that ordering is schedule, not proof dependency:

  * `R.slice .pcs = sliceOf R.pv R.model .pcs` (`LoweringV2/Statements.lean:171`), i.e.
    `Inline.inlineContractConstants (constTableOf R.model)
       (GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .pcs)`
    (`LoweringV2/Program.lean:145`).
  * `emitPartialM` differs from `emitPartial` ONLY on `.quotientLin`
    (`GenAstDispatch.lean:239-254`; `emitPartialM_eq_on_the_other_arms`, PROVED), and
    `emitPartial ... .pcs = emitPcsFromPlan` (`:203-209`).
  * `emitPcsFromPlan` is `computationsAst R.pv.meta_ R.pv.dat R.pv.memory ...`
    (`GenAstDispatch.lean:145-152`). `GenAstPcs.lean` imports `Generator.Kzg`, `Lowering.GenAst`
    and `Generator.YulGolden` only; it contains no `batch_invert`/`batchInvert` occurrence and no
    reference to any `QuotientInterp`/`Qvm*` declaration (`grep -n 'batch_invert\|batchInvert'
    Midfall/Lowering/GenAstPcs.lean` -> empty; `grep -n 'quotient'` -> only the LIMB COUNT of the
    PCS's own block 5, :40/:379/:778/:790/:863).
  * The row's postcondition vocabulary `StageInv`/`BlockSim`/`BlockProgS`
    (`LoweringV2/Stages.lean:171-245`) is defined before any V3 quotient file and reads `Inv`
    (`Lowering/Inv.lean:824`), whose `.pcs` clause is the five PCS-written slots (fEval, v,
    finalCom, pairingLhs, pairingRhs) - all written by PCS itself, none by quotientLin.
  * A5/`batch_invert_summary` is a LAGRANGE helper (the lagrange slice is its only caller:
    `Partials.lean:1806-1809` `[("fail", .finalPairing), ("scalar_inv", .pcs), ...]`); PCS's
    helper is `scalar_inv`, at `GenAst.lean:447`. Nothing in the pcs block needs `batch_invert`.

  Conclusion: a `pcs_blockSim`/`pcs_blockProgS` proof may cite A2's shared leaves (run
  decomposition/scans) and B2/REF's codec laws for `Holds.g1Msm1`/`g1Add`, but not any A8/QVM
  artifact. The `A8` entry is an ordering constraint on the same worker lane, not a premise.

  ## What is proved here

  `decode_exists`: a raw walk whose every G1 frame decodes lifts to `Decoded`. The proof is Lean
  only: `rawDecode`'s instance guard gives `instOfWords?`, and `decodeCalldata_eq_raw` +
  `decodeCalldata_isSome_iff` (both in `Lowering/Stage.lean`) supply the decoding. No semantics,
  no fixture (D-P71), no `native_decide`.

  ## What is NOT here yet

  ROW.PCS.2 is PROVED (`pcs_b2_sem`, section 8): the block-2 loop walks of section 6 and the
  inliner alignment of section 4.1 compose into the evidence's block-2 statement. The block SEM
  leaves 1/3/4/5/6, the coverage invariant and the row glue are NOT stated here. Stating them
  without their proofs would add register rows that need their own W12 falsifiers, and `Rows.lean`'s
  two pcs leaves must not be moved onto unproved children.

  ## ROW.PCS's residual at this HEAD (measured, for the row owner)

  `pcs_blockSim` is a `StmtsContractAll` over the whole `R.slice .pcs`. The slice is ONE outer
  `Stmt.block` whose body is the eight blocks of `GenAstPcs.computationsAst` (the inliner keeps
  every block wrapper; it does not flatten them). Block 2 is section 8. The remaining children are
  NOT small: blocks 1, 3, 4, 5 and 6 compute the rotation point table, the per-set q_eval sums
  (including the rolled arm's `scalar_inv` call), the Horner f_eval walk, the final MSM with its
  `staticcall` to 0x0c, and the two pairing-input staticcalls to 0x0b; the post's `Agree .pcs`
  clause needs the emitted values to equal `snapshotOf`'s `b.fEval`, `c.v`, `c.finalCom` and
  `c.dual`, which is `phaseA/B/C` correctness. Two further prerequisites are not in the tree:
  (i) PG-PCS-EMIT - `computationsAst` must not fault and must be non-empty (the fault arm leaves
  `R.slice .pcs = []` and then the row's `LeanRaw .pcs` post is false); (ii) the coverage invariant
  that turns `Mirror .quotient` + `Holds.g1Decodes` into `decode_exists`'s `hpts`, so the post's
  `∃ ms ..., Decoded` conjunct can be established. Both are named in the evidence's PG table, and
  neither is a hypothesis a row may take.

  PG-PCS-EMIT'S FAULT ARMS, MEASURED. Only two are live at `trace = false`
  (`GenAstPcs.lean`): the first `pcsBlock5Ast` panic (:432) is DEFINITIONAL and therefore
  unreachable - `finalMsmLen = (FinalMsmShape.fromTerms (terms+1)).inputBytes` IS
  `(terms+1) * g1MsmPairBytes` by `rfl` (`Layout.lean:880`); the second (:460) is a COUNTING
  lemma over the same `ecPointBeq` tests `finalMsmShape` folds (`pcsLinExpansion` adds
  `numQuotients + simpleSelectorCols.length` for the linearization commitment and 1 otherwise);
  and `pcsLinExpansion`'s `listGetMut dat.fixedComms col` (:407) needs the generation invariant
  `simpleSelectorCols ⊆ fixedComms.indices`. `intermediateSets`/`commitmentsBySet` have their own
  fault arms (`Kzg.lean:930/1124`). The empty-plan arm is excluded by `ValidV3`'s
  `hasMultiPointSet` clause (`Statements.lean:3462`), but no projection from `GeneratedBy` to
  fault-freedom is in the tree. None of this is a row hypothesis; it is generator work.
-/
import Midfall.LoweringV2.Stages
import Midfall.Lowering.GenAstPcs
import Midfall.Yul.Word
import Midfall.Yul.LoopRule
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.LoweringV3.VkWindow
import Midfall.Tools.Done
set_option autoImplicit false

namespace Midfall.LoweringV3.PcsRows

open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.Lowering.Stage
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. Option/mapM plumbing (generic, no render)

  `List.mapM` for `Option` is a `Bind.bind` chain, and `rw` does not reach under its `do`-binders
  (WORKER-RULES). The three lemmas below are the membership API the PCS parser bridge needs; they
  are proved by induction and carry no axioms. -/

/-- A successful `mapM` makes every element's `f` succeed - the direction the parser needs. -/
theorem mapM_some_mem {α β : Type} (f : α → Option β) :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ∀ a ∈ l, (f a).isSome = true
  | [], ys, h, a, ha => by simp at ha
  | a :: as, ys, h, x, hx => by
      rw [List.mapM_cons] at h
      change Option.bind (f a) (fun y => Option.bind (List.mapM f as) (fun ys => some (y :: ys))) =
        some ys at h
      cases hfa : f a with
      | none => rw [hfa] at h; cases h
      | some b =>
          rw [hfa, Option.bind_some] at h
          cases hmap : List.mapM f as with
          | none => rw [hmap] at h; cases h
          | some bs =>
              rw [hmap, Option.bind_some] at h
              have hys : ys = b :: bs := (Option.some.inj h).symm
              subst hys
              rcases List.mem_cons.mp hx with rfl | hx
              · rw [hfa]; rfl
              · exact mapM_some_mem f hmap x hx

/-- Pointwise success makes the whole `mapM` succeed - the direction the decode bridge needs. -/
theorem mapM_isSome_of_forall {α β : Type} (f : α → Option β) (l : List α)
    (h : ∀ a ∈ l, (f a).isSome = true) : (l.mapM f).isSome = true := by
  have hex : ∃ ys, l.mapM f = some ys := by
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons a as ih =>
        have ha : (f a).isSome = true := h a (by simp)
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ha
        obtain ⟨bs, hbs⟩ := ih (fun x hx => h x (by simp [hx]))
        refine ⟨b :: bs, ?_⟩
        rw [List.mapM_cons]
        change Option.bind (f a) (fun y => Option.bind (List.mapM f as) (fun ys => some (y :: ys))) =
          some (b :: bs)
        rw [hb, Option.bind_some, hbs]
        rfl
  obtain ⟨ys, hys⟩ := hex
  rw [hys]
  rfl

/-! ## 2. The raw decoder's instance array

  `rawDecode` ends with `inst.all (fun w => w.toNat < p)` before it commits. That guard is exactly
  what `instOfWords?` needs, and `rawDecode_inst_eq` (`LoweringV3/WideningStages.lean:207`) already
  identifies the array. These two lemmas turn the guard into the `instOfWords? = some` conjunct of
  `Decoded`. -/

/-- The `frOfWord?` gate on a list whose words are all below `p`. -/
theorem mapM_Midfall.LoweringV2.frOfWord?_of_all (l : List Word256)
    (h : l.all (fun w => w.toNat < p) = true) :
    ∃ inst : List (Fr p), l.mapM (Midfall.LoweringV2.frOfWord? (p := p)) = some inst := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨ha, has⟩ := h
      obtain ⟨inst, hin⟩ := ih has
      have hfa : Midfall.LoweringV2.frOfWord? (p := p) a = some (Nat.cast a.toNat) := by
        simpa [Midfall.LoweringV2.frOfWord?] using ha
      refine ⟨(Nat.cast a.toNat) :: inst, ?_⟩
      rw [List.mapM_cons]
      change Option.bind (Midfall.LoweringV2.frOfWord? (p := p) a)
        (fun x => Option.bind (List.mapM (Midfall.LoweringV2.frOfWord? (p := p)) as) (fun xs => some (x :: xs))) =
        some (Nat.cast a.toNat :: inst)
      rw [hfa, Option.bind_some, hin]
      rfl

/-- The array form: a word array all of whose entries are below `p` has an `instOfWords?` image. -/
theorem instOfWords?_of_all (l : List Word256)
    (h : l.all (fun w => w.toNat < p) = true) :
    ∃ inst : Array (Fr p), Midfall.LoweringV2.instOfWords? (p := p) l.toArray = some inst := by
  obtain ⟨instL, hmap⟩ := mapM_Midfall.LoweringV2.frOfWord?_of_all (p := p) l h
  refine ⟨instL.toArray, ?_⟩
  unfold Midfall.LoweringV2.instOfWords?
  rw [show l.toArray.toList = l from rfl, hmap]
  rfl

/-- **The raw walk's instance guard is `instOfWords?`.** Unfolds `rawDecode` and reads the last
  `split_ifs` branch; no semantic fact is used. -/
theorem instOfWords?_of_rawDecode {L : ProofCalldataLayout} {n : Nat} {cd : Bytes}
    {raw : List (RawMsg p)} {iw : Array Word256}
    (h : rawDecode (p := p) L n cd = some (raw, iw)) :
    ∃ inst : Array (Fr p), Midfall.LoweringV2.instOfWords? (p := p) iw = some inst := by
  unfold rawDecode at h
  split_ifs at h with henv
  · cases h2 : rawSlots (p := p) cd (RepackedProofLayoutPlan.fromProofLayout L).slots
        L.proofCptr with
    | none => rw [h2] at h; cases h
    | some x =>
      obtain ⟨ms, cur⟩ := x
      rw [h2] at h
      dsimp only at h
      split_ifs at h with hall
      · have hinj := Option.some.inj h
        rw [Prod.mk.injEq] at hinj
        rw [← hinj.2]
        have hall' : ((List.map (fun i => cdWord cd (L.proofEnd + 32 + 32 * i))
            (List.range n)).all fun w => decide (BitVec.toNat w < p)) = true := by
          rw [Bool.and_eq_true] at hall
          exact hall.2
        exact instOfWords?_of_all (p := p) _ hall'

/-! ## 3. ROW.PCS.9 / SIM.12: `decode_exists` -/

/-- **THE DECODE-EXISTS LEMMA (SIM.12), PROVED.** The parser established the raw walk; if every G1
    frame is a group element the calldata decodes. PCS proves the second hypothesis from G1MSM
    (`Holds.g1Decodes`) and the coverage invariant; this file proves the Lean-only implication.
    Statement ported verbatim from `GeneratorRows.lean:1005`; no render validity is needed. -/
theorem decode_exists (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (raw : List (RawMsg p))
    (instW : Array Word256)
    (hraw : rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd = some (raw, instW))
    (hpts : ∀ b, RawMsg.g1 b ∈ raw → (R.E.g1.ofEip? b).isSome = true) :
    ∃ ms instW' inst, Decoded R cd ms instW' inst := by
  have hmap : (raw.mapM (liftRaw R.E.g1)).isSome = true := by
    apply mapM_isSome_of_forall
    intro a ha
    cases a with
    | g1 b =>
        have hb := hpts b ha
        simpa [liftRaw] using hb
    | fr s => simp [liftRaw]
  have hdec : (decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd).isSome = true :=
    (decodeCalldata_isSome_iff (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd).2
      ⟨raw, instW, hraw, hmap⟩
  cases hcd : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd with
  | none => rw [hcd] at hdec; cases hdec
  | some pr =>
      obtain ⟨ms, iw⟩ := pr
      have hcd' := hcd
      rw [decodeCalldata_eq_raw, hraw] at hcd'
      simp only [Option.bind_some] at hcd'
      cases hm : raw.mapM (liftRaw (p := p) R.E.g1) with
      | none => rw [hm] at hcd'; cases hcd'
      | some ms' =>
          rw [hm] at hcd'
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcd'
          obtain ⟨hms, hiw⟩ := hcd'
          rw [← hms, ← hiw] at hcd
          obtain ⟨inst, hinst⟩ := instOfWords?_of_rawDecode (p := p) hraw
          exact ⟨_, _, inst, hcd, hinst⟩

/-! ## 4. Block 2 inliner groundwork (ROW.PCS.2, phase 2)

  `pcsBlock2Ast` is a five-statement block whose only loop is the x1 power table. The full
  `pcs_b2_sem` statement is about `Inline.inlineContractConstants consts (pcsBlock2Ast nb trunc)`;
  reaching the literal AST from that term is an INLINER-shape obligation, not a premise. The four
  facts below are the concrete shadow-list steps that obligation needs. They are stated at the
  shadow lists the block actually threads, because `shadowed` is a list recursion and a general
  `sh` makes the statement false when `sh` names no binder. No hypothesis is added to any row:
  these are lemmas about `Inline` alone.

  Still open for `pcs_b2_sem` (recorded, not sorried): the full-block equality
  `inlineContractConstants consts (pcsBlock2Ast nb trunc) = pcsBlock2Inline a1 aP nb trunc`
  (`pcsBlock2Inline` is the literal five-statement block) needs the `inlineScan 64`/`inlineScan 63`
  fuel alignment at the block wrapper; then the loop's `AllRuns` contract. Both are phase 2. -/

/-- `inExpr` on a literal is the literal at every fuel. -/
theorem inExpr_lit (fuel : Nat) (l : Literal) (consts : Inline.Consts) (sh : List String) :
    Inline.inExpr fuel (Expr.lit l) consts sh = Expr.lit l := by
  cases fuel with
  | zero => rfl
  | succ f => rfl

/-- Block 2's loop body, at a fixed `trunc`. -/
def pcsLoopBody (trunc : Bool) : Block EVM.Op :=
  [ GenAst.yset "p" (GenAst.yop EVM.Op.add [GenAst.yvar "p", GenAst.ylit 32]),
    GenAst.yset "acc" (GenAst.yop EVM.Op.mulmod
      [GenAst.yvar "acc", GenAst.yvar "x1", GenAst.yvar "r"]),
    GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "p",
      if trunc then GenAst.yop EVM.Op.and [GenAst.yvar "acc", GenAstPcs.truncMaskExpr]
      else GenAst.yvar "acc"]) ]

/-- Block 2's loop init. -/
def pcsInit : Block EVM.Op := [GenAst.ylet "i" (GenAst.ylit 0)]

/-- Block 2's loop post block. -/
def pcsPost : Block EVM.Op :=
  [GenAst.yset "i" (GenAst.yop EVM.Op.add [GenAst.yvar "i", GenAst.ylit 1])]

/-- The body inlines to itself at the block's own shadow list, non-truncated arm. -/
theorem inline_loopBody_false (consts : Inline.Consts) (hr : consts.lookup "r" = none) :
    Inline.inlineScan 63 consts ["x1", "acc", "p", "i"] (pcsLoopBody false) =
      { blks := pcsLoopBody false, exhausted := false } := by
  rw [show Inline.inlineScan 63 consts ["x1", "acc", "p", "i"] (pcsLoopBody false) =
      Inline.inlineStep (Inline.inlineScan 62 consts) consts ["x1", "acc", "p", "i"]
        (pcsLoopBody false) from rfl]
  simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil, pcsLoopBody,
    GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.yexpr,
    Inline.inlineStmtStep.eq_4, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_1, Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    Inline.inExpr.eq_5, inExpr_lit, Inline.exprFuel, Inline.boundOf, hr,
    List.map_cons, List.map_nil, Bool.false_or, Bool.or_false,
    (show Inline.shadowed ["x1", "acc", "p", "i"] "p" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"]) "acc" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"]) "x1" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"]) "r" = false by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"] ++ ["acc"]) "p" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"] ++ ["acc"]) "acc" = true by decide)]
  rfl

/-- The body inlines to itself at the block's own shadow list, truncated arm. -/
theorem inline_loopBody_true (consts : Inline.Consts) (hr : consts.lookup "r" = none) :
    Inline.inlineScan 63 consts ["x1", "acc", "p", "i"] (pcsLoopBody true) =
      { blks := pcsLoopBody true, exhausted := false } := by
  rw [show Inline.inlineScan 63 consts ["x1", "acc", "p", "i"] (pcsLoopBody true) =
      Inline.inlineStep (Inline.inlineScan 62 consts) consts ["x1", "acc", "p", "i"]
        (pcsLoopBody true) from rfl]
  simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil, pcsLoopBody,
    GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.yexpr,
    Inline.inlineStmtStep.eq_4, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_1, Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    Inline.inExpr.eq_5, inExpr_lit, Inline.exprFuel, Inline.boundOf, hr,
    List.map_cons, List.map_nil, Bool.false_or, Bool.or_false,
    (show Inline.shadowed ["x1", "acc", "p", "i"] "p" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"]) "acc" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"]) "x1" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"]) "r" = false by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"] ++ ["acc"]) "p" = true by decide),
    (show Inline.shadowed (["x1", "acc", "p", "i"] ++ ["p"] ++ ["acc"]) "acc" = true by decide)]
  rfl

/-- The loop init inlines to itself at the shadow list entering block 2's loop. -/
theorem inline_init (consts : Inline.Consts) :
    Inline.inlineScan 63 consts ["x1", "acc", "p"] pcsInit =
      { blks := pcsInit, exhausted := false } := by
  rw [show Inline.inlineScan 63 consts ["x1", "acc", "p"] pcsInit =
      Inline.inlineStep (Inline.inlineScan 62 consts) consts ["x1", "acc", "p"] pcsInit from rfl]
  simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil, List.nil_append, pcsInit,
    GenAst.ylet, GenAst.ylit, Inline.inlineStmtStep.eq_3, inExpr_lit,
    Inline.exprFuel, Inline.boundOf, Option.map_some, Option.map_none, Bool.false_or]

/-- The loop post block inlines to itself at the loop's own shadow list. -/
theorem inline_post (consts : Inline.Consts) :
    Inline.inlineScan 63 consts ["x1", "acc", "p", "i"] pcsPost =
      { blks := pcsPost, exhausted := false } := by
  rw [show Inline.inlineScan 63 consts ["x1", "acc", "p", "i"] pcsPost =
      Inline.inlineStep (Inline.inlineScan 62 consts) consts ["x1", "acc", "p", "i"] pcsPost
        from rfl]
  simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil, List.nil_append, pcsPost,
    GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit, Inline.inlineStmtStep.eq_4,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, inExpr_lit, Inline.exprFuel, Inline.boundOf,
    List.map_cons, List.map_nil, Bool.false_or,
    (show Inline.shadowed ["x1", "acc", "p", "i"] "i" = true by decide)]

/-! ### 4.1 Block 2: the inliner alignment (PROVED)

  `pcs_b2_sem` is stated about `inlineContractConstants consts (pcsBlock2Ast nb trunc)`. This is
  the literal five-statement block it denotes: the two prefix statements, then (when `nb > 1`) the
  two scalar lets and the `for` whose init/post/body are `pcsInit`/`pcsPost`/`pcsLoopBody`. The
  proof below threads the inliner's shadow list through the prefix, the loop init, the post block
  and the body, then through the condition. It is the `inlineScan 64`/`inlineScan 63` alignment the
  earlier header called open; it is now closed, with no fuel or heartbeat raise. -/

/-- The block-2 emitter with its loop pieces named, for the inliner proof. -/
def pcsBlock2AstV (nb : Nat) (trunc : Bool) : Block EVM.Op :=
  [GenAst.ylet "x1" (GenAst.yop EVM.Op.mload [GenAst.yvar "X1_MPTR"]),
   GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "X1_POWERS_MPTR", GenAst.ylit 1])] ++
  (if nb > 1 then
    [ GenAst.ylet "acc" (GenAst.ylit 1),
      GenAst.ylet "p" (GenAst.yvar "X1_POWERS_MPTR"),
      GenAst.yfor pcsInit
        (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
        pcsPost
        (pcsLoopBody trunc) ]
    else [])

/-- `pcsBlock2Ast` is the named-piece form, by `rfl`. -/
theorem pcsBlock2Ast_eq (nb : Nat) (trunc : Bool) :
    GenAstPcs.pcsBlock2Ast nb trunc = pcsBlock2AstV nb trunc := rfl

/-- The literal block 2 after inlining: the two prefix statements and, when `nb > 1`, the loop. -/
def pcsBlock2Inline (a1 aP nb : Nat) (trunc : Bool) : Block EVM.Op :=
  [GenAst.ylet "x1" (GenAst.yop EVM.Op.mload [GenAst.ylit a1]),
   GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.ylit aP, GenAst.ylit 1])] ++
  (if nb > 1 then
    [ GenAst.ylet "acc" (GenAst.ylit 1),
      GenAst.ylet "p" (GenAst.ylit aP),
      GenAst.yfor pcsInit
        (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
        pcsPost
        (pcsLoopBody trunc) ]
    else [])

/-- **BLOCK 2 INLINER ALIGNMENT**: the slice is the literal block at the three sites. -/
theorem pcsBlock2_inline (consts : Inline.Consts) (hr : consts.lookup "r" = none)
    (nb : Nat) (trunc : Bool) (a1 aP : Nat)
    (h1 : consts.lookup "X1_MPTR" = some a1) (hP : consts.lookup "X1_POWERS_MPTR" = some aP) :
    Inline.inlineContractConstants consts (GenAstPcs.pcsBlock2Ast nb trunc) =
      pcsBlock2Inline a1 aP nb trunc := by
  cases trunc
  · rw [pcsBlock2Ast_eq]
    rw [show Inline.inlineContractConstants consts (pcsBlock2AstV nb false) =
        (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
          (pcsBlock2AstV nb false)).blks from rfl]
    by_cases hnb : nb > 1
    · simp only [pcsBlock2AstV, hnb, if_true, pcsBlock2Inline, GenAst.ylet, GenAst.ylit,
        GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.yset, GenAst.yfor, List.nil_append,
        List.append_assoc, List.singleton_append, List.cons_append]
      simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil,
        List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
        Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_9,
        Inline.inlineStmtStep.eq_4, Inline.inlineStmtStep.eq_8,
        Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_5, inExpr_lit,
        Inline.exprFuel, Inline.boundOf, h1, hP, hr, Option.map_some, Option.map_none,
        List.map_cons, List.map_nil,
        (show Inline.shadowed [] "X1_MPTR" = false by decide),
        (show Inline.shadowed ["x1"] "X1_POWERS_MPTR" = false by decide),
        (show Inline.shadowed ["x1", "acc"] "X1_POWERS_MPTR" = false by decide)]
      rw [inline_init]
      simp only [pcsInit, GenAst.ylet, GenAst.ylit, Inline.boundOf, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append, List.singleton_append,
        List.cons_append]
      rw [inline_post, inline_loopBody_false consts hr]
      simp only [pcsInit, GenAst.ylet, GenAst.ylit, Inline.boundOf, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append, List.singleton_append,
        List.cons_append, reduceIte, Bool.false_or, Bool.or_false,
        Inline.inExpr.eq_2, inExpr_lit,
        (show Inline.shadowed ["x1", "acc", "p", "i"] "i" = true by decide)]
    · simp only [pcsBlock2AstV, hnb, if_false, pcsBlock2Inline, GenAst.ylet, GenAst.ylit,
        GenAst.yexpr, GenAst.yop, GenAst.yvar, List.nil_append, List.append_assoc,
        List.singleton_append, List.cons_append]
      simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil,
        List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
        Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_9, Inline.inExpr.eq_2,
        Inline.inExpr.eq_3, Inline.inExpr.eq_5, inExpr_lit, Inline.exprFuel, Inline.boundOf,
        h1, hP, hr, Option.map_some, Option.map_none, List.map_cons, List.map_nil,
        (show Inline.shadowed [] "X1_MPTR" = false by decide),
        (show Inline.shadowed ["x1"] "X1_POWERS_MPTR" = false by decide)]
  · rw [pcsBlock2Ast_eq]
    rw [show Inline.inlineContractConstants consts (pcsBlock2AstV nb true) =
        (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
          (pcsBlock2AstV nb true)).blks from rfl]
    by_cases hnb : nb > 1
    · simp only [pcsBlock2AstV, hnb, if_true, pcsBlock2Inline, GenAst.ylet, GenAst.ylit,
        GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.yset, GenAst.yfor, List.nil_append,
        List.append_assoc, List.singleton_append, List.cons_append]
      simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil,
        List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
        Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_9,
        Inline.inlineStmtStep.eq_4, Inline.inlineStmtStep.eq_8,
        Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_5, inExpr_lit,
        Inline.exprFuel, Inline.boundOf, h1, hP, hr, Option.map_some, Option.map_none,
        List.map_cons, List.map_nil,
        (show Inline.shadowed [] "X1_MPTR" = false by decide),
        (show Inline.shadowed ["x1"] "X1_POWERS_MPTR" = false by decide),
        (show Inline.shadowed ["x1", "acc"] "X1_POWERS_MPTR" = false by decide)]
      rw [inline_init]
      simp only [pcsInit, GenAst.ylet, GenAst.ylit, Inline.boundOf, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append, List.singleton_append,
        List.cons_append]
      rw [inline_post, inline_loopBody_true consts hr]
      simp only [pcsInit, GenAst.ylet, GenAst.ylit, Inline.boundOf, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append, List.singleton_append,
        List.cons_append, reduceIte, Bool.false_or, Bool.or_false,
        Inline.inExpr.eq_2, inExpr_lit,
        (show Inline.shadowed ["x1", "acc", "p", "i"] "i" = true by decide)]
    · simp only [pcsBlock2AstV, hnb, if_false, pcsBlock2Inline, GenAst.ylet, GenAst.ylit,
        GenAst.yexpr, GenAst.yop, GenAst.yvar, List.nil_append, List.append_assoc,
        List.singleton_append, List.cons_append]
      simp only [Inline.inlineStep, List.foldl_cons, List.foldl_nil, List.append_nil,
        List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
        Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_9, Inline.inExpr.eq_2,
        Inline.inExpr.eq_3, Inline.inExpr.eq_5, inExpr_lit, Inline.exprFuel, Inline.boundOf,
        h1, hP, hr, Option.map_some, Option.map_none, List.map_cons, List.map_nil,
        (show Inline.shadowed [] "X1_MPTR" = false by decide),
        (show Inline.shadowed ["x1"] "X1_POWERS_MPTR" = false by decide)]

/-! ## 5. Block 2 loop vocabulary (ROW.PCS.2, phase 2; all PROVED)

  The x1 power table's loop is stated over `wPowers` and written by `pcsWriteWords`. These are
  the render-free definitions and the read-over-write/outside lemmas the loop contract needs; the
  `AllRuns` proof itself is section 8's `pcs_loop_*`/`pcs_b2_sem`. The generic `VEnv` lemmas are
  dialect-generic copies of the ones `LagrangeRows`/`QuotientRows` already proved - copied rather
  than imported so this file's cone does not pull in the quotient modules. -/

/-- `VEnv.set` preserves length. -/
theorem venv_set_length {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (a : D.Value) : (VEnv.set V x a).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

/-- Setting the head binding to itself. -/
theorem venv_set_cons_same {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {u v : D.Value} : VEnv.set ((x, u) :: V) x v = (x, v) :: V := by
  simp [VEnv.set]

/-- Setting a different variable through the head binding. -/
theorem venv_set_cons_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {u v : D.Value} (h : y ≠ x) :
    VEnv.set ((y, u) :: V) x v = (y, u) :: VEnv.set V x v := by
  simp [VEnv.set, h]

/-- Setting a variable twice is setting it once. -/
theorem venv_set_set {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D} {x : Ident}
    {a b : D.Value} : VEnv.set (VEnv.set V x a) x b = VEnv.set V x b := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

/-- Reading back a variable just set when it is bound. -/
theorem venv_get_set_same {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
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

/-- Reading a different variable from a cons. -/
theorem venv_get_cons_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get ((x, v) :: V) y = VEnv.get V y := by
  have hd : decide (x = y) = false := decide_eq_false (fun h' => h h'.symm)
  simp only [VEnv.get, List.find?, hd]

/-- Reading the head binding at its own name. -/
theorem venv_get_cons_self {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (v : D.Value) : VEnv.get ((x, v) :: V) x = some v := by
  simp [VEnv.get, List.find?]

/-- Reading a different variable after a set. -/
theorem venv_get_set_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
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

/-- Setting a bound variable to its own value is the identity. -/
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
        simp [VEnv.set, hy, hset]

/-- A loop-exit environment drops the loop's own binding and keeps the in-place updates. -/
theorem restore_cons_set {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {y x : Ident} {a b : D.Value} :
    restore V ((y, b) :: VEnv.set V x a) = VEnv.set V x a := by
  simp [restore, venv_set_length]

/-- `restore` is the identity when the inner scope has the outer length. -/
theorem restore_eq_self {D : YulSemantics.Dialect} [DecidableEq D.Value] {V W : VEnv D}
    (h : W.length = V.length) : restore V W = W := by
  simp [restore, h]

/-- A block that only assigns exits by `restore`-identity. -/
theorem restore_set_same {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {a : D.Value} : restore V (VEnv.set V x a) = VEnv.set V x a := by
  simp [restore, venv_set_length]

/-- Setting two distinct variables commutes. -/
theorem venv_set_comm {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D} {x y : Ident}
    {a b : D.Value} (h : x ≠ y) :
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

/-- The environment equation of one `pcsLoopBody` step: the two outer sets update the loop
    head, and the old `p`/`acc` values are overwritten. -/
theorem venv_set_loop_step {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (j : Nat)
    (oldAcc oldP newP newAcc newI : U256) :
    VEnv.set (VEnv.set (VEnv.set
      (("i", BitVec.ofNat 256 j) :: (V.set "acc" oldAcc).set "p" oldP) "p" newP) "acc" newAcc) "i" newI
    = ("i", newI) :: (V.set "acc" newAcc).set "p" newP := by
  rw [venv_set_comm (D := Bridge.Dialect c g) (x := "acc") (y := "i") (by decide)]
  rw [venv_set_comm (D := Bridge.Dialect c g) (x := "p") (y := "i") (by decide)]
  rw [venv_set_cons_same (D := Bridge.Dialect c g)]
  rw [venv_set_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "i")
    (u := newI) (v := newP) (by decide)]
  rw [venv_set_cons_ne (D := Bridge.Dialect c g) (x := "acc") (y := "i")
    (u := newI) (v := newAcc) (by decide)]
  rw [venv_set_set (D := Bridge.Dialect c g) (x := "p")]
  rw [venv_set_comm (D := Bridge.Dialect c g)
    (V := VEnv.set V "acc" oldAcc) (x := "p") (y := "acc") (by decide)]
  rw [venv_set_set (D := Bridge.Dialect c g) (x := "acc")]

/-- A scope that adds one binding exits by dropping it. -/
theorem restore_cons_length {D : YulSemantics.Dialect} [DecidableEq D.Value] {V W : VEnv D}
    {y : Ident} {b : D.Value} (h : W.length = V.length) :
    restore V ((y, b) :: W) = W := by
  simp [restore, h]

/-- EVM `mulmod` at an arbitrary modulus word. -/
def wMulmodAt (a b n : U256) : U256 :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)

/-- The x1 power table exactly as block 2's loop writes it. The evidence writes the mask as the
    numeral `2^128-1`; the emitter writes `ylit (hexLiteral truncMask128)`, and the two are equal by
    a concrete computation that does not kernel-reduce (`String.foldl` is opaque). This definition
    uses the emitter's own literal, so the SEM loop statement is definitional. -/
def wPowers (r x1 : U256) (mask : Bool) : Nat → U256 × U256
  | 0 => (1, 1)
  | i + 1 =>
      let acc := wMulmodAt (wPowers r x1 mask i).1 x1 r
      (acc, if mask then acc &&& litValue (Literal.number (GenAst.hexLiteral truncMask128)) else acc)

/-- The memory a run of `j` stores leaves at `D, D+32, …`. -/
def pcsWriteWords (mem : Nat → UInt8) (D : Nat) (f : Nat → U256) : Nat → (Nat → UInt8)
  | 0 => mem
  | j + 1 => storeWord (pcsWriteWords mem D f j) (D + 32 * j) (f j)

/-- Reading back the `i`-th stored word. -/
theorem pcsLoadWord_writeWords_lt (mem : Nat → UInt8) (D : Nat) (f : Nat → U256) :
    ∀ {j i : Nat}, i < j → loadWord (pcsWriteWords mem D f j) (D + 32 * i) = f i
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | j + 1, i, h => by
      by_cases hij : i = j
      · subst hij
        rw [pcsWriteWords, Midfall.Yul.Word.loadWord_storeWord_same]
      · have hi : i < j := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hij
        have hdisj : D + 32 * i + 32 ≤ D + 32 * j := by omega
        rw [pcsWriteWords, show loadWord (storeWord (pcsWriteWords mem D f j) (D + 32 * j) (f j))
              (D + 32 * i) = loadWord (pcsWriteWords mem D f j) (D + 32 * i) from
            Midfall.Yul.Word.loadWord_storeWord_disjoint _ _ _ _ (Or.inl hdisj)]
        exact pcsLoadWord_writeWords_lt mem D f hi

/-- A byte outside the written window is unchanged. -/
theorem pcsWriteWords_outside (mem : Nat → UInt8) (D : Nat) (f : Nat → U256) :
    ∀ {j a : Nat}, (a < D ∨ D + 32 * j ≤ a) → pcsWriteWords mem D f j a = mem a
  | 0, a, _ => rfl
  | j + 1, a, h => by
      rw [pcsWriteWords]
      have hnot : ¬ (D + 32 * j ≤ a ∧ a < D + 32 * j + 32) := by
        rintro ⟨h1, h2⟩
        omega
      rw [storeWord, ite_eq_right hnot]
      exact pcsWriteWords_outside mem D f (j := j) (a := a) (by omega)

/-- Re-storing the same word at the same address is the identity. -/
theorem storeWord_storeWord_same (mem : Nat → UInt8) (p : Nat) (v : U256) :
    storeWord (storeWord mem p v) p v = storeWord mem p v := by
  funext a
  by_cases h : p ≤ a ∧ a < p + 32
  · simp [storeWord, h]
  · simp [storeWord, h]

/-! ## 6. `pcsLoopBody`: the non-truncated arm (ROW.PCS.2, phase 2)

  The `allRuns_for_cons_wp` proof of block 2's loop, `trunc = false` arm. It uses the invariant
  `p = aP + 32j`, `acc = (wPowers j).1`, memory `pcsWriteWords … (j+1)`, and the env step lemma
  `venv_set_loop_step`. The truncated arm is the same loop with the masked store; it is not landed
  yet, so this section adds no row. -/

open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac Midfall.Yul.LoopRule

variable {c : ExternalCalls} {g : ExternalGas}

theorem stepOp_mstore (st : EvmState) (p v : U256) :
    stepOp EVM.Op.mstore [p, v] st =
      some (.ok [] { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v }) := rfl

theorem stepOp_and (a b : U256) (st : EvmState) :
    stepOp EVM.Op.and [a, b] st = some (.ok [a &&& b] st) := rfl

theorem pcs_loop_false (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (nb : Nat) (hnb : nb > 1) (aP : Nat)
    (hlt : aP + 32 * nb < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [Stmt.forLoop pcsInit
        (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
        pcsPost (pcsLoopBody false)]
      (fun V st => VEnv.get V "acc" = some (1 : U256) ∧
        VEnv.get V "p" = some (BitVec.ofNat 256 aP) ∧
        (VEnv.get V "x1").isSome ∧ (VEnv.get V "r").isSome ∧
        st.memory = storeWord st.memory aP 1)
      (fun V st V' st' o => o = .normal ∧
        ∃ rw x1, VEnv.get V "r" = some rw ∧ VEnv.get V "x1" = some x1 ∧
          V' = VEnv.set (VEnv.set V "acc" (wPowers rw x1 false (nb - 1)).1) "p"
            (BitVec.ofNat 256 (aP + 32 * (nb - 1))) ∧
          st'.memory = pcsWriteWords st.memory aP
            (fun i => (wPowers rw x1 false i).2) nb ∧
          st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre
  obtain ⟨hacc, hp, hx1s, hrs, hmem0⟩ := hpre
  obtain ⟨x1, hx1⟩ := Option.isSome_iff_exists.mp hx1s
  obtain ⟨rw, hrw⟩ := Option.isSome_iff_exists.mp hrs
  let f : Nat → U256 := fun i => (wPowers rw x1 false i).2
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop := fun V' st' =>
    ∃ j, j ≤ nb - 1 ∧
      V' = ("i", BitVec.ofNat 256 j) ::
        VEnv.set (VEnv.set V "acc" (wPowers rw x1 false j).1) "p"
          (BitVec.ofNat 256 (aP + 32 * j)) ∧
      VEnv.get V' "i" = some (BitVec.ofNat 256 j) ∧
      VEnv.get V' "acc" = some (wPowers rw x1 false j).1 ∧
      VEnv.get V' "p" = some (BitVec.ofNat 256 (aP + 32 * j)) ∧
      VEnv.get V' "x1" = some x1 ∧ VEnv.get V' "r" = some rw ∧
      st'.memory = pcsWriteWords st.memory aP f (j + 1) ∧
      st'.env = st.env ∧ st'.halted = st.halted
  change AllRuns funs V st
    [Stmt.forLoop pcsInit
      (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
      pcsPost (pcsLoopBody false)]
    (fun V' st' o => o = .normal ∧
      ∃ rw x1, VEnv.get V "r" = some rw ∧ VEnv.get V "x1" = some x1 ∧
        V' = VEnv.set (VEnv.set V "acc" (wPowers rw x1 false (nb - 1)).1) "p"
          (BitVec.ofNat 256 (aP + 32 * (nb - 1))) ∧
        st'.memory = pcsWriteWords st.memory aP
          (fun i => (wPowers rw x1 false i).2) nb ∧
        st'.env = st.env ∧ st'.halted = st.halted)
  refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _)
    (Bopen_sound c g) (Cnone_sound _) (n := 20) Inv ?hinit ?hstep
  · simp only [pcsInit, GenAst.ylet, GenAst.ylit, wpSS, wpS, wpE]
    refine ⟨rfl, ⟨?_⟩⟩
    show Inv (["i"].zip [litValue (Literal.number 0)] ++ V) st
    rw [show litValue (Literal.number 0) = (0 : U256) from rfl]
    rw [show (["i"].zip [(0 : U256)] ++ V) = ("i", (0 : U256)) :: V from rfl]
    have hset_acc : VEnv.set V "acc" (wPowers rw x1 false 0).1 = V := by
      rw [show (wPowers rw x1 false 0).1 = (1 : U256) from rfl]
      exact venv_set_eq_self hacc
    have hset_p : VEnv.set V "p" (BitVec.ofNat 256 (aP + 32 * 0)) = V := by
      rw [show aP + 32 * 0 = aP by omega]
      exact venv_set_eq_self hp
    refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hset_acc, hset_p]; rfl
    · exact venv_get_cons_self V "i" 0
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "acc")
        (v := (0 : U256)) (by decide)]
      exact hacc
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "p")
        (v := (0 : U256)) (by decide), show aP + 32 * 0 = aP by omega]
      exact hp
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "x1")
        (v := (0 : U256)) (by decide)]
      exact hx1
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "r")
        (v := (0 : U256)) (by decide)]
      exact hrw
    · rw [pcsWriteWords]
      rw [show f 0 = (1 : U256) from rfl, show aP + 32 * 0 = aP by omega]
      rw [show pcsWriteWords st.memory aP f 0 = st.memory from rfl]
      exact hmem0
    · rfl
    · rfl
  · intro Vi sti hInv
    simp only [wpIter]
    obtain ⟨j, hj, hV, hig, haccg, hpg, hx1g, hrg, hmemg, henvg, hhaltg⟩ := hInv
    subst hV
    simp only [GenAst.yop, GenAst.yvar, GenAst.ylit, wpE, wpA, Bopen, stepOp, bin]
    rw [hig]
    simp only [litValue]
    refine ⟨?exit, ?iter⟩
    · intro hzero
      have hJ : j < 2 ^ 256 := by omega
      have hN : nb - 1 < 2 ^ 256 := by omega
      have hge : nb - 1 ≤ j := LoopRule.lt_guard_false hJ hN hzero
      have hjk : j = nb - 1 := Nat.le_antisymm hj hge
      refine ⟨?allRuns⟩
      intro V' st' o hrun
      cases hrun with
      | seqNil =>
          rw [hjk] at hmemg ⊢
          refine ⟨rfl, rw, x1, hrw, hx1, ?_, ?_, henvg, hhaltg⟩
          · refine restore_cons_length (D := Bridge.Dialect c g) (V := V)
              (W := (V.set "acc" (wPowers rw x1 false (nb - 1)).1).set "p"
                (BitVec.ofNat 256 (aP + 32 * (nb - 1))))
              (y := "i") (b := BitVec.ofNat 256 (nb - 1)) ?_
            rw [venv_set_length (D := Bridge.Dialect c g),
              venv_set_length (D := Bridge.Dialect c g)]
          · rw [hmemg, show nb - 1 + 1 = nb by omega]
    · intro hnz
      have hJ : j < 2 ^ 256 := by omega
      have hN : nb - 1 < 2 ^ 256 := by omega
      have hltj : j < nb - 1 := LoopRule.lt_guard_true hJ hN hnz
      rw [wpS.eq_3]
      simp only [pcsLoopBody, GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.yexpr]
      rw [wpSS.eq_3]
      rw [wpS.eq_6]
      simp only [wpE, wpA, Bopen, stepOp, bin, hpg]
      refine ⟨by simp, ⟨?_⟩⟩
      set newp : U256 := BitVec.ofNat 256 (aP + 32 * j) + litValue (Literal.number 32) with hnewp
      have hnewpval : newp = BitVec.ofNat 256 (aP + 32 * (j + 1)) := by
        rw [hnewp]
        rw [show litValue (Literal.number 32) = BitVec.ofNat 256 32 from rfl, ← BitVec.ofNat_add]
        congr 1
      have hacc1 : VEnv.get (VEnv.setMany
          (("i", BitVec.ofNat 256 j) ::
            (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
          ["p"] [newp]) "acc" = some (wPowers rw x1 false j).1 := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc") (v := newp)
          (by decide)]
        exact haccg
      have hx11 : VEnv.get (VEnv.setMany
          (("i", BitVec.ofNat 256 j) ::
            (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
          ["p"] [newp]) "x1" = some x1 := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "x1") (v := newp)
          (by decide)]
        exact hx1g
      have hr1 : VEnv.get (VEnv.setMany
          (("i", BitVec.ofNat 256 j) ::
            (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
          ["p"] [newp]) "r" = some rw := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "r") (v := newp)
          (by decide)]
        exact hrg
      rw [wpSS.eq_3]
      rw [wpS.eq_6]
      simp only [wpE, wpA, Bopen, stepOp, bin, ter, hacc1, hx11, hr1]
      refine ⟨by simp, ⟨?_⟩⟩
      set newacc : U256 := if rw = 0 then 0 else
        BitVec.ofNat 256 (BitVec.toNat (wPowers rw x1 false j).1 * BitVec.toNat x1 % BitVec.toNat rw)
        with hnewaccdef
      have hnewacc : newacc = (wPowers rw x1 false (j + 1)).1 := by
        rw [hnewaccdef]; rfl
      have hpcur : VEnv.get
          ((VEnv.setMany
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            ["p"] [newp]).setMany ["acc"] [newacc]) "p" = some newp := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "p") (v := newacc)
          (by decide)]
        exact venv_get_set_same hpg
      have hacccur : VEnv.get
          ((VEnv.setMany
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            ["p"] [newp]).setMany ["acc"] [newacc]) "acc" = some newacc := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        have haccp : VEnv.get (VEnv.set
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            "p" newp) "acc" = some (wPowers rw x1 false j).1 := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc")
            (v := newp) (by decide)]
          exact haccg
        exact venv_get_set_same (D := Bridge.Dialect c g) haccp
      rw [wpSS.eq_3]
      rw [wpS.eq_7]
      rw [show (15 : Nat) = Nat.succ 14 from rfl, wpE.eq_4]
      rw [show (14 : Nat) = Nat.succ 13 from rfl, wpA.eq_3]
      rw [show (13 : Nat) = Nat.succ 12 from rfl, wpA.eq_3]
      rw [show (12 : Nat) = Nat.succ 11 from rfl, wpA.eq_2]
      simp only [reduceIte, Bool.false_eq_true]
      rw [wpE.eq_3, hacccur]
      dsimp only
      rw [wpE.eq_3, hpcur]
      dsimp only
      simp only [Bopen]
      rw [stepOp_mstore]
      dsimp only
      refine ⟨?_⟩
      rw [wpSS.eq_2]
      simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
        List.foldl_cons, List.foldl_nil]
      rw [restore_eq_self (D := Bridge.Dialect c g) (by
        rw [venv_set_length (D := Bridge.Dialect c g),
          venv_set_length (D := Bridge.Dialect c g)])]
      have higb : VEnv.get
          ((VEnv.set
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 false j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            "p" newp).set "acc" newacc) "i" = some (BitVec.ofNat 256 j) := by
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "i") (v := newacc)
          (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "i") (v := newp)
          (by decide)]
        exact hig
      rw [wpS.eq_3]
      simp only [pcsPost, GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit]
      rw [wpSS.eq_3]
      rw [wpS.eq_6]
      simp only [wpE, wpA, Bopen, stepOp, bin, higb]
      refine ⟨by simp, ⟨?_⟩⟩
      rw [wpSS.eq_2]
      simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
        List.foldl_cons, List.foldl_nil]
      rw [restore_set_same (D := Bridge.Dialect c g)]
      have hnewi : BitVec.ofNat 256 j + litValue (Literal.number 1) =
          BitVec.ofNat 256 (j + 1) := by
        rw [show litValue (Literal.number 1) = BitVec.ofNat 256 1 from rfl,
          ← BitVec.ofNat_add]
      have hbound : aP + 32 * (j + 1) < 2 ^ 256 := by omega
      have hnewp_toNat : newp.toNat = aP + 32 * (j + 1) := by
        rw [hnewpval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
      have hf : f (j + 1) = newacc := by
        rw [hnewacc]; rfl
      dsimp only [Inv]
      rw [venv_set_loop_step (V := V) (j := j) (oldAcc := (wPowers rw x1 false j).1)
        (oldP := BitVec.ofNat 256 (aP + 32 * j)) (newP := newp) (newAcc := newacc)
        (newI := BitVec.ofNat 256 j + litValue (Literal.number 1))]
      refine ⟨j + 1, by omega, ?env, ?gi, ?gacc, ?gp, ?gx1, ?gr, ?gmem, ?genv, ?ghalt⟩
      · rw [← hnewi, ← hnewpval, ← hnewacc]
      · rw [← hnewi]
        exact venv_get_cons_self (D := Bridge.Dialect c g) _ "i"
          (BitVec.ofNat 256 j + litValue (Literal.number 1))
      · rw [← hnewacc]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "acc")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc") (v := newp)
          (by decide)]
        exact venv_get_set_same (D := Bridge.Dialect c g) hacc
      · rw [← hnewpval]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "p")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        have hpold : VEnv.get (VEnv.set V "acc" newacc) "p" = some (BitVec.ofNat 256 aP) := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "p") (v := newacc)
            (by decide)]
          exact hp
        exact venv_get_set_same (D := Bridge.Dialect c g) hpold
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "x1")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "x1") (v := newp)
          (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "x1") (v := newacc)
          (by decide)]
        exact hx1
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "r")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "r") (v := newp)
          (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "r") (v := newacc)
          (by decide)]
        exact hrw
      · rw [hmemg]
        rw [show pcsWriteWords st.memory aP f (j + 1 + 1) =
            storeWord (pcsWriteWords st.memory aP f (j + 1)) (aP + 32 * (j + 1))
              (f (j + 1)) from rfl]
        rw [hnewp_toNat, ← hf]
      · rw [show (touchMemory sti (BitVec.toNat newp) 32).env = sti.env from rfl, henvg]
      · rw [show (touchMemory sti (BitVec.toNat newp) 32).halted = sti.halted from rfl, hhaltg]

theorem pcs_loop_true (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (nb : Nat) (hnb : nb > 1) (aP : Nat)
    (hlt : aP + 32 * nb < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [Stmt.forLoop pcsInit
        (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
        pcsPost (pcsLoopBody true)]
      (fun V st => VEnv.get V "acc" = some (1 : U256) ∧
        VEnv.get V "p" = some (BitVec.ofNat 256 aP) ∧
        (VEnv.get V "x1").isSome ∧ (VEnv.get V "r").isSome ∧
        st.memory = storeWord st.memory aP 1)
      (fun V st V' st' o => o = .normal ∧
        ∃ rw x1, VEnv.get V "r" = some rw ∧ VEnv.get V "x1" = some x1 ∧
          V' = VEnv.set (VEnv.set V "acc" (wPowers rw x1 true (nb - 1)).1) "p"
            (BitVec.ofNat 256 (aP + 32 * (nb - 1))) ∧
          st'.memory = pcsWriteWords st.memory aP
            (fun i => (wPowers rw x1 true i).2) nb ∧
          st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre
  obtain ⟨hacc, hp, hx1s, hrs, hmem0⟩ := hpre
  obtain ⟨x1, hx1⟩ := Option.isSome_iff_exists.mp hx1s
  obtain ⟨rw, hrw⟩ := Option.isSome_iff_exists.mp hrs
  let f : Nat → U256 := fun i => (wPowers rw x1 true i).2
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop := fun V' st' =>
    ∃ j, j ≤ nb - 1 ∧
      V' = ("i", BitVec.ofNat 256 j) ::
        VEnv.set (VEnv.set V "acc" (wPowers rw x1 true j).1) "p"
          (BitVec.ofNat 256 (aP + 32 * j)) ∧
      VEnv.get V' "i" = some (BitVec.ofNat 256 j) ∧
      VEnv.get V' "acc" = some (wPowers rw x1 true j).1 ∧
      VEnv.get V' "p" = some (BitVec.ofNat 256 (aP + 32 * j)) ∧
      VEnv.get V' "x1" = some x1 ∧ VEnv.get V' "r" = some rw ∧
      st'.memory = pcsWriteWords st.memory aP f (j + 1) ∧
      st'.env = st.env ∧ st'.halted = st.halted
  change AllRuns funs V st
    [Stmt.forLoop pcsInit
      (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
      pcsPost (pcsLoopBody true)]
    (fun V' st' o => o = .normal ∧
      ∃ rw x1, VEnv.get V "r" = some rw ∧ VEnv.get V "x1" = some x1 ∧
        V' = VEnv.set (VEnv.set V "acc" (wPowers rw x1 true (nb - 1)).1) "p"
          (BitVec.ofNat 256 (aP + 32 * (nb - 1))) ∧
        st'.memory = pcsWriteWords st.memory aP
          (fun i => (wPowers rw x1 true i).2) nb ∧
        st'.env = st.env ∧ st'.halted = st.halted)
  refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _)
    (Bopen_sound c g) (Cnone_sound _) (n := 20) Inv ?hinit ?hstep
  · simp only [pcsInit, GenAst.ylet, GenAst.ylit, wpSS, wpS, wpE]
    refine ⟨rfl, ⟨?_⟩⟩
    show Inv (["i"].zip [litValue (Literal.number 0)] ++ V) st
    rw [show litValue (Literal.number 0) = (0 : U256) from rfl]
    rw [show (["i"].zip [(0 : U256)] ++ V) = ("i", (0 : U256)) :: V from rfl]
    have hset_acc : VEnv.set V "acc" (wPowers rw x1 true 0).1 = V := by
      rw [show (wPowers rw x1 true 0).1 = (1 : U256) from rfl]
      exact venv_set_eq_self hacc
    have hset_p : VEnv.set V "p" (BitVec.ofNat 256 (aP + 32 * 0)) = V := by
      rw [show aP + 32 * 0 = aP by omega]
      exact venv_set_eq_self hp
    refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hset_acc, hset_p]; rfl
    · exact venv_get_cons_self V "i" 0
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "acc")
        (v := (0 : U256)) (by decide)]
      exact hacc
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "p")
        (v := (0 : U256)) (by decide), show aP + 32 * 0 = aP by omega]
      exact hp
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "x1")
        (v := (0 : U256)) (by decide)]
      exact hx1
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "r")
        (v := (0 : U256)) (by decide)]
      exact hrw
    · rw [pcsWriteWords]
      rw [show f 0 = (1 : U256) from rfl, show aP + 32 * 0 = aP by omega]
      rw [show pcsWriteWords st.memory aP f 0 = st.memory from rfl]
      exact hmem0
    · rfl
    · rfl
  · intro Vi sti hInv
    simp only [wpIter]
    obtain ⟨j, hj, hV, hig, haccg, hpg, hx1g, hrg, hmemg, henvg, hhaltg⟩ := hInv
    subst hV
    simp only [GenAst.yop, GenAst.yvar, GenAst.ylit, wpE, wpA, Bopen, stepOp, bin]
    rw [hig]
    simp only [litValue]
    refine ⟨?exit, ?iter⟩
    · intro hzero
      have hJ : j < 2 ^ 256 := by omega
      have hN : nb - 1 < 2 ^ 256 := by omega
      have hge : nb - 1 ≤ j := LoopRule.lt_guard_false hJ hN hzero
      have hjk : j = nb - 1 := Nat.le_antisymm hj hge
      refine ⟨?allRuns⟩
      intro V' st' o hrun
      cases hrun with
      | seqNil =>
          rw [hjk] at hmemg ⊢
          refine ⟨rfl, rw, x1, hrw, hx1, ?_, ?_, henvg, hhaltg⟩
          · refine restore_cons_length (D := Bridge.Dialect c g) (V := V)
              (W := (V.set "acc" (wPowers rw x1 true (nb - 1)).1).set "p"
                (BitVec.ofNat 256 (aP + 32 * (nb - 1))))
              (y := "i") (b := BitVec.ofNat 256 (nb - 1)) ?_
            rw [venv_set_length (D := Bridge.Dialect c g),
              venv_set_length (D := Bridge.Dialect c g)]
          · rw [hmemg, show nb - 1 + 1 = nb by omega]
    · intro hnz
      have hJ : j < 2 ^ 256 := by omega
      have hN : nb - 1 < 2 ^ 256 := by omega
      have hltj : j < nb - 1 := LoopRule.lt_guard_true hJ hN hnz
      rw [wpS.eq_3]
      simp only [pcsLoopBody, GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.yexpr]
      rw [wpSS.eq_3]
      rw [wpS.eq_6]
      simp only [wpE, wpA, Bopen, stepOp, bin, hpg]
      refine ⟨by simp, ⟨?_⟩⟩
      set newp : U256 := BitVec.ofNat 256 (aP + 32 * j) + litValue (Literal.number 32) with hnewp
      have hnewpval : newp = BitVec.ofNat 256 (aP + 32 * (j + 1)) := by
        rw [hnewp]
        rw [show litValue (Literal.number 32) = BitVec.ofNat 256 32 from rfl, ← BitVec.ofNat_add]
        congr 1
      have hacc1 : VEnv.get (VEnv.setMany
          (("i", BitVec.ofNat 256 j) ::
            (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
          ["p"] [newp]) "acc" = some (wPowers rw x1 true j).1 := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc") (v := newp)
          (by decide)]
        exact haccg
      have hx11 : VEnv.get (VEnv.setMany
          (("i", BitVec.ofNat 256 j) ::
            (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
          ["p"] [newp]) "x1" = some x1 := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "x1") (v := newp)
          (by decide)]
        exact hx1g
      have hr1 : VEnv.get (VEnv.setMany
          (("i", BitVec.ofNat 256 j) ::
            (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
          ["p"] [newp]) "r" = some rw := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "r") (v := newp)
          (by decide)]
        exact hrg
      rw [wpSS.eq_3]
      rw [wpS.eq_6]
      simp only [wpE, wpA, Bopen, stepOp, bin, ter, hacc1, hx11, hr1]
      refine ⟨by simp, ⟨?_⟩⟩
      set newacc : U256 := if rw = 0 then 0 else
        BitVec.ofNat 256 (BitVec.toNat (wPowers rw x1 true j).1 * BitVec.toNat x1 % BitVec.toNat rw)
        with hnewaccdef
      have hnewacc : newacc = (wPowers rw x1 true (j + 1)).1 := by
        rw [hnewaccdef]; rfl
      have hpcur : VEnv.get
          ((VEnv.setMany
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            ["p"] [newp]).setMany ["acc"] [newacc]) "p" = some newp := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "p") (v := newacc)
          (by decide)]
        exact venv_get_set_same hpg
      have hacccur : VEnv.get
          ((VEnv.setMany
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            ["p"] [newp]).setMany ["acc"] [newacc]) "acc" = some newacc := by
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
          List.foldl_cons, List.foldl_nil]
        have haccp : VEnv.get (VEnv.set
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            "p" newp) "acc" = some (wPowers rw x1 true j).1 := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc")
            (v := newp) (by decide)]
          exact haccg
        exact venv_get_set_same (D := Bridge.Dialect c g) haccp
      rw [wpSS.eq_3]
      rw [wpS.eq_7]
      simp only [reduceIte]
      rw [show (15 : Nat) = Nat.succ 14 from rfl, wpE.eq_4]
      rw [show (14 : Nat) = Nat.succ 13 from rfl, wpA.eq_3]
      rw [show (13 : Nat) = Nat.succ 12 from rfl, wpA.eq_3]
      rw [show (12 : Nat) = Nat.succ 11 from rfl, wpA.eq_2]
      dsimp only
      rw [wpE.eq_4]
      rw [show (11 : Nat) = Nat.succ 10 from rfl, wpA.eq_3]
      rw [show (10 : Nat) = Nat.succ 9 from rfl, wpA.eq_3]
      rw [show (9 : Nat) = Nat.succ 8 from rfl, wpA.eq_2]
      simp only [GenAstPcs.truncMaskExpr, GenAst.ylit]
      rw [wpE.eq_2]
      dsimp only
      rw [wpE.eq_3, hacccur]
      simp only [Bopen]
      rw [stepOp_and]
      dsimp only
      rw [wpE.eq_3, hpcur]
      dsimp only
      rw [stepOp_mstore]
      refine ⟨?_⟩
      rw [wpSS.eq_2]
      simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
        List.foldl_cons, List.foldl_nil]
      rw [restore_eq_self (D := Bridge.Dialect c g) (by
        rw [venv_set_length (D := Bridge.Dialect c g),
          venv_set_length (D := Bridge.Dialect c g)])]
      have higb : VEnv.get
          ((VEnv.set
            (("i", BitVec.ofNat 256 j) ::
              (V.set "acc" (wPowers rw x1 true j).1).set "p" (BitVec.ofNat 256 (aP + 32 * j)))
            "p" newp).set "acc" newacc) "i" = some (BitVec.ofNat 256 j) := by
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "i") (v := newacc)
          (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "i") (v := newp)
          (by decide)]
        exact hig
      rw [wpS.eq_3]
      simp only [pcsPost, GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit]
      rw [wpSS.eq_3]
      rw [wpS.eq_6]
      simp only [wpE, wpA, Bopen, stepOp, bin, higb]
      refine ⟨by simp, ⟨?_⟩⟩
      rw [wpSS.eq_2]
      simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left,
        List.foldl_cons, List.foldl_nil]
      rw [restore_set_same (D := Bridge.Dialect c g)]
      have hnewi : BitVec.ofNat 256 j + litValue (Literal.number 1) =
          BitVec.ofNat 256 (j + 1) := by
        rw [show litValue (Literal.number 1) = BitVec.ofNat 256 1 from rfl,
          ← BitVec.ofNat_add]
      have hbound : aP + 32 * (j + 1) < 2 ^ 256 := by omega
      have hnewp_toNat : newp.toNat = aP + 32 * (j + 1) := by
        rw [hnewpval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
      have hf : f (j + 1) = newacc &&& litValue (Literal.number (GenAst.hexLiteral truncMask128)) := by
        rw [hnewacc]; rfl
      dsimp only [Inv]
      rw [venv_set_loop_step (V := V) (j := j) (oldAcc := (wPowers rw x1 true j).1)
        (oldP := BitVec.ofNat 256 (aP + 32 * j)) (newP := newp) (newAcc := newacc)
        (newI := BitVec.ofNat 256 j + litValue (Literal.number 1))]
      refine ⟨j + 1, by omega, ?env, ?gi, ?gacc, ?gp, ?gx1, ?gr, ?gmem, ?genv, ?ghalt⟩
      · rw [← hnewi, ← hnewpval, ← hnewacc]
      · rw [← hnewi]
        exact venv_get_cons_self (D := Bridge.Dialect c g) _ "i"
          (BitVec.ofNat 256 j + litValue (Literal.number 1))
      · rw [← hnewacc]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "acc")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc") (v := newp)
          (by decide)]
        exact venv_get_set_same (D := Bridge.Dialect c g) hacc
      · rw [← hnewpval]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "p")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        have hpold : VEnv.get (VEnv.set V "acc" newacc) "p" = some (BitVec.ofNat 256 aP) := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "p") (v := newacc)
            (by decide)]
          exact hp
        exact venv_get_set_same (D := Bridge.Dialect c g) hpold
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "x1")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "x1") (v := newp)
          (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "x1") (v := newacc)
          (by decide)]
        exact hx1
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "i") (y := "r")
          (v := BitVec.ofNat 256 j + litValue (Literal.number 1)) (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "p") (y := "r") (v := newp)
          (by decide)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "acc") (y := "r") (v := newacc)
          (by decide)]
        exact hrw
      · rw [hmemg]
        rw [show pcsWriteWords st.memory aP f (j + 1 + 1) =
            storeWord (pcsWriteWords st.memory aP f (j + 1)) (aP + 32 * (j + 1))
              (f (j + 1)) from rfl]
        rw [hnewp_toNat, ← hf]
      · rw [show (touchMemory sti (BitVec.toNat newp) 32).env = sti.env from rfl, henvg]
      · rw [show (touchMemory sti (BitVec.toNat newp) 32).halted = sti.halted from rfl, hhaltg]

/-! ## 7. The `scalar_inv` frame bridge (start)

  The first two memory-level facts the `scalar_inv` summary needs: a 32-byte `mstore` reads back
  as the big-endian byte list `bytesNatBE v 32`, and the byte encoder's digit order is the word
  reader's order. These are the store/read half of the bridge recorded in
  `BatchInvert.lean:1055-1135`; the six-store `modexpInvFrame` equality, the `fail` effect and the
  staticcall step are not landed yet, so this section adds no row. -/

/-- `Nat.toUInt8` only sees the low byte. -/
theorem toUInt8_mod (x : Nat) : Nat.toUInt8 x = Nat.toUInt8 (x % 256) := by
  apply UInt8.toNat_inj.mp
  unfold Nat.toUInt8
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_mod]

/-- The EVM `byteAt` is the base-256 digit of the word's `Nat`. -/
theorem byteAt_eq_toUInt8 (v : U256) (k : Nat) :
    EVM.byteAt v k = Nat.toUInt8 (v.toNat / 256 ^ k) := by
  unfold EVM.byteAt
  rw [show 256 ^ k = 2 ^ (8 * k) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Reversing a `range` is the complement-index map. -/
theorem range_map_reverse {α : Type} (n : Nat) (f : Nat → α) :
    (List.range n).reverse.map f = (List.range n).map (fun i => f (n - 1 - i)) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    rw [List.getElem_map, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.getElem_range, List.length_range]

/-- **THE 32-BYTE STORE/READ BRIDGE**: an `mstore` reads back as `bytesNatBE v 32`. -/
theorem readBytes_storeWord_32 (mem : Nat → UInt8) (p : Nat) (v : U256) :
    readBytes (storeWord mem p v) p 32 = (bytesNatBE v.toNat 32).data.toList := by
  unfold readBytes bytesNatBE
  dsimp only
  rw [range_map_reverse]
  show (List.range 32).map (fun i => storeWord mem p v (p + i)) =
    (List.range 32).map (fun i => Nat.toUInt8 ((v.toNat / 256 ^ (32 - 1 - i)) % 256))
  apply List.map_eq_map_iff.mpr
  intro i hi
  have hi' : i < 32 := List.mem_range.mp hi
  have hstore : storeWord mem p v (p + i) = EVM.byteAt v (31 - i) := by
    unfold storeWord
    rw [if_pos]
    · congr 1; omega
    · omega
  rw [hstore, byteAt_eq_toUInt8, show 31 - i = 32 - 1 - i by omega, toUInt8_mod]

theorem fold_byte_lt_aux (l : List UInt8) :
    ∀ (n acc : Nat), acc < 256 ^ n →
      l.foldl (fun (acc : Nat) (b : UInt8) => acc * 256 + b.toNat) acc < 256 ^ (n + l.length) := by
  induction l with
  | nil => intro n acc h; simpa using h
  | cons b rest ih =>
      intro n acc h
      simp only [List.foldl_cons, List.length_cons]
      have hb : b.toNat < 256 := UInt8.toNat_lt_size b
      have hacc : acc * 256 + b.toNat < 256 ^ (n + 1) := by
        rw [Nat.pow_succ]
        nlinarith
      have h' := ih (n + 1) (acc * 256 + b.toNat) hacc
      rwa [show n + 1 + rest.length = n + (rest.length + 1) by omega] at h'

theorem fold_byte_lt (l : List UInt8) :
    l.foldl (fun (acc : Nat) (b : UInt8) => acc * 256 + b.toNat) 0 < 256 ^ l.length := by
  have h := fold_byte_lt_aux l 0 0 (by norm_num)
  simpa using h

theorem bytesToNatBE_readBytes_32 (mem : Nat → UInt8) (p : Nat) :
    bytesToNatBE (ByteArray.mk (readBytes mem p 32).toArray) = (loadWord mem p).toNat := by
  unfold bytesToNatBE readBytes loadWord
  rw [← Array.foldl_toList]
  dsimp only
  change List.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0
    (List.map (fun i => mem (p + i)) (List.range 32)) =
    BitVec.toNat (List.foldl (fun (acc : U256) (i : Nat) =>
      acc <<< 8 ||| BitVec.ofNat 256 (mem (p + i)).toNat) 0 (List.range 32))
  have hmap : List.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0
      (List.map (fun i => mem (p + i)) (List.range 32)) =
      (List.range 32).foldl (fun (acc : Nat) (i : Nat) =>
        acc * 256 + (mem (p + i)).toNat) 0 := by
    rw [List.foldl_map]
  rw [hmap]
  have hb : ∀ i, (mem (p + i)).toNat < 256 := fun i => UInt8.toNat_lt_size _
  have h := Midfall.LoweringV3.VkWindow.fold_be_eq (fun i => (mem (p + i)).toNat) hb
    (List.range 32) 0
  have hload : (List.foldl (fun (acc : U256) (i : Nat) =>
      acc <<< 8 ||| BitVec.ofNat 256 (mem (p + i)).toNat) 0 (List.range 32)) =
      BitVec.ofNat 256 ((List.range 32).foldl
        (fun (acc : Nat) (i : Nat) => acc * 256 + (mem (p + i)).toNat) 0) := by
    simpa using h
  rw [hload, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have hlt := fold_byte_lt (List.map (fun i => mem (p + i)) (List.range 32))
  rw [List.length_map, List.length_range] at hlt
  rw [show 256 ^ 32 = 2 ^ 256 by norm_num [Nat.pow_succ]] at hlt
  rw [hmap] at hlt
  exact hlt

/-- Splitting a 32-byte read into two adjacent reads. -/
theorem readBytes_append (mem : Nat → UInt8) (p m n : Nat) :
    readBytes mem p (m + n) = readBytes mem p m ++ readBytes mem (p + m) n := by
  unfold readBytes
  rw [List.range_add, List.map_append]
  congr 1
  rw [List.map_map]
  show List.map (fun i => mem (p + (m + i))) (List.range n) =
    List.map (fun i => mem (p + m + i)) (List.range n)
  apply List.map_eq_map_iff.mpr
  intro i hi
  congr 1
  omega

/-- A store outside a read window is invisible to that read. -/
theorem readBytes_storeWord_outside (mem : Nat → UInt8) (q : Nat) (v : U256) (p n : Nat)
    (h : q + 32 ≤ p ∨ p + n ≤ q) :
    readBytes (storeWord mem q v) p n = readBytes mem p n := by
  unfold readBytes
  apply List.map_eq_map_iff.mpr
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  unfold storeWord
  rw [if_neg]
  rintro ⟨h1, h2⟩
  omega


/-! ## 8. ROW.PCS.2: block 2's x1 power table (PROVED)

  `pcsBlock2_inline` (section 4.1) turns the emitted block-2 term into the literal
  `pcsBlock2Inline a1 aP nb trunc`; the two loop walks of section 6 give the x1 power table when
  `nb > 1`. This section composes them. `pcs_b2_sem` is the child at the evidence's statement
  (`GeneratorRows.lean:986`) and `pcs_b2_sem_inline` is the same fact at the inlined term the
  slice carries.

  THE PROOF. `pcs_b2_prefix` inverts the two-statement prefix (`let x1 := mload(a1)`,
  `mstore(aP, 1)`) with the small `stepOp` inversions at the top of this section; `pcs_b2_lets`
  inverts `let acc := 1; let p := aP`; `pcs_b2_body_of_loop` threads them into `pcs_loop_*` and
  reads the table back with `pcsLoadWord_writeWords_lt`/`pcsWriteWords_outside`. The `nb ≤ 1`
  arm is `pcs_b2_small`: the emitter omits the loop there, and the unconditional `mstore` at
  `aP` is already the first (and only) table entry. No ROW hypothesis is added: this is a CHILD
  lemma (ROW.PCS.2), stated with the evidence's three layout hypotheses
  (`aP + 32*nb < 2^256`, the a1/aP disjointness, `a1 < 2^256`); all three are layout facts at the
  row, not new row hypotheses.

  The `VEnv.set`/`restore` facts are section 5's copies; the three small evaluation inversions at
  the top of this section are copies of `LagrangeRows` §7b (this file deliberately does not import
  the quotient modules), and the memory-window conjunct is spelled inline instead of importing
  `MemSameOutside` for the same reason. -/

/-- A one-element list is a singleton (copy of `LagrangeRows.list_length_one`, so this file
    does not import the quotient modules). -/
theorem b2_list_length_one {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a t =>
      cases t with
      | nil => exact ⟨a, rfl⟩
      | cons b t => simp at h

/-- A literal evaluates to its word (copy of `LagrangeRows.eval_lit_inv`). -/
theorem b2_eval_lit_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {n : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n)) (.vals [cv] st')) :
    cv = BitVec.ofNat 256 n ∧ st' = st := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A local builtin's value evaluation, split into arguments and the builtin fact (copy of
    `LagrangeRows.eval_builtin_vals_inv`). -/
theorem b2_eval_builtin_vals_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {op : EVM.Op} {args : List (Expr EVM.Op)}
    {vals : List U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op args) (.vals vals st')) :
    ∃ argvals st1, EvalArgs (Bridge.Dialect c g) funs V st args (.vals argvals st1) ∧
      (Bridge.Dialect c g).Builtin op argvals st1 (.ok vals st') := by
  cases h with
  | builtinOk hargs hbi => exact ⟨_, _, hargs, hbi⟩

theorem b2_ok_mstore {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin EVM.Op.mstore [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  have h' : stepOp EVM.Op.mstore [a, b] st = some r := h
  simp only [stepOp] at h'
  cases h'
  exact ⟨_, _, rfl⟩

theorem b2_eval_mload_lit_vals {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {k : Nat} {v : U256} {st' : EvmState} (hk : k < 2 ^ 256)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mload [Expr.lit (Literal.number k)]) (.vals [v] st')) :
    v = loadWord st.memory k ∧ st' = touchMemory st k 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ :=
    b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hhead =>
      cases hnil with
      | argsNil =>
          obtain ⟨hv, hst⟩ := b2_eval_lit_inv hhead
          rw [hv, hst] at hbi
          have hb : stepOp EVM.Op.mload [BitVec.ofNat 256 k] st =
              some (.ok [v] st') := hbi
          simp only [stepOp] at hb
          have hk' : (BitVec.ofNat 256 k).toNat = k := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
          rw [hk'] at hb
          cases hb
          exact ⟨rfl, rfl⟩

theorem b2_eval_mload_lit_halt {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {k : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mload [Expr.lit (Literal.number k)]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.mload)
    (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_mload hr)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h

theorem b2_eval_mstore_lit_vals {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {a v : Nat} {st' : EvmState} (ha : a < 2 ^ 256)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mstore
        [Expr.lit (Literal.number a), Expr.lit (Literal.number v)]) (.vals [] st')) :
    st' = { touchMemory st a 32 with memory := storeWord st.memory a (BitVec.ofNat 256 v) } := by
  obtain ⟨argvals, st1, hargs, hbi⟩ :=
    b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead1 =>
      cases hrest with
      | argsCons hnil hhead2 =>
          cases hnil with
          | argsNil =>
              obtain ⟨haa, hsta⟩ := b2_eval_lit_inv hhead1
              obtain ⟨hv, hstv⟩ := b2_eval_lit_inv hhead2
              rw [haa, hsta, hv, hstv] at hbi
              have hb : stepOp EVM.Op.mstore [BitVec.ofNat 256 a, BitVec.ofNat 256 v] st =
                  some (.ok [] st') := hbi
              simp only [stepOp] at hb
              have ha' : (BitVec.ofNat 256 a).toNat = a := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
              rw [ha'] at hb
              cases hb
              rfl

theorem b2_eval_mstore_lit_halt {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {a v : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mstore
        [Expr.lit (Literal.number a), Expr.lit (Literal.number v)]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.mstore)
    (fun _ _ _ _ hr => b2_ok_mstore hr)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h

theorem b2_exec_let_mload_lit {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    {x : String} {k : Nat} (hk : k < 2 ^ 256)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.builtin EVM.Op.mload [Expr.lit (Literal.number k)]))) V' st' o) :
    o = .normal ∧ V' = (x, loadWord st.memory k) :: V ∧ st' = touchMemory st k 32 := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := b2_list_length_one hlen
      obtain ⟨hv, hst⟩ := b2_eval_mload_lit_vals hk he
      subst hv; subst hst
      exact ⟨rfl, rfl, rfl⟩
  | letHalt he => exact (b2_eval_mload_lit_halt he).elim

theorem b2_exec_exprStmt_mstore_lit {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    {a v : Nat} (ha : a < 2 ^ 256)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin EVM.Op.mstore
        [Expr.lit (Literal.number a), Expr.lit (Literal.number v)])) V' st' o) :
    o = .normal ∧ V' = V ∧
      st' = { touchMemory st a 32 with memory := storeWord st.memory a (BitVec.ofNat 256 v) } := by
  cases h with
  | exprStmt he => exact ⟨rfl, rfl, b2_eval_mstore_lit_vals ha he⟩
  | exprStmtHalt he => exact (b2_eval_mstore_lit_halt he).elim

theorem b2_exec_let_lit {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    {x : String} {k : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.lit (Literal.number k)))) V' st' o) :
    o = .normal ∧ V' = (x, BitVec.ofNat 256 k) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := b2_list_length_one hlen
      obtain ⟨hv, hst⟩ := b2_eval_lit_inv he
      subst hv; subst hst
      exact ⟨rfl, rfl, rfl⟩
  | letHalt he => exact (Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts he).elim

/-- Composition with a mid that may depend on the pre-state. -/
theorem b2_append_dep {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {ss₁ ss₂ : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {mid : VEnv D → D.State → VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h₁ : StmtsContractAll funs ss₁ pre (fun V st V' st' o =>
      (o = .normal ∧ mid V st V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (h₂ : ∀ V st, pre V st → ∀ Vm stm, mid V st Vm stm →
      ∀ V' st' o, ExecStmts D funs Vm stm ss₂ V' st' o → post V st V' st' o) :
    StmtsContractAll funs (ss₁ ++ ss₂) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨Vm, stm, h1run, h2run⟩ | ⟨h1run, hne⟩
  · rcases h₁ V st hpre Vm stm .normal h1run with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact h₂ V st hpre Vm stm hmid V' st' o h2run
    · exact absurd rfl hne'
  · rcases h₁ V st hpre V' st' o h1run with ⟨heq, _⟩ | ⟨_, hpost⟩
    · exact absurd heq hne
    · exact hpost

/-- Composition where the head always terminates normally. -/
theorem pcs_b2_prefix {funs : FunEnv (Bridge.Dialect c g)} (a1 aP : Nat)
    (ha1b : a1 < 2 ^ 256) (haP : aP < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [GenAst.ylet "x1" (GenAst.yop EVM.Op.mload [GenAst.ylit a1]),
       GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.ylit aP, GenAst.ylit 1])]
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧
        V' = ("x1", loadWord st.memory a1) :: V ∧
        st'.memory = storeWord st.memory aP 1 ∧ st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with ⟨V1, st1, h1, h2⟩ | ⟨h1, hne⟩
  · obtain ⟨_, hV1, hst1⟩ := b2_exec_let_mload_lit (funs := funs) ha1b h1
    rw [hV1, hst1] at h2
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h2 with ⟨V2, st2, h2', h3⟩ | ⟨h2', hne2⟩
    · obtain ⟨_, hV2, hst2⟩ := b2_exec_exprStmt_mstore_lit (funs := funs) haP h2'
      cases h3
      rw [hV2, hst2]
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> rfl
    · obtain ⟨ho, _, _⟩ := b2_exec_exprStmt_mstore_lit (funs := funs) haP h2'
      exact absurd ho hne2
  · obtain ⟨ho, _, _⟩ := b2_exec_let_mload_lit (funs := funs) ha1b h1
    exact absurd ho hne

theorem pcs_b2_lets {funs : FunEnv (Bridge.Dialect c g)} (aP : Nat) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [GenAst.ylet "acc" (GenAst.ylit 1), GenAst.ylet "p" (GenAst.ylit aP)]
      (fun _ _ => True)
      (fun V st V' st' o => o = .normal ∧
        V' = ("p", BitVec.ofNat 256 aP) :: ("acc", (1 : U256)) :: V ∧ st' = st) := by
  intro V st _ V' st' o hrun
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with ⟨V1, st1, h1, h2⟩ | ⟨h1, hne⟩
  · obtain ⟨_, hV1, hst1⟩ := b2_exec_let_lit (funs := funs) (x := "acc") (k := 1) h1
    rw [hV1, hst1] at h2
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h2 with ⟨V2, st2, h2', h3⟩ | ⟨h2', hne2⟩
    · obtain ⟨_, hV2, hst2⟩ := b2_exec_let_lit (funs := funs) (x := "p") (k := aP) h2'
      cases h3
      rw [hV2, hst2]
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨ho, _, _⟩ := b2_exec_let_lit (funs := funs) (x := "p") (k := aP) h2'
      exact absurd ho hne2
  · obtain ⟨ho, _, _⟩ := b2_exec_let_lit (funs := funs) (x := "acc") (k := 1) h1
    exact absurd ho hne

theorem pcs_b2_body_of_loop {funs : FunEnv (Bridge.Dialect c g)} (nb : Nat) (trunc : Bool)
    (a1 aP : Nat) (hnb : aP + 32 * nb < 2 ^ 256) (hnb1 : nb > 1)
    (ha1 : a1 + 32 ≤ aP ∨ aP + 32 * nb ≤ a1) (ha1b : a1 < 2 ^ 256)
    (hloop : StmtsContractAll (D := Bridge.Dialect c g) funs
      [Stmt.forLoop pcsInit (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
        pcsPost (pcsLoopBody trunc)]
      (fun V st => VEnv.get V "acc" = some (1 : U256) ∧
        VEnv.get V "p" = some (BitVec.ofNat 256 aP) ∧
        (VEnv.get V "x1").isSome ∧ (VEnv.get V "r").isSome ∧
        st.memory = storeWord st.memory aP 1)
      (fun V st V' st' o => o = .normal ∧
        ∃ rw x1, VEnv.get V "r" = some rw ∧ VEnv.get V "x1" = some x1 ∧
          V' = VEnv.set (VEnv.set V "acc" (wPowers rw x1 trunc (nb - 1)).1) "p"
            (BitVec.ofNat 256 (aP + 32 * (nb - 1))) ∧
          st'.memory = pcsWriteWords st.memory aP
            (fun i => (wPowers rw x1 trunc i).2) nb ∧
          st'.env = st.env ∧ st'.halted = st.halted)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsBlock2Inline a1 aP nb trunc)
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ restore V V' = V ∧ st'.env = st.env ∧
        st'.halted = st.halted ∧ (∀ a, (a < aP ∨ aP + 32 * (max nb 1) ≤ a) → st'.memory a = st.memory a) ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          ∀ i, i < max nb 1 → loadWord st'.memory (aP + 32 * i) =
            (wPowers rw (loadWord st.memory a1) trunc i).2) := by
  intro V st hpre V' st' o hrun
  rw [pcsBlock2Inline, if_pos hnb1] at hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
    ⟨Vm, stm, h1run, h2run⟩ | ⟨h1run, hne⟩
  · obtain ⟨_, hVm, hmem, henv, hhalt⟩ :=
      pcs_b2_prefix (funs := funs) a1 aP ha1b (Nat.lt_of_le_of_lt (Nat.le_add_right aP (32 * nb)) hnb) V st hpre Vm stm .normal h1run
    rw [show [GenAst.ylet "acc" (GenAst.ylit 1), GenAst.ylet "p" (GenAst.ylit aP),
        GenAst.yfor pcsInit (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
          pcsPost (pcsLoopBody trunc)] =
        [GenAst.ylet "acc" (GenAst.ylit 1), GenAst.ylet "p" (GenAst.ylit aP)] ++
        [GenAst.yfor pcsInit (GenAst.yop EVM.Op.lt [GenAst.yvar "i", GenAst.ylit (nb - 1)])
          pcsPost (pcsLoopBody trunc)] from rfl] at h2run
    rcases Step.stmts_append_inv (D := Bridge.Dialect c g) h2run with
      ⟨Vl, stl, hlrun, hlooprun⟩ | ⟨hlrun, hne2⟩
    · obtain ⟨_, hVl, hstl⟩ :=
        pcs_b2_lets (funs := funs) aP Vm stm trivial Vl stl .normal hlrun
      rw [hVm] at hVl
      have hmemno : stl.memory = storeWord stl.memory aP 1 := by
        rw [hstl, hmem, storeWord_storeWord_same]
      have hacc : VEnv.get Vl "acc" = some (1 : U256) := by
        rw [hVl]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "acc")
          (v := BitVec.ofNat 256 aP) (by decide)]
        exact venv_get_cons_self (D := Bridge.Dialect c g) _ "acc" 1
      have hpp : VEnv.get Vl "p" = some (BitVec.ofNat 256 aP) := by
        rw [hVl]
        exact venv_get_cons_self (D := Bridge.Dialect c g) _ "p" (BitVec.ofNat 256 aP)
      have hx1s : (VEnv.get Vl "x1").isSome = true := by
        rw [hVl]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "x1")
          (v := BitVec.ofNat 256 aP) (by decide)]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "acc") (y := "x1")
          (v := (1 : U256)) (by decide)]
        rw [venv_get_cons_self (D := Bridge.Dialect c g)]
        rfl
      have hrs : (VEnv.get Vl "r").isSome = true := by
        rw [hVl]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "r")
          (v := BitVec.ofNat 256 aP) (by decide)]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "acc") (y := "r")
          (v := (1 : U256)) (by decide)]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x1") (y := "r")
          (v := loadWord st.memory a1) (by decide)]
        exact hpre
      obtain ⟨ho, rw, x1v, hrw, hx1v, hV, hmem', henv', hhalt'⟩ :=
        hloop Vl stl ⟨hacc, hpp, hx1s, hrs, hmemno⟩ V' st' o hlooprun
      have hVr : VEnv.get V "r" = some rw := by
        rw [hVl] at hrw
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "r")
          (v := BitVec.ofNat 256 aP) (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "acc") (y := "r")
          (v := (1 : U256)) (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x1") (y := "r")
          (v := loadWord st.memory a1) (by decide)] at hrw
        exact hrw
      have hx1val : x1v = loadWord st.memory a1 := by
        rw [hVl] at hx1v
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "x1")
          (v := BitVec.ofNat 256 aP) (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "acc") (y := "x1")
          (v := (1 : U256)) (by decide),
          venv_get_cons_self (D := Bridge.Dialect c g)] at hx1v
        exact (Option.some.inj hx1v).symm
      rw [hx1val] at hV hmem'
      have hrestore : restore V V' = V := by
        rw [hV, hVl]
        rw [venv_set_cons_ne (D := Bridge.Dialect c g) (x := "acc") (y := "p") (by decide)]
        rw [venv_set_cons_same (D := Bridge.Dialect c g)]
        rw [venv_set_cons_same (D := Bridge.Dialect c g)]
        simp only [restore, List.length_cons]
        rw [show List.length V + 1 + 1 + 1 - List.length V = 3 by omega]
        rfl
      refine ⟨ho, ?_⟩
      refine ⟨hrestore, ?_⟩
      refine ⟨by rw [henv', hstl, henv], ?_⟩
      refine ⟨by rw [hhalt', hstl, hhalt], ?_⟩
      refine ⟨?_, ?_⟩
      · intro a ha
        rw [show (32 * (max nb 1)) = 32 * nb from by rw [Nat.max_eq_left (Nat.le_of_lt hnb1)]] at ha
        rw [hmem']
        rw [pcsWriteWords_outside _ _ _ ha]
        rw [hstl, hmem]
        unfold storeWord
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rcases ha with h | h
        · exact absurd h1 (Nat.not_le_of_gt h)
        · have h32 : aP + 32 ≤ a :=
            Nat.le_trans (Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left 32 (Nat.le_of_lt hnb1)) aP) h
          exact absurd h2 (Nat.not_lt_of_ge h32)
      · refine ⟨rw, hVr, ?_⟩
        intro i hi
        rw [show (max nb 1) = nb from by rw [Nat.max_eq_left (Nat.le_of_lt hnb1)]] at hi
        rw [hmem']
        rw [pcsLoadWord_writeWords_lt _ _ _ hi]
    · obtain ⟨ho, _, _⟩ := pcs_b2_lets (funs := funs) aP Vm stm trivial V' st' o hlrun
      exact absurd ho hne2
  · obtain ⟨ho, _, _, _, _⟩ :=
      pcs_b2_prefix (funs := funs) a1 aP ha1b
        (Nat.lt_of_le_of_lt (Nat.le_add_right aP (32 * nb)) hnb) V st hpre V' st' o h1run
    exact absurd ho hne
/-- The `nb ≤ 1` arm: the block is the two-statement prefix only. -/
theorem pcs_b2_small {funs : FunEnv (Bridge.Dialect c g)} (nb : Nat) (trunc : Bool)
    (a1 aP : Nat) (hnb : aP + 32 * nb < 2 ^ 256) (hnb1 : ¬ nb > 1)
    (ha1b : a1 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsBlock2Inline a1 aP nb trunc)
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ restore V V' = V ∧ st'.env = st.env ∧
        st'.halted = st.halted ∧ (∀ a, (a < aP ∨ aP + 32 * (max nb 1) ≤ a) → st'.memory a = st.memory a) ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          ∀ i, i < max nb 1 → loadWord st'.memory (aP + 32 * i) =
            (wPowers rw (loadWord st.memory a1) trunc i).2) := by
  intro V st hpre V' st' o hrun
  rw [pcsBlock2Inline, if_neg hnb1] at hrun
  rw [List.append_nil] at hrun
  obtain ⟨ho, hVm, hmem, henv, hhalt⟩ :=
    pcs_b2_prefix (funs := funs) a1 aP ha1b
      (Nat.lt_of_le_of_lt (Nat.le_add_right aP (32 * nb)) hnb) V st hpre V' st' o hrun
  have hrestore : restore V V' = V := by
    rw [hVm]
    simp only [restore, List.length_cons]
    rw [show List.length V + 1 - List.length V = 1 by omega]
    rfl
  refine ⟨ho, ?_⟩
  refine ⟨hrestore, ?_⟩
  refine ⟨henv, ?_⟩
  refine ⟨hhalt, ?_⟩
  refine ⟨?_, ?_⟩
  · intro a ha
    have hmax : max nb 1 = 1 := Nat.max_eq_right (Nat.le_of_not_gt hnb1)
    rw [hmax] at ha
    rw [hmem]
    unfold storeWord
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rcases ha with h | h
    · exact absurd h1 (Nat.not_le_of_gt h)
    · have h32 : aP + 32 ≤ a := by
        have h1' : aP + 32 * 1 ≤ a := by simpa using h
        exact Nat.le_trans (Nat.add_le_add_left (le_refl 32) aP) h1'
      exact absurd h2 (Nat.not_lt_of_ge h32)
  · obtain ⟨rw, hrw⟩ := Option.isSome_iff_exists.mp hpre
    refine ⟨rw, hrw, ?_⟩
    intro i hi
    have hmax : max nb 1 = 1 := Nat.max_eq_right (Nat.le_of_not_gt hnb1)
    rw [hmax] at hi
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    rw [hmem, Nat.mul_zero, Nat.add_zero]
    rw [Midfall.Yul.Word.loadWord_storeWord_same]
    rfl

theorem pcs_b2_body {funs : FunEnv (Bridge.Dialect c g)} (nb : Nat) (trunc : Bool)
    (a1 aP : Nat) (hnb : aP + 32 * nb < 2 ^ 256)
    (ha1 : a1 + 32 ≤ aP ∨ aP + 32 * nb ≤ a1) (ha1b : a1 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsBlock2Inline a1 aP nb trunc)
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ restore V V' = V ∧ st'.env = st.env ∧
        st'.halted = st.halted ∧ (∀ a, (a < aP ∨ aP + 32 * (max nb 1) ≤ a) → st'.memory a = st.memory a) ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          ∀ i, i < max nb 1 → loadWord st'.memory (aP + 32 * i) =
            (wPowers rw (loadWord st.memory a1) trunc i).2) := by
  by_cases hnb1 : nb > 1
  · cases trunc
    · exact pcs_b2_body_of_loop (c := c) (g := g) (funs := funs) nb false a1 aP hnb hnb1 ha1 ha1b
        (pcs_loop_false (c := c) (g := g) (funs := funs) ([] : Inline.Consts) rfl nb hnb1 aP hnb)
    · exact pcs_b2_body_of_loop (c := c) (g := g) (funs := funs) nb true a1 aP hnb hnb1 ha1 ha1b
        (pcs_loop_true (c := c) (g := g) (funs := funs) ([] : Inline.Consts) rfl nb hnb1 aP hnb)
  · exact pcs_b2_small (c := c) (g := g) (funs := funs) nb trunc a1 aP hnb hnb1 ha1b

/-! ### 8.1 The shape of the `.pcs` slice (PROVED)

  The evidence's `pcs_slice_of_ok` (`GeneratorRows.lean:960`) says the slice is
  `Inline.inlineContractConstants consts blocks.flatten`. That is FALSE at this tree: the inliner
  keeps every `Stmt.block` wrapper (`InlineConstants.lean:322`), so the slice is ONE outer block
  whose body is the eight inlined blocks. `pcs_slice_of_ok` below is the true shape (and records
  the non-emptiness PG-PCS-EMIT requires); `pcs_slice_of_fault` is the evidence's fault-arm
  finding, still true: on `.error` the slice is `[]`. -/

/-- **THE SUCCESS-ARM SHAPE OF THE `.pcs` SLICE.** One outer `Stmt.block`; its body is the
    inlined `blocks`, each still wrapped in its own `Stmt.block`. -/
theorem pcs_slice_of_ok (R : Render p G₁ G₂ Gₜ) (blocks : List (Block EVM.Op))
    (h : GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
      R.pv.truncatedChallenges false = .ok blocks) (hn : blocks ≠ []) :
    R.slice Partial.pcs =
      [Stmt.block (Inline.inlineContractConstantsAt 63 R.consts (blocks.map Stmt.block))] := by
  show Inline.inlineContractConstants R.consts
      (GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) Partial.pcs) = _
  rw [GenAst.emitPartialM, if_neg (by decide : ¬ (Partial.pcs = Partial.quotientLin))]
  show Inline.inlineContractConstants R.consts (GenAst.emitPartial R.pv Partial.pcs) = _
  rw [GenAst.emitPartial]
  show Inline.inlineContractConstants R.consts
      (match GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
        R.pv.truncatedChallenges false with
      | .ok [] => []
      | .ok blocks => [Stmt.block (blocks.map Stmt.block)]
      | .error _ => []) = _
  rw [h]
  cases blocks with
  | nil => exact absurd rfl hn
  | cons b bs => rfl

/-- **THE FAULT ARM** (the evidence's PG-PCS-EMIT finding, restated at V3): a faulting PCS
    emitter leaves the slice EMPTY, so the `.pcs` row is false on that arm (its exit claims a
    `Decoded` the parser never established). -/
theorem pcs_slice_of_fault (R : Render p G₁ G₂ Gₜ) (f : Midfall.Halo2.Fault)
    (h : GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
      R.pv.truncatedChallenges false = .error f) :
    R.slice Partial.pcs = [] := by
  show Inline.inlineContractConstants R.consts
      (GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) Partial.pcs) = _
  rw [GenAst.emitPartialM, if_neg (by decide : ¬ (Partial.pcs = Partial.quotientLin))]
  show Inline.inlineContractConstants R.consts (GenAst.emitPartial R.pv Partial.pcs) = _
  rw [GenAst.emitPartial]
  show Inline.inlineContractConstants R.consts
      (match GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
        R.pv.truncatedChallenges false with
      | .ok [] => []
      | .ok blocks => [Stmt.block (blocks.map Stmt.block)]
      | .error _ => []) = _
  rw [h]
  rfl

/-- **ROW.PCS.2 (block 2 of the PCS region), PROVED**: the emitted x1 power table. -/
theorem pcs_b2_sem {funs : FunEnv (Bridge.Dialect c g)} (nb : Nat) (trunc : Bool) (a1 aP : Nat)
    (hnb : aP + 32 * nb < 2 ^ 256)
    (ha1 : a1 + 32 ≤ aP ∨ aP + 32 * nb ≤ a1) (ha1b : a1 < 2 ^ 256) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.block (pcsBlock2Inline a1 aP nb trunc))
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ V' = V ∧ st'.env = st.env ∧
        st'.halted = st.halted ∧ (∀ a, (a < aP ∨ aP + 32 * (max nb 1) ≤ a) → st'.memory a = st.memory a) ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          ∀ i, i < max nb 1 → loadWord st'.memory (aP + 32 * i) =
            (wPowers rw (loadWord st.memory a1) trunc i).2) := by
  intro V st hpre V' st' o hrun
  cases hrun with
  | block hbody =>
      exact pcs_b2_body (funs := hoist (Bridge.Dialect c g) (pcsBlock2Inline a1 aP nb trunc) :: funs)
        nb trunc a1 aP hnb ha1 ha1b V st hpre _ _ _ hbody

/-- One-statement sequences: `StmtContractAll` at a single statement is `StmtsContractAll`. -/
theorem stmtsContractAll_singleton {D : Dialect} [DecidableEq D.Value] {funs : FunEnv D}
    {s : Stmt D.Op} {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtContractAll funs s pre post) : StmtsContractAll funs [s] pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv (D := D) hrun with ⟨V1, st1, h1, h2⟩ | ⟨h1, _⟩
  · cases h2
    exact h V st hpre _ _ _ h1
  · exact h V st hpre V' st' o h1

/-- **ROW.PCS.2 at the term the slice carries**: `pcs_b2_sem` after the block-2 inliner
    alignment. The constants are the render's own table (an arbitrary `consts` with the three
    lookups), so no render is named. -/
theorem pcs_b2_sem_inline {funs : FunEnv (Bridge.Dialect c g)} (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (nb : Nat) (trunc : Bool) (a1 aP : Nat)
    (h1 : consts.lookup "X1_MPTR" = some a1) (hP : consts.lookup "X1_POWERS_MPTR" = some aP)
    (hnb : aP + 32 * nb < 2 ^ 256)
    (ha1 : a1 + 32 ≤ aP ∨ aP + 32 * nb ≤ a1) (ha1b : a1 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [Stmt.block (Inline.inlineContractConstants consts (GenAstPcs.pcsBlock2Ast nb trunc))]
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ V' = V ∧ st'.env = st.env ∧
        st'.halted = st.halted ∧ (∀ a, (a < aP ∨ aP + 32 * (max nb 1) ≤ a) → st'.memory a = st.memory a) ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          ∀ i, i < max nb 1 → loadWord st'.memory (aP + 32 * i) =
            (wPowers rw (loadWord st.memory a1) trunc i).2) := by
  rw [pcsBlock2_inline consts hr nb trunc a1 aP h1 hP]
  exact stmtsContractAll_singleton (pcs_b2_sem (c := c) (g := g) (funs := funs)
    nb trunc a1 aP hnb ha1 ha1b)


/-! ## 9. Block 1: the ROT_POINTS walk (ROW.PCS.1, walk half)

  `pcsBlock1Ast` (`GenAstPcs.lean:131`) walks `x_pow_of_omega` forward over the rotations
  `1..maxRot` by `mulmod(·, omega, r)` and backward over `-1..minRot` by
  `mulmod(·, omega_inv, r)`, storing the current value at `ROT_POINTS_MPTR + 32*idx` for every
  rotation in the distinct set (`findIdx?` gives `idx`). This section is the WALK contract:
  `b1_walk_contract` takes a list of rotations, proves every step normal, tracks the walk value
  (`wWalk`), proves the entry written for each element is the prefix value, and proves that an
  index not written keeps its load. `b1_store_step` is the one-element instance
  (`walkStep` then the optional store).

  Not yet here: the head (four lets plus the rot-0 store) and the block assembly over
  `pcsBlock1Ast rots maxRot minRot false ps`; those are the remaining half of ROW.PCS.1. No
  register row is added; no hypothesis is added to any row.
-/

/-! ### `findIdx?` spec -/

theorem findIdx?_some_lt {α : Type} {l : List α} {p : α → Bool} {i : Nat}
    (h : l.findIdx? p = some i) : i < l.length :=
  (List.findIdx?_eq_some_iff_getElem.mp h).1

theorem findIdx?_some_spec {α : Type} {l : List α} {p : α → Bool} {i : Nat}
    (h : l.findIdx? p = some i) (hi : i < l.length) : p (l[i]'hi) = true :=
  (List.findIdx?_eq_some_iff_getElem.mp h).2.1

theorem findIdx?_prev_false {α : Type} {l : List α} {p : α → Bool} {i : Nat}
    (h : l.findIdx? p = some i) : ∀ (j : Nat) (hj : j < l.length), j < i → p (l[j]'hj) = false := by
  intro j hj hji
  have hnot := (List.findIdx?_eq_some_iff_getElem.mp h).2.2 j hji
  simpa using hnot

theorem findIdx?_eq_some_of {α : Type} {l : List α} {p : α → Bool} {i : Nat}
    (hi : i < l.length) (hp : p (l[i]'hi) = true)
    (hprev : ∀ (j : Nat) (hj : j < l.length), j < i → p (l[j]'hj) = false) :
    l.findIdx? p = some i := by
  refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hi, hp, ?_⟩
  intro j hj
  rw [hprev j (Nat.lt_trans hj hi) hj]
  simp

theorem findIdx?_beq_getElem {l : List Int} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.findIdx? (fun r => r == l[i]'hi) = some i := by
  refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hi, by simp, ?_⟩
  intro j hj hji
  have hjl : j < l.length := Nat.lt_trans hj hi
  rw [beq_iff_eq] at hji
  have heq : l[j]'hjl = l[i]'hi := by simpa using hji
  have := (hnd.getElem_inj (hi := hjl) (hj := hi)).mp heq
  omega

theorem findIdx?_beq_inj {l : List Int} {a b : Int} {ia ib : Nat}
    (ha : l.findIdx? (fun r => r == a) = some ia)
    (hb : l.findIdx? (fun r => r == b) = some ib) (hab : ia = ib) : a = b := by
  subst hab
  have hia : ia < l.length := findIdx?_some_lt ha
  have h1 := findIdx?_some_spec ha hia
  have h2 := findIdx?_some_spec hb hia
  simp only [beq_iff_eq] at h1 h2
  exact h1.symm.trans h2

/-- A variable evaluates to its value (copy of `LagrangeRows.eval_var_inv`). -/
theorem b1_eval_var_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : Ident} {av : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var x) (.vals [av] st')) :
    VEnv.get V x = some av ∧ st' = st := by
  cases h with
  | var hget => exact ⟨hget, rfl⟩

/-! ### Block 1: definitions -/

/-- The x_pow walk: `v` then one `mulmod(·, b, rv)` per element. -/
def wWalk (v b rv : U256) : List Int → U256
  | [] => v
  | _ :: rest => wWalk (wMulmodAt v b rv) b rv rest

/-- The table entry a rotation must hold. -/
def rotVal (xv om oi rv : U256) (rot : Int) : U256 :=
  if 0 ≤ rot then wWalk xv om rv (Midfall.Generator.intRangeInclusive 1 rot)
  else wWalk xv oi rv (Midfall.Generator.intRangeInclusive 1 (-rot))

/-- The block's store statement for one rotation, as `pcsBlock1Ast` builds it. -/
def b1Store (rots : List Int) (rot : Int) : Option (Stmt EVM.Op) :=
  (rots.findIdx? (fun r => r == rot)).map fun idx =>
    GenAst.yexpr (GenAst.yop EVM.Op.mstore
      [GenAst.yop EVM.Op.add [GenAst.yvar "ROT_POINTS_MPTR",
         GenAst.ylit (idx * Midfall.Generator.wordBytes)],
       GenAst.yvar "x_pow_of_omega"])

/-! ### Exec inversions -/

theorem b1_eval_mulmod_vars_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x y z : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mulmod [Expr.var x, Expr.var y, Expr.var z]) (.vals [cv] st')) :
    ∃ xv yv zv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      cv = wMulmodAt xv yv zv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ :=
    b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hrest with
      | argsCons hrest2 hy =>
          cases hrest2 with
          | argsCons hnil hz =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hzv, hstz⟩ := b1_eval_var_inv hz
                  obtain ⟨hyv, hsty⟩ := b1_eval_var_inv hy
                  obtain ⟨hxv, hstx⟩ := b1_eval_var_inv hx
                  rw [hstx, hsty, hstz] at hbi
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨_, _, _, hxv, hyv, hzv, rfl, rfl⟩


/-! ### More exec inversions -/

theorem b1_eval_mload_var_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {p : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mload [Expr.var p]) (.vals [cv] st')) :
    ∃ pv, VEnv.get V p = some pv ∧ cv = loadWord st.memory pv.toNat ∧
      st' = touchMemory st pv.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hp =>
      cases hnil with
      | argsNil =>
          obtain ⟨hpv, hst⟩ := b1_eval_var_inv hp
          rw [hst] at hbi
          simp only [builtinWithExternal, stepOp] at hbi
          cases hbi
          exact ⟨_, hpv, rfl, rfl⟩

theorem b1_eval_mload_var_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {p : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mload [Expr.var p]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.mload)
    (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_mload hr)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h

theorem b1_eval_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {b : String} {off : Nat} {cv : U256}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.add [Expr.var b, Expr.lit (Literal.number off)]) (.vals [cv] st')) :
    ∃ bv, VEnv.get V b = some bv ∧ cv = bv + BitVec.ofNat 256 off ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hb =>
      cases hrest with
      | argsCons hnil hl =>
          cases hnil with
          | argsNil =>
              obtain ⟨hv, hst⟩ := b2_eval_lit_inv hl
              obtain ⟨hbv, hstv⟩ := b1_eval_var_inv hb
              subst hst; subst hstv
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, hbv, by rw [hv], rfl⟩

theorem b1_eval_add_var_lit_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {b : String} {off : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.add [Expr.var b, Expr.lit (Literal.number off)]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.add)
    (fun _ _ _ _ hr => by
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h

theorem b1_ok_mstore {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin EVM.Op.mstore [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  have h' : stepOp EVM.Op.mstore [a, b] st = some r := h
  simp only [stepOp] at h'
  cases h'
  exact ⟨_, _, rfl⟩

theorem b1_eval_args_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {es : List (Expr EVM.Op)} {st' : EvmState}
    (hne : ∀ e ∈ es, ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False)
    (h : EvalArgs (Bridge.Dialect c g) funs V st es (.halt st')) : False := by
  induction es generalizing st with
  | nil => cases h
  | cons e rest ih =>
      cases h with
      | argsRestHalt h' =>
          exact ih (fun e' he' => hne e' (List.mem_cons_of_mem _ he')) h'
      | argsHeadHalt _ h' => exact hne e (by simp) _ _ h'

theorem b1_eval_mulmod_vars_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {a b z : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mulmod [Expr.var a, Expr.var b, Expr.var z]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest ha =>
          cases hrest with
          | argsCons hrest2 hb2 =>
              cases hrest2 with
              | argsCons hnil hz =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;>
          exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

theorem b1_eval_mstore_add_var_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {p val : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mstore
        [Expr.builtin EVM.Op.add [Expr.var p, Expr.lit (Literal.number off)],
         Expr.var val]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hval =>
          cases hrest with
          | argsCons hnil haddr =>
              cases hnil with
              | argsNil =>
                  simp only [builtinWithExternal, stepOp] at hbi
                  cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact b1_eval_add_var_lit_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

theorem b1_exec_yset_mulmod {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x a b z : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.yset x (GenAst.yop EVM.Op.mulmod
        [GenAst.yvar a, GenAst.yvar b, GenAst.yvar z])) V' st' o) :
    o = .normal ∧ ∃ av bv zv, VEnv.get V a = some av ∧ VEnv.get V b = some bv ∧
      VEnv.get V z = some zv ∧ V' = VEnv.set V x (wMulmodAt av bv zv) ∧ st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨av, bv, zv, ha, hb, hz, hcv, hst⟩ := b1_eval_mulmod_vars_inv he
      subst hcv; subst hst
      exact ⟨rfl, _, _, _, ha, hb, hz, rfl, rfl⟩
  | assignHalt he => exact (b1_eval_mulmod_vars_halt he).elim

theorem b1_exec_ylet_mload_var {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x p : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.yop EVM.Op.mload [GenAst.yvar p])) V' st' o) :
    o = .normal ∧ ∃ pv, VEnv.get V p = some pv ∧
      V' = (x, loadWord st.memory pv.toNat) :: V ∧ st' = touchMemory st pv.toNat 32 := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨pv, hp, hcv, hst⟩ := b1_eval_mload_var_inv he
      subst hcv; subst hst
      exact ⟨rfl, _, hp, rfl, rfl⟩
  | letHalt he => exact (b1_eval_mload_var_halt he).elim

theorem b1_exec_ylet_var {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x y : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.yvar y)) V' st' o) :
    o = .normal ∧ ∃ yv, VEnv.get V y = some yv ∧ V' = (x, yv) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨hyv, hst⟩ := b1_eval_var_inv he
      exact ⟨rfl, _, hyv, rfl, hst⟩
  | letHalt he => exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts he).elim

theorem b1_exec_mstore_add_var {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {p val : String} {off : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.yexpr (GenAst.yop EVM.Op.mstore
        [GenAst.yop EVM.Op.add [GenAst.yvar p, GenAst.ylit off], GenAst.yvar val])) V' st' o) :
    o = .normal ∧ V' = V ∧ ∃ pv vv, VEnv.get V p = some pv ∧ VEnv.get V val = some vv ∧
      st'.memory = storeWord st.memory (pv + BitVec.ofNat 256 off).toNat vv ∧
      st'.env = st.env ∧ st'.halted = st.halted := by
  cases h with
  | exprStmt he =>
      obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv he
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsCons hnil htail =>
              cases hnil with
              | argsNil =>
                  obtain ⟨pv, hpv, hcv, hst2⟩ := b1_eval_add_var_lit_inv hhead
                  obtain ⟨hvv, hst1⟩ := b1_eval_var_inv htail
                  rw [hcv, hst2, hst1] at hbi
                  simp only [builtinWithExternal, stepOp] at hbi
                  cases hbi
                  exact ⟨rfl, rfl, pv, _, hpv, hvv, rfl, rfl, rfl⟩
  | exprStmtHalt he => exact (b1_eval_mstore_add_var_halt he).elim


/-! ### Address arithmetic for the table -/

theorem b1_addr_toNat {R idx : Nat} (hR : R < 2 ^ 256) (hi : idx * 32 < 2 ^ 256)
    (hsum : R + idx * 32 < 2 ^ 256) :
    ((BitVec.ofNat 256 R) + BitVec.ofNat 256 (idx * 32)).toNat = R + idx * 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hi]
  exact Nat.mod_eq_of_lt hsum

theorem b1_addr_disjoint {R idx idx' : Nat} (h : idx ≠ idx') :
    R + idx * 32 + 32 ≤ R + idx' * 32 ∨ R + idx' * 32 + 32 ≤ R + idx * 32 := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · left
    have : idx + 1 ≤ idx' := hlt
    nlinarith
  · right
    have : idx' + 1 ≤ idx := hgt
    nlinarith

theorem loadWord_storeWord_at_eq {mem : Nat → UInt8} {p q : Nat} {v : U256} (hpq : q = p) :
    loadWord (storeWord mem p v) q = v := by
  rw [hpq]; exact Midfall.Yul.Word.loadWord_storeWord_same mem p v

theorem loadWord_storeWord_at_ne {mem : Nat → UInt8} {p q : Nat} {v : U256}
    (h : q + 32 ≤ p ∨ p + 32 ≤ q) :
    loadWord (storeWord mem p v) q = loadWord mem q :=
  Midfall.Yul.Word.loadWord_storeWord_disjoint mem p q v h

theorem b1_stmt_of_singleton {funs : FunEnv (Bridge.Dialect c g)} {s : Stmt EVM.Op}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st [s] V' st' o) :
    ExecStmt (Bridge.Dialect c g) funs V st s V' st' o := by
  cases h with
  | seqCons h1 h2 => cases h2; exact h1
  | seqStop h1 _ => exact h1

/-! ### One walk step (walkStep then the optional table store) -/

theorem b1_store_step {funs : FunEnv (Bridge.Dialect c g)} (rots : List Int) (rot : Int)
    (w : String) (v wv rv : U256) (mem0 : Nat → UInt8) (R : Nat)
    (hR : R < 2 ^ 256) (hlen : R + rots.length * 32 ≤ 2 ^ 256)
    (hidx : ∀ idx, rots.findIdx? (fun r => r == rot) = some idx → idx < rots.length) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      ([GenAstPcs.walkStep w] ++ (b1Store rots rot).toList)
      (fun V st => VEnv.get V "x_pow_of_omega" = some v ∧ VEnv.get V w = some wv ∧
        VEnv.get V "r" = some rv ∧
        VEnv.get V "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st.memory a = mem0 a))
      (fun V st V' st' o => o = .normal ∧
        V' = VEnv.set V "x_pow_of_omega" (wMulmodAt v wv rv) ∧
        (∀ idx, rots.findIdx? (fun r => r == rot) = some idx →
            loadWord st'.memory (R + idx * 32) = wMulmodAt v wv rv) ∧
        (∀ idx, rots.findIdx? (fun r => r == rot) ≠ some idx →
            loadWord st'.memory (R + idx * 32) = loadWord st.memory (R + idx * 32)) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st'.memory a = mem0 a) ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hv, hwv, hrv, hRpt, hout⟩ := hpre
  obtain ⟨V1, st1, h1, h2⟩ | ⟨h1, hne⟩ :=
    Step.stmts_append_inv (D := Bridge.Dialect c g) hrun
  · -- the walkStep
    have h1' : ExecStmt (Bridge.Dialect c g) funs V st
        (GenAst.yset "x_pow_of_omega" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "x_pow_of_omega", GenAst.yvar w, GenAst.yvar "r"])) V1 st1 .normal :=
      b1_stmt_of_singleton h1
    obtain ⟨_, av, bv, zv, ha, hb, hz, hV1, hst1⟩ := b1_exec_yset_mulmod h1'
    have hav : av = v := Option.some.inj (ha.symm.trans hv)
    have hbv : bv = wv := Option.some.inj (hb.symm.trans hwv)
    have hzv : zv = rv := Option.some.inj (hz.symm.trans hrv)
    have hV1' : V1 = VEnv.set V "x_pow_of_omega" (wMulmodAt v wv rv) := by
      rw [hV1, hav, hbv, hzv]
    cases hV1'
    cases hst1
    -- the optional store
    cases hf : rots.findIdx? (fun r => r == rot) with
    | none =>
        rw [show (b1Store rots rot).toList = [] by simp [b1Store, hf]] at h2
        cases h2
        refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
        · intro idx hidx; cases hidx
        · intro idx _; rfl
        · exact hout
    | some idx =>
        rw [show (b1Store rots rot).toList =
            [GenAst.yexpr (GenAst.yop EVM.Op.mstore
              [GenAst.yop EVM.Op.add [GenAst.yvar "ROT_POINTS_MPTR",
                 GenAst.ylit (idx * Midfall.Generator.wordBytes)],
               GenAst.yvar "x_pow_of_omega"])] by simp [b1Store, hf]] at h2
        obtain ⟨ho, hV2, pv, vv, hpv, hvv, hmem, henv, hhalt⟩ :=
          b1_exec_mstore_add_var (b1_stmt_of_singleton h2)
        have hRpt' : VEnv.get (VEnv.set V "x_pow_of_omega" (wMulmodAt v wv rv))
            "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
            (y := "ROT_POINTS_MPTR") (by decide)]
          exact hRpt
        rw [hRpt'] at hpv
        have hpv' : pv = BitVec.ofNat 256 R := (Option.some.inj hpv).symm
        subst hpv'
        have hvv' : vv = wMulmodAt v wv rv := by
          have hx : VEnv.get (VEnv.set V "x_pow_of_omega" (wMulmodAt v wv rv))
              "x_pow_of_omega" = some (wMulmodAt v wv rv) :=
            venv_get_set_same (D := Bridge.Dialect c g) hv
          exact Option.some.inj (hvv.symm.trans hx)
        subst hvv'
        have hidx' : idx < rots.length := hidx idx hf
        have hidx_le : idx * 32 < rots.length * 32 :=
          Nat.mul_lt_mul_of_pos_right hidx' (by norm_num)
        have hidx32 : idx * 32 < 2 ^ 256 :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hidx_le (Nat.le_add_left _ _)) hlen
        have hsum : R + idx * 32 < 2 ^ 256 :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left hidx_le R) hlen
        have haddr : ((BitVec.ofNat 256 R) + BitVec.ofNat 256 (idx * 32)).toNat
            = R + idx * 32 := b1_addr_toNat hR hidx32 hsum
        rw [show Midfall.Generator.wordBytes = 32 from rfl] at hmem
        rw [haddr] at hmem
        refine ⟨ho, hV2, ?_, ?_, ?_, by rw [henv], by rw [hhalt]⟩
        · intro idx' hidx'
          have hidx'' : idx = idx' := Option.some.inj hidx'
          subst hidx''
          rw [hmem, Midfall.Yul.Word.loadWord_storeWord_same]
        · intro idx' hidx'
          have hne : idx' ≠ idx := by
            intro heq; exact hidx' (by rw [heq])
          rw [hmem]
          exact Midfall.Yul.Word.loadWord_storeWord_disjoint st.memory (R + idx * 32)
            (R + idx' * 32) (wMulmodAt v wv rv) (b1_addr_disjoint hne)
        · intro a ha
          rw [hmem]
          unfold storeWord
          rw [if_neg]
          · exact hout a ha
          · rintro ⟨h1, h2⟩
            rcases ha with h | h
            · omega
            · have : idx * 32 + 32 ≤ rots.length * 32 := by nlinarith
              omega

  · obtain ⟨ho, _, _, _, _, _, _, _⟩ := b1_exec_yset_mulmod (b1_stmt_of_singleton h1)
    exact absurd ho hne


/-- The walk's precondition, named so the induction's hypothesis matches syntactically. -/
def b1Pre {c : ExternalCalls} {g : ExternalGas} (rots : List Int) (w : String)
    (v0 wv rv : U256) (mem0 : Nat -> UInt8) (R : Nat)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  VEnv.get V "x_pow_of_omega" = some v0 ∧ VEnv.get V w = some wv ∧
    VEnv.get V "r" = some rv ∧
    VEnv.get V "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) ∧
    (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st.memory a = mem0 a)

/-! ### The walk over a list -/

theorem b1_walk_contract {funs : FunEnv (Bridge.Dialect c g)} (rots l : List Int) (w : String)
    (v0 wv rv : U256) (mem0 : Nat → UInt8) (R : Nat)
    (hw : w ≠ "x_pow_of_omega")
    (hnd : rots.Nodup) (hR : R < 2 ^ 256) (hb : R + rots.length * 32 ≤ 2 ^ 256)
    (hwrite : ∀ rot ∈ l, ∀ idx, rots.findIdx? (fun r => r == rot) = some idx →
      idx < rots.length) (hlnd : l.Nodup) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (l.flatMap (fun rot => [GenAstPcs.walkStep w] ++ (b1Store rots rot).toList))
      (b1Pre rots w v0 wv rv mem0 R)
      (fun V st V' st' o => o = .normal ∧
        V' = VEnv.set V "x_pow_of_omega" (wWalk v0 wv rv l) ∧
        (∀ (i : Nat) (hi : i < l.length) (idx : Nat),
            rots.findIdx? (fun r => r == l[i]'hi) = some idx →
            loadWord st'.memory (R + idx * 32) = wWalk v0 wv rv (l.take (i + 1))) ∧
        (∀ (idx : Nat), (∀ (i : Nat) (hi : i < l.length),
            rots.findIdx? (fun r => r == l[i]'hi) ≠ some idx) →
            loadWord st'.memory (R + idx * 32) = loadWord st.memory (R + idx * 32)) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st'.memory a = mem0 a) ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  induction l generalizing v0 with
  | nil =>
      intro V st hpre V' st' o hrun
      cases hrun
      refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · rw [show wWalk v0 wv rv [] = v0 from rfl]
        exact (venv_set_eq_self (D := Bridge.Dialect c g) hpre.1).symm
      · intro i hi; simp at hi
      · intro idx _; rfl
      · exact hpre.2.2.2.2
  | cons rot rest ih =>
      intro V st hpre V' st' o hrun
      rw [List.flatMap_cons] at hrun
      rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
        ⟨V1, st1, hrun1, hrun2⟩ | ⟨hrun1, hne⟩
      · obtain ⟨ho1, hV1, hread1, hunw1, hout1, henv1, hhalt1⟩ :=
          b1_store_step rots rot w v0 wv rv mem0 R hR hb (hwrite rot (by simp))
            V st hpre V1 st1 .normal hrun1
        -- IH at the post-step state
        have hpre2 : b1Pre rots w (wMulmodAt v0 wv rv) wv rv mem0 R V1 st1 := by
          rw [hV1]
          refine ⟨?_, ?_, ?_, ?_, hout1⟩
          · exact venv_get_set_same (D := Bridge.Dialect c g) hpre.1
          · rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega") (y := w)
              hw]
            exact hpre.2.1
          · rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega") (y := "r")
              (by decide)]
            exact hpre.2.2.1
          · rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
              (y := "ROT_POINTS_MPTR") (by decide)]
            exact hpre.2.2.2.1
        have hwrite' : ∀ rot ∈ rest, ∀ (idx : Nat),
            rots.findIdx? (fun r => r == rot) = some idx → idx < rots.length :=
          fun rot hrot => hwrite rot (List.mem_cons_of_mem _ hrot)
        have hlnd' : rest.Nodup := (List.nodup_cons.mp hlnd).2
        obtain ⟨ho2, hV2, hread2, hunw2, hout2, henv2, hhalt2⟩ :=
          ih (wMulmodAt v0 wv rv) hwrite' hlnd' V1 st1 hpre2 V' st' o hrun2
        refine ⟨ho2, ?_, ?_, ?_, hout2, by rw [henv2, henv1], by rw [hhalt2, hhalt1]⟩
        · rw [hV2, hV1, venv_set_set (D := Bridge.Dialect c g)]
          rfl
        · -- the head's entry
          intro i hi idx hidx
          cases i with
          | zero =>
              have hread1' := hread1 idx hidx
              have hnv : ∀ (j : Nat) (hj : j < rest.length),
                  rots.findIdx? (fun r => r == rest[j]'hj) ≠ some idx := by
                intro j hj hfind
                have hrot : rot = rest[j]'hj := findIdx?_beq_inj hidx hfind rfl
                have hmem : rest[j]'hj ∈ rest := List.getElem_mem hj
                rw [← hrot] at hmem
                exact (List.nodup_cons.mp hlnd).1 hmem
              rw [hunw2 idx hnv, hread1']
              rfl
          | succ i =>
              have hri : i < rest.length := by simpa using hi
              have hidx' : rots.findIdx? (fun r => r == rest[i]'hri) = some idx := by
                simpa using hidx
              have h := hread2 i hri idx hidx'
              simpa [wWalk, List.take_succ_cons] using h
        · -- unwritten indices
          intro idx hnot
          have hnotrest : ∀ (j : Nat) (hj : j < rest.length),
              rots.findIdx? (fun r => r == rest[j]'hj) ≠ some idx := by
            intro j hj
            exact hnot (j + 1) (by simpa using hj)
          have hnot0 : rots.findIdx? (fun r => r == rot) ≠ some idx := by
            intro hfind
            exact (hnot 0 (by simp)) (by simpa using hfind)
          rw [hunw2 idx hnotrest, hunw1 idx hnot0]
      · obtain ⟨ho, _, _, _, _, _, _⟩ :=
          b1_store_step rots rot w v0 wv rv mem0 R hR hb (hwrite rot (by simp))
            V st hpre V' st' o hrun1
        exact absurd ho hne


/-! ### The rotation index lists -/

theorem intRangeInclusive_one_eq (m : Int) (hm : 1 ≤ m) :
    Midfall.Generator.intRangeInclusive 1 m =
      (List.range (Int.toNat m)).map (fun k => (1 : Int) + Int.ofNat k) := by
  unfold Midfall.Generator.intRangeInclusive
  rw [if_neg (by omega)]
  have h : m - 1 + 1 = m := by ring
  rw [h]

theorem intRange_rev_eq (mn : Int) (hm : mn < 0) :
    (Midfall.Generator.intRange mn 0).reverse =
      (List.range (Int.toNat (-mn))).map (fun k => -((1 : Int) + Int.ofNat k)) := by
  unfold Midfall.Generator.intRange
  rw [if_neg (by omega)]
  rw [← List.map_reverse, Midfall.LoweringV3.PcsRows.range_map_reverse]
  rw [show (0 : Int) - mn = -mn by ring]
  apply List.map_eq_map_iff.mpr
  intro i hi
  have hi' : i < (-mn).toNat := List.mem_range.mp hi
  have hn : ((-mn).toNat : Int) = -mn := by
    rw [Int.toNat_of_nonneg (by omega)]
  simp only [Int.ofNat_eq_natCast]
  omega

theorem range_map_one_take (K k : Nat) (hk : k < K) :
    ((List.range K).map (fun i => (1 : Int) + Int.ofNat i)).take (k + 1) =
      (List.range (k + 1)).map (fun i => (1 : Int) + Int.ofNat i) := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left (Nat.succ_le_of_lt hk)]

theorem range_map_neg_take (K k : Nat) (hk : k < K) :
    ((List.range K).map (fun i => -((1 : Int) + Int.ofNat i))).take (k + 1) =
      (List.range (k + 1)).map (fun i => -((1 : Int) + Int.ofNat i)) := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left (Nat.succ_le_of_lt hk)]

/-! ### Block 1: the head (four lets + the rot-0 store) -/

/-- Terminate a four-binding env with the four constant reads. -/
theorem b1_env4_mem (V : VEnv (Bridge.Dialect c g)) (xv om oi : U256) :
    VEnv.get (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
      ("x", xv) :: V) "x_pow_of_omega" = some xv :=
  venv_get_cons_self (D := Bridge.Dialect c g) _ "x_pow_of_omega" xv

theorem b1_env4_omega (V : VEnv (Bridge.Dialect c g)) (xv om oi : U256) :
    VEnv.get (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
      ("x", xv) :: V) "omega" = some om := by
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega") (y := "omega")
    (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega_inv") (y := "omega")
    (by decide)]
  exact venv_get_cons_self (D := Bridge.Dialect c g) _ "omega" om

theorem b1_env4_omega_inv (V : VEnv (Bridge.Dialect c g)) (xv om oi : U256) :
    VEnv.get (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
      ("x", xv) :: V) "omega_inv" = some oi := by
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega") (y := "omega_inv")
    (by decide)]
  exact venv_get_cons_self (D := Bridge.Dialect c g) _ "omega_inv" oi

theorem b1_env4_r (V : VEnv (Bridge.Dialect c g)) (xv om oi rv : U256)
    (hrv : VEnv.get V "r" = some rv) :
    VEnv.get (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
      ("x", xv) :: V) "r" = some rv := by
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega") (y := "r")
    (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega_inv") (y := "r")
    (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega") (y := "r")
    (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "r")
    (by decide)]
  exact hrv

theorem b1_env4_rot (V : VEnv (Bridge.Dialect c g)) (xv om oi : U256) (R : Nat)
    (hRP : VEnv.get V "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R)) :
    VEnv.get (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
      ("x", xv) :: V) "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) := by
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
    (y := "ROT_POINTS_MPTR") (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega_inv")
    (y := "ROT_POINTS_MPTR") (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega")
    (y := "ROT_POINTS_MPTR") (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x")
    (y := "ROT_POINTS_MPTR") (by decide)]
  exact hRP

theorem b1_lets_contract {funs : FunEnv (Bridge.Dialect c g)} (xp op oip : U256)
    (xv om oi : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [GenAst.ylet "x" (GenAst.yop EVM.Op.mload [GenAst.yvar "X_MPTR"]),
       GenAst.ylet "omega" (GenAst.yop EVM.Op.mload [GenAst.yvar "OMEGA_MPTR"]),
       GenAst.ylet "omega_inv" (GenAst.yop EVM.Op.mload [GenAst.yvar "OMEGA_INV_MPTR"]),
       GenAst.ylet "x_pow_of_omega" (GenAst.yvar "x")]
      (fun V st => VEnv.get V "X_MPTR" = some xp ∧
        VEnv.get V "OMEGA_MPTR" = some op ∧ VEnv.get V "OMEGA_INV_MPTR" = some oip ∧
        loadWord st.memory xp.toNat = xv ∧ loadWord st.memory op.toNat = om ∧
        loadWord st.memory oip.toNat = oi)
      (fun V st V' st' o => o = .normal ∧
        V' = ("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) :: ("x", xv) :: V ∧
        st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hX, hO, hOI, hx, ho, hoi⟩ := hpre
  obtain ⟨V1, st1, h1, h2⟩ | ⟨h1, _⟩ :=
    Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun
  · obtain ⟨_, p1, hp1, hV1, hst1⟩ :=
      b1_exec_ylet_mload_var (x := "x") (p := "X_MPTR") h1
    rw [hX] at hp1
    have hp1' : p1 = xp := (Option.some.inj hp1).symm
    rw [hp1'] at hV1
    obtain ⟨V2, st2, h2a, h2b⟩ | ⟨h2a, _⟩ :=
      Step.stmts_cons_inv (D := Bridge.Dialect c g) h2
    · obtain ⟨_, p2, hp2, hV2, hst2⟩ :=
        b1_exec_ylet_mload_var (x := "omega") (p := "OMEGA_MPTR") h2a
      rw [hV1] at hp2
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "OMEGA_MPTR")
        (by decide)] at hp2
      rw [hO] at hp2
      have hp2' : p2 = op := (Option.some.inj hp2).symm
      rw [hp2'] at hV2
      have hv2 : loadWord st1.memory op.toNat = om := by rw [hst1]; exact ho
      obtain ⟨V3, st3, h3a, h3b⟩ | ⟨h3a, _⟩ :=
        Step.stmts_cons_inv (D := Bridge.Dialect c g) h2b
      · obtain ⟨_, p3, hp3, hV3, hst3⟩ :=
          b1_exec_ylet_mload_var (x := "omega_inv") (p := "OMEGA_INV_MPTR") h3a
        rw [hV2] at hp3
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega")
          (y := "OMEGA_INV_MPTR") (by decide)] at hp3
        rw [hV1] at hp3
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x")
          (y := "OMEGA_INV_MPTR") (by decide)] at hp3
        rw [hOI] at hp3
        have hp3' : p3 = oip := (Option.some.inj hp3).symm
        rw [hp3'] at hV3
        have hv3 : loadWord st2.memory oip.toNat = oi := by rw [hst2, hst1]; exact hoi
        obtain ⟨V4, st4, h4a, h4b⟩ | ⟨h4a, _⟩ :=
          Step.stmts_cons_inv (D := Bridge.Dialect c g) h3b
        · obtain ⟨_, yv, hyv, hV4, hst4⟩ := b1_exec_ylet_var h4a
          rw [hV3] at hyv
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega_inv") (y := "x")
            (by decide)] at hyv
          rw [hV2] at hyv
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega") (y := "x")
            (by decide)] at hyv
          rw [hV1] at hyv
          rw [hx] at hyv
          rw [venv_get_cons_self (D := Bridge.Dialect c g)] at hyv
          have hyv' : yv = xv := (Option.some.inj hyv).symm
          rw [hyv'] at hV4
          cases h4b
          -- exact env, state
          have hV_eq : V' = ("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
              ("x", xv) :: V := by
            rw [hV4, hV3, hV2, hV1, hx, hv2, hv3]
          have hmem : st'.memory = st.memory := by
            rw [hst4, hst3, hst2, hst1]
            rfl
          have henv : st'.env = st.env := by
            rw [hst4, hst3, hst2, hst1]
            rfl
          have hhalt : st'.halted = st.halted := by
            rw [hst4, hst3, hst2, hst1]
            rfl
          exact ⟨rfl, hV_eq, hmem, henv, hhalt⟩
        · obtain ⟨ho, _, _, _⟩ := b1_exec_ylet_var h4a
          exact absurd ho ‹_›
      · obtain ⟨ho, _, _, _⟩ := b1_exec_ylet_mload_var (x := "omega_inv") (p := "OMEGA_INV_MPTR") h3a
        exact absurd ho ‹_›
    · obtain ⟨ho, _, _, _⟩ := b1_exec_ylet_mload_var (x := "omega") (p := "OMEGA_MPTR") h2a
      exact absurd ho ‹_›
  · obtain ⟨ho, _, _, _⟩ := b1_exec_ylet_mload_var (x := "x") (p := "X_MPTR") h1
    exact absurd ho ‹_›

theorem b1_store_only {funs : FunEnv (Bridge.Dialect c g)} (rots : List Int) (rot : Int)
    (v xv : U256) (mem0 : Nat → UInt8) (R : Nat)
    (hR : R < 2 ^ 256) (hb : R + rots.length * 32 ≤ 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (b1Store rots rot).toList
      (fun V st => VEnv.get V "x_pow_of_omega" = some v ∧
        VEnv.get V "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st.memory a = mem0 a))
      (fun V st V' st' o => o = .normal ∧ V' = V ∧
        (∀ idx, rots.findIdx? (fun r => r == rot) = some idx →
            loadWord st'.memory (R + idx * 32) = v) ∧
        (∀ idx, rots.findIdx? (fun r => r == rot) ≠ some idx →
            loadWord st'.memory (R + idx * 32) = loadWord st.memory (R + idx * 32)) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st'.memory a = mem0 a) ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hv, hRP, hout⟩ := hpre
  cases hf : rots.findIdx? (fun r => r == rot) with
  | none =>
      rw [show (b1Store rots rot).toList = [] by simp [b1Store, hf]] at hrun
      cases hrun
      refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
      · intro idx hidx; cases hidx
      · intro idx _; rfl
      · exact hout
  | some idx =>
      rw [show (b1Store rots rot).toList =
          [GenAst.yexpr (GenAst.yop EVM.Op.mstore
            [GenAst.yop EVM.Op.add [GenAst.yvar "ROT_POINTS_MPTR",
               GenAst.ylit (idx * Midfall.Generator.wordBytes)],
             GenAst.yvar "x_pow_of_omega"])] by simp [b1Store, hf]] at hrun
      obtain ⟨ho, hV, pv, vv, hpv, hvv, hmem, henv, hhalt⟩ :=
        b1_exec_mstore_add_var (b1_stmt_of_singleton hrun)
      rw [hRP] at hpv
      have hpv' : pv = BitVec.ofNat 256 R := (Option.some.inj hpv).symm
      rw [hpv'] at hmem
      have hvv' : vv = v := Option.some.inj (hvv.symm.trans hv)
      rw [hvv'] at hmem
      have hidx' : idx < rots.length := by
        have := findIdx?_some_lt hf
        simpa using this
      have hidx32 : idx * 32 < 2 ^ 256 :=
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_right hidx' (by norm_num)) (Nat.le_add_left _ _)) hb
      have hsum : R + idx * 32 < 2 ^ 256 :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left
          (Nat.mul_lt_mul_of_pos_right hidx' (by norm_num)) R) hb
      have haddr : ((BitVec.ofNat 256 R) + BitVec.ofNat 256 (idx * 32)).toNat
          = R + idx * 32 := b1_addr_toNat hR hidx32 hsum
      rw [show Midfall.Generator.wordBytes = 32 from rfl] at hmem
      rw [haddr] at hmem
      refine ⟨ho, hV, ?_, ?_, ?_, by rw [henv], by rw [hhalt]⟩
      · intro idx' hidx''
        have hidx_eq : idx = idx' := Option.some.inj hidx''
        subst hidx_eq
        rw [hmem, Midfall.Yul.Word.loadWord_storeWord_same]
      · intro idx' hidx''
        have hne' : idx' ≠ idx := by
          intro heq
          exact hidx'' (by rw [heq])
        rw [hmem]
        exact Midfall.Yul.Word.loadWord_storeWord_disjoint st.memory (R + idx * 32)
          (R + idx' * 32) v (b1_addr_disjoint hne')
      · intro a ha
        rw [hmem]
        unfold storeWord
        rw [if_neg]
        · exact hout a ha
        · rintro ⟨h1', h2'⟩
          rcases ha with h | h
          · omega
          · have : idx * 32 + 32 ≤ rots.length * 32 := by nlinarith
            omega

/-- Block 1's head: the three memory reads, `x_pow_of_omega := x`, then the rot-0 store. -/
def b1Head (rots : List Int) : Block EVM.Op :=
  [GenAst.ylet "x" (GenAst.yop EVM.Op.mload [GenAst.yvar "X_MPTR"]),
   GenAst.ylet "omega" (GenAst.yop EVM.Op.mload [GenAst.yvar "OMEGA_MPTR"]),
   GenAst.ylet "omega_inv" (GenAst.yop EVM.Op.mload [GenAst.yvar "OMEGA_INV_MPTR"]),
   GenAst.ylet "x_pow_of_omega" (GenAst.yvar "x")] ++ (b1Store rots 0).toList

theorem b1_head_contract {funs : FunEnv (Bridge.Dialect c g)} (rots : List Int)
    (xp op oip : U256) (xv om oi rv : U256) (mem0 : Nat → UInt8) (R : Nat)
    (hR : R < 2 ^ 256) (hb : R + rots.length * 32 ≤ 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (b1Head rots)
      (fun V st => VEnv.get V "X_MPTR" = some xp ∧
        VEnv.get V "OMEGA_MPTR" = some op ∧ VEnv.get V "OMEGA_INV_MPTR" = some oip ∧
        VEnv.get V "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) ∧
        VEnv.get V "r" = some rv ∧
        loadWord st.memory xp.toNat = xv ∧ loadWord st.memory op.toNat = om ∧
        loadWord st.memory oip.toNat = oi ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st.memory a = mem0 a))
      (fun V st V' st' o => o = .normal ∧
        V' = ("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) :: ("x", xv) :: V ∧
        (∀ idx, rots.findIdx? (fun r => r == 0) = some idx →
            loadWord st'.memory (R + idx * 32) = xv) ∧
        (∀ idx, rots.findIdx? (fun r => r == 0) ≠ some idx →
            loadWord st'.memory (R + idx * 32) = loadWord st.memory (R + idx * 32)) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st'.memory a = mem0 a) ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩ := hpre
  rw [b1Head] at hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
    ⟨Vh, sth, hlets, hstore⟩ | ⟨hlets, hne⟩
  · obtain ⟨ho1, hV1, hmem1, henv1, hhalt1⟩ :=
      b1_lets_contract (c := c) (g := g) (funs := funs) xp op oip xv om oi
        V st ⟨hX, hO, hOI, hx, ho, hoi⟩ Vh sth .normal hlets
    rw [hV1] at hstore
    have hout1 : ∀ a, a < R ∨ R + rots.length * 32 ≤ a → sth.memory a = mem0 a := by
      intro a ha
      rw [hmem1]
      exact hout a ha
    obtain ⟨ho2, hV2, hread, hunw, hout2, henv2, hhalt2⟩ :=
      b1_store_only (c := c) (g := g) (funs := funs) rots 0 xv xv mem0 R hR hb
        (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) :: ("x", xv) :: V)
        sth ⟨b1_env4_mem V xv om oi, b1_env4_rot V xv om oi R hRP, hout1⟩
        V' st' o hstore
    have hunw' : ∀ (idx : Nat), rots.findIdx? (fun r => r == 0) ≠ some idx →
        loadWord st'.memory (R + idx * 32) = loadWord st.memory (R + idx * 32) := by
      intro idx h
      rw [← hmem1]
      exact hunw idx h
    refine ⟨ho2, hV2, hread, hunw', hout2, ?_, ?_⟩
    · rw [henv2, henv1]
    · rw [hhalt2, hhalt1]
  · obtain ⟨ho, _, _, _, _⟩ :=
      b1_lets_contract (c := c) (g := g) (funs := funs) xp op oip xv om oi
        V st ⟨hX, hO, hOI, hx, ho, hoi⟩ V' st' o hlets
    exact absurd ho hne
/-! ## 10. Blocks 3-5 groundwork: generator words (`valueExpr`/`wordExpr`) evaluated

  Every q_eval_set / f_eval / MSM statement reads generator `Word`s (`wordExpr`): a pointer
  expression (literal, `name`, `name+off`, or `name-off`) read with `mload` or `calldataload`.
  The four theorems below are the total evaluation bridge: `b3val`/`b3word` name the value in
  terms of the env/state, and the inversions recover it from any `EvalExpr`/`ExecStmt` derivation,
  together with the fact that a read leaves memory, env and the halt record untouched and cannot
  halt. These are the base cases for block 3's seeds/folds and for blocks 4 and 5, whose
  operands are all `wordExpr`/`x1Pow` reads. No row, bundle or `ValidV3` gains a hypothesis.
-/

/-- The value of a generator pointer expression (the AST twin of `printValue`). -/
def b3val (V : VEnv (Bridge.Dialect c g)) (v : Midfall.Generator.Value) : Option U256 :=
  match v with
  | .integer i =>
      if 0 ≤ i then some (BitVec.ofNat 256 i.toNat)
      else some (-(BitVec.ofNat 256 i.natAbs))
  | .identifier name 0 => VEnv.get V name
  | .identifier name off =>
      if 0 < off then (VEnv.get V name).map (fun x => x + BitVec.ofNat 256 off.toNat)
      else (VEnv.get V name).map (fun x => x - BitVec.ofNat 256 off.natAbs)

/-- The word a generator `Word` reads (memory `mload` or calldata `calldataload`). -/
def b3word (st : EvmState) (V : VEnv (Bridge.Dialect c g)) (w : Midfall.Generator.Word) :
    Option U256 :=
  match w.ptr.loc with
  | .calldata => (b3val V w.ptr.value).map (fun p => wordFrom st.env.calldata p.toNat)
  | .memory => (b3val V w.ptr.value).map (fun p => loadWord st.memory p.toNat)

theorem b3_ok_add {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin EVM.Op.add [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  have h' : stepOp EVM.Op.add [a, b] st = some r := h
  simp only [stepOp] at h'
  cases h'
  exact ⟨_, _, rfl⟩

theorem b3_ok_sub {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin EVM.Op.sub [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  have h' : stepOp EVM.Op.sub [a, b] st = some r := h
  simp only [stepOp] at h'
  cases h'
  exact ⟨_, _, rfl⟩

theorem b3_eval_two_lits_add {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {a b : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.add
        [Expr.lit (Literal.number a), Expr.lit (Literal.number b)]) (.vals [cv] st')) :
    cv = BitVec.ofNat 256 a + BitVec.ofNat 256 b ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest ha =>
      cases hrest with
      | argsCons hnil hb =>
          cases hnil with
          | argsNil =>
              obtain ⟨ha', hsta⟩ := b2_eval_lit_inv ha
              obtain ⟨hb', hstb⟩ := b2_eval_lit_inv hb
              subst hsta; subst hstb
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨by rw [ha', hb'], rfl⟩

theorem b3_eval_two_lits_sub {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {a b : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub
        [Expr.lit (Literal.number a), Expr.lit (Literal.number b)]) (.vals [cv] st')) :
    cv = BitVec.ofNat 256 a - BitVec.ofNat 256 b ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest ha =>
      cases hrest with
      | argsCons hnil hb =>
          cases hnil with
          | argsNil =>
              obtain ⟨ha', hsta⟩ := b2_eval_lit_inv ha
              obtain ⟨hb', hstb⟩ := b2_eval_lit_inv hb
              subst hsta; subst hstb
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨by rw [ha', hb'], rfl⟩

theorem b1_eval_sub_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {b : String} {off : Nat} {cv : U256}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.var b, Expr.lit (Literal.number off)]) (.vals [cv] st')) :
    ∃ bv, VEnv.get V b = some bv ∧ cv = bv - BitVec.ofNat 256 off ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hb =>
      cases hrest with
      | argsCons hnil hl =>
          cases hnil with
          | argsNil =>
              obtain ⟨hv, hst⟩ := b2_eval_lit_inv hl
              obtain ⟨hbv, hstv⟩ := b1_eval_var_inv hb
              subst hst; subst hstv
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, hbv, by rw [hv], rfl⟩

theorem b3_eval_valueExpr {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {v : Midfall.Generator.Value}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.valueExpr v) (.vals [cv] st')) :
    b3val V v = some cv ∧ st' = st := by
  cases v with
  | integer i =>
      by_cases hi : 0 ≤ i
      · simp only [GenAstPcs.valueExpr, hi, if_true] at h
        obtain ⟨hc, hst⟩ := b2_eval_lit_inv h
        subst hc; subst hst
        simp only [b3val, hi, if_true, and_self]
      · have hlt : i < 0 := by omega
        simp only [GenAstPcs.valueExpr, hi, if_false] at h
        obtain ⟨hc, hst⟩ := b3_eval_two_lits_sub h
        subst hc; subst hst
        simp only [b3val, hi, if_false]
        rw [BitVec.zero_sub]
        simp only [and_self]
  | identifier name off =>
      cases off with
      | ofNat n =>
          cases n with
          | zero =>
              simp only [GenAstPcs.valueExpr] at h
              obtain ⟨hget, hst⟩ := b1_eval_var_inv h
              change VEnv.get V name = some cv ∧ st' = st
              exact ⟨hget, hst⟩
          | succ k =>
              have hpos : (0 : Int) < Int.ofNat (k + 1) := by
                have h : ((k + 1 : Nat) : Int) = Int.ofNat (k + 1) := rfl
                rw [← h, Nat.cast_add, Nat.cast_one]
                omega
              simp only [GenAstPcs.valueExpr, if_pos hpos, GenAst.yvar, GenAst.yop,
                GenAst.ylit] at h
              obtain ⟨xv, hxv, hc, hst⟩ := b1_eval_add_var_lit_inv h
              subst hc; subst hst
              simp only [b3val, if_pos hpos]
              rw [hxv]
              simp
      | negSucc n =>
          have hneg : ¬ (Int.negSucc n > 0) := by omega
          simp only [GenAstPcs.valueExpr, if_neg hneg, GenAst.yvar, GenAst.yop,
            GenAst.ylit] at h
          obtain ⟨xv, hxv, hc, hst⟩ := b1_eval_sub_var_lit_inv h
          subst hc; subst hst
          simp only [b3val, if_neg hneg]
          rw [hxv]
          simp

theorem b3_eval_valueExpr_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {v : Midfall.Generator.Value}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.valueExpr v) (.halt st')) : False := by
  cases v with
  | integer i =>
      by_cases hi : 0 ≤ i
      · simp only [GenAstPcs.valueExpr, hi, if_true] at h
        exact Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts h
      · simp only [GenAstPcs.valueExpr, hi, if_false] at h
        exact Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.sub)
          (fun _ _ _ _ hr => b3_ok_sub hr)
          (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh)
          (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h
  | identifier name off =>
      cases off with
      | ofNat n =>
          cases n with
          | zero =>
              simp only [GenAstPcs.valueExpr] at h
              exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts h
          | succ k =>
              have hpos : (0 : Int) < Int.ofNat (k + 1) := by
                have hh : ((k + 1 : Nat) : Int) = Int.ofNat (k + 1) := rfl
                rw [← hh, Nat.cast_add, Nat.cast_one]
                omega
              simp only [GenAstPcs.valueExpr, if_pos hpos] at h
              exact Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.add)
                (fun _ _ _ _ hr => b3_ok_add hr)
                (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
                (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h
      | negSucc n =>
          have hneg : ¬ (Int.negSucc n > 0) := by
            rw [Int.negSucc_eq]; omega
          simp only [GenAstPcs.valueExpr, if_neg hneg] at h
          exact Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.sub)
            (fun _ _ _ _ hr => b3_ok_sub hr)
            (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
            (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h

theorem b3_eval_wordExpr {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {w : Midfall.Generator.Word}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.wordExpr w) (.vals [cv] st')) :
    b3word st V w = some cv ∧ st'.memory = st.memory ∧ st'.env = st.env ∧
      st'.halted = st.halted := by
  cases hl : w.ptr.loc with
  | calldata =>
      have hw : GenAstPcs.wordExpr w = GenAst.yop EVM.Op.calldataload
          [GenAstPcs.valueExpr w.ptr.value] := by
        simp [GenAstPcs.wordExpr, hl]
      rw [hw] at h
      obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
      cases hargs with
      | argsCons hnil ha =>
          cases hnil with
          | argsNil =>
              obtain ⟨hav, hsta⟩ := b3_eval_valueExpr ha
              rw [hsta] at hbi
              simp only [stepOp] at hbi
              cases hbi
              refine ⟨?_, rfl, rfl, rfl⟩
              simp only [b3word, hl, hav, Option.map_some]
  | memory =>
      have hw : GenAstPcs.wordExpr w = GenAst.yop EVM.Op.mload
          [GenAstPcs.valueExpr w.ptr.value] := by
        simp [GenAstPcs.wordExpr, hl]
      rw [hw] at h
      obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
      cases hargs with
      | argsCons hnil ha =>
          cases hnil with
          | argsNil =>
              obtain ⟨hav, hsta⟩ := b3_eval_valueExpr ha
              rw [hsta] at hbi
              simp only [stepOp] at hbi
              cases hbi
              refine ⟨?_, rfl, rfl, rfl⟩
              simp only [b3word, hl, hav, Option.map_some]

theorem b3_eval_wordExpr_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {w : Midfall.Generator.Word}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.wordExpr w) (.halt st')) : False := by
  cases hl : w.ptr.loc with
  | calldata =>
      have hw : GenAstPcs.wordExpr w = GenAst.yop EVM.Op.calldataload
          [GenAstPcs.valueExpr w.ptr.value] := by
        simp [GenAstPcs.wordExpr, hl]
      rw [hw] at h
      exact Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.calldataload)
        (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_calldataload hr)
        (fun _ _ hh => b3_eval_valueExpr_halt hh) h
  | memory =>
      have hw : GenAstPcs.wordExpr w = GenAst.yop EVM.Op.mload
          [GenAstPcs.valueExpr w.ptr.value] := by
        simp [GenAstPcs.wordExpr, hl]
      rw [hw] at h
      exact Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.mload)
        (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_mload hr)
        (fun _ _ hh => b3_eval_valueExpr_halt hh) h

theorem b3_eval_x1Pow {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} (i : Nat) {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.x1Pow i) (.vals [cv] st')) :
    ∃ pv, VEnv.get V "X1_POWERS_MPTR" = some pv ∧
      cv = loadWord st.memory (pv + BitVec.ofNat 256 (i * 32)).toNat ∧
      st' = touchMemory st (pv + BitVec.ofNat 256 (i * 32)).toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil harg =>
      cases hnil with
      | argsNil =>
          obtain ⟨pv, hpv, hcv, hst1⟩ := b1_eval_add_var_lit_inv harg
          rw [hst1] at hbi
          simp only [stepOp] at hbi
          cases hbi
          exact ⟨pv, hpv, by rw [hcv]; rfl, by rw [hcv]; rfl⟩

theorem b3_eval_x1Pow_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} (i : Nat) {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.x1Pow i) (.halt st')) : False := by
  unfold GenAstPcs.x1Pow at h
  exact Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.mload)
    (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_mload hr)
    (fun _ _ hh => b1_eval_add_var_lit_halt hh) h

/-- The seed statement of the unrolled/rolled q_eval_set arm: `let q_eval_set_k := wordExpr ev`. -/
theorem b3_exec_seed {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (k : Nat) (ev : Midfall.Generator.Word)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet ("q_eval_set_" ++ toString k) (GenAstPcs.wordExpr ev)) V' st' o) :
    o = .normal ∧ ∃ v, b3word st V ev = some v ∧
      V' = (("q_eval_set_" ++ toString k), v) :: V ∧
      st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨hv, hmem, henv, hhalt⟩ := b3_eval_wordExpr he
      exact ⟨rfl, _, hv, rfl, hmem, henv, hhalt⟩
  | letHalt he => exact (b3_eval_wordExpr_halt he).elim

/-! ### Block 3: the persist statement and ∃-form value variants -/

theorem b1_eval_var_vals {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : Ident} {av : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var x) (.vals [av] st')) :
    ∃ av', VEnv.get V x = some av' ∧ st' = st := by
  cases h with
  | var hget => exact ⟨_, hget, rfl⟩

theorem b3_eval_x1Pow_vals {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} (i : Nat) {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.x1Pow i) (.vals [cv] st')) :
    ∃ pv xv, VEnv.get V "X1_POWERS_MPTR" = some pv ∧
      xv = loadWord st.memory (pv + BitVec.ofNat 256 (i * 32)).toNat ∧
      st' = touchMemory st (pv + BitVec.ofNat 256 (i * 32)).toNat 32 := by
  obtain ⟨pv, hpv, hxv, hsth⟩ := b3_eval_x1Pow (c := c) (g := g) i h
  exact ⟨pv, _, hpv, hxv, hsth⟩

theorem b3_eval_wordExpr_vals {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {w : Midfall.Generator.Word}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (GenAstPcs.wordExpr w) (.vals [cv] st')) :
    ∃ v, b3word st V w = some v ∧ st'.memory = st.memory ∧ st'.env = st.env ∧
      st'.halted = st.halted := by
  obtain ⟨hwv, hwm, hwe, hwh⟩ := b3_eval_wordExpr (c := c) (g := g) h
  exact ⟨_, hwv, hwm, hwe, hwh⟩

/-- The persist statement of block 3: `mstore(add(Q_EVAL_SET_MPTR, (off+k)*32), q_eval_set_k)`. -/
theorem b3_exec_persist {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (k off R : Nat) (hR : R < 2 ^ 256) (hoff : (off + k) * 32 < 2 ^ 256)
    (hsum : R + (off + k) * 32 < 2 ^ 256)
    (hbase : VEnv.get V "Q_EVAL_SET_MPTR" = some (BitVec.ofNat 256 R))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAstPcs.mstoreAdd "Q_EVAL_SET_MPTR" ((off + k) * Midfall.Generator.wordBytes)
        (GenAst.yvar ("q_eval_set_" ++ toString k)))
      V' st' o) :
    o = .normal ∧ V' = V ∧ ∃ v, VEnv.get V ("q_eval_set_" ++ toString k) = some v ∧
      st'.memory = storeWord st.memory (R + (off + k) * 32) v ∧
      st'.env = st.env ∧ st'.halted = st.halted := by
  obtain ⟨ho, hV, pv, vv, hpv, hvv, hmem, henv, hhalt⟩ :=
    b1_exec_mstore_add_var (p := "Q_EVAL_SET_MPTR")
      (val := "q_eval_set_" ++ toString k) (off := (off + k) * Midfall.Generator.wordBytes) h
  refine ⟨ho, hV, vv, hvv, ?_, henv, hhalt⟩
  rw [hbase] at hpv
  have hpv' : pv = BitVec.ofNat 256 R := (Option.some.inj hpv).symm
  rw [hpv'] at hmem
  rw [show Midfall.Generator.wordBytes = 32 from rfl] at hmem
  rw [hmem, b1_addr_toNat hR hoff hsum]
#assert_axioms Midfall.LoweringV3.PcsRows.b1_eval_var_vals
  [propext, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_x1Pow_vals
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_wordExpr_vals
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_exec_persist
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_x1Pow
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_x1Pow_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_exec_seed
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_valueExpr
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_valueExpr_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_wordExpr
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b3_eval_wordExpr_halt
  [propext, Classical.choice, Quot.sound] native []


/-! ### Block 1: the walk as an iteration count, the list shapes, and the back reset -/

/-- The walk count: `k` mulmod steps. -/
def wIter (v b rv : U256) : Nat → U256
  | 0 => v
  | k + 1 => wMulmodAt (wIter v b rv k) b rv

theorem wIter_shift (v b rv : U256) : ∀ k,
    wIter (wMulmodAt v b rv) b rv k = wIter v b rv (k + 1)
  | 0 => rfl
  | k + 1 => by
      rw [show wIter (wMulmodAt v b rv) b rv (k + 1) =
        wMulmodAt (wIter (wMulmodAt v b rv) b rv k) b rv from rfl,
        wIter_shift v b rv k]
      rfl

theorem wWalk_eq (v b rv : U256) (l : List Int) : wWalk v b rv l = wIter v b rv l.length := by
  induction l generalizing v with
  | nil => rfl
  | cons a rest ih =>
      rw [show wWalk v b rv (a :: rest) = wWalk (wMulmodAt v b rv) b rv rest from rfl,
        ih (wMulmodAt v b rv), wIter_shift, List.length_cons]

theorem intRangeInclusive_one_length (m : Int) (hm : 0 ≤ m) :
    (Midfall.Generator.intRangeInclusive 1 m).length = Int.toNat m := by
  unfold Midfall.Generator.intRangeInclusive
  by_cases h : m < 1
  · rw [if_pos h]
    have : m = 0 := by omega
    subst this
    rfl
  · rw [if_neg h]
    simp only [List.length_map, List.length_range]
    congr 1
    omega

theorem intRange_rev_length (mn : Int) (hm : mn < 0) :
    (Midfall.Generator.intRange mn 0).reverse.length = Int.toNat (-mn) := by
  unfold Midfall.Generator.intRange
  rw [if_neg (by omega)]
  simp only [List.length_reverse, List.length_map, List.length_range]
  congr 1
  omega

/-- The table entry a rotation holds, as a pure iteration count. -/
def rotValI (xv om oi rv : U256) (rot : Int) : U256 :=
  wIter xv (if 0 ≤ rot then om else oi) rv rot.natAbs

theorem rotVal_eq (xv om oi rv : U256) (rot : Int) :
    rotVal xv om oi rv rot = rotValI xv om oi rv rot := by
  unfold rotVal rotValI
  by_cases h : 0 ≤ rot
  · rw [if_pos h, if_pos h, wWalk_eq, intRangeInclusive_one_length rot (by omega)]
    congr 1
    omega
  · rw [if_neg h, if_neg h, wWalk_eq, intRangeInclusive_one_length (-rot) (by omega)]
    congr 1
    omega

/-! ### The block-1 list shapes -/

def b1WalkL (rots : List Int) (l : List Int) (w : String) : Block EVM.Op :=
  l.flatMap (fun rot => [GenAstPcs.walkStep w] ++ (b1Store rots rot).toList)

def b1Fwd (rots : List Int) (maxRot : Int) : Block EVM.Op :=
  b1WalkL rots (Midfall.Generator.intRangeInclusive 1 maxRot) "omega"

def b1Back (rots : List Int) (minRot : Int) : Block EVM.Op :=
  if minRot < 0 then
    [GenAst.yset "x_pow_of_omega" (GenAst.yvar "x")] ++
      b1WalkL rots ((Midfall.Generator.intRange minRot 0).reverse) "omega_inv"
  else []

def b1All (rots : List Int) (maxRot minRot : Int) : Block EVM.Op :=
  b1Head rots ++ b1Fwd rots maxRot ++ b1Back rots minRot

/-- `pcsBlock1Ast` at `trace = false` is the three named pieces: head, forward walk, back walk
    (the trace serialiser arm is dead at the slice's flag). -/
theorem pcsBlock1Ast_eq (rots : List Int) (maxRot minRot : Int)
    (ps : List (List Int)) :
    GenAstPcs.pcsBlock1Ast rots maxRot minRot false ps = b1All rots maxRot minRot := by
  simp only [GenAstPcs.pcsBlock1Ast, b1All, b1Head, b1Fwd, b1Back, b1WalkL, b1Store,
    GenAstPcs.walkStep, GenAstPcs.mstoreAdd]
  split_ifs <;> simp_all

theorem b1_reset_contract {funs : FunEnv (Bridge.Dialect c g)} (xv : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [GenAst.yset "x_pow_of_omega" (GenAst.yvar "x")]
      (fun V _ => VEnv.get V "x" = some xv)
      (fun V st V' st' o => o = .normal ∧
        V' = VEnv.set V "x_pow_of_omega" xv ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  have h := b1_stmt_of_singleton hrun
  cases h with
  | assignVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨hav, hst⟩ := b1_eval_var_inv he
      subst hst
      have hcv : cv = xv := Option.some.inj (hav.symm.trans hpre)
      subst hcv
      exact ⟨rfl, rfl, rfl⟩
  | assignHalt he =>
      exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts he).elim

theorem natAbs_one_add (j : Nat) : ((1 : Int) + Int.ofNat j).natAbs = j + 1 := by
  rw [Int.natAbs_eq_iff]
  left
  simp only [Int.ofNat_eq_natCast]
  omega

theorem natAbs_neg_one_sub (j : Nat) : ((-1 : Int) - Int.ofNat j).natAbs = j + 1 := by
  rw [Int.natAbs_eq_iff]
  right
  simp only [Int.ofNat_eq_natCast]
  omega

theorem fwd_mem {maxRot rot : Int} (h : 0 < rot) (hle : rot ≤ maxRot) :
    rot ∈ Midfall.Generator.intRangeInclusive 1 maxRot := by
  rw [intRangeInclusive_one_eq maxRot (by omega), List.mem_map]
  refine ⟨(rot.toNat - 1), ?_, ?_⟩
  · rw [List.mem_range]
    have hr : ((rot.toNat : Nat) : Int) = rot := Int.toNat_of_nonneg (by omega)
    have hm : ((maxRot.toNat : Nat) : Int) = maxRot := Int.toNat_of_nonneg (by omega)
    omega
  · have hr : ((rot.toNat : Nat) : Int) = rot := Int.toNat_of_nonneg (by omega)
    have hge : 1 ≤ rot.toNat := by omega
    have hc : (((rot.toNat - 1 : Nat)) : Int) = (rot.toNat : Int) - 1 := by
      rw [Nat.cast_sub hge, Nat.cast_one]
    simp only [Int.ofNat_eq_natCast]
    rw [hc]
    omega

theorem fwd_pos {maxRot rot : Int} (h : rot ∈ Midfall.Generator.intRangeInclusive 1 maxRot) :
    0 < rot := by
  rw [intRangeInclusive_one_eq maxRot (by
    rcases List.mem_iff_getElem.mp h with ⟨i, hi, _⟩
    unfold Midfall.Generator.intRangeInclusive at hi
    split at hi
    · simp at hi
    · simp only [List.length_map, List.length_range] at hi
      omega), List.mem_map] at h
  obtain ⟨k, _, rfl⟩ := h
  simp only [Int.ofNat_eq_natCast]
  omega

theorem back_mem {mn rot : Int} (h : rot < 0) (hle : mn ≤ rot) :
    rot ∈ (Midfall.Generator.intRange mn 0).reverse := by
  rw [intRange_rev_eq mn (by omega), List.mem_map]
  refine ⟨((-rot).toNat - 1), ?_, ?_⟩
  · rw [List.mem_range]
    have hr : (((-rot).toNat : Nat) : Int) = -rot := Int.toNat_of_nonneg (by omega)
    have hm : (((-mn).toNat : Nat) : Int) = -mn := Int.toNat_of_nonneg (by omega)
    omega
  · have hr : (((-rot).toNat : Nat) : Int) = -rot := Int.toNat_of_nonneg (by omega)
    have hge : 1 ≤ (-rot).toNat := by omega
    have hc : ((((-rot).toNat - 1 : Nat)) : Int) = ((-rot).toNat : Int) - 1 := by
      rw [Nat.cast_sub hge, Nat.cast_one]
    simp only [Int.ofNat_eq_natCast]
    rw [hc]
    omega

theorem back_neg {mn rot : Int} (h : rot ∈ (Midfall.Generator.intRange mn 0).reverse) :
    rot < 0 := by
  unfold Midfall.Generator.intRange at h
  split at h
  · simp at h
  · rw [List.mem_reverse, List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    rw [List.mem_range] at hk
    simp only [Int.ofNat_eq_natCast]
    omega

theorem b1_env4_x (V : VEnv (Bridge.Dialect c g)) (xv om oi : U256) :
    VEnv.get (("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
      ("x", xv) :: V) "x" = some xv := by
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega") (y := "x") (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega_inv") (y := "x") (by decide)]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "omega") (y := "x") (by decide)]
  exact venv_get_cons_self (D := Bridge.Dialect c g) _ "x" xv

theorem b1_restore4 (V : VEnv (Bridge.Dialect c g)) (xv om oi a b cc : U256) :
    restore V (VEnv.set (VEnv.set (("x_pow_of_omega", a) :: ("omega_inv", oi) ::
      ("omega", om) :: ("x", xv) :: V) "x_pow_of_omega" b) "x_pow_of_omega" cc) = V := by
  rw [venv_set_cons_same (D := Bridge.Dialect c g)]
  rw [venv_set_cons_same (D := Bridge.Dialect c g)]
  simp only [restore, venv_set_length, List.length_cons]
  rw [show List.length V + 1 + 1 + 1 + 1 - List.length V = 4 by omega]
  rfl

theorem b1_restore4_one (V : VEnv (Bridge.Dialect c g)) (xv om oi a : U256) :
    restore V (VEnv.set (("x_pow_of_omega", a) :: ("omega_inv", oi) ::
      ("omega", om) :: ("x", xv) :: V) "x_pow_of_omega" a) = V := by
  rw [venv_set_cons_same (D := Bridge.Dialect c g)]
  simp only [restore, venv_set_length, List.length_cons]
  rw [show List.length V + 1 + 1 + 1 + 1 - List.length V = 4 by omega]
  rfl

/-! ## 11. ROW.PCS.1: block 1's table spec (PROVED)

  The block-level contract over the whole emitted block 1. `b1BlockPre` names the pre-state
  (the three header reads, the rotation table pointer, `r`, and the three loaded words), and the
  post says: every run is normal, the block exits with its env restored, the env/halted records
  are unchanged, the table holds `rotVal` at every distinct-rotation slot, and nothing outside the
  table window moved.

  The body contract (`pcs_b1_body`) is proved over `b1All = head ++ fwd ++ back`: the head writes
  the rot-0 entry, the forward walk writes `1..maxRot`, the back walk (after the reset) writes
  `-1..minRot`; the three-way split for an index `i < rots.length` uses the head readback plus the
  two walks' unwritten clauses for `rot = 0`, `fwd_mem`/`back_mem` and the prefix length lemmas
  for the other two cases. `pcs_b1_sem` wraps it through `StmtContractAll.block` and the
  `pcsBlock1Ast_eq` shape. -/

/-- The block-1 precondition, named (the theorem states it twice). -/
def b1BlockPre (xp op oip xv om oi rv : U256) (mem0 : Nat → UInt8) (R : Nat) (rots : List Int)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  VEnv.get V "X_MPTR" = some xp ∧ VEnv.get V "OMEGA_MPTR" = some op ∧
    VEnv.get V "OMEGA_INV_MPTR" = some oip ∧
    VEnv.get V "ROT_POINTS_MPTR" = some (BitVec.ofNat 256 R) ∧
    VEnv.get V "r" = some rv ∧
    loadWord st.memory xp.toNat = xv ∧ loadWord st.memory op.toNat = om ∧
    loadWord st.memory oip.toNat = oi ∧
    (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st.memory a = mem0 a)

theorem nodup_intRangeInclusive_one (m : Int) :
    (Midfall.Generator.intRangeInclusive 1 m).Nodup := by
  unfold Midfall.Generator.intRangeInclusive
  split
  · simp
  · exact List.Nodup.map (fun a b h => by
      simp only [Int.ofNat_eq_natCast] at h
      omega) List.nodup_range

theorem nodup_intRange_rev (mn : Int) :
    ((Midfall.Generator.intRange mn 0).reverse).Nodup := by
  unfold Midfall.Generator.intRange
  split
  · simp
  · rw [← List.map_reverse]
    exact List.Nodup.map (fun a b h => by
      simp only [Int.ofNat_eq_natCast] at h
      omega) (List.nodup_reverse.mpr List.nodup_range)

theorem pcs_b1_body {funs : FunEnv (Bridge.Dialect c g)} (rots : List Int)
    (maxRot minRot : Int) (xp op oip xv om oi rv : U256) (mem0 : Nat → UInt8) (R : Nat)
    (hnd : rots.Nodup) (hR : R < 2 ^ 256) (hb : R + rots.length * 32 ≤ 2 ^ 256)
    (hmax : ∀ r ∈ rots, 0 ≤ r → r ≤ maxRot)
    (hmin : ∀ r ∈ rots, r < 0 → minRot ≤ r) :
    StmtsContractAll (D := Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g) (b1All rots maxRot minRot) :: funs)
      (b1All rots maxRot minRot)
      (b1BlockPre xp op oip xv om oi rv mem0 R rots)
      (fun V st Vb stb o => o = .normal ∧ restore V Vb = V ∧ stb.env = st.env ∧
        stb.halted = st.halted ∧
        (∀ (i : Nat) (hi : i < rots.length),
          loadWord stb.memory (R + i * 32) = rotVal xv om oi rv (rots[i]'hi)) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → stb.memory a = mem0 a)) := by
  intro V st hpre Vb stb o hbody
  obtain ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩ := hpre
  set fns : FunEnv (Bridge.Dialect c g) :=
    hoist (Bridge.Dialect c g) (b1All rots maxRot minRot) :: funs with hfns
  rcases Step.stmts_append_inv hbody with ⟨Vhf, shf, hHF, hBackRun⟩ | ⟨hHF, hne⟩
  · rcases Step.stmts_append_inv hHF with ⟨Vh, sh, hHead, hFwd⟩ | ⟨hHead, hne1⟩
    · -- head
      obtain ⟨hoH, hVH, hreadH, hunwH, houtH, henvH, hhaltH⟩ :=
        b1_head_contract (c := c) (g := g) (funs := fns) rots xp op oip xv om oi rv mem0 R
          hR hb V st ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩
          Vh sh .normal hHead
      -- fwd
      have hpreF : b1Pre rots "omega" xv om rv mem0 R Vh sh := by
        rw [hVH]
        exact ⟨b1_env4_mem V xv om oi, b1_env4_omega V xv om oi,
          b1_env4_r V xv om oi rv hrv, b1_env4_rot V xv om oi R hRP, houtH⟩
      unfold b1Fwd b1WalkL at hFwd
      obtain ⟨hoF, hVF, hreadF, hunwF, houtF, henvF, hhaltF⟩ :=
        b1_walk_contract (c := c) (g := g) (funs := fns) rots
          (Midfall.Generator.intRangeInclusive 1 maxRot) "omega" xv om rv mem0 R
          (by decide) hnd hR hb
          (fun rot _ idx hf => by
            have := findIdx?_some_lt hf
            simpa using this)
          (nodup_intRangeInclusive_one maxRot)
          Vh sh hpreF Vhf shf .normal hFwd
      by_cases hmn : minRot < 0
      · -- back = reset ++ walk
        have hbackShape : b1Back rots minRot =
            [GenAst.yset "x_pow_of_omega" (GenAst.yvar "x")] ++
              b1WalkL rots ((Midfall.Generator.intRange minRot 0).reverse) "omega_inv" := by
          rw [b1Back, if_pos hmn]
        rw [hbackShape] at hBackRun
        rcases Step.stmts_append_inv hBackRun with ⟨Vr, sr, hReset, hWalk⟩ | ⟨hReset, hne2⟩
        · have hpreR : VEnv.get Vhf "x" = some xv := by
            rw [hVF, hVH]
            exact b1_env4_x V xv om oi
          obtain ⟨hoR, hVR, hsr⟩ :=
            b1_reset_contract (c := c) (g := g) (funs := fns) xv
              Vhf shf hpreR Vr sr .normal hReset
          have hpreB : b1Pre rots "omega_inv" xv oi rv mem0 R Vr sr := by
            rw [hVR, hsr, hVF, hVH]
            refine ⟨?_, ?_, ?_, ?_, houtF⟩
            · exact venv_get_set_same (D := Bridge.Dialect c g)
                (venv_get_set_same (D := Bridge.Dialect c g) (b1_env4_mem V xv om oi))
            · rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
                (y := "omega_inv") (by decide)]
              rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
                (y := "omega_inv") (by decide)]
              exact b1_env4_omega_inv V xv om oi
            · rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
                (y := "r") (by decide)]
              rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
                (y := "r") (by decide)]
              exact b1_env4_r V xv om oi rv hrv
            · rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
                (y := "ROT_POINTS_MPTR") (by decide)]
              rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_pow_of_omega")
                (y := "ROT_POINTS_MPTR") (by decide)]
              exact b1_env4_rot V xv om oi R hRP
          unfold b1WalkL at hWalk
          obtain ⟨hoB, hVB, hreadB, hunwB, houtB, henvB, hhaltB⟩ :=
            b1_walk_contract (c := c) (g := g) (funs := fns) rots
              ((Midfall.Generator.intRange minRot 0).reverse) "omega_inv" xv oi rv mem0 R
              (by decide) hnd hR hb
              (fun rot _ idx hf => by
                have := findIdx?_some_lt hf
                simpa using this)
              (nodup_intRange_rev minRot)
              Vr sr hpreB Vb stb o hWalk
          refine ⟨hoB, ?_, ?_, ?_, ?_, houtB⟩
          · rw [hVB, hVR, hVF, hVH]
            exact b1_restore4 V xv om oi
              (wWalk xv om rv (Midfall.Generator.intRangeInclusive 1 maxRot)) xv
              (wWalk xv oi rv ((Midfall.Generator.intRange minRot 0).reverse))
          · rw [henvB, hsr, henvF, henvH]
          · rw [hhaltB, hsr, hhaltF, hhaltH]
          · intro i hi
            set rot := rots[i]'hi with hrot
            have hmem : rot ∈ rots := List.getElem_mem hi
            have hidx : rots.findIdx? (fun r => r == rot) = some i := findIdx?_beq_getElem hnd hi
            by_cases hzero : rot = 0
            · have hidx0 : rots.findIdx? (fun r => r == 0) = some i := by
                rw [← hzero]; exact hidx
              have hnf : ∀ (j : Nat)
                  (hj : j < (Midfall.Generator.intRangeInclusive 1 maxRot).length),
                  rots.findIdx? (fun r => r ==
                    (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj) ≠ some i := by
                intro j hj hfj
                have hrotj : (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj = rot :=
                  (findIdx?_beq_inj (l := rots) (a := rot)
                    (b := (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj)
                    (ia := i) (ib := i) hidx hfj rfl).symm
                have hpos := fwd_pos (List.getElem_mem hj)
                rw [hzero] at hrotj
                omega
              have hnb : ∀ (j : Nat)
                  (hj : j < ((Midfall.Generator.intRange minRot 0).reverse).length),
                  rots.findIdx? (fun r => r ==
                    ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj) ≠ some i := by
                intro j hj hfj
                have hrotj : ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj = rot :=
                  (findIdx?_beq_inj (l := rots) (a := rot)
                    (b := ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj)
                    (ia := i) (ib := i) hidx hfj rfl).symm
                have hneg := back_neg (List.getElem_mem hj)
                rw [hzero] at hrotj
                omega
              have e1 : loadWord stb.memory (R + i * 32) = loadWord sh.memory (R + i * 32) := by
                rw [hunwB i hnb, hsr, hunwF i hnf]
              rw [e1, hreadH i hidx0, hzero, rotVal_eq, rotValI]
              rw [if_pos (by norm_num : (0 : Int) ≤ 0)]
              rfl
            · by_cases hpos : 0 < rot
              · have hle : rot ≤ maxRot := hmax rot hmem (by omega)
                obtain ⟨j, hj, hget⟩ :=
                  List.mem_iff_getElem.mp (fwd_mem (maxRot := maxRot) hpos hle)
                have hidx' : rots.findIdx? (fun r => r ==
                    (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj) = some i := by
                  rw [hget]; exact hidx
                have hnb : ∀ (j : Nat)
                    (hj : j < ((Midfall.Generator.intRange minRot 0).reverse).length),
                    rots.findIdx? (fun r => r ==
                      ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj) ≠ some i := by
                  intro j hj hfj
                  have hrotj : ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj = rot :=
                    (findIdx?_beq_inj (l := rots) (a := rot)
                      (b := ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj)
                      (ia := i) (ib := i) hidx hfj rfl).symm
                  have hneg := back_neg (List.getElem_mem hj)
                  omega
                have e1 : loadWord stb.memory (R + i * 32) = loadWord shf.memory (R + i * 32) := by
                  rw [hunwB i hnb, hsr]
                rw [e1, hreadF j hj i hidx', wWalk_eq]
                have hlen : ((Midfall.Generator.intRangeInclusive 1 maxRot).take (j + 1)).length
                    = j + 1 := by
                  rw [List.length_take]
                  omega
                rw [hlen, rotVal_eq, rotValI, if_pos (le_of_lt hpos)]
                have hgetI : rot = 1 + (j : Int) := by
                  have hm1 : 1 ≤ maxRot := by omega
                  simpa [intRangeInclusive_one_eq maxRot hm1, List.getElem_map,
                    List.getElem_range] using hget.symm
                have hnat : ((1 : Int) + (j : Int)).natAbs = j + 1 := by
                  rw [Int.natAbs_eq_iff]; left; omega
                rw [hgetI, hnat]
              · have hneg : rot < 0 := by omega
                have hle : minRot ≤ rot := hmin rot hmem hneg
                obtain ⟨j, hj, hget⟩ :=
                  List.mem_iff_getElem.mp (back_mem (mn := minRot) hneg hle)
                have hidx' : rots.findIdx? (fun r => r ==
                    ((Midfall.Generator.intRange minRot 0).reverse)[j]'hj) = some i := by
                  rw [hget]; exact hidx
                rw [hreadB j hj i hidx', wWalk_eq]
                have hlen : (((Midfall.Generator.intRange minRot 0).reverse).take (j + 1)).length
                    = j + 1 := by
                  rw [List.length_take]
                  omega
                rw [hlen, rotVal_eq, rotValI, if_neg (by omega)]
                have hgetI : rot = -1 - (j : Int) := by
                  have h := hget.symm
                  simp only [intRange_rev_eq minRot hmn, List.getElem_map,
                    List.getElem_range] at h
                  rw [h]
                  simp only [Int.ofNat_eq_natCast]
                  ring
                have hnat : ((-1 : Int) - (j : Int)).natAbs = j + 1 := by
                  rw [Int.natAbs_eq_iff]; right; omega
                rw [hgetI, hnat]
        · obtain ⟨ho, _, _⟩ :=
            b1_reset_contract (c := c) (g := g) (funs := fns) xv Vhf shf
              (by rw [hVF, hVH]; exact b1_env4_x V xv om oi) Vb stb o hReset
          exact absurd ho hne2
      · -- no back
        have hbackNil : b1Back rots minRot = [] := by
          rw [b1Back, if_neg hmn]
        rw [hbackNil] at hBackRun
        cases hBackRun
        refine ⟨rfl, ?_, ?_, ?_, ?_, houtF⟩
        · rw [hVF, hVH]
          exact b1_restore4_one V xv om oi
            (wWalk xv om rv (Midfall.Generator.intRangeInclusive 1 maxRot))
        · rw [henvF, henvH]
        · rw [hhaltF, hhaltH]
        · intro i hi
          set rot := rots[i]'hi with hrot
          have hmem : rot ∈ rots := List.getElem_mem hi
          have hidx : rots.findIdx? (fun r => r == rot) = some i := findIdx?_beq_getElem hnd hi
          by_cases hzero : rot = 0
          · have hidx0 : rots.findIdx? (fun r => r == 0) = some i := by
              rw [← hzero]; exact hidx
            have hnf : ∀ (j : Nat)
                (hj : j < (Midfall.Generator.intRangeInclusive 1 maxRot).length),
                rots.findIdx? (fun r => r ==
                  (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj) ≠ some i := by
              intro j hj hfj
              have hrotj : (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj = rot :=
                (findIdx?_beq_inj (l := rots) (a := rot)
                  (b := (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj)
                  (ia := i) (ib := i) hidx hfj rfl).symm
              have hpos := fwd_pos (List.getElem_mem hj)
              rw [hzero] at hrotj
              omega
            have e1 : loadWord stb.memory (R + i * 32) = loadWord sh.memory (R + i * 32) :=
              hunwF i hnf
            rw [e1, hreadH i hidx0, hzero, rotVal_eq, rotValI]
            rw [if_pos (by norm_num : (0 : Int) ≤ 0)]
            rfl
          · have hpos : 0 < rot := by
              by_contra hle0
              have := hmin rot hmem (by omega)
              omega
            have hle : rot ≤ maxRot := hmax rot hmem (by omega)
            obtain ⟨j, hj, hget⟩ :=
              List.mem_iff_getElem.mp (fwd_mem (maxRot := maxRot) hpos hle)
            have hidx' : rots.findIdx? (fun r => r ==
                (Midfall.Generator.intRangeInclusive 1 maxRot)[j]'hj) = some i := by
              rw [hget]; exact hidx
            rw [hreadF j hj i hidx', wWalk_eq]
            have hlen : ((Midfall.Generator.intRangeInclusive 1 maxRot).take (j + 1)).length
                = j + 1 := by
              rw [List.length_take]
              omega
            rw [hlen, rotVal_eq, rotValI, if_pos (le_of_lt hpos)]
            have hgetI : rot = 1 + (j : Int) := by
              have hm1 : 1 ≤ maxRot := by omega
              simpa [intRangeInclusive_one_eq maxRot hm1, List.getElem_map,
                List.getElem_range] using hget.symm
            have hnat : ((1 : Int) + (j : Int)).natAbs = j + 1 := by
              rw [Int.natAbs_eq_iff]; left; omega
            rw [hgetI, hnat]
    · exact absurd rfl hne1
  · rcases Step.stmts_append_inv hHF with ⟨Vh, sh, hHead, hFwd⟩ | ⟨hHead, hne1⟩
    · obtain ⟨_, _, _, _, _, _, _⟩ :=
        b1_head_contract (c := c) (g := g) (funs := fns) rots xp op oip xv om oi rv mem0 R
          hR hb V st ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩
          Vh sh .normal hHead
      have hpreF : b1Pre rots "omega" xv om rv mem0 R Vh sh := by
        rw [show Vh = ("x_pow_of_omega", xv) :: ("omega_inv", oi) :: ("omega", om) ::
            ("x", xv) :: V from by assumption]
        exact ⟨b1_env4_mem V xv om oi, b1_env4_omega V xv om oi,
          b1_env4_r V xv om oi rv hrv, b1_env4_rot V xv om oi R hRP,
          by assumption⟩
      unfold b1Fwd b1WalkL at hFwd
      obtain ⟨hoF, _, _, _, _, _, _⟩ :=
        b1_walk_contract (c := c) (g := g) (funs := fns) rots
          (Midfall.Generator.intRangeInclusive 1 maxRot) "omega" xv om rv mem0 R
          (by decide) hnd hR hb
          (fun rot _ idx hf => by
            have := findIdx?_some_lt hf
            simpa using this)
          (nodup_intRangeInclusive_one maxRot)
          Vh sh hpreF Vb stb o hFwd
      exact absurd hoF hne
    · obtain ⟨ho, _, _, _, _, _, _⟩ :=
        b1_head_contract (c := c) (g := g) (funs := fns) rots xp op oip xv om oi rv mem0 R
          hR hb V st ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩
          Vb stb o hHead
      exact absurd ho hne1

theorem pcs_b1_sem {funs : FunEnv (Bridge.Dialect c g)} (rots : List Int)
    (maxRot minRot : Int) (xp op oip xv om oi rv : U256) (mem0 : Nat → UInt8) (R : Nat)
    (hnd : rots.Nodup) (hR : R < 2 ^ 256) (hb : R + rots.length * 32 ≤ 2 ^ 256)
    (hmax : ∀ r ∈ rots, 0 ≤ r → r ≤ maxRot)
    (hmin : ∀ r ∈ rots, r < 0 → minRot ≤ r) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.block (GenAstPcs.pcsBlock1Ast rots maxRot minRot false []))
      (b1BlockPre xp op oip xv om oi rv mem0 R rots)
      (fun V st V' st' o => o = .normal ∧ V' = V ∧ st'.env = st.env ∧
        st'.halted = st.halted ∧
        (∀ (i : Nat) (hi : i < rots.length),
          loadWord st'.memory (R + i * 32) = rotVal xv om oi rv (rots[i]'hi)) ∧
        (∀ a, a < R ∨ R + rots.length * 32 ≤ a → st'.memory a = mem0 a)) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩ := hpre
  cases hrun with
  | block hbody =>
    rename_i Vb
    rw [pcsBlock1Ast_eq] at hbody
    obtain ⟨ho, hrestore, henv, hhalt, htable, hout'⟩ :=
      pcs_b1_body (c := c) (g := g) (funs := funs) rots maxRot minRot xp op oip xv om oi rv
        mem0 R hnd hR hb hmax hmin V st ⟨hX, hO, hOI, hRP, hrv, hx, ho, hoi, hout⟩
        Vb _ o hbody
    exact ⟨ho, hrestore, henv, hhalt, htable, hout'⟩
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_b1_body
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_b1_sem
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.wWalk_eq
  [propext, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.rotVal_eq
  [propext, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b1_reset_contract
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.b1_lets_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b1_store_only
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b1_head_contract
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.b1_store_step
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.b1_walk_contract
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.pcs_b2_prefix
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_b2_lets
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_b2_sem
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_b2_sem_inline
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsRows.decode_exists [propext, Classical.choice, Quot.sound]
  native []
#assert_axioms Midfall.LoweringV3.PcsRows.inline_loopBody_false
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.inline_loopBody_true
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcsBlock2_inline
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcsLoadWord_writeWords_lt
  [propext, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_loop_false
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.pcs_loop_true
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.readBytes_storeWord_32
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.bytesToNatBE_readBytes_32
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.readBytes_append
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsRows.readBytes_storeWord_outside
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.PcsRows

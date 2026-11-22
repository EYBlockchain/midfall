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

  ROW.PCS.2 (`pcs_b2_sem`), the block SEM leaves 1/3/4/5/6 and the row glue are not stated here.
  Stating them without their proofs would add register rows that need their own W12 falsifiers, and
  `Rows.lean`'s two pcs leaves must not be moved onto unproved children. Section 4 proves the
  block-2 inliner facts AND the full alignment `pcsBlock2_inline`: the slice is the literal
  `pcsBlock2Inline a1 aP nb trunc`. The remaining piece for `pcs_b2_sem` is the loop's `AllRuns`
  contract over `pcsLoopBody` (`wPowers`, the `p = aP + 32j` / `acc` / `writeWords` invariant). It
  is not a premise and adds no hypothesis to a row.
-/
import Midfall.LoweringV2.Stages
import Midfall.Lowering.GenAstPcs
import Midfall.Yul.Word
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
theorem mapM_frOfWord?_of_all (l : List Word256)
    (h : l.all (fun w => w.toNat < p) = true) :
    ∃ inst : List (Fr p), l.mapM (frOfWord? (p := p)) = some inst := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨ha, has⟩ := h
      obtain ⟨inst, hin⟩ := ih has
      have hfa : frOfWord? (p := p) a = some (Nat.cast a.toNat) := by
        simpa [frOfWord?] using ha
      refine ⟨(Nat.cast a.toNat) :: inst, ?_⟩
      rw [List.mapM_cons]
      change Option.bind (frOfWord? (p := p) a)
        (fun x => Option.bind (List.mapM (frOfWord? (p := p)) as) (fun xs => some (x :: xs))) =
        some (Nat.cast a.toNat :: inst)
      rw [hfa, Option.bind_some, hin]
      rfl

/-- The array form: a word array all of whose entries are below `p` has an `instOfWords?` image. -/
theorem instOfWords?_of_all (l : List Word256)
    (h : l.all (fun w => w.toNat < p) = true) :
    ∃ inst : Array (Fr p), instOfWords? (p := p) l.toArray = some inst := by
  obtain ⟨instL, hmap⟩ := mapM_frOfWord?_of_all (p := p) l h
  refine ⟨instL.toArray, ?_⟩
  unfold instOfWords?
  rw [show l.toArray.toList = l from rfl, hmap]
  rfl

/-- **The raw walk's instance guard is `instOfWords?`.** Unfolds `rawDecode` and reads the last
  `split_ifs` branch; no semantic fact is used. -/
theorem instOfWords?_of_rawDecode {L : ProofCalldataLayout} {n : Nat} {cd : Bytes}
    {raw : List (RawMsg p)} {iw : Array Word256}
    (h : rawDecode (p := p) L n cd = some (raw, iw)) :
    ∃ inst : Array (Fr p), instOfWords? (p := p) iw = some inst := by
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
  `AllRuns` proof itself is the next step and is not stated here (no register row is added). The
  generic `VEnv` lemmas are dialect-generic copies of the ones `LagrangeRows`/`QuotientRows`
  already proved; they are copied rather than imported so this file's cone does not pull in the
  quotient modules. -/

/-- `VEnv.set` preserves length. -/
theorem venv_set_length {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (a : D.Value) : (VEnv.set V x a).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

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

/-- A scope that adds one binding exits by dropping it. -/
theorem restore_cons_length {D : YulSemantics.Dialect} [DecidableEq D.Value] {V W : VEnv D}
    {y : Ident} {b : D.Value} (h : W.length = V.length) :
    restore V ((y, b) :: W) = W := by
  simp [restore, h]

/-- EVM `mulmod` at an arbitrary modulus word. -/
def wMulmodAt (a b n : U256) : U256 :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)

/-- The x1 power table exactly as block 2's loop writes it. -/
def wPowers (r x1 : U256) (mask : Bool) : Nat → U256 × U256
  | 0 => (1, 1)
  | i + 1 =>
      let acc := wMulmodAt (wPowers r x1 mask i).1 x1 r
      (acc, if mask then acc &&& BitVec.ofNat 256 (2 ^ 128 - 1) else acc)

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

end Midfall.LoweringV3.PcsRows

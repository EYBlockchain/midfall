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
  `Rows.lean`'s two pcs leaves must not be moved onto unproved children. `pcs_b2_sem`'s remaining
  obstacle is NOT a premise: it is the kernel shape of `Inline.inlineContractConstants` on
  `pcsBlock2Ast` (the inliner unfolds through 64 fuel levels with a symbolic `Consts`, so the
  literal block has to be reached by the `inlineScan_append`/`stepAcc` route, phase 2).
-/
import Midfall.LoweringV2.Stages
import Midfall.Lowering.GenAstPcs
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

#assert_axioms Midfall.LoweringV3.PcsRows.decode_exists [propext, Classical.choice, Quot.sound]
  native []

end Midfall.LoweringV3.PcsRows

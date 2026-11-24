/-
  StatementsV3 (SCRATCH - design area "statements", PLAN-V3)

  THE REPAIRED STATEMENT SURFACE, as it should read after sign-off. Typechecked against the built
  tree with `lake env lean` from formal/. Nothing here is in the repository.

  Naming: every repaired item carries a V3 suffix (or a new name) and lives in
  `Midfall.LoweringV3`, so nothing clashes with the frozen `Midfall.LoweringV2` text it replaces.
  `Render` itself is NOT changed: the eleven fields of `LoweringV2.Render` are reused as they are.

  Sections follow the brief:
    §G  codec laws                         (g)
    §A  calldataOfV3                       (a)
    §D  scopeV3, slicesV3, noShadow        (d)
    §J  the repaired WellFormed clause     (j)
    §N  programOk: the program checks      (RECON.1: the seven D-P71 clauses)
    §B  PlanMeta (circuitMeta + data)      (b)
    §C  PayloadAgrees                      (c)
    §I  ExitDiscipline, TwoOutcomes        (i)
    §V  ValidV3 - THE SINGLE TEXT, and its projections
    §E  EntryFrameV3                       (e)
    §F  GasTotal, the totality conjunct    (f)
    §K  LoweringEquivalenceV3, the four-obligation composition,
        HypothesesInhabitedV3, EndToEndV3                            (h), (k)

  DEFINITIONS are real. THEOREMS that are obligations of the plan are stated and `sorry`ed, each
  with the experiment that discharges it; the ones that are cheap are PROVED here.

  This file imports nothing from Midfall/Instances (D-P17): the deployment measurements are in
  StatementsV3Deploy.lean, the refutations of the frozen text in StatementsV3Falsifiers.lean.
-/
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Generated
import Midfall.LoweringV2.ProgramLemmas
import Midfall.LoweringV3.RunMono
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §G. The codec laws (g)

  OLD: `Assumptions/Codec.lean:75-90` `G1CodecLaws` (seven fields), a hypothesis of conjunct 2 only
  (`Statements.lean:305`) and of `BlockProgress` only (`Blocks.lean:126`).

  WHY IT IS NOT ENOUGH. `verifyMsgs` (`Native.lean:269-292`) re-serialises every decoded G1 message
  with `toCompressed` and re-reads it with `ofCompressed?` (`Transcript.lean:65-69`, `:145-151`).
  `G1CodecLaws.compressedRoundtrip` is DECODER-first, so a codec whose `ofCompressed?` is the
  constant `none` satisfies all seven laws (`CurveSurface.lean:540 g1CodecZ_laws` is that proof)
  and makes `LeanAccepts` identically false. The ENCODER-first law is what forces the re-read to
  return the point that was decoded from calldata. -/

/-- THE LAWS EVERY CONJUNCT OF THE HEADLINE NEEDS (soundness included).

    * `eipRoundtrip` - `decodeCalldata` yields `Q` with `ofEip? b = some Q`; the contract absorbed
      and copied the raw bytes `b`; `Inv` compares memory with `toEip Q` (`Inv.lean:401-402`).
    * `compressedEncoderFirst` - `verifyMsgs` reads back `ofCompressed? (toCompressed Q)`; without
      this law it reads `none` (Lean rejects everything) or another point (finding A-4).
    * `compressedWidth` - the transcript cursor advances by `g1CompressedWidth` per G1 read
      (`Transcript.read`), so a wrong width misaligns every later read.
    * `toEip_one` - the committed-instance commitment is absorbed by the contract as 128 zero
      bytes (`TranscriptProofParser.yul:36-46`) and by Lean as `toEip 1`; the `g1_identity`
      window of `Inv` is the same pin. -/
structure G1CodecHeadlineLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  toEip_one : c.toEip 1 = natToBytesBE 0 128

/-- THE FULL BUNDLE `EndToEndV3` NEEDS: the seven frozen laws plus the encoder-first one. The four
    extra laws over `G1CodecHeadlineLaws` are consumed by the calldata round trip only:
    `compressedRoundtrip` by `verifyNative_iff_msgs_codec` (`Obligations.lean:832`) and
    `repack_spec_of_decodeRust` (`Calldata.lean:1276`); `ofEip_toEip`, `eipShape`, `eipWidth` by
    `calldata_roundtrip` (`Calldata.lean:731`). -/
structure G1CodecLawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop
    extends G1CodecLaws c where
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q

/-- The full bundle gives the headline bundle. PROVED. -/
theorem G1CodecLawsV3.headline {G₁ : Type} [Group G₁] {c : G1Codec G₁} (h : G1CodecLawsV3 c) :
    G1CodecHeadlineLaws c :=
  ⟨h.eipRoundtrip, h.compressedEncoderFirst, h.compressedWidth, h.toEip_one⟩

/-- A codec whose compressed half is `comp`, with the decoder chosen classically. This is the
    shape `g1zOfEip?` already has for the EIP half (`G1Agreement.lean:1996`). -/
noncomputable def withCompressed {G₁ : Type} (c : G1Codec G₁) (comp : G₁ → Bytes) : G1Codec G₁ :=
  { c with
    toCompressed := comp
    ofCompressed? := fun b =>
      open Classical in if h : ∃ Q, comp Q = b then some (Classical.choose h) else none }

/-- WITNESS (joint satisfiability, generic). Any codec satisfying the seven frozen laws becomes a
    codec satisfying all eight once its compressed half is replaced by an INJECTIVE map of the
    right width. PROVED: so the V3 law set is satisfiable wherever the frozen one is and an
    injection `G₁ → 48 bytes` exists. `StatementsV3Deploy.lean` instantiates it at `G₁z`. -/
theorem withCompressed_lawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) (hc : G1CodecLaws c)
    (comp : G₁ → Bytes) (hinj : Function.Injective comp)
    (hw : ∀ Q, (comp Q).size = g1CompressedWidth) : G1CodecLawsV3 (withCompressed c comp) where
  eipRoundtrip := hc.eipRoundtrip
  compressedRoundtrip := by
    intro b Q h
    simp only [withCompressed] at h
    by_cases hex : ∃ Q, comp Q = b
    · simp only [hex, ↓reduceDIte] at h
      have hQ : Classical.choose hex = Q := Option.some.inj h
      rw [← hQ]
      exact Classical.choose_spec hex
    · simp only [hex, ↓reduceDIte] at h
      cases h
  ofEip_toEip := hc.ofEip_toEip
  eipShape := hc.eipShape
  toEip_one := hc.toEip_one
  compressedWidth := hw
  eipWidth := hc.eipWidth
  compressedEncoderFirst := by
    intro Q
    have hex : ∃ Q', comp Q' = comp Q := ⟨Q, rfl⟩
    simp only [withCompressed, hex, ↓reduceDIte]
    exact congrArg some (hinj (Classical.choose_spec hex))

/-! ## §A. calldataOfV3 (a)

  OLD (`Statements.lean:335-340`):
      (repackProof plan R.E.g1 π).mapError fromRepackError >>= fun π' =>
        encodeCalldata R.cfg.numInstances plan R.E.g1 π' inst
  `Lowering.encodeCalldata` (`Calldata.lean:241-250`) repacks its proof argument AGAIN, so the
  second repack sees `repackedLen` bytes where it demands `compressedLen` and throws
  `lengthMismatch`. The frozen term never returns `.ok`.

  NEW: the tree's own intended composition, `Lowering.repackThenEncode` (`Calldata.lean:257`). -/

/-- The calldata the ported repacker and encoder produce for a compressed proof. -/
def calldataOfV3 (R : Render p G₁ G₂ Gₜ) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  Midfall.Lowering.repackThenEncode (p := p) R.cfg.numInstances
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π inst

/-- The FROZEN composition, as a function of exactly the three things it reads off the render, so
    that it can be EVALUATED on the in-tree toy data (a `Render` needs a prime-order group and
    a pairing; `CdKats.ToyG` is a two-point type). PINNED VERBATIM AS OF ST.4 (the D-P27 pattern:
    an amended frozen statement keeps its old text as a named definition next to the exhibit that
    shows why it was wrong): until ST.4 the live `LoweringV2.calldataOf` WAS this term, by `rfl`,
    and the bridge lemma said so. From ST.4 on the live def is `repackThenEncode`, the bridge is
    false and is gone, and this core is what the falsifier `frozenCalldata_isOk` evaluates. -/
def frozenCalldataCore {G : Type} (numInstances : Nat) (plan : RepackedProofLayoutPlan)
    (c : G1Codec G) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  (Midfall.Lowering.repackProof (p := p) plan c π).mapError
      Midfall.Generator.GeneratorError.fromRepackError >>= fun π' =>
    Midfall.Lowering.encodeCalldata (p := p) numInstances plan c π' inst


section CalldataWitness
open Midfall.Lowering.CdKats
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- WITNESS for (a): on the toy data the repaired composition returns `.ok`, the result is the
    tree's canonical `Lowering.calldataOf` of the toy messages, and `decodeCalldata` reads it
    back. `katLayout`'s plan is `katPlan` (the last conjunct), so this is the composition
    `calldataOfV3` performs. -/
def calldataOfV3_witness_ok : Bool :=
  (match Midfall.Lowering.repackThenEncode (p := 17) 1 katPlan toyCodec katCompressed #[5] with
   | .ok cd =>
       cd == Midfall.Lowering.calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 5] &&
       (match Midfall.Lowering.decodeCalldata (p := 17) katLayout 1 toyCodec cd with
        | some (ms, inst) => ms.map msgCode == katMsgs.map msgCode && inst.toList.map BitVec.toNat == [5]
        | none => false)
   | .error _ => false) &&
  (RepackedProofLayoutPlan.fromProofLayout katLayout).slots == katPlan.slots

#eval calldataOfV3_witness_ok   -- expect true

/-- FALSIFIER for the frozen text, at the same data: `.ok` never comes back. -/
def frozenCalldata_isOk : Bool :=
  match frozenCalldataCore (p := 17) 1 katPlan toyCodec katCompressed #[5] with
  | .ok _ => true
  | .error _ => false

#eval frozenCalldata_isOk   -- expect false

end CalldataWitness

/-! ## §D. The block scope and the slice decomposition (d)

  OLD (`Statements.lean:107-110`): `Render.scope c g := [hoist D R.helpers]`, with the docstring
  "the only funDefs of the program". FALSE for the generator's text: `q_program_fail` and `q_pow5`
  are defined inside the quotient region (token indices 3814 and 3837 of
  `mainAssemblyTokens poseidonM`), so once WP-G1 emits them `lookupFun (R.scope c g) "q_pow5"` is
  `none` and no slice run through that call exists.

  TWO CANDIDATES were measured (`ProbeScope.lean`):
    A. `[hoist D (R.prog 0 0)]`                       - `fail_lookup ... := rfl` FAILS for generic R
    B. `[hoist D R.helpers ++ hoist D R.slices]`      - `fail_lookup ... := rfl` still holds
  `Blocks/TraceReturn.lean:405 fail_lookup` is the one place the tree unfolds the scope, and it
  does so by `rfl`; under A the reduction is stuck on `wrapperLocals`' `if m.embeddedVk.isNone`.
  B is A up to the structural lemma `hoist_prog_eq_scopeV3` below, is address-independent by
  construction (no `hoist_prog_addr_indep` needed to state it), and keeps every existing lookup.
  V3 takes B. -/

/-- The seven slices in include order. Moved from `Blocks.lean:202` (refinable) into the statement
    surface, because the scope is now defined through it. Same text. -/
def slicesV3 (R : Render p G₁ G₂ Gₜ) : YulBlock :=
  R.slice .vkLoading ++ R.slice .transcriptParser ++ R.slice .lagrange ++
    R.slice .quotientLin ++ R.slice .pcs ++ R.slice .finalPairing ++ R.slice .traceReturn

/-- It is the definition `Blocks.lean` already uses. -/
theorem slicesV3_eq (R : Render p G₁ G₂ Gₜ) : slicesV3 R = R.slices := rfl

/-- THE FUNCTION SCOPE EVERY BLOCK RUNS IN: every function the closed program defines at its top
    level - the inlined helpers, then whatever the slices define (the quotient region's
    `q_program_fail`, `q_pow5`, `q_limb7*`). -/
def scopeV3 (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas) :
    FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) R.helpers ++ hoist (Bridge.Dialect c g) (slicesV3 R)]

/-- NO SHADOWING, decidably: no top-level binder of the un-inlined program is a constant name.
    This is the side condition of `inline_append` (`ProgramLemmas.lean:27`), without which
    `prog_slices_decomp` is false (findings B-5, D-13: a model constant named `r` is substituted in
    the standalone slices and not in the program). solc rejects such shadowing, so the clause also
    aligns the model with Solidity. -/
def noShadowCore (pv : PlanView) (m : Model) : Bool :=
  (topBinders (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m)).all
    fun x => !((constTableOf m).map Prod.fst).contains x

/-- The render-level face of `noShadowCore`. -/
def noShadowB (R : Render p G₁ G₂ Gₜ) : Bool := noShadowCore R.pv R.model

/-! ### ST.11 machinery: the shadow condition, and the shape of the inliner

  Nothing below is a new assumption about a render. The hypothesis `noShadowB R = true` is
  PROJECTED out of `ValidV3.program` by `noShadow_of_programOk` (section N), never postulated,
  and every lemma here is a fact about the emitter and about `Inline.inlineContractConstants`.
  D-P71: generic in `R`, no fixture in any statement, no `native_decide`. -/

/-- Is this statement a top-level function definition? `hoist` is exactly the `filterMap` that
    keeps these, so this boolean is the one `hoist` cares about. -/
private def isFunDefStmt (s : Stmt EVM.Op) : Bool :=
  match s with | Stmt.funDef _ _ _ _ => true | _ => false

/-- THE THIRTEEN TOP-LEVEL PIECES OF THE UN-INLINED PROGRAM, in declaration order: the ABI guard,
    the wrapper locals, the main guard, the two helper trees, the two main locals and the seven
    slices. `asmOf` is `inlineContractConstants` of the flattening of this list. -/
private def progPieces (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256) : List YulBlock :=
  [abiGuardBlock R.model, wrapperLocals R.model vkAddr qAddr, mainGuardBlock,
    GenAst.emitHelpers R.pv, GenAst.emitAccumulatorHelpers, mainLocals,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .vkLoading,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .transcriptParser,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .lagrange,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .quotientLin,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .pcs,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .finalPairing,
    GenAst.emitPartialM R.pv (partialCtxOfVerifier R.model) .traceReturn]

/-- `topBinders` is a `flatMap`, so it distributes over `++`. -/
private theorem topBinders_append (a b : YulBlock) :
    topBinders (a ++ b) = topBinders a ++ topBinders b := by
  simp only [topBinders, List.flatMap_append]

/-- THE WRAPPER LOCALS BIND THE SAME TWO NAMES whatever addresses they are given. This is what
    lets the scan of `noShadowCore` at `(0, 0)` license the cuts of a program built at the
    deployment addresses. -/
private theorem topBinders_wrapperLocals (m : Model) (vkAddr qAddr : U256) :
    topBinders (wrapperLocals m vkAddr qAddr) = topBinders (wrapperLocals m 0 0) := by
  by_cases h1 : m.embeddedVk = none <;> by_cases h2 : m.quotientExternal.isSome <;>
    simp [topBinders, wrapperLocals, Inline.boundOf, List.flatMap, h1, h2]

/-- **THE CUT LEMMA, N WAYS.** `inline_append` at every cut of a block list at once. The
    hypothesis is read off the FLAT block rather than off each piece, which is what makes it
    usable: `noShadowCore` scans the flat un-inlined program, so one membership chain licenses
    every cut. -/
private theorem inline_append_many_aux (consts : List (String × Nat)) :
    ∀ (l : List YulBlock), (∀ x ∈ topBinders l.flatten, x ∉ consts.map Prod.fst) →
      Inline.inlineContractConstants consts (l.flatten) =
        (l.map (Inline.inlineContractConstants consts)).flatten := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b rest ih =>
      intro h
      have h1 : ∀ x ∈ topBinders b, x ∉ consts.map Prod.fst := by
        intro x hx
        refine h x ?_
        simp only [List.flatten_cons, topBinders_append]
        exact List.mem_append_left (topBinders rest.flatten) hx
      have h2 : ∀ x ∈ topBinders rest.flatten, x ∉ consts.map Prod.fst := by
        intro x hx
        refine h x ?_
        simp only [List.flatten_cons, topBinders_append]
        exact List.mem_append_right (topBinders b) hx
      rw [List.flatten_cons, List.map_cons, List.flatten_cons,
        Midfall.LoweringV2.inline_append consts b rest.flatten h1, ih h2]

private theorem inline_append_many (consts : List (String × Nat)) (l : List YulBlock)
    (h : ∀ x ∈ topBinders l.flatten, x ∉ consts.map Prod.fst) :
    Inline.inlineContractConstants consts (l.flatten) =
      (l.map (Inline.inlineContractConstants consts)).flatten :=
  inline_append_many_aux consts l h

/-- The inliner rewrites a statement IN PLACE: `inlineStmtStep` maps block/cond/letDecl/assign/
    switch/forLoop/exprStmt to the same constructor and only ever produces a `funDef` from a
    `funDef`. So it cannot create a top-level function definition. -/
private theorem inlineStmtStep_isFunDef
    {rec : List String -> List (Stmt EVM.Op) -> Inline.SRes}
    {consts : List (String × Nat)} {sh : List String} {s : Stmt EVM.Op}
    (h : !isFunDefStmt s) : !isFunDefStmt (Inline.inlineStmtStep rec consts sh s).1 := by
  cases s
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · exact h
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]
  · simp only [isFunDefStmt, Inline.inlineStmtStep, Bool.not_false]

/-- The fold invariant: a block with no top-level `funDef` folds to no top-level `funDef`,
    whatever accumulator it starts from. -/
private theorem foldl_isFunDef
    {rec : List String -> List (Stmt EVM.Op) -> Inline.SRes}
    {consts : List (String × Nat)}
    (h : ∀ (sh : List String) (s : Stmt EVM.Op), !isFunDefStmt s →
        !isFunDefStmt (Inline.inlineStmtStep rec consts sh s).1) :
    ∀ (X : List (Stmt EVM.Op)) (acc : Inline.Acc),
      (∀ s ∈ acc.blks, !isFunDefStmt s) → (∀ s ∈ X, !isFunDefStmt s) →
      ∀ s ∈ (X.foldl (Inline.stepAcc rec consts) acc).blks, !isFunDefStmt s := by
  intro X
  induction X with
  | nil =>
      intro acc ha _ s hs
      have hs' : s ∈ acc.blks := by simpa [List.foldl_nil] using hs
      exact ha s hs'
  | cons t r ih =>
      intro acc ha hr s hs
      rw [List.foldl_cons] at hs
      have acc' : ∀ x ∈ (Inline.stepAcc rec consts acc t).blks, !isFunDefStmt x := by
        intro x hx
        rw [Inline.stepAcc_blks] at hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ha x hx
        · exact h acc.sh t (hr t (List.Mem.head r))
      exact ih (Inline.stepAcc rec consts acc t) acc'
        (fun x hx => hr x (List.Mem.tail t hx)) s hs

/-- **THE INLINER CREATES NO TOP-LEVEL FUNCTION DEFINITION.** The walk is one `inlineStep`, i.e.
    one `foldl` over the block (`Inline.inlineStep_eq_foldl`), so the fold invariant carries it. -/
private theorem noFunDef_inline {consts : List (String × Nat)} {X : YulBlock}
    (h : ∀ s ∈ X, !isFunDefStmt s) :
    ∀ s ∈ Inline.inlineContractConstants consts X, !isFunDefStmt s := by
  have hblks : Inline.inlineContractConstants consts X =
      (X.foldl (Inline.stepAcc (Inline.inlineScan 63 consts) consts) (Inline.initAcc [])).blks := by
    show (Inline.inlineScan Inline.inlineFuel consts [] X).blks = _
    have h1 : Inline.inlineScan Inline.inlineFuel consts [] X =
        Inline.inlineStep (Inline.inlineScan 63 consts) consts [] X := rfl
    rw [h1, Inline.inlineStep_eq_foldl]
  have hstep : ∀ (sh : List String) (s : Stmt EVM.Op), !isFunDefStmt s →
      !isFunDefStmt (Inline.inlineStmtStep (Inline.inlineScan 63 consts) consts sh s).1 :=
    fun sh s hs => inlineStmtStep_isFunDef hs
  rw [hblks]
  exact foldl_isFunDef hstep X (Inline.initAcc [])
    (fun s hs => absurd hs (by simp [Inline.initAcc_blks])) h

/-- `hoist` keeps exactly the `funDef`s, so a block with none hoists to the empty scope. -/
private theorem hoist_nil_of_isFunDef {c : ExternalCalls} {g : ExternalGas} (X : YulBlock)
    (h : ∀ s ∈ X, !isFunDefStmt s) : hoist (Bridge.Dialect c g) X = [] := by
  unfold hoist
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  cases s with
  | funDef n ps rs body =>
      have h2 := h (Stmt.funDef n ps rs body) hs
      simp [isFunDefStmt] at h2
  | _ => rfl

/-- The prefix and the main locals hoist to the EMPTY scope, inlined or not. -/
private theorem hoist_inline_nil {c : ExternalCalls} {g : ExternalGas}
    {consts : List (String × Nat)} {X : YulBlock} (h : ∀ s ∈ X, !isFunDefStmt s) :
    hoist (Bridge.Dialect c g) (Inline.inlineContractConstants consts X) = [] :=
  hoist_nil_of_isFunDef _ (noFunDef_inline h)

/-- `hoist` is a `filterMap`, so it distributes over `++`. -/
private theorem hoist_append {c : ExternalCalls} {g : ExternalGas} (a b : YulBlock) :
    hoist (Bridge.Dialect c g) (a ++ b) =
      hoist (Bridge.Dialect c g) a ++ hoist (Bridge.Dialect c g) b := by
  simp only [hoist, List.filterMap_append]

/-- The guard block, the wrapper locals and the main guard declare no function. -/
private theorem noFunDef_prefix (m : Model) (vkAddr qAddr : U256) :
    ∀ s ∈ abiGuardBlock m ++ wrapperLocals m vkAddr qAddr ++ mainGuardBlock, !isFunDefStmt s := by
  by_cases h1 : m.embeddedVk = none <;> by_cases h2 : m.quotientExternal.isSome <;>
    simp [isFunDefStmt, abiGuardBlock, mainGuardBlock, wrapperLocals, h1, h2]

/-- The two main locals declare no function. -/
private theorem noFunDef_mainLocals : ∀ s ∈ mainLocals, !isFunDefStmt s := by
  simp [isFunDefStmt, mainLocals]

/-- **THE STRUCTURAL DECOMPOSITION, RESTATED** (replaces `Blocks.lean:220 prog_slices_decomp`).
    Conjunct 1 is unchanged but now carries the no-shadow hypothesis it needs. Conjunct 2 was
    `hoist prog = hoist helpers` (false once the quotient functions are emitted) and is now "the
    hoisted program scope is the block scope".

    PROVED (ST.11). THE SHAPE. Write the un-inlined program as the flat list of its THIRTEEN
    top-level pieces - the ABI guard, the wrapper locals, the main guard, the two helper trees,
    the two main locals and the seven slices - so `asmOf` is `inline` of the flat block.
    `noShadowB R` says every top-level binder of that flat block names no constant of `R.consts`,
    so EVERY cut of it satisfies the side condition of `inline_append`, and `inline_append_many`
    distributes the inliner over all twelve cuts at once; regrouping the first three pieces into
    `R.preSlice` and the next two into `R.helpers` is `inline_append` three times more. (The card
    said five cuts: that was the pre-OBJ.2 shape, before `emitAccumulatorHelpers` joined the
    helper tree and before the quotient region put seven separate `emitPartialM` arms where
    `emitSlices` was one.) Conjunct 2 is conjunct 1 under `hoist`: `hoist` is a `filterMap`
    (`hoist_append`), and neither the prefix nor the main locals contains a top-level `funDef`
    even AFTER inlining (`hoist_inline_nil`), so what is left is exactly `scopeV3`. NOTHING WAS
    POSTULATED: `noShadowB` is the projection `noShadow_of_programOk` of `ValidV3.program`; no
    clause was added to `ValidV3`; and the only tree premise is
    `Midfall.LoweringV2.inline_append` (GEN.4, proved, cone `-`). -/
theorem prog_slices_decompV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (vkAddr qAddr : U256) (c : ExternalCalls) (g : ExternalGas) :
    R.prog vkAddr qAddr =
        R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ slicesV3 R ∧
      [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = scopeV3 R c g := by
  -- THE FLAT UN-INLINED PROGRAM, and `noShadowB` in ∀ form at the addresses the scan uses.
  have hflatB : abiGuardBlock R.model ++ wrapperLocals R.model vkAddr qAddr
      ++ mainAsmRaw R.pv R.model = (progPieces R vkAddr qAddr).flatten := by
    show abiGuardBlock R.model ++ wrapperLocals R.model vkAddr qAddr
        ++ (mainGuardBlock ++ GenAst.emitHelpers R.pv ++ GenAst.emitAccumulatorHelpers
            ++ mainLocals ++ GenAst.emitSlicesM R.pv (partialCtxOfVerifier R.model)) = _
    rw [emitSlicesM_eq]
    simp only [progPieces, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
  have hall0 : ∀ x ∈ topBinders (abiGuardBlock R.model ++ wrapperLocals R.model 0 0
      ++ mainAsmRaw R.pv R.model), x ∉ R.consts.map Prod.fst := by
    have h := List.all_eq_true.mp hns
    intro x hx hmem
    have hx' := h x hx
    have h2 : ((constTableOf R.model).map Prod.fst).contains x = true :=
      List.contains_iff_mem.mpr hmem
    rw [h2, Bool.not_true] at hx'
    exact Bool.noConfusion hx'
  have hW : topBinders (abiGuardBlock R.model ++ wrapperLocals R.model vkAddr qAddr
      ++ mainAsmRaw R.pv R.model)
      = topBinders (abiGuardBlock R.model ++ wrapperLocals R.model 0 0
        ++ mainAsmRaw R.pv R.model) := by
    simp only [topBinders_append, topBinders_wrapperLocals]
  have hall : ∀ x ∈ topBinders (abiGuardBlock R.model ++ wrapperLocals R.model vkAddr qAddr
      ++ mainAsmRaw R.pv R.model), x ∉ R.consts.map Prod.fst := by
    intro x hx
    refine hall0 x ?_
    rw [← hW]
    exact hx
  have hmany : ∀ x ∈ topBinders (progPieces R vkAddr qAddr).flatten,
      x ∉ R.consts.map Prod.fst := by
    intro x hx
    refine hall x ?_
    rw [hflatB]
    exact hx
  have hflat : R.prog vkAddr qAddr =
      Inline.inlineContractConstants R.consts (progPieces R vkAddr qAddr).flatten := by
    show Inline.inlineContractConstants (constTableOf R.model)
        (abiGuardBlock R.model ++ wrapperLocals R.model vkAddr qAddr ++ mainAsmRaw R.pv R.model) = _
    rw [hflatB]
    simp only [Midfall.LoweringV2.Render.consts]
  -- THE THREE SHADOW FACTS THE REGROUPING NEEDS: each piece is a sub-block of the flat program.
  have tbSub : ∀ x ∈ topBinders (abiGuardBlock R.model),
      x ∈ topBinders (progPieces R vkAddr qAddr).flatten := by
    intro x hx
    simp only [progPieces, topBinders_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.mem_append]
    tauto
  have tbSubB : ∀ x ∈ topBinders (wrapperLocals R.model vkAddr qAddr),
      x ∈ topBinders (progPieces R vkAddr qAddr).flatten := by
    intro x hx
    simp only [progPieces, topBinders_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.mem_append]
    tauto
  have tbSubH : ∀ x ∈ topBinders (GenAst.emitHelpers R.pv),
      x ∈ topBinders (progPieces R vkAddr qAddr).flatten := by
    intro x hx
    simp only [progPieces, topBinders_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.mem_append]
    tauto
  have hcA : ∀ x ∈ topBinders (abiGuardBlock R.model),
      x ∉ (constTableOf R.model).map Prod.fst :=
    fun x hx => hmany x (tbSub x hx)
  have hcB : ∀ x ∈ topBinders (wrapperLocals R.model vkAddr qAddr),
      x ∉ (constTableOf R.model).map Prod.fst := fun x hx => hmany x (tbSubB x hx)
  have hcH : ∀ x ∈ topBinders (GenAst.emitHelpers R.pv),
      x ∉ (constTableOf R.model).map Prod.fst :=
    fun x hx => hmany x (tbSubH x hx)
  -- CONJUNCT 1. One `simp` normalises both sides to the same right-nested concatenation of the
  -- thirteen inlined pieces: the left unfolds `progPieces` through the N-way cut lemma, the right
  -- unfolds `preSlice`/`helpers`/`mainLocalsInlined`/`slicesV3` and splits the two grouped blocks
  -- with `inline_append` at the three cuts whose side condition the scan supplies.
  have h1 : R.prog vkAddr qAddr =
      R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ slicesV3 R := by
    rw [hflat, inline_append_many R.consts (progPieces R vkAddr qAddr) hmany]
    simp only [Midfall.LoweringV2.Render.preSlice, Midfall.LoweringV2.Render.helpers,
      Midfall.LoweringV2.Render.mainLocalsInlined, Midfall.LoweringV2.Render.slice,
      Midfall.LoweringV2.sliceOf,
      Midfall.LoweringV2.helpersOf, Midfall.LoweringV2.Render.consts, slicesV3, progPieces,
      Midfall.LoweringV2.inline_append (constTableOf R.model) (abiGuardBlock R.model)
        (wrapperLocals R.model vkAddr qAddr ++ mainGuardBlock) hcA,
      Midfall.LoweringV2.inline_append (constTableOf R.model)
        (wrapperLocals R.model vkAddr qAddr) mainGuardBlock hcB,
      Midfall.LoweringV2.inline_append (constTableOf R.model) (GenAst.emitHelpers R.pv)
        GenAst.emitAccumulatorHelpers hcH,
      List.flatten_cons, List.map_cons, List.flatten_nil, List.map_nil, List.append_nil,
      List.append_assoc]
  have hpre_nil : hoist (Bridge.Dialect c g) (R.preSlice vkAddr qAddr) = [] :=
    hoist_inline_nil (noFunDef_prefix R.model vkAddr qAddr)
  have hml_nil : hoist (Bridge.Dialect c g) R.mainLocalsInlined = [] :=
    hoist_inline_nil noFunDef_mainLocals
  have h2 : [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = scopeV3 R c g := by
    rw [h1, hoist_append, hoist_append, hoist_append, hpre_nil, hml_nil]
    simp only [List.nil_append, List.append_nil, scopeV3]
  exact ⟨h1, h2⟩

/-- CONSEQUENCE, PROVED from the obligation above: the frozen `hoist_prog_addr_indep`
    (`Blocks.lean:145`, sorried) is no longer a separate hole. -/
theorem hoist_prog_addr_indepV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (c : ExternalCalls) (g : ExternalGas) (a b a' b' : U256) :
    hoist (Bridge.Dialect c g) (R.prog a b) = hoist (Bridge.Dialect c g) (R.prog a' b') := by
  have h1 := (prog_slices_decompV3 R hns a b c g).2
  have h2 := (prog_slices_decompV3 R hns a' b' c g).2
  exact List.head_eq_of_cons_eq (h1.trans h2.symm)

/-- A helper is still found where it was: the V3 scope starts with the hoisted helpers, and
    `lookupFun` short-circuits. PROVED, by the same `rfl` as `Blocks/TraceReturn.lean:405`. -/
theorem fail_lookupV3 (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    lookupFun (scopeV3 R c g) "fail" =
      some ({ params := ["sel"], rets := [],
              body := [Stmt.exprStmt (Expr.builtin Op.mstore
                  [Expr.lit (.number 0),
                   Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
                Stmt.exprStmt (Expr.builtin Op.revert
                  [Expr.lit (.number 0), Expr.lit (.number 4)])] },
            scopeV3 R c g) := rfl

/-! ## §J. VerifyingKey.WellFormed (j)

  OLD (`Halo2/Exec/VerifyingKey.lean:99-102`):
      permutationCommitmentsMatch :
        vk.permutation.commitments.size = divCeil vk.cs.permutation.columns.size (vk.csDegree - 2)
  That is the number of permutation PRODUCT commitments the PROOF carries (one per chunk,
  `permutation/verifier.rs:41-46`). The VK holds one sigma commitment per permutation COLUMN:
  `permutation/keygen.rs:244-250` (`Vec::with_capacity(p.columns.len())`, one push per column)
  and `permutation.rs:123` (`(0..argument.columns.len())`). The Lean port itself reads
  `vk.commitments.size` evaluations (`Permutation.lean:209`). 8 against 3 at the deployment. -/

/- **`WellFormedV3` IS DELETED (RECON.1 step 4).** Its one corrected clause - one sigma commitment per
    permutation COLUMN, not `divCeil columns (csDegree - 2)` - is kept as the computation
    `permCommMatchRepaired` (§N), a conjunct of `programOkB`, because `supported` is the frozen
    `SupportedV2` and cannot gain a field. The other six clauses were verbatim
    `VerifyingKey.WellFormed` fields and are carried by `SupportedV2.wf`. At the deployment the frozen
    clause is FALSE (8 against 3, `Deploy.wellFormedPermCounts_ok`) and the repaired one is TRUE (8
    against 8): R.7 repairs the frozen predicate, at which point `permCommMatchRepaired` is
    `supported.wf.permutationCommitmentsMatch` and leaves this file. -/
/-! ### D-GATE18 / D-GATE19 (2026-11-24)

  D-GATE18 adds `advicePhaseColumnOrder` to `VerifyingKey.WellFormed`: the phases,
  in `vk.cs.phases` order, enumerate the advice columns in column order.
  `advicePhaseTotal` fixes only the vector length, and the falsifier
  `advicePhaseTotal_not_columnOrder` shows the order is not derivable; it is the
  bridge between the parser's phase-indexed advice block and `scatterIndexed`'s
  column-indexed rows. It is a decidable key-side clause, not a row/bundle/`ValidV3`
  field.

  D-GATE19 is SIGNED as the genuine entry/calldata predicate
  `cdSize36 : cd.size < 2^36` on `EntryFrame`/`EntryFrameV3` (with `Decoded`'s
  `cd.size = proofEnd + 32 + 32 * numInstances`, this is exactly
  `numInstances < 2^31`). It is an entry witness, not a row/bundle/`ValidV3`
  field. `pfx_stageInv_start` reads `hentry.cdSize36` into the initial
  `Frame.cdSize36`, and `Frame` carries it across every later boundary. The fixed
  `TranscriptRows.tp_agrees` is therefore CLOSED by
  `tp_agrees_of_valid_closed_cdSize` with `hframe.cdSize36` (statement unchanged).
  `EndToEndV3` carries the named calldata premise
  `hcd36 : proofEnd + 32 + 32 * numInstances < 2^36` for the encoder's output,
  because its backward direction constructs an `EntryFrameV3`. -/

/-! ## §B. The plan's circuit meta and data (b)

  OLD (`Statements.lean:186-190`):
      circuitMeta : ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances
                      = .ok R.plan.meta_
      layout      : ProofCalldataLayout.fromProtocol R.plan.meta_.protocol abiVerifyProofProofCptr
                      R.plan.meta_.numEvals R.plan.meta_.numPointSets = .ok R.plan.proofLayout
  `ConstraintSystemMeta.new` returns `numPointSets := 0` (`Encoding.lean:473`). Rust's plan meta is
  that value AFTER `meta_data_for_vk` (`vk.rs:504-519`: `set_num_dummy_evals`, then
  `set_num_point_sets(kzg::num_point_sets(&meta, &data))`), and `plan.rs:238-244` builds the proof
  layout from the post-processed count. So the frozen pair forces a layout with zero `q_eval`
  words; no faithful plan satisfies both clauses.

  NEW: clause 1 states the post-processing. Clause 2 (`layout`) keeps its text. -/

/-- `vk.rs:504-519` at `Features.solidity` (`outer-fewer-point-sets` off, so `n_dummy = 0`): the
    meta the plan carries is the raw meta with the dummy count set to 0 and the point-set count
    set to `kzg::num_point_sets` of the data built from it; and the data is `Data::new` of that
    same pre-point-set meta. `m0` is the raw meta, `n` the point-set count.

    `Data.new` is given `R.plan.memory`. Rust gives it the intermediate default-config layout
    (`vk.rs:512-514`); `Data.new` reads ten base pointers of the layout (`Encoding.lean:626-639`)
    and at the deployment the two layouts agree on all ten (measured, `ProbeStable.lean`). That
    this holds for every render is NOT settled here; WP-G4's port of `LoweringPlan::new` replaces
    this clause by an equation with the ported constructor. -/
def PlanMeta (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ (m0 : ConstraintSystemMeta) (n : Nat),
    ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok m0 ∧
    Data.new (m0.setNumDummyEvals 0) R.plan.vk R.plan.memory = .ok R.plan.data ∧
    numPointSets (m0.setNumDummyEvals 0) R.plan.data = .ok n ∧
    R.plan.meta_ = (m0.setNumDummyEvals 0).setNumPointSets n

/-- The decidable face of the two clauses that do not mention `Data` equality (`Data` derives no
    `BEq`): what `StatementsV3Deploy.lean` evaluates. `cs` and `nci` are `R.vk.cs` and
    `R.cfg.numCommittedInstances`. -/
def planMetaB {F : Type} (cs : ConstraintSystem F) (nci : Nat) (plan : LoweringPlan Unit Unit) :
    Bool :=
  match ConstraintSystemMeta.new Features.solidity cs nci with
  | .error _ => false
  | .ok m0 =>
    match numPointSets (m0.setNumDummyEvals 0) plan.data with
    | .error _ => false
    | .ok n => plan.meta_ == (m0.setNumDummyEvals 0).setNumPointSets n

/-- The decidable face of the (unchanged) `layout` clause. -/
def planLayoutB (plan : LoweringPlan Unit Unit) : Bool :=
  match ProofCalldataLayout.fromProtocol plan.meta_.protocol abiVerifyProofProofCptr
      plan.meta_.numEvals plan.meta_.numPointSets with
  | .ok l => l == plan.proofLayout
  | .error _ => false

/-- The decidable face of the FROZEN clause 1, for the comparison table. -/
def frozenCircuitMetaB {F : Type} (cs : ConstraintSystem F) (nci : Nat)
    (plan : LoweringPlan Unit Unit) : Bool :=
  match ConstraintSystemMeta.new Features.solidity cs nci with
  | .ok m => m == plan.meta_
  | .error _ => false

/-! ## §C. The payload-content pins (c)

  OLD: `Valid.slots : EnvAgrees ...` (`Statements.lean:205`, `Inv.lean:533-579`) ties the payload
  `R.pv.vk` to the Lean key through ONE word, `vkDigestWord`. v1 had `VkSlotsAgree`
  (`Inv.lean:608-634`) for the three base slots; V2 dropped it. Nothing pins the commitment words,
  the domain words, or `E.delta`. -/

/-- Header word `i` of the payload image. `getD` past the end is the zero word, so a pin about a
    slot the payload does not have is false for every non-zero expected value. -/
def payloadWord (PV : PlanView) (i : Nat) : Word256 := (PV.vk.constants.getD i ("", 0)).2

/-- The 128-byte EIP-2537 image of one payload commitment: `x_hi ‖ x_lo ‖ y_hi ‖ y_lo`, the order
    `Halo2VerifyingKey.bytes` writes (`Models.lean:475-481`). -/
def g1WordsBytes (w : G1Words) : Bytes :=
  wordToBytesBE w.xHi ++ wordToBytesBE w.xLo ++ wordToBytesBE w.yHi ++ wordToBytesBE w.yLo

/-- **THE PAYLOAD AGREES WITH THE LEAN KEY.** One structure for every payload word the contract
    reads and every environment constant the generator emits as a literal. Slot numbers are
    `vkHeaderTemplateSlotsDefault`'s (`Models.lean:734`), never literals. `vkDigest` (slot 0) is
    NOT repeated here: it stays `EnvAgrees.vkDigestWord`. -/
structure PayloadAgrees (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- The object text's first field (card step 3): header word 0 is the Lean key's transcript
      representation. THE OVERLAP IS KEPT BECAUSE THE CARD NAMES THE FIELD: `EnvAgrees.vkDigestWord`
      (`Inv.lean:579`) states the same equation, and the 18-clause text omitted it here for that
      reason. It is redundant with `env`, not with `generated`. -/
  digest : payloadWord R.pv vkHeaderTemplateSlotsDefault.vkDigest =
    frWord R.vk.transcriptRepr
  /-- Justifies `eq(mload(NUM_INSTANCES_MPTR), <num_instances>)` in VkLoading (progress: the
      guard passes) - slot 1. -/
  numInstances : payloadWord R.pv vkHeaderTemplateSlotsDefault.numInstances =
    BitVec.ofNat 256 R.cfg.numInstances
  /-- Justifies `eq(mload(K_MPTR), <k>)` in VkLoading - slot 2. -/
  k : payloadWord R.pv vkHeaderTemplateSlotsDefault.k = BitVec.ofNat 256 R.vk.domain.k
  /-- Justifies `mload(N_INV_MPTR)` in Lagrange (`l_i_common := mulmod(x_n_minus_1, N_INV, r)`);
      Lean uses `barycentricWeight`, tied to this value by `EnvAgrees.baryWeight` - slot 3. -/
  nInv : payloadWord R.pv vkHeaderTemplateSlotsDefault.nInv =
    frWord ((((2 ^ R.vk.domain.k : ℕ) : Fr p))⁻¹)
  /-- Justifies `mload(OMEGA_MPTR)` in Lagrange (the `x - omega^i` walk) and in the PCS rotation
      points; Lean rotates by `vk.domain.omega` - slot 4. -/
  omega : payloadWord R.pv vkHeaderTemplateSlotsDefault.omega = frWord R.vk.domain.omega
  /-- Justifies `mload(OMEGA_INV_MPTR)` in the PCS rotation points (negative rotations) -
      slot 5. -/
  omegaInv : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInv =
    frWord R.vk.domain.omegaInv
  /-- Justifies `mload(OMEGA_INV_TO_L_MPTR)`, the start of both Lagrange loops:
      `omega_inv ^ |rotation_last|` (`Vk.lean:724-726`, VK:115-118) - slot 6. -/
  omegaInvToL : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInvToL =
    frWord (R.vk.domain.omegaInv ^ R.plan.meta_.rotationLast.natAbs)
  /-- Justifies the four `eq(mload(*ACC*_MPTR), <literal>)` guards in VkLoading: the header's
      accumulator quadruple is the configuration's (`accWordsOfEncoding`, `Inv.lean:259`) -
      slots 7-10. -/
  accWords :
    ((payloadWord R.pv vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (payloadWord R.pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
    accWordsOfEncoding R.cfg.accumulator
  /-- Justifies `mcopy(_, G1_BASE_MPTR, 0x80)` in the PCS final MSM (the `-v * G` term): the slot
      holds the encoding of the generator Lean's `DualMSM` uses (`P.g₁`). v1
      `VkSlotsAgree.g1BaseWords` - slot 11. -/
  g1Base : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip P.g₁
  /-- Justifies `mcopy(add(scratch, 0x80), G2_BASE_MPTR, 0x100)` in `ec_pairing`. v1
      `VkSlotsAgree.g2BaseWords` - slot 15. -/
  g2Base : vkG2Words R.pv vkG2BaseSlot = R.encG2 P.g₂
  /-- Justifies `mcopy(add(scratch, 0x200), NEG_S_G2_BASE_MPTR, 0x100)` in `ec_pairing`. v1
      `VkSlotsAgree.negSG2Words` - slot 23. -/
  negSG2 : vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 R.sG2gen⁻¹
  /-- Justifies every read of a fixed-commitment EcPoint in the PCS MSMs (the payload section
      after the header constants): the words are the EIP encoding of the Lean key's own
      commitments, in order. -/
  fixedComms : R.pv.vk.fixedComms.map g1WordsBytes =
    R.vk.fixedCommitments.toList.map R.E.g1.toEip
  /-- Same for the permutation (sigma) commitments, the last payload section. -/
  permutationComms : R.pv.vk.permutationComms.map g1WordsBytes =
    R.vk.permutation.commitments.toList.map R.E.g1.toEip
  /-- **D-GATE1 (PG-VKHEADER): the payload carries the eleven header constants.** Slots 0-10 are
      `vkHeaderTemplateSlotsDefault`; VkLoading S3-S8 reads slots 1 and 7-10 out of the memory the
      S2 `extcodecopy` wrote, and `PayloadAgrees`' word equations reach that memory only when the
      serialization's constant section covers them (`VkClean.wordFrom_foldl_chunks`). The eleven
      scalars are what `generateVk` writes (`headerWords := vk0.constants.length`); a payload with
      seven constants and no commitments is 224 bytes, so the copy ends before slot 7 and the
      header checks read unpinned memory. This is the minimal clause that makes the S3-S8 window
      reads follow (`VkClean.vk_hdr_word_read`). -/
  constantsLength : 11 ≤ R.pv.vk.constants.length
  /- **`delta` IS DROPPED (card step 3).** The 18-clause text pinned the emitted `frDelta` literal
      against `R.E.delta`; the single text does not, because `generated` already pins `R.E.delta`
      against the program: OBJ.7's gate 9 (`GeneratedKats.generateAll_falsifierDeltaAndOmega_ok`)
      measures that `delta := 2` changes the generated text AND the quotient blocks, so DELTA reaches
      the text through the generator and not through a payload equation - and `inputs.frDelta` alone is
      INERT at the deployment (`Artifacts.lean:129-135`: the one template site that interpolates it is
      inside the `when None` arm P-13c never renders; `Deploy.frDeltaIsGeneratorPow_ok` measures the literal's own value
      halves). The card's acceptance line - "`delta := 2` falsifies `generated` (not `payload`)" - is
      gate 9, and `Deploy.recon1_programOkB_ok` measures the bundle that reads the table. -/

/-- The decidable face of the seven fields that mention no codec and no group element: the header
    scalars (`digest` included) and the accumulator quadruple. `StatementsV3Deploy.lean` evaluates it. The
    five remaining fields (`g1Base`, `g2Base`, `negSG2`, `fixedComms`, `permutationComms`) compare
    payload bytes with `toEip` of group elements: each needs a codec fact (`toEip` is
    noncomputable at `g1CodecZ`) and, for the three base slots, a pairing whose generators are
    pinned (finding H-2). -/
def payloadScalarsB (PV : PlanView) (numInstances k : Nat) (omega omegaInv : Fr p)
    (rotationLast : Int) (acc : Option Midfall.Generator.AccumulatorEncoding) : List Bool :=
  let s := vkHeaderTemplateSlotsDefault
  [ payloadWord PV s.numInstances == BitVec.ofNat 256 numInstances,
    payloadWord PV s.k == BitVec.ofNat 256 k,
    payloadWord PV s.nInv == frWord ((((2 ^ k : ℕ) : Fr p))⁻¹),
    payloadWord PV s.omega == frWord omega,
    payloadWord PV s.omegaInv == frWord omegaInv,
    payloadWord PV s.omegaInvToL == frWord (omegaInv ^ rotationLast.natAbs),
    ((payloadWord PV s.hasAccumulator).toNat, (payloadWord PV s.accOffset).toNat,
      (payloadWord PV s.numAccLimbs).toNat, (payloadWord PV s.numAccLimbBits).toNat) ==
        accWordsOfEncoding acc ]

/-! ## §I. The exit discipline and TwoOutcomes (i)

  OLD (`Blocks.lean:356-363`): `rejects_of_not_accepts`, a sorried lemma with neither `SoundSide`
  nor `R.Valid`, concluding `obs.isRevertOrHalt` from `¬ LeanAccepts`. FALSE on the logup-panic
  set (the contract accepts there, `Inv.lean:698-706`) and false for every render whose
  `cfg.numInstances` is perturbed (finding A+1).

  NEW: conjunct 3 does not need any rejection lemma. Every run of the program either returns ABI
  `true` or is a non-committing halt, with the world unchanged, WHATEVER the Lean verifier says,
  for every call relation, every gas oracle and every start state. Three syntactic facts give it:
    1. `NoWriters` (already `Valid.noWriters`) - the world is unchanged;
    2. no `stop`, `selfdestruct` or `return` builtin occurs outside the designated tail, so the
       only halts the body can produce are `revert`, `invalid`, `invalidMemoryAccess`,
       `staticViolation` - all non-committing (`HaltKind.commits`);
    3. the program ends with `mstore(p, 1)  return(p, 0x20)` and has no `leave` outside a
       function nor `break`/`continue` outside a loop, so a run that does not halt earlier
       reaches that tail and returns `abiTrue`. -/

/-- The builtins that end the frame with a COMMITTING halt. -/
def isCommittingExit : EVM.Op → Bool
  | .stop | .ret | .selfdestruct => true
  | _ => false

/-- One layer of the exit scan, in the shape of `Bridge.noWritersStep` (`Bridge.lean:1069`), with
    two context bits: inside a function body (where `leave` is legal) and inside a loop body
    (where `break` / `continue` are). -/
def exitStep (inFun inLoop : Bool) : Scan → (Bool → Bool → Scan → Bool) → Bool
  | .e (.lit _), _ => true
  | .e (.var _), _ => true
  | .e (.builtin op args), rec => !isCommittingExit op && rec inFun inLoop (.es args)
  | .e (.call _ args), rec => rec inFun inLoop (.es args)
  | .es [], _ => true
  | .es (e :: rest), rec => rec inFun inLoop (.e e) && rec inFun inLoop (.es rest)
  | .s (.block body), rec => rec inFun inLoop (.b body)
  | .s (.funDef _ _ _ body), rec => rec true false (.b body)
  | .s (.letDecl _ none), _ => true
  | .s (.letDecl _ (some e)), rec => rec inFun inLoop (.e e)
  | .s (.assign _ e), rec => rec inFun inLoop (.e e)
  | .s (.cond c body), rec => rec inFun inLoop (.e c) && rec inFun inLoop (.b body)
  | .s (.switch c cases dflt), rec =>
      rec inFun inLoop (.e c) && rec inFun inLoop (.cs cases) &&
        (match dflt with | none => true | some d => rec inFun inLoop (.b d))
  | .s (.forLoop init c post body), rec =>
      rec inFun false (.b init) && rec inFun false (.e c) && rec inFun false (.b post) &&
        rec inFun true (.b body)
  | .s (.exprStmt e), rec => rec inFun inLoop (.e e)
  | .s .break, _ => inLoop
  | .s .continue, _ => inLoop
  | .s .leave, _ => inFun
  | .b [], _ => true
  | .b (s :: ss), rec => rec inFun inLoop (.s s) && rec inFun inLoop (.b ss)
  | .cs [], _ => true
  | .cs ((_, b) :: rest), rec => rec inFun inLoop (.b b) && rec inFun inLoop (.cs rest)

/-- Fuel-bounded scan; exhaustion answers `false` (R-37), as in `noWritersScan`. -/
def exitScan : Nat → Bool → Bool → Scan → Bool
  | 0, _, _, _ => false
  | n + 1, f, l, sc => exitStep f l sc (exitScan n)

/-- The program minus its designated tail `mstore(p, 1)  return(p, 0x20)`, when it has one. -/
def returnTail? (b : Block EVM.Op) : Option (Block EVM.Op) :=
  match b.reverse with
  | Stmt.exprStmt (Expr.builtin EVM.Op.ret
        [Expr.lit (Literal.number p₁), Expr.lit (Literal.number n)]) ::
      Stmt.exprStmt (Expr.builtin EVM.Op.mstore
        [Expr.lit (Literal.number p₂), Expr.lit (Literal.number v)]) :: initRev =>
      if p₁ = p₂ ∧ n = 32 ∧ v = 1 then some initRev.reverse else none
  | _ => none

/-- The whole check: the tail is there and nothing before it can commit or escape. -/
def exitDisciplineFuel (n : Nat) (b : Block EVM.Op) : Bool :=
  match returnTail? b with
  | some init => exitScan n false false (.b init)
  | none => false

/-- The only committing exit of the block is its final `return` of the word 1. -/
def ExitDiscipline (b : Block EVM.Op) : Prop := ∃ n, exitDisciplineFuel n b = true

/-- WITNESS: the shape `traceReturn` ends the program with passes. PROVED by `decide`. -/
theorem exitDiscipline_witness :
    ExitDiscipline (yul% {
      if iszero(calldataload(0)) { mstore(0, 7) revert(0, 4) }
      mstore(4096, 1)
      return(4096, 32) }) :=
  ⟨16, by decide⟩

/-- FALSIFIERS: an early `return`, a `stop`, a missing tail and a top-level `leave` are each
    refused at the fuel that accepts the witness. PROVED by `decide`. -/
theorem exitDiscipline_refuses :
    exitDisciplineFuel 16 (yul% { return(0, 32) mstore(4096, 1) return(4096, 32) }) = false ∧
    exitDisciplineFuel 16 (yul% { if calldataload(0) { stop() } mstore(4096, 1) return(4096, 32) })
      = false ∧
    exitDisciplineFuel 16 (yul% { mstore(4096, 1) }) = false ∧
    exitDisciplineFuel 16 (yul% { mstore(4096, 2) return(4096, 32) }) = false ∧
    exitDisciplineFuel 16 (yul% { leave mstore(4096, 1) return(4096, 32) }) = false := by
  decide

/-! ## §I.a The exit classification (the proof of `twoOutcomes_of_exitDiscipline`)

  THE INVARIANT. `exitScan` is a syntactic over-approximation of the halting behaviour of a block.
  This section turns it into a semantic judgement: `ExitCleanRes fu la st res` says that a `Step`
  result either leaves `halted` exactly as it was (and its outcome is `normal`, or `leave` when
  `fu`, or `break`/`continue` when `la`), or halts with a NON-COMMITTING `HaltKind` (revert,
  invalid, invalidMemoryAccess, staticViolation). `Step.exitClassified` is the induction on the
  derivation carrying `ExitScanCleanCode` for the code and `ExitCleanFuns` for the function
  environment; `exitScan`'s closure lemmas below hand every sub-derivation its scan.

  THE TWO REMAINING FACTS are about the designated tail `mstore(p, 1); return(p, 0x20)`:
  `Step.stmts_mstore_one_ret` computes the halt record (`readBytes_storeWord_one` is the 32-byte
  read-back of the word 1), and `returnTail?_spec` inverts the syntactic split so the final proof
  can use `Step.stmts_append_inv` at exactly that boundary. -/



def ExitScanClean (fu la : Bool) (sc : Scan) : Prop := ∃ n, exitScan n fu la sc = true

def ExitScanCleanCode (fu la : Bool) (code : Code EVM.Op) : Prop :=
  ExitScanClean fu la (codeScan code)

def ExitCleanFuns {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) : Prop :=
  ∀ scope ∈ funs, ∀ q ∈ scope, ExitScanClean true false (.b q.2.body)

theorem exitScan_mono_succ : ∀ (n : Nat) (fu la : Bool) (sc : Scan),
    exitScan n fu la sc = true → exitScan (n + 1) fu la sc = true := by
  intro n
  induction n with
  | zero => intro fu la sc h; simp [exitScan] at h
  | succ k ih =>
      intro fu la sc h
      change exitStep fu la sc (exitScan k) = true at h
      change exitStep fu la sc (exitScan (k + 1)) = true
      cases sc with
      | e e =>
          cases e with
          | lit l => exact h
          | var x => exact h
          | builtin op args =>
              simp only [exitStep, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
              exact ⟨h.1, ih fu la _ h.2⟩
          | call fn args =>
              simp only [exitStep] at h ⊢
              exact ih fu la _ h
      | es es =>
          cases es with
          | nil => exact h
          | cons e rest =>
              simp only [exitStep, Bool.and_eq_true] at h ⊢
              exact ⟨ih fu la _ h.1, ih fu la _ h.2⟩
      | s s =>
          cases s with
          | block body =>
              simp only [exitStep] at h ⊢
              exact ih fu la _ h
          | funDef n ps rs b =>
              simp only [exitStep] at h ⊢
              exact ih true false _ h
          | letDecl xs val =>
              cases val with
              | none => exact h
              | some e =>
                  simp only [exitStep] at h ⊢
                  exact ih fu la _ h
          | assign xs e =>
              simp only [exitStep] at h ⊢
              exact ih fu la _ h
          | cond cc body =>
              simp only [exitStep, Bool.and_eq_true] at h ⊢
              exact ⟨ih fu la _ h.1, ih fu la _ h.2⟩
          | «switch» cc cases dflt =>
              cases dflt with
              | none =>
                  simp only [exitStep, Bool.and_eq_true] at h ⊢
                  exact ⟨⟨ih fu la _ h.1.1, ih fu la _ h.1.2⟩, h.2⟩
              | some d =>
                  simp only [exitStep, Bool.and_eq_true] at h ⊢
                  exact ⟨⟨ih fu la _ h.1.1, ih fu la _ h.1.2⟩, ih fu la _ h.2⟩
          | forLoop init cc post body =>
              simp only [exitStep, Bool.and_eq_true] at h ⊢
              exact ⟨⟨⟨ih fu false _ h.1.1.1, ih fu false _ h.1.1.2⟩,
                ih fu false _ h.1.2⟩, ih fu true _ h.2⟩
          | exprStmt e =>
              simp only [exitStep] at h ⊢
              exact ih fu la _ h
          | «break» => exact h
          | «continue» => exact h
          | «leave» => exact h
      | b b =>
          cases b with
          | nil => exact h
          | cons s ss =>
              simp only [exitStep, Bool.and_eq_true] at h ⊢
              exact ⟨ih fu la _ h.1, ih fu la _ h.2⟩
      | cs cs =>
          cases cs with
          | nil => exact h
          | cons q rest =>
              simp only [exitStep, Bool.and_eq_true] at h ⊢
              exact ⟨ih fu la _ h.1, ih fu la _ h.2⟩

theorem exitScan_mono {n m : Nat} (h : n ≤ m) {fu la : Bool} {sc : Scan}
    (hn : exitScan n fu la sc = true) : exitScan m fu la sc = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simpa using hn
  | succ d ih =>
      simpa only [Nat.add_succ] using exitScan_mono_succ (n + d) fu la sc ih

/-! ## Closure (projections) -/

theorem exitScan_b_cons {fu la : Bool} {s : Stmt EVM.Op} {ss : Block EVM.Op}
    (h : ExitScanClean fu la (.b (s :: ss))) :
    ExitScanClean fu la (.s s) ∧ ExitScanClean fu la (.b ss) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k =>
      simp only [exitScan, exitStep, Bool.and_eq_true] at hn
      exact ⟨⟨k, hn.1⟩, ⟨k, hn.2⟩⟩

theorem exitScan_es_cons {fu la : Bool} {e : Expr EVM.Op} {es : List (Expr EVM.Op)}
    (h : ExitScanClean fu la (.es (e :: es))) :
    ExitScanClean fu la (.e e) ∧ ExitScanClean fu la (.es es) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k =>
      simp only [exitScan, exitStep, Bool.and_eq_true] at hn
      exact ⟨⟨k, hn.1⟩, ⟨k, hn.2⟩⟩

theorem exitScan_cs_cons {fu la : Bool} {q : Literal × Block EVM.Op}
    {rest : List (Literal × Block EVM.Op)}
    (h : ExitScanClean fu la (.cs (q :: rest))) :
    ExitScanClean fu la (.b q.2) ∧ ExitScanClean fu la (.cs rest) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k =>
      simp only [exitScan, exitStep, Bool.and_eq_true] at hn
      exact ⟨⟨k, hn.1⟩, ⟨k, hn.2⟩⟩

theorem exitScan_e_builtin {fu la : Bool} {op : EVM.Op} {args : List (Expr EVM.Op)}
    (h : ExitScanClean fu la (.e (.builtin op args))) :
    isCommittingExit op = false ∧ ExitScanClean fu la (.es args) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k =>
      simp only [exitScan, exitStep, Bool.and_eq_true, Bool.not_eq_true'] at hn
      exact ⟨hn.1, ⟨k, hn.2⟩⟩

theorem exitScan_e_call {fu la : Bool} {fn : Ident} {args : List (Expr EVM.Op)}
    (h : ExitScanClean fu la (.e (.call fn args))) :
    ExitScanClean fu la (.es args) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => exact ⟨k, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_block {fu la : Bool} {body : Block EVM.Op}
    (h : ExitScanClean fu la (.s (.block body))) : ExitScanClean fu la (.b body) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => exact ⟨k, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_funDef {fu la : Bool} {n : Ident} {ps rs : List Ident}
    {body : Block EVM.Op} (h : ExitScanClean fu la (.s (.funDef n ps rs body))) :
    ExitScanClean true false (.b body) := by
  obtain ⟨f, hf⟩ := h
  cases f with
  | zero => simp [exitScan] at hf
  | succ k => exact ⟨k, by simpa [exitScan, exitStep] using hf⟩

theorem exitScan_s_letDecl_some {fu la : Bool} {xs : List Ident} {e : Expr EVM.Op}
    (h : ExitScanClean fu la (.s (.letDecl xs (some e)))) :
    ExitScanClean fu la (.e e) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => exact ⟨k, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_assign {fu la : Bool} {xs : List Ident} {e : Expr EVM.Op}
    (h : ExitScanClean fu la (.s (.assign xs e))) : ExitScanClean fu la (.e e) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => exact ⟨k, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_exprStmt {fu la : Bool} {e : Expr EVM.Op}
    (h : ExitScanClean fu la (.s (.exprStmt e))) : ExitScanClean fu la (.e e) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => exact ⟨k, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_cond {fu la : Bool} {cc : Expr EVM.Op} {body : Block EVM.Op}
    (h : ExitScanClean fu la (.s (.cond cc body))) :
    ExitScanClean fu la (.e cc) ∧ ExitScanClean fu la (.b body) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k =>
      simp only [exitScan, exitStep, Bool.and_eq_true] at hn
      exact ⟨⟨k, hn.1⟩, ⟨k, hn.2⟩⟩

def ExitScanDflt (fu la : Bool) (dflt : Option (Block EVM.Op)) : Prop :=
  match dflt with | none => True | some d => ExitScanClean fu la (.b d)

theorem exitScan_s_switch {fu la : Bool} {cc : Expr EVM.Op}
    {cases : List (Literal × Block EVM.Op)} {dflt : Option (Block EVM.Op)}
    (h : ExitScanClean fu la (.s (.switch cc cases dflt))) :
    ExitScanClean fu la (.e cc) ∧ ExitScanClean fu la (.cs cases) ∧
      ExitScanDflt fu la dflt := by
  revert h
  cases dflt with
  | none =>
      intro h
      obtain ⟨n, hn⟩ := h
      cases n with
      | zero => simp [exitScan] at hn
      | succ k =>
          simp only [exitScan, exitStep, Bool.and_eq_true] at hn
          exact ⟨⟨k, hn.1.1⟩, ⟨k, hn.1.2⟩, trivial⟩
  | some d =>
      intro h
      obtain ⟨n, hn⟩ := h
      cases n with
      | zero => simp [exitScan] at hn
      | succ k =>
          simp only [exitScan, exitStep, Bool.and_eq_true] at hn
          exact ⟨⟨k, hn.1.1⟩, ⟨k, hn.1.2⟩, ⟨k, hn.2⟩⟩

theorem exitScan_s_forLoop {fu la : Bool} {init : Block EVM.Op} {cc : Expr EVM.Op}
    {post body : Block EVM.Op}
    (h : ExitScanClean fu la (.s (.forLoop init cc post body))) :
    ExitScanClean fu false (.b init) ∧ ExitScanClean fu false (.e cc) ∧
      ExitScanClean fu false (.b post) ∧ ExitScanClean fu true (.b body) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k =>
      simp only [exitScan, exitStep, Bool.and_eq_true] at hn
      exact ⟨⟨k, hn.1.1.1⟩, ⟨k, hn.1.1.2⟩, ⟨k, hn.1.2⟩, ⟨k, hn.2⟩⟩

theorem exitScan_s_break {fu la : Bool} (h : ExitScanClean fu la (.s .«break»)) : la = true := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => simpa [exitScan, exitStep] using hn

theorem exitScan_s_continue {fu la : Bool} (h : ExitScanClean fu la (.s .«continue»)) :
    la = true := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => simpa [exitScan, exitStep] using hn

theorem exitScan_s_leave {fu la : Bool} (h : ExitScanClean fu la (.s .«leave»)) : fu = true := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [exitScan] at hn
  | succ k => simpa [exitScan, exitStep] using hn

/-! ## Reverse closure -/

theorem exitScanClean_nil {fu la : Bool} : ExitScanClean fu la (.b ([] : Block EVM.Op)) :=
  ⟨1, rfl⟩

theorem exitScanClean_and {fu la : Bool} {sc₁ sc₂ : Scan}
    (h₁ : ExitScanClean fu la sc₁) (h₂ : ExitScanClean fu la sc₂) :
    ∃ n, exitScan n fu la sc₁ = true ∧ exitScan n fu la sc₂ = true := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨max n₁ n₂, exitScan_mono (Nat.le_max_left _ _) hn₁,
    exitScan_mono (Nat.le_max_right _ _) hn₂⟩

theorem exitScan_s_block_rev {fu la : Bool} {body : Block EVM.Op}
    (h : ExitScanClean fu la (.b body)) : ExitScanClean fu la (.s (.block body)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_b_cons_rev {fu la : Bool} {s : Stmt EVM.Op} {ss : Block EVM.Op}
    (hs : ExitScanClean fu la (.s s)) (hss : ExitScanClean fu la (.b ss)) :
    ExitScanClean fu la (.b (s :: ss)) := by
  obtain ⟨n, hn1, hn2⟩ := exitScanClean_and hs hss
  exact ⟨n + 1, by simp only [exitScan, exitStep, hn1, hn2, Bool.and_true]⟩

theorem exitScan_es_cons_rev {fu la : Bool} {e : Expr EVM.Op} {es : List (Expr EVM.Op)}
    (he : ExitScanClean fu la (.e e)) (hes : ExitScanClean fu la (.es es)) :
    ExitScanClean fu la (.es (e :: es)) := by
  obtain ⟨n, hn1, hn2⟩ := exitScanClean_and he hes
  exact ⟨n + 1, by simp only [exitScan, exitStep, hn1, hn2, Bool.and_true]⟩

theorem exitScan_cs_cons_rev {fu la : Bool} {q : Literal × Block EVM.Op}
    {rest : List (Literal × Block EVM.Op)}
    (hb : ExitScanClean fu la (.b q.2)) (hrest : ExitScanClean fu la (.cs rest)) :
    ExitScanClean fu la (.cs (q :: rest)) := by
  obtain ⟨n, hn1, hn2⟩ := exitScanClean_and hb hrest
  exact ⟨n + 1, by simp only [exitScan, exitStep, hn1, hn2, Bool.and_true]⟩

theorem exitScan_e_builtin_rev {fu la : Bool} {op : EVM.Op} {args : List (Expr EVM.Op)}
    (hw : isCommittingExit op = false) (hargs : ExitScanClean fu la (.es args)) :
    ExitScanClean fu la (.e (.builtin op args)) := by
  obtain ⟨n, hn⟩ := hargs
  exact ⟨n + 1, by simp only [exitScan, exitStep, hw, Bool.not_false, Bool.true_and]; exact hn⟩

theorem exitScan_e_call_rev {fu la : Bool} {fn : Ident} {args : List (Expr EVM.Op)}
    (hargs : ExitScanClean fu la (.es args)) : ExitScanClean fu la (.e (.call fn args)) := by
  obtain ⟨n, hn⟩ := hargs
  exact ⟨n + 1, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_letDecl_some_rev {fu la : Bool} {xs : List Ident} {e : Expr EVM.Op}
    (h : ExitScanClean fu la (.e e)) : ExitScanClean fu la (.s (.letDecl xs (some e))) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_assign_rev {fu la : Bool} {xs : List Ident} {e : Expr EVM.Op}
    (h : ExitScanClean fu la (.e e)) : ExitScanClean fu la (.s (.assign xs e)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_exprStmt_rev {fu la : Bool} {e : Expr EVM.Op}
    (h : ExitScanClean fu la (.e e)) : ExitScanClean fu la (.s (.exprStmt e)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simpa [exitScan, exitStep] using hn⟩

theorem exitScan_s_cond_rev {fu la : Bool} {cc : Expr EVM.Op} {body : Block EVM.Op}
    (hc : ExitScanClean fu la (.e cc)) (hb : ExitScanClean fu la (.b body)) :
    ExitScanClean fu la (.s (.cond cc body)) := by
  obtain ⟨n, hn1, hn2⟩ := exitScanClean_and hc hb
  exact ⟨n + 1, by simp only [exitScan, exitStep, hn1, hn2, Bool.and_true]⟩

theorem exitScan_s_forLoop_rev {fu la : Bool} {init : Block EVM.Op} {cc : Expr EVM.Op}
    {post body : Block EVM.Op} (hi : ExitScanClean fu false (.b init))
    (hc : ExitScanClean fu false (.e cc)) (hp : ExitScanClean fu false (.b post))
    (hb : ExitScanClean fu true (.b body)) :
    ExitScanClean fu la (.s (.forLoop init cc post body)) := by
  obtain ⟨n1, h1⟩ := hi
  obtain ⟨n2, h2⟩ := hc
  obtain ⟨n3, h3⟩ := hp
  obtain ⟨n4, h4⟩ := hb
  refine ⟨max (max (max n1 n2) n3) n4 + 1, ?_⟩
  have h1' : exitScan (max (max (max n1 n2) n3) n4) fu false (.b init) = true :=
    exitScan_mono (le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _)
      (Nat.le_max_left _ _))) h1
  have h2' : exitScan (max (max (max n1 n2) n3) n4) fu false (.e cc) = true :=
    exitScan_mono (le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _)
      (Nat.le_max_left _ _))) h2
  have h3' : exitScan (max (max (max n1 n2) n3) n4) fu false (.b post) = true :=
    exitScan_mono (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) h3
  have h4' : exitScan (max (max (max n1 n2) n3) n4) fu true (.b body) = true :=
    exitScan_mono (Nat.le_max_right _ _) h4
  simp only [exitScan, exitStep, h1', h2', h3', h4', Bool.and_true]

theorem exitScan_s_switch_rev_none {fu la : Bool} {cc : Expr EVM.Op}
    {cases : List (Literal × Block EVM.Op)}
    (hc : ExitScanClean fu la (.e cc)) (hcs : ExitScanClean fu la (.cs cases)) :
    ExitScanClean fu la (.s (.switch cc cases none)) := by
  obtain ⟨n, hn1, hn2⟩ := exitScanClean_and hc hcs
  exact ⟨n + 1, by simp only [exitScan, exitStep, hn1, hn2, Bool.and_true]⟩

theorem exitScan_s_switch_rev_some {fu la : Bool} {cc : Expr EVM.Op}
    {cases : List (Literal × Block EVM.Op)} {d : Block EVM.Op}
    (hc : ExitScanClean fu la (.e cc)) (hcs : ExitScanClean fu la (.cs cases))
    (hd : ExitScanClean fu la (.b d)) :
    ExitScanClean fu la (.s (.switch cc cases (some d))) := by
  obtain ⟨n12, hn1, hn2⟩ := exitScanClean_and hc hcs
  obtain ⟨n3, hn3⟩ := hd
  refine ⟨max n12 n3 + 1, ?_⟩
  have hn1' : exitScan (max n12 n3) fu la (.e cc) = true :=
    exitScan_mono (Nat.le_max_left _ _) hn1
  have hn2' : exitScan (max n12 n3) fu la (.cs cases) = true :=
    exitScan_mono (Nat.le_max_left _ _) hn2
  have hn3' : exitScan (max n12 n3) fu la (.b d) = true :=
    exitScan_mono (Nat.le_max_right _ _) hn3
  simp only [exitScan, exitStep, hn1', hn2', hn3', Bool.and_true]

theorem exitScan_s_switch_rev {fu la : Bool} {cc : Expr EVM.Op}
    {cases : List (Literal × Block EVM.Op)} {dflt : Option (Block EVM.Op)}
    (hc : ExitScanClean fu la (.e cc)) (hcs : ExitScanClean fu la (.cs cases))
    (hd : ExitScanDflt fu la dflt) :
    ExitScanClean fu la (.s (.switch cc cases dflt)) := by
  revert hd
  cases dflt with
  | none => intro _; exact exitScan_s_switch_rev_none hc hcs
  | some d => intro hd; exact exitScan_s_switch_rev_some hc hcs hd

theorem exitScan_loop_rev {fu la : Bool} {cc : Expr EVM.Op} {post body : Block EVM.Op}
    (hc : ExitScanClean fu false (.e cc)) (hp : ExitScanClean fu false (.b post))
    (hb : ExitScanClean fu true (.b body)) :
    ExitScanClean fu la (.s (.forLoop [] cc post body)) :=
  exitScan_s_forLoop_rev exitScanClean_nil hc hp hb

/-! ## Subterm / environment facts -/

theorem exitScan_b_mem {s : Stmt EVM.Op} :
    ∀ {ss : Block EVM.Op}, s ∈ ss → ExitScanClean false false (.b ss) →
      ExitScanClean false false (.s s) := by
  intro ss
  induction ss with
  | nil => intro hmem _; simp at hmem
  | cons a as ih =>
      intro hmem h
      rw [List.mem_cons] at hmem
      obtain ⟨ha, has⟩ := exitScan_b_cons h
      rcases hmem with rfl | hmem
      · exact ha
      · exact ih hmem has

theorem exitScan_b_mem_fun {fu la : Bool} {s : Stmt EVM.Op} :
    ∀ {ss : Block EVM.Op}, s ∈ ss → ExitScanClean fu la (.b ss) →
      ExitScanClean fu la (.s s) := by
  intro ss
  induction ss with
  | nil => intro hmem _; simp at hmem
  | cons a as ih =>
      intro hmem h
      rw [List.mem_cons] at hmem
      obtain ⟨ha, has⟩ := exitScan_b_cons h
      rcases hmem with rfl | hmem
      · exact ha
      · exact ih hmem has

theorem exitScan_hoist {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {body : Block EVM.Op} (h : ExitScanClean fu la (.b body)) :
    ∀ q ∈ hoist (Bridge.Dialect c g) body, ExitScanClean true false (.b q.2.body) := by
  intro q hq
  simp only [hoist, List.mem_filterMap] at hq
  obtain ⟨s, hs, hsq⟩ := hq
  have hss := exitScan_b_mem_fun hs h
  cases s with
  | block body => simp at hsq
  | funDef n ps rs b =>
      simp only [Option.some.injEq] at hsq
      subst hsq
      exact exitScan_s_funDef hss
  | letDecl vars val => simp at hsq
  | assign vars val => simp at hsq
  | cond cc body => simp at hsq
  | «switch» cc cs dflt => simp at hsq
  | forLoop init cc post body => simp at hsq
  | exprStmt e => simp at hsq
  | «break» => simp at hsq
  | «continue» => simp at hsq
  | «leave» => simp at hsq

theorem exitCleanFuns_nil {c : ExternalCalls} {g : ExternalGas} :
    ExitCleanFuns ([] : FunEnv (Bridge.Dialect c g)) := by
  intro scope hscope
  simp at hscope

theorem exitCleanFuns_hoist {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {body : Block EVM.Op} (hb : ExitScanClean fu la (.b body))
    {funs : FunEnv (Bridge.Dialect c g)} (hf : ExitCleanFuns funs) :
    ExitCleanFuns (hoist (Bridge.Dialect c g) body :: funs) := by
  intro scope hscope q hq
  rw [List.mem_cons] at hscope
  rcases hscope with rfl | hscope
  · exact exitScan_hoist hb q hq
  · exact hf scope hscope q hq

theorem lookupFun_exitClean {c : ExternalCalls} {g : ExternalGas} :
    ∀ {funs : FunEnv (Bridge.Dialect c g)} {fn : Ident} {decl : FDecl (Bridge.Dialect c g)}
      {cenv : FunEnv (Bridge.Dialect c g)},
    ExitCleanFuns funs → lookupFun funs fn = some (decl, cenv) →
      ExitCleanFuns cenv ∧ ExitScanClean true false (.b decl.body) := by
  intro funs
  induction funs with
  | nil => intro fn decl cenv hf h; simp [lookupFun] at h
  | cons scope rest ih =>
      intro fn decl cenv hf h
      simp only [lookupFun] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hdecl, hcenv⟩ := h
        subst hcenv
        refine ⟨?_, ?_⟩
        · intro sc hsc r hr
          rw [List.mem_cons] at hsc
          rcases hsc with rfl | hsc
          · exact hf sc (by simp) r hr
          · exact hf sc (by simp [hsc]) r hr
        · simpa [hdecl] using hf scope (by simp) q (List.mem_of_find?_eq_some hq)
      · exact ih (fun sc hs => hf sc (by simp [hs])) h

theorem exitScan_cs_mem {fu la : Bool} {q : Literal × Block EVM.Op} :
    ∀ {cs : List (Literal × Block EVM.Op)}, q ∈ cs → ExitScanClean fu la (.cs cs) →
      ExitScanClean fu la (.b q.2) := by
  intro cs
  induction cs with
  | nil => intro hmem _; simp at hmem
  | cons a as ih =>
      intro hmem h
      rw [List.mem_cons] at hmem
      obtain ⟨ha, has⟩ := exitScan_cs_cons h
      rcases hmem with rfl | hmem
      · exact ha
      · exact ih hmem has

theorem exitScan_selectSwitch {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {cv : U256} {cases : List (Literal × Block EVM.Op)} {dflt : Option (Block EVM.Op)}
    (hcs : ExitScanClean fu la (.cs cases)) (hd : ExitScanDflt fu la dflt) :
    ExitScanClean fu la (.b (selectSwitch (Bridge.Dialect c g) cv cases dflt)) := by
  revert hd
  unfold selectSwitch
  cases hfind : List.find? (fun q : Literal × Block EVM.Op =>
      decide (cv = (Bridge.Dialect c g).litValue q.1)) cases with
  | some q =>
      intro _
      exact exitScan_cs_mem (List.mem_of_find?_eq_some hfind) hcs
  | none =>
      cases dflt with
      | none => intro _; exact exitScanClean_nil
      | some d => intro hd; exact hd

/-! ## Builtin halted behaviour -/

theorem finishCall_halted (kind : EVM.CallKind) (st : EvmState) (response : CallResponse)
    (io is oo os : Nat) : (finishCall kind st response io is oo os).halted = st.halted := by
  unfold finishCall
  split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCreate_halted (st : EvmState) (response : CreateResponse) (off size : Nat) :
    (finishCreate st response off size).halted = st.halted := by
  unfold finishCreate
  split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem stepOp_ok_halted {op : EVM.Op} {args : List U256} {st : EvmState}
    {rets : List U256} {st' : EvmState} (hr : stepOp op args st = some (.ok rets st')) :
    st'.halted = st.halted := by
  unfold stepOp at hr
  simp only [bin, un, ter, rd0, rd1, guardStatic] at hr
  repeat' (split at hr <;> try simp at hr)
  all_goals (try (obtain ⟨-, rfl⟩ := hr; rfl))
  all_goals (try (subst hr; rfl))
  all_goals (try (rw [hr]))

theorem stepOp_halt_noncommitting {op : EVM.Op} (h : isCommittingExit op = false)
    {args : List U256} {st st' : EvmState} (hr : stepOp op args st = some (.halt st')) :
    ∃ k d, st'.halted = some (k, d) ∧ k.commits = false := by
  unfold stepOp at hr
  simp only [bin, un, ter, rd0, rd1, guardStatic] at hr
  repeat' (split at hr <;> try simp at hr)
  all_goals (try (unfold isCommittingExit at h; cases h))
  all_goals (try (cases hr; first
    | exact ⟨.revert, _, rfl, rfl⟩
    | exact ⟨.invalid, _, rfl, rfl⟩
    | exact ⟨.invalidMemoryAccess, _, rfl, rfl⟩
    | exact ⟨.staticViolation, _, rfl, rfl⟩))

theorem builtin_ok_halted {c : ExternalCalls} {g : ExternalGas} {op : EVM.Op}
    {args : List U256} {st : EvmState} {rets : List U256} {st' : EvmState}
    (hb : (Bridge.Dialect c g).Builtin op args st (.ok rets st')) :
    st'.halted = st.halted := by
  change builtinWithExternal c ExternalCreates.none g op args st (.ok rets st') at hb
  cases op with
  | call =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨v, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x8, xs⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      by_cases hstat : st.env.static = true ∧ v ≠ 0
      · rw [ite_eq_left hstat] at hb
        cases hb
      · rw [ite_eq_right hstat] at hb
        obtain ⟨resp, _, hres⟩ := hb
        cases hres
        exact finishCall_halted _ _ _ _ _ _ _
  | callcode =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨v, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x8, xs⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨resp, _, hres⟩ := hb
      cases hres
      exact finishCall_halted _ _ _ _ _ _ _
  | delegatecall =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x7, xs⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨resp, _, hres⟩ := hb
      cases hres
      exact finishCall_halted _ _ _ _ _ _ _
  | staticcall =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x7, xs⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨resp, _, hres⟩ := hb
      cases hres
      exact finishCall_halted _ _ _ _ _ _ _
  | create =>
      rcases args with _ | ⟨v, _ | ⟨off, _ | ⟨sz, _ | ⟨x4, xs⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      by_cases hstat : st.env.static = true
      · rw [ite_eq_left hstat] at hb
        cases hb
      · rw [ite_eq_right hstat] at hb
        obtain ⟨resp, _, hres⟩ := hb
        cases hres
        exact finishCreate_halted _ _ _ _
  | create2 =>
      rcases args with _ | ⟨v, _ | ⟨off, _ | ⟨sz, _ | ⟨salt, _ | ⟨x5, xs⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      by_cases hstat : st.env.static = true
      · rw [ite_eq_left hstat] at hb
        cases hb
      · rw [ite_eq_right hstat] at hb
        obtain ⟨resp, _, hres⟩ := hb
        cases hres
        exact finishCreate_halted _ _ _ _
  | gas =>
      rcases args with _ | ⟨a, as⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨w, _, hres⟩ := hb
      cases hres
      rfl
  | _ => exact stepOp_ok_halted hb

theorem builtin_halt_noncommitting {c : ExternalCalls} {g : ExternalGas} {op : EVM.Op}
    (h : isCommittingExit op = false) {args : List U256} {st st' : EvmState}
    (hb : (Bridge.Dialect c g).Builtin op args st (.halt st')) :
    ∃ k d, st'.halted = some (k, d) ∧ k.commits = false := by
  change builtinWithExternal c ExternalCreates.none g op args st (.halt st') at hb
  cases op with
  | call =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨v, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x8, xs⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      by_cases hstat : st.env.static = true ∧ v ≠ 0
      · rw [ite_eq_left hstat] at hb
        cases hb
        exact ⟨.staticViolation, [], rfl, rfl⟩
      · rw [ite_eq_right hstat] at hb
        obtain ⟨resp, _, hres⟩ := hb
        cases hres
  | callcode =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨v, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x8, xs⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨resp, _, hres⟩ := hb
      cases hres
  | delegatecall =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x7, xs⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨resp, _, hres⟩ := hb
      cases hres
  | staticcall =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨io, _ | ⟨is, _ | ⟨oo, _ | ⟨os, _ | ⟨x7, xs⟩⟩⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨resp, _, hres⟩ := hb
      cases hres
  | create =>
      rcases args with _ | ⟨v, _ | ⟨off, _ | ⟨sz, _ | ⟨x4, xs⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      by_cases hstat : st.env.static = true
      · rw [ite_eq_left hstat] at hb
        cases hb
        exact ⟨.staticViolation, [], rfl, rfl⟩
      · rw [ite_eq_right hstat] at hb
        obtain ⟨resp, _, hres⟩ := hb
        cases hres
  | create2 =>
      rcases args with _ | ⟨v, _ | ⟨off, _ | ⟨sz, _ | ⟨salt, _ | ⟨x5, xs⟩⟩⟩⟩⟩
      all_goals simp only [builtinWithExternal] at hb
      by_cases hstat : st.env.static = true
      · rw [ite_eq_left hstat] at hb
        cases hb
        exact ⟨.staticViolation, [], rfl, rfl⟩
      · rw [ite_eq_right hstat] at hb
        obtain ⟨resp, _, hres⟩ := hb
        cases hres
  | gas =>
      rcases args with _ | ⟨a, as⟩
      all_goals simp only [builtinWithExternal] at hb
      obtain ⟨w, _, hres⟩ := hb
      cases hres
  | _ => exact stepOp_halt_noncommitting h hb


/-! ## The exit-classification invariant -/

def ExitCleanRes {c : ExternalCalls} {g : ExternalGas} (fu la : Bool) (st : EvmState) :
    Res (Bridge.Dialect c g) → Prop
  | .eres (.vals _ st') => st'.halted = st.halted
  | .eres (.halt st') => ∃ k d, st'.halted = some (k, d) ∧ k.commits = false
  | .sres _ st' o =>
      (st'.halted = st.halted ∧
        (o = .normal ∨ (fu = true ∧ o = .leave) ∨
          (la = true ∧ (o = .«break» ∨ o = .«continue»)))) ∨
      (o = .halt ∧ ∃ k d, st'.halted = some (k, d) ∧ k.commits = false)

theorem ExitCleanRes.sres_normal {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExitCleanRes fu la st (.sres V' st' o)) (ho : o = .normal) :
    st'.halted = st.halted := by
  rcases h with ⟨hh, _⟩ | ⟨h, _⟩
  · exact hh
  · subst ho; cases h

theorem ExitCleanRes.sres_halt {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    (h : ExitCleanRes fu la st (.sres V' st' .halt)) :
    ∃ k d, st'.halted = some (k, d) ∧ k.commits = false := by
  rcases h with ⟨_, ho⟩ | ⟨_, hk⟩
  · rcases ho with h | ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · cases h
    · rcases h with h | h <;> cases h
  · exact hk

theorem ExitCleanRes.sres_normal_or_continue {c : ExternalCalls} {g : ExternalGas}
    {fu la : Bool} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    {ob : Outcome} (h : ExitCleanRes fu la st (.sres V' st' ob))
    (hob : ob = .normal ∨ ob = .«continue») : st'.halted = st.halted := by
  rcases h with ⟨hh, _⟩ | ⟨ho, _⟩
  · exact hh
  · rcases hob with h' | h' <;> (subst h'; cases ho)

theorem ExitCleanRes.sres_break {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    (h : ExitCleanRes fu la st (.sres V' st' .«break»)) :
    st'.halted = st.halted := by
  rcases h with ⟨hh, _⟩ | ⟨ho, _⟩
  · exact hh
  · cases ho

theorem ExitCleanRes.sres_leave {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    (h : ExitCleanRes fu la st (.sres V' st' .leave)) :
    st'.halted = st.halted ∧ fu = true := by
  rcases h with ⟨hh, ho⟩ | ⟨ho, _⟩
  · rcases ho with h | ⟨hfu, h⟩ | ⟨_, h⟩
    · cases h
    · exact ⟨hh, hfu⟩
    · rcases h with h | h <;> cases h
  · cases ho

theorem ExitCleanRes.trans_sres {c : ExternalCalls} {g : ExternalGas} {fu la : Bool}
    {st st1 : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h1 : st1.halted = st.halted)
    (h2 : ExitCleanRes fu la st1 (.sres V' st' o)) :
    ExitCleanRes fu la st (.sres V' st' o) := by
  rcases h2 with ⟨hh, ho⟩ | ⟨ho, hk⟩
  · exact Or.inl ⟨hh.trans h1, ho⟩
  · exact Or.inr ⟨ho, hk⟩

theorem Step.exitClassified :
    ∀ {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (Bridge.Dialect c g)}
      {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {code : Code EVM.Op}
      {res : Res (Bridge.Dialect c g)},
      Step (Bridge.Dialect c g) funs V st code res →
      ∀ (fu la : Bool), ExitCleanFuns funs →
        ExitScanCleanCode fu la code → ExitCleanRes fu la st res := by
  intro c g funs V st code res h
  induction h with
  | lit => intro fu la hf hc; rfl
  | var hget => intro fu la hf hc; rfl
  | builtinOk hargs hb ihargs =>
      intro fu la hf hc
      exact (builtin_ok_halted hb).trans (ihargs fu la hf (exitScan_e_builtin hc).2)
  | builtinHalt hargs hb ihargs =>
      intro fu la hf hc
      exact builtin_halt_noncommitting (exitScan_e_builtin hc).1 hb
  | builtinArgsHalt hargs ihargs =>
      intro fu la hf hc
      exact ihargs fu la hf (exitScan_e_builtin hc).2
  | callOk hargs hlookup hlen hbody hout ihargs ihbody =>
      intro fu la hf hc
      obtain ⟨hcenv, hbodyClean⟩ := lookupFun_exitClean hf hlookup
      have h1 := ihargs fu la hf (exitScan_e_call hc)
      rcases ihbody true false hcenv (exitScan_s_block_rev hbodyClean) with
        ⟨hh, _⟩ | ⟨ho, _⟩
      · exact hh.trans h1
      · rcases hout with h | h <;> (subst h; cases ho)
  | callHalt hargs hlookup hlen hbody ihargs ihbody =>
      intro fu la hf hc
      obtain ⟨hcenv, hbodyClean⟩ := lookupFun_exitClean hf hlookup
      exact ExitCleanRes.sres_halt
        (ihbody true false hcenv (exitScan_s_block_rev hbodyClean))
  | callArgsHalt hargs ihargs =>
      intro fu la hf hc
      exact ihargs fu la hf (exitScan_e_call hc)
  | argsNil => intro fu la hf hc; rfl
  | argsCons hrest hhead ihrest ihhead =>
      intro fu la hf hc
      obtain ⟨hheadC, hrestC⟩ := exitScan_es_cons hc
      exact (ihhead fu la hf hheadC).trans (ihrest fu la hf hrestC)
  | argsRestHalt hrest ihrest =>
      intro fu la hf hc
      exact ihrest fu la hf (exitScan_es_cons hc).2
  | argsHeadHalt hrest hhead ihrest ihhead =>
      intro fu la hf hc
      exact ihhead fu la hf (exitScan_es_cons hc).1
  | funDef => intro fu la hf hc; exact Or.inl ⟨rfl, Or.inl rfl⟩
  | block hbody ihbody =>
      intro fu la hf hc
      exact ihbody fu la (exitCleanFuns_hoist (exitScan_s_block hc) hf)
        (exitScan_s_block hc)
  | letZero => intro fu la hf hc; exact Or.inl ⟨rfl, Or.inl rfl⟩
  | letVal hbody hlen ihbody =>
      intro fu la hf hc
      exact Or.inl ⟨ihbody fu la hf (exitScan_s_letDecl_some hc), Or.inl rfl⟩
  | letHalt hbody ihbody =>
      intro fu la hf hc
      exact Or.inr ⟨rfl, ihbody fu la hf (exitScan_s_letDecl_some hc)⟩
  | assignVal hbody hlen ihbody =>
      intro fu la hf hc
      exact Or.inl ⟨ihbody fu la hf (exitScan_s_assign hc), Or.inl rfl⟩
  | assignHalt hbody ihbody =>
      intro fu la hf hc
      exact Or.inr ⟨rfl, ihbody fu la hf (exitScan_s_assign hc)⟩
  | exprStmt hbody ihbody =>
      intro fu la hf hc
      exact Or.inl ⟨ihbody fu la hf (exitScan_s_exprStmt hc), Or.inl rfl⟩
  | exprStmtHalt hbody ihbody =>
      intro fu la hf hc
      exact Or.inr ⟨rfl, ihbody fu la hf (exitScan_s_exprStmt hc)⟩
  | ifTrue hcond hne hbody ihcond ihbody =>
      intro fu la hf hc
      obtain ⟨hcC, hbodyC⟩ := exitScan_s_cond hc
      exact ExitCleanRes.trans_sres (ihcond fu la hf hcC)
        (ihbody fu la hf (exitScan_s_block_rev hbodyC))
  | ifFalse hcond hzero ihcond =>
      intro fu la hf hc
      exact Or.inl ⟨ihcond fu la hf (exitScan_s_cond hc).1, Or.inl rfl⟩
  | ifHalt hcond ihcond =>
      intro fu la hf hc
      exact Or.inr ⟨rfl, ihcond fu la hf (exitScan_s_cond hc).1⟩
  | switchExec hcond hbody ihcond ihbody =>
      intro fu la hf hc
      obtain ⟨hcC, hcsC, hdC⟩ := exitScan_s_switch hc
      exact ExitCleanRes.trans_sres (ihcond fu la hf hcC)
        (ihbody fu la hf (exitScan_s_block_rev (exitScan_selectSwitch hcsC hdC)))
  | switchHalt hcond ihcond =>
      intro fu la hf hc
      exact Or.inr ⟨rfl, ihcond fu la hf (exitScan_s_switch hc).1⟩
  | forLoop hinit hloop ihinit ihloop =>
      intro fu la hf hc
      obtain ⟨hinitC, hcC, hpostC, hbodyC⟩ := exitScan_s_forLoop hc
      have hf' := exitCleanFuns_hoist hinitC hf
      have hh1 := ExitCleanRes.sres_normal (ihinit fu false hf' hinitC) rfl
      exact ExitCleanRes.trans_sres hh1
        (ihloop fu la hf' (exitScan_loop_rev hcC hpostC hbodyC))
  | forInitHalt hinit ihinit =>
      intro fu la hf hc
      obtain ⟨hinitC, _, _, _⟩ := exitScan_s_forLoop hc
      exact Or.inr ⟨rfl, ExitCleanRes.sres_halt
        (ihinit fu false (exitCleanFuns_hoist hinitC hf) hinitC)⟩
  | «break» =>
      intro fu la hf hc
      exact Or.inl ⟨rfl, Or.inr (Or.inr ⟨exitScan_s_break hc, Or.inl rfl⟩)⟩
  | «continue» =>
      intro fu la hf hc
      exact Or.inl ⟨rfl, Or.inr (Or.inr ⟨exitScan_s_continue hc, Or.inr rfl⟩)⟩
  | «leave» =>
      intro fu la hf hc
      exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨exitScan_s_leave hc, rfl⟩)⟩
  | seqNil => intro fu la hf hc; exact Or.inl ⟨rfl, Or.inl rfl⟩
  | seqCons hs hrest ihs ihrest =>
      intro fu la hf hc
      obtain ⟨hsC, hrestC⟩ := exitScan_b_cons hc
      exact ExitCleanRes.trans_sres (ExitCleanRes.sres_normal (ihs fu la hf hsC) rfl)
        (ihrest fu la hf hrestC)
  | seqStop hs hne ihs =>
      intro fu la hf hc
      exact ihs fu la hf (exitScan_b_cons hc).1
  | loopDone hcond hzero ihcond =>
      intro fu la hf hc
      exact Or.inl ⟨ihcond fu false hf (exitScan_s_forLoop hc).2.1, Or.inl rfl⟩
  | loopCondHalt hcond ihcond =>
      intro fu la hf hc
      exact Or.inr ⟨rfl, ihcond fu false hf (exitScan_s_forLoop hc).2.1⟩
  | loopStep hcond hne hbody hob hpost hpostnorm ihcond ihbody ihpost ihloop =>
      intro fu la hf hc
      obtain ⟨_, hcC, hpostC, hbodyC⟩ := exitScan_s_forLoop hc
      have hh1 := ihcond fu false hf hcC
      have hh2 := ExitCleanRes.sres_normal_or_continue
        (ihbody fu true hf (exitScan_s_block_rev hbodyC)) hob
      have hh3 := ExitCleanRes.sres_normal (ihpost fu false hf (exitScan_s_block_rev hpostC)) rfl
      exact ExitCleanRes.trans_sres (hh3.trans (hh2.trans hh1))
        (ihloop fu la hf (exitScan_loop_rev hcC hpostC hbodyC))
  | loopPostHalt hcond hne hbody hob hpost ihcond ihbody ihpost =>
      intro fu la hf hc
      obtain ⟨_, hcC, hpostC, hbodyC⟩ := exitScan_s_forLoop hc
      have hh1 := ihcond fu false hf hcC
      have hh2 := ExitCleanRes.sres_normal_or_continue
        (ihbody fu true hf (exitScan_s_block_rev hbodyC)) hob
      exact Or.inr ⟨rfl, ExitCleanRes.sres_halt
        (ihpost fu false hf (exitScan_s_block_rev hpostC))⟩
  | loopBreak hcond hne hbody ihcond ihbody =>
      intro fu la hf hc
      obtain ⟨_, hcC, _, hbodyC⟩ := exitScan_s_forLoop hc
      have hh1 := ihcond fu false hf hcC
      have hh2 := ExitCleanRes.sres_break (ihbody fu true hf (exitScan_s_block_rev hbodyC))
      exact Or.inl ⟨hh2.trans hh1, Or.inl rfl⟩
  | loopLeave hcond hne hbody ihcond ihbody =>
      intro fu la hf hc
      obtain ⟨_, hcC, _, hbodyC⟩ := exitScan_s_forLoop hc
      have hh1 := ihcond fu false hf hcC
      obtain ⟨hh2, hfu⟩ := ExitCleanRes.sres_leave
        (ihbody fu true hf (exitScan_s_block_rev hbodyC))
      exact Or.inl ⟨hh2.trans hh1, Or.inr (Or.inl ⟨hfu, rfl⟩)⟩
  | loopBodyHalt hcond hne hbody ihcond ihbody =>
      intro fu la hf hc
      obtain ⟨_, hcC, _, hbodyC⟩ := exitScan_s_forLoop hc
      exact Or.inr ⟨rfl, ExitCleanRes.sres_halt
        (ihbody fu true hf (exitScan_s_block_rev hbodyC))⟩


/-! ## The return tail: inversion, the two step lemmas, and the final theorem -/

theorem map_congr_range {β : Type} (n : Nat) (f g : Nat → β) (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append]
      rw [ih (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_succ n)))]
      rw [List.map_singleton, List.map_singleton, h n (Nat.lt_succ_self n)]

theorem readBytes_storeWord_one (mem : Nat → UInt8) (p : Nat) :
    readBytes (storeWord mem p 1) p 32 = abiTrue := by
  have pt : ∀ i, i < 32 → storeWord mem p 1 (p + i) = byteAt (1 : U256) (31 - i) := by
    intro i hi
    show (if p ≤ p + i ∧ p + i < p + 32 then byteAt (1 : U256) (31 - (p + i - p))
      else mem (p + i)) = byteAt (1 : U256) (31 - i)
    simp [hi]
  have key : (List.range 32).map (fun i => storeWord mem p 1 (p + i))
      = (List.range 32).map (fun i => byteAt (1 : U256) (31 - i)) := map_congr_range 32 _ _ pt
  have tail : (List.range 32).map (fun i => byteAt (1 : U256) (31 - i)) = abiTrue := by decide
  show (List.range 32).map (fun i => storeWord mem p 1 (p + i)) =
    (Midfall.natToBytesBE 1 32).data.toList
  rw [key, tail]
  rfl

theorem WorldEq.symm {a b : EvmState} (h : WorldEq a b) : WorldEq b a := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm,
    h9.symm, h10.symm, h11.symm⟩

theorem returnTail?_spec {b init : Block EVM.Op} (h : returnTail? b = some init) :
    ∃ (p₁ p₂ n v : Nat), b = init ++
      [Stmt.exprStmt (Expr.builtin EVM.Op.mstore
         [Expr.lit (Literal.number p₂), Expr.lit (Literal.number v)]),
       Stmt.exprStmt (Expr.builtin EVM.Op.ret
         [Expr.lit (Literal.number p₁), Expr.lit (Literal.number n)])] ∧
      p₁ = p₂ ∧ n = 32 ∧ v = 1 := by
  unfold returnTail? at h
  split at h
  · rename_i p₁ n p₂ v initRev heq
    split at h
    · rename_i hcond
      obtain ⟨hp, hn, hv⟩ := hcond
      have hinit : init = initRev.reverse := (Option.some.inj h).symm
      subst hinit
      refine ⟨p₁, p₂, n, v, ?_, hp, hn, hv⟩
      have hb : b.reverse = Stmt.exprStmt (Expr.builtin EVM.Op.ret
            [Expr.lit (Literal.number p₁), Expr.lit (Literal.number n)]) ::
          Stmt.exprStmt (Expr.builtin EVM.Op.mstore
            [Expr.lit (Literal.number p₂), Expr.lit (Literal.number v)]) :: initRev := heq
      conv_lhs => rw [← List.reverse_reverse b]
      rw [hb]
      simp [List.reverse_cons, List.append_assoc]
    · simp at h
  · simp at h

theorem Step.args_lits_vals {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (l : List Nat) {vs : List U256} {st' : EvmState} :
    Step (Bridge.Dialect c g) funs V st
      (.args (l.map (fun k => Expr.lit (Literal.number k)))) (.eres (.vals vs st')) →
    vs = l.map (fun k => (BitVec.ofNat 256 k : U256)) ∧ st' = st := by
  induction l generalizing vs st' with
  | nil =>
      intro h
      cases h with
      | argsNil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
      intro h
      cases h with
      | argsCons hrest hhead =>
          obtain ⟨hvs, hst⟩ := ih hrest
          cases hhead with
          | lit =>
              refine ⟨?_, ?_⟩
              · rw [hvs]; rfl
              · exact hst

theorem Step.args_lits_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState} :
    ∀ (l : List Nat) {st' : EvmState},
      ¬ Step (Bridge.Dialect c g) funs V st
        (.args (l.map (fun k => Expr.lit (Literal.number k)))) (.eres (.halt st')) := by
  intro l
  induction l with
  | nil => intro st' h; cases h
  | cons a as ih =>
      intro st' h
      cases h with
      | argsRestHalt hrest => exact ih hrest
      | argsHeadHalt hrest hhead => cases hhead

theorem Step.mstore_lit_step {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} (p : Nat) :
    Step (Bridge.Dialect c g) funs V st
      (.stmt (.exprStmt (.builtin EVM.Op.mstore [Expr.lit (Literal.number p), Expr.lit (Literal.number 1)])))
      (.sres V' st' .normal) →
    V' = V ∧ st' = { touchMemory st ((BitVec.ofNat 256 p : U256)).toNat 32 with
      memory := storeWord st.memory ((BitVec.ofNat 256 p : U256)).toNat 1 } := by
  intro h
  cases h with
  | exprStmt hex =>
      cases hex with
      | builtinOk hargs hb =>
          obtain ⟨hvs, hst⟩ := Step.args_lits_vals [p, 1] hargs
          subst hvs; rw [hst] at hb
          simp only [List.map_cons, List.map_nil] at hb
          simp only [builtinWithExternal, stepOp] at hb
          cases hb
          exact ⟨rfl, rfl⟩

theorem Step.ret_lit_expr {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {st' : EvmState} (q : Nat) :
    Step (Bridge.Dialect c g) funs V st
      (.expr (.builtin EVM.Op.ret [Expr.lit (Literal.number q), Expr.lit (Literal.number 32)]))
      (.eres (.halt st')) →
    st'.halted = some (.ret, readBytes st.memory ((BitVec.ofNat 256 q : U256)).toNat 32) := by
  intro h
  cases h with
  | builtinHalt hargs hb =>
      obtain ⟨hvs, hst⟩ := Step.args_lits_vals [q, 32] hargs
      subst hvs; rw [hst] at hb
      simp only [List.map_cons, List.map_nil] at hb
      simp only [builtinWithExternal, stepOp] at hb
      cases hb
      rfl
  | builtinArgsHalt hargs => exact (Step.args_lits_no_halt [q, 32] hargs).elim

theorem Step.stmts_mstore_one_ret {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome} (p q : Nat) (hpq : p = q) :
    Step (Bridge.Dialect c g) funs V st
      (.stmts [Stmt.exprStmt (.builtin EVM.Op.mstore
          [Expr.lit (Literal.number p), Expr.lit (Literal.number 1)]),
        Stmt.exprStmt (.builtin EVM.Op.ret
          [Expr.lit (Literal.number q), Expr.lit (Literal.number 32)])])
      (.sres V' st' o) →
    o = .halt ∧ st'.halted = some (.ret, abiTrue) := by
  subst hpq
  intro h
  cases h with
  | seqCons hms hrest =>
      obtain ⟨-, hstM⟩ := Step.mstore_lit_step p hms
      cases hrest with
      | seqCons hret hnil =>
          cases hret with
          | exprStmt hex =>
              cases hex with
              | builtinOk hargs hb =>
                  obtain ⟨hvs, hst⟩ := Step.args_lits_vals [p, 32] hargs
                  subst hvs; rw [hst] at hb
                  simp only [List.map_cons, List.map_nil] at hb
                  simp only [builtinWithExternal, stepOp] at hb
                  cases hb
      | seqStop hret hne =>
          cases hret with
          | exprStmt hex => exact absurd rfl hne
          | exprStmtHalt hex =>
              have hhalt := Step.ret_lit_expr p hex
              refine ⟨rfl, ?_⟩
              rw [hhalt, hstM, readBytes_storeWord_one]
  | seqStop hms hne =>
      cases hms with
      | exprStmt hex => exact absurd rfl hne
      | exprStmtHalt hex =>
          cases hex with
          | builtinHalt hargs hb =>
              obtain ⟨hvs, hst⟩ := Step.args_lits_vals [p, 1] hargs
              subst hvs; rw [hst] at hb
              simp only [List.map_cons, List.map_nil] at hb
              simp only [builtinWithExternal, stepOp] at hb
              cases hb
          | builtinArgsHalt hargs => exact (Step.args_lits_no_halt [p, 1] hargs).elim

/-- **TWO OUTCOMES.** Every run of the body, under ANY call relation and ANY gas oracle, from ANY
    state, returns ABI `true` with the world unchanged or is a non-committing halt with the world
    unchanged. No `LeanAccepts`, no `SoundSide`, no snapshot, no `EntryFrame`, no `Eip2537.Holds`. -/
def TwoOutcomes (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∀ (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (obs : Obs),
    RunBody R vkAddr 0 c g st₀ obs →
    obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)

/-- **THE OBLIGATION THAT REPLACES `rejects_of_not_accepts`** (WP-M5c). Generic in the block: no
    render, no plan, no key. PROVED (EXITSOUND).

    The proof is the exit-classification induction of §I.a: `Step.exitClassified` says every
    derivation of an `exitScan`-clean code leaves `halted` unchanged or halts with a NON-COMMITTING
    kind; `returnTail?_spec` splits the block at its designated `mstore(p,1); return(p,0x20)` tail,
    `Step.stmts_append_inv` splits the run there, and `Step.stmts_mstore_one_ret` computes the
    tail's halt record as `(ret, abiTrue)`. `NoWriters` supplies the world equality through the
    PROVED `Bridge.Run_worldEq_of_noWriters`. -/
theorem twoOutcomes_of_exitDiscipline (b : Block EVM.Op) (hw : NoWriters b) (hx : ExitDiscipline b)
    (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (V' : VEnv (Bridge.Dialect c g))
    (stObs : EvmState) (o : Outcome) (hrun : Bridge.RunCommitted c g b st₀ V' stObs o) :
    (⟨stObs, o⟩ : Obs).view = returnView st₀ ∨
      ((⟨stObs, o⟩ : Obs).isRevertOrHalt ∧ (⟨stObs, o⟩ : Obs).worldUnchanged st₀) := by
  obtain ⟨n, hn⟩ := hx
  unfold exitDisciplineFuel at hn
  split at hn
  · rename_i init ht
    obtain ⟨p₁, p₂, nlen, v, hb, hpq, hn32, hv⟩ := returnTail?_spec ht
    subst hn32; subst hv
    subst hb
    obtain ⟨st', hrun0, hstObs⟩ := hrun
    have hw0 : WorldEq st₀ st' := Run_worldEq_of_noWriters hw hrun0
    cases hrun0 with
    | block hbody =>
      have hinitClean : ExitScanClean false false (.b init) := ⟨n, hn⟩
      have hhoist : hoist (Bridge.Dialect c g)
          (init ++ [Stmt.exprStmt (Expr.builtin EVM.Op.mstore
              [Expr.lit (Literal.number p₂), Expr.lit (Literal.number 1)]),
            Stmt.exprStmt (Expr.builtin EVM.Op.ret
              [Expr.lit (Literal.number p₁), Expr.lit (Literal.number 32)])]) =
          hoist (Bridge.Dialect c g) init := by
        simp [hoist, List.filterMap_append]
      have hfuns : ExitCleanFuns (hoist (Bridge.Dialect c g) init :: []) :=
        exitCleanFuns_hoist hinitClean exitCleanFuns_nil
      have hfuns' : ExitCleanFuns
          (hoist (Bridge.Dialect c g)
            (init ++ [Stmt.exprStmt (Expr.builtin EVM.Op.mstore
                [Expr.lit (Literal.number p₂), Expr.lit (Literal.number 1)]),
              Stmt.exprStmt (Expr.builtin EVM.Op.ret
                [Expr.lit (Literal.number p₁), Expr.lit (Literal.number 32)])]) :: []) := by
        rw [hhoist]; exact hfuns
      rcases Step.stmts_append_inv hbody with ⟨V₁, st₁, hinit, htail⟩ | ⟨hinit, hne⟩
      · rw [hpq] at htail
        obtain ⟨ho, hhalt⟩ := Step.stmts_mstore_one_ret p₂ p₂ rfl htail
        subst ho
        have hcommit : committedState st₀ st' = st' := committedState_commit hhalt rfl
        left
        rw [hstObs, hcommit]
        show (⟨st', .halt⟩ : Obs).view =
          Obs.view ⟨{ st₀ with halted := some (.ret, abiTrue) }, .halt⟩
        exact view_eq_of_worldEq_and_halt (by simpa [WorldEq] using WorldEq.symm hw0) hhalt rfl
      · have hclass := Step.exitClassified hinit false false hfuns' hinitClean
        have hhalt : o = .halt := by
          rcases hclass with ⟨_, ho⟩ | ⟨ho, _⟩
          · rcases ho with h | ⟨hf, _⟩ | ⟨hl, _⟩
            · exact absurd h hne
            · cases hf
            · cases hl
          · exact ho
        rw [hhalt] at hclass
        obtain ⟨k, d, hk, hnc⟩ := ExitCleanRes.sres_halt hclass
        right
        have hroll : committedState st₀ st' =
            { st₀ with halted := st'.halted, returndata := st'.returndata } :=
          committedState_rollback hk hnc
        refine ⟨⟨k, d, ?_, hnc⟩, ?_⟩
        · rw [hstObs, hroll]
          exact hk
        · rw [hstObs, hroll]
          simp [Obs.worldUnchanged, WorldEq]
  · simp at hn

/-! # A2 (ST.12): the two scans do not read the VALUE of a literal

  \`scans_prog_addr_indep\` says the two syntactic scans of the closed program do not see the two
  addresses the wrapper binds as let literals. The whole section below is the machinery that lemma
  needs and nothing else: an eraser, a congruence for each of the two scans, a congruence for the
  constant inliner, and the transfer.

  THE ERASURE IS NOT TOTAL. \`exitDisciplineFuel\` splits the block at its return tail by matching
  the tail's literal VALUES (\`returnTail?\`), so an eraser that zeroes every literal would erase the
  very evidence the split reads. \`eraseS\` therefore erases only the right-hand sides of \`let\` /
  \`:=\` - which is where the wrapper addresses land - and leaves every other literal EXACTLY as it
  is. The two statements of the return tail are \`exprStmt\`s: they are untouched, a block has a
  return tail exactly when its erasure does, and the transfer of \`returnTail?\` is a reflection
  (\`eraseB_cons_inv\`) rather than a guess.

  WHY THE WALK IS INVARIANT WITHOUT AN INDUCTION ON ITS FUEL: the difference never reaches a
  sub-block. A let of a literal has none, so \`inlineStmtStep\`'s recursion argument is never called
  at a differing statement, and one congruence for the expression walk plus one for the block fold
  is the whole argument. Measured: this section elaborates in seconds; no heartbeat was raised. -/

section A2ScanBlind
open Midfall.Lowering.Inline

/-! ## ST.12 machinery: neither scan reads the VALUE of a literal

  scans_prog_addr_indep says the two syntactic scans of the closed program do not see the two
  addresses the wrapper binds as let literals.

  THE ERASURE IS NOT TOTAL. exitDisciplineFuel splits the block at its return tail by matching the
  tail's literal VALUES (returnTail?), so an eraser that zeroes every literal would erase the very
  evidence the split reads. eraseS therefore erases only the right-hand sides of let / := - which is
  where the wrapper addresses land - and leaves every other literal EXACTLY as it is. The two
  statements of the return tail are exprStmts, so they are untouched: the transfer of returnTail?
  is an identity, not a congruence. -/

mutual
/-- Every literal payload in an expression, erased. -/
def eraseE : Expr EVM.Op → Expr EVM.Op
  | .lit _ => .lit (.number 0)
  | .var x => .var x
  | .builtin op args => .builtin op (eraseEs args)
  | .call f args => .call f (eraseEs args)

/-- eraseE, lifted to a list. -/
def eraseEs : List (Expr EVM.Op) → List (Expr EVM.Op)
  | [] => []
  | e :: es => eraseE e :: eraseEs es

/-- The literals of let / := right-hand sides, erased; every other literal left alone. -/
def eraseS : Stmt EVM.Op → Stmt EVM.Op
  | .letDecl xs e => .letDecl xs (e.map eraseE)
  | .assign xs e => .assign xs (eraseE e)
  | .block b => .block (eraseB b)
  | .funDef n ps rs body => .funDef n ps rs (eraseB body)
  | .cond c body => .cond c (eraseB body)
  | .switch c cs d => .switch c (eraseCs cs) (eraseOd d)
  | .forLoop init c post body => .forLoop (eraseB init) c (eraseB post) (eraseB body)
  | s => s

/-- eraseS, lifted to a block. -/
def eraseB : List (Stmt EVM.Op) → List (Stmt EVM.Op)
  | [] => []
  | s :: ss => eraseS s :: eraseB ss

/-- eraseB, lifted over switch case arms: the case LABEL is a literal the scan never reads, and
    returnTail? never sees one, so it is left alone too. -/
def eraseCs : List (Literal × List (Stmt EVM.Op)) → List (Literal × List (Stmt EVM.Op))
  | [] => []
  | p :: ps => (p.1, eraseB p.2) :: eraseCs ps

/-- eraseB, lifted over the optional switch default. -/
def eraseOd : Option (List (Stmt EVM.Op)) → Option (List (Stmt EVM.Op))
  | none => none
  | some b => some (eraseB b)
end

/-- The same erasure at the five positions a scan can stand at. -/
def eraseScan : Scan → Scan
  | .e e => .e (eraseE e)
  | .es es => .es (eraseEs es)
  | .s s => .s (eraseS s)
  | .b b => .b (eraseB b)
  | .cs cs => .cs (eraseCs cs)

@[simp] theorem eraseEs_nil : eraseEs [] = [] := rfl
@[simp] theorem eraseB_nil : eraseB [] = [] := rfl
theorem eraseB_cons (s : Stmt EVM.Op) (b : List (Stmt EVM.Op)) :
    eraseB (s :: b) = eraseS s :: eraseB b := rfl


/-- Erasing does not change what a statement BINDS: boundOf reads names, never a value. -/
theorem eraseS_boundOf (s : Stmt EVM.Op) : boundOf (eraseS s) = boundOf s := by
  cases s <;> rfl

/-- An exprStmt is left EXACTLY alone by the erasure, and nothing else becomes one. -/
theorem eraseS_exprStmt_inv {s : Stmt EVM.Op} {e : Expr EVM.Op}
    (h : eraseS s = .exprStmt e) : s = .exprStmt e := by
  cases s <;> simp_all [eraseS]

/-- The erasure of a concatenation. -/
theorem eraseB_append (x y : List (Stmt EVM.Op)) :
    eraseB (x ++ y) = eraseB x ++ eraseB y := by
  induction x with
  | nil => rfl
  | cons s rest ih => simp [eraseB, ih]
/-! ### The writer scan cannot see an erased literal -/

theorem noWritersStep_erase (sc : Scan) (rec : Scan → Bool)
    (h : ∀ sc', rec sc' = rec (eraseScan sc')) :
    noWritersStep sc rec = noWritersStep (eraseScan sc) rec := by
  cases sc with
  | e x =>
      refine match x with
      | Expr.lit _ => rfl
      | Expr.var _ => rfl
      | Expr.builtin op args => by
          show (! Op.isWriter op && rec (Scan.es args)) =
            (! Op.isWriter op && rec (Scan.es (eraseEs args)))
          rw [h (Scan.es args)]; rfl
      | Expr.call _ args => by
          show rec (Scan.es args) = rec (Scan.es (eraseEs args))
          rw [h (Scan.es args)]; rfl
  | es xs =>
      induction xs with
      | nil => rfl
      | cons a rest ih =>
          show (rec (Scan.e a) && rec (Scan.es rest)) =
            (rec (Scan.e (eraseE a)) && rec (Scan.es (eraseEs rest)))
          rw [h (Scan.e a), h (Scan.es rest)]; rfl
  | s x =>
      refine match x with
      | Stmt.block b => by
          show rec (Scan.b b) = rec (Scan.b (eraseB b)); rw [h (Scan.b b)]; rfl
      | Stmt.funDef _ _ _ body => by
          show rec (Scan.b body) = rec (Scan.b (eraseB body)); rw [h (Scan.b body)]; rfl
      | Stmt.letDecl _ val => by
          cases val with
          | none => rfl
          | some e => show rec (Scan.e e) = rec (Scan.e (eraseE e)); rw [h (Scan.e e)]; rfl
      | Stmt.assign _ e => by
          show rec (Scan.e e) = rec (Scan.e (eraseE e)); rw [h (Scan.e e)]; rfl
      | Stmt.cond c body => by
          show (rec (Scan.e c) && rec (Scan.b body)) =
            (rec (Scan.e c) && rec (Scan.b (eraseB body)))
          rw [h (Scan.b body)]; rfl
      | Stmt.switch c cs d => by
          show (rec (Scan.e c) && rec (Scan.cs cs) &&
                match d with | none => true | some db => rec (Scan.b db)) =
               (rec (Scan.e c) && rec (Scan.cs (eraseCs cs)) &&
                match eraseOd d with | none => true | some db => rec (Scan.b db))
          rw [h (Scan.cs cs)]
          cases d with
          | none => rfl
          | some db =>
              show (rec (Scan.e c) && rec (Scan.cs (eraseCs cs)) && rec (Scan.b db)) =
                   (rec (Scan.e c) && rec (Scan.cs (eraseCs cs)) && rec (Scan.b (eraseB db)))
              rw [h (Scan.b db)]; rfl
      | Stmt.forLoop init c post body => by
          show (rec (Scan.b init) && rec (Scan.e c) && rec (Scan.b post) && rec (Scan.b body)) =
               (rec (Scan.b (eraseB init)) && rec (Scan.e c) && rec (Scan.b (eraseB post)) &&
                rec (Scan.b (eraseB body)))
          rw [h (Scan.b init), h (Scan.b post), h (Scan.b body)]; rfl
      | Stmt.exprStmt _ => rfl
      | Stmt.break => rfl
      | Stmt.continue => rfl
      | Stmt.leave => rfl
  | b bs =>
      induction bs with
      | nil => rfl
      | cons s rest ih =>
          show (rec (Scan.s s) && rec (Scan.b rest)) =
            (rec (Scan.s (eraseS s)) && rec (Scan.b (eraseB rest)))
          rw [h (Scan.s s), h (Scan.b rest)]; rfl
  | cs xs =>
      induction xs with
      | nil => rfl
      | cons p rest ih =>
          show (rec (Scan.b p.2) && rec (Scan.cs rest)) =
            (rec (Scan.b (eraseB p.2)) && rec (Scan.cs (eraseCs rest)))
          rw [h (Scan.b p.2), h (Scan.cs rest)]; rfl

theorem noWritersScan_erase (n : Nat) : ∀ (sc : Scan),
    noWritersScan n sc = noWritersScan n (eraseScan sc) := by
  induction n with
  | zero => intro sc; rfl
  | succ n ih =>
      intro sc
      show noWritersStep sc (noWritersScan n) = noWritersStep (eraseScan sc) (noWritersScan n)
      exact noWritersStep_erase sc (noWritersScan n) ih

/-- The congruence form: two scans with the same erasure have the same answer. -/
theorem noWritersScan_congr (n : Nat) (sc₁ sc₂ : Scan)
    (h : eraseScan sc₁ = eraseScan sc₂) : noWritersScan n sc₁ = noWritersScan n sc₂ :=
  calc noWritersScan n sc₁ = noWritersScan n (eraseScan sc₁) := noWritersScan_erase n sc₁
    _ = noWritersScan n (eraseScan sc₂) := congrArg (noWritersScan n) h
    _ = noWritersScan n sc₂ := (noWritersScan_erase n sc₂).symm

theorem noWritersFuel_congr (n : Nat) (b₁ b₂ : List (Stmt EVM.Op))
    (h : eraseB b₁ = eraseB b₂) : noWritersFuel n b₁ = noWritersFuel n b₂ :=
  noWritersScan_congr n (Scan.b b₁) (Scan.b b₂) (congrArg Scan.b h)

/-- NoWriters is a statement about the erased block only. -/
theorem noWriters_of_eraseB_eq {b₁ b₂ : List (Stmt EVM.Op)} (h : eraseB b₁ = eraseB b₂)
    (hw : NoWriters b₁) : NoWriters b₂ := by
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, by rw [noWritersFuel_congr n b₂ b₁ h.symm]; exact hn⟩



/-! ### The exit scan cannot see an erased literal either -/

theorem exitStep_erase (fu la : Bool) (sc : Scan) (rec : Bool → Bool → Scan → Bool)
    (h : ∀ fu la sc', rec fu la sc' = rec fu la (eraseScan sc')) :
    exitStep fu la sc rec = exitStep fu la (eraseScan sc) rec := by
  cases sc with
  | e x =>
      refine match x with
      | Expr.lit _ => rfl
      | Expr.var _ => rfl
      | Expr.builtin op args => by
          show (! isCommittingExit op && rec fu la (Scan.es args)) =
            (! isCommittingExit op && rec fu la (Scan.es (eraseEs args)))
          rw [h fu la (Scan.es args)]; rfl
      | Expr.call _ args => by
          show rec fu la (Scan.es args) = rec fu la (Scan.es (eraseEs args))
          rw [h fu la (Scan.es args)]; rfl
  | es xs =>
      induction xs with
      | nil => rfl
      | cons a rest ih =>
          show (rec fu la (Scan.e a) && rec fu la (Scan.es rest)) =
            (rec fu la (Scan.e (eraseE a)) && rec fu la (Scan.es (eraseEs rest)))
          rw [h fu la (Scan.e a), h fu la (Scan.es rest)]; rfl
  | s x =>
      refine match x with
      | Stmt.block b => by
          show rec fu la (Scan.b b) = rec fu la (Scan.b (eraseB b))
          rw [h fu la (Scan.b b)]; rfl
      | Stmt.funDef _ _ _ body => by
          show rec true false (Scan.b body) = rec true false (Scan.b (eraseB body))
          rw [h true false (Scan.b body)]; rfl
      | Stmt.letDecl _ val => by
          cases val with
          | none => rfl
          | some e =>
              show rec fu la (Scan.e e) = rec fu la (Scan.e (eraseE e))
              rw [h fu la (Scan.e e)]; rfl
      | Stmt.assign _ e => by
          show rec fu la (Scan.e e) = rec fu la (Scan.e (eraseE e))
          rw [h fu la (Scan.e e)]; rfl
      | Stmt.cond c body => by
          show (rec fu la (Scan.e c) && rec fu la (Scan.b body)) =
            (rec fu la (Scan.e c) && rec fu la (Scan.b (eraseB body)))
          rw [h fu la (Scan.b body)]; rfl
      | Stmt.switch c cs d => by
          show (rec fu la (Scan.e c) && rec fu la (Scan.cs cs) &&
                match d with | none => true | some db => rec fu la (Scan.b db)) =
               (rec fu la (Scan.e c) && rec fu la (Scan.cs (eraseCs cs)) &&
                match eraseOd d with | none => true | some db => rec fu la (Scan.b db))
          rw [h fu la (Scan.cs cs)]
          cases d with
          | none => rfl
          | some db =>
              show (rec fu la (Scan.e c) && rec fu la (Scan.cs (eraseCs cs)) &&
                    rec fu la (Scan.b db)) =
                   (rec fu la (Scan.e c) && rec fu la (Scan.cs (eraseCs cs)) &&
                    rec fu la (Scan.b (eraseB db)))
              rw [h fu la (Scan.b db)]; rfl
      | Stmt.forLoop init c post body => by
          show (rec fu false (Scan.b init) && rec fu false (Scan.e c) &&
                rec fu false (Scan.b post) && rec fu true (Scan.b body)) =
               (rec fu false (Scan.b (eraseB init)) && rec fu false (Scan.e c) &&
                rec fu false (Scan.b (eraseB post)) && rec fu true (Scan.b (eraseB body)))
          rw [h fu false (Scan.b init), h fu false (Scan.b post), h fu true (Scan.b body)]; rfl
      | Stmt.exprStmt _ => rfl
      | Stmt.break => rfl
      | Stmt.continue => rfl
      | Stmt.leave => rfl
  | b bs =>
      induction bs with
      | nil => rfl
      | cons s rest ih =>
          show (rec fu la (Scan.s s) && rec fu la (Scan.b rest)) =
            (rec fu la (Scan.s (eraseS s)) && rec fu la (Scan.b (eraseB rest)))
          rw [h fu la (Scan.s s), h fu la (Scan.b rest)]; rfl
  | cs xs =>
      induction xs with
      | nil => rfl
      | cons p rest ih =>
          show (rec fu la (Scan.b p.2) && rec fu la (Scan.cs rest)) =
            (rec fu la (Scan.b (eraseB p.2)) && rec fu la (Scan.cs (eraseCs rest)))
          rw [h fu la (Scan.b p.2), h fu la (Scan.cs rest)]; rfl

theorem exitScan_erase (n : Nat) : ∀ (fu la : Bool) (sc : Scan),
    exitScan n fu la sc = exitScan n fu la (eraseScan sc) := by
  induction n with
  | zero => intro fu la sc; rfl
  | succ n ih =>
      intro fu la sc
      show exitStep fu la sc (exitScan n) = exitStep fu la (eraseScan sc) (exitScan n)
      exact exitStep_erase fu la sc (exitScan n) ih

theorem exitScan_congr (n : Nat) (fu la : Bool) (sc₁ sc₂ : Scan)
    (h : eraseScan sc₁ = eraseScan sc₂) :
    exitScan n fu la sc₁ = exitScan n fu la sc₂ :=
  calc exitScan n fu la sc₁ = exitScan n fu la (eraseScan sc₁) := exitScan_erase n fu la sc₁
    _ = exitScan n fu la (eraseScan sc₂) := congrArg (exitScan n fu la) h
    _ = exitScan n fu la sc₂ := (exitScan_erase n fu la sc₂).symm


/-! ### The constant inliner cannot see a literal either

  The program is the inliner applied to a block whose only address-dependent part is two let
  literals, so the erasure of the OUTPUT has to be shown to depend only on the erasure of the
  INPUT. The difference never reaches a sub-block - a let of a literal has none - so the walk's
  recursion is never called at a differing statement and no induction on the walk's fuel is
  needed: one congruence for the expression walk, one for the block fold. -/

/-- The erasure of the expression walk depends only on the erasure of its input: the walk reads a
    NAME and a shadow list, never a literal payload. Stated for lists so that the nested List
    occurrences of Expr are discharged by one induction on the fuel. -/
theorem inExpr_eraseE : ∀ (fuel : Nat) (as as' : List (Expr EVM.Op)) (consts : Consts)
    (sh : List String), eraseEs as = eraseEs as' →
      eraseEs (as.map fun a => inExpr fuel a consts sh) =
        eraseEs (as'.map fun a => inExpr fuel a consts sh) := by
  intro fuel
  induction fuel with
  | zero =>
      intro as as' consts sh h
      simpa [inExpr] using h
  | succ fuel ih =>
      intro as
      induction as with
      | nil =>
          intro as' consts sh h
          cases as' with
          | nil => rfl
          | cons a' rest => exact absurd h (by simp [eraseEs])
      | cons a as ih' =>
          intro as' consts sh h
          cases as' with
          | nil => exact absurd h.symm (by simp [eraseEs])
          | cons a' rest =>
              have hhead : eraseE a = eraseE a' := List.head_eq_of_cons_eq h
              have htail : eraseEs as = eraseEs rest := List.tail_eq_of_cons_eq h
              have hstep : eraseE (inExpr (fuel+1) a consts sh) =
                  eraseE (inExpr (fuel+1) a' consts sh) := by
                refine match a with
                | Expr.lit _ => by
                    refine match a' with
                    | Expr.lit _ => by simp [inExpr, eraseE]
                    | Expr.var _ => by simp [eraseE] at hhead
                    | Expr.builtin _ _ => by simp [eraseE] at hhead
                    | Expr.call _ _ => by simp [eraseE] at hhead
                | Expr.var x => by
                    refine match a' with
                    | Expr.lit _ => by simp [eraseE] at hhead
                    | Expr.var x' => by
                        have hx : x = x' := by simpa [eraseE] using hhead
                        subst hx
                        by_cases hs : shadowed sh x
                        · simp [inExpr, hs]
                        · simp [inExpr, hs]
                    | Expr.builtin _ _ => by simp [eraseE] at hhead
                    | Expr.call _ _ => by simp [eraseE] at hhead
                | Expr.builtin op args => by
                    refine match a' with
                    | Expr.lit _ => by simp [eraseE] at hhead
                    | Expr.var _ => by simp [eraseE] at hhead
                    | Expr.builtin op' args' => by
                        have hop : op = op' := by
                          simpa [eraseE] using congrArg
                            (fun x : Expr EVM.Op => match x with
                              | Expr.builtin o _ => o | _ => op) hhead
                        subst hop
                        have hargs : eraseEs args = eraseEs args' := by
                          simpa [eraseE] using congrArg
                            (fun x : Expr EVM.Op => match x with
                              | Expr.builtin _ a => a | _ => eraseEs args) hhead
                        show eraseE (Expr.builtin op (args.map fun a => inExpr fuel a consts sh)) =
                             eraseE (Expr.builtin op (args'.map fun a => inExpr fuel a consts sh))
                        simp only [eraseE]
                        exact congrArg (Expr.builtin op) (ih args args' consts sh hargs)
                    | Expr.call _ _ => by simp [eraseE] at hhead
                | Expr.call fn args => by
                    refine match a' with
                    | Expr.lit _ => by simp [eraseE] at hhead
                    | Expr.var _ => by simp [eraseE] at hhead
                    | Expr.builtin _ _ => by simp [eraseE] at hhead
                    | Expr.call fn' args' => by
                        have hf : fn = fn' := by
                          simpa [eraseE] using congrArg
                            (fun x : Expr EVM.Op => match x with
                              | Expr.call i _ => i | _ => fn) hhead
                        subst hf
                        have hargs : eraseEs args = eraseEs args' := by
                          simpa [eraseE] using congrArg
                            (fun x : Expr EVM.Op => match x with
                              | Expr.call _ a => a | _ => eraseEs args) hhead
                        show eraseE (Expr.call fn (args.map fun a => inExpr fuel a consts sh)) =
                             eraseE (Expr.call fn (args'.map fun a => inExpr fuel a consts sh))
                        simp only [eraseE]
                        exact congrArg (Expr.call fn) (ih args args' consts sh hargs)
              show eraseE (inExpr (fuel+1) a consts sh) ::
                  eraseEs (as.map fun x => inExpr (fuel+1) x consts sh) =
                eraseE (inExpr (fuel+1) a' consts sh) ::
                  eraseEs (rest.map fun x => inExpr (fuel+1) x consts sh)
              rw [hstep, ih' rest consts sh htail]

/-- One let of a literal: the walk's output, erased, does not see the value. -/
theorem inExpr_lit (consts : Consts) (sh : List String) (u v : Nat) :
    eraseE (inExpr exprFuel (Expr.lit (.number u)) consts sh) =
      eraseE (inExpr exprFuel (Expr.lit (.number v)) consts sh) := by
  show eraseE (Expr.lit (.number u)) = eraseE (Expr.lit (.number v))
  rfl

/-- The block fold's step, named so the fold can be talked about. -/
def foldAt (rec : List String → List (Stmt EVM.Op) → SRes) (consts : Consts)
    (acc : Acc) (s : Stmt EVM.Op) : Acc :=
  let r := inlineStmtStep rec consts acc.sh s
  { blks := acc.blks ++ [r.1], sh := acc.sh ++ boundOf s, exhausted := acc.exhausted || r.2 }

theorem inlineStep_foldl (rec : List String → List (Stmt EVM.Op) → SRes) (consts : Consts)
    (sh : List String) (bl : List (Stmt EVM.Op)) :
    (inlineStep rec consts sh bl).blks =
      (bl.foldl (foldAt rec consts) { blks := [], sh := sh, exhausted := false }).blks := rfl

/-- The fold, from two accumulators that agree on their shadow list and on the erasure of their
    statements, ends in accumulators that agree on the erasure. -/
theorem foldl_eraseB_congr (rec : List String → List (Stmt EVM.Op) → SRes) (consts : Consts) :
    ∀ (Q : List (Stmt EVM.Op)) (acc acc' : Acc), acc.sh = acc'.sh →
      eraseB acc.blks = eraseB acc'.blks →
      eraseB (Q.foldl (foldAt rec consts) acc).blks =
        eraseB (Q.foldl (foldAt rec consts) acc').blks := by
  intro Q
  induction Q with
  | nil => intro acc acc' _ hbl; exact hbl
  | cons s rest ih =>
      intro acc acc' hsh hbl
      show eraseB (rest.foldl (foldAt rec consts) (foldAt rec consts acc s)).blks =
           eraseB (rest.foldl (foldAt rec consts) (foldAt rec consts acc' s)).blks
      refine ih _ _ ?_ ?_
      · show acc.sh ++ boundOf s = acc'.sh ++ boundOf s; rw [hsh]
      · show eraseB (acc.blks ++ [(inlineStmtStep rec consts acc.sh s).1]) =
             eraseB (acc'.blks ++ [(inlineStmtStep rec consts acc'.sh s).1])
        rw [hsh, eraseB_append, eraseB_append, hbl]

/-- The walk at a let of a literal: the erasure of the output does not see the value, and the
    binder list is unchanged. -/
theorem inlineStmtStep_letLit (rec : List String → List (Stmt EVM.Op) → SRes) (consts : Consts)
    (sh : List String) (xs : List String) (u v : Nat) :
    eraseS (inlineStmtStep rec consts sh (Stmt.letDecl xs (some (Expr.lit (.number u))))).1 =
      eraseS (inlineStmtStep rec consts sh (Stmt.letDecl xs (some (Expr.lit (.number v))))).1 := by
  show eraseS (Stmt.letDecl xs (some (inExpr exprFuel (Expr.lit (.number u)) consts sh))) =
       eraseS (Stmt.letDecl xs (some (inExpr exprFuel (Expr.lit (.number v)) consts sh)))
  simp only [eraseS, Option.map_some]
  rw [inExpr_lit consts sh u v]

theorem boundOf_letLit (xs : List String) (u : Nat) :
    boundOf (Stmt.letDecl xs (some (Expr.lit (.number u)))) = xs := rfl

/-- One differing let-of-a-literal anywhere inside the block the walk runs on: the erasure of the
    walk's output does not see it. -/
theorem foldl_eraseB_local (rec : List String → List (Stmt EVM.Op) → SRes) (consts : Consts)
    (init : Acc) (P Q : List (Stmt EVM.Op)) (xs : List String) (u v : Nat) :
    let su := Stmt.letDecl xs (some (Expr.lit (.number u)))
    let sv := Stmt.letDecl xs (some (Expr.lit (.number v)))
    eraseB (List.foldl (foldAt rec consts) init (P ++ [su] ++ Q)).blks =
      eraseB (List.foldl (foldAt rec consts) init (P ++ [sv] ++ Q)).blks := by
  intro su sv
  set accP := List.foldl (foldAt rec consts) init P with haccP
  have hsplit (w : Nat) : List.foldl (foldAt rec consts) init
      (P ++ [Stmt.letDecl xs (some (Expr.lit (.number w)))] ++ Q) =
      List.foldl (foldAt rec consts)
        (foldAt rec consts accP (Stmt.letDecl xs (some (Expr.lit (.number w))))) Q := by
    have h2 : List.foldl (foldAt rec consts) accP
        [Stmt.letDecl xs (some (Expr.lit (.number w)))] =
        foldAt rec consts accP (Stmt.letDecl xs (some (Expr.lit (.number w)))) := rfl
    rw [List.foldl_append, List.foldl_append, ← haccP, h2]
  rw [hsplit u, hsplit v]
  have hsh : (foldAt rec consts accP su).sh = (foldAt rec consts accP sv).sh := by
    show accP.sh ++ boundOf su = accP.sh ++ boundOf sv
    rw [show boundOf su = xs from rfl, show boundOf sv = xs from rfl]
  have hbl : eraseB (foldAt rec consts accP su).blks =
      eraseB (foldAt rec consts accP sv).blks := by
    show eraseB (accP.blks ++ [(inlineStmtStep rec consts accP.sh su).1]) =
      eraseB (accP.blks ++ [(inlineStmtStep rec consts accP.sh sv).1])
    rw [eraseB_append, eraseB_append]
    dsimp only [su, sv] at *
    congr 1
  exact foldl_eraseB_congr rec consts Q _ _ hsh hbl

/-- The walk over a block is insensitive, up to erasure, to one let-of-a-literal inside it. -/
theorem inlineScan_eraseB_local (consts : Consts) (sh : List String)
    (P Q : List (Stmt EVM.Op)) (xs : List String) (u v : Nat) :
    let su := Stmt.letDecl xs (some (Expr.lit (.number u)))
    let sv := Stmt.letDecl xs (some (Expr.lit (.number v)))
    eraseB ((inlineScan inlineFuel consts sh (P ++ [su] ++ Q)).blks) =
      eraseB ((inlineScan inlineFuel consts sh (P ++ [sv] ++ Q)).blks) := by
  intro su sv
  show eraseB ((inlineStep (inlineScan (inlineFuel - 1) consts) consts sh (P ++ [su] ++ Q)).blks) =
      eraseB ((inlineStep (inlineScan (inlineFuel - 1) consts) consts sh (P ++ [sv] ++ Q)).blks)
  rw [inlineStep_foldl, inlineStep_foldl]
  exact foldl_eraseB_local (inlineScan (inlineFuel - 1) consts) consts
    { blks := [], sh := sh, exhausted := false } P Q xs u v








/-! ### The return tail survives the erasure

  exitDisciplineFuel splits the block at its return tail, and the split reads the tail's literal
  VALUES. That is exactly why eraseS erases only let right-hand sides: an exprStmt is left alone by
  eraseS and nothing else becomes one, so the split is the same split on two blocks with the same
  erasure, and the two inits have the same erasure. -/

theorem eraseB_reverse (b : List (Stmt EVM.Op)) :
    eraseB (List.reverse b) = List.reverse (eraseB b) := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
      rw [List.reverse_cons, eraseB_append, ih]
      show List.reverse (eraseB rest) ++ [eraseS s] = (eraseS s :: eraseB rest).reverse
      rw [List.reverse_cons]

/-- The two statements a return tail is made of, named. -/
@[match_pattern] abbrev retTailStmt (p₁ n : Nat) : Stmt EVM.Op :=
  Stmt.exprStmt (Expr.builtin EVM.Op.ret [Expr.lit (.number p₁), Expr.lit (.number n)])

@[match_pattern] abbrev mstoreTailStmt (p₂ v : Nat) : Stmt EVM.Op :=
  Stmt.exprStmt (Expr.builtin EVM.Op.mstore [Expr.lit (.number p₂), Expr.lit (.number v)])

theorem eraseS_retTail (p₁ n : Nat) : eraseS (retTailStmt p₁ n) = retTailStmt p₁ n := rfl
theorem eraseS_mstoreTail (p₂ v : Nat) : eraseS (mstoreTailStmt p₂ v) = mstoreTailStmt p₂ v := rfl

/-- The erasure reflects a two-statement head of exprStmts: if the erased block begins with two,
    so does the block, with the same two and an erased remainder. -/
theorem eraseB_cons_inv {l : List (Stmt EVM.Op)} {p₁ p₂ nn vv : Nat} {r : List (Stmt EVM.Op)}
    (h : eraseB l = retTailStmt p₁ nn :: mstoreTailStmt p₂ vv :: r) :
    ∃ l', l = retTailStmt p₁ nn :: mstoreTailStmt p₂ vv :: l' ∧ eraseB l' = r := by
  match hl : l with
  | [] => exact absurd h (by simp [eraseB])
  | [_] => exact absurd h (by simp [eraseB] at h)
  | x :: y :: rest =>
      have hx : eraseS x = retTailStmt p₁ nn := List.head_eq_of_cons_eq h
      have h2 : eraseS y :: eraseB rest = mstoreTailStmt p₂ vv :: r :=
        List.tail_eq_of_cons_eq h
      have hy : eraseS y = mstoreTailStmt p₂ vv := List.head_eq_of_cons_eq h2
      have hr : eraseB rest = r := List.tail_eq_of_cons_eq h2
      exact ⟨rest, by rw [eraseS_exprStmt_inv hx, eraseS_exprStmt_inv hy], hr⟩

/-- INVERSION of the tail match: if it answers some, the block ends in the two tail statements and
    the init is what the match returns. The case tree below IS the match's own pattern: every branch
    that does not reach it answers none, so it cannot be the witness. -/
theorem returnTail?_some {b : Block EVM.Op} {t : Block EVM.Op}
    (h : returnTail? b = some t) :
    ∃ (p₁ p₂ n v : Nat) (initRev : List (Stmt EVM.Op)),
      b.reverse = retTailStmt p₁ n :: mstoreTailStmt p₂ v :: initRev ∧
        p₁ = p₂ ∧ n = 32 ∧ v = 1 ∧ t = initRev.reverse := by
  have h2 := h
  rw [returnTail?] at h2
  match hb : List.reverse b with
  | [] => rw [hb] at h2; simp at h2
  | [_] => rw [hb] at h2; simp at h2
  | retTailStmt p₁ n :: mstoreTailStmt p₂ v :: initRev =>
      rw [hb] at h2
      simp at h2
      obtain ⟨⟨ha, hb', hc⟩, hd⟩ := h2
      exact ⟨p₁, p₂, n, v, initRev, rfl, ha, hb', hc, hd.symm⟩
  | a :: c :: r =>
      rw [hb] at h2
      cases a with
      | exprStmt e =>
          cases e with
          | builtin op args =>
              cases op with
              | ret =>
                  cases args with
                  | nil =>
                      simp at h2
                  | cons x xs =>
                      cases xs with
                      | nil =>
                          simp at h2
                      | cons y ys =>
                          cases ys with
                          | cons p q =>
                              simp at h2
                          | nil =>
                              cases x with
                              | lit l1 =>
                                  cases l1 with
                                  | number p₁ =>
                                      cases y with
                                      | lit l2 =>
                                          cases l2 with
                                          | number n =>
                                              cases c with
                                              | exprStmt e2 =>
                                                  cases e2 with
                                                  | builtin op2 args2 =>
                                                      cases op2 with
                                                      | mstore =>
                                                          cases args2 with
                                                          | nil =>
                                                              simp at h2
                                                          | cons x2 xs2 =>
                                                              cases xs2 with
                                                              | nil =>
                                                                  simp at h2
                                                              | cons y2 ys2 =>
                                                                  cases ys2 with
                                                                  | cons p2 q2 =>
                                                                      simp at h2
                                                                  | nil =>
                                                                      cases x2 with
                                                                      | lit l3 =>
                                                                          cases l3 with
                                                                          | number p₂ =>
                                                                              cases y2 with
                                                                              | lit l4 =>
                                                                                  cases l4 with
                                                                                  | number v =>
                                                                                      simp at h2
                                                                                      obtain ⟨⟨ha, hb', hc⟩, hd⟩ := h2
                                                                                      exact ⟨p₁, p₂, n, v, r, rfl, ha, hb', hc, hd.symm⟩
                                                                                  | _ =>
                                                                                      simp at h2
                                                                              | _ =>
                                                                                  simp at h2
                                                                          | _ =>
                                                                              simp at h2
                                                                      | _ =>
                                                                          simp at h2
                                                      | _ =>
                                                          simp at h2
                                                  | _ =>
                                                      simp at h2
                                              | _ =>
                                                  simp at h2
                                          | _ =>
                                              simp at h2
                                      | _ =>
                                          simp at h2
                                  | _ =>
                                      simp at h2
                              | _ =>
                                  simp at h2
              | _ =>
                  simp at h2
          | _ =>
              simp at h2
      | _ =>
          simp at h2

theorem exitDiscipline_of_eraseB_eq {b₁ b₂ : Block EVM.Op} (h : eraseB b₁ = eraseB b₂)
    (hx : ExitDiscipline b₁) : ExitDiscipline b₂ := by
  obtain ⟨n, hn⟩ := hx
  have hnt : returnTail? b₁ ≠ none := by
    intro hnone
    have : exitDisciplineFuel n b₁ = false := by
      unfold exitDisciplineFuel
      rw [hnone]
    rw [this] at hn
    exact Bool.noConfusion hn
  obtain ⟨t, ht⟩ : ∃ t, returnTail? b₁ = some t := by
    rcases h' : returnTail? b₁ with _ | t
    · exact absurd h' hnt
    · exact ⟨t, rfl⟩
  obtain ⟨p₁, p₂, nn, vv, rev₁, hb₁, hp, hn32, hv1, ht₁⟩ := returnTail?_some ht
  subst hn32
  subst hv1
  subst ht₁
  have h2' : eraseB b₂.reverse =
      retTailStmt p₁ 32 :: mstoreTailStmt p₂ 1 :: eraseB rev₁ := by
    have hrev : eraseB b₁.reverse = eraseB b₂.reverse := by
      rw [eraseB_reverse, eraseB_reverse, h]
    rw [hb₁] at hrev
    exact (by simpa [eraseB_cons, eraseS_retTail, eraseS_mstoreTail] using hrev.symm)
  obtain ⟨rev₂, hb₂, her₂⟩ := eraseB_cons_inv h2'
  have hback : exitDisciplineFuel n b₁ = exitScan n false false (Scan.b rev₁.reverse) := by
    unfold exitDisciplineFuel
    rw [ht]
  rw [hback] at hn
  have hcongr : eraseScan (Scan.b rev₂.reverse) = eraseScan (Scan.b rev₁.reverse) := by
    show Scan.b (eraseB rev₂.reverse) = Scan.b (eraseB rev₁.reverse)
    rw [eraseB_reverse, her₂, ← eraseB_reverse]
  have hfuel : exitDisciplineFuel n b₂ = exitScan n false false (Scan.b rev₂.reverse) := by
    unfold exitDisciplineFuel
    rw [returnTail?, hb₂]
    simp [hp]
  refine ⟨n, ?_⟩
  rw [hfuel]
  exact (exitScan_congr n false false (Scan.b rev₂.reverse) (Scan.b rev₁.reverse) hcongr).symm ▸ hn

/-! ### ST.12: the two scans ignore the two wrapper addresses -/

/-- A whole block of let-of-a-literal statements: the fold, and so the walk, does not see their
    values. -/
theorem foldl_eraseB_lets (rec : List String → List (Stmt EVM.Op) → SRes) (consts : Consts) :
    ∀ (s₁ s₂ : List (Stmt EVM.Op)) (acc : Acc) (Q : List (Stmt EVM.Op)),
      eraseB s₁ = eraseB s₂ →
      (∀ x ∈ s₁, ∃ (bs : List String) (u : Nat), x = Stmt.letDecl bs (some (Expr.lit (.number u)))) →
      (∀ x ∈ s₂, ∃ (bs : List String) (u : Nat), x = Stmt.letDecl bs (some (Expr.lit (.number u)))) →
      eraseB ((s₁ ++ Q).foldl (foldAt rec consts) acc).blks =
        eraseB ((s₂ ++ Q).foldl (foldAt rec consts) acc).blks := by
  intro s₁
  induction s₁ with
  | nil =>
      intro s₂ acc Q herase h₁ h₂
      cases s₂ with
      | nil => rfl
      | cons y ys => exact absurd herase (by simp [eraseB])
  | cons x xs ih =>
      intro s₂ acc Q herase h₁ h₂
      cases s₂ with
      | nil => exact absurd herase (by simp [eraseB])
      | cons y ys =>
          have hxy : eraseS x = eraseS y := List.head_eq_of_cons_eq herase
          have hrest : eraseB xs = eraseB ys := List.tail_eq_of_cons_eq herase
          obtain ⟨bs, u, hx0⟩ := h₁ x (by simp)
          obtain ⟨bs', v, hy0⟩ := h₂ y (by simp)
          subst hx0
          subst hy0
          have hnames : bs = bs' := by
            have := congrArg (fun s : Stmt EVM.Op =>
                match s with | Stmt.letDecl n _ => n | _ => []) hxy
            simpa [eraseS] using this
          subst hnames
          have hstep : eraseB (foldAt rec consts acc (Stmt.letDecl bs (some (Expr.lit (.number u))))).blks =
              eraseB (foldAt rec consts acc (Stmt.letDecl bs (some (Expr.lit (.number v))))).blks := by
            show eraseB (acc.blks ++
                  [(inlineStmtStep rec consts acc.sh
                      (Stmt.letDecl bs (some (Expr.lit (.number u))))).1]) =
                eraseB (acc.blks ++
                  [(inlineStmtStep rec consts acc.sh
                      (Stmt.letDecl bs (some (Expr.lit (.number v))))).1])
            rw [eraseB_append, eraseB_append]
            congr 1
          have hsh : (foldAt rec consts acc (Stmt.letDecl bs (some (Expr.lit (.number u))))).sh =
              (foldAt rec consts acc (Stmt.letDecl bs (some (Expr.lit (.number v))))).sh := by
            show acc.sh ++ boundOf _ = acc.sh ++ boundOf _
            rw [show boundOf (Stmt.letDecl bs (some (Expr.lit (.number u)))) = bs from rfl,
                show boundOf (Stmt.letDecl bs (some (Expr.lit (.number v)))) = bs from rfl]
          rw [List.cons_append, List.cons_append, List.foldl_cons, List.foldl_cons]
          refine Eq.trans ?_ (foldl_eraseB_congr rec consts (ys ++ Q) _ _ hsh hstep)
          exact ih ys (foldAt rec consts acc (Stmt.letDecl bs (some (Expr.lit (.number u))))) Q hrest
            (fun z hz => h₁ z (by simp [hz])) (fun z hz => h₂ z (by simp [hz]))

/-- The walk over a block is insensitive, up to erasure, to a block of let-of-a-literal statements
    spliced into it. -/
theorem inlineScan_eraseB_lets (consts : Consts) (sh : List String) (P Q : List (Stmt EVM.Op))
    (s₁ s₂ : List (Stmt EVM.Op))
    (herase : eraseB s₁ = eraseB s₂)
    (h₁ : ∀ x ∈ s₁, ∃ (bs : List String) (u : Nat), x = Stmt.letDecl bs (some (Expr.lit (.number u))))
    (h₂ : ∀ x ∈ s₂, ∃ (bs : List String) (u : Nat), x = Stmt.letDecl bs (some (Expr.lit (.number u)))) :
    eraseB ((inlineScan inlineFuel consts sh (P ++ s₁ ++ Q)).blks) =
      eraseB ((inlineScan inlineFuel consts sh (P ++ s₂ ++ Q)).blks) := by
  set rec' := inlineScan (inlineFuel - 1) consts with hrec'
  set init0 : Acc := { blks := [], sh := sh, exhausted := false } with hinit0
  show eraseB ((inlineStep rec' consts sh (P ++ s₁ ++ Q)).blks) =
      eraseB ((inlineStep rec' consts sh (P ++ s₂ ++ Q)).blks)
  rw [inlineStep_foldl, inlineStep_foldl]
  have h : eraseB ((s₁ ++ Q).foldl (foldAt rec' consts) (P.foldl (foldAt rec' consts) init0)).blks =
      eraseB ((s₂ ++ Q).foldl (foldAt rec' consts) (P.foldl (foldAt rec' consts) init0)).blks :=
    foldl_eraseB_lets rec' consts s₁ s₂ (P.foldl (foldAt rec' consts) init0) Q herase h₁ h₂
  have e1 : (P ++ s₁ ++ Q).foldl (foldAt rec' consts) init0 =
      (s₁ ++ Q).foldl (foldAt rec' consts) (P.foldl (foldAt rec' consts) init0) := by
    simp only [List.foldl_append]
  have e2 : (P ++ s₂ ++ Q).foldl (foldAt rec' consts) init0 =
      (s₂ ++ Q).foldl (foldAt rec' consts) (P.foldl (foldAt rec' consts) init0) := by
    simp only [List.foldl_append]
  rw [e1, e2]
  exact h

/-- The two wrapper bindings, erased: the addresses are gone, and every one of them is a let of a
    literal. -/
theorem eraseB_wrapperLocals (m : Model) (a b a' b' : U256) :
    eraseB (wrapperLocals m a b) = eraseB (wrapperLocals m a' b') := by
  unfold wrapperLocals
  split <;> split <;> simp [eraseB, eraseS, eraseE, lit]

theorem mem_wrapperLocals (m : Model) (a b : U256) (x : Stmt EVM.Op)
    (hx : x ∈ wrapperLocals m a b) :
    ∃ (bs : List String) (u : Nat), x = Stmt.letDecl bs (some (Expr.lit (.number u))) := by
  unfold wrapperLocals at hx
  split at hx
  · split at hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with h | h
      · exact ⟨["vk"], BitVec.toNat a, by rw [h]; simp [lit]⟩
      · exact ⟨["quotientEvaluator"], BitVec.toNat b, by rw [h]; simp [lit]⟩
    · simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx
      exact ⟨["vk"], BitVec.toNat a, by rw [hx]; simp [lit]⟩
  · split at hx
    · simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, false_or] at hx
      exact ⟨["quotientEvaluator"], BitVec.toNat b, by rw [hx]; simp [lit]⟩
    · exact absurd hx (by simp)

theorem eraseB_asmOf_eq (pv : PlanView) (m : Model) (a b a' b' : U256) :
    eraseB (asmOf pv m a b) = eraseB (asmOf pv m a' b') := by
  show eraseB (Inline.inlineContractConstants (constTableOf m)
        (abiGuardBlock m ++ wrapperLocals m a b ++ mainAsmRaw pv m)) =
      eraseB (Inline.inlineContractConstants (constTableOf m)
        (abiGuardBlock m ++ wrapperLocals m a' b' ++ mainAsmRaw pv m))
  show eraseB ((Inline.inlineScan Inline.inlineFuel (constTableOf m) []
        (abiGuardBlock m ++ wrapperLocals m a b ++ mainAsmRaw pv m)).blks) =
      eraseB ((Inline.inlineScan Inline.inlineFuel (constTableOf m) []
        (abiGuardBlock m ++ wrapperLocals m a' b' ++ mainAsmRaw pv m)).blks)
  exact inlineScan_eraseB_lets (constTableOf m) [] (abiGuardBlock m) (mainAsmRaw pv m)
    (wrapperLocals m a b) (wrapperLocals m a' b')
    (eraseB_wrapperLocals m a b a' b')
    (fun x hx => mem_wrapperLocals m a b x hx)
    (fun x hx => mem_wrapperLocals m a' b' x hx)

end A2ScanBlind

/-- The two scans are insensitive to the two addresses the wrapper binds (they occur only as
    \`let\` literals). PROVED (WP-A2, ST.12): the two programs are equal after \`eraseB\`, and neither
    scan reads a literal payload. This retires \`noWriters_prog\` (\`Blocks.lean:340\`), which it
    subsumes. -/
theorem scans_prog_addr_indep (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256)
    (hw : NoWriters (R.prog 0 0)) (hx : ExitDiscipline (R.prog 0 0)) :
    NoWriters (R.prog vkAddr qAddr) ∧ ExitDiscipline (R.prog vkAddr qAddr) := by
  have he : eraseB (R.prog 0 0) = eraseB (R.prog vkAddr qAddr) :=
    eraseB_asmOf_eq R.pv R.model 0 0 vkAddr qAddr
  exact ⟨noWriters_of_eraseB_eq he hw, exitDiscipline_of_eraseB_eq he hx⟩
/-- `TwoOutcomes` from the two decidable render facts. PROVED from the two obligations above. -/
theorem twoOutcomes_of_scans (R : Render p G₁ G₂ Gₜ)
    (hw : NoWriters (R.prog 0 0)) (hx : ExitDiscipline (R.prog 0 0)) : TwoOutcomes R := by
  intro vkAddr c g st₀ obs hobs
  obtain ⟨V', hrun⟩ := hobs
  obtain ⟨hw', hx'⟩ := scans_prog_addr_indep R vkAddr 0 hw hx
  exact twoOutcomes_of_exitDiscipline (R.prog vkAddr 0) hw' hx' c g st₀ V' obs.state obs.outcome hrun

/-! ## §N. THE PROGRAM CHECKS: one decidable bundle with the seven D-P71 clauses folded in (RECON.1)

  THE BASE IS THE OBJECT TEXT (`ObjectV3Full.lean:747-755`, `programOkWith`): `codegenStruct`,
  `constsCoherent`, `callsResolved`, `noShadow`, `mainClosed`, `0x80 ≤ transcriptMptr`. RECON.1 step 2
  adds the frozen token clause (`codegenAgrees`), ONE exit scan, `cdBound` and `hasMultiPointSet`; the
  D-P71 blockquote adds `gasScan`, the transcript region (PG-TPBUF), `0x80 ≤ g1IdentityMptr`
  (PG-G1ID), `2 ≤ numNegLagranges` (PG-NEGLAG) and the repaired permutation clause that step 4 deletes
  with `WellFormedV3`. `FR_MODULUS = p` and `returnMptr` are NOT conjuncts: they are THEOREMS of
  `constsCoherent` (additions 6 and 7), proved below.

  WHY `programOk` IS A `Prop` AND NOT THE OBJECT TEXT'S `Bool`: three conjuncts - the exit scan and
  the two gas scans (`GasCallOk`, D-GATE1's `GasFree`) - are fuel-bounded scans stated as
  `∃ n, scan n = true`, exactly as `NoWriters` is
  (`Bridge.lean:1108`). Folding them into one `Bool` would pin a fuel in the statement and make the
  class depend on the witness: a render whose program needs one more unit of fuel than the pin would
  be excluded by a number that means nothing. So `programOkB` is the decidable bundle the clause table
  evaluates and `programOk` is `programOkB = true` conjoined with the two scans. Nothing is weakened
  and nothing is invented.

  `constsCoherent`, `expectedConsts`, `callsResolved` and `noShadowProg` are the object text's, ported
  verbatim except where the tree's own names differ (`mainAsmRaw` takes the model since WP-G1;
  `FR_MODULUS` is the tree's `frModulusConstant` and not a second copy of the literal). -/

/-- Byte address of a layout pointer (same adapter as `Inv.ptrAddr`). -/
def cAddr (q : Ptr) : Nat := Value.asUsizeNat q.value

/-- THE CONTRACT CONSTANT TABLE AS DATA, in the order of `templates/partials/verifier/Constants.sol`.
    Every address is read from the PLAN VIEW (the record `Inv` reads), every length from the plan
    view's payload, every calldata pointer from the plan view's proof layout. Only the build-time
    numbers that the plan view does not carry come from the model: the three optional-arm selectors
    (`expectedVkCodehash`, `quotientExternal`/`expectedQuotient*`, `expectedHasAccumulator`), the
    gas schedule and the two derived gas numbers. The 14 trailing entries are template literals. -/
def expectedConsts (pv : PlanView) (m : Model) : List (String × Nat) :=
  let M := pv.memory
  let H := m.vkHeader
  let hdr (w : Nat) : Nat := cAddr (Ptr.add M.vkMptr w)
  (match m.expectedVkCodehash with
    | some _ =>
        [ ("EXPECTED_VK_PAYLOAD_LENGTH", pv.vk.len)
        , ("EXPECTED_VK_LENGTH", pv.vk.len + 1)
        , ("EXPECTED_VK_CODEHASH_WORD", (keccak256 pv.vk.runtimeBytes).toNat) ]
    | none => []) ++
  (match m.quotientExternal, m.expectedQuotientCodehash with
    | some _, some h =>
        [ ("EXPECTED_QUOTIENT_LENGTH", m.expectedQuotientLen.getD 0)
        , ("EXPECTED_QUOTIENT_CODEHASH_WORD", h.toNat) ]
    | _, _ => []) ++
  [ ("PROOF_LEN_CPTR", pv.proofLayout.proofCptr - 32)
  , ("PROOF_CPTR", pv.proofLayout.proofCptr)
  , ("NUM_INSTANCE_CPTR", pv.proofLayout.proofEnd)
  , ("INSTANCE_CPTR", pv.proofLayout.proofEnd + 32)
  , ("TRANSCRIPT_MPTR", M.transcriptMptr)
  , ("RETURN_MPTR", M.verifierReturnMptr)
  , ("VK_MPTR", cAddr M.vkMptr)
  , ("VK_DIGEST_MPTR", hdr H.vkDigest)
  , ("NUM_INSTANCES_MPTR", hdr H.numInstances)
  , ("K_MPTR", hdr H.k)
  , ("N_INV_MPTR", hdr H.nInv)
  , ("OMEGA_MPTR", hdr H.omega)
  , ("OMEGA_INV_MPTR", hdr H.omegaInv)
  , ("OMEGA_INV_TO_L_MPTR", hdr H.omegaInvToL)
  , ("HAS_ACCUMULATOR_MPTR", hdr H.hasAccumulator)
  , ("ACC_OFFSET_MPTR", hdr H.accOffset)
  , ("NUM_ACC_LIMBS_MPTR", hdr H.numAccLimbs)
  , ("NUM_ACC_LIMB_BITS_MPTR", hdr H.numAccLimbBits)
  , ("G1_BASE_MPTR", hdr H.g1Base)
  , ("G2_BASE_MPTR", hdr H.g2Base)
  , ("NEG_S_G2_BASE_MPTR", hdr H.negSG2Base)
  , ("CHALLENGE_MPTR", cAddr M.challengeMptr)
  , ("THETA_MPTR", cAddr M.thetaMptr)
  , ("BETA_MPTR", cAddr M.betaMptr)
  , ("GAMMA_MPTR", cAddr M.gammaMptr)
  , ("TRASH_CHALLENGE_MPTR", cAddr M.trashChallengeMptr)
  , ("Y_MPTR", cAddr M.yMptr)
  , ("X_MPTR", cAddr M.xMptr)
  , ("X1_MPTR", cAddr M.x1Mptr)
  , ("X2_MPTR", cAddr M.x2Mptr)
  , ("X3_MPTR", cAddr M.x3Mptr)
  , ("X4_MPTR", cAddr M.x4Mptr)
  , ("F_COM_MPTR", cAddr M.fComMptr)
  , ("PI_MPTR", cAddr M.piMptr)
  , ("ACC_LHS_MPTR", cAddr M.accLhsMptr)
  , ("ACC_RHS_MPTR", cAddr M.accRhsMptr)
  , ("X_N_MPTR", cAddr M.xNMptr)
  , ("X_N_MINUS_1_INV_MPTR", cAddr M.xNMinus1InvMptr)
  , ("L_LAST_MPTR", cAddr M.lLastMptr)
  , ("L_BLIND_MPTR", cAddr M.lBlindMptr)
  , ("L_0_MPTR", cAddr M.l0Mptr)
  , ("INSTANCE_EVAL_MPTR", cAddr M.instanceEvalMptr)
  , ("QUOTIENT_EVAL_MPTR", cAddr M.quotientEvalMptr)
  , ("QUOTIENT_MPTR", cAddr M.quotientMptr)
  , ("F_EVAL_MPTR", cAddr M.fEvalMptr)
  , ("V_MPTR", cAddr M.vMptr)
  , ("FINAL_COM_MPTR", cAddr M.finalComMptr)
  , ("PAIRING_LHS_MPTR", cAddr M.pairingLhsMptr)
  , ("PAIRING_RHS_MPTR", cAddr M.pairingRhsMptr)
  , ("ROT_POINTS_MPTR", cAddr M.rotPointsMptr)
  , ("X1_POWERS_MPTR", cAddr M.x1PowersMptr)
  , ("Q_COM_MPTR", cAddr M.qComMptr)
  , ("Q_EVAL_SET_MPTR", cAddr M.qEvalSetMptr)
  , ("Q_EVAL_CPTR_MPTR", cAddr M.qEvalCptrMptr)
  , ("G1_IDENTITY_MPTR", cAddr M.g1IdentityMptr)
  , ("REVERSED_EVALS_MPTR", cAddr M.reversedEvalsMptr)
  , ("SELECTOR_ACC_MPTR", M.selectorAccMptr)
  , ("QUOTIENT_RETURN_MPTR", M.quotientReturnMptr)
  , ("BATCH_INV_SCRATCH_MPTR", M.batchInvertScratchMptr)
  , ("LAGRANGE_DENOMS_MPTR", M.lagrangeDenomsMptr)
  , ("TRACE_U256_MPTR", M.traceU256Mptr)
  , ("ADVICE_COMMS_MPTR_BASE", cAddr M.adviceCommsMptrBase)
  , ("LOOKUP_M_COMMS_MPTR_BASE", cAddr M.lookupMCommsMptrBase)
  , ("PERM_Z_COMMS_MPTR_BASE", cAddr M.permZCommsMptrBase)
  , ("LOOKUP_HELPER_COMMS_MPTR_BASE", cAddr M.lookupHelperCommsMptrBase)
  , ("LOOKUP_Z_COMMS_MPTR_BASE", cAddr M.lookupZCommsMptrBase)
  , ("TRASHCAN_COMMS_MPTR_BASE", cAddr M.trashcanCommsMptrBase)
  , ("QUOTIENT_LIMB_COMMS_MPTR_BASE", cAddr M.quotientLimbCommsMptrBase)
  , ("G1ADD_GAS", m.templateConstants.gas.g1add)
  , ("G1MSM_GAS_1PAIR", m.templateConstants.gas.g1msmOnePair)
  , ("PAIRING_GAS_2PAIR", m.templateConstants.gas.pairingTwoPair)
  , ("MODEXP_GAS", m.templateConstants.gas.modexp)
  , ("G1MSM_GAS_SMOKE", m.constructorG1msmSmokeGas) ] ++
  (if m.expectedHasAccumulator then [("ACC_RHS_MSM_GAS", m.accRhsMsmGas)] else []) ++
  [ ("ERR_BAD_CALLDATA_SHAPE", 0x1b99e37c)
  , ("ERR_VK_MISMATCH", 0xa447d73e)
  , ("ERR_NON_CANONICAL_SCALAR", 0x77530042)
  , ("ERR_BAD_POINT_ENCODING", 0xf27905ec)
  , ("ERR_PRECOMPILE_FAILED", 0x84e81692)
  , ("ERR_PROOF_REJECTED", 0xc3b0d8cd)
  , ("ERR_QUOTIENT_PROGRAM_INVALID", 0x3cc81b89)
  , ("ERR_MEMORY_LAYOUT_VIOLATED", 0xc9888d23)
  , ("FR_MODULUS", frModulusConstant)
  , ("BLS_P_HI", 0x1a0111ea397fe69a4b1ba7b6434bacd7)
  , ("BLS_P_MINUS_ONE_LO", 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_1", 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84) ]

/-- The names the un-inlined program reads that it does not bind: exactly the contract constants
    plus the two wrapper locals. Includes the ABI guard block, which `mainClosed` omits. -/
def progConstNames (pv : PlanView) (m : Model) : List String :=
  (Midfall.LoweringV2.freeNames (abiGuardBlock m ++ mainAsmRaw pv m)).filter
    fun x => x != "vk" && x != "quotientEvaluator"

/-- Every constant line of the rendered `Constants.sol` that declares a `uint256 internal constant`
    has a LITERAL right-hand side (decimal or 0x-hex digits only) - the KAT `Program.lean:55-57`
    asks for and never got. Without it `solConstantLine?` silently mis-parses `sub(0, 0x20)`. -/
def constLinesLiteral (m : Model) : Bool :=
  ((renderConstants (partialCtxOfVerifier m)).splitOn "\n").all fun l =>
    match l.splitOn "uint256 internal constant " with
    | [_, rest] =>
        (match rest.splitOn "=" with
         | [_, rhs] =>
             let v := ((rhs.splitOn ";").headD "").trimAscii.toString
             let digits := if v.startsWith "0x" then (v.drop 2).toString else v
             !digits.isEmpty && digits.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
         | _ => false)
    | _ => true

/-- **THE ONE CONSTANTS-COHERENCE CLAUSE.** Four conjuncts, all computations on the render:
    1. first-headline scope: no Direct lowering (its constant lines are free strings);
    2. every constant line parses as a literal;
    3. the table read back from the rendered text IS the data-level table of the plan view;
    4. no name is declared twice, and every name the program reads is declared. -/
def constsCoherent (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone &&
  constLinesLiteral m &&
  constTableOf m == expectedConsts pv m &&
  decide (((expectedConsts pv m).map Prod.fst).Nodup) &&
  (progConstNames pv m).all fun x => ((expectedConsts pv m).map Prod.fst).contains x


mutual
def callSitesE : Expr EVM.Op → List (String × Nat)
  | Expr.call f args => (f, args.length) :: callSitesEs args
  | Expr.builtin _ args => callSitesEs args
  | _ => []
def callSitesEs : List (Expr EVM.Op) → List (String × Nat)
  | [] => []
  | e :: es => callSitesE e ++ callSitesEs es
end

mutual
def callSitesS : Stmt EVM.Op → List (String × Nat)
  | Stmt.block body => callSitesSs body
  | Stmt.funDef _ _ _ body => callSitesSs body
  | Stmt.letDecl _ (some e) => callSitesE e
  | Stmt.assign _ e => callSitesE e
  | Stmt.cond c body => callSitesE c ++ callSitesSs body
  | Stmt.switch c cases dflt =>
      callSitesE c ++ callSitesSC cases ++
        (match dflt with | some d => callSitesSs d | none => [])
  | Stmt.forLoop init c post body =>
      callSitesSs init ++ callSitesE c ++ callSitesSs post ++ callSitesSs body
  | Stmt.exprStmt e => callSitesE e
  | _ => []
termination_by s => sizeOf s
def callSitesSs : List (Stmt EVM.Op) → List (String × Nat)
  | [] => []
  | s :: ss => callSitesS s ++ callSitesSs ss
termination_by ss => sizeOf ss
def callSitesSC : List (Literal × List (Stmt EVM.Op)) → List (String × Nat)
  | [] => []
  | (_, body) :: rest => callSitesSs body ++ callSitesSC rest
termination_by cs => sizeOf cs
end

/-- The functions a block defines at its top level, with their arities. -/
def funSigsOf (blk : YulBlock) : List (String × Nat) :=
  blk.filterMap fun s => match s with | .funDef n ps _ _ => some (n, ps.length) | _ => none

/-- Every user call resolves to a top-level definition of the main block with the same arity;
    no definition is named after a built-in; no name is defined twice. With it, a `.call` node
    can never be a mis-spelled built-in and no run is stuck on an unresolved callee. -/
def callsResolved (main : YulBlock) : Bool :=
  let sigs := funSigsOf main
  (callSitesSs main).all (fun c => sigs.contains c) &&
    sigs.all (fun s => (EVM.parse s.1).isNone) &&
    decide ((sigs.map Prod.fst).Nodup)

/-- No binder of the program - at ANY depth, `boundSs` - is the name of a contract constant (solc
    rejects it too). This is the hypothesis `inline_append` needs, the object text's `noShadow`, and the
    stricter of the two shadowing scans: `noShadowCore` (§D) checks top-level binders only and is the
    face the registered `prog_slices_decompV3` cites, so `programOkB` carries both and
    `noShadow_of_programOk` projects the second. The B-5 hazard is a model constant named `r`: it is
    substituted at every `mulmod(…, r)` site of a standalone slice and not in the program. -/
def noShadowProg (consts : List (String × Nat)) (prog : YulBlock) : Bool :=
  (Midfall.LoweringV2.boundSs prog).all fun x => !(consts.map Prod.fst).contains x

/- The `noShadow` and `callsResolved` witness/falsifier pair is an EVALUATION, not a `decide`:
    both scans end in `List.contains` on strings, whose `Decidable` instance does not reduce in the
    kernel here. See `Deploy.recon1_scans_ok` - a binder named `FR_MODULUS` (as a `let` and as a
    function parameter) is refused, a plain binder passes; a call to a declared function resolves, an
    undeclared call and a function named after a built-in do not. -/

/-- The builtins whose FIRST argument is the gas the frame hands the callee: the four call ops and
    the two create ops. **D-P71 addition 1 (PG-GAS)** reads "gas() occurs only as the gas argument of
    a call", NOT "no gas()": the external-evaluator render calls the evaluator as
    `staticcall(gas(), …)` (D-P72), so "no gas()" would exclude every external-evaluator render and
    every widened one. TOT.1 needs exactly this fact. -/
def takesGasArg : EVM.Op → Bool
  | .call | .staticcall | .delegatecall | .callcode | .create | .create2 => true
  | _ => false

/-- One layer of the gas scan, in the shape of `noWritersStep` (`Bridge.lean:1069`). A call op skips
    its own `gas()` argument and scans the rest; every other op rejects `gas()` in any position, and
    a `gas()` nested inside a call's OTHER arguments is rejected because that position is not a call
    op's first argument. -/
def gasStep : Scan → (Scan → Bool) → Bool
  | .e (.lit _), _ => true
  | .e (.var _), _ => true
  | .e (.builtin op args), rec =>
      if takesGasArg op then
        match args with
        | Expr.builtin EVM.Op.gas [] :: rest => rec (.es rest)
        | _ => rec (.es args)
      else ! (op == EVM.Op.gas) && rec (.es args)
  | .e (.call _ args), rec => rec (.es args)
  | .es [], _ => true
  | .es (e :: rest), rec => rec (.e e) && rec (.es rest)
  | .s (.block body), rec => rec (.b body)
  | .s (.funDef _ _ _ body), rec => rec (.b body)
  | .s (.letDecl _ none), _ => true
  | .s (.letDecl _ (some e)), rec => rec (.e e)
  | .s (.assign _ e), rec => rec (.e e)
  | .s (.cond c body), rec => rec (.e c) && rec (.b body)
  | .s (.switch c cases dflt), rec =>
      rec (.e c) && rec (.cs cases) &&
        (match dflt with | none => true | some d => rec (.b d))
  | .s (.forLoop init c post body), rec =>
      rec (.b init) && rec (.e c) && rec (.b post) && rec (.b body)
  | .s (.exprStmt e), rec => rec (.e e)
  | .s .break, _ => true
  | .s .continue, _ => true
  | .s .leave, _ => true
  | .b [], _ => true
  | .b (s :: ss), rec => rec (.s s) && rec (.b ss)
  | .cs [], _ => true
  | .cs ((_, b) :: rest), rec => rec (.b b) && rec (.cs rest)

/-- Fuel-bounded gas scan; exhaustion answers `false` (R-37), as `noWritersScan` and `exitScan` do. -/
def gasScan : Nat → Scan → Bool
  | 0, _ => false
  | n + 1, sc => gasStep sc (gasScan n)

/-- **D-P71 addition 1.** Every `gas()` of the block is the gas argument of a call. -/
def GasCallOk (b : Block EVM.Op) : Prop := ∃ n, gasScan n (.b b) = true

/-- **THE GAS-FREE SCAN (D-GATE1).** No `gas()` anywhere, function bodies included. Structural in
    the fuel, like `Bridge.noWritersScan`, so `decide` reduces it. Moved here from
    `LoweringV3/Totality.lean` by D-GATE1 so the `programOk` class can carry the clause; TOT.1's
    `GasFreeScan` is its `∃ fuel` face. Ported verbatim from the evidence
    (`GeneratorRows.lean:1215`). -/
def gasFreeScan : Nat → Scan → Bool
  | 0, _ => false
  | n + 1, sc =>
    match sc with
    | .e (.lit _) => true
    | .e (.var _) => true
    | .e (.builtin op args) => !(op == EVM.Op.gas) && gasFreeScan n (.es args)
    | .e (.call _ args) => gasFreeScan n (.es args)
    | .es [] => true
    | .es (e :: rest) => gasFreeScan n (.e e) && gasFreeScan n (.es rest)
    | .s (.block body) => gasFreeScan n (.b body)
    | .s (.funDef _ _ _ body) => gasFreeScan n (.b body)
    | .s (.letDecl _ none) => true
    | .s (.letDecl _ (some e)) => gasFreeScan n (.e e)
    | .s (.assign _ e) => gasFreeScan n (.e e)
    | .s (.cond c body) => gasFreeScan n (.e c) && gasFreeScan n (.b body)
    | .s (.switch c cases dflt) =>
        gasFreeScan n (.e c) && gasFreeScan n (.cs cases) &&
          (match dflt with | none => true | some d => gasFreeScan n (.b d))
    | .s (.forLoop init c post body) =>
        gasFreeScan n (.b init) && gasFreeScan n (.e c) &&
          gasFreeScan n (.b post) && gasFreeScan n (.b body)
    | .s (.exprStmt e) => gasFreeScan n (.e e)
    | .s .break => true
    | .s .continue => true
    | .s .leave => true
    | .b [] => true
    | .b (s :: ss) => gasFreeScan n (.s s) && gasFreeScan n (.b ss)
    | .cs [] => true
    | .cs ((_, b) :: rest) => gasFreeScan n (.b b) && gasFreeScan n (.cs rest)

/-- A block executes no `gas()`. -/
def GasFree (b : Block EVM.Op) : Prop := ∃ n, gasFreeScan n (.b b) = true

/-! ### D-GATE1: `gasFreeScan` cannot see an erased literal

  The same erasure the writer and exit scans use (ST.12, `eraseB`): the wrapper addresses occur
  only as `let` literals, so `eraseB (R.prog 0 0) = eraseB (R.prog vkAddr qAddr)` and the scan
  transfers. This is what turns the `programOk` clause at `0 0` into the leaf at every `vkAddr`. -/

theorem gasFreeScan_erase (n : Nat) : ∀ (sc : Scan),
    gasFreeScan n sc = gasFreeScan n (eraseScan sc) := by
  induction n with
  | zero => intro sc; rfl
  | succ n ih =>
      intro sc
      cases sc with
      | e x =>
          cases x with
          | lit l => rfl
          | var x => rfl
          | builtin op args =>
              show (!(op == EVM.Op.gas) && gasFreeScan n (.es args)) =
                (!(op == EVM.Op.gas) && gasFreeScan n (.es (eraseEs args)))
              rw [ih (Scan.es args)]; rfl
          | call f args =>
              show gasFreeScan n (.es args) = gasFreeScan n (.es (eraseEs args))
              rw [ih (Scan.es args)]; rfl
      | es xs =>
          induction xs with
          | nil => rfl
          | cons a rest =>
              show (gasFreeScan n (.e a) && gasFreeScan n (.es rest)) =
                (gasFreeScan n (.e (eraseE a)) && gasFreeScan n (.es (eraseEs rest)))
              rw [ih (Scan.e a), ih (Scan.es rest)]; rfl
      | s x =>
          refine match x with
          | Stmt.block b => by
              simp only [eraseScan, eraseS]
              show gasFreeScan n (.b b) = gasFreeScan n (.b (eraseB b))
              rw [ih (Scan.b b)]; rfl
          | Stmt.funDef _ _ _ body => by
              simp only [eraseScan, eraseS]
              show gasFreeScan n (.b body) = gasFreeScan n (.b (eraseB body))
              rw [ih (Scan.b body)]; rfl
          | Stmt.letDecl _ val => by
              simp only [eraseScan, eraseS]
              cases val with
              | none => rfl
              | some e =>
                  show gasFreeScan n (.e e) = gasFreeScan n (.e (eraseE e))
                  rw [ih (Scan.e e)]; rfl
          | Stmt.assign _ e => by
              simp only [eraseScan, eraseS]
              show gasFreeScan n (.e e) = gasFreeScan n (.e (eraseE e))
              rw [ih (Scan.e e)]; rfl
          | Stmt.cond c body => by
              simp only [eraseScan, eraseS]
              show (gasFreeScan n (.e c) && gasFreeScan n (.b body)) =
                (gasFreeScan n (.e c) && gasFreeScan n (.b (eraseB body)))
              rw [ih (Scan.b body)]; rfl
          | Stmt.switch c cs d => by
              simp only [eraseScan, eraseS]
              show (gasFreeScan n (.e c) && gasFreeScan n (.cs cs) &&
                    match d with | none => true | some db => gasFreeScan n (.b db)) =
                   (gasFreeScan n (.e c) && gasFreeScan n (.cs (eraseCs cs)) &&
                    match eraseOd d with | none => true | some db => gasFreeScan n (.b db))
              rw [ih (Scan.cs cs)]
              cases d with
              | none => rfl
              | some db =>
                  show (gasFreeScan n (.e c) && gasFreeScan n (.cs (eraseCs cs)) &&
                        gasFreeScan n (.b db)) =
                       (gasFreeScan n (.e c) && gasFreeScan n (.cs (eraseCs cs)) &&
                        gasFreeScan n (.b (eraseB db)))
                  rw [ih (Scan.b db)]; rfl
          | Stmt.forLoop init c post body => by
              simp only [eraseScan, eraseS]
              show (gasFreeScan n (.b init) && gasFreeScan n (.e c) &&
                    gasFreeScan n (.b post) && gasFreeScan n (.b body)) =
                   (gasFreeScan n (.b (eraseB init)) && gasFreeScan n (.e c) &&
                    gasFreeScan n (.b (eraseB post)) && gasFreeScan n (.b (eraseB body)))
              rw [ih (Scan.b init), ih (Scan.b post), ih (Scan.b body)]; rfl
          | Stmt.exprStmt e => by
              simp only [eraseScan, eraseS]
          | Stmt.break => rfl
          | Stmt.continue => rfl
          | Stmt.leave => rfl
      | b bs =>
          induction bs with
          | nil => rfl
          | cons a rest =>
              show (gasFreeScan n (.s a) && gasFreeScan n (.b rest)) =
                (gasFreeScan n (.s (eraseS a)) && gasFreeScan n (.b (eraseB rest)))
              rw [ih (Scan.s a), ih (Scan.b rest)]; rfl
      | cs xs =>
          induction xs with
          | nil => rfl
          | cons p rest =>
              show (gasFreeScan n (.b p.2) && gasFreeScan n (.cs rest)) =
                (gasFreeScan n (.b (eraseB p.2)) && gasFreeScan n (.cs (eraseCs rest)))
              rw [ih (Scan.b p.2), ih (Scan.cs rest)]; rfl

/-- The congruence form: two scans with the same erasure have the same answer. -/
theorem gasFreeScan_congr (n : Nat) (sc₁ sc₂ : Scan)
    (h : eraseScan sc₁ = eraseScan sc₂) : gasFreeScan n sc₁ = gasFreeScan n sc₂ :=
  calc gasFreeScan n sc₁ = gasFreeScan n (eraseScan sc₁) := gasFreeScan_erase n sc₁
    _ = gasFreeScan n (eraseScan sc₂) := congrArg (gasFreeScan n) h
    _ = gasFreeScan n sc₂ := (gasFreeScan_erase n sc₂).symm

/-- `GasFree` is a statement about the erased block only. -/
theorem gasFree_of_eraseB_eq {b₁ b₂ : Block EVM.Op} (h : eraseB b₁ = eraseB b₂)
    (hg : GasFree b₁) : GasFree b₂ := by
  obtain ⟨n, hn⟩ := hg
  exact ⟨n, by
    rw [gasFreeScan_congr n (.b b₂) (.b b₁) (congrArg Scan.b h.symm)]
    exact hn⟩

/-- The program's gas scan does not see the two wrapper addresses (D-GATE1). PROVED from the
    erasure identity `eraseB_asmOf_eq` and `gasFreeScan_erase`: this is the address independence
    `gasFree_of_valid` needs, at both addresses, not just `0 0`. -/
theorem gasFree_prog_addr_indep (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256)
    (hg : GasFree (R.prog 0 0)) : GasFree (R.prog vkAddr qAddr) :=
  gasFree_of_eraseB_eq (eraseB_asmOf_eq R.pv R.model 0 0 vkAddr qAddr) hg

/-- WITNESS: a call's own `gas()` passes the scan - the arm that "no gas()" would have excluded, and
    the arm every external-evaluator render lives in. PROVED by `decide`. -/
theorem gasCallOk_witness : GasCallOk (yul% {
    if iszero(staticcall(gas(), 0x0b, 0, 0x100, 0x80, 0x80)) { revert(0, 4) }
    mstore(4096, 1)
    return(4096, 32) }) :=
  ⟨16, by decide⟩

/-- FALSIFIER: the same `gas()` outside a call's gas argument - as a value, as a call's SECOND
    argument, and inside a call's offset argument - is refused at the fuel that accepts the witness;
    zero fuel refuses even the empty block (R-37). PROVED by `decide`. -/
theorem gasCallOk_refuses :
    gasScan 16 (.b (yul% { mstore(0, gas()) })) = false ∧
    gasScan 16 (.b (yul% { pop(gas()) })) = false ∧
    gasScan 16 (.b (yul% { let a := staticcall(0, gas(), 0, 0, 0, 0) })) = false ∧
    gasScan 16 (.b (yul% { let a := staticcall(gas(), 0x0b, gas(), 0, 0, 0) })) = false ∧
    gasScan 0 (.b (yul% { })) = false := by
  decide

/-- Two half-open byte ranges meet. -/
def spansMeet (a b : Nat × Nat) : Bool := !(a.1 + a.2 ≤ b.1 || b.1 + b.2 ≤ a.1)

/-- The bytes the transcript parser writes into memory: every walk window, each base paired with the
    length of the section walked into it (`GenAst.g1WalkLoop` bounds each loop by its section's
    `byteLen`): the six commitment bases, the two single-absorb destinations and the evals run. -/
def walkWindowsOf (pv : PlanView) : List (Nat × Nat) :=
  let M := pv.memory
  let L := pv.proofLayout
  let sum (ss : List ProofSection) : Nat := (ss.map (·.byteLen)).foldl (· + ·) 0
  [ (ptrAddr M.adviceCommsMptrBase, sum L.advicePhases),
    (ptrAddr M.lookupMCommsMptrBase, L.lookupMultiplicities.byteLen),
    (ptrAddr M.permZCommsMptrBase, L.permutationProducts.byteLen),
    (ptrAddr M.lookupHelperCommsMptrBase, sum (L.lookups.map (·.helpers))),
    (ptrAddr M.trashcanCommsMptrBase, L.trash.byteLen),
    (ptrAddr M.quotientLimbCommsMptrBase, L.quotientLimbs.byteLen),
    (ptrAddr M.fComMptr, L.fCom.byteLen),
    (ptrAddr M.piMptr, L.pi.byteLen),
    (ptrAddr M.reversedEvalsMptr, L.evals.byteLen) ]

/-- The longest run of absorbs between two squeezes: one whole section (each walk absorbs its section
    before the squeeze that follows it), or the instance run, absorbed at 128 bytes per instance. -/
def longestAbsorbRunOf (pv : PlanView) (numInstances : Nat) : Nat :=
  let L := pv.proofLayout
  (L.advicePhases.map (·.byteLen) ++
    [L.lookupMultiplicities.byteLen, L.permutationProducts.byteLen, L.trash.byteLen,
      L.quotientLimbs.byteLen, L.evals.byteLen, L.qEvals.byteLen,
      128 * numInstances]).foldl Nat.max 0

/-- **D-P71 addition 2 (PG-TPBUF), stated as a CLAUSE and not as a lemma, and the reason is
    measured: it does NOT follow from `memory.map.WellFormed`.** Two independent reasons, both in the
    tree. (1) `WellFormed` is PHASE-SCOPED: it routes disjointness through `memoryLifetimeIntersects`
    (`Layout.lean:1114-1119`), and gate 14 of `LayoutMemory.lean:884-911` measures FIFTY-FOUR pairs of
    poseidon regions that share bytes under it while the global byte-disjointness predicate on the
    same map is FALSE - so `SupportedV2.layout` cannot give byte-disjointness between the transcript
    region and a walk window. (2) `WellFormed` bounds a region START by `0x80` and checks alignment
    and NOTHING about capacity (gate 15, `LayoutMemory.lean:928-960`: "WellFormed IS strictly weaker
    than `validate`"); the absorb run is a capacity demand. ROW.TP step 3 was to check which - this is
    the check, and the answer is "clause". -/
def transcriptRegionOk (pv : PlanView) (numInstances : Nat) : Bool :=
  match pv.memory.map.region "transcript_buffer" with
  | none => false
  | some t => decide (longestAbsorbRunOf pv numInstances ≤ t.len) &&
      (walkWindowsOf pv).all fun w => !spansMeet (t.start, t.len) w

/-- **D-P71 addition 3 (PG-G1ID).** `EntryFrameV3'` was declined under D-P64, so the only memory the
    frame knows is zero is what `ZeroAbove` gives from `0x80` up: the `g1_identity` window that
    `BaseInv .start` pins to zero has to lie above that floor. A REAL restriction, not a formality:
    the default layout puts `g1IdentityMptr` at 0 (`Layout.lean:1732`). -/
def g1IdentityFloor (pv : PlanView) : Bool := decide (0x80 ≤ ptrAddr pv.memory.g1IdentityMptr)

/-- **D-P71 addition 4 (PG-NEGLAG).** The block reads `l_blind` from word 1 and starts the instance
    walk at `max 2 numNegLagranges` (`GenAst.lean:727-733`), so at `numNegLagranges < 2` it computes
    values the Lean verifier does not. `EnvAgrees.negLagranges` gives
    `numNegLagranges = blindingFactors.toOption.getD 0 + 1`, which is 1 when `blindingFactors` is an
    error - so this does NOT follow from the frozen `EnvAgrees`, and step 4 deletes the
    `WellFormedV3` that did not carry it either. A REAL restriction. -/
def negLagrangesFloor (pv : PlanView) : Bool := decide (2 ≤ pv.numNegLagranges)

/-- The card's clause-2 addition: the calldata length the contract expects fits a word, as a
    computation (the `Prop` face is `EntryFrameV3.cdSize`). -/
def cdBoundB (pv : PlanView) (numInstances : Nat) : Bool :=
  decide (pv.proofLayout.proofEnd + 32 + 32 * numInstances < 2 ^ 256)

/-- The card's clause-2 addition, and the one `SimPins` field that is a program fact: some static
    point set has two points, so the `x = 0` row of the fault table is discharged by a revert in the
    PCS block (Lean and Rust deduplicate opening points BY VALUE, `Kzg/Utils.lean:137`). -/
def hasMultiPointSet (pv : PlanView) : Bool :=
  match Midfall.Generator.intermediateSets pv.meta_ pv.dat with
  | .ok s => (s.pointSets.any fun ps => decide (2 ≤ ps.length))
  | .error _ => false

/-- **D-P59's repaired `WellFormed.permutationCommitmentsMatch`, kept as a computation.** Step 4
    deletes `WellFormedV3`, and `supported` is the FROZEN `SupportedV2`, whose `wf` field still means
    `divCeil columns (csDegree - 2)` - FALSE at the deployment (8 against 3, `Deploy`'s
    `wellFormedPermCounts_ok`) and repaired by R.7. The corrected clause is one sigma commitment per
    permutation COLUMN (`keygen.rs:244-250`, `permutation.rs:123`); it lives here until R.7 merges, at
    which point it is `supported.wf.permutationCommitmentsMatch` and can be dropped from here. -/
def permCommMatchRepaired (vk : VerifyingKey (Fr p) G₁) : Bool :=
  vk.permutation.commitments.size == vk.cs.permutation.columns.size

/-- **THE ADDRESS-FIT INVARIANT (D-QVM1, signed 2026-11-21).** The port keeps `usize` addresses as
    `Nat`, so a pointer plus a window length can pass `2^256` even though the emitted Yul registers
    are 256-bit words. The QVM window counterexample (`qinterpRefines_qvmLoop_row_is_false`, BOXD)
    and VKFIT's `fit1`/`fit2` are both instances of that one model gap. This is the computation the
    program clause checks: every region the emitted code addresses must lie below `2^256`.

    The `vk` half is the payload VkLoading copies; the `quotientProgram` half is the interpreter's
    own window. `quotientProgram = none` is the direct-lowering case, which uses no QVM window. -/
def quotientProgramFits (p : QuotientProgram) : Prop :=
  p.programMptr + p.len < 2 ^ 256 ∧
  p.constMptr + 32 * (p.guards.constMax + 1) < 2 ^ 256 ∧
  p.stackMptr ≤ p.guards.stackLast ∧
  p.guards.stackLast + 32 < 2 ^ 256 ∧
  p.evalNumerMptr + 32 < 2 ^ 256 ∧
  p.traceIdMptr + 32 < 2 ^ 256 ∧
  p.selectorPowerMptr + 32 * (p.selectorMaxPower + 1) < 2 ^ 256

/-- **D-GATE8 (signed 2026-11-23): THE STATIC WORKING-SET FIT.** `traceU256Mptr` is the
    aligned maximum of every registered static region end (`LayoutMemory`'s `traceU256Bound`,
    twenty-three candidates including the challenge and theta blocks, the VK payload, the
    commitment census, the pairing scratch, and the PCS tables); the log word itself is one
    `wordBytes` cell at that address. Bounding `traceU256Mptr + wordBytes` therefore bounds
    every static region the emitted code addresses, in particular the pairing slots
    `pairingLhsMptr`/`pairingRhsMptr` and the G2 header pointers inside the VK payload.
    The VK-only bounds below are NOT enough: `MemoryPairs.new_vkMptr_image_unbounded` shows the
    post-payload `allocAfter` chain can cross `2^256`, where the emitted `BitVec.ofNat 256`
    register wraps (A11's `PG-PAIRINGFIT` falsifier). -/
def staticWorkingSetFits (pv : PlanView) : Prop :=
  pv.memory.traceU256Mptr + Midfall.Generator.wordBytes < 2 ^ 256

/-- **D-GATE9 (signed 2026-11-23): THE BATCH-INVERT SCRATCH FLOOR.** The batch-inversion
    helper subtracts 32 from `mptr` while walking backwards, so the scratch window must start
    above the EVM's 0x40 scratch. `LayoutMemory` allocates it at `selectorAccMptr`, far above
    the floor, but `WellFormed` carries no pointer lower bound; A4's lag call needs this one
    clause. It is a layout fact, not a row hypothesis. -/
def batchInvertScratchFits (pv : PlanView) : Prop :=
  32 ≤ pv.memory.batchInvertScratchMptr

def programFits (pv : PlanView) (m : Model) : Prop :=
  ptrAddr pv.memory.vkMptr + pv.vk.len < 2 ^ 256 ∧
  ptrAddr pv.memory.vkMptr + pv.vk.runtimeLen < 2 ^ 256 ∧
  staticWorkingSetFits pv ∧
  batchInvertScratchFits pv ∧
  match m.quotientProgram with
  | some p => quotientProgramFits p
  | none => True

/-- The `Bool` face of `quotientProgramFits`; the clauses are explicit so the kernel can compute
    the conjunction without a `Decidable` instance for the `Prop` def. -/
def quotientProgramFitB (p : QuotientProgram) : Bool :=
  decide (p.programMptr + p.len < 2 ^ 256) &&
  decide (p.constMptr + 32 * (p.guards.constMax + 1) < 2 ^ 256) &&
  decide (p.stackMptr ≤ p.guards.stackLast) &&
  decide (p.guards.stackLast + 32 < 2 ^ 256) &&
  decide (p.evalNumerMptr + 32 < 2 ^ 256) &&
  decide (p.traceIdMptr + 32 < 2 ^ 256) &&
  decide (p.selectorPowerMptr + 32 * (p.selectorMaxPower + 1) < 2 ^ 256)

theorem quotientProgramFitB_eq_true_iff {p : QuotientProgram} :
    quotientProgramFitB p = true ↔ quotientProgramFits p := by
  simp only [quotientProgramFitB, quotientProgramFits, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `Bool` face of `programFits`, so the program clause computes it per render. -/
def programFitB (pv : PlanView) (m : Model) : Bool :=
  decide (ptrAddr pv.memory.vkMptr + pv.vk.len < 2 ^ 256) &&
  decide (ptrAddr pv.memory.vkMptr + pv.vk.runtimeLen < 2 ^ 256) &&
  decide (pv.memory.traceU256Mptr + Midfall.Generator.wordBytes < 2 ^ 256) &&
  decide (32 ≤ pv.memory.batchInvertScratchMptr) &&
  match m.quotientProgram with
  | some p => quotientProgramFitB p
  | none => true

theorem programFitB_eq_true_iff {pv : PlanView} {m : Model} :
    programFitB pv m = true ↔ programFits pv m := by
  unfold programFitB programFits staticWorkingSetFits batchInvertScratchFits
  cases m.quotientProgram <;>
    simp [Bool.and_eq_true, decide_eq_true_eq, quotientProgramFitB_eq_true_iff]
    <;> tauto

/-- **ONE BUNDLE FOR THE PROGRAM.** Everything about the emitted program that a computation at a
    render decides: it is the parse of the text (`codegenStruct`, structural) AND the token equality
    the frozen surface states (`codegenAgrees`, the card's "frozen token clause"); its constant table
    is the plan view's (`constsCoherent`); every call resolves; no binder shadows a constant (both the
    object text's every-binder scan and the `noShadowB` face `prog_slices_decompV3` cites); after
    inlining only the wrapper locals are free (`mainClosed`); the transcript base is above Solidity's
    reserved words; and the five D-P71 floors and bounds. -/
def programOkCore (pv : PlanView) (m : Model) (numInstances : Nat)
    (vk : VerifyingKey (Fr p) G₁) : Bool :=
  let main := mainAsmRaw pv m
  let consts := constTableOf m
  codegenStruct main m &&
  codegenAgrees pv m &&
  constsCoherent pv m &&
  callsResolved main &&
  noShadowProg consts (abiGuardBlock m ++ wrapperLocals m 0 0 ++ main) &&
  noShadowCore pv m &&
  mainClosed pv m &&
  decide (0x80 ≤ pv.memory.transcriptMptr) &&
  cdBoundB pv numInstances &&
  hasMultiPointSet pv &&
  transcriptRegionOk pv numInstances &&
  g1IdentityFloor pv &&
  negLagrangesFloor pv &&
  permCommMatchRepaired vk

/-- The render-level face. The fixture render is `noncomputable` (its model is the typed-in artifact
    value), so `Deploy` evaluates `programOkCore` at the render's own computable fields and
    `programOkB_of_valid` is the projection. -/
def programOkB (R : Render p G₁ G₂ Gₜ) : Bool :=
  programOkCore R.pv R.model R.cfg.numInstances R.vk

/-- **THE PROGRAM CLAUSE**: the bundle above plus the THREE SCANS. All are `∃ n` propositions and
    stay out of the `Bool` so that no fuel is pinned in the statement (section header). ONE exit
    scan (D-P71 addition 5): `ExitDiscipline` is the scan of §I and `ExitShape` below is the SAME
    `exitScan` applied to a different block - there is no second scan function in the tree.
    `GasFree` is the D-GATE1 addition: the whole program executes no `gas()` at all, stronger than
    `GasCallOk`'s "only as a call's gas argument"; it is what TOT.1.a's oracle independence needs. -/
def programOk (R : Render p G₁ G₂ Gₜ) : Prop :=
  programOkB R = true ∧ GasCallOk (R.prog 0 0) ∧ GasFree (R.prog 0 0) ∧
    ExitDiscipline (R.prog 0 0) ∧ programFits R.pv R.model

/-- The three names the projections read are in the data table for EVERY plan view and model,
    whatever the four optional arms of the model hold. -/
theorem expectedConsts_lookups (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "FR_MODULUS" = some frModulusConstant ∧
    (expectedConsts pv m).lookup "RETURN_MPTR" = some pv.memory.verifierReturnMptr ∧
    (expectedConsts pv m).lookup "TRANSCRIPT_MPTR" = some pv.memory.transcriptMptr := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- **THE CONSTS-COHERENCE PROJECTION**: the render's table IS the data table, so a lookup in one is
    a lookup in the other. Every table projection below is this lemma plus `expectedConsts_lookups`.
    This is what `GeneratorCertified.lean:458` (`v3_pins_of_valid`) runs on; RECON.1b ports the pin
    bundles through it. -/
theorem lookup_expectedConsts_of_programOkB {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true)
    (name : String) :
    (constTableOf R.model).lookup name = (expectedConsts R.pv R.model).lookup name := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  have hcc := hc.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [constsCoherent, Bool.and_eq_true] at hcc
  rw [eq_of_beq hcc.1.1.2]

/-- **D-P71 addition 6 (PG-FRMOD): NOT a clause.** `FR_MODULUS = p` is `constsCoherent` together with
    `EnvAgrees.modulus`, and here is the proof, so the rows get it as a projection of `hR.program` and
    `hR.env` and the text carries no redundant conjunct. -/
theorem frModulus_of_programOk_of_modulus {R : Render p G₁ G₂ Gₜ}
    (hp : programOkB R = true) (hmod : p = frModulusConstant) :
    R.consts.lookup "FR_MODULUS" = some p := by
  have h : (constTableOf R.model).lookup "FR_MODULUS" = some frModulusConstant := by
    rw [lookup_expectedConsts_of_programOkB hp, (expectedConsts_lookups R.pv R.model).1]
  exact h.trans (congrArg Option.some hmod.symm)

/-- **D-P71 addition 7: NOT a clause either.** `returnMptr` (`Valid.returnMptr`, the clause Q0.5 added
    to the frozen surface) is carried over as a THEOREM of the single text: the table IS
    `expectedConsts`, and `expectedConsts` declares `RETURN_MPTR`. This is the object text's
    `Render.ValidV3.returnMptr_const`, restated for the reconciled clause; the TraceReturn progress
    row reads exactly this. -/
theorem returnMptr_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    ∃ m, R.consts.lookup "RETURN_MPTR" = some m := by
  refine ⟨R.pv.memory.verifierReturnMptr, ?_⟩
  show (constTableOf R.model).lookup "RETURN_MPTR" = some R.pv.memory.verifierReturnMptr
  rw [lookup_expectedConsts_of_programOkB hp, (expectedConsts_lookups R.pv R.model).2.1]

/-- The two D-P71 floors as `Prop`s the rows cite, discharged from the bundle. -/
theorem g1IdentityFloor_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    0x80 ≤ ptrAddr R.pv.memory.g1IdentityMptr := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.1.2

theorem negLagranges_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    2 ≤ R.pv.numNegLagranges := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.2

/-- **THE GENERATED-BY CLAUSE** (the object text's `Render.GeneratedBy`, `ObjectV3Full.lean:615`): the
    plan, the compact quotient blocks and the model are what `generateAll` returns for THIS render's
    own verifier-side inputs - including `R.E.delta`, which is how DELTA reaches the program text
    (finding H-7). It replaces the frozen clauses 1-4 (`circuitMeta`, `layout`, `invariants`,
    `model`), the `validate_layout` gap B-7, the VM-lowering gap B+3 and `vkPins.numInst`. -/
def generated (R : Render p G₁ G₂ Gₜ) : Except Fault GenOut :=
  generateAll Features.solidity R.E.delta R.vk R.cfg R.plan.vk R.inputs R.flags

def GeneratedBy (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ out, generated R = .ok out ∧ out.plan = R.plan ∧ out.qblocks = R.qblocks ∧ out.model = R.model


/-! ## §V. VALIDITY, V3 - THE SINGLE TEXT (RECON.1)

  ONE structure. The base is the object text's seven clauses (`ObjectV3Full.lean:762-779`); the
  eighteen-clause draft of `StatementsV3.lean:613` is the FALLBACK if D-P67 is struck and stays in the
  evidence directory, not here (the card's Guidance). Where the two texts disagreed:

  * `circuitMeta`, `layout`, `invariants`, `model` (four clauses of the 18-clause text) collapse into
    `generated` - the object text's `GeneratedBy`, which is what the card's step 1 ("take the object
    text's seven-clause structure as the base") means in practice. `PlanMeta` stays defined above
    because `Deploy` and `Falsifiers` measure it; it is no longer a clause.
  * `noShadow`: the object text scans EVERY binder (`boundSs`); the 18-clause text scanned top-level
    binders only (`noShadowCore`). Both are conjuncts of `programOkB` - not a union of two texts but a
    strictness ordering: the every-binder scan is the one `inline_append` needs, and the top-level face
    is the one the registered `prog_slices_decompV3` cites. Neither is dropped; `noShadow_of_programOk`
    projects the second.
  * `exitDiscipline`: kept, as ONE scan, inside `programOk` (addition 5).
  * `gasFree`: D-GATE1, inside `programOk`: no `gas()` anywhere in the program (the TOT.1 leaf's
    projection; `GasCallOk` alone permits a call's own `gas()` argument).
  * `cdBound`, `transcriptMptr`, `vkPins`, `vkProgressPins`: the first two are conjuncts of
    `programOkB`; the pin bundles are NOT clauses - `constsCoherent` is, and `vkPins` /
    `vkProgressPins` / `transcriptMptr` are theorems of it (`GeneratorCertified.lean:458` proves the
    bundle; RECON.1b ports it).
  * `payload`: the object text's field list - `digest` in, `delta` out (card step 3).
  * `supported : SupportedV2 R` (frozen), NOT `SupportedV3`: step 4 deletes `SupportedV3` and
    `WellFormedV3`. The repaired permutation clause that `WellFormedV3.wf` carried is kept as
    `permCommMatchRepaired`, a conjunct of `programOkB`, because `SupportedV2` is frozen and cannot
    gain a field; `supported.wf` is refuted at the deployment until R.7 merges and this card reports
    that rather than weakening it. -/

/-- **VALIDITY, V3 - THE ONE TEXT.** Seven clauses in four groups: what the generator produced
    (`generated`, `inputs`), what the program is (`program`, `noWriters`), what the environment and the
    payload say (`env`, `payload`), and the scope (`supported`). Every clause except the five
    codec-bearing fields of `payload` and `SupportedV2.vkPoints` is decided by computation at a
    deployment; the clause table is in `Midfall/Instances/StatementsV3Deploy.lean`. -/
structure ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- G. Plan, compact quotient blocks and model are the generator's output for THIS constraint
      system, configuration, payload and DELTA (the object text's clause 1). -/
  generated : GeneratedBy R
  /-- G. The build inputs are the configuration's and the key's (frozen clause 5, unchanged; the
      18-clause text's `inputs` is verbatim the same). -/
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  /-- P. The program checks: one decidable bundle plus the two scans (D-P71 additions 1-5 and the
      card's four additions, all inside). -/
  program : programOk R
  /-- P. No world write (frozen clause 10, unchanged). -/
  noWriters : NoWriters (R.prog 0 0)
  /-- K. Field, domain and G2 parameters agree (frozen clause 8, unchanged). Carries
      `modulus : p = frModulusConstant`, which with `constsCoherent` is PG-FRMOD (addition 6). -/
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  /-- K. Every payload word is the Lean key's. -/
  payload : PayloadAgrees R
  /-- S. Scope (frozen `SupportedV2`; `wf.permutationCommitmentsMatch` is repaired by R.7 and kept in
      the meantime as `permCommMatchRepaired`). -/
  supported : SupportedV2 R

/-! ### Projections: what the rows and the headline used to read off the eighteen-clause text. -/

theorem programOkB_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : programOkB R = true :=
  hR.program.1

/-- The address-fit conjunct of the program clause (D-QVM1). -/
theorem programFit_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    programFits R.pv R.model :=
  hR.program.2.2.2.2

/-- **D-GATE8 projection**: the full static working set fits a word. -/
theorem staticWorkingSetFits_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    staticWorkingSetFits R.pv :=
  (programFit_of_valid hR).2.2.1

/-- **D-GATE9 projection**: the batch-invert scratch starts above the EVM scratch. -/
theorem batchInvertScratchFits_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    batchInvertScratchFits R.pv :=
  (programFit_of_valid hR).2.2.2.1

/-- The interpreter's own window, at the model's quotient program. -/
theorem quotientProgramFits_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R)
    {p : QuotientProgram} (hp : R.model.quotientProgram = some p) :
    quotientProgramFits p := by
  have h := programFit_of_valid hR
  unfold programFits at h
  rw [hp] at h
  exact h.2.2.2.2

theorem noShadow_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    noShadowCore R.pv R.model = true := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.1.1.1.2

theorem cdBound_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256 := by
  have hc := programOkB_of_valid hR
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.1.1.1.1.2

theorem hasMultiPointSet_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    hasMultiPointSet R.pv = true := by
  have hc := programOkB_of_valid hR
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.2

theorem transcriptMptr_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t := by
  have hc := programOkB_of_valid hR
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  refine ⟨R.pv.memory.transcriptMptr, ?_, of_decide_eq_true hc.1.1.1.1.1.1.2⟩
  show (constTableOf R.model).lookup "TRANSCRIPT_MPTR" = some R.pv.memory.transcriptMptr
  rw [lookup_expectedConsts_of_programOkB (programOkB_of_valid hR),
    (expectedConsts_lookups R.pv R.model).2.2]
theorem frModulus_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.consts.lookup "FR_MODULUS" = some p :=
  frModulus_of_programOk_of_modulus (programOkB_of_valid hR) hR.env.modulus

theorem returnMptr_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ∃ m, R.consts.lookup "RETURN_MPTR" = some m :=
  returnMptr_of_programOk (programOkB_of_valid hR)

/-- (`g1IdentityAbove`, §E, is this same inequality stated at the render.) -/
theorem g1IdentityFloor_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    0x80 ≤ ptrAddr R.pv.memory.g1IdentityMptr :=
  g1IdentityFloor_of_programOk (programOkB_of_valid hR)

theorem negLagranges_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    2 ≤ R.pv.numNegLagranges := negLagranges_of_programOk (programOkB_of_valid hR)

theorem exitDiscipline_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ExitDiscipline (R.prog 0 0) := hR.program.2.2.2.1

theorem gasCallOk_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : GasCallOk (R.prog 0 0) :=
  hR.program.2.1

/-- **D-P71 addition 5, discharged.** The rows' exit notion (`SoundnessV3`'s `Render.ExitOk`,
    `ExitShape (R.preBlock 0 ++ R.slices6)`) is NOT a second scan: it is the SAME `exitScan` of §I
    applied to a different block, and it is a consequence of the one clause the text carries. The
    block-level half is proved here; the render-level bridge
    (`returnTail? (R.prog 0 0) = some (R.preBlock 0 ++ R.slices6 ++ …)`) is the program decomposition
    `prog_slices_decompV3` already registers as an obligation, and RECON.1b joins the two. -/
def ExitShape (b : Block EVM.Op) : Prop := ∃ n, exitScan n false false (.b b) = true

theorem exitShape_of_exitDiscipline {b : Block EVM.Op} (init : Block EVM.Op)
    (h : ExitDiscipline b) (ht : returnTail? b = some init) : ExitShape init := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simpa [exitDisciplineFuel, ht] using hn⟩

/-! ## §E. EntryFrameV3 (e)

  OLD (`Statements.lean:240-247`): five fields, no bound on the calldata. `calldatasize` is
  `BitVec.ofNat 256 st.env.calldata.length` (`EVMExec.lean:792`) while `decodeCalldata` compares
  `cd.size` in `Nat` (`Calldata.lean:341`), so `cd ++ (2^256 zero bytes)` runs exactly like `cd`
  and is rejected by Lean: conjunct 1 is false.

  NEW: `cdSize : cd.size < 2 ^ 256` (D-P64/ST.4) plus **D-GATE19's `cdSize36 : cd.size < 2 ^ 36`**.
  `cdSize` is the word-length repair; `cdSize36` is the genuine entry/calldata premise that
  `Decoded` turns into `numInstances < 2^31`, and it is the field `pfx_stageInv_start` reads into
  the initial `Frame.cdSize36`. It is an entry witness, not a row/bundle/`ValidV3` field. -/

/-- **TRUSTED.** As `LoweringV2.EntryFrame`, plus the calldata length bound. -/
structure EntryFrameV3 (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (st : EvmState) : Prop where
  shape : ∃ (mem₀ : Nat → UInt8) (aw : U256),
    st = { initState W Lyt H cd mem₀ with activeWords := aw }
  zeroAbove : ZeroAbove st.memory
  fmp : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ (loadWord st.memory 0x40).toNat ≤ t
  callvalue : st.env.callvalue = 0
  selector : bytesTake cd 0 4 = some fnSigVerifyProof
  /-- ADDED: the calldata length is a word. -/
  cdSize : cd.size < 2 ^ 256
  /-- **D-GATE19: the genuine entry calldata bound.** See `EntryFrame.cdSize36`;
      this is the entry witness that feeds `pfx_stageInv_start` and hence the
      initial `Frame.cdSize36`. -/
  cdSize36 : cd.size < 2 ^ 36

/-- The V3 frame is a V2 frame: nothing proved from `EntryFrame` is lost. PROVED. -/
theorem EntryFrameV3.toV2 {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st : EvmState} (h : EntryFrameV3 R W Lyt H cd st) :
    EntryFrame R W Lyt H cd st :=
  ⟨h.shape, h.zeroAbove, h.fmp, h.callvalue, h.selector, h.cdSize, h.cdSize36⟩

/-- **INHABITATION**, the V3 form of `Blocks.lean:624 entryFrame_inhabited`: one more premise
    (`hcd`), the same witness. PROVED. -/
theorem entryFrame_inhabitedV3 (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) (hcv : W.callvalue = 0)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t)
    (hcd : cd.size < 2 ^ 256) (hcd36 : cd.size < 2 ^ 36) :
    ∃ st₀, EntryFrameV3 R W Lyt H cd st₀ := by
  refine ⟨initState W Lyt H cd (fun _ => 0), ⟨fun _ => 0, 0, rfl⟩, ?_, ?_, hcv, hsel, hcd, hcd36⟩
  · exact fun a _ => rfl
  · obtain ⟨t, ht₁, ht₂⟩ := ht
    refine ⟨t, ht₁, ?_⟩
    have h0 : (loadWord ((initState W Lyt H cd (fun _ : Nat => (0 : UInt8)))).memory 0x40).toNat
        = 0 := by
      show (loadWord (fun _ : Nat => (0 : UInt8)) 0x40).toNat = 0
      decide
    rw [h0]; omega

/-- OPTION (finding A-9, a DECISION): zero from the generator's own `TRANSCRIPT_MPTR` up, instead
    of from `0x80`. This is what the on-chain MF-2 guard supports: a fresh frame is zero above
    solc's initial free-memory pointer, the guard enforces `fmp ≤ TRANSCRIPT_MPTR`, and solc may
    have spilled into `[0x80, fmp)`. Strictly weaker than `EntryFrameV3` (lemma below), so it
    covers MORE frames; the price is one decidable pin (`g1IdentityAbove`). -/
structure EntryFrameV3' (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (st : EvmState) : Prop where
  shape : ∃ (mem₀ : Nat → UInt8) (aw : U256),
    st = { initState W Lyt H cd mem₀ with activeWords := aw }
  /-- The free-memory pointer is at or below `TRANSCRIPT_MPTR`, and memory is zero from there. -/
  fmpZero : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧
    (loadWord st.memory 0x40).toNat ≤ t ∧ ∀ a, t ≤ a → st.memory a = 0
  callvalue : st.env.callvalue = 0
  selector : bytesTake cd 0 4 = some fnSigVerifyProof
  cdSize : cd.size < 2 ^ 256

/-- `EntryFrameV3` implies the option when `TRANSCRIPT_MPTR ≥ 0x80` (`Valid.transcriptMptr`).
    PROVED: the option is the weaker assumption. -/
theorem EntryFrameV3.toOption {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st : EvmState} (h : EntryFrameV3 R W Lyt H cd st)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t) :
    EntryFrameV3' R W Lyt H cd st := by
  obtain ⟨t, ht₁, ht₂⟩ := ht
  obtain ⟨t', ht'₁, ht'₂⟩ := h.fmp
  have htt : t' = t := Option.some.inj (ht'₁.symm.trans ht₁)
  subst htt
  exact ⟨h.shape, ⟨t', ht₁, ht'₂, fun a ha => h.zeroAbove a (le_trans ht₂ ha)⟩, h.callvalue,
    h.selector, h.cdSize⟩

/-- The pin the option needs: the `g1_identity` window `Inv` pins to zero at every checkpoint
    lies at or above `TRANSCRIPT_MPTR`. Decidable. -/
def g1IdentityAbove (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ t ≤ ptrAddr R.pv.memory.g1IdentityMptr

/-! ## §F. Totality (f)

  OLD: none. Conjuncts 1 and 3 of the frozen headline are ∀-runs statements; nothing says the
  modelled program has a run on calldata the Lean verifier rejects.

  WHICH STATEMENT IS THE RIGHT ONE.
  * Gas. `gas()` is the one builtin whose step is `∃ w, g.Gas st w ∧ ...`
    (`EVMExec.lean`, `builtinWithExternal`): under `ExternalGas.none` it is stuck. The supported
    renders never emit `gas()` (trace, gas checkpoints and the external evaluator are excluded by
    `SupportedV3`), so existence holds for every oracle there - but that needs one more scan. The
    statement below asks for a TOTAL oracle instead, which is what a real chain provides and what
    stays true when the scope restrictions are lifted.
  * Calls. `permissive c` admits the failed response to every request (`Bridge.lean:1433
    permissive_failResp_call`). So "a permissive run exists" is witnessed by the run whose FIRST
    precompile call fails and which then reverts through `fail(ERR_PRECOMPILE_FAILED)`: it says
    nothing about the paths on which the precompiles answer. The statement that makes the ∀-runs
    conjuncts non-vacuous on a real chain is existence under the HONEST relation `callsOf product`.
    An honest run is a permissive run (`runBody_mono` below), so the permissive form follows. -/

/-- The gas oracle answers in every state. `ExternalGas.ofFun f` and `ExternalGas.any` are total;
    `ExternalGas.none` is not. -/
def GasTotal (g : ExternalGas) : Prop := ∀ st, ∃ w, g.Gas st w

theorem gasTotal_ofFun (f : EvmState → U256) : GasTotal (ExternalGas.ofFun f) :=
  fun st => ⟨f st, rfl⟩

theorem gasTotal_any : GasTotal ExternalGas.any := fun _ => ⟨0, trivial⟩

theorem not_gasTotal_none : ¬ GasTotal ExternalGas.none := fun h => (h EvmState.init).elim fun _ hw => hw

/-- **TOTALITY.** From every entry frame of a deployed render, under the honest precompiles and
    any total gas oracle, the body has a run - whatever the calldata. -/
def BodyTotal (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (vkAddr : U256)
    (st₀ : EvmState) : Prop :=
  ∀ g : ExternalGas, GasTotal g → ∃ obs, RunBody R vkAddr 0 (callsOf product) g st₀ obs

/-- The honest relation never reports a world change (`ofOutcome`, `failResp`,
    `Bridge.lean:689-696`), so an honest response is a permissive response. PROVED from
    `Bridge.honest_le_permissive`. -/
theorem callsOf_le_permissive (product : PairingProduct) :
    ∀ req st r, (callsOf product).Call req st r → (permissive (callsOf product)).Call req st r := by
  refine honest_le_permissive (callsOf product) ?_
  intro req st r h
  rcases h with h | ⟨_, hF⟩
  · simp only [honestOf, Option.map_eq_some_iff] at h
    obtain ⟨rel, _, hr⟩ := h
    rw [← hr]
    split <;> rfl
  · exact hF.elim

/-- A run under a call relation is a run under any larger one. OBLIGATION (Bridge layer).
    Experiment: induction on `Step`; the call relation occurs only in `externalCall`
    (`EVMExec.lean`), in a positive position. -/
theorem runBody_mono (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256) (c c' : ExternalCalls)
    (g : ExternalGas) (st₀ : EvmState) (obs : Obs)
    (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    (h : RunBody R vkAddr qAddr c g st₀ obs) : RunBody R vkAddr qAddr c' g st₀ obs := by
  rw [RunBody] at h ⊢
  obtain ⟨V', hrun⟩ := h
  exact Midfall.LoweringV3.RunMono.RunCommitted_mono (c := c) (c' := c') hcc hrun

/-- CONSEQUENCE, PROVED from `runBody_mono`: totality gives a permissive run, so conjuncts 1 and 3
    are not vacuous at any entry frame. -/
theorem BodyTotal.permissive {R : Render p G₁ G₂ Gₜ} {product : PairingProduct}
    {vkAddr : U256} {st₀ : EvmState}
    (h : BodyTotal R product vkAddr st₀) (g : ExternalGas) (hg : GasTotal g) :
    ∃ obs, RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs := by
  obtain ⟨obs, hobs⟩ := h g hg
  exact ⟨obs, runBody_mono R vkAddr 0 _ _ g st₀ obs (callsOf_le_permissive product) hobs⟩

/-! ## §K. The headline, the gate, end to end (h), (k) -/

/-- `LeanAccepts` is unchanged (`Statements.lean:263-267`). Restated only so that the V3 file
    shows the whole surface; `rfl`. -/
theorem leanAccepts_unchanged (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) :
    LeanAccepts R H cd =
      ∃ ms instW inst,
        decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
        instOfWords? (p := p) instW = some inst ∧
        verifyMsgs (Gₜ := Gₜ) R.E H Features.solidity R.params R.vk inst ms = .ok () := rfl

/-- **LOWERING EQUIVALENCE, V3.** For every world the render is deployed into, every hash, every
    calldata and every entry frame, under honest-or-failing precompiles and a lawful codec:

    1. soundness - a run that returns returns ABI `true`, and the Lean verifier accepts;
    2. completeness - if the Lean verifier accepts, an honest run exists and every honest run
       returns ABI `true` with the world unchanged;
    3. two outcomes - every run returns ABI `true` or is a non-committing halt, world unchanged;
    4. totality - under the honest precompiles and any total gas oracle, a run exists.

    DIFFERENCES FROM `LoweringV2.LoweringEquivalence` (`Statements.lean:298-311`): `EntryFrameV3`
    for `EntryFrame`; the codec laws are a hypothesis of ALL conjuncts (they were a hypothesis of
    conjunct 2 only, and there the frozen seven without the encoder-first law); conjunct 4 is
    new. Conjuncts 1 and 3 are otherwise verbatim. -/
def LoweringEquivalenceV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs → obs.isReturn →
        SoundSide R H cd → obs.returnData = abiTrue ∧ LeanAccepts R H cd) ∧
    (LeanAccepts R H cd → CompleteSide R H cd →
        (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
          obs.view = returnView st₀) ∧
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs →
        obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)) ∧
    BodyTotal R product vkAddr st₀

/-- Conjunct 3 is an instance of `TwoOutcomes`. PROVED: no rejection lemma is involved. -/
theorem conj3_of_twoOutcomes (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (h : TwoOutcomes R) (vkAddr : U256) (st₀ : EvmState) :
    ∀ (g : ExternalGas) (obs : Obs),
      RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs →
      obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀) :=
  fun g obs hobs => h vkAddr (permissive (callsOf product)) g st₀ obs hobs

/-! ### The four obligations the headline decomposes into

  The frozen composition (`Blocks.lean:493 lowering_equivalence_of_blocks`) spends the seven
  `BlockSound` rows in conjunct 1 only to read off `returnData = abiTrue`, and closes conjunct 3
  with the false `rejects_of_not_accepts`. With `TwoOutcomes` both uses disappear: -/

/-- PROGRAM-LEVEL REJECTION, V3 (replaces `Blocks.lean:134 Render.Rejects`). `SoundSide` STAYS (it
    excludes the logup-panic set, where the contract accepts and Lean panics). The conclusion is
    `¬ obs.isReturn`; with `TwoOutcomes` that is the same as `obs.isRevertOrHalt`. This is where
    ALL of "the contract returns, so Lean accepts" lives; the staged per-block rejection
    contracts prove it. -/
def RejectsV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (g : ExternalGas) (obs : Obs),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    SoundSide R H cd → ¬ LeanAccepts R H cd →
    RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs → ¬ obs.isReturn

/-- Conjunct 2, named. -/
def CompleteV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    LeanAccepts R H cd → CompleteSide R H cd →
      (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
      ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
        obs.view = returnView st₀

/-- Conjunct 4, named. -/
def TotalV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    BodyTotal R product vkAddr st₀

/-- **COMPOSITION, V3.** The headline is four independent obligations: `TwoOutcomes` (syntactic),
    `RejectsV3` (soundness), `CompleteV3` (the progress rows) and `TotalV3` (termination and
    non-stuckness). PROVED, no `sorry`: conjunct 1 is `TwoOutcomes` (a returning run returned
    `abiTrue`) plus `RejectsV3` (and Lean accepted); conjunct 3 is `TwoOutcomes`. -/
theorem lowering_equivalenceV3_of (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (h2 : TwoOutcomes R) (hrej : RejectsV3 R product) (hcomp : CompleteV3 R product)
    (htot : TotalV3 R product) : LoweringEquivalenceV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec
  refine ⟨?_, hcomp W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec,
    conj3_of_twoOutcomes R product h2 vkAddr st₀,
    htot W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec⟩
  intro g obs hobs hret hside
  constructor
  · rcases h2 vkAddr _ g st₀ obs hobs with hview | ⟨hrh, _⟩
    · have hh : obs.state.halted = some (.ret, abiTrue) := congrArg ObsView.halted hview
      simp only [Obs.returnData, hh]
    · exact absurd hrh (not_isRevertOrHalt_of_isReturn hret)
  · by_contra hna
    exact hrej W Lyt H vkAddr cd st₀ g obs hdep hentry hpc hcodec hside hna hobs hret

/-- `SoundSide` is implied by `LeanAccepts` (the decode is a function, and an accepting
    `verifyMsgs` did not fault in `prepareMsgs`). PROVED: it is listed in the gate below for
    symmetry with conjunct 1, not as an extra demand. -/
theorem soundSide_of_leanAccepts (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : LeanAccepts R H cd) : SoundSide R H cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, hv⟩ := h
  intro ms' instW' inst' hdec' hinst' hpanic
  rw [hdec] at hdec'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hdec')
  rw [hinst] at hinst'
  obtain rfl := Option.some.inj hinst'
  unfold verifyMsgs at hv
  rw [hpanic] at hv
  cases hv

/-- **NON-VACUITY, V3** (replaces `Statements.lean:317-320` and the D-P45 draft). Every hypothesis
    of `LoweringEquivalenceV3` holds at once, AT KECCAK, with a calldata the Lean verifier
    ACCEPTS and the side conditions admit.

    The hash is `keccak256`, not `∃ H`: `DeploymentV2.vkHash` pins `H` at the VK runtime bytes
    only, so an existential hash is met by a hash constant elsewhere, every challenge is then
    independent of the proof, and `π := 1` with a solved-for `fCom` passes `DualMSM.check` for any
    params (finding H+1). `LeanAccepts` is required because without it the gate is satisfied by a
    codec that decodes nothing. `SoundSide` follows from `LeanAccepts` and is kept for symmetry
    with the hypotheses of conjunct 1. -/
def HypothesesInhabitedV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W keccak256 vkAddr ∧ EntryFrameV3 R W Lyt keccak256 cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ G1CodecHeadlineLaws R.E.g1 ∧
      LeanAccepts R keccak256 cd ∧ SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd

/-- What the gate buys, PROVED: at a render where the gate and the headline both hold, an honest
    run exists and returns ABI `true`. So the two together exclude "the contract never returns". -/
theorem returns_of_inhabited (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hEq : LoweringEquivalenceV3 R product) (hI : HypothesesInhabitedV3 R product) :
    ∃ (vkAddr : U256) (st₀ : EvmState) (obs : Obs),
      RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs ∧
        obs.view = returnView st₀ := by
  obtain ⟨W, Lyt, vkAddr, cd, st₀, hdep, hentry, hpc, hcodec, hacc, _, hcomp⟩ := hI
  obtain ⟨_, h2, _, _⟩ := hEq W Lyt keccak256 vkAddr cd st₀ hdep hentry hpc hcodec
  obtain ⟨⟨obs, hobs⟩, hall⟩ := h2 hacc hcomp
  exact ⟨vkAddr, st₀, obs, hobs, hall obs hobs⟩

set_option linter.unusedVariables false in
/-- **END TO END, V3** (replaces `Statements.lean:347-361`). Differences: `ValidV3`,
    `LoweringEquivalenceV3`, `calldataOfV3`, `EntryFrameV3`, and ONE codec hypothesis
    `G1CodecLawsV3` in place of the two frozen ones (`G1CodecLaws` and `compressedRoundtrip`,
    the second of which is a field of the first). `hcd36` is D-GATE19's named
    entry/calldata premise: the encoder's calldata is inside the genuine `< 2^36`
    entry bound (`Decoded` makes this exactly `numInstances < 2^31`), so the
    backward direction can build an `EntryFrameV3` with `cdSize36`. It is an
    interface premise, not a row/bundle/`ValidV3` field. -/
def EndToEndV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hEq : LoweringEquivalenceV3 R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hcd36 : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 36)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd) : Prop :=
  verifyNative (Gₜ := Gₜ) R.E Features.solidity R.params R.vk inst π = .ok () ↔
    ∃ cd, calldataOfV3 R π inst = .ok cd ∧
      ∀ st₀, EntryFrameV3 R W Lyt keccak256 cd st₀ →
        (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
          obs.view = returnView st₀

/-- The size fact `EndToEndV3`'s right-to-left direction needs to build an entry frame for the
    encoder's output: a calldata the decoder accepts has exactly the expected length, which
    `ValidV3.cdBound` bounds. PROVED for the decoder half (`decodeCalldata`'s seventh guard). -/
theorem cdSize_of_decodes {G : Type} (L : ProofCalldataLayout) (numInstances : Nat)
    (c : G1Codec G) (cd : Bytes) (ms : List (Msg (Fr p) G)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd.size = L.proofEnd + 32 + 32 * numInstances := by
  by_contra hne
  have hnone : decodeCalldata (p := p) L numInstances c cd = none := by
    unfold decodeCalldata
    simp [hne]
  rw [hnone] at h
  cases h

/-! ## Axiom audit of what is PROVED here and what rests on a stated obligation -/

#print axioms withCompressed_lawsV3            -- no sorryAx
#print axioms entryFrame_inhabitedV3           -- no sorryAx
#print axioms EntryFrameV3.toOption            -- no sorryAx
#print axioms callsOf_le_permissive            -- no sorryAx
#print axioms lowering_equivalenceV3_of        -- no sorryAx
#print axioms returns_of_inhabited             -- no sorryAx
#print axioms soundSide_of_leanAccepts         -- no sorryAx
#print axioms cdSize_of_decodes                -- no sorryAx
#print axioms fail_lookupV3                    -- no sorryAx
#check Midfall.LoweringV3.prog_slices_decompV3
#print axioms Midfall.LoweringV3.prog_slices_decompV3   -- no sorryAx (ST.11)
#print axioms Midfall.LoweringV3.hoist_prog_addr_indepV3  -- no sorryAx (ST.11)
#check Midfall.LoweringV3.scans_prog_addr_indep   -- ST.12 (WP-A2): PROVED
#print axioms scans_prog_addr_indep         -- no sorryAx
#print axioms twoOutcomes_of_scans             -- sorryAx: twoOutcomes_of_exitDiscipline
#print axioms programOkB_of_valid                -- no sorryAx
#print axioms frModulus_of_valid                 -- no sorryAx
#print axioms returnMptr_of_valid                -- no sorryAx
#print axioms g1IdentityFloor_of_valid           -- no sorryAx
#print axioms negLagranges_of_valid              -- no sorryAx
#print axioms cdBound_of_valid                   -- no sorryAx
#print axioms hasMultiPointSet_of_valid          -- no sorryAx
#print axioms transcriptMptr_of_valid            -- no sorryAx
#print axioms exitShape_of_exitDiscipline        -- no sorryAx
#print axioms gasCallOk_witness                  -- no sorryAx
#print axioms BodyTotal.permissive             -- sorryAx: runBody_mono

end Midfall.LoweringV3

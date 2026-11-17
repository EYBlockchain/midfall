/-
  Midfall.LoweringV2.Program

  THE PROGRAM THE V2 THEOREM IS ABOUT, AS A FUNCTION OF THE LEAN CODEGEN.

  Scope (decision D-V2, PLAN-V2 §2): the object of the semantic-equivalence theorem is the Yul that
  the Lean port of the Rust generator (`Midfall/Generator/*`, golden-tested against
  `proofs/solidity-verifier`) emits for the body of `verifyProof`, with the contract-level
  `uint256 internal constant`s substituted at their use sites (which is what the Solidity language
  does with constants). solc is trusted and appears in no statement; there is no IR import, no
  `irCheck`, no `RunContractIR`, no `ObsEquiv` against a compiler output.

  NOTHING HERE IS A FREE FIELD. The plan view, the constant table, the two assembly blocks and the
  per-partial slices are functions of `(plan, model)`, where `model` is the output of the ported
  `artifacts.rs` on that plan. `CodegenAgrees` ties the AST emitter (`GenAst`) to the TEXT the
  ported codegen prints (`renderHalo2Verifier`), token for token. It is decidable and must be
  exhibited (by computation) at every render the headline is instantiated at.

  SPLIT (Q0.3). §1-§4 are the FROZEN program surface; they are hashed in
  `Midfall/LoweringV2/Frozen.sha256` and checked by `scripts/checks.sh`. §5 (the generator-side
  obligations `topBinders`, `inline_append`, `emitSlices_eq`) moved verbatim to
  `ProgramLemmas.lean`, which is refinable. No statement text was changed by the split.
-/
import Midfall.Lowering.GenAstDispatch
import Midfall.Lowering.YulParse
import Midfall.Lowering.InlineConstants
import Midfall.LoweringV2.Shared
import Midfall.Generator.Artifacts
import Midfall.Generator.Contracts
import Midfall.Generator.YulGolden

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

/-- The render model produced by the ported `artifacts.rs` (`generateVerifierFromPlan`). -/
abbrev Model := Halo2Verifier VerifierMemoryLayout ProofCalldataLayout

/-- A word literal. -/
def lit (n : Nat) : Expr EVM.Op := Expr.lit (.number n)

/-! ## 1. Views DERIVED from (plan, model) -/

/-- The `PlanView` the AST emitter reads. Derived, never supplied: every field comes from the plan
    or the model, through `Inv.planViewWithAccumulator` (the one constructor in the tree). -/
def planViewOf {Program Layout : Type} (L : LoweringPlan Program Layout) (m : Model)
    (acc : Option AccumulatorEncoding) : PlanView :=
  planViewWithAccumulator L.vk L.vkMptr L.memory L.proofLayout m.numInstances m.k
    m.numNegLagranges acc (parserFactsOfPlan m) L.meta_ L.data

/-- The contract-level constant table of THIS render: the ported `Constants.sol` template applied
    to this model and read back as `(name, value)` pairs. Replaces `Inline.contractConstants`, which
    is the pinned POSEIDON table and therefore wrong for every other render.

    WP-G2 replaces the read-back by a data-level table from which `renderConstants` is printed;
    until then a KAT must check that every `uint256 internal constant` line of `renderConstants`
    parses to a literal (no expression right-hand sides). -/
def constTableOf (m : Model) : List (String × Nat) :=
  (((renderConstants (partialCtxOfVerifier m)).splitOn "\n").filterMap
      Inline.solConstantLine?).filter fun c => c.1 != "vk" && c.1 != "success"

/-! ## 2. The two assembly blocks of `verifyProof`, un-inlined: exactly what the codegen prints -/

/-- `verifyProof`'s FIRST assembly block, the ABI-shape guard (template `Halo2Verifier.sol`,
    rendered by `Contracts.verifierNoticeSection` from `vhGuardOpen` to `vhGuardClose`). -/
def abiGuardBlock (m : Model) : YulBlock :=
  [Stmt.cond
    (Expr.builtin Op.iszero [Expr.builtin Op.and
      [Expr.builtin Op.eq
          [Expr.builtin Op.calldataload [lit m.abiSelectorBytes], lit m.abiProofHeadOffset],
       Expr.builtin Op.eq
          [Expr.builtin Op.calldataload [lit m.abiInstancesHeadCptr],
           Expr.builtin Op.sub [Expr.var "NUM_INSTANCE_CPTR", lit m.abiSelectorBytes]]]])
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [lit 0, Expr.builtin Op.shl [lit 224, Expr.var "ERR_BAD_CALLDATA_SHAPE"]]),
     Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])]]

/-- The MF-2 entry guard that opens the MAIN assembly block (`vhMainAssemblyOpen`). NOT the
    `fxHeadGuard` of the v1 fixtures, which reverted `(0, 0)` and compared against a literal. -/
def mainGuardBlock : YulBlock :=
  [Stmt.cond
    (Expr.builtin Op.gt [Expr.builtin Op.mload [lit 0x40], Expr.var "TRANSCRIPT_MPTR"])
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [lit 0, Expr.builtin Op.shl [lit 224, Expr.var "ERR_MEMORY_LAYOUT_VIOLATED"]]),
     Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])]]

/-- `let r := FR_MODULUS` / `let success := true` (`vhAfterTraceAndGas`). -/
def mainLocals : YulBlock :=
  [Stmt.letDecl ["r"] (some (Expr.var "FR_MODULUS")),
   Stmt.letDecl ["success"] (some (Expr.lit (.bool true)))]

/-- The main assembly block as the AST emitter produces it.

    WP-G1 IS CLOSED HERE (M2: G1.1, G1.2, OBJ.2). Until this commit `emitSlices` emitted the
    linearization SCOPE of QuotientAndLinearization but not the two `quotient_numerator` includes in
    front of it, and the accumulator helper include was not emitted at all: 6,779 of the generator's
    14,054 tokens, so `codegenAgrees` was FALSE at the deployment and clause 6 of `Render.Valid` was
    REFUTED. The three missing regions are now emitted - the five accumulator-codec definitions as a
    tree (G1.1), `q_program_fail` and `q_pow5` as a tree on the render's own flag (G1.2), and the
    6,384-token numerator as the PARSE of the model's own lines (OBJ.2, which replaces G1.3 as
    carded: the split is 5,431 generated + 953 template, not the 895 + 5,489 the card assumed).
    Hence the `m` below: the flags and the generated lines are `Model` fields that `PlanView` cannot
    reach (G1.2b) - which is what makes this signature, and with it this frozen file, one re-hash
    with `Statements.lean`'s scope (D-P65).

    STILL UN-EMITTED, NAMED: the `q_limb7` / `q_widelimb7` arms (each interpolates a coefficient
    list, so no Bool-selectable emitter covers them) and `validate_public_accumulator` (rendered only
    when the render HAS an accumulator). A render that takes either arm makes `codegenAgrees` FALSE -
    a red gate, not a silent omission, which is this file's standing rule. -/
def mainAsmRaw (pv : PlanView) (m : Model) : YulBlock :=
  mainGuardBlock ++ GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers ++ mainLocals
    ++ GenAst.emitSlicesM pv (partialCtxOfVerifier m)

/-- The two Solidity locals declared between the blocks, only when the render declares them
    (`address vk = AUTHORIZED_VK;`, `address quotientEvaluator = AUTHORIZED_QUOTIENT;`). Their
    values are the immutables, i.e. deployment addresses, supplied explicitly: reading an immutable
    is Solidity semantics, which is trusted (see `EntryFrame`). -/
def wrapperLocals (m : Model) (vkAddr qAddr : U256) : YulBlock :=
  (if m.embeddedVk.isNone then [Stmt.letDecl ["vk"] (some (lit vkAddr.toNat))] else []) ++
  (if m.quotientExternal.isSome then
      [Stmt.letDecl ["quotientEvaluator"] (some (lit qAddr.toNat))] else [])

/-! ## 3. The program the theorem runs: constants inlined, closed -/

/-- THE PROGRAM. The body of `verifyProof` after the Solidity entry path: the ABI-shape guard, the
    two wrapper locals, and the main block, with contract constants substituted. -/
def asmOf (pv : PlanView) (m : Model) (vkAddr qAddr : U256) : YulBlock :=
  Inline.inlineContractConstants (constTableOf m)
    (abiGuardBlock m ++ wrapperLocals m vkAddr qAddr ++ mainAsmRaw pv m)

/-- THE HELPER DEFINITIONS OF THE PROGRAM, inlined. Wider than `GenAst.emitHelpers` by the five
    accumulator-codec definitions: those are `funDef`s of the main block, so a slice that calls
    `load_acc_coord` can only run in a scope that has them, and `prog_slices_decomp`'s first conjunct
    is the statement that the program's function definitions are exactly these. They are NOT appended
    to `emitHelpers` itself: gate 51 pins that block's eight names to the AssemblyHelpers render, and
    the per-block contracts reach the helpers through this function. -/
def helpersOf (pv : PlanView) (m : Model) : YulBlock :=
  Inline.inlineContractConstants (constTableOf m)
    (GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers)

/-- One partial of the CLOSED program. Model-aware since OBJ.2: the `.quotientLin` slice now carries
    the two `quotient_numerator` includes in front of the linearization scope, so it is FOUR
    statements where it was one. Every other arm is `GenAst.emitPartial` verbatim. -/
def sliceOf (pv : PlanView) (m : Model) (q : Partial) : YulBlock :=
  Inline.inlineContractConstants (constTableOf m)
    (GenAst.emitPartialM pv (partialCtxOfVerifier m) q)

/-- Closedness, decidably: the only free names of the inlined main block are the wrapper locals.
    `Shared.freeNames` (the copy of `FrameWalk.freeNames`) is not kernel-reducible, so this is
    discharged by `native_decide` in
    `Instances/` (D-P17), per render. -/
def mainClosed (pv : PlanView) (m : Model) : Bool :=
  (freeNames (Inline.inlineContractConstants (constTableOf m) (mainAsmRaw pv m))).all
    fun x => x == "vk" || x == "quotientEvaluator"

/-! ## 4. Codegen agreement: the AST IS the text the ported codegen prints -/

/-- The thirteen include renders, all from the model (the PCS lines are the model's own
    `pcsComputations`, NOT the artifact's - contrast `DeployedProfile.poseidonDerivedParts`). -/
def partsOf (m : Model) : VerifierParts :=
  let b := partialCtxOfVerifier m
  { constants := renderConstants b
    precompileSmoke := renderPrecompileSmoke b
    constructors := renderConstructors b
    assemblyHelpers := renderAssemblyHelpers b
    accumulatorHelpers := renderAccumulatorHelpers b
    traceAndGasHelpers := renderTraceAndGasHelpers b
    vkLoading := renderVkLoading b
    transcriptProofParser := renderTranscriptProofParser b
    lagrange := renderLagrange b
    quotientAndLinearization := renderQuotientAndLinearization b
      (renderQuotientHelpers b) (renderQuotientNumeratorBlock b)
    pcs := renderPcs b m.pcsComputations
    finalPairing := renderFinalPairing b
    traceReturn := renderTraceReturn b }

/-- The text of the main assembly block exactly as `renderHalo2Verifier` lays it out, from
    `assembly ("memory-safe") {` up to (excluding) the closing braces of `vhFooter`. -/
def mainAssemblyText (m : Model) : String :=
  let ctx := rootCtxOfVerifier m
  let parts := partsOf m
  vhMainAssemblyOpen ++ parts.assemblyHelpers ++ includeGlue ++ parts.accumulatorHelpers ++
    includeGlue ++ parts.traceAndGasHelpers ++ verifierDirectSection ctx ++ vhAfterTraceAndGas ++
    parts.vkLoading ++ includeGlue ++ parts.transcriptProofParser ++ includeGlue ++
    parts.lagrange ++ includeGlue ++ parts.quotientAndLinearization ++ includeGlue ++
    parts.pcs ++ includeGlue ++ parts.finalPairing ++ includeGlue ++ parts.traceReturn

/-- The text of the ABI-shape guard block, `vhGuardOpen` .. `vhGuardClose`. -/
def abiGuardText (m : Model) : String :=
  let ctx := rootCtxOfVerifier m
  vhGuardOpen ++ hexFilter ctx.abiSelectorBytes ++ vhGuardSep1 ++
    hexFilter ctx.abiProofHeadOffset ++ vhGuardSep2 ++ hexFilter ctx.abiInstancesHeadCptr ++
    vhGuardSep3 ++ hexFilter ctx.abiSelectorBytes ++ vhGuardClose

/-- The main block's tokens in the form `EVM.print` produces for a block, i.e. WITH its braces:
    drop `assembly ( "memory - safe" )` (six tokens - `yulTokens` splits the string literal at the
    hyphen) and close with the brace `vhFooter` carries. Measured at the deployed profile by the
    probe in PLAN-V2 (WP-A1 turns it into a KAT). -/
def mainAssemblyTokens (m : Model) : List String :=
  (yulTokens (mainAssemblyText m)).drop 6 ++ ["}"]

/-- The guard block's tokens WITH its braces: drop the function-body brace and
    `assembly ( "memory - safe" )` (seven tokens); the text already ends with the block's `}`. -/
def abiGuardTokens (m : Model) : List String := (yulTokens (abiGuardText m)).drop 7

/-- THE LINK BETWEEN THE THEOREM AND THE LEAN CODEGEN. The program the semantics runs prints to
    exactly the token stream the ported generator emits for the two assembly blocks of
    `verifyProof`. Comments, whitespace and hex-versus-decimal spelling are not observable
    (`yulTokens` normalises them, D-P13). -/
def codegenAgrees (pv : PlanView) (m : Model) : Bool :=
  yulTokens (YulSemantics.EVM.print (abiGuardBlock m)) == abiGuardTokens m &&
    yulTokens (YulSemantics.EVM.print (mainAsmRaw pv m)) == mainAssemblyTokens m

def CodegenAgrees (pv : PlanView) (m : Model) : Prop := codegenAgrees pv m = true

/-! ### The structural tie (OBJ.2) -/

/-- The vendored AST of the generator's own main assembly text, or `none` if the parser cannot read
    it. `YulParse` is total and fuel-structural (OBJ.1), so this is a computable function of the model
    with no `partial`, no `unsafe` and no oracle in it. -/
def parsedMain? (m : Model) : Option YulBlock := YulParse.parseTokens (mainAssemblyTokens m)

/-- The same, for the ABI-shape guard block. -/
def parsedGuard? (m : Model) : Option YulBlock := YulParse.parseTokens (abiGuardTokens m)

/-- **THE STRUCTURAL CODEGEN TIE.** `codegenAgrees` compares TOKEN STREAMS, and `yulTokens` cannot
    see the difference between a dialect built-in and a user call (RV-27), so token equality is
    strictly weaker than the AST relation D-P13 names. This is the stronger clause: the emitter's AST
    is `SyntaxEq.stmtsBeq`-equal to the PARSE of the generator's text, for both assembly blocks.

    WHERE ITS TEETH ARE, and where they are not - stated plainly, because a reviewer needs to know
    which of the two they are looking at. For a region the emitters BUILD (the eight helpers, the six
    structured partials, `q_program_fail` / `q_pow5`, the five accumulator codecs) a mutation of the
    template moves one side only and this goes FALSE: that is the falsifier each structured region
    carries. For a region that IS a parse of the rendered text - the 5,431 generated tokens of the
    numerator, OBJ.2's route - both sides are built from the same `render m`, so agreement holds BY
    CONSTRUCTION and `codegenStruct` checks nothing there; what is trusted is the parser-printer round
    trip and `EVM.mkCall`'s builtin-versus-call resolution. The content of a parsed region is checked
    elsewhere: by `GeneratedBy`, by the artifact gate, and by the block proofs.

    D-P71: this is a `Bool` the VM computes, and it is DISCHARGED in `Midfall/Instances/` only.
    Nothing in the cone of `lowering_correct` may rest on `native_decide`, and nothing here needs it. -/
def codegenStruct (main : YulBlock) (m : Model) : Bool :=
  (match parsedGuard? m with
    | some g => SyntaxEq.stmtsBeq (abiGuardBlock m) g
    | none => false) &&
  (match parsedMain? m with
    | some g => SyntaxEq.stmtsBeq main g
    | none => false)

/-- The proposition `codegenStruct` decides, in the shape a `Valid` clause would want. -/
def CodegenStruct (pv : PlanView) (m : Model) : Prop := codegenStruct (mainAsmRaw pv m) m

end Midfall.LoweringV2

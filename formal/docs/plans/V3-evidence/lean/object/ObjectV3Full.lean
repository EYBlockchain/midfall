/-
  RECON.1b-ii STATUS — THE COLLISIONS ARE RESOLVED; THIS FILE TYPECHECKS AT HEAD.

  The recorded plan said "43 errors, 15 of them already been declared". **Measured at d8e5c3f the
  count had moved: 43 errors, 39 of them "has already been declared"** (the other 4 were cascades of
  the collisions: `Render.ValidV3.program`, the two `simp only [programOk]` projections, and the
  §7.2 `#eval`). ST.6 (0e4086d) ported the clause machinery into `Midfall/LoweringV2/Statements.lean`,
  `Midfall/LoweringV2/Program.lean`, `Midfall/LoweringV2/Generated.lean`,
  `Midfall/Generator/PlanNew.lean` and `Midfall/Lowering/YulParse.lean` — the same namespaces this
  scratch file had been copying.

  EVERY PAIR WAS DIFFED BEFORE ANYTHING WAS DELETED. The resolutions:

  * **DELETED — 38 copies, because the tree's same-named declaration is the SAME STATEMENT.**
    - `Midfall.Lowering.YulParse` (13: `Toks`, `isNumTok`, `isIdentTok`, `litOf`, `identList`,
      `parseArgs`, `parseExpr`, `parseStmts`, `parseBlock`, `parseCases`, `parseStmt`, `parseTokens`,
      `parseLines`): byte-identical to `Midfall/Lowering/YulParse.lean`.
    - `Midfall.Generator.PlanNew` (12: `pn`, `frFieldCtx`, `quotientProgramPlan`,
      `buildQuotientProgramItemsWithLimbOps`, `nativeCallbackScratchWords`, `usedHas`,
      `quotientOpcodeUsage`, `quotientMemUsage`, `quotientTemplateProgram`, `vkCarriesBuild`,
      `newFromVk`, `compactBlocksOf`): the proposed port LANDED. Where the landed text differs it is
      a repair of the same proposal, not a rival statement — `frFieldCtx` uses `a == b` where the
      scratch wrote `decide (a = b)`; `quotientProgramPlan` gained the `validateExecutionManifest`
      gate (QRS:523-524) the proposal had not yet asked for; `newFromVk`/`generateAll` were re-plumbed
      when `VerifierBuildInputs` was replaced by `(rawMeta, numInstances, accEncoding)`. The scratch
      copies were private plumbing for a scratch `generateAll` that is itself redundant, so nothing
      downstream needed them.
    - `Midfall.LoweringV2` (13 colliding: `cAddr`, `expectedConsts`, `progConstNames`,
      `constLinesLiteral`, `constsCoherent`, `GenOut`, `generateAll`, `callSitesE`, `callSitesS`,
      `funSigsOf`, `callsResolved`, `g1WordsBytes`, `payloadWord`, `PayloadAgrees`, `parsedMain?`,
      `parsedGuard?`, `codegenStruct`): same statement. Three are worth naming because the texts are
      NOT literally equal. `constsCoherent` wrapped conjunct 4 in `decide` in the tree; the scratch
      wrote bare `.Nodup`, a Prop in a Bool — the scratch's copy could no longer elaborate at all,
      and the tree's is the same four conjuncts. `expectedConsts` differs only in that the tree names
      `frModulusConstant`, whose definition (`Templates.lean:187`) IS the scratch's literal.
      `progConstNames` differs only in the arity `mainAsmRaw` gained. `PayloadAgrees` is ST.6's landed
      port of the object text's own clause (its doc comment says so): same fields, re-spelled through
      `R.pv` and the named `vkHeaderTemplateSlotsDefault` slots, `fixed`/`perm` renamed
      `fixedComms`/`permutationComms`, and `delta` dropped with a recorded reason. **That is the
      statement RECON.1 chose**, so the scratch copy went and `Render.ValidV3.payload` reads the
      tree's.

  * **RENAMED — 1 copy: `programOk` -> `programOkRaw`.** Here the two versions state DIFFERENT things
    and neither is redundant. The tree's `Midfall.LoweringV2.programOk` is
    `programOkB R = true ∧ GasCallOk (R.prog 0 0) ∧ ExitDiscipline (R.prog 0 0)` — a `Prop` on a
    `Render`, and it is the `program` clause of the single `ValidV3` that RECON.1 chose. The object
    text's `programOk pv m` is a `Bool` on the plan view and the model, computed at the emitter's
    output; `Render.ValidV3.program` and the §7.2 `#eval` exist to measure THAT historical form, and
    deleting it would have removed the only place the base text's program clause survives. So it is
    kept, under its own name, beside `programOkWith`/`constsCoherentWith`, which never collided.
    **FINDING, not a naming problem: the object text's `program` clause is weaker than the landed
    one — it carries neither `GasCallOk` nor `ExitDiscipline`.** RECON.1 strengthened it; nothing
    here hides that.

  * **QUALIFIED — 0.** No third convention was invented: WideningV3's rule (delete the copy, name the
    landed one) covered 38 of the 39, and the 39th needed its own name.

  NOT TOUCHED BY THIS CARD, and still FAILING in the object area for reasons outside these 39:
  `Cov1`, `Plan1`, `Plan2` (tree signature drift on `mainAsmRaw` / `metaDataForStableStaticLayout`),
  `Parse1` (9 of the same YulParse copies), `Consts2` (5 of the same LoweringV2 copies), `Key1`
  (2 `Ambiguous term g1WordsBytes`), and `GeneratorCertified`/`CertMeasure` (their own rebase, which
  this card unblocks but does not perform).
-/
import Midfall.Instances.PoseidonValid
import Midfall.Generator.Vk
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldCompute
set_option autoImplicit false

 /-! RECON.1b-ii: the scratch copy of the Yul token parser (`Midfall.Lowering.YulParse`:
      `Toks`, `isNumTok`, `isIdentTok`, `litOf`, `identList`, `parseArgs`, `parseExpr`,
      `parseStmts`, `parseBlock`, `parseCases`, `parseStmt`, `parseTokens`, `parseLines`)
     was DELETED here. All thirteen are byte-identical to `Midfall/Lowering/YulParse.lean`,
     which is in this file's import closure, so the tree now owns that vocabulary (the same
     convention RECON.1b applied in `widening/WideningV3.lean`: delete the copy, use the
     landed one). -/

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

def ConstsCoherent (pv : PlanView) (m : Model) : Prop := constsCoherent pv m = true

/-- What a block proof uses: a table lookup is a lookup in the DATA table. Generic in the render. -/
theorem consts_lookup_of_coherent {pv : PlanView} {m : Model} (h : ConstsCoherent pv m)
    (name : String) :
    (constTableOf m).lookup name = (expectedConsts pv m).lookup name := by
  have h3 : (constTableOf m == expectedConsts pv m) = true := by
    unfold ConstsCoherent constsCoherent at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.2
  rw [eq_of_beq h3]

end Midfall.LoweringV2

/-!
  PLAN-V3 / area OBJECT: the proposed statements, typechecked against the tree at 6bde89f.
  Sections:
   1. `Except.getOk` (closes DECISIONS-PENDING section 9 with no v1 edit and no frozen change)
   2. `Generator/PlanNew.lean` (proposed): the ported `LoweringPlan::new`, generic
   3. `LoweringV2/Generated.lean` (proposed): `GenOut`, `generateAll`, `Render.GeneratedBy`
   4. program well-scopedness checks (`callsResolved`, `noShadow`)
   5. key coherence: `PayloadAgrees`
   6. `Render.ValidV3`
   7. evaluation at the fixture, on the DERIVED render
-/

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientBlocks
open Midfall.Generator.QuotientEvaluator Midfall.Generator.QuotientRecognizers
open YulSemantics YulSemantics.EVM

/-! ## 1. The total projection of an `Except` along a Bool proof -/

/-- The `.ok` value of an `Except` whose `isOk` is `true`. The motive is NON-dependent in the
    scrutinee (the proof argument is about a Bool), which is what `poseidonModelVal`'s
    `match h : poseidonModel with` lacks. -/
def Except.getOk {ε α : Type} : (e : Except ε α) → e.isOk = true → α
  | .ok a, _ => a
  | .error _, h => by simp [Except.isOk, Except.toBool] at h

theorem Except.eq_ok_getOk {ε α : Type} (e : Except ε α) (h : e.isOk = true) :
    e = .ok (e.getOk h) := by
  cases e with
  | ok a => rfl
  | error _ => simp [Except.isOk, Except.toBool] at h

namespace Midfall.LoweringV2

open Midfall.Generator.PlanNew Midfall.Assumptions

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 3. The generator, end to end, and the ONE generated-by clause -/

namespace Render

variable (R : Render p G₁ G₂ Gₜ)

/-- The generator run on THIS render's verifier-side inputs. The permutation DELTA the quotient
    blocks print is the Lean verifier's own `E.delta`. -/
def generated : Except Fault GenOut :=
  generateAll Features.solidity R.E.delta R.vk R.cfg R.plan.vk R.inputs R.flags

/-- **THE GENERATED-BY CLAUSE.** Replaces frozen clauses 1 `circuitMeta`, 2 `layout`,
    3 `invariants`, 4 `model`, the `validate_layout` gap (B-7), the VM-lowering gap (B+3),
    `vkPins.numInst`, and makes `E.delta` reach the program text (H-7). -/
def GeneratedBy : Prop :=
  ∃ out, R.generated = .ok out ∧ out.plan = R.plan ∧ out.qblocks = R.qblocks ∧
    out.model = R.model

end Render

/-! ## 4. Program well-scopedness (decidable; closes B-4 and B-5) -/

/-- No binder of the program is the name of a contract constant (solc rejects it too). This is
    the hypothesis `inline_append` needs and no clause supplied (B-5). -/
def noShadow (consts : List (String × Nat)) (prog : YulBlock) : Bool :=
  (boundSs prog).all fun x => !(consts.map Prod.fst).contains x

/-! ## 5. Key coherence: what the payload must say about the Lean verifier's key -/

end Midfall.LoweringV2

/-! ## 6. The repaired validity predicate -/

namespace Midfall.LoweringV2

open Midfall.Lowering.YulParse Midfall.Assumptions Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-- `constsCoherent` with the main block as a parameter (the emitter's output after WP-G1). -/
def constsCoherentWith (main : YulBlock) (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone && constLinesLiteral m &&
  constTableOf m == expectedConsts pv m &&
  decide (((expectedConsts pv m).map Prod.fst).Nodup) &&
  ((freeNames (abiGuardBlock m ++ main)).filter
      fun x => x != "vk" && x != "quotientEvaluator").all
    fun x => ((expectedConsts pv m).map Prod.fst).contains x

/-- **ONE BOOL FOR THE PROGRAM.** Everything about the emitted program that is decided by
    computation at a render: it is the parse of the text; its constant table is the plan view's;
    every call resolves; no binder shadows a constant; after inlining only the wrapper locals are
    free (guard block included); the transcript base is above Solidity's reserved words. -/
def programOkWith (main : YulBlock) (pv : PlanView) (m : Model) : Bool :=
  let consts := constTableOf m
  codegenStruct main m &&
  constsCoherentWith main pv m &&
  callsResolved main &&
  noShadow consts (abiGuardBlock m ++ wrapperLocals m 0 0 ++ main) &&
  (freeNames (Inline.inlineContractConstants consts (abiGuardBlock m ++ main))).all
    (fun x => x == "vk" || x == "quotientEvaluator") &&
  decide (0x80 ≤ pv.memory.transcriptMptr)

/-- **RENAMED BY RECON.1b-ii: `programOk` -> `programOkRaw`.** This rename is not a dodge: ST.6
    landed a DIFFERENT `Midfall.LoweringV2.programOk` --
    `programOk (R : Render p G₁ G₂ Gₜ) : Prop := programOkB R = true ∧ GasCallOk (R.prog 0 0) ∧
    ExitDiscipline (R.prog 0 0)` (`Midfall/LoweringV2/Statements.lean:914`, the single text's
    `program` clause). **That is the statement RECON.1 chose, and it remains the tree's.** The object
    text's own `program` clause is a different thing: one Bool computed from the plan view and the
    model at the emitter's output. `Render.ValidV3.program` below and the `#eval` at §7.2 are the
    places that clause is used AS THE HISTORICAL FORM UNDER TEST, so it is kept under its own name
    rather than deleted. Deleting it would have discarded the base text RECON.1 reconciled from.
    One application is repaired in passing: `mainAsmRaw` gained the `Model` argument, so
    `mainAsmRaw pv` is now `mainAsmRaw pv m` -- the same clause read at today's emitter, exactly as
    the tree's own `progConstNames` reads it. -/
def programOkRaw (pv : PlanView) (m : Model) : Bool := programOkWith (mainAsmRaw pv m) pv m

/-- **VALIDITY, V3.** Seven clauses in four groups, replacing the thirteen of
    `Statements.lean:182-217` and the proposed pins D-P46 / D-P48. -/
structure Render.ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- G. Plan, compact quotient blocks and model are the generator's output for THIS constraint
      system, configuration, payload and DELTA. -/
  generated : R.GeneratedBy
  /-- G. The build inputs are the configuration's and the key's (frozen clause 5, unchanged). -/
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  /-- P. The program checks, one computation. -/
  program : programOkRaw R.pv R.model = true
  /-- P. No world write (frozen clause 10, unchanged). -/
  noWriters : NoWriters (R.prog 0 0)
  /-- K. Field, domain and G2 parameters agree (frozen clause 8, unchanged). -/
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  /-- K. Every payload word is the Lean key's. -/
  payload : PayloadAgrees R
  /-- S. Scope (frozen clause 9; `wf.permutationCommitmentsMatch` repaired elsewhere). -/
  supported : SupportedV2 R

/-- What V3 gives the block proofs that V2 supplied pin by pin: a table lookup is a lookup in the
    DATA table, for EVERY valid render, with no string parsing in the proof. -/
theorem Render.ValidV3.vkMptr_const {R : Render p G₁ G₂ Gₜ} (h : R.ValidV3) :
    R.consts.lookup "VK_MPTR" = some (ptrAddr R.pv.memory.vkMptr) := by
  have hp := h.program
  simp only [programOkRaw, programOkWith, Bool.and_eq_true] at hp
  have hc := hp.1.1.1.1.2
  simp only [constsCoherentWith, Bool.and_eq_true] at hc
  have heq := eq_of_beq hc.1.1.2
  show (constTableOf R.model).lookup "VK_MPTR" = _
  rw [heq]
  cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
    cases h3 : R.model.expectedQuotientCodehash <;>
    simp [expectedConsts, h1, h2, h3, List.lookup, cAddr, ptrAddr, ptrValue]

/-- The same for the pin D-P48 asked to add to the frozen surface. -/
theorem Render.ValidV3.returnMptr_const {R : Render p G₁ G₂ Gₜ} (h : R.ValidV3) :
    R.consts.lookup "RETURN_MPTR" = some R.pv.memory.verifierReturnMptr := by
  have hp := h.program
  simp only [programOkRaw, programOkWith, Bool.and_eq_true] at hp
  have hc := hp.1.1.1.1.2
  simp only [constsCoherentWith, Bool.and_eq_true] at hc
  have heq := eq_of_beq hc.1.1.2
  show (constTableOf R.model).lookup "RETURN_MPTR" = _
  rw [heq]
  cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
    cases h3 : R.model.expectedQuotientCodehash <;>
    simp [expectedConsts, h1, h2, h3, List.lookup]

end Midfall.LoweringV2

/-! ## 7. Evaluation at the fixture, on the DERIVED render -/

namespace Fixture

open Midfall.Instances Midfall.Instances.PoseidonValid Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.LoweringV2 Midfall.Generator.PlanNew Midfall.Lowering.YulParse
open Midfall.Generator.ContractKats Midfall.Generator.VerifierPartialKats

/-- Fq::DELTA (curves/src/bls12_381/fq.rs:492); the contract literal at dump line 1975. -/
def blsDelta : Fr Yul.blsR :=
  (0x08634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7 : Fr Yul.blsR)

/-- The parsed payload plus the four reservation fields `vkModelFromArtifact` leaves empty. -/
def vkFull : Except Fault Halo2VerifyingKey := do
  let v := poseidonVkGen
  let hdr := (v.constants.filter fun c => c.1 != "quotient_const" && c.1 != "quotient_program").length
  let nC := (v.constants.filter fun c => c.1 == "quotient_const").length
  let nP := (v.constants.filter fun c => c.1 == "quotient_program").length
  let lay ← unwrapAt "scratch" (VkPayloadLayout.forVk hdr nC nP v.fixedComms.length v.permutationComms.length)
  let qc ← unwrapAt "scratch" (lay.wordOffset PayloadSectionKind.quotientConstants)
  let qp ← unwrapAt "scratch" (lay.wordOffset PayloadSectionKind.quotientProgram)
  pure { v with quotientConstOffsetWords := some qc, quotientConstWords := nC, quotientProgramOffsetWords := some qp, quotientProgramWords := nP }

def genWith (delta : Fr Yul.blsR) (f : Halo2VerifyingKey → Halo2VerifyingKey) : Except Fault GenOut :=
  vkFull >>= fun v =>
    generateAll Features.solidity delta poseidonVkExec poseidonConfig (f v) poseidonInputs poseidonFlags

def gen : Except Fault GenOut := genWith blsDelta id

def diffCount (a b : String) : Nat :=
  (((a.splitOn "\n").zip (b.splitOn "\n")).filter fun (x, y) => x != y).length

def textOf (o : GenOut) : String := renderHalo2Verifier (rootCtxOfVerifier o.model) (partsOf o.model)

def emitPcsScoped (pv : PlanView) : Block EVM.Op :=
  match Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory pv.truncatedChallenges false with
  | .ok blocks => [Stmt.block (blocks.map Stmt.block)]
  | .error _ => []

/-- Stand-in for the WP-G1 emitter: today's emitters, pcs with its scopes, and the three
    un-emitted regions taken as the PARSE of the model's own text. -/
def mainV3 (pv : PlanView) (m : Model) : YulBlock :=
  let b := partialCtxOfVerifier m
  let P (t : String) : Block EVM.Op := (parseLines [t]).getD []
  mainGuardBlock ++ GenAst.emitHelpers pv ++ P (renderAccumulatorHelpers b) ++ mainLocals ++
    Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++
      (match q with
       | .quotientLin => P (renderQuotientHelpers b) ++ P (renderQuotientNumeratorBlock b) ++ GenAst.emitQuotientLin pv
       | .pcs => emitPcsScoped pv
       | q => GenAst.emitPartial pv q)

def report (e : Except Fault GenOut) (f : GenOut → String) : String :=
  match e with
  | .ok o => f o
  | .error (Fault.panic s) => "PANIC " ++ s
  | .error _ => "ERR"

-- 7.1 the generator runs, and its text is the artifact but for BUILD_ID
#eval report gen fun o =>
  s!"ok; text differs from the Rust artifact in {diffCount (textOf o) poseidonVerifierDump} line(s); len {(textOf o).length}/{poseidonVerifierDump.length}; proofLen={o.plan.proofLayout.proofLen}; vkMptr={pn o.plan.vkMptr}"
-- 7.2 the program clause at the derived render: with the V3 stand-in, and with today's emitter
#eval report gen fun o =>
  let pv := planViewOf o.plan o.model none
  s!"programOkWith mainV3 = {programOkWith (mainV3 pv o.model) pv o.model}; programOkRaw (today's mainAsmRaw) = {programOkRaw pv o.model}; noWriters = {Midfall.Yul.Bridge.noWritersFuel 20000 (Inline.inlineContractConstants (constTableOf o.model) (abiGuardBlock o.model ++ wrapperLocals o.model 0 0 ++ mainV3 pv o.model))}"
-- 7.3 the conjuncts of the program clause, separately
#eval report gen fun o =>
  let pv := planViewOf o.plan o.model none
  let main := mainV3 pv o.model
  s!"codegenStruct={codegenStruct main o.model} consts={constsCoherentWith main pv o.model} callsResolved={callsResolved main} noShadow={noShadow (constTableOf o.model) (abiGuardBlock o.model ++ wrapperLocals o.model 0 0 ++ main)} transcriptFloor={decide (0x80 ≤ pv.memory.transcriptMptr)}"
-- 7.4 the frozen clauses 1-3 at the generator's plan: 1 is FALSE, 2 and 3 are TRUE
#eval report gen fun o =>
  let c1 := match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
    | .ok m => m == o.plan.meta_ | .error _ => false
  let c2 := match ProofCalldataLayout.fromProtocol o.plan.meta_.protocol abiVerifyProofProofCptr o.plan.meta_.numEvals o.plan.meta_.numPointSets with
    | .ok l => l.proofLen == o.plan.proofLayout.proofLen && l.proofEnd == o.plan.proofLayout.proofEnd | .error _ => false
  let c3 := match o.plan.validateGeneratorInvariants with | .ok (.ok ()) => true | _ => false
  s!"frozen circuitMeta={c1} layout={c2} invariants={c3}"
-- 7.5 FALSIFIER (delta): the placeholder delta 2 of poseidonE changes the generated text
#eval report (genWith 2 id) fun o =>
  s!"delta=2: ok; text differs from the artifact in {diffCount (textOf o) poseidonVerifierDump} line(s)"
-- 7.6 FALSIFIER (payload, quotient section): flip one quotient_program word -> the generator refuses
def flipProgWord (v : Halo2VerifyingKey) : Halo2VerifyingKey :=
  { v with constants := v.constants.zipIdx.map fun (c, i) => if i == 33 then (c.1, c.2 + 1) else c }
#eval report (genWith blsDelta flipProgWord) fun _ => "ok (NOT refused)"
-- 7.7 NON-FALSIFIER (payload, header): flip omega (word 4) -> the generator still accepts, so
--     `PayloadAgrees` is needed in addition to `GeneratedBy`
def flipOmega (v : Halo2VerifyingKey) : Halo2VerifyingKey :=
  { v with constants := v.constants.zipIdx.map fun (c, i) => if i == 4 then (c.1, c.2 + 1) else c }
#eval report (genWith blsDelta flipOmega) fun o =>
  s!"omega flipped: generator ok; verifier text differs in {diffCount (textOf o) poseidonVerifierDump} line(s)"
-- 7.8 Except.getOk closes the model clause shape
example : gen = .ok (gen.getOk (by native_decide)) := Except.eq_ok_getOk _ _

end Fixture

#print axioms Except.eq_ok_getOk
#print axioms Midfall.LoweringV2.Render.ValidV3.vkMptr_const
#print axioms Midfall.LoweringV2.Render.ValidV3.returnMptr_const
#check @Midfall.LoweringV2.Render.ValidV3
#check @Midfall.LoweringV2.Render.GeneratedBy
#check @Midfall.LoweringV2.generateAll
#check @Midfall.Generator.PlanNew.newFromVk

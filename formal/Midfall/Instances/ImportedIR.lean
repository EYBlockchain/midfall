-- |
-- Midfall.Instances.ImportedIR
--
-- P-IR (docs/plans/P-IR-import.md) hazard 3: RUNCONTRACTIR HAS A WITNESS.
--
-- Midfall.Lowering.RunContractIR (Lowering/Surface.lean:565) takes a Surface, a world, a hash,
-- an imported solc object, a layout, calldata, a call relation and a gas oracle, and asks for a
-- committed run of the object's runtime block. Stage 4 could not exhibit one - not because the
-- run was hard, but because the imported object did not exist and, before P-VEND, the very first
-- statement of its runtime (mstore(64, memoryguard(128))) had no Step rule at all. Both
-- blockers are gone: Midfall/Yul/ImportSolcIR.lean imports the artifact and
-- Midfall/Yul/Builtins.lean derives the memoryguard step. This file puts the two together.
--
-- WHY HERE. RunContractIR is stated over a Surface, and a Surface needs an AdmissiblePairing;
-- the only model of one in the tree is the exponent model (R-28), which lives in Instances/.
-- The Instances-confinement gate in scripts/checks.sh refuses a theorem in any file that
-- imports Instances/ from outside it (D-P17), so the witness has to live here, exactly as
-- Instances/SurfaceFixture.lean does for the invariant. Nothing outside Instances/ cites this
-- file; the statements that will consume the witness are stage 6's.
--
-- WHAT THE RUN IS. The entry frame carries an EMPTY calldata, so the dispatcher's selector test
-- iszero(lt(calldatasize(), 4)) evaluates to zero, the whole switch is skipped, and the runtime
-- falls through to the next statement: a call to the user function
-- revert_error_42b3...(), whose body is revert(0, 0). So this is a real run of the real
-- imported runtime - prologue, dispatcher, fall-through, revert - not a stand-in: three
-- statements of the 28 top-level statements of the deployed block, ending in a revert exactly as
-- the contract does when called with no calldata. The remaining statements are function
-- definitions, which Step.funDef executes as no-ops and which the halt short-circuits anyway.
--
-- WHY THE OPEN DIALECT. RunContractIR quantifies over ExternalCalls and ExternalGas, so the
-- witness is proved for ARBITRARY c and g rather than for a chosen pair. That is only possible
-- because the executed path touches no external call and no gas(): every builtin it uses falls
-- through the catch-all arm stepOp op args st = some result of builtinWithExternal, which is
-- what makes the transfer from the closed dialect definitional (P-VEND's note at
-- Builtins.lean:259). A witness that picked c and g would prove inhabitation of a statement no
-- theorem uses.
--
-- WHAT THE WITNESS DOES NOT CLAIM. It is not verifier_sound, and the revert is not a proof that
-- the verifier rejects: calldata of length zero is the one input the dispatcher cannot route,
-- and the contract reverts on it before any check runs. What is claimed is precisely that the
-- hypothesis of ir_refines and lowering_equivalence is satisfiable - the vacuity class those
-- statements were held out of - and, in witness_freePointer_is_the_ir_value, that the
-- free-memory pointer the imported ir writes is the artifact's 0x80: DECISION 1 showing up in a
-- state rather than in a comment.
import Midfall.Lowering.Surface
import Midfall.Instances.SurfaceFixture
import Midfall.Yul.ImportSolcIR

namespace Midfall.Instances.ImportedIR
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Generator Midfall.Yul Midfall.Yul.Bridge
open Midfall.Yul.Builtins Midfall.Yul.Ir Midfall.Instances.SurfaceFixture
open YulSemantics YulSemantics.EVM

-- The imported runtime is a 2,900-line term and the derivations below evaluate pieces of it.
set_option maxRecDepth 400000

/-- The open dialect RunContractIR runs in, named so the derivation stays readable. -/
abbrev OD (c : ExternalCalls) (g : ExternalGas) : YulSemantics.Dialect := Bridge.Dialect c g

/-- The Surface, with the one field the import needs changed: runtimeName must name the imported
    object's runtime sub-object. realSurface uses the fixture convention n ++ "_1_deployed",
    which is right for the fixture object and wrong for solc's, so the witness overrides it and
    nothing else. -/
def irSurface : Surface rp RP RP RP :=
  { realSurface with runtimeName := fun _ => verifierRuntimeName }

/-- The deployment world and the layout, both taken from the fixture: the witness is about the
    imported contract, not about a second model of the deployment. -/
def irW : ExecEnv := fxW

def irLyt : EVM.Layout := fxShellLayout

/-- Empty calldata: the one input the dispatcher cannot route. -/
def irCd : Bytes := ByteArray.mk #[]

/-- The entry frame RunContractIR builds: callState W irLyt H cd. -/
def irSt0 : EvmState := callState irW irLyt keccak256 irCd

/-- The frame after the prologue: the free-memory pointer now holds the artifact's reservation. -/
def irSt1 : EvmState := prologuePostFrom irSt0

/-- The frame the fall-through revert leaves. -/
def irSt2 : EvmState :=
  { touchMemory irSt1 0 0 with halted := some (.revert, readBytes irSt1.memory 0 0) }

theorem irSt0_calldataNil : irSt0.env.calldata = [] := rfl
theorem irSt1_calldataNil : irSt1.env.calldata = [] := rfl

/-! ### The three statements that run -/

/-- The prologue's two builtin steps in the open dialect, from the entry frame. Reuses P-VEND's
    closed-dialect derivations through the catch-all arm of builtinWithExternal. -/
theorem guardOpen {c : ExternalCalls} {g : ExternalGas} :
    (OD c g).Builtin Op.memoryguard [128] irSt0 (.ok [128] irSt0) := by
  simp only [OD, Bridge.Dialect, evmWithExternal, builtinWithExternal]
  exact guardBuiltinFrom

theorem mstoreOpen {c : ExternalCalls} {g : ExternalGas} :
    (OD c g).Builtin Op.mstore [64, 128] irSt0 (.ok [] irSt1) := by
  simp only [OD, Bridge.Dialect, evmWithExternal, builtinWithExternal]
  exact mstoreBuiltinFrom

theorem prologueArgsOpen {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)} :
    Step (OD c g) funs [] irSt0
      (Code.args [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])
      (.eres (.vals [64, 128] irSt0)) :=
  Step.argsCons
    (Step.argsCons (Step.argsNil (D := OD c g) (st := irSt0))
      (Step.builtinOk (D := OD c g) (argvals := [128]) (st1 := irSt0) (rets := [128])
        (st2 := irSt0)
        (Step.argsCons (D := OD c g) (rest := []) (restvals := []) (st := irSt0)
          (Step.argsNil (D := OD c g) (st := irSt0))
          (Step.lit (D := OD c g) (st := irSt0) (l := Literal.number 128)))
        guardOpen))
    (Step.lit (D := OD c g) (st := irSt0) (l := Literal.number 64))

theorem prologueExprOpen {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)} :
    Step (OD c g) funs [] irSt0
      (Code.expr (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]]))
      (.eres (.vals [] irSt1)) :=
  Step.builtinOk (D := OD c g) prologueArgsOpen mstoreOpen

/-- The dispatcher test, as the imported AST has it: the selector-length check solc emits before
    the switch. -/
def irCond : Expr EVM.Op := yulE% iszero(lt(calldatasize(), 4))

theorem calldatasizeStep {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)} :
    Step (OD c g) funs [] irSt1 (Code.expr (Expr.builtin Op.calldatasize []))
      (.eres (.vals [0] irSt1)) :=
  Step.builtinOk (D := OD c g) (Step.argsNil (D := OD c g) (st := irSt1))
    (by show stepOp Op.calldatasize [] irSt1 = some (.ok [0] irSt1); rfl)

theorem ltStep {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)} :
    Step (OD c g) funs [] irSt1
      (Code.expr (Expr.builtin Op.lt [Expr.builtin Op.calldatasize [], Expr.lit (.number 4)]))
      (.eres (.vals [1] irSt1)) :=
  Step.builtinOk (D := OD c g)
    (Step.argsCons (D := OD c g) (rest := [Expr.lit (.number 4)]) (restvals := [4])
      (st := irSt1)
      (Step.argsCons (D := OD c g) (rest := []) (restvals := []) (st := irSt1)
        (Step.argsNil (D := OD c g) (st := irSt1))
        (Step.lit (D := OD c g) (st := irSt1) (l := Literal.number 4)))
      (calldatasizeStep (c := c) (g := g)))
    (by show stepOp Op.lt [0, 4] irSt1 = some (.ok [1] irSt1); rfl)

theorem iszeroStep {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)} :
    Step (OD c g) funs [] irSt1 (Code.expr (Expr.builtin Op.iszero [Expr.lit (.number 1)]))
      (.eres (.vals [0] irSt1)) :=
  Step.builtinOk (D := OD c g)
    (Step.argsCons (D := OD c g) (rest := []) (restvals := []) (st := irSt1)
      (Step.argsNil (D := OD c g) (st := irSt1))
      (Step.lit (D := OD c g) (st := irSt1) (l := Literal.number 1)))
    (by show stepOp Op.iszero [1] irSt1 = some (.ok [0] irSt1); rfl)

theorem condStep {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)} :
    Step (OD c g) funs [] irSt1 (Code.expr irCond) (.eres (.vals [0] irSt1)) :=
  Step.builtinOk (D := OD c g)
    (Step.argsCons (D := OD c g) (rest := []) (restvals := []) (st := irSt1)
      (Step.argsNil (D := OD c g) (st := irSt1))
      (ltStep (c := c) (g := g)))
    (by show stepOp Op.iszero [1] irSt1 = some (.ok [0] irSt1); rfl)

/-- The dispatcher is skipped: the condition is zero, so the switch body never runs. -/
theorem dispatcherSkipped {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (OD c g)}
    (body : Block EVM.Op) :
    Step (OD c g) funs [] irSt1 (Code.stmt (Stmt.cond irCond body))
      (.sres [] irSt1 .normal) :=
  Step.ifFalse (D := OD c g) (condStep (c := c) (g := g)) rfl

/-! ### The fall-through: a user call whose body reverts -/

/-- The user function the imported runtime falls through to. -/
def irFallthrough : String :=
  "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"

/-- Its body, as the artifact has it: revert(0, 0). -/
def irRevertBody : Block EVM.Op :=
  [Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 0)])]

/-- THE IMPORTED BLOCK BEGINS WHERE THIS DERIVATION SAYS IT DOES. Proved by rfl against the
    import, so if the artifact, the pin or the rename ever changes shape, the witness stops
    applying rather than quietly describing a different program. -/
theorem irRuntime_shape :
    (match verifierRuntime with
      | Stmt.exprStmt e :: Stmt.cond c _ :: Stmt.exprStmt (Expr.call fn []) :: _ =>
          (SyntaxEq.exprBeq e (Expr.builtin Op.mstore
            [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]]),
           SyntaxEq.exprBeq c irCond, fn == irFallthrough)
      | _ => (false, false, false)) = (true, true, true) := rfl

/-- The hoisted function environment of the imported runtime block: what Step.block installs,
    and what the fall-through call resolves against. -/
def irFuns (c : ExternalCalls) (g : ExternalGas) : FunEnv (OD c g) :=
  [hoist (OD c g) verifierRuntime]

/-- LOOKUP WORKS IN THE IMPORTED BLOCK. The function is found in the hoisted scope of the real
    imported runtime, with the body the artifact gives it. rfl, so this is a computation over the
    imported term, not a claim about a copy of it. -/
theorem lookupFallthrough {c : ExternalCalls} {g : ExternalGas} :
    lookupFun (irFuns c g) irFallthrough =
      some ({ params := [], rets := [], body := irRevertBody }, irFuns c g) := rfl

theorem revertBuiltinOpen {c : ExternalCalls} {g : ExternalGas} :
    (OD c g).Builtin Op.revert [0, 0] irSt1 (.halt irSt2) := by
  simp only [OD, Bridge.Dialect, evmWithExternal, builtinWithExternal, irSt2, irSt1]
  rfl

theorem revertBodyRuns {c : ExternalCalls} {g : ExternalGas} :
    Step (OD c g) (hoist (OD c g) irRevertBody :: irFuns c g) [] irSt1
      (Code.stmts irRevertBody) (.sres [] irSt2 .halt) :=
  Step.seqStop (D := OD c g) (rest := []) (V1 := []) (st1 := irSt2)
    (Step.exprStmtHalt (D := OD c g)
      (Step.builtinHalt (D := OD c g)
        (Step.argsCons (D := OD c g) (rest := [Expr.lit (.number 0)]) (restvals := [0])
          (st := irSt1)
          (Step.argsCons (D := OD c g) (rest := []) (restvals := []) (st := irSt1)
            (Step.argsNil (D := OD c g) (st := irSt1))
            (Step.lit (D := OD c g) (st := irSt1) (l := Literal.number 0)))
          (Step.lit (D := OD c g) (st := irSt1) (l := Literal.number 0)))
        revertBuiltinOpen))
    (by intro h; cases h)

/-- The fall-through call: a user call that halts inside the imported runtime. -/
theorem fallthroughRuns {c : ExternalCalls} {g : ExternalGas} :
    Step (OD c g) (irFuns c g) [] irSt1 (Code.expr (Expr.call irFallthrough []))
      (.eres (.halt irSt2)) :=
  Step.callHalt (D := OD c g) (args := []) (argvals := []) (st1 := irSt1)
    (decl := { params := [], rets := [], body := irRevertBody }) (cenv := irFuns c g)
    (Vend := []) (st2 := irSt2)
    (Step.argsNil (D := OD c g) (st := irSt1))
    lookupFallthrough
    rfl
    (Step.block (D := OD c g) (Vb := []) (stb := irSt2) (o := .halt) revertBodyRuns)

/-! ### The run, and the inhabitation of RunContractIR -/

/-- THE RUN EXISTS. The imported deployed runtime block, from the entry frame an empty calldata
    produces, in the open dialect, for every call relation and every gas oracle: three steps,
    ending in a revert. -/
theorem importedRuntime_runs (c : ExternalCalls) (g : ExternalGas) :
    Bridge.Run c g verifierRuntime irSt0 [] irSt2 .halt :=
  Step.block (D := OD c g) (Vb := []) (stb := irSt2) (o := .halt)
    (Step.seqCons (D := OD c g) (V1 := []) (st1 := irSt1)
      (Step.exprStmt (D := OD c g) prologueExprOpen)
      (Step.seqCons (D := OD c g) (V1 := []) (st1 := irSt1)
        (Step.ifFalse (D := OD c g) (condStep (c := c) (g := g)
          (funs := irFuns c g)) rfl)
        (Step.seqStop (D := OD c g) (V1 := []) (st1 := irSt2)
          (Step.exprStmtHalt (D := OD c g) (fallthroughRuns (c := c) (g := g)))
          (by intro h; cases h))))

/-- The imported object plugs into Surface.irRuntime: the runtime block RunContractIR asks for is
    the block this file imported. rfl, i.e. a computation over the imported term. -/
theorem irRuntime_of_import : irSurface.irRuntime verifierIr = some verifierRuntime := rfl

/-- THE REQUIRED FINDING, AS A TERM: RunContractIR is inhabited, for every call relation and
    every gas oracle. Not vacuously - the hypothesis it supplies is a real committed run of the
    real imported runtime, and witness_is_a_revert says what that run ends in. -/
theorem runContractIR_inhabited (c : ExternalCalls) (g : ExternalGas) :
    exists obs, RunContractIR irSurface irW keccak256 verifierIr irLyt irCd c g obs :=
  ⟨⟨committedState irSt0 irSt2, .halt⟩, verifierRuntime, [], irRuntime_of_import,
    ⟨irSt2, importedRuntime_runs c g, rfl⟩⟩

/-! ### R-60 S1: the JOINT exhibit, which is what the headline fields actually take -/

/-- THE CHECK READS THE FIELD IT BELONGS TO. `Surface.irCheck` is now a projection of
    `Surface.runtimeName` (Surface.lean, R-60 S1), so on the Surface whose runtimeName names
    the imported sub-object, the check accepts the imported object. Kernel-checked, not
    argued: this is the term that makes `S.irCheck ir = true` satisfiable at the artifact
    the package exists to talk about. -/
theorem irCheck_holds_at_imported : irSurface.irCheck verifierIr = true := by
  rfl

/-- The same decision on the WRONG Surface: the fixture's own naming convention does not
    name the imported sub-object, so the projection says false - which is the point of
    making it a projection. Under the old free field this pair was inverted on the
    imported object: the check said false while the run said true. -/
theorem irCheck_false_at_fixture_naming : realSurface.irCheck verifierIr = false := by
  rfl

/-- THE CONJUNCTION, NOT THE HALVES. Every headline field takes BOTH `S.irCheck ir = true`
    and a `RunContractIR` of that same `ir`; gate 6 above checked the run alone, which is
    exactly how the S1 defect survived a green build: the two halves were individually
    inhabited and jointly empty. This is the exhibit the repair brief asks for - one object,
    one layout, one observation, both conjuncts, for every call relation and gas oracle. -/
theorem irHypothesis_jointlyInhabited (c : ExternalCalls) (g : ExternalGas) :
    ∃ (ir : YulObject) (irLyt : EVM.Layout) (obs : Obs),
      irSurface.irCheck ir = true ∧
        RunContractIR irSurface irW keccak256 ir irLyt irCd c g obs := by
  obtain ⟨obs, hrun⟩ := runContractIR_inhabited c g
  exact ⟨verifierIr, irLyt, obs, irCheck_holds_at_imported, hrun⟩

/-- The check the fixture used to hard-code: the naming function baked into the body
    instead of read off the Surface. Kept ONLY as the refutation below - nothing in the
    tree uses it to state an obligation, and `Surface.irCheck` no longer exists as a
    free field that could be filled with it. -/
def irCheckPreR60 (ir : YulObject) : Bool :=
  match ir.subObject (fxRuntimeName ir.name) with
  | some rt => ! unresolvedTop rt.codeBlock
  | none => false

/-- THE S1 DEFECT, EXHIBITED AS A FAILING CONJUNCTION rather than described. The old check
    rejects the imported object - `irCheckPreR60 verifierIr = false` - while the run
    relation accepts it, so a Surface carrying the old check satisfies `RunContractIR` and
    satisfies the negation of its own gate, and every field of the shape
    `irCheck ir = true -> ...` was vacuous at the real artifact. This is the demonstration
    (R-41) that the joint exhibit can fail: perturb `Surface.irCheck` back to a hard-coded
    name and `irHypothesis_jointlyInhabited` stops applying to the imported object while
    `runContractIR_inhabited` still does. -/
theorem s1_defect_refutes_the_conjunction (c : ExternalCalls) (g : ExternalGas) :
    irCheckPreR60 verifierIr = false ∧
      (∃ obs, RunContractIR irSurface irW keccak256 verifierIr irLyt irCd c g obs) :=
  ⟨by native_decide, runContractIR_inhabited c g⟩

/-- And the observation is a REVERT, not a stop and not a normal return: the run ends where the
    contract ends on an unroutable call. Without this the witness could be satisfied by a run
    that never reached the contract at all. -/
theorem witness_is_a_revert (c : ExternalCalls) (g : ExternalGas) :
    exists obs, RunContractIR irSurface irW keccak256 verifierIr irLyt irCd c g obs ∧
      obs.outcome = .halt ∧ (obs.state.halted).map (fun h => h.1) = some HaltKind.revert :=
  ⟨⟨committedState irSt0 irSt2, .halt⟩,
    ⟨⟨verifierRuntime, [], irRuntime_of_import, ⟨irSt2, importedRuntime_runs c g, rfl⟩⟩,
      rfl, rfl⟩⟩

/-- DECISION 1, OBSERVED: the imported ir leaves the free-memory pointer at 0x80. The deployed
    bytes leave it at 0x8e0; that gap is the trusted Yul-optimizer hop, and this is the state fact
    that says so. It is not observable through Bridge.ObsView, which excludes memory by design -
    which is exactly why ir_refines can be stated at view level over this run. -/
theorem witness_freePointer_is_the_ir_value : (freePtr irSt2 : U256) = 128 := rfl

/-- NON-VACUITY IN THE OTHER DIRECTION: the hypothesis is about THIS object. Give the Surface a
    runtimeName that does not name the imported sub-object and RunContractIR has no witness at
    all, because there is no runtime block to run. A definition that was always inhabited would
    not pass this. -/
theorem runContractIR_none_for_wrong_name (c : ExternalCalls) (g : ExternalGas) :
    ¬ (exists obs, RunContractIR { irSurface with runtimeName := fun _ => "nope" } irW
      keccak256 verifierIr irLyt irCd c g obs) := by
  rintro ⟨obs, rt, V, h⟩
  have hnone : ({ irSurface with runtimeName := fun _ => "nope" } :
      Surface rp RP RP RP).irRuntime verifierIr = none := rfl
  have : (none : Option YulBlock) = some rt := by rw [← hnone]; exact h.1
  cases this

/-! ### The statement form -/

/-- THE REQUIRED FINDING, AS SOMETHING THE ELABORATOR CHECKS. The shape PLAN 9.5 gives
    ir_refines - observational equivalence at view level between a run of the imported via-IR
    runtime and a run of the shell model - elaborates, over an object that exists in the tree
    and a hypothesis that this file exhibits a witness for. It is stated as a Prop, not proved:
    proving it is stage 6, and it needs the shell side of a REAL Surface (P-11 plan, P-13 AST
    emitter) and the stage-1 determinism obligations, none of which this package owns. What was
    blocking it was that the left-hand predicate could never hold. It can now. -/
example : Prop :=
  forall (c : ExternalCalls) (g : ExternalGas),
    (hloc : c.WorldLocal) ->
    ObsEquiv (RunContractIR irSurface irW keccak256 verifierIr irLyt irCd c g)
      (RunShell irSurface irW keccak256 irCd c g)

/-- The same for lowering_equivalence's first conjunct: the hypothesis is a pair of runs, both
    of which are now nameable, and the IR side of that pair is inhabited. -/
example : Prop :=
  forall (c : ExternalCalls) (g : ExternalGas),
    (∀ obs, RunContractIR irSurface irW keccak256 verifierIr irLyt irCd c g obs ->
      RunShell irSurface irW keccak256 irCd c g obs) ->
    forall obs, RunContractIR irSurface irW keccak256 verifierIr irLyt irCd c g obs ->
      exists obs', RunShell irSurface irW keccak256 irCd c g obs' ∧
        obs.view = obs'.view

/-! ### Gates -/

/-- GATE: the witness file is reachable and the run it exhibits is the one claimed. Red if the
    import stops starting with the prologue, if the dispatcher stops being the second statement,
    or if the fall-through stops being a user call into a revert body. -/
def importedIrWitness_ok : Bool :=
  verifierRuntime.length == 28 &&
    irSt0.env.calldata == [] &&
    irSt0.memory 64 == 0 &&
    irSt1.memory 95 == 128 &&
    irSt2.halted.map (fun h => h.1) == some HaltKind.revert &&
    (match irSurface.irRuntime verifierIr with
      | some rt => SyntaxEq.stmtsBeq rt verifierRuntime
      | none => false) &&
    freePtr irSt2 == 128 && freePtr irSt0 == 0

#eval importedIrWitness_ok                -- expect true

/-- THE GATE THAT WOULD HAVE CAUGHT S1. Not "irCheck is sometimes true" - the broken
    version was true on the fixture object - and not "a run exists" (gate 6, also true
    throughout). The two halves have to agree about the SAME object: line 1 is the check
    at the imported artifact, line 2 is the run relation reading the same runtime block
    out of the same naming field, line 3 is the pre-R-60 check REFUTING that object while
    the run accepted it, and line 4 is a name that names nothing failing BOTH halves
    together, which is what a projection guarantees and what a free field did not. -/
def irCheckAgreesWithRun_ok : Bool :=
  irSurface.irCheck verifierIr &&
    (match irSurface.irRuntime verifierIr with
      | some rt => SyntaxEq.stmtsBeq rt verifierRuntime
      | none => false) &&
    ! irCheckPreR60 verifierIr &&
    ! { irSurface with runtimeName := fun _ => "nope" }.irCheck verifierIr &&
    irSurface.runtimeName verifierIr.name == verifierRuntimeName

#eval irCheckAgreesWithRun_ok             -- expect true

/-! ### Axiom audit -/

-- The witness must not lean on anything the semantics does not compute. Expected: the three
-- axioms the quotation macro leaves behind, and no sorryAx.
#print axioms Midfall.Instances.ImportedIR.runContractIR_inhabited
#print axioms Midfall.Instances.ImportedIR.importedRuntime_runs
#print axioms Midfall.Instances.ImportedIR.witness_freePointer_is_the_ir_value

end Midfall.Instances.ImportedIR

import Midfall.Instances.FrameWalkWitness
import Midfall.Instances.RunShellInversion
import Midfall.Instances.CurveSurface
import Midfall.Yul.ShellModel
import Midfall.Lowering.InlineConstants
import YulSemantics.BigStep

/-!
Midfall/Instances/RunShellInhabited

P-INLINE deliverables 4 and 5: **RunShell IS INHABITED** at the curve Surface once D-P39's embedding
is applied, and LoweringCorrect.ir_refines is answered again from that starting point.

THE HEADLINE, AND IT IS A DERIVATION AND NOT A GATE. runShell_curveSurface_inhabited exhibits, for
every call relation and every gas oracle, an observation of RunShell curveSurface at the fixture
deployment world and the empty calldata. The run is the real one: the head guard passes on zero
memory, the two shell locals bind, the eight emitted helpers are Step.funDef no-ops, and the VK gate
- with EXPECTED_VK_LENGTH and EXPECTED_VK_CODEHASH_WORD now LITERALS because the constants were
inlined - evaluates, fails, and calls the emitted fail helper, which stores the selector and reverts
four bytes. RunShellInversion.no_arm_run proved that the same program WITHOUT the inlining has no
derivation at all, so the pair is the evidence that D-P39 is what changed: the inhabitation is not an
artefact of how RunShell is spelled, and no statement was weakened to get it.

WHY THE HALT IS A REVERT, AND WHY THAT IS NOT CHEATING. The frame has no extcode at the VK address
the locals bind, so the verifier's first guard fires. That is the same halt
RunEmitted.emittedWholeProgramStopsAt_ok and emittedWholeProgramRevertSelector_ok already pin for the
whole-program interpreter run, and it is a real run of the real emitted block. It is NOT a
verification and nothing here claims it is.

D-P23, BOTH HALVES, AS THEOREMS. Satisfiability: runShell_curveSurface_inhabited and
shell_run_reverts_four_bytes. Falsification: shell_run_is_not_the_wrap_run - the shell's halt payload
is four bytes where the dispatcher's is empty - so BOTH sides are inhabited and they are still
observably different, which is what makes ir_refines_refuted_at_curveSurface a refutation for a NEW
reason rather than the old emptiness one.

THE MECHANISM OF THE NEW REFUTATION, in one sentence: RunShell runs the ARM and ShellModel.wrap runs
the DISPATCHER, and on a calldata shorter than four bytes the dispatcher's size test skips the
selector switch entirely and falls through to revert(0, 0), while the arm runs the VK gate and
reverts with a four-byte selector. ObsView carries halted, and Bridge.RunCommitted is functional for
a functional call relation and gas oracle, so the dispatcher has EXACTLY ONE view at that frame and
it is not the shell's. That is the entry-path guard difference the brief named as the candidate, and
it is now the whole story: it was masked before only because one side was empty.

WHAT THIS PACKAGE DOES NOT SETTLE, stated rather than hidden: whether the fork should be closed by
making Surface.shell BE the dispatcher (F1) or by restating ir_refines' right-hand side to wrap (F2).
Both are in the package report; neither is decided here; ir_refines is not edited in the process.

TRUST. Kernel-checked throughout: rfl and decide, with two exceptions, both about WHICH statements the
generated program is rather than about the derivation - armDefs_are_defs and gateBody_decomp are
native_decide, because membership in a list of statements and the block-body split have no
kernel-decidable form at this dialect (Stmt carries no DecidableEq: Ast.lean:92-97). The axiom prints
at the foot of the file say exactly what each headline rests on.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

namespace Midfall.Instances.RunShellInhabited

open Midfall Midfall.Lowering Midfall.Instances.SurfaceFixture Midfall.Instances.CurveSurface
open Midfall.Instances.FrameWalkWitness Midfall.Instances.RunShellInversion
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

abbrev FOp := YulSemantics.EVM.Op
/-- **THE DIALECT IS CONCRETE, AND THAT IS THE POINT OF THE EXHIBIT.** The brief asked for a
    concrete run, and a concrete run is what this is: the empty call relation and the constant zero
    gas oracle, both world-local and both functional, which is exactly what 'ir_refines' quantifies
    over. Keeping the dialect concrete is also what makes every 'Builtin' fact below a kernel 'rfl':
    with 'c' and 'g' abstract, 'builtinWithExternal' will not reduce for 'and'. -/
abbrev OD0 : YulSemantics.Dialect := ShellModel.OD ExternalCalls.none (ExternalGas.ofFun fun _ => 0)
abbrev c0 : ExternalCalls := ExternalCalls.none
abbrev g0 : ExternalGas := ExternalGas.ofFun fun _ => 0

/-- The program RunShell curveSurface runs: the arm with the contract constants inlined. -/
def arm : List (Stmt FOp) := armInlined

/-- The shell's entry frame at the fixture deployment world and the empty calldata.
    curveSurface.shellLayout IS fxShellLayout by rfl, so this is the headline's frame. -/
def stF : EvmState := callState fxW fxShellLayout keccak256 (ByteArray.empty : Bytes)

theorem stF_mem : stF.memory = fun _ => 0 := rfl

/-- The state after the head guard's mload(64). -/
def st1 : EvmState := touchMemory stF 64 32

/-- The variable environment after the two shell locals are bound. -/
def V2 : VEnv (OD0) := [("success", (1 : U256)), ("vk", (4096 : U256))]
theorem get_vk : VEnv.get (D := OD0) V2 "vk" = some 4096 := rfl

/-! ### The shape of the program -/

theorem arm_hg : (arm.drop 0).headD (Stmt.block []) = hgStmt := rfl
theorem arm_vk : (arm.drop 1).headD (Stmt.block []) =
    Stmt.letDecl ["vk"] (some (Expr.lit (Literal.number 4096))) := rfl
theorem arm_su : (arm.drop 2).headD (Stmt.block []) =
    Stmt.letDecl ["success"] (some (Expr.lit (Literal.number 1))) := rfl

def armDefs : List (Stmt FOp) := (arm.drop 3).take 8
theorem armDefs_are_defs : forall d, d ∈ armDefs → isFunDefS d = true := by decide

/-- The gate's condition with the constants INLINED: 4577 and the codehash word are literals now, and
    ERR_VK_MISMATCH is a literal argument to the emitted fail. -/
def gateB : Expr FOp := Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"],
    Expr.lit (Literal.number 4577)]
def gateC : Expr FOp := Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
    Expr.lit (Literal.number 15933609736973938366157763540951553264596488184743928812768469146773639656731)]
def gateCond : Expr FOp := Expr.builtin Op.iszero [Expr.builtin Op.and [gateB, gateC]]
def gateFailBody : List (Stmt FOp) :=
  [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number 2756171582)])]
def gateCondStmt : Stmt FOp := Stmt.cond gateCond gateFailBody
def gate : Stmt FOp := (arm.drop 11).headD (Stmt.block [])
def gateBody : List (Stmt FOp) := match gate with | Stmt.block b => b | _ => []
/-- The gate block's own tail, after the VK check. -/
def gateTail : List (Stmt FOp) := gateBody.drop 1
/-- The ARM's statements after the gate block. -/
def gateRest : List (Stmt FOp) := arm.drop 12
theorem gate_is : gate = Stmt.block gateBody := rfl
theorem gateBody_decomp : gateBody = gateCondStmt :: gateTail := rfl
theorem arm_decomp : arm =
    [(arm.drop 0).headD (Stmt.block []), (arm.drop 1).headD (Stmt.block []),
      (arm.drop 2).headD (Stmt.block [])] ++ armDefs ++ [gate] ++ gateRest := rfl

/-- The emitted fail helper, as the inlined arm carries it. -/
def failBody : List (Stmt FOp) :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [Expr.lit (Literal.number 0),
      Expr.builtin Op.shl [Expr.lit (Literal.number 224), Expr.var "sel"]]),
   Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (Literal.number 0), Expr.lit (Literal.number 4)])]
def failDecl : FDecl (OD0) := { params := ["sel"], rets := [], body := failBody }

/-- The arm's hoisted function scope, named once so the derivation unfolds it once. -/
def armFuns : FScope (OD0) := hoist (OD0) arm

/-- The function environment the gate body runs in. -/
def funsGate : FunEnv (OD0) := hoist (OD0) gateBody :: armFuns :: []
/-- The function environment the CALLEE runs in: Step.callOk passes the definition site's scope. -/
def funsCallee : FunEnv (OD0) := hoist (OD0) failBody :: armFuns :: []
/-- The environment INSIDE the gate's if-body block: 'Step.block' conses that block's own hoisted
    scope, which is empty here but is still a scope, so the call below is stated against it rather
    than against 'funsGate'. -/
def funsFail : FunEnv (OD0) := hoist (OD0) gateFailBody :: funsGate

theorem lookup_fail : lookupFun funsFail "fail" = some (failDecl, armFuns :: []) := rfl

/-- The selector the emitted fail stores at address 0, and the states it writes and halts in. -/
def selWord : U256 := (2756171582 : U256) <<< 224
def st2 : EvmState := { touchMemory st1 0 32 with memory := storeWord st1.memory 0 selWord }
def stH : EvmState := { st2 with halted := some (.revert, readBytes st2.memory 0 4) }
def shellHaltData : List UInt8 := readBytes st2.memory 0 4
theorem shellHaltData_len : shellHaltData.length = 4 := rfl

/-! ### The gate condition evaluates to true -/

theorem bi_extcodesize : (OD0).Builtin Op.extcodesize [(4096 : U256)] st1
    (.ok [BitVec.ofNat 256 (st1.env.extCodeOf 4096).length] st1) := rfl
theorem bi_extcodehash : (OD0).Builtin Op.extcodehash [(4096 : U256)] st1
    (.ok [projectedCodeHash st1.env st1.env.balanceOf 4096] st1) := rfl
theorem bi_eq0 : (OD0).Builtin Op.eq
    [BitVec.ofNat 256 (st1.env.extCodeOf 4096).length, 4577] st1 (.ok [0] st1) := rfl
theorem bi_eq1 : (OD0).Builtin Op.eq
    [projectedCodeHash st1.env st1.env.balanceOf 4096,
      15933609736973938366157763540951553264596488184743928812768469146773639656731] st1
    (.ok [0] st1) := rfl
theorem bi_and0 : (OD0).Builtin Op.and [0, 0] st1 (.ok [0] st1) := rfl
theorem bi_iszero1 : (OD0).Builtin Op.iszero [0] st1 (.ok [1] st1) := rfl

/-- **THE GATE FIRES.** -/
theorem gate_step : Step (OD0) funsGate V2 st1 (.expr gateCond) (.eres (.vals [1] st1)) := by
  have hb : Step (OD0) funsGate V2 st1 (.expr gateB) (.eres (.vals [0] st1)) :=
    ShellModel.bi2 (Step.lit (D := OD0))
      (ShellModel.bi1 (ShellModel.varS get_vk) bi_extcodesize) bi_eq0
  have hc : Step (OD0) funsGate V2 st1 (.expr gateC) (.eres (.vals [0] st1)) :=
    ShellModel.bi2 (Step.lit (D := OD0))
      (ShellModel.bi1 (ShellModel.varS get_vk) bi_extcodehash) bi_eq1
  have ha : Step (OD0) funsGate V2 st1
      (.expr (Expr.builtin Op.and [gateB, gateC])) (.eres (.vals [0] st1)) :=
    ShellModel.bi2 hc hb bi_and0
  exact ShellModel.bi1 ha bi_iszero1

/-! ### The fail call, and the halt -/

theorem get_sel : VEnv.get (D := OD0) [("sel", (2756171582 : U256))] "sel" =
    some 2756171582 := rfl

theorem shl_step : Step (OD0) funsCallee [("sel", (2756171582 : U256))] st1
    (.expr (Expr.builtin Op.shl [Expr.lit (Literal.number 224), Expr.var "sel"]))
    (.eres (.vals [selWord] st1)) :=
  ShellModel.bi2 (ShellModel.varS get_sel) (Step.lit (D := OD0))
    (rfl : (OD0).Builtin Op.shl [224, 2756171582] st1 (.ok [selWord] st1))

theorem mstore_step : Step (OD0) funsCallee [("sel", (2756171582 : U256))] st1
    (.expr (Expr.builtin Op.mstore [Expr.lit (Literal.number 0),
      Expr.builtin Op.shl [Expr.lit (Literal.number 224), Expr.var "sel"]]))
    (.eres (.vals [] st2)) :=
  Step.builtinOk (D := OD0)
    (Step.argsCons (D := OD0) (Step.argsCons (D := OD0) (Step.argsNil (D := OD0)) shl_step)
      (Step.lit (D := OD0)))
    (rfl : (OD0).Builtin Op.mstore [0, selWord] st1 (.ok [] st2))

theorem revert_step : Step (OD0) funsCallee [("sel", (2756171582 : U256))] st2
    (.expr (Expr.builtin Op.revert [Expr.lit (Literal.number 0),
      Expr.lit (Literal.number 4)])) (.eres (.halt stH)) :=
  Step.builtinHalt (D := OD0)
    (Step.argsCons (D := OD0) (Step.argsCons (D := OD0) (Step.argsNil (D := OD0))
      (Step.lit (D := OD0))) (Step.lit (D := OD0)))
    (rfl : (OD0).Builtin Op.revert [0, 4] st2 (.halt stH))

/-- The body of the emitted fail helper, run as the callee. -/
theorem fail_body_run : Step (OD0) (armFuns :: []) [("sel", (2756171582 : U256))] st1
    (Code.stmt (Stmt.block failBody)) (.sres [("sel", (2756171582 : U256))] stH .halt) :=
  Step.block (D := OD0) (body := failBody) (funs := armFuns :: [])
    (V := [("sel", (2756171582 : U256))]) (st := st1)
    (Step.seqCons (D := OD0) (Step.exprStmt (D := OD0) mstore_step)
      (Step.seqStop (D := OD0) (Step.exprStmtHalt (D := OD0) revert_step)
        ShellModel.halt_ne_normal))

/-- The call to fail, as the gate body sees it. -/
theorem fail_call_step : Step (OD0) funsFail V2 st1
    (.expr (Expr.call "fail" [Expr.lit (Literal.number 2756171582)])) (.eres (.halt stH)) :=
  Step.callHalt (D := OD0)
    (Step.argsCons (D := OD0) (Step.argsNil (D := OD0)) (Step.lit (D := OD0)))
    lookup_fail (by decide : ([2756171582] : List U256).length = (["sel"] : List String).length)
    fail_body_run

/-- The gate body halts. Stated against the DECOMPOSED body and transferred by 'gateBody_decomp':
    unifying '.stmts gateBody' against (?s :: ?rest) would otherwise force the kernel to evaluate the
    whole generated program, which is the one reduction this file has measured at over a heartbeat
    budget. -/
theorem gate_body_run_decomp : Step (OD0) funsGate V2 st1 (Code.stmts (gateCondStmt :: gateTail))
    (.sres V2 stH .halt) :=
  Step.seqStop (D := OD0)
    (Step.ifTrue (D := OD0) gate_step ShellModel.one_ne_zero
      (Step.block (D := OD0) (body := gateFailBody) (funs := funsGate) (V := V2) (st := st1)
        (Step.seqStop (D := OD0)
          (Step.exprStmtHalt (D := OD0) fail_call_step) ShellModel.halt_ne_normal)))
    ShellModel.halt_ne_normal

theorem gate_body_run : Step (OD0) funsGate V2 st1 (Code.stmts gateBody) (.sres V2 stH .halt) := by
  rw [gateBody_decomp]
  exact gate_body_run_decomp

/-- The gate statement halts, in the arm's own function environment. -/
theorem gate_stmt_run : Step (OD0) (armFuns :: []) V2 st1 (Code.stmt gate)
    (.sres (restore (D := OD0) V2 V2) stH .halt) := by
  rw [gate_is]
  exact Step.block (D := OD0) (body := gateBody) (funs := armFuns :: []) (V := V2) (st := st1)
    gate_body_run

/-- One function definition is a no-op step. -/
theorem step_of_isFunDef {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    {d : Stmt FOp} (h : isFunDefS d = true) :
    Step (OD0) funs V st (.stmt d) (.sres V st .normal) := by
  obtain ⟨n, ps, rs, b, rfl⟩ := stmt_isFunDef h
  exact Step.funDef (D := OD0)

/-- A list of function definitions is a no-op step. -/
theorem stmts_of_defs {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState} :
    (defs : List (Stmt FOp)) -> (forall d, d ∈ defs → isFunDefS d = true) ->
    Step (OD0) funs V st (Code.stmts defs) (.sres V st .normal)
  | [], _ => Step.seqNil (D := OD0)
  | d :: ds, h =>
      Step.seqCons (D := OD0) (step_of_isFunDef (h d (by simp)))
        (stmts_of_defs ds (fun x hx => h x (by simp [hx])))

/-! ### The first three statements, and the whole arm -/

/-- The head guard passes and binds nothing. -/
theorem guard_stmt_run : Step (OD0) (armFuns :: []) [] stF
    (Code.stmt ((arm.drop 0).headD (Stmt.block []))) (.sres ([] : VEnv (OD0)) st1 .normal) := by
  rw [arm_hg, hgStmt_is]
  exact Step.ifFalse (D := OD0)
    (hgTest_step (funs := armFuns :: []) (W := fxW) (H := keccak256)
      (cd := (ByteArray.empty : Bytes))) ShellModel.zero_eq_zero

/-- The two shell locals bind. -/
theorem vk_stmt_run : Step (OD0) (armFuns :: []) [] st1
    (Code.stmt ((arm.drop 1).headD (Stmt.block []))) (.sres [("vk", (4096 : U256))] st1 .normal) := by
  rw [arm_vk]
  exact Step.letVal (D := OD0) (Step.lit (D := OD0)) rfl

theorem su_stmt_run : Step (OD0) (armFuns :: []) [("vk", (4096 : U256))] st1
    (Code.stmt ((arm.drop 2).headD (Stmt.block []))) (.sres V2 st1 .normal) := by
  rw [arm_su]
  exact Step.letVal (D := OD0) (Step.lit (D := OD0)) rfl

/-- A chunk of function definitions in front of a list of statements does not change the
    environment or the state, so a run of the tail extends to a run of the whole. Written this way
    (rather than as a general chunk lemma) because a 'funDef' step is exactly the case where both
    stay fixed - which is what makes the induction close. -/
theorem seq_after_defs {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState} :
    (defs : List (Stmt FOp)) -> (forall d, d ∈ defs → isFunDefS d = true) ->
      (l₂ : List (Stmt FOp)) -> {V' : VEnv (OD0)} -> {st' : EvmState} -> {o : Outcome} ->
      Step (OD0) funs V st (Code.stmts l₂) (Res.sres V' st' o) ->
      Step (OD0) funs V st (Code.stmts (defs ++ l₂)) (Res.sres V' st' o)
  | [], _, l₂, _, _, _, h₂ => h₂
  | d :: ds, h, l₂, V', st', o, h₂ =>
      Step.seqCons (D := OD0) (step_of_isFunDef (h d (by simp)))
        (seq_after_defs ds (fun x hx => h x (by simp [hx])) l₂ h₂)
/-- The derivation, stated against the arm's own decomposition. The pieces ARE the elements of that
    decomposition by definition, so no rewriting is needed to line them up; the transfer to 'arm'
    happens once, at the top, by 'arm_decomp'. -/
theorem arm_pieces_run :
    Step (OD0) (armFuns :: []) [] stF
      (Code.stmts ([(arm.drop 0).headD (Stmt.block []), (arm.drop 1).headD (Stmt.block []),
        (arm.drop 2).headD (Stmt.block [])] ++ armDefs ++ ([gate] ++ gateRest)))
      (Res.sres V2 stH .halt) :=
  Step.seqCons (D := OD0) guard_stmt_run
    (Step.seqCons (D := OD0) vk_stmt_run
      (Step.seqCons (D := OD0) su_stmt_run
        (seq_after_defs armDefs armDefs_are_defs ([gate] ++ gateRest)
          (Step.seqStop (D := OD0) gate_stmt_run ShellModel.halt_ne_normal))))

/-- **THE ARM RUNS.** A Step derivation of the whole inlined program from the shell's entry frame,
    ending in the VK-mismatch revert. 'arm' IS 'curveSurface.shell.codeBlock' and 'stF' IS the
    Surface's 'callState' - both by 'rfl' - so this is a derivation of the program the headline's
    run relation runs, not of a model of it. -/
theorem arm_derivation :
    Step (OD0) [] [] stF (Code.stmt (Stmt.block arm))
      (Res.sres (restore (D := OD0) [] V2) stH .halt) :=
  Step.block (D := OD0) (body := arm) (funs := []) (V := []) (st := stF)
    (by rw [arm_decomp]; exact arm_pieces_run)

/-- The same, packaged. -/
theorem arm_run : exists (V : VEnv (OD0)) (st : EvmState),
    Step (OD0) [] [] stF (Code.stmt (Stmt.block arm)) (Res.sres V st .halt) :=
  ⟨restore (D := OD0) [] V2, stH, arm_derivation⟩
/-- **THE HEADLINE: RunShell IS INHABITED AT THE CURVE SURFACE.** The empty call relation and the
    constant zero gas oracle - both world-local and both functional, which is what 'ir_refines'
    quantifies over. The run never reaches a call-family builtin, so it does not care how the
    precompiles answer. Contrast RunShellInversion.no_arm_run, about the same program with the
    embedding removed. -/
theorem runShell_curveSurface_inhabited :
    exists obs, RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes)
      ExternalCalls.none (ExternalGas.ofFun fun _ => 0) obs :=
  ⟨⟨committedState stF stH, .halt⟩, restore (D := OD0) [] V2, stH, arm_derivation, rfl⟩

/-- A revert does not commit, so the committed state keeps the halt record verbatim. -/
theorem committedState_revert_halted (st0 st' : EvmState) (d : List UInt8)
    (h : st'.halted = some (.revert, d)) :
    (committedState st0 st').halted = some (.revert, d) := by
  have hc : ((HaltKind.revert : HaltKind).commits = false) := rfl
  simp [committedState, h, hc]

/-- **AND WHAT IT HALTS WITH.** The revert payload is four bytes - the VK-mismatch selector the
    emitted fail helper stores at address 0. -/
theorem shell_run_reverts_four_bytes :
    exists obs, RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes)
      ExternalCalls.none (ExternalGas.ofFun fun _ => 0) obs ∧
      obs.state.halted = some (.revert, shellHaltData) ∧ shellHaltData.length = 4 := by
  refine ⟨⟨committedState stF stH, .halt⟩, ⟨restore (D := OD0) [] V2, stH, arm_derivation, rfl⟩,
    committedState_revert_halted stF stH shellHaltData rfl, shellHaltData_len⟩

/-! ### The dispatcher side, and the new refutation -/

/-- The dispatcher's view at the same frame: revert with an EMPTY payload. -/
theorem wrap_empty_cd_reverts_nil :
    exists obs, ShellModel.wrap curveSurface fxW keccak256 (ByteArray.empty : Bytes)
      ExternalCalls.none (ExternalGas.ofFun fun _ => 0) obs ∧
      obs.state.halted = some (.revert, []) := by
  have hsize : ShellModel.sizeTestValue stF = 0 := rfl
  obtain ⟨st', hrun, hor⟩ :=
    ShellModel.unroutable_calldata_reverts (body := ShellModel.armBody curveSurface) hsize
  refine ⟨⟨committedState stF st', .halt⟩, ⟨[], ⟨st', hrun, rfl⟩⟩,
    committedState_revert_halted stF st' [] hor⟩

/-- **THE TWO SIDES DISAGREE IN THE HALT PAYLOAD**, with BOTH sides inhabited. -/
theorem shell_run_is_not_the_wrap_run : shellHaltData ≠ ([] : List UInt8) := by
  intro h
  exact absurd h (by decide : ¬(shellHaltData = ([] : List UInt8)))

theorem noCalls_worldLocal : ExternalCalls.WorldLocal ExternalCalls.none :=
  fun _ _ _ _ _ => Iff.rfl
theorem noCalls_functional : ExternalCalls.Functional ExternalCalls.none := by
  intro req st r₁ r₂ h₁ h₂; cases h₁
theorem gas_functional : (ExternalGas.ofFun (fun _ => (0 : U256))).Functional :=
  fun _ _ _ h₁ h₂ => h₁.trans h₂.symm

/-- **THE ANSWER TO THE QUESTION THIS PACKAGE EXISTS TO ANSWER.**

SHORT ANSWER: the P-RUNSHELL refutation of 'ir_refines' is RETRACTED - it was an artefact of the
shell side being empty - and what replaces it is a REDUCTION, not a new refutation. The field is
neither provable nor refuted by this package, and the reason is named: 'ObsEquiv' needs a
'no IR run realises the shell view' statement, and the only route to that here is uniqueness of the
committed run at the OPEN dialect, i.e. 'Bridge.RunCommitted.det', which inherits the registered hole
'Bridge.dialect_deterministic' (SORRY.md: 'Midfall/Yul/Bridge.lean | 186'). So the refutation is
stated BELOW AS A CONDITIONAL THEOREM whose hypothesis is exactly that uniqueness, and the unconditional
content is the three theorems above it: the shell run exists and reverts with four bytes,
the dispatcher run exists and reverts with none, and those two payloads are different.

THE MECHANISM, which IS established unconditionally: the entry-path guard difference the brief named
as the candidate. 'wrap' runs the callvalue guard and the thirteen ABI bounds tests behind a
calldatasize test; on a calldata shorter than four bytes the switch is skipped entirely and the
dispatcher falls through to 'revert(0, 0)'. 'RunShell' runs the arm alone, whose first executed
non-definition statement is the VK gate, which fails and reverts with a four-byte selector. Both
sides are now inhabited, and they disagree in 'ObsView.halted'. That is a real difference between two
real runs, not an emptiness artefact - and it is the F1/F2 fork the package report names.
-/
theorem ir_refines_refuted_at_curveSurface_of_unique_wrap
    (hunique : forall (o : Midfall.Yul.Bridge.Obs),
        RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
          curveSurface.shellLayout (ByteArray.empty : Bytes) ExternalCalls.none
          (ExternalGas.ofFun fun _ => 0) o ->
          forall (oSh : Midfall.Yul.Bridge.Obs),
          RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) ExternalCalls.none
            (ExternalGas.ofFun fun _ => 0) oSh ->
          o.view ≠ oSh.view) :
    ¬ ObsEquiv
        (RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
          curveSurface.shellLayout (ByteArray.empty : Bytes) ExternalCalls.none
          (ExternalGas.ofFun fun _ => 0))
        (RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) ExternalCalls.none
          (ExternalGas.ofFun fun _ => 0)) := by
  intro h
  unfold ObsEquiv at h
  obtain ⟨obsSh, hsh, hShalt, -⟩ := shell_run_reverts_four_bytes
  obtain ⟨oIr, hIr, hv⟩ := (h obsSh.view).2 ⟨obsSh, hsh, rfl⟩
  exact hunique oIr hIr obsSh hsh hv

/-! ### P-DET: the hypothesis of the theorem above is now a PROOF, so the refutation is UNCONDITIONAL -/

/-- **THE UNIQUENING STEP, AND IT IS NO LONGER A HYPOTHESIS.** Two committed runs of the SAME program
    from the SAME frame at the fixture dialect have the same view. This is 'Bridge.RunCommitted.det'
    read at 'c0' and 'g0', and the only reason it was out of reach before P-DET is that
    'RunCommitted.det' inherits 'Bridge.dialect_deterministic' - the registered hole at
    Bridge.lean:186, which P-DET CLOSED as a theorem, TRUE EXACTLY AS REGISTERED. Both functionality
    hypotheses are discharged at the concrete oracles above ('noCalls_functional', 'gas_functional'). -/
theorem view_eq_of_committed_runs {prog : Block FOp} {st0 : EvmState}
    {V₁ V₂ : VEnv OD0} {s₁ s₂ : EvmState} {o₁ o₂ : Outcome}
    (h₁ : RunCommitted c0 g0 prog st0 V₁ s₁ o₁)
    (h₂ : RunCommitted c0 g0 prog st0 V₂ s₂ o₂) :
    (⟨s₁, o₁⟩ : Midfall.Yul.Bridge.Obs).view = (⟨s₂, o₂⟩ : Midfall.Yul.Bridge.Obs).view := by
  obtain ⟨rfl, rfl, rfl⟩ := RunCommitted.det noCalls_functional gas_functional h₁ h₂
  rfl

/-- So the SHELL side has exactly one view at the fixture frame: the four-byte VK-mismatch revert. -/
theorem runShell_view_unique {o₁ o₂ : Midfall.Yul.Bridge.Obs}
    (h₁ : RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) c0 g0 o₁)
    (h₂ : RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) c0 g0 o₂) :
    o₁.view = o₂.view := by
  obtain ⟨V₁, hr₁⟩ := h₁
  obtain ⟨V₂, hr₂⟩ := h₂
  exact view_eq_of_committed_runs hr₁ hr₂

/-- And the IR side has exactly one view: the dispatcher's empty revert. The runtime sub-object is
    pinned by 'S.irRuntime ir = some rt' - a function - so two runs cannot disagree about WHICH
    block they ran, which is what makes the uniqueness argument go through at all. -/
theorem runContractIR_view_unique {o₁ o₂ : Midfall.Yul.Bridge.Obs}
    (h₁ : RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
      curveSurface.shellLayout (ByteArray.empty : Bytes) c0 g0 o₁)
    (h₂ : RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
      curveSurface.shellLayout (ByteArray.empty : Bytes) c0 g0 o₂) :
    o₁.view = o₂.view := by
  obtain ⟨rt₁, V₁, hrt₁, hr₁⟩ := h₁
  obtain ⟨rt₂, V₂, hrt₂, hr₂⟩ := h₂
  have hrt : rt₁ = rt₂ := (Option.some.inj hrt₁).symm.trans (Option.some.inj hrt₂)
  subst hrt
  exact view_eq_of_committed_runs hr₁ hr₂

/-- **THE HYPOTHESIS, DISCHARGED.** No run of the model IR at the fixture frame has the shell's view,
    and conversely - the two sides have ONE view each and those views differ in 'ObsView.halted'. -/
theorem ir_refines_hunique_at_curveSurface :
    forall (o : Midfall.Yul.Bridge.Obs),
      RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
        curveSurface.shellLayout (ByteArray.empty : Bytes) ExternalCalls.none
        (ExternalGas.ofFun fun _ => 0) o ->
        forall (oSh : Midfall.Yul.Bridge.Obs),
        RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) ExternalCalls.none
          (ExternalGas.ofFun fun _ => 0) oSh ->
        o.view ≠ oSh.view := by
  intro o ho oSh hSh hEq
  obtain ⟨obsSh, hsh, hShalt, -⟩ := shell_run_reverts_four_bytes
  obtain ⟨obsIr, hir, hIrhalt⟩ := wrap_empty_cd_reverts_nil
  have hIr : RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
      curveSurface.shellLayout (ByteArray.empty : Bytes) c0 g0 obsIr :=
    (ShellModel.wrap_iff_modelRunContractIR curveSurface fxW keccak256
      (ByteArray.empty : Bytes) c0 g0 obsIr).mpr hir
  have h1 : o.view = obsIr.view := runContractIR_view_unique ho hIr
  have h2 : oSh.view = obsSh.view := runShell_view_unique hSh hsh
  rw [h1, h2] at hEq
  have hh := halted_of_view_eq hEq
  have hEq2 : (some (.revert, []) : Option (HaltKind × List UInt8)) = some (.revert, shellHaltData) :=
    hIrhalt.symm.trans (hh.trans hShalt)
  exact shell_run_is_not_the_wrap_run
    ((congrArg Prod.snd (Option.some.inj hEq2))).symm

/-- **THE REQUIRED FINDING OF P-INLINE, NOW UNCONDITIONALLY: 'ir_refines' IS FALSE AT THE CURVE
    SURFACE.** Read the field as 'LoweringCorrect.ir_refines' (Obligations.lean:316) at
    'S := curveSurface' and instantiate its binders with the in-tree model object, the Surface's own
    shell layout, the fixture world and hash, the EMPTY calldata, the empty call relation and the
    constant-zero gas oracle. Every hypothesis of the field holds at that instantiation -
    'ShellModel.modelIr_irCheck' gives 'irCheck (modelIr curveSurface) = true' and
    'noCalls_worldLocal' gives the world-locality the field asks for - and the conclusion is FALSE. -/
theorem ir_refines_refuted_at_curveSurface :
    ¬ ObsEquiv
        (RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
          curveSurface.shellLayout (ByteArray.empty : Bytes) ExternalCalls.none
          (ExternalGas.ofFun fun _ => 0))
        (RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) ExternalCalls.none
          (ExternalGas.ofFun fun _ => 0)) :=
  ir_refines_refuted_at_curveSurface_of_unique_wrap ir_refines_hunique_at_curveSurface

/-- **D-P23, THE FALSIFICATION HALF OF THE REFUTATION ITSELF.** The refutation is not vacuous: the
    instantiation it refutes at satisfies every hypothesis of the field. Both sides are inhabited -
    'runShell_curveSurface_inhabited' and 'wrap_empty_cd_reverts_nil' - and the two hypotheses the
    field asks for are theorems at this instantiation, not assumptions. -/
theorem ir_refines_hypotheses_hold_at_the_refuted_instantiation :
    curveSurface.irCheck (ShellModel.modelIr curveSurface) = true ∧
      (ExternalCalls.none : YulSemantics.EVM.ExternalCalls).WorldLocal ∧
      (exists o, RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) c0 g0 o) ∧
      (exists o, RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
        curveSurface.shellLayout (ByteArray.empty : Bytes) c0 g0 o) := by
  refine ⟨ShellModel.modelIr_irCheck curveSurface, noCalls_worldLocal,
    runShell_curveSurface_inhabited, ?_⟩
  obtain ⟨obsIr, hir, -⟩ := wrap_empty_cd_reverts_nil
  exact ⟨obsIr,
    (ShellModel.wrap_iff_modelRunContractIR curveSurface fxW keccak256
      (ByteArray.empty : Bytes) c0 g0 obsIr).mpr hir⟩

/-- **THE CONSEQUENCE THE BUNDLE HAS TO LIVE WITH: THE CURVE SURFACE CANNOT DISCHARGE
    'LoweringCorrect' AT ALL, FOR ANY 'product'.** This is the conclusion P-RUNSHELL reached by shell
    emptiness and P-INLINE retracted along with six others - arrived at again, by a different and
    better-founded route. The mechanism is NOT emptiness this time: BOTH sides are inhabited
    ('runShell_curveSurface_inhabited', 'wrap_empty_cd_reverts_nil') and they disagree because the
    bare arm has no entry path and the dispatcher does. So the bundle has a FALSE field at this
    Surface, not an unproved one, and 'lowering_equivalence curveSurface product' is vacuous for every
    product however many of its other seven fields hold. 'ir_refines' was NOT edited to make this
    true; D-P42 records the decision this forces. -/
theorem curveSurface_not_LoweringCorrect (product : Midfall.Yul.PairingProduct) :
    ¬ LoweringCorrect curveSurface product := by
  intro hc
  exact ir_refines_refuted_at_curveSurface
    (hc.ir_refines (ShellModel.modelIr curveSurface) curveSurface.shellLayout
      (ShellModel.modelIr_irCheck curveSurface) fxW keccak256 (ByteArray.empty : Bytes)
      ExternalCalls.none 0 noCalls_worldLocal)

/-! ### Independent measurement: the entry path is the whole difference (D-P23, KAT form)

The theorems above prove the disagreement through the big-step 'Step' relation. These two gates
measure the SAME fact through a completely different engine - the vendored fuel interpreter
'YulSemantics.Interp.run' at the closed 'EVM.exec' dialect - which is what makes them an independent
measurement rather than a restatement: they never call 'arm_derivation', 'RunCommitted.det' or any
lemma above. Both runs use the SAME body 'arm'; the only difference is whether 'ShellModel.dispatcher
puts the entry path in front of it. That is the F2 mechanism of D-P42, measured.

FUEL SHAPE, and it is the reason these two lines cost 3 s and not 18 min: 'Interp.run' charges fuel
per NESTING LEVEL, so a walk over the generated AST is linear in the program's depth. Any fuel-bounded
walk that charges per LIST ELEMENT is pathological on a program this size - the measurement is on
the record in P-INLINE and in the P-DET brief.
-/

/-- The dispatcher over the arm reverts with ZERO bytes at the shell's own frame: the size test skips
    the switch and the fall-through 'revert(0, 0)' fires. -/
def dispatcher_reverts_zero_bytes_ok : Bool :=
  match YulSemantics.Interp.run EVM.exec 20000 (ShellModel.dispatcher arm) stF with
  | .ok (_, st, _) => match st.halted with
      | some (.revert, d) => d.length == 0
      | _ => false
  | _ => false

#eval dispatcher_reverts_zero_bytes_ok -- expect true

/-- The bare arm at the same frame reverts with FOUR bytes: the VK-mismatch selector the emitted fail
    helper stores at address 0. Same body, same frame, no entry path - a different halt payload. -/
def arm_reverts_four_bytes_ok : Bool :=
  match YulSemantics.Interp.run EVM.exec 20000 arm stF with
  | .ok (_, st, _) => match st.halted with
      | some (.revert, d) => d.length == 4
      | _ => false
  | _ => false

#eval arm_reverts_four_bytes_ok -- expect true


#print axioms Midfall.Instances.RunShellInhabited.curveSurface_not_LoweringCorrect
#print axioms Midfall.Instances.RunShellInhabited.ir_refines_refuted_at_curveSurface
#print axioms Midfall.Instances.RunShellInhabited.runShell_curveSurface_inhabited
#print axioms Midfall.Instances.RunShellInhabited.shell_run_reverts_four_bytes
#print axioms Midfall.Instances.RunShellInhabited.ir_refines_refuted_at_curveSurface_of_unique_wrap

end Midfall.Instances.RunShellInhabited

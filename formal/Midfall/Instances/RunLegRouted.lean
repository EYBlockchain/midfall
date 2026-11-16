import Midfall.Instances.RunShellInhabited
import Midfall.Instances.ImportedIR
import YulSemantics.Interp

/-!
Midfall/Instances/RunLegRouted

P-RUNLEG (docs/plans/P-RUNLEG.md). THE RUN LEG, AND THE LIVE ATTACK ON D-P42: construct a calldata
the dispatcher ACTUALLY ROUTES, evaluate both run relations on it, and see whether the disagreement
between 'RunShell' and 'ShellModel.wrap' that D-P42 called CONSTRUCTIVE is a property of the entry
path or only of the EMPTY calldata. D-P42's own falsifiability paragraph named this test - item (i),
"a routed-calldata comparison showing the disagreement is an artefact of the empty calldata" - and
this file is that test, run honestly.

THE ANSWER, AND IT IS BOTH WAYS AT ONCE. D-P42's CONCLUSION SURVIVES: the two sides still disagree
on a routed calldata, so the disagreement is not an artefact of the empty input. But the MECHANISM
D-P42 recorded is the mechanism of the UNROUTABLE input only, and it is NOT what makes the routed
comparison fail. 'ShellModel.armBody S = S.L.headGuard ++ S.bindLocals ++ S.L.main' is the
UN-INLINED fragment - D-P39 left it alone on purpose, because changing it would change 'wrap' - and
it still carries 59 free contract-level identifiers, among them 'EXPECTED_VK_LENGTH' and
'EXPECTED_VK_CODEHASH_WORD'. The dispatcher's own entry path binds 'vk' and 'quotientEvaluator'
from the immutables and NOTHING ELSE, so on a routed calldata the dispatcher ENTERS the arm and
gets STUCK at the VK gate: 'wrap curveSurface' has no observation at all there, while 'RunShell'
has exactly one and it is the four-byte VK-mismatch revert. TWO MECHANISMS, therefore, and they are
distinct: at the unroutable input both sides run and their halt PAYLOADS differ (zero bytes against
four); at the routed input the model side does not run at all.

TWO MECHANISMS, NAMED PRECISELY, because the repair differs for each:
  M1 (unroutable calldata, 'cd.length < 4'): the dispatcher's size test 'iszero(lt(calldatasize(),4))'
     fails, the selector switch is skipped, and the runtime falls through to 'revert(0, 0)' - zero
     bytes. The bare arm runs the VK gate and reverts with FOUR bytes. Both sides inhabited; the
     views differ in 'ObsView.halted'. This is the difference D-P42 describes, and it is real.
  M2 (routed calldata): the entry path is NOT the obstruction - the control below shows the
     dispatcher over the CLOSED (inlined) arm reverting with the same four bytes as the bare arm
     (measured by 'routed_comparison_ok' through the fuel interpreter, and transported by
     'control_of_arm_block_run', whose hypothesis is the arm's own run from the arm frame) - the
     obstruction is that the model's arm is the OPEN fragment. 'wrap' is uninhabited there, as a
     THEOREM ('wrap_routed_uninhabited'), not as a measurement. Restating 'ir_refines' right-hand
     side to 'wrap' (D-P42's F2) therefore repairs nothing at 'curveSurface': it swaps a side that
     disagrees for a side that is empty.

WHAT THIS FILE DOES NOT DO. It does not edit 'ir_refines', does not restate its right-hand side, and
does not touch 'ShellModel.armBody' - making the model's arm the closed program is the repair the
evidence points at, but it is a statement change and needs its own recorded decision (D-P43).

SECOND DELIVERABLE, LANDED FIRST: 'ir_refines_refuted_at_the_imported_artifact' - retracted by
P-INLINE and never re-established - is back, at the REAL solc artifact, unconditionally. The route
is cheap and it is not the one the retraction suspected: 'irSt0 = stF' and
'irSurface.shell.codeBlock = armInlined' both hold by 'rfl', so the curve-surface shell derivation
transplants verbatim, and 'ImportedIR.importedRuntime_runs' already gave the artifact a run at EVERY
call relation and gas oracle. Both sides have exactly one view ('Bridge.RunCommitted.det', a theorem
since P-DET) and the views differ in the halt payload: the artifact reverts with zero bytes, the
shell with four. Every hypothesis of the field holds at the instantiation - D-P23's falsification
half is 'ir_refines_hypotheses_hold_at_the_imported_instantiation', a theorem.

TRUST. Kernel-checked throughout: 'rfl', 'decide' and 'Step' derivations, plus 'Step.det' against
'Bridge.dialect_deterministic' (proved by P-DET) to pin the entry path. The axiom prints at the foot
of each section say what each headline rests on: the five curve-pairing assumptions the Surfaces
themselves are built on, 'propext', 'Classical.choice', 'Quot.sound', and - inherited from the
fixture's own 'realSurface' definition, not introduced here - one 'native_decide' axiom.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option maxRecDepth 4000000
set_option maxHeartbeats 3000000

namespace Midfall.Instances.RunLegRouted

/-! ### 1. THE RETRACTED REFUTATION, RE-ESTABLISHED AT THE REAL SOLC ARTIFACT

'irSurface' is 'realSurface' with 'runtimeName' pointed at the imported object's runtime sub-object,
'irW'/'irLyt' are the fixture world and shell layout, and 'irCd' is the EMPTY calldata - the one
input the dispatcher cannot route. 'ImportedIR' exhibits a committed run of the real imported
runtime at that frame for every call relation and every gas oracle; D-P39 gave the shell side a run
at the same frame; P-DET made each side's view unique. The three together are the refutation. -/


open Midfall Midfall.Lowering Midfall.Instances.SurfaceFixture Midfall.Instances.CurveSurface
open Midfall.Instances.FrameWalkWitness Midfall.Instances
open Midfall.Instances.RunShellInhabited Midfall.Instances.ImportedIR
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-- The empty frame at 'irSurface' IS the fixture shell frame 'stF'. -/
example : irSt0 = stF := rfl

/-- The shell side at 'irSurface' is INHABITED, and by the same derivation as at 'curveSurface'. -/
theorem runShell_irSurface_inhabited :
    exists obs, RunShell irSurface irW keccak256 irCd c0 g0 obs :=
  ⟨⟨committedState stF stH, .halt⟩, restore (D := OD0) [] V2, stH, arm_derivation, rfl⟩

theorem runShell_irSurface_reverts_four_bytes :
    exists obs, RunShell irSurface irW keccak256 irCd c0 g0 obs ∧
      obs.state.halted = some (.revert, shellHaltData) ∧ shellHaltData.length = 4 := by
  refine ⟨⟨committedState stF stH, .halt⟩, ⟨restore (D := OD0) [] V2, stH, arm_derivation, rfl⟩,
    committedState_revert_halted stF stH shellHaltData rfl, shellHaltData_len⟩

/-- The shell side has exactly one view at 'irSurface'. -/
theorem runShell_irSurface_view_unique {o₁ o₂ : Midfall.Yul.Bridge.Obs}
    (h₁ : RunShell irSurface irW keccak256 irCd c0 g0 o₁)
    (h₂ : RunShell irSurface irW keccak256 irCd c0 g0 o₂) :
    o₁.view = o₂.view := by
  obtain ⟨V₁, hr₁⟩ := h₁
  obtain ⟨V₂, hr₂⟩ := h₂
  exact view_eq_of_committed_runs hr₁ hr₂

/-- The artifact's halt at the unroutable input: revert with ZERO bytes. -/
theorem artifact_irSurface_reverts_nil :
    exists obs, RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0 obs ∧
      obs.state.halted = some (.revert, []) := by
  refine ⟨⟨committedState irSt0 irSt2, .halt⟩,
    ⟨Midfall.Yul.Ir.verifierRuntime, [], irRuntime_of_import, ⟨irSt2, importedRuntime_runs c0 g0, rfl⟩⟩, ?_⟩
  exact committedState_revert_halted irSt0 irSt2 [] rfl

theorem runContractIR_irSurface_view_unique {o₁ o₂ : Midfall.Yul.Bridge.Obs}
    (h₁ : RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0 o₁)
    (h₂ : RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0 o₂) :
    o₁.view = o₂.view := by
  obtain ⟨rt₁, V₁, hrt₁, hr₁⟩ := h₁
  obtain ⟨rt₂, V₂, hrt₂, hr₂⟩ := h₂
  have hrt : rt₁ = rt₂ := (Option.some.inj hrt₁).symm.trans (Option.some.inj hrt₂)
  subst hrt
  exact view_eq_of_committed_runs hr₁ hr₂

theorem ir_refines_refuted_at_irSurface_of_unique
    (hunique : forall (o : Midfall.Yul.Bridge.Obs),
        RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0 o ->
        forall (oSh : Midfall.Yul.Bridge.Obs),
        RunShell irSurface irW keccak256 irCd c0 g0 oSh -> o.view ≠ oSh.view) :
    ¬ ObsEquiv
        (RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0)
        (RunShell irSurface irW keccak256 irCd c0 g0) := by
  intro h
  unfold ObsEquiv at h
  obtain ⟨obsSh, hsh, hShalt, -⟩ := runShell_irSurface_reverts_four_bytes
  obtain ⟨oIr, hIr, hv⟩ := (h obsSh.view).2 ⟨obsSh, hsh, rfl⟩
  exact hunique oIr hIr obsSh hsh hv

/-- No artifact view equals the shell view. -/
theorem ir_refines_hunique_at_irSurface :
    forall (o : Midfall.Yul.Bridge.Obs),
      RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0 o ->
      forall (oSh : Midfall.Yul.Bridge.Obs),
      RunShell irSurface irW keccak256 irCd c0 g0 oSh ->
      o.view ≠ oSh.view := by
  intro o ho oSh hSh hEq
  obtain ⟨obsSh, hsh, hShalt, -⟩ := runShell_irSurface_reverts_four_bytes
  obtain ⟨obsIr, hir, hIrhalt⟩ := artifact_irSurface_reverts_nil
  have h1 : o.view = obsIr.view := runContractIR_irSurface_view_unique ho hir
  have h2 : oSh.view = obsSh.view := runShell_irSurface_view_unique hSh hsh
  rw [h1, h2] at hEq
  have hh := halted_of_view_eq hEq
  have hEq2 : (some (.revert, []) : Option (HaltKind × List UInt8)) =
      some (.revert, shellHaltData) := hIrhalt.symm.trans (hh.trans hShalt)
  exact shell_run_is_not_the_wrap_run
    ((congrArg Prod.snd (Option.some.inj hEq2))).symm

/-- **THE RETRACTED THEOREM, RE-ESTABLISHED.** -/
theorem ir_refines_refuted_at_the_imported_artifact :
    ¬ ObsEquiv
        (RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0)
        (RunShell irSurface irW keccak256 irCd c0 g0) :=
  ir_refines_refuted_at_irSurface_of_unique ir_refines_hunique_at_irSurface

/-- D-P23 falsification half. -/
theorem ir_refines_hypotheses_hold_at_the_imported_instantiation :
    irSurface.irCheck Midfall.Yul.Ir.verifierIr = true ∧
      (ExternalCalls.none : YulSemantics.EVM.ExternalCalls).WorldLocal ∧
      (exists o, RunShell irSurface irW keccak256 irCd c0 g0 o) ∧
      (exists o, RunContractIR irSurface irW keccak256 Midfall.Yul.Ir.verifierIr irLyt irCd c0 g0 o) := by
  refine ⟨irCheck_holds_at_imported, noCalls_worldLocal, runShell_irSurface_inhabited, ?_⟩
  obtain ⟨obsIr, hir, -⟩ := artifact_irSurface_reverts_nil
  exact ⟨obsIr, hir⟩

/-- Consequence: 'irSurface' cannot discharge 'LoweringCorrect' for any product. -/
theorem irSurface_not_LoweringCorrect (product : Midfall.Yul.PairingProduct) :
    ¬ LoweringCorrect irSurface product := by
  intro hc
  exact ir_refines_refuted_at_the_imported_artifact
    (hc.ir_refines Midfall.Yul.Ir.verifierIr irLyt irCheck_holds_at_imported irW keccak256 irCd
      ExternalCalls.none 0 noCalls_worldLocal)

#print axioms Midfall.Instances.RunLegRouted.ir_refines_refuted_at_the_imported_artifact
#print axioms Midfall.Instances.RunLegRouted.irSurface_not_LoweringCorrect






/-! ### 2. THE ROUTED CALLDATA, AND THE SHELL SIDE OF THE COMPARISON -/

/-- The routed calldata: 'ShellModel.cdWellFormed', the file's own 228-byte well-formed witness,
    as the 'Bytes' a frame carries. -/
def cdR : Bytes := ByteArray.mk ShellModel.cdWellFormed.toArray

/-- The frame 'RunShell curveSurface' runs in at the routed calldata. -/
def stR : EvmState := callState fxW fxShellLayout keccak256 cdR

theorem cdR_hsel : Midfall.bytesTake cdR 0 4 = some Midfall.Generator.fnSigVerifyProof := rfl
theorem cdR_len : cdR.size = 228 := rfl
theorem stR_mem : stR.memory = fun _ => 0 := rfl
theorem stR_frame : callState fxW curveSurface.shellLayout keccak256 cdR = stR := rfl
theorem cdR_accepts : ShellModel.dispatcherAccepts (callState fxW fxShellLayout keccak256 cdR) :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, ⟨rfl, rfl⟩⟩, ⟨rfl, rfl, ⟨rfl, rfl⟩⟩⟩

/-- The state after the head guard's 'mload(64)'. -/
def stR1 : EvmState := touchMemory stR 64 32
/-- The state the emitted fail helper's 'mstore' leaves. -/
def stR2 : EvmState := { touchMemory stR1 0 32 with memory := storeWord stR1.memory 0 selWord }
/-- The halting state: revert with the four selector bytes. -/
def stRH : EvmState := { stR2 with halted := some (.revert, readBytes stR2.memory 0 4) }

theorem stRH_halted : stRH.halted = some (.revert, shellHaltData) := rfl

theorem bi_extcodesizeR : (OD0).Builtin Op.extcodesize [(4096 : U256)] stR1
    (.ok [BitVec.ofNat 256 (stR1.env.extCodeOf 4096).length] stR1) := rfl
theorem bi_extcodehashR : (OD0).Builtin Op.extcodehash [(4096 : U256)] stR1
    (.ok [projectedCodeHash stR1.env stR1.env.balanceOf 4096] stR1) := rfl
theorem bi_eq0R : (OD0).Builtin Op.eq
    [BitVec.ofNat 256 (stR1.env.extCodeOf 4096).length, 4577] stR1 (.ok [0] stR1) := rfl
theorem bi_eq1R : (OD0).Builtin Op.eq
    [projectedCodeHash stR1.env stR1.env.balanceOf 4096,
      15933609736973938366157763540951553264596488184743928812768469146773639656731] stR1
    (.ok [0] stR1) := rfl
theorem bi_and0R : (OD0).Builtin Op.and [0, 0] stR1 (.ok [0] stR1) := rfl
theorem bi_iszero1R : (OD0).Builtin Op.iszero [0] stR1 (.ok [1] stR1) := rfl

/-- The gate condition evaluates to true at the routed frame. -/
theorem gate_stepR : Step (OD0) funsGate V2 stR1 (.expr gateCond) (.eres (.vals [1] stR1)) := by
  have hb : Step (OD0) funsGate V2 stR1 (.expr gateB) (.eres (.vals [0] stR1)) :=
    ShellModel.bi2 (Step.lit (D := OD0))
      (ShellModel.bi1 (ShellModel.varS get_vk) bi_extcodesizeR) bi_eq0R
  have hc : Step (OD0) funsGate V2 stR1 (.expr gateC) (.eres (.vals [0] stR1)) :=
    ShellModel.bi2 (Step.lit (D := OD0))
      (ShellModel.bi1 (ShellModel.varS get_vk) bi_extcodehashR) bi_eq1R
  have ha : Step (OD0) funsGate V2 stR1
      (.expr (Expr.builtin Op.and [gateB, gateC])) (.eres (.vals [0] stR1)) :=
    ShellModel.bi2 hc hb bi_and0R
  exact ShellModel.bi1 ha bi_iszero1R

theorem shl_stepR : Step (OD0) funsCallee [("sel", (2756171582 : U256))] stR1
    (.expr (Expr.builtin Op.shl [Expr.lit (Literal.number 224), Expr.var "sel"]))
    (.eres (.vals [selWord] stR1)) :=
  ShellModel.bi2 (ShellModel.varS get_sel) (Step.lit (D := OD0))
    (rfl : (OD0).Builtin Op.shl [224, 2756171582] stR1 (.ok [selWord] stR1))

theorem mstore_stepR : Step (OD0) funsCallee [("sel", (2756171582 : U256))] stR1
    (.expr (Expr.builtin Op.mstore [Expr.lit (Literal.number 0),
      Expr.builtin Op.shl [Expr.lit (Literal.number 224), Expr.var "sel"]]))
    (.eres (.vals [] stR2)) :=
  Step.builtinOk (D := OD0)
    (Step.argsCons (D := OD0) (Step.argsCons (D := OD0) (Step.argsNil (D := OD0)) shl_stepR)
      (Step.lit (D := OD0)))
    (rfl : (OD0).Builtin Op.mstore [0, selWord] stR1 (.ok [] stR2))

theorem revert_stepR : Step (OD0) funsCallee [("sel", (2756171582 : U256))] stR2
    (.expr (Expr.builtin Op.revert [Expr.lit (Literal.number 0),
      Expr.lit (Literal.number 4)])) (.eres (.halt stRH)) :=
  Step.builtinHalt (D := OD0)
    (Step.argsCons (D := OD0) (Step.argsCons (D := OD0) (Step.argsNil (D := OD0))
      (Step.lit (D := OD0))) (Step.lit (D := OD0)))
    (rfl : (OD0).Builtin Op.revert [0, 4] stR2 (.halt stRH))

theorem fail_body_runR : Step (OD0) (armFuns :: []) [("sel", (2756171582 : U256))] stR1
    (Code.stmt (Stmt.block failBody)) (.sres [("sel", (2756171582 : U256))] stRH .halt) :=
  Step.block (D := OD0) (body := failBody) (funs := armFuns :: [])
    (V := [("sel", (2756171582 : U256))]) (st := stR1)
    (Step.seqCons (D := OD0) (Step.exprStmt (D := OD0) mstore_stepR)
      (Step.seqStop (D := OD0) (Step.exprStmtHalt (D := OD0) revert_stepR)
        ShellModel.halt_ne_normal))

theorem fail_call_stepR : Step (OD0) funsFail V2 stR1
    (.expr (Expr.call "fail" [Expr.lit (Literal.number 2756171582)])) (.eres (.halt stRH)) :=
  Step.callHalt (D := OD0)
    (Step.argsCons (D := OD0) (Step.argsNil (D := OD0)) (Step.lit (D := OD0)))
    lookup_fail (by decide : ([2756171582] : List U256).length = (["sel"] : List String).length)
    fail_body_runR

theorem gate_body_run_decompR : Step (OD0) funsGate V2 stR1 (Code.stmts (gateCondStmt :: gateTail))
    (.sres V2 stRH .halt) :=
  Step.seqStop (D := OD0)
    (Step.ifTrue (D := OD0) gate_stepR ShellModel.one_ne_zero
      (Step.block (D := OD0) (body := gateFailBody) (funs := funsGate) (V := V2) (st := stR1)
        (Step.seqStop (D := OD0)
          (Step.exprStmtHalt (D := OD0) fail_call_stepR) ShellModel.halt_ne_normal)))
    ShellModel.halt_ne_normal

theorem gate_body_runR : Step (OD0) funsGate V2 stR1 (Code.stmts gateBody) (.sres V2 stRH .halt) := by
  rw [gateBody_decomp]
  exact gate_body_run_decompR

theorem gate_stmt_runR : Step (OD0) (armFuns :: []) V2 stR1 (Code.stmt gate)
    (.sres (restore (D := OD0) V2 V2) stRH .halt) := by
  rw [gate_is]
  exact Step.block (D := OD0) (body := gateBody) (funs := armFuns :: []) (V := V2) (st := stR1)
    gate_body_runR

theorem guard_stmt_runR : Step (OD0) (armFuns :: []) [] stR
    (Code.stmt ((arm.drop 0).headD (Stmt.block []))) (.sres ([] : VEnv (OD0)) stR1 .normal) := by
  rw [arm_hg, Midfall.Instances.RunShellInversion.hgStmt_is]
  exact Step.ifFalse (D := OD0)
    (Midfall.Instances.RunShellInversion.hgTest_step (funs := armFuns :: []) (W := fxW) (H := keccak256) (cd := cdR))
    ShellModel.zero_eq_zero

theorem vk_stmt_runR : Step (OD0) (armFuns :: []) [] stR1
    (Code.stmt ((arm.drop 1).headD (Stmt.block []))) (.sres [("vk", (4096 : U256))] stR1 .normal) := by
  rw [arm_vk]
  exact Step.letVal (D := OD0) (Step.lit (D := OD0)) rfl

theorem su_stmt_runR : Step (OD0) (armFuns :: []) [("vk", (4096 : U256))] stR1
    (Code.stmt ((arm.drop 2).headD (Stmt.block []))) (.sres V2 stR1 .normal) := by
  rw [arm_su]
  exact Step.letVal (D := OD0) (Step.lit (D := OD0)) rfl

theorem arm_pieces_runR :
    Step (OD0) (armFuns :: []) [] stR
      (Code.stmts ([(arm.drop 0).headD (Stmt.block []), (arm.drop 1).headD (Stmt.block []),
        (arm.drop 2).headD (Stmt.block [])] ++ armDefs ++ ([gate] ++ gateRest)))
      (Res.sres V2 stRH .halt) :=
  Step.seqCons (D := OD0) guard_stmt_runR
    (Step.seqCons (D := OD0) vk_stmt_runR
      (Step.seqCons (D := OD0) su_stmt_runR
        (seq_after_defs armDefs armDefs_are_defs ([gate] ++ gateRest)
          (Step.seqStop (D := OD0) gate_stmt_runR ShellModel.halt_ne_normal))))

/-- **THE ARM RUNS ON THE ROUTED CALLDATA.** -/
theorem arm_derivationR :
    Step (OD0) [] [] stR (Code.stmt (Stmt.block arm))
      (Res.sres (restore (D := OD0) [] V2) stRH .halt) :=
  Step.block (D := OD0) (body := arm) (funs := []) (V := []) (st := stR)
    (by rw [arm_decomp]; exact arm_pieces_runR)

/-- **THE SHELL SIDE OF THE ROUTED COMPARISON: INHABITED, AND IT REVERTS WITH FOUR BYTES.** -/
theorem runShell_routed_inhabited :
    exists obs, RunShell curveSurface fxW keccak256 cdR c0 g0 obs :=
  ⟨⟨committedState stR stRH, .halt⟩, restore (D := OD0) [] V2, stRH, arm_derivationR, rfl⟩

theorem runShell_routed_reverts_four_bytes :
    exists obs, RunShell curveSurface fxW keccak256 cdR c0 g0 obs ∧
      obs.state.halted = some (.revert, shellHaltData) ∧ shellHaltData.length = 4 := by
  refine ⟨⟨committedState stR stRH, .halt⟩,
    ⟨restore (D := OD0) [] V2, stRH, arm_derivationR, rfl⟩,
    committedState_revert_halted stR stRH shellHaltData stRH_halted, shellHaltData_len⟩






theorem hdet : ∀ op, (OD0).Deterministic op :=
  Bridge.dialect_deterministic noCalls_functional gas_functional

/-- Two steps of one code from one configuration have one result. -/
theorem pin {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState} {code : Code EVM.Op}
    {r₁ r₂ : Res (OD0)} (h₁ : Step (OD0) funs V st code r₁)
    (h₂ : Step (OD0) funs V st code r₂) : r₁ = r₂ :=
  Step.det hdet h₁ h₂


/-- A variable read that steps to values has its name bound. -/
theorem var_bound {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st st' : EvmState} {x : Ident} {v : U256}
    (h : Step (OD0) funs V st (.expr (Expr.var x)) (.eres (.vals [v] st'))) :
    ∃ u, VEnv.get V x = some u := by
  cases h with | var hget => exact ⟨_, hget⟩

theorem no_vals_var {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st st' : EvmState} {x : Ident} {v : U256}
    (hV : VEnv.get V x = none)
    (h : Step (OD0) funs V st (.expr (Expr.var x)) (.eres (.vals [v] st'))) : False := by
  obtain ⟨_, hget⟩ := var_bound h; rw [hV] at hget; exact absurd hget (by simp)

theorem no_halt_var {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st st' : EvmState} {x : Ident}
    (h : Step (OD0) funs V st (.expr (Expr.var x)) (.eres (.halt st'))) : False := by cases h

/-- The two contract-level constants the OPEN arm reads and the entry path never binds. -/
abbrev vkLenName : Ident := "EXPECTED_VK_LENGTH"
abbrev vkHashName : Ident := "EXPECTED_VK_CODEHASH_WORD"

/-- 'eq(extcodesize(vk), EXPECTED_VK_LENGTH)' has no step, on either channel. -/
theorem gateB_no_step {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    (hV : VEnv.get V vkLenName = none) :
    ∀ {r : EResult (OD0)}, ¬ Step (OD0) funs V st (.expr RunShellInversion.gateB) (.eres r) := by
  intro r h
  rw [RunShellInversion.gateB_shape] at h
  cases h with
  | builtinOk hargs _ | builtinHalt hargs _ =>
      cases hargs with
      | argsCons hrest hhead => cases hrest with
          | argsCons hnil hvar => exact no_vals_var hV hvar
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt hrest _ => cases hrest with
          | argsCons hnil hvar => exact no_vals_var hV hvar
      | argsRestHalt hrest => cases hrest with
          | argsHeadHalt hnil hvar => cases hnil with | argsNil => exact no_halt_var hvar
          | argsRestHalt hnil => cases hnil

theorem gateC_no_step {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    (hV : VEnv.get V vkHashName = none) :
    ∀ {r : EResult (OD0)}, ¬ Step (OD0) funs V st (.expr RunShellInversion.gateC) (.eres r) := by
  intro r h
  rw [RunShellInversion.gateC_shape] at h
  cases h with
  | builtinOk hargs _ | builtinHalt hargs _ =>
      cases hargs with
      | argsCons hrest hhead => cases hrest with
          | argsCons hnil hvar => exact no_vals_var hV hvar
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt hrest _ => cases hrest with
          | argsCons hnil hvar => exact no_vals_var hV hvar
      | argsRestHalt hrest => cases hrest with
          | argsHeadHalt hnil hvar => cases hnil with | argsNil => exact no_halt_var hvar
          | argsRestHalt hnil => cases hnil

theorem gateA_no_step {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    (hV : VEnv.get V vkLenName = none ∧ VEnv.get V vkHashName = none) :
    ∀ {r : EResult (OD0)}, ¬ Step (OD0) funs V st (.expr RunShellInversion.gateA) (.eres r) := by
  intro r h
  rw [RunShellInversion.gateA_shape] at h
  cases h with
  | builtinOk hargs _ | builtinHalt hargs _ =>
      cases hargs with
      | argsCons hrest hhead => exact gateB_no_step hV.1 hhead
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt _ hhead => exact gateB_no_step hV.1 hhead
      | argsRestHalt hrest => cases hrest with
          | argsHeadHalt hnil hstepC => cases hnil with | argsNil => exact gateC_no_step hV.2 hstepC
          | argsRestHalt hnil => cases hnil

theorem gateCond_no_step {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    (hV : VEnv.get V vkLenName = none ∧ VEnv.get V vkHashName = none) :
    ∀ {r : EResult (OD0)},
      ¬ Step (OD0) funs V st (.expr RunShellInversion.gateCond) (.eres r) := by
  intro r h
  rw [RunShellInversion.gateCond_shape] at h
  cases h with
  | builtinOk hargs _ | builtinHalt hargs _ => cases hargs with
      | argsCons hnil hA => exact gateA_no_step hV hA
  | builtinArgsHalt hargs => cases hargs with
      | argsHeadHalt hnil hA => cases hnil with | argsNil => exact gateA_no_step hV hA
      | argsRestHalt hnil => cases hnil

theorem gateStmt_no_step {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    (hV : VEnv.get V vkLenName = none ∧ VEnv.get V vkHashName = none) :
    ∀ {V' : VEnv (OD0)} {st' : EvmState} {o : Outcome},
      ¬ Step (OD0) funs V st (.stmt RunShellInversion.gateCondStmt) (.sres V' st' o) := by
  intro V' st' o h
  rw [RunShellInversion.gateCond_is_cond] at h
  cases h with
  | ifTrue hexpr _ _ | ifFalse hexpr _ | ifHalt hexpr => exact gateCond_no_step hV hexpr

theorem gate_no_stmts {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
    (hV : VEnv.get V vkLenName = none ∧ VEnv.get V vkHashName = none) :
    ∀ {V' : VEnv (OD0)} {st' : EvmState} {o : Outcome},
      ¬ Step (OD0) funs V st (.stmts RunShellInversion.gateBody) (.sres V' st' o) := by
  intro V' st' o h
  rw [RunShellInversion.gateBody_decomp] at h
  cases h with
  | seqCons hgate _ | seqStop hgate _ => exact gateStmt_no_step hV hgate

/-! ### THE INVERSION: 'wrap curveSurface' has NO RUN on the routed calldata -/

/-- The program 'wrap curveSurface' runs: the dispatcher over the UN-INLINED arm. -/
def dispR : List (Stmt EVM.Op) := ShellModel.dispatcher armWithLocals
theorem dispR_is_wrap_program : dispR = ShellModel.dispatcherCode curveSurface := rfl
theorem stR_accepts : ShellModel.dispatcherAccepts stR := cdR_accepts

theorem dispR_decomp : dispR =
    [Stmt.exprStmt (Expr.builtin Op.mstore [ShellModel.w ShellModel.fmpAddr,
        Expr.builtin Op.memoryguard [ShellModel.w ShellModel.irMemoryguardReservation]]),
      Stmt.cond ShellModel.calldatasizeTest [ShellModel.selectorDecl,
        ShellModel.selectorSwitch armWithLocals],
      ShellModel.revert00] := rfl

/-- The function scope the dispatcher's three statements run in. -/
def FD : FunEnv (OD0) := hoist (OD0) dispR :: []
/-- The scope inside the size-guarded block. -/
def FI2 : FunEnv (OD0) :=
  hoist (OD0) [ShellModel.selectorDecl, ShellModel.selectorSwitch armWithLocals] :: FD
/-- The scope inside the routed 'verifyProof' arm block. -/
def FA2 : FunEnv (OD0) := hoist (OD0) (ShellModel.verifyProofArm armWithLocals) :: FI2

/-- The frame the arm executes in: the routed frame after the prologue. -/
def frameArm : EvmState := ShellModel.armFrame stR
/-- The environment the selector declaration leaves. -/
def envSel : VEnv (OD0) := ShellModel.selEnv (c := c0) (g := g0) stR
/-- The environment the whole entry path leaves. -/
def envArm : VEnv (OD0) := ShellModel.armEnv (c := c0) (g := g0) stR
/-- The environment after the arm's first shell local. -/
def envVk : VEnv (OD0) := [("vk", (4096 : U256))] ++ envArm
/-- The environment the arm's own two shell locals leave on top of the entry path's. -/
def armLocals : VEnv (OD0) := [("success", (1 : U256))] ++ envVk

theorem frameArm_prologue : frameArm = ShellModel.stAfterPrologue stR := rfl
theorem sizeTest_frameArm : ShellModel.sizeTestValue frameArm = 1 := rfl
theorem envSel_get : VEnv.get envSel "selector" = some ShellModel.selectorVerifyProof := rfl
theorem armLocals_free : VEnv.get armLocals vkLenName = none ∧
    VEnv.get armLocals vkHashName = none := ⟨rfl, rfl⟩

theorem hprolR {F : FunEnv (OD0)} :
    Step (OD0) F [] stR (.stmt (dispR.headD (Stmt.block [])))
      (.sres [] frameArm .normal) := by
  show Step (OD0) F [] stR (.stmt (Stmt.exprStmt (Expr.builtin Op.mstore
      [ShellModel.w ShellModel.fmpAddr,
        Expr.builtin Op.memoryguard [ShellModel.w ShellModel.irMemoryguardReservation]])))
      (.sres [] (ShellModel.stAfterPrologue stR) .normal)
  exact ShellModel.prologueStmtStep (c := c0) (g := g0) (funs := F) (V := []) (st₀ := stR)

theorem hsizeR {F : FunEnv (OD0)} :
    Step (OD0) F [] frameArm (.expr ShellModel.calldatasizeTest) (.eres (.vals [1] frameArm)) := by
  have e := ShellModel.calldatasizeTest_val (c := c0) (g := g0) (funs := F) (V := []) (st := frameArm)
  rw [sizeTest_frameArm] at e
  exact e

theorem hdeclR {F : FunEnv (OD0)} :
    Step (OD0) F [] frameArm (.stmt ShellModel.selectorDecl) (.sres envSel frameArm .normal) := by
  refine Step.letVal (D := OD0) (vars := ["selector"]) (vals := [ShellModel.selectorVerifyProof])
    (e := ShellModel.selectorExpr) (st1 := frameArm) ?_ rfl
  exact ShellModel.selectorStep (c := c0) (g := g0) (funs := F) (V := []) (st := frameArm)

theorem hscrR {F : FunEnv (OD0)} :
    Step (OD0) F envSel frameArm (.expr (Expr.var "selector"))
      (.eres (.vals [ShellModel.selectorVerifyProof] frameArm)) :=
  Step.var (D := OD0) (funs := F) (V := envSel) (st := frameArm) (x := "selector")
    (v := ShellModel.selectorVerifyProof) envSel_get

theorem hprefixR {F : FunEnv (OD0)} :
    Step (OD0) F envSel frameArm (.stmts ShellModel.armPrefix)
      (.sres envArm frameArm .normal) :=
  ShellModel.armPrefix_normal (hacc := stR_accepts) (c := c0) (g := g0) (F := F)

theorem hhg_armFrame {F : FunEnv (OD0)} {V : VEnv (OD0)} :
    Step (OD0) F V frameArm (.expr RunShellInversion.hgTest) (.eres (.vals [0] frameArm)) := by
  have hrest : Step (OD0) F V frameArm (.args [Expr.lit (Literal.number 0x1000)])
      (.eres (.vals [0x1000] frameArm)) :=
    Step.argsCons (D := OD0) (Step.argsNil (D := OD0)) (Step.lit (D := OD0))
  have hml : Step (OD0) F V frameArm
      (.expr (Expr.builtin Op.mload [Expr.lit (Literal.number 64)]))
      (.eres (.vals [128] (touchMemory frameArm 64 32))) :=
    Step.builtinOk (D := OD0)
      (Step.argsCons (D := OD0) (Step.argsNil (D := OD0)) (Step.lit (D := OD0)))
      (by have h0 : (OD0).Builtin Op.mload [(64 : U256)] frameArm
              (.ok [loadWord frameArm.memory 64] (touchMemory frameArm 64 32)) :=
              RunShellInversion.bi_mload_ok (c := c0) (g := g0)
          rw [show loadWord frameArm.memory 64 = (128 : U256) from rfl] at h0
          exact h0)
  have htouch : touchMemory frameArm 64 32 = frameArm := rfl
  rw [htouch] at hml
  exact Step.builtinOk (D := OD0) (Step.argsCons (D := OD0) hrest hml)
    (RunShellInversion.bi_gt_ok (c := c0) (g := g0))

theorem hhg_stmtR {F : FunEnv (OD0)} {V : VEnv (OD0)} :
    Step (OD0) F V frameArm (.stmt RunShellInversion.hgStmt) (.sres V frameArm .normal) := by
  rw [RunShellInversion.hgStmt_is]
  exact Step.ifFalse (D := OD0) (hhg_armFrame (F := F) (V := V)) ShellModel.zero_eq_zero

theorem armBody_curve_eq : ShellModel.armBody curveSurface = armWithLocals :=
  Midfall.Instances.FrameWalkWitness.armWithLocals_is_the_arm_body

theorem armWithLocals_decomp : armWithLocals =
    RunShellInversion.hgStmt :: Midfall.Lowering.Inline.shellLocalLets ++
      RunShellInversion.mainBlk := rfl

theorem shellLocalLets_decomp : Midfall.Lowering.Inline.shellLocalLets =
    [Stmt.letDecl ["vk"] (some (Expr.lit (Literal.number 4096))),
      Stmt.letDecl ["success"] (some (Expr.lit (Literal.number 1)))] := rfl

/-- The first shell local's step, pinned. -/
theorem hlet1R {F : FunEnv (OD0)} {V : VEnv (OD0)} (st : EvmState) :
    Step (OD0) F V st (.stmt (Stmt.letDecl ["vk"] (some (Expr.lit (Literal.number 4096)))))
      (.sres ([("vk", (4096 : U256))] ++ V) st .normal) :=
  Step.letVal (D := OD0) (Step.lit (D := OD0)) rfl

/-- The second shell local's step, pinned. -/
theorem hlet2R {F : FunEnv (OD0)} {V : VEnv (OD0)} (st : EvmState) :
    Step (OD0) F V st (.stmt (Stmt.letDecl ["success"] (some (Expr.lit (Literal.number 1)))))
      (.sres ([("success", (1 : U256))] ++ V) st .normal) :=
  Step.letVal (D := OD0) (Step.lit (D := OD0)) rfl

/-- **SEQUENCE APPEND INVERSION, PINNED.** If a list of statements runs to '.normal' from a
    configuration, and that list followed by a tail also runs from the same configuration, then the
    tail runs from where the list left off. Every intermediate step is PINNED against the forward
    derivation, so no branch of the sequence inversion is skipped - and a sixteen-statement entry path
    comes off the front of a run in one line. -/
theorem stmts_append_inv (pre : List (Stmt EVM.Op)) :
    ∀ {funs : FunEnv (OD0)} {V : VEnv (OD0)} {st : EvmState}
      {V₁ : VEnv (OD0)} {st₁ : EvmState} {o₁ : Outcome},
      Step (OD0) funs V st (.stmts pre) (.sres V₁ st₁ o₁) →
      ∀ {P : List (Stmt EVM.Op)} {V' : VEnv (OD0)} {st' : EvmState} {o : Outcome},
        Step (OD0) funs V st (.stmts (pre ++ P)) (.sres V' st' o) →
        o₁ = .normal →
        ∃ Vb, Step (OD0) funs V₁ st₁ (.stmts P) (.sres Vb st' o) := by
  induction pre with
  | nil =>
      intro funs V st V₁ st₁ o₁ h₁ P V' st' o h₂ _
      cases h₁
      exact ⟨V', h₂⟩
  | cons x xs ih =>
      intro funs V st V₁ st₁ o₁ h₁ P V' st' o h₂ hnormal
      cases h₁ with
      | seqStop hx ho => exact absurd hnormal ho
      | seqCons hx hxs =>
          cases h₂ with
          | seqCons hx' hrest =>
              have hpin := pin hx hx'
              cases hpin
              exact ih hxs hrest hnormal
          | seqStop hx' ho =>
              have hpin := pin hx hx'
              cases hpin
              exact (ho rfl).elim

/-- **THE DESCENT PAST THE ROUTED SWITCH.** A step of the selector switch on the routed calldata
    forces a step of the arm body, from the environment and frame the entry path leaves: the switch
    routes to 'verifyProof', the thirteen-statement prefix plus the callvalue guard and the two
    immutable bindings leave 'envArm' in 'frameArm', and what is left is the arm's own first
    statement. Every guard is PINNED against its forward derivation, so no branch is skipped. -/
theorem of_switch {V₂ : VEnv (OD0)} {st₂ : EvmState} {o₂ : Outcome}
    (hsw1 : Step (OD0) FI2 envSel frameArm
      (.stmt (ShellModel.selectorSwitch armWithLocals)) (.sres V₂ st₂ o₂)) :
    ∃ (Vb : VEnv (OD0)) (st₅ : EvmState) (o₅ : Outcome),
      Step (OD0) FA2 envArm frameArm (.stmts armWithLocals) (.sres Vb st₅ o₅) := by
  cases hsw1 with
  | switchHalt hscr => have := pin hscr (hscrR (F := FI2)); cases this
  | switchExec hscr hblk =>
      have hpin4 := pin hscr (hscrR (F := FI2))
      cases hpin4
      rw [ShellModel.switch_verifyProof (c := c0) (g := g0)
        (cv := ShellModel.selectorVerifyProof) (body := armWithLocals) rfl] at hblk
      rw [ShellModel.verifyProofArm_eq_armPrefix armWithLocals] at hblk
      cases hblk with
      | block hseq =>
          obtain ⟨Vb, hb⟩ := stmts_append_inv ShellModel.armPrefix
              (hprefixR (F := FA2)) hseq rfl
          exact ⟨Vb, _, _, hb⟩

/-- The descent past the size-guarded selector switch. -/
theorem of_cond {V₂ : VEnv (OD0)} {st₂ : EvmState} {o₂ : Outcome}
    (hcond : Step (OD0) FD [] frameArm
      (.stmt (Stmt.cond ShellModel.calldatasizeTest
        [ShellModel.selectorDecl, ShellModel.selectorSwitch armWithLocals])) (.sres V₂ st₂ o₂)) :
    ∃ (Vb : VEnv (OD0)) (st₅ : EvmState) (o₅ : Outcome),
      Step (OD0) FA2 envArm frameArm (.stmts armWithLocals) (.sres Vb st₅ o₅) := by
  cases hcond with
  | ifHalt htest => have := pin htest (hsizeR (F := FD)); cases this
  | ifFalse htest hz =>
      have := pin htest (hsizeR (F := FD))
      cases this
      exact absurd hz ShellModel.one_ne_zero
  | ifTrue htest hnz hbody =>
      have hpin2 := pin htest (hsizeR (F := FD))
      cases hpin2
      cases hbody with
      | block hbs =>
          cases hbs with
          | seqStop hdecl ho =>
              have := pin hdecl (hdeclR (F := FI2)); cases this; exact (ho rfl).elim
          | seqCons hdecl hsw =>
              have hpin3 := pin hdecl (hdeclR (F := FI2))
              cases hpin3
              cases hsw with
              | seqStop hsw1 _ => exact of_switch hsw1
              | seqCons hsw1 _ => exact of_switch hsw1
/-- A run of the dispatcher on the routed calldata forces a run of the arm body. -/
theorem arm_body_step_of_disp_run {V' : VEnv (OD0)} {st' : EvmState} {o : Outcome}
    (h : Step (OD0) FD [] stR (.stmts dispR) (.sres V' st' o)) :
    ∃ (Vb : VEnv (OD0)) (st₂ : EvmState) (o₂ : Outcome),
      Step (OD0) FA2 envArm frameArm (.stmts armWithLocals) (.sres Vb st₂ o₂) := by
  rw [dispR_decomp] at h
  cases h with
  | seqStop hp ho => have := pin hp (hprolR (F := FD)); cases this; exact (ho rfl).elim
  | seqCons hp hrest =>
      have hpin := pin hp (hprolR (F := FD))
      cases hpin
      cases hrest with
      | seqCons hcond _ => exact of_cond hcond
      | seqStop hcond _ => exact of_cond hcond

/-- **NO RUN OF 'wrap curveSurface' ON THE ROUTED CALLDATA.** The dispatcher ENTERS the arm - the size
    test passes, the selector routes, the callvalue guard passes, all thirteen ABI bounds tests pass
    and the two immutable bindings bind - and then the arm's own VK gate reads 'EXPECTED_VK_LENGTH'
    and 'EXPECTED_VK_CODEHASH_WORD', which NOTHING in the entry path binds. The run is stuck: not a
    revert with a different payload, no observation at all. -/
theorem no_wrap_run_routed {V' : VEnv (OD0)} {st' : EvmState} {o : Outcome}
    (h : Step (OD0) [] [] stR (Code.stmt (Stmt.block dispR)) (.sres V' st' o)) : False := by
  cases h with
  | block hstmts =>
      obtain ⟨Vb, st₂, o₂, harm⟩ := arm_body_step_of_disp_run hstmts
      rw [armWithLocals_decomp] at harm
      cases harm with
      | seqStop hhg ho =>
          have := pin hhg (hhg_stmtR (F := FA2) (V := envArm)); cases this; exact (ho rfl).elim
      | seqCons hhg hrest' =>
          have hpin := pin hhg (hhg_stmtR (F := FA2) (V := envArm))
          cases hpin
          rw [shellLocalLets_decomp] at hrest'
          cases hrest' with
          | seqStop h1 ho =>
              have := pin h1 (hlet1R (F := FA2) (V := envArm) frameArm)
              cases this; exact (ho rfl).elim
          | seqCons h1 hrest'' =>
              have hpin1 := pin h1 (hlet1R (F := FA2) (V := envArm) frameArm)
              cases hpin1
              cases hrest'' with
              | seqStop h2 ho =>
                  have := pin h2 (hlet2R (F := FA2) (V := envVk) frameArm)
                  cases this; exact (ho rfl).elim
              | seqCons h2 hmain =>
                  have hpin2 := pin h2 (hlet2R (F := FA2) (V := envVk) frameArm)
                  cases hpin2
                  rw [RunShellInversion.main_decomp] at hmain
                  have hpeel := RunShellInversion.peel_defs RunShellInversion.mainDefs
                    RunShellInversion.mainDefs_are_defs
                    (RunShellInversion.gateStmt :: RunShellInversion.mainRest) hmain
                  cases hpeel with
                  | seqCons hgs _ | seqStop hgs _ =>
                      cases hgs with
                      | block hgb => exact gate_no_stmts armLocals_free hgb

/-- **THE WRAP SIDE IS EMPTY ON THE ROUTED CALLDATA.** -/
theorem wrap_routed_uninhabited :
    ¬ exists obs, ShellModel.wrap curveSurface fxW keccak256 cdR c0 g0 obs := by
  rintro ⟨obs, V', st', hrun, _⟩
  exact no_wrap_run_routed hrun

/-! ### THE ROUTED REFUTATION OF 'ir_refines', AND THE TWO MECHANISMS -/

/-- **THE ROUTED REFUTATION.** 'ir_refines' read at 'curveSurface' and instantiated at the in-tree
    model object, the Surface's own shell layout, the fixture world and hash, the ROUTED calldata,
    the empty call relation and the constant-zero gas oracle: every hypothesis holds and the
    conclusion is FALSE. Unlike the empty-calldata refutation, this one is not a difference in halt
    payload - the model side has NO observation at all. -/
theorem ir_refines_refuted_at_curveSurface_routed :
    ¬ ObsEquiv
        (RunContractIR curveSurface fxW keccak256 (ShellModel.modelIr curveSurface)
          curveSurface.shellLayout cdR c0 g0)
        (RunShell curveSurface fxW keccak256 cdR c0 g0) := by
  intro h
  obtain ⟨obsSh, hsh, -, -⟩ := runShell_routed_reverts_four_bytes
  obtain ⟨oIr, hIr, hv⟩ := (h obsSh.view).2 ⟨obsSh, hsh, rfl⟩
  obtain ⟨V', st', hrun, hobs⟩ :=
    (ShellModel.wrap_iff_modelRunContractIR curveSurface fxW keccak256 cdR c0 g0 oIr).mp hIr
  exact wrap_routed_uninhabited ⟨oIr, V', st', hrun, hobs⟩

/-- **D-P23, SATISFIABILITY HALF AT THE ROUTED INSTANTIATION.** The calldata really routes, the
    dispatcher really accepts it, the model really passes the import check, and the shell really has
    a run. -/
theorem routed_hypotheses_hold :
    Midfall.bytesTake cdR 0 4 = some Midfall.Generator.fnSigVerifyProof ∧
      ShellModel.dispatcherAccepts stR ∧
      curveSurface.irCheck (ShellModel.modelIr curveSurface) = true ∧
      (ExternalCalls.none : YulSemantics.EVM.ExternalCalls).WorldLocal ∧
      (exists o, RunShell curveSurface fxW keccak256 cdR c0 g0 o) :=
  ⟨cdR_hsel, cdR_accepts, ShellModel.modelIr_irCheck curveSurface, noCalls_worldLocal,
    runShell_routed_inhabited⟩

/-- **THE TWO MECHANISMS ARE DISTINCT, AND THIS IS THE THEOREM THAT SAYS SO.** At the UNROUTABLE
    calldata both sides have a run and their halt payloads differ (zero bytes against four): that is
    D-P42's mechanism M1. At the ROUTED calldata the shell still has its four-byte run but the model
    side has NO run at all: that is M2, and it is a different failure of the same field. So the
    disagreement is not an artefact of the empty input - but neither is it the entry-path guard on the
    routed input, where the entry path is exactly what does NOT fire. -/
theorem the_two_mechanisms_are_distinct :
    (exists obs, ShellModel.wrap curveSurface fxW keccak256 (ByteArray.empty : Bytes) c0 g0 obs) ∧
      (exists obs, RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) c0 g0 obs) ∧
      (exists obs, RunShell curveSurface fxW keccak256 cdR c0 g0 obs) ∧
      (¬ exists obs, ShellModel.wrap curveSurface fxW keccak256 cdR c0 g0 obs) :=
  ⟨by obtain ⟨o, h, -⟩ := wrap_empty_cd_reverts_nil; exact ⟨o, h⟩,
    by obtain ⟨o, h, -⟩ := shell_run_reverts_four_bytes; exact ⟨o, h⟩,
    runShell_routed_inhabited, wrap_routed_uninhabited⟩

/-- Consequence: the routed input alone refutes 'LoweringCorrect curveSurface', without any appeal to
    the empty calldata. -/
theorem curveSurface_not_LoweringCorrect_routed (product : Midfall.Yul.PairingProduct) :
    ¬ LoweringCorrect curveSurface product := by
  intro hc
  exact ir_refines_refuted_at_curveSurface_routed
    (hc.ir_refines (ShellModel.modelIr curveSurface) curveSurface.shellLayout
      (ShellModel.modelIr_irCheck curveSurface) fxW keccak256 cdR ExternalCalls.none 0
      noCalls_worldLocal)

/-- The frame-boundary commit map never loses the halt record: a committing kind keeps the whole
    post-state, a non-committing one rolls the effects back to 'st0' but carries 'halted' over, and
    running off the end keeps it as 'none'. -/
theorem committedState_preserves_halted (st0 st' : EvmState) :
    (committedState st0 st').halted = st'.halted := by
  cases hst : st'.halted with
  | none => simp [committedState, hst]
  | some kd =>
      cases kd with
      | mk k d =>
          simp only [committedState, hst]
          by_cases hc : k.commits <;> simp [hc, hst]

/-! ### 5. THE CONTROL: what the entry path does and does not contribute -/

/-- **THE CONTROL, AS A TRANSPORT.** Suppose the ROUTED switch block over the CLOSED (inlined) arm
    runs to a halt leaving the selector environment. Then the dispatcher over that same closed arm
    has a run at the routed frame, and its halt is the arm's own: the prologue, the size test, the
    selector binding, the switch, the callvalue guard, the thirteen ABI bounds tests and the two
    immutable bindings contribute NO halt, no world effect and no call. This is the theorem form of
    the claim that the entry path is not what makes 'RunShell' and 'wrap' disagree on routed input -
    the disagreement is the OPEN arm, not the dispatcher in front of it.

    The hypothesis is not exhibited here: discharging it means re-deriving the arm at the dispatcher's
    function scopes and at the post-prologue frame, which is the same work as section 2 with three
    call-site scopes changed. The gate 'control_dispatcher_over_closed_arm_ok' below measures it
    instead, through the vendored fuel interpreter at the closed dialect - an independent engine that
    never calls any lemma in this file. -/
theorem control_of_arm_block_run {st' : EvmState}
    (harm : Step (OD0)
        (hoist (OD0) [ShellModel.selectorDecl, ShellModel.selectorSwitch armInlined] :: [[]])
        (ShellModel.selEnv (c := c0) (g := g0) stR) (ShellModel.armFrame stR)
        (.stmt (.block (selectSwitch (OD0) (ShellModel.selectorWord stR)
          (ShellModel.caseList armInlined) none)))
        (.sres (ShellModel.selEnv (c := c0) (g := g0) stR) st' .halt)) :
    ∃ obs, ShellModel.runOn armInlined stR c0 g0 obs ∧ obs.state.halted = st'.halted := by
  have hstmts : Step (OD0) [[]] [] stR (.stmts (ShellModel.dispatcher armInlined))
      (.sres [] st' .halt) :=
    ShellModel.dispatch_prefix (body := armInlined) (st₀ := stR) (c := c0) (g := g0)
      (by rfl : ShellModel.sizeTestValue stR = 1) harm
  have hblock : Step (OD0) [] [] stR (Code.stmt (Stmt.block (ShellModel.dispatcher armInlined)))
      (.sres ([] : VEnv (OD0)) st' .halt) := by
    have key : Step (OD0) [] [] stR (Code.stmt (Stmt.block (ShellModel.dispatcher armInlined)))
        (.sres (restore (D := OD0) ([] : VEnv (OD0)) ([] : VEnv (OD0))) st' .halt) :=
      Step.block (D := OD0) (body := ShellModel.dispatcher armInlined) (funs := []) (V := [])
        (st := stR) hstmts
    rw [ShellModel.restore_nil (c := c0) (g := g0) (V := ([] : VEnv (OD0)))] at key
    exact key
  refine ⟨⟨committedState stR st', .halt⟩, ?_, committedState_preserves_halted stR st'⟩
  · exact ⟨[], st', hblock, rfl⟩

/-! ### 6. GATES: the routed comparison, measured by an independent engine

Every gate below runs the vendored fuel interpreter 'YulSemantics.Interp.run' at the closed
'EVM.exec' dialect - a different engine from the 'Step' relation every theorem above is proved in,
and none of them calls any lemma of this file. Fuel is charged per NESTING LEVEL, which is what makes
each of these lines cost seconds rather than the eighteen minutes a per-element walk measured (R-71,
P-INLINE). -/

/-- The routed frame's halt payload, as a length: 4 for the arm, 0 for the dispatcher over the open
    arm at the EMPTY calldata. -/
def haltLen (r : YulSemantics.Result (VEnv (EVM.exec).toDialect × EvmState × Outcome)) : Int :=
  match r with
  | .ok (_, st, _) => match st.halted with
      | some (_, d) => (d.length : Int)
      | none => -1
  | .stuck => -2
  | .outOfFuel => -3

def routedHaltLens : List Int :=
  [YulSemantics.Interp.run EVM.exec 200000 armInlined stR,
    YulSemantics.Interp.run EVM.exec 200000 (ShellModel.dispatcher armWithLocals) stR,
    YulSemantics.Interp.run EVM.exec 200000 (ShellModel.dispatcher armInlined) stR,
    YulSemantics.Interp.run EVM.exec 200000 armWithLocals stR].map haltLen

/-- **THE ROUTED COMPARISON, MEASURED.** Left to right: the bare closed arm reverts with FOUR bytes;
    the dispatcher over the OPEN arm (what 'wrap' runs) is STUCK; the dispatcher over the CLOSED arm
    (the control) reverts with the SAME FOUR bytes; the bare open arm is STUCK. So the entry path is
    not what separates the two sides on routed input - the open arm is. -/
def routed_comparison_ok : Bool :=
  routedHaltLens == [4, -2, 4, -2]

#eval routed_comparison_ok -- expect true

/-- The same four programs at the UNROUTABLE (empty) calldata: the arm reverts with four bytes, the
    dispatcher with zero, and nothing is stuck. This is D-P42's mechanism M1, and the contrast with
    the gate above is the two-mechanisms finding, measured. -/
def unroutable_comparison_ok : Bool :=
  [YulSemantics.Interp.run EVM.exec 200000 armInlined stF,
    YulSemantics.Interp.run EVM.exec 200000 (ShellModel.dispatcher armWithLocals) stF,
    YulSemantics.Interp.run EVM.exec 200000 (ShellModel.dispatcher armInlined) stF].map haltLen
      == [4, 0, 0]

#eval unroutable_comparison_ok -- expect true

/-- **THE ROUTED CALLDATA IS THE ONE THE FIELD ITSELF ASKS FOR.** 'bytesTake cd 0 4 = some
    fnSigVerifyProof' is 'LoweringCorrect.only_two_outcomes'’s hypothesis on the calldata, and the
    dispatcher's own acceptance is the model-side analogue. Both hold of 'cdR', and the gate refutes
    them for the empty calldata and for the wrong-selector witness, so the exhibit discriminates. -/
def routed_calldata_is_the_routed_one_ok : Bool :=
  (Midfall.bytesTake cdR 0 4 == some Midfall.Generator.fnSigVerifyProof) &&
    (ShellModel.sizeTestValue stR == 1) &&
    (ShellModel.selectorWord stR == ShellModel.selectorVerifyProof) &&
    (ShellModel.armFrame stR).memory 95 == 128 &&
    (Midfall.bytesTake (ByteArray.mk #[] : Bytes) 0 4 == none) &&
    (ShellModel.selectorWord (ShellModel.frame ShellModel.cdWrongSelector 0) !=
      ShellModel.selectorVerifyProof) &&
    (ShellModel.tailValue (ShellModel.headStart + 64) 100
      (ShellModel.frame ShellModel.cdTruncatedProof 0) != 0) &&
    (ShellModel.sizeTestValue (ShellModel.frame ([] : List UInt8) 0) == 0)

#eval routed_calldata_is_the_routed_one_ok -- expect true

/-- **THE IMPORTED ARTIFACT AT BOTH INPUTS**, measured: zero bytes on the unroutable calldata and
    zero bytes on the routed one, against the shell's four in both cases. The artifact's routed path
    reaches its own VK-mismatch abort, which is a 'revert_error_*()' - 'revert(0, 0)' - while the
    emitted shell's abort is the 'fail(sel)' helper, which stores the selector and reverts with four
    bytes. No theorem in this file depends on this gate: the artifact's routed run is a MEASUREMENT,
    not a derivation, and it is labelled as such in the package report. -/
def artifact_both_inputs_ok : Bool :=
  [YulSemantics.Interp.run EVM.exec 200000 Midfall.Yul.Ir.verifierRuntime irSt0,
    YulSemantics.Interp.run EVM.exec 200000 Midfall.Yul.Ir.verifierRuntime
      (callState irW irLyt keccak256 cdR)].map haltLen == [0, 0]

#eval artifact_both_inputs_ok -- expect true

#print axioms Midfall.Instances.RunLegRouted.control_of_arm_block_run

#print axioms Midfall.Instances.RunLegRouted.wrap_routed_uninhabited
#print axioms Midfall.Instances.RunLegRouted.ir_refines_refuted_at_curveSurface_routed
#print axioms Midfall.Instances.RunLegRouted.runShell_routed_reverts_four_bytes
#print axioms Midfall.Instances.RunLegRouted.the_two_mechanisms_are_distinct

end Midfall.Instances.RunLegRouted


import Midfall.Instances.FrameWalkWitness
import Midfall.Yul.ShellModel
import Midfall.Lowering.RunEmitted
import YulSemantics.Interp

/-!
Midfall/Instances/RunShellInversion

P-RUNSHELL (docs/plans/P-RUNSHELL.md) STEP 1 AND 2. **THE INVERSION GOES THE REFUTATION WAY, AND IT
IS THE FOURTH REFUTED HEADLINE HYPOTHESIS IN THIS PROJECT.**

THE CLAIM, AND IT IS A THEOREM. \`RunShell curveSurface W H cd c g\` is EMPTY - for every world, every
hash, every calldata, every call relation and every gas oracle. \`no_arm_run\` proves that the arm has
no \`Step\` derivation at all from the shell's entry frame; \`runShell_curveSurface_empty\` lifts it to
the run predicate, and \`wrap_empty_cd_inhabited\` exhibits the observation the dispatcher side DOES
have on the empty calldata (\`ShellModel.unroutable_calldata_reverts\`). Therefore
\`ObsEquiv (ShellModel.wrap curveSurface ...) (RunShell curveSurface ...)\` is FALSE
(\`obsEquiv_wrap_runShell_fails\`), and since \`ShellModel.modelIr S\` passes \`S.irCheck\` by \`rfl\` and
\`RunContractIR S W H (modelIr S) S.shellLayout\` IS \`wrap S W H\`
(\`ShellModel.wrap_iff_modelRunContractIR\`), the field \`LoweringCorrect.ir_refines\` is REFUTED at the
curve Surface, not merely unprovable (\`ir_refines_refuted_at_curveSurface\`). Consequence, and it is
the required finding: \`LoweringCorrect curveSurface product\` has no instance for ANY product
(\`curveSurface_not_LoweringCorrect\`), so the headline \`lowering_equivalence\` is vacuous at the curve
Surface and the eight-leg exhibit \`CurveSurface.loweqBundleCore\` cannot be repaired into a witness of
the bundle. The same holds at the fixture Surface (\`runShell_realSurface_empty\`).

THE MECHANISM, IN ONE SENTENCE. \`YulSemantics.Run\` starts the variable environment at \`[]\`
(BigStep.lean:366-368) and \`Step.var\` needs \`VEnv.get V x = some v\`; the arm's first executed
statement is \`if iszero(and(eq(extcodesize(vk), EXPECTED_VK_LENGTH), eq(extcodehash(vk),
EXPECTED_VK_CODEHASH_WORD))) { fail(ERR_VK_MISMATCH) }\` and all three of \`vk\`,
\`EXPECTED_VK_LENGTH\`, \`EXPECTED_VK_CODEHASH_WORD\` are free in the arm (\`curveSurface.bindLocals = []\`
and \`shell_unfolds\` pins the code block to \`headGuard ++ bindLocals ++ main\`).

WHAT THE PROOF ACTUALLY HAS TO DO, and what it does NOT. The head guard is NOT the obstruction:
\`gt(mload(0x40), 0x1000)\` evaluates to 0 in a zero-memory frame, so the guard passes and binds
nothing (\`guard_forced\`, plus \`guard_is_not_the_obstruction\`, which exhibits a run of
\`[head guard; revert(0,0)]\` from the same frame). The eight emitted \`AssemblyHelpers\` definitions
before the gate are \`Step.funDef\` no-ops (\`peel_defs\`). The gate itself has NO step for ANY outcome:
neither values (\`step_vals_noVar\`) nor a halt (\`gate_no_expr\`, which has to walk the halt channel
because \`Step.argsHeadHalt\` lets an argument list halt while skipping its head). FALSIFICATION 2
(\`bound_read_has_a_run\`) exhibits a derivation of the very read that kills the arm once \`vk\` is
bound, so the emptiness is about the binding and not about \`extcodesize\`, the frame, or every program.

TRUST. Everything here is kernel-checked: \`decide\` and \`rfl\`, no \`native_decide\`, no \`OfReduceBool\`.
The syntactic predicate \`exprHasVar\` is deliberately a MUTUAL STRUCTURAL recursion rather than a
re-use of \`FrameWalk.freeNames\`, because \`freeNames\` goes through \`WellFounded.fix\` and the kernel
will not reduce it - that is why \`FrameWalkWitness\`'s free-name counts are \`native_decide\` and
compiler-trusted. The counts this file needs are checked by \`decide\` instead. The only axioms the
refutation rests on are \`propext\`, \`Classical.choice\`, \`Quot.sound\` and the five D-P36a curve-pairing
assumptions that \`curveSurface\` itself is built on; no \`sorryAx\`.

STEP 2, FIXTURE OR SPEC? BOTH, AND THE SPEC HALF IS THE ONE THAT MATTERS. \`Surface.bindLocals\` is
documented as "the constant-substituted locals block", so an empty one at a Surface whose program has
61 free identifiers is a fixture bug - \`RunEmitted.shellLets\` (the artifact's own parsed constant
table) bound at the arm level does make the arm run on the empty calldata (\`armRunsUnderArmLevel
Binding_ok\`: a four-byte revert instead of a stuck state). But it is NOT the honest fix, because a
Yul function is not a closure: \`Step.callOk\` initialises the callee environment with the parameters
and the zeroed return slots and nothing else (BigStep.lean:189), SIX of the eight emitted helpers
read names that neither their signature nor their own binders provide (\`helperOwnFree_count_ok\`), and
\`transcript_init_name_unbound_in_callee\` pins the mechanism for one of them by \`rfl\`. So NO legal
value of \`bindLocals\` closes the program: \`helperStuckUnderArmLevelBinding_ok\` shows the helper call
still stuck under the maximal arm-level binding, and \`armBoundAllZeroStillStuck_ok\` shows the stuck
state is not an artefact of the constant VALUES. The spec has no place for contract-level constants
that reaches into function bodies. That is a spec question and it is reported, not patched: the
Surface was NOT edited, \`RunShell\` was NOT edited, and \`ir_refines\` was NOT weakened.

STEP 3, THE ENTRY PATH: THE SAME BINDING PROBLEM PLUS A DIFFERENCE THAT CANNOT BE SEEN. Half of the
entry-path gap IS this gap: \`ShellModel.bindLocalsFromImmutables\` is exactly the block that binds
\`vk\` (\`entry_path_binds_vk\`), so "the dispatcher binds what the arm leaves free" and "the arm has
free identifiers" are one fact from two sides. The guard half is a genuinely different mechanism -
R-66 and \`ShellModel.old_shell_runs_the_verifier_on_the_same_frame\` prove the two entry paths differ
in halt kind on a wrong-selector calldata - but it is a SECOND, ALREADY-LANDED refutation and it is
MASKED here: \`RunShell curveSurface\` is empty for every calldata
(\`runShell_empty_for_every_cd\`), so there is no shell run for a guard to disagree with. It is not
independent evidence for anything new.

D-P23, BOTH HALVES. Satisfiability: \`wrap_empty_cd_inhabited\` (the inhabited side, at a concrete
calldata and a world-local call relation), \`guard_is_not_the_obstruction\` and
\`bound_read_has_a_run\` (runs that exist exactly where the inversion says they must). Falsification:
\`step_vals_noVar\` discriminates (it is a theorem about derivations, and \`gate_no_expr\` fails on the
halt channel for a program whose head argument can halt before the free read is reached), and the
vendored interpreter is run on the arm as an INDEPENDENT check (\`armInterpStuck_ok\`: STUCK). THE
LIMIT, STATED NOT HIDDEN: no gate in this repository deletes a falsification theorem and reddens the
build; that gap has been measured twenty-nine times and this package does not close it.
-/

set_option linter.unusedSimpArgs false

namespace Midfall.Instances.RunShellInversion

open Midfall Midfall.Lowering
open Midfall.Instances.SurfaceFixture Midfall.Instances.CurveSurface
open YulSemantics YulSemantics.EVM
open Midfall.Yul

abbrev FOp := YulSemantics.EVM.Op
variable {c : ExternalCalls} {g : ExternalGas}

/-- The open dialect \`RunShell\` runs in, named. -/
abbrev OD' (calls : ExternalCalls) (gas : ExternalGas) : YulSemantics.Dialect :=
  ShellModel.OD calls gas

/-! ### 1. The spine of the arm \`RunShell\` runs -/

def mainBlk : List (Stmt FOp) := Midfall.Instances.FrameWalkWitness.mainBlk
def armBlk : List (Stmt FOp) := Midfall.Instances.FrameWalkWitness.armBlk

def hgStmt : Stmt FOp := fxHeadGuard.headD (Stmt.block [])
def hgTest : Expr FOp :=
  Expr.builtin Op.gt [Expr.builtin Op.mload [Expr.lit (Literal.number 64)],
    Expr.lit (Literal.number 0x1000)]
def hgBody : List (Stmt FOp) := match hgStmt with | Stmt.cond _ b => b | _ => []
theorem hgStmt_is : hgStmt = Stmt.cond hgTest hgBody := rfl
theorem arm_cons : armBlk = hgStmt :: mainBlk := rfl

def mainDefs : List (Stmt FOp) := mainBlk.take 8
def gateStmt : Stmt FOp := (mainBlk.drop 8).headD (Stmt.block [])
def mainRest : List (Stmt FOp) := (mainBlk.drop 8).tail
def gateBody : List (Stmt FOp) := match gateStmt with | Stmt.block b => b | _ => []
def gateCondStmt : Stmt FOp := gateBody.headD (Stmt.cond (Expr.lit (Literal.number 0)) [])
def gateCond : Expr FOp := match gateCondStmt with | Stmt.cond e _ => e | _ => Expr.lit (Literal.number 0)
def gateFailBody : List (Stmt FOp) := match gateCondStmt with | Stmt.cond _ b => b | _ => []
def gateB : Expr FOp :=
  Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"], Expr.var "EXPECTED_VK_LENGTH"]
def gateC : Expr FOp :=
  Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
    Expr.var "EXPECTED_VK_CODEHASH_WORD"]
def gateA : Expr FOp := Expr.builtin Op.and [gateB, gateC]

/-- The shell's entry frame at the curve Surface. -/
noncomputable def st₀ (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes) : EvmState :=
  callState W curveSurface.shellLayout H cd

theorem st₀_mem (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes) :
    (st₀ W H cd).memory = fun _ => 0 := rfl
theorem loadWord_zero (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes) :
    loadWord (st₀ W H cd).memory 64 = (0 : U256) := by
  rw [st₀_mem]; decide

def isFunDefS : Stmt FOp -> Bool
  | Stmt.funDef _ _ _ _ => true
  | _ => false

theorem stmt_isFunDef {d : Stmt FOp} (hd : isFunDefS d = true) :
    exists n ps rs b, d = Stmt.funDef n ps rs b := by
  cases d
  all_goals (first | exact ⟨_, _, _, _, rfl⟩ | exact absurd hd (by simp [isFunDefS]))

theorem mainDefs_are_defs : forall d, d ∈ mainDefs -> isFunDefS d = true := by decide
theorem drop8 : mainBlk.drop 8 = gateStmt :: mainRest := rfl
theorem main_decomp : mainBlk = mainDefs ++ (gateStmt :: mainRest) := by
  rw [<- drop8]
  exact (List.take_append_drop 8 mainBlk).symm
theorem gateStmt_is_block : gateStmt = Stmt.block gateBody := rfl
theorem gateBody_decomp : gateBody = gateCondStmt :: gateBody.tail := rfl
theorem gateCond_is_cond : gateCondStmt = Stmt.cond gateCond gateFailBody := rfl
theorem gateCond_shape : gateCond = Expr.builtin Op.iszero [gateA] := rfl
theorem gateA_shape : gateA = Expr.builtin Op.and [gateB, gateC] := rfl
theorem gateB_shape : gateB =
    Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"],
      Expr.var "EXPECTED_VK_LENGTH"] := rfl
theorem gateC_shape : gateC =
    Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
      Expr.var "EXPECTED_VK_CODEHASH_WORD"] := rfl

/-! ### 2. The stuckness lemma -/

mutual
/-- \`e\` mentions at least one variable. Mutual STRUCTURAL recursion, so unlike
    \`Midfall.Lowering.FrameWalk.freeNames\` (a \`WellFounded.fix\` the kernel will not reduce, hence
    the \`native_decide\` verdicts in \`FrameWalkWitness\`) every verdict in this file that reads it is
    \`decide\`, i.e. kernel-checked. -/
def exprHasVar {Op : Type} : Expr Op -> Bool
  | Expr.var _ => true
  | Expr.builtin _ args => exprsHasVar args
  | Expr.call _ args => exprsHasVar args
  | Expr.lit _ => false
def exprsHasVar {Op : Type} : List (Expr Op) -> Bool
  | [] => false
  | a :: as => exprHasVar a || exprsHasVar as
end

/-- **THE STUCKNESS LEMMA.** In a variable environment that binds nothing, nothing that mentions a
    variable can be evaluated to values: \`Step.var\` needs \`VEnv.get V x = some v\`
    (BigStep.lean:171-173) and \`VEnv.get [] x = none\`. -/
theorem step_vals_noVar {funs : FunEnv (OD' c g)} {st : EvmState} :
    ∀ {V : VEnv (OD' c g)} {code : Code FOp} {r : Res (OD' c g)},
      YulSemantics.Step (OD' c g) funs V st code r ->
      V = [] ->
      match code, r with
      | .expr e, .eres (.vals _ _) => exprHasVar e = false
      | .args es, .eres (.vals _ _) => exprsHasVar es = false
      | _, _ => True := by
  intro V code r h
  induction h with
  | lit => intro _; rfl
  | var hget =>
      intro hV
      rw [hV] at hget
      exact absurd hget (by simp [VEnv.get])
  | builtinOk _ _ ih => intro hV; exact ih hV
  | callOk _ _ _ _ _ ih _ => intro hV; exact ih hV
  | argsNil => intro _; rfl
  | argsCons _ _ ih₁ ih₂ => intro hV; simp [exprsHasVar, ih₁ hV, ih₂ hV]
  | _ => intro _; trivial

theorem no_step_var {funs : FunEnv (OD' c g)} {st : EvmState} {x : Ident} {r : EResult (OD' c g)}
    (h : YulSemantics.Step (OD' c g) funs [] st (.expr (Expr.var x)) (.eres r)) : False := by
  cases h with | var hget => exact absurd hget (by simp [VEnv.get])

theorem no_args_nil_halt {funs : FunEnv (OD' c g)} {st st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] st (.args []) (.eres (.halt st'))) : False := by cases h

theorem lit_no_halt {funs : FunEnv (OD' c g)} {st st' : EvmState} {l : Literal}
    (h : YulSemantics.Step (OD' c g) funs [] st (.expr (Expr.lit l)) (.eres (.halt st'))) : False := by
  cases h

/-- A one-element argument list that halts does so through its element. -/
theorem args1_halt {funs : FunEnv (OD' c g)} {st st' : EvmState} {a : Expr FOp}
    (h : YulSemantics.Step (OD' c g) funs [] st (.args [a]) (.eres (.halt st'))) :
    exists st₁, YulSemantics.Step (OD' c g) funs [] st₁ (.expr a) (.eres (.halt st')) := by
  cases h with
  | argsHeadHalt _ hhead => exact ⟨_, hhead⟩
  | argsRestHalt hrest => exact absurd hrest no_args_nil_halt

/-! ### 3. The builtins the arm reaches before it gets stuck -/

theorem bi_det {op : EVM.Op} {args : List U256} {st : EvmState}
    (hU : ∀ r, (OD' c g).Builtin op args st r ↔ YulSemantics.EVM.stepOp op args st = some r)
    {r₁ r₂ : BuiltinResult U256 EvmState} (h₁ : (OD' c g).Builtin op args st r₁)
    (h₂ : (OD' c g).Builtin op args st r₂) : r₁ = r₂ :=
  Option.some.inj (((hU r₁).mp h₁).symm.trans ((hU r₂).mp h₂))

theorem bi_not_halt {op : EVM.Op} {args : List U256} {st st' : EvmState}
    (hU : ∀ r, (OD' c g).Builtin op args st r ↔ YulSemantics.EVM.stepOp op args st = some r)
    (hok : exists rets st'', YulSemantics.EVM.stepOp op args st = some (.ok rets st'')) :
    ¬ (OD' c g).Builtin op args st (.halt st') := by
  obtain ⟨rets, st'', hstep⟩ := hok
  intro hh
  exact absurd (Option.some.inj (((hU (BuiltinResult.halt st')).mp hh).symm.trans hstep)) (by simp)

theorem bi_mload_ok {p : U256} {st : EvmState} :
    (OD' c g).Builtin Op.mload [p] st (.ok [loadWord st.memory p.toNat] (touchMemory st p.toNat 32)) :=
  rfl
theorem bi_gt_ok {a b : U256} {st : EvmState} :
    (OD' c g).Builtin Op.gt [a, b] st (.ok [b2w (b.ult a)] st) := rfl

/-! ### 4. The VK gate has no step -/

theorem gateB_no_halt {funs : FunEnv (OD' c g)} {st st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] st (.expr gateB) (.eres (.halt st'))) : False := by
  rw [gateB_shape] at h
  cases h with
  | builtinHalt hargs _ =>
      have hC := step_vals_noVar (funs := funs) (st := st) hargs rfl
      simp [gateB, gateC, exprHasVar, exprsHasVar] at hC
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt hrest _ =>
          have hC := step_vals_noVar (funs := funs) (st := st) hrest rfl
          simp [gateB, gateC, exprHasVar, exprsHasVar] at hC
      | argsRestHalt hrest =>
          obtain ⟨_, hh⟩ := args1_halt hrest
          exact no_step_var hh

theorem gateC_no_halt {funs : FunEnv (OD' c g)} {st st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] st (.expr gateC) (.eres (.halt st'))) : False := by
  rw [gateC_shape] at h
  cases h with
  | builtinHalt hargs _ =>
      have hC := step_vals_noVar (funs := funs) (st := st) hargs rfl
      simp [gateB, gateC, exprHasVar, exprsHasVar] at hC
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt hrest _ =>
          have hC := step_vals_noVar (funs := funs) (st := st) hrest rfl
          simp [gateB, gateC, exprHasVar, exprsHasVar] at hC
      | argsRestHalt hrest =>
          obtain ⟨_, hh⟩ := args1_halt hrest
          exact no_step_var hh

theorem gateA_no_halt {funs : FunEnv (OD' c g)} {st st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] st (.expr gateA) (.eres (.halt st'))) : False := by
  rw [gateA_shape] at h
  cases h with
  | builtinHalt hargs _ =>
      have hC := step_vals_noVar (funs := funs) (st := st) hargs rfl
      simp [gateB, gateC, exprHasVar, exprsHasVar] at hC
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt _ hB => exact gateB_no_halt hB
      | argsRestHalt hrest =>
          obtain ⟨_, hc⟩ := args1_halt hrest
          exact gateC_no_halt hc

theorem gate_no_expr {funs : FunEnv (OD' c g)} {st : EvmState} {r : EResult (OD' c g)}
    (h : YulSemantics.Step (OD' c g) funs [] st (.expr gateCond) (.eres r)) : False := by
  rw [gateCond_shape] at h
  cases h with
  | builtinOk hargs _ | builtinHalt hargs _ =>
      have hC := step_vals_noVar (funs := funs) (st := st) hargs rfl
      simp [gateA, gateB, gateC, exprHasVar, exprsHasVar] at hC
  | builtinArgsHalt hargs =>
      obtain ⟨_, ha⟩ := args1_halt hargs
      exact gateA_no_halt ha

theorem gate_no_step {funs : FunEnv (OD' c g)} {st : EvmState} {V' : VEnv (OD' c g)}
    {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) funs [] st (.stmt gateCondStmt) (.sres V' st' o)) : False := by
  rw [gateCond_is_cond] at h
  cases h with
  | ifTrue hexpr _ _ | ifFalse hexpr _ | ifHalt hexpr => exact gate_no_expr hexpr

theorem gate_no_stmts {funs : FunEnv (OD' c g)} {st : EvmState} {V' : VEnv (OD' c g)}
    {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) funs [] st (.stmts gateBody) (.sres V' st' o)) : False := by
  rw [gateBody_decomp] at h
  cases h with
  | seqCons hgate _ | seqStop hgate _ => exact gate_no_step hgate

/-! ### 5. The head guard passes, and definitions are no-ops -/

theorem hgTest_args_vals {funs : FunEnv (OD' c g)} {W : ExecEnv} {H : Midfall.Halo2.Hash}
    {cd : Bytes} {argvals : List U256} {st₁ : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] (st₀ W H cd)
      (.args [Expr.builtin Op.mload [Expr.lit (Literal.number 64)],
        Expr.lit (Literal.number 0x1000)]) (.eres (.vals argvals st₁))) :
    argvals = [0, 0x1000] := by
  cases h with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil hlit =>
          cases hnil
          cases hlit
          cases hhead with
          | builtinOk hnil2 hm =>
              cases hnil2 with
              | argsCons hnil3 hlit3 =>
                  cases hnil3
                  cases hlit3
                  have h0 : (OD' c g).Builtin Op.mload [(64 : U256)] (st₀ W H cd)
                      (.ok [loadWord (st₀ W H cd).memory 64]
                        (touchMemory (st₀ W H cd) 64 32)) := bi_mload_ok
                  rw [loadWord_zero W H cd] at h0
                  cases bi_det (fun _ => Iff.rfl) hm h0
                  rfl

theorem hgTest_vals {funs : FunEnv (OD' c g)} {W : ExecEnv} {H : Midfall.Halo2.Hash} {cd : Bytes}
    {cv : U256} {st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] (st₀ W H cd) (.expr hgTest) (.eres (.vals [cv] st'))) :
    cv = 0 := by
  cases h with
  | builtinOk hargs hb =>
      rw [hgTest_args_vals hargs] at hb
      cases bi_det (fun _ => Iff.rfl) hb bi_gt_ok
      rfl

theorem mload64_no_halt {funs : FunEnv (OD' c g)} {st st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] st
      (.expr (Expr.builtin Op.mload [Expr.lit (Literal.number 64)])) (.eres (.halt st'))) : False := by
  cases h with
  | builtinHalt hargs hb =>
      cases hargs with
      | argsCons hnil hlit =>
          cases hnil
          cases hlit
          exact bi_not_halt (fun _ => Iff.rfl) ⟨_, _, rfl⟩ hb
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt _ hlit => exact lit_no_halt hlit
      | argsRestHalt hnil => exact no_args_nil_halt hnil

theorem hgTest_no_halt {funs : FunEnv (OD' c g)} {W : ExecEnv} {H : Midfall.Halo2.Hash}
    {cd : Bytes} {st' : EvmState}
    (h : YulSemantics.Step (OD' c g) funs [] (st₀ W H cd) (.expr hgTest) (.eres (.halt st'))) : False := by
  cases h with
  | builtinHalt hargs hb =>
      rw [hgTest_args_vals hargs] at hb
      exact bi_not_halt (fun _ => Iff.rfl) ⟨_, _, rfl⟩ hb
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsHeadHalt _ hhead => exact mload64_no_halt hhead
      | argsRestHalt hrest =>
          cases hrest with
          | argsHeadHalt _ hlit => exact lit_no_halt hlit
          | argsRestHalt hnil => exact no_args_nil_halt hnil

/-- **THE HEAD GUARD IS NOT THE OBSTRUCTION.** \`if gt(mload(0x40), 0x1000) { revert(0,0) }\` passes
    from the shell's entry frame - memory is zero there - and it binds nothing, so the environment
    the arm's first executed statement sees is the empty one. -/
theorem guard_forced {funs : FunEnv (OD' c g)} {W : ExecEnv} {H : Midfall.Halo2.Hash} {cd : Bytes}
    {V' : VEnv (OD' c g)} {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) funs [] (st₀ W H cd) (.stmt hgStmt) (.sres V' st' o)) :
    V' = [] ∧ o = .normal := by
  rw [hgStmt_is] at h
  cases h with
  | ifTrue hexpr hcv _ =>
      have hcv0 := hgTest_vals (funs := funs) (W := W) (H := H) (cd := cd) hexpr
      rw [hcv0] at hcv
      exact absurd ShellModel.zero_eq_zero hcv
  | ifFalse _ _ => exact ⟨rfl, rfl⟩
  | ifHalt hexpr =>
      exact absurd hexpr (hgTest_no_halt (funs := funs) (W := W) (H := H) (cd := cd))

theorem peel_one_def {funs : FunEnv (OD' c g)} {V : VEnv (OD' c g)} {st : EvmState}
    {d : Stmt FOp} (hd : isFunDefS d = true) {rest : List (Stmt FOp)} {V' : VEnv (OD' c g)}
    {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) funs V st (.stmts (d :: rest)) (.sres V' st' o)) :
    YulSemantics.Step (OD' c g) funs V st (.stmts rest) (.sres V' st' o) := by
  obtain ⟨n, ps, rs, b, rfl⟩ := stmt_isFunDef hd
  cases h with
  | seqCons hs hrest => cases hs with | funDef => exact hrest
  | seqStop hs ho => cases hs with | funDef => exact absurd rfl ho

theorem peel_defs {funs : FunEnv (OD' c g)} {V : VEnv (OD' c g)} {st : EvmState} :
    ∀ (defs : List (Stmt FOp)), (∀ d, d ∈ defs -> isFunDefS d = true) ->
      ∀ (rest : List (Stmt FOp)) {V' : VEnv (OD' c g)} {st' : EvmState} {o : Outcome},
        YulSemantics.Step (OD' c g) funs V st (.stmts (defs ++ rest)) (.sres V' st' o) ->
        YulSemantics.Step (OD' c g) funs V st (.stmts rest) (.sres V' st' o) := by
  intro defs hdefs rest V' st' o h
  induction defs with
  | nil => exact h
  | cons d ds ih =>
      have h1 : YulSemantics.Step (OD' c g) funs V st (.stmts (ds ++ rest)) (.sres V' st' o) :=
        peel_one_def (hdefs d (by simp)) h
      exact ih (fun x hx => hdefs x (by simp [hx])) h1

/-! ### 6. THE INVERSION: the arm has no run at all -/

/-- Inverting a block step: the body runs in the same variable environment the block started with. -/
theorem step_block_inv {funs : FunEnv (OD' c g)} {V : VEnv (OD' c g)} {st : EvmState}
    {body : List (Stmt FOp)} {V' : VEnv (OD' c g)} {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) funs V st (.stmt (Stmt.block body)) (.sres V' st' o)) :
    exists Vb, YulSemantics.Step (OD' c g) (hoist (OD' c g) body :: funs) V st (.stmts body)
      (.sres Vb st' o) := by
  cases h
  exact ⟨_, ‹_›⟩

/-- Inverting the top-level program step: `Run` is a block step from the empty environments. -/
theorem step_top_inv {st₀ : EvmState} {V' : VEnv (OD' c g)} {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) [] [] st₀ (.stmt (Stmt.block armBlk)) (.sres V' st' o)) :
    exists Vb, YulSemantics.Step (OD' c g) (hoist (OD' c g) armBlk :: []) [] st₀ (.stmts armBlk)
      (.sres Vb st' o) := by
  cases h
  exact ⟨_, ‹_›⟩

/-- **NO RUN OF THE ARM**, at any \`callState\` frame, for any call relation and any gas oracle. -/
theorem no_arm_run {W : ExecEnv} {H : Midfall.Halo2.Hash} {cd : Bytes}
    {V' : VEnv (OD' c g)} {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step (OD' c g) [] [] (st₀ W H cd)
      (.stmt (Stmt.block armBlk)) (.sres V' st' o)) : False := by
  obtain ⟨Vb, hbody⟩ := step_top_inv h
  rw [arm_cons] at hbody
  cases hbody with
  | seqCons hguard hmain =>
      have ⟨hrfl, _⟩ := guard_forced hguard
      rw [hrfl] at hmain
      rw [main_decomp] at hmain
      have h2 := peel_defs mainDefs mainDefs_are_defs (gateStmt :: mainRest) hmain
      rw [gateStmt_is_block] at h2
      cases h2 with
      | seqCons hgate _ | seqStop hgate _ =>
          obtain ⟨Vb2, hstmts⟩ := step_block_inv hgate
          exact gate_no_stmts hstmts
  | seqStop hguard ho =>
      have ⟨_, horfl⟩ := guard_forced hguard
      exact absurd horfl ho

/-! ### 7. RunShell at the curve Surface is empty -/

/-- **THE INVERSION, AT THE SURFACE.** For every world, every hash, every calldata, every call
    relation and every gas oracle, \`RunShell curveSurface\` has NO observation: the set is empty. -/
theorem runShell_curveSurface_empty (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (obs : Midfall.Yul.Bridge.Obs) :
    ¬ RunShell curveSurface W H cd c g obs := by
  rintro ⟨V', st', hrun, _⟩
  rw [<- FrameWalkWitness.armBlk_is_the_shell_codeBlock] at hrun
  exact no_arm_run hrun

/-- The same emptiness at the FIXTURE Surface: its shell block, its layout and its empty
    \`bindLocals\` are the same data, so \`RunShell realSurface\` is empty too. -/
theorem runShell_realSurface_empty (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (obs : Midfall.Yul.Bridge.Obs) :
    ¬ RunShell realSurface W H cd c g obs := by
  rintro ⟨V', st', hrun, _⟩
  have key : realSurface.shell.codeBlock = armBlk := rfl
  rw [key] at hrun
  exact no_arm_run hrun

/-! ### 8. The dispatcher side IS inhabited there, so ObsEquiv fails -/

/-- **ONE SIDE INHABITED.** On the empty calldata the dispatcher falls through to \`revert(0,0)\` for
    ANY arm body (\`ShellModel.unroutable_calldata_reverts\`), so \`wrap curveSurface\` has an
    observation at exactly the frame where \`RunShell curveSurface\` has none. -/
theorem wrap_empty_cd_inhabited (c : ExternalCalls) (g : ExternalGas) :
    ∃ obs, ShellModel.wrap curveSurface fxW keccak256 (ByteArray.empty : Bytes) c g obs := by
  have hsize : ShellModel.sizeTestValue
      (callState fxW curveSurface.shellLayout keccak256 (ByteArray.empty : Bytes)) = 0 := rfl
  obtain ⟨st', hrun, _⟩ :=
    ShellModel.unroutable_calldata_reverts (body := ShellModel.armBody curveSurface) hsize
  exact ⟨⟨committedState (callState fxW curveSurface.shellLayout keccak256
      (ByteArray.empty : Bytes)) st', .halt⟩, ⟨[], ⟨st', hrun, rfl⟩⟩⟩

/-- **THE OBSERVATIONAL EQUIVALENCE FAILS.** One view exists on the dispatcher side and on no
    observation of the shell side - because there is no observation of the shell side. -/
theorem obsEquiv_wrap_runShell_fails (c : ExternalCalls) (g : ExternalGas) :
    ¬ ObsEquiv (ShellModel.wrap curveSurface fxW keccak256 (ByteArray.empty : Bytes) c g)
      (RunShell curveSurface fxW keccak256 (ByteArray.empty : Bytes) c g) := by
  intro h
  obtain ⟨obs, hwrap⟩ := wrap_empty_cd_inhabited c g
  obtain ⟨o, hsh, _⟩ := (h obs.view).1 ⟨obs, hwrap, rfl⟩
  exact runShell_curveSurface_empty fxW keccak256 (ByteArray.empty : Bytes) c g o hsh

/-- The empty call relation is world-local, so it is an admissible witness for the binder
    \`ir_refines\` puts on the call relation. No assumption about the precompiles is needed for the
    refutation: the arm gets stuck before it reaches one. -/
theorem noCalls_worldLocal : ExternalCalls.WorldLocal ExternalCalls.none :=
  fun _ _ _ _ _ => Iff.rfl

/-- **\`LoweringCorrect.ir_refines\` AT THE CURVE SURFACE IS REFUTED, NOT UNPROVABLE.** Read at the
    in-tree dispatcher model \`ShellModel.modelIr curveSurface\` - the object the headline
    \`lowering_equivalence\` transports through, whose import check is \`rfl\` - its conclusion is false
    for a world-local call relation, a zero gas oracle, the fixture world and the empty calldata. -/
theorem ir_refines_refuted_at_curveSurface :
    ¬ (∀ (ir : YulObject) (irLyt : EVM.Layout), curveSurface.irCheck ir = true →
        ∀ (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes) (c : ExternalCalls) (g₀ : U256),
          c.WorldLocal →
          ObsEquiv (RunContractIR curveSurface W H ir irLyt cd c (ExternalGas.ofFun fun _ => g₀))
            (RunShell curveSurface W H cd c (ExternalGas.ofFun fun _ => g₀))) := by
  intro h
  have hob := h (ShellModel.modelIr curveSurface) curveSurface.shellLayout
    (ShellModel.modelIr_irCheck curveSurface) fxW keccak256 (ByteArray.empty : Bytes)
    ExternalCalls.none 0 noCalls_worldLocal
  obtain ⟨obs, hwrap⟩ := wrap_empty_cd_inhabited ExternalCalls.none (ExternalGas.ofFun fun _ => 0)
  have hiff := ShellModel.wrap_iff_modelRunContractIR curveSurface fxW keccak256
    (ByteArray.empty : Bytes) ExternalCalls.none (ExternalGas.ofFun fun _ => 0) obs
  obtain ⟨o, ho, _⟩ := (hob obs.view).1 ⟨obs, hiff.mpr hwrap, rfl⟩
  exact runShell_curveSurface_empty fxW keccak256 (ByteArray.empty : Bytes) ExternalCalls.none
    (ExternalGas.ofFun fun _ => 0) o ho

/-- **THE REQUIRED FINDING: THE CURVE SURFACE CANNOT DISCHARGE \`LoweringCorrect\` AT ALL.** For
    EVERY \`product\`. The bundle has a FALSE field, not an unproved one. So
    \`lowering_equivalence curveSurface product\` is vacuous for every product, and the eight-leg
    exhibit \`loweqBundleCore\` - every binder the headline takes outside its bundle - cannot be
    repaired into a witness of the bundle. -/
theorem curveSurface_not_LoweringCorrect (product : PairingProduct) :
    ¬ LoweringCorrect curveSurface product := by
  intro hc
  exact ir_refines_refuted_at_curveSurface hc.ir_refines

/-- The same emptiness at the IMPORT-NAMING Surface: it is \`realSurface\` with one field changed,
    and \`shell\` is not that field, so its arm is the same open statement list. -/
theorem runShell_irSurface_empty (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (obs : Midfall.Yul.Bridge.Obs) :
    ¬ RunShell Midfall.Instances.ImportedIR.irSurface W H cd c g obs := by
  rintro ⟨V', st', hrun, _⟩
  have key : Midfall.Instances.ImportedIR.irSurface.shell.codeBlock = armBlk := rfl
  rw [key] at hrun
  exact no_arm_run hrun

/-- **THE STRONGER REFUTATION: IT IS NOT AN ARTEFACT OF THE MODEL OBJECT.** The \`ir_refines\` shape
    that \`Instances/ImportedIR.lean:355\` states as an \`example : Prop\` and hopes stage 6 will prove
    is FALSE at the REAL imported solc artifact. \`irHypothesis_jointlyInhabited\` exhibits, for every
    call relation and gas oracle, ONE object that both passes \`irSurface.irCheck\` and has a committed
    \`RunContractIR\` at the empty calldata; the shell side of the same equivalence is empty. So the M8
    bridge is refuted for solc's own output and not merely for \`ShellModel.modelIr\`, and no
    IR-to-shell simulation can prove it while the shell's arm is the emitted program. -/
theorem ir_refines_refuted_at_the_imported_artifact :
    ¬ (∀ (ir : YulObject) (irLyt : EVM.Layout),
        Midfall.Instances.ImportedIR.irSurface.irCheck ir = true →
        ∀ (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes) (c : ExternalCalls) (g₀ : U256),
          c.WorldLocal →
          ObsEquiv (RunContractIR Midfall.Instances.ImportedIR.irSurface W H ir irLyt cd c
            (ExternalGas.ofFun fun _ => g₀))
            (RunShell Midfall.Instances.ImportedIR.irSurface W H cd c (ExternalGas.ofFun fun _ => g₀))) := by
  intro h
  obtain ⟨ir, irLyt, obs, hcheck, hrun⟩ :=
    Midfall.Instances.ImportedIR.irHypothesis_jointlyInhabited ExternalCalls.none
      (ExternalGas.ofFun fun _ => 0)
  have hob := h ir irLyt hcheck Midfall.Instances.ImportedIR.irW keccak256
    Midfall.Instances.ImportedIR.irCd ExternalCalls.none 0 noCalls_worldLocal
  obtain ⟨o, ho, _⟩ := (hob obs.view).1 ⟨obs, hrun, rfl⟩
  exact runShell_irSurface_empty Midfall.Instances.ImportedIR.irW keccak256
    Midfall.Instances.ImportedIR.irCd ExternalCalls.none (ExternalGas.ofFun fun _ => 0) o ho

/-! ### 9. D-P23: the falsification half -/

/-- The head guard's test, evaluated POSITIVELY: \`gt(mload(0x40), 0x1000) = 0\` in the shell frame. -/
theorem hgTest_step {funs : FunEnv (OD' c g)} {W : ExecEnv} {H : Midfall.Halo2.Hash} {cd : Bytes} :
    YulSemantics.Step (OD' c g) funs [] (st₀ W H cd) (.expr hgTest)
      (.eres (.vals [0] (touchMemory (st₀ W H cd) 64 32))) := by
  have hrest : YulSemantics.Step (OD' c g) funs [] (st₀ W H cd)
      (.args [Expr.lit (Literal.number 0x1000)]) (.eres (.vals [0x1000] (st₀ W H cd))) :=
    Step.argsCons (D := OD' c g) (Step.argsNil (D := OD' c g)) (Step.lit (D := OD' c g))
  have hml : YulSemantics.Step (OD' c g) funs [] (st₀ W H cd)
      (.expr (Expr.builtin Op.mload [Expr.lit (Literal.number 64)]))
      (.eres (.vals [0] (touchMemory (st₀ W H cd) 64 32))) :=
    Step.builtinOk (D := OD' c g)
      (Step.argsCons (D := OD' c g) (Step.argsNil (D := OD' c g)) (Step.lit (D := OD' c g)))
      (by
        have h0 : (OD' c g).Builtin Op.mload [(64 : U256)] (st₀ W H cd)
            (.ok [loadWord (st₀ W H cd).memory 64] (touchMemory (st₀ W H cd) 64 32)) := bi_mload_ok
        rw [loadWord_zero W H cd] at h0
        exact h0)
  exact Step.builtinOk (D := OD' c g) (Step.argsCons (D := OD' c g) hrest hml)
    (bi_gt_ok (c := c) (g := g))

/-- **FALSIFICATION 1: THE HEAD GUARD IS NOT WHY THERE IS NO RUN.** \`[head guard; revert(0,0)]\` HAS
    a run from the same frame: the guard passes and execution reaches the statement after it. Delete
    the gate and the emptiness goes away; delete the guard and it stays. -/
theorem guard_is_not_the_obstruction {W : ExecEnv} {H : Midfall.Halo2.Hash} {cd : Bytes} :
    exists st', YulSemantics.Step (OD' c g) [] [] (st₀ W H cd)
      (.stmts [hgStmt, ShellModel.revert00]) (.sres [] st' .halt) := by
  have hp : YulSemantics.Step (OD' c g) [] [] (st₀ W H cd) (.stmt hgStmt)
      (.sres ([] : VEnv (OD' c g)) (touchMemory (st₀ W H cd) 64 32) .normal) := by
    rw [hgStmt_is]
    exact Step.ifFalse (D := OD' c g) (hgTest_step (funs := []) (W := W) (H := H) (cd := cd))
      ShellModel.zero_eq_zero
  refine ⟨_, Step.seqCons (D := OD' c g) hp
    (Step.seqStop (D := OD' c g) (ShellModel.revert00_step (c := c) (g := g))
      ShellModel.halt_ne_normal)⟩

/-- **FALSIFICATION 2: THE MISSING BINDING IS THE WHOLE OBSTRUCTION.** The same read that kills the
    arm - \`extcodesize(vk)\` - has a derivation as soon as \`vk\` is bound. So \`no_arm_run\` is not a
    theorem about \`extcodesize\`, about the frame, or about every program: supply the binding and the
    run exists. -/
def boundProbe : List (Stmt FOp) :=
  [Stmt.letDecl ["vk"] (some (Expr.lit (Literal.number 0x1000))),
   Stmt.letDecl ["n"] (some (Expr.builtin Op.extcodesize [Expr.var "vk"])),
   ShellModel.revert00]

theorem bound_read_has_a_run {W : ExecEnv} {H : Midfall.Halo2.Hash} {cd : Bytes} :
    exists (V' : VEnv (OD' c g)) (st' : EvmState), YulSemantics.Step (OD' c g) [] [] (st₀ W H cd)
      (.stmt (Stmt.block boundProbe)) (.sres V' st' .halt) := by
  have hget : VEnv.get (D := OD' c g) ([("vk", (0x1000 : U256))] : VEnv (OD' c g)) "vk" =
      some (0x1000 : U256) := rfl
  have h1 : YulSemantics.Step (OD' c g) (hoist (OD' c g) boundProbe :: []) [] (st₀ W H cd)
      (.stmt (Stmt.letDecl ["vk"] (some (Expr.lit (Literal.number 0x1000)))))
      (.sres [("vk", (0x1000 : U256))] (st₀ W H cd) .normal) :=
    Step.letVal (D := OD' c g) (Step.lit (D := OD' c g)) rfl
  have h2 : YulSemantics.Step (OD' c g) (hoist (OD' c g) boundProbe :: []) [("vk", (0x1000 : U256))]
      (st₀ W H cd) (.expr (Expr.builtin Op.extcodesize [Expr.var "vk"]))
      (.eres (.vals [BitVec.ofNat 256 ((st₀ W H cd).env.extCodeOf (0x1000 : U256)).length]
        (st₀ W H cd))) :=
    Step.builtinOk (D := OD' c g)
      (Step.argsCons (D := OD' c g) (Step.argsNil (D := OD' c g)) (Step.var hget))
      (rfl : (OD' c g).Builtin Op.extcodesize [(0x1000 : U256)] (st₀ W H cd)
        (.ok [BitVec.ofNat 256 ((st₀ W H cd).env.extCodeOf (0x1000 : U256)).length] (st₀ W H cd)))
  have h3 : YulSemantics.Step (OD' c g) (hoist (OD' c g) boundProbe :: []) [("vk", (0x1000 : U256))]
      (st₀ W H cd) (.stmt (Stmt.letDecl ["n"] (some (Expr.builtin Op.extcodesize [Expr.var "vk"]))))
      (.sres (("n", BitVec.ofNat 256 ((st₀ W H cd).env.extCodeOf (0x1000 : U256)).length) ::
        [("vk", (0x1000 : U256))]) (st₀ W H cd) .normal) :=
    Step.letVal (D := OD' c g) h2 rfl
  have h4 : YulSemantics.Step (OD' c g) (hoist (OD' c g) boundProbe :: [])
      [("n", BitVec.ofNat 256 ((st₀ W H cd).env.extCodeOf (0x1000 : U256)).length),
        ("vk", (0x1000 : U256))] (st₀ W H cd) (.stmt ShellModel.revert00)
      (.sres [("n", BitVec.ofNat 256 ((st₀ W H cd).env.extCodeOf (0x1000 : U256)).length),
        ("vk", (0x1000 : U256))] (ShellModel.revertState (st₀ W H cd)) .halt) :=
    ShellModel.revert00_step (c := c) (g := g)
  exact ⟨_, _, Step.block (D := OD' c g) (body := boundProbe) (funs := []) (V := [])
    (st := st₀ W H cd)
    (Step.seqCons (D := OD' c g) h1
      (Step.seqCons (D := OD' c g) h3
        (Step.seqStop (D := OD' c g) h4 ShellModel.halt_ne_normal)))⟩

/-! ### 10. Why a fixture-only fix is not the honest fix -/

/-- **A YUL FUNCTION IS NOT A CLOSURE.** \`Step.callOk\` initialises the callee environment with the
    parameters and the zeroed return slots and nothing else (BigStep.lean:189), so no block placed
    above a call can bind a name that the callee's body reads and its own signature does not
    provide. The instance that matters: \`transcript_init\` as emitted takes no parameters, returns one
    word, and its body reads \`TRANSCRIPT_MPTR\` - one of the 61 free identifiers of the arm - so in
    EVERY derivation of a call to it that name is unbound. -/
def helperSig (n : String) : List Ident × List Ident :=
  (mainBlk.filterMap fun
    | Stmt.funDef m ps rs _ => if m == n then some (ps, rs) else none
    | _ => none).headD ([], [])

theorem transcript_init_signature : helperSig "transcript_init" = ([], ["buf_len"]) := by decide

theorem transcript_init_name_unbound_in_callee (argvals : List U256) :
    VEnv.get (D := OD' c g) ((helperSig "transcript_init").1.zip argvals ++
      bindZeros (OD' c g) (helperSig "transcript_init").2) "TRANSCRIPT_MPTR" = none := rfl

/-- The names each emitted helper reads that neither its parameters, its return slots, nor its own
    binders provide. SIX of the EIGHT emitted helpers have such names, so the arm is not a closed
    Yul program and no legal value of \`Surface.bindLocals\` can make it one. -/
def helperOwnFree : List (String × List String) :=
  mainBlk.filterMap fun
    | Stmt.funDef n ps rs body =>
        let fr := (Midfall.Lowering.FrameWalk.freeNames body).filter fun x =>
          !(ps.contains x || rs.contains x)
        if fr.isEmpty then none else some (n, fr)
    | _ => none

/-- SIX OF EIGHT helpers, as a gate rather than a sentence. \`freeNames\` is the \`WellFounded.fix\`
    mutual recursion the kernel will not reduce, so this is a KAT (compiler-trusted), and it is a
    measurement rather than a load-bearing step of any theorem above. -/
def helperOwnFree_count_ok : Bool := helperOwnFree.length == 6

#eval helperOwnFree_count_ok -- expect true

/-- **THE FIXTURE FIX IS NOT ENOUGH, AS A MEASUREMENT.** With the artifact's own constant table bound
    at the arm level - the maximal legal \`bindLocals\` - the driver that calls \`transcript_init\` is
    STUCK, because the helper's own body reads a name the arm-level binding cannot reach. -/
def helperStuckUnderArmLevelBinding_ok : Bool :=
  match YulSemantics.Interp.run EVM.exec 20000
    (Midfall.Lowering.RunEmitted.shellLets ++ mainDefs ++
      [Stmt.exprStmt (Expr.call "transcript_init" [])]) EvmState.init with
  | .stuck => true
  | _ => false

#eval helperStuckUnderArmLevelBinding_ok -- expect true

/-- **AND THE FIXTURE FIX DOES MAKE THE EMPTY-CALLDATA RUN EXIST.** With the same binding the whole
    arm reverts with a four-byte selector instead of getting stuck. Stated so the next reader sees
    exactly what a \`bindLocals\` patch would and would not buy: it inhabits this one calldata, and it
    does not close the program. -/
def armRunsUnderArmLevelBinding_ok : Bool :=
  match YulSemantics.Interp.run EVM.exec 20000
    (Midfall.Lowering.RunEmitted.shellLets ++ armBlk) EvmState.init with
  | .ok (_, st, _) => match st.halted with
      | some (.revert, d) => d.length == 4
      | _ => false
  | _ => false

#eval armRunsUnderArmLevelBinding_ok -- expect true

/-- The vendored interpreter, run on the arm exactly as \`RunShell\` runs it, agrees with
    \`no_arm_run\`: STUCK. Independent evidence, not a substitute for the theorem. -/
def armInterpStuck_ok : Bool :=
  match YulSemantics.Interp.run EVM.exec 4000 armBlk EvmState.init with
  | .stuck => true
  | _ => false

#eval armInterpStuck_ok -- expect true

/-- **THE STUCKNESS IS NOT AN ARTEFACT OF THE CONSTANT VALUES.** Binding every one of the 61 free
    names to zero does not produce a run either: the VK gate then passes and the program dies inside
    \`transcript_init\`. So the obstruction is the missing bindings, not the wrong ones. -/
def bindAllFreeZero : List (Stmt FOp) :=
  (Midfall.Lowering.FrameWalk.freeNames armBlk).map fun n =>
    Stmt.letDecl [n] (some (Expr.lit (Literal.number 0)))

def armBoundAllZeroStillStuck_ok : Bool :=
  match YulSemantics.Interp.run EVM.exec 20000 (bindAllFreeZero ++ armBlk) EvmState.init with
  | .stuck => true
  | _ => false

#eval armBoundAllZeroStillStuck_ok -- expect true

/-! ### 11. The entry-path difference: the same binding problem, plus a difference that cannot be seen -/

/-- The dispatcher model runs three statements in front of the arm - the memoryguard prologue, the
    size-guarded selector switch and the fall-through abort - and inside the \`verifyProof\` arm it
    runs the callvalue guard, the thirteen ABI decode statements and the two immutable bindings. -/
def entry_path_len_ok : Bool :=
  (ShellModel.dispatcher armBlk).length == 3 &&
    ShellModel.armPrefix.length == 16 &&
    ShellModel.abiDecode.length == 13 &&
    ShellModel.bindLocalsFromImmutables.length == 2 &&
    (ShellModel.verifyProofArm armBlk).length == armBlk.length + 16

#eval entry_path_len_ok -- expect true

/-- **THE DISPATCHER BINDS \`vk\`; THE SHELL DOES NOT.** \`bindLocalsFromImmutables\` is two \`let\`
    declarations and one of them binds \`vk\`. So on that name the entry-path difference and the
    free-identifier difference are the SAME FACT seen from two sides: the arm's \`vk\` is bound by the
    dispatcher's entry path in the deployed contract, and \`RunShell\` omits the entry path. -/
theorem entry_path_binds_vk :
    (ShellModel.bindLocalsFromImmutables.filterMap fun
      | Stmt.letDecl xs _ => some xs
      | _ => none).flatten.contains "vk" = true := rfl

/-- **AND THE SHELL SIDE IS EMPTY FOR EVERY CALLDATA**, not just the unroutable one. That is what
    makes the guard-firing difference unobservable at this Surface: there is no shell run at any
    input for a guard to disagree with. The guard difference is a REAL second mechanism - R-66 and
    \`ShellModel.old_shell_runs_the_verifier_on_the_same_frame\` prove it on a body with no free
    identifiers - but it is MASKED here, not independent evidence. -/
theorem runShell_empty_for_every_cd (W : ExecEnv) (H : Midfall.Halo2.Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (obs : Midfall.Yul.Bridge.Obs) :
    ¬ RunShell curveSurface W H cd c g obs :=
  runShell_curveSurface_empty W H cd c g obs

#print axioms Midfall.Instances.RunShellInversion.no_arm_run
#print axioms Midfall.Instances.RunShellInversion.runShell_curveSurface_empty
#print axioms Midfall.Instances.RunShellInversion.ir_refines_refuted_at_the_imported_artifact
#print axioms Midfall.Instances.RunShellInversion.ir_refines_refuted_at_curveSurface
#print axioms Midfall.Instances.RunShellInversion.curveSurface_not_LoweringCorrect
#print axioms Midfall.Instances.RunShellInversion.guard_is_not_the_obstruction
#print axioms Midfall.Instances.RunShellInversion.bound_read_has_a_run
#print axioms Midfall.Instances.RunShellInversion.step_vals_noVar
#print axioms Midfall.Instances.RunShellInversion.guard_forced
#print axioms Midfall.Instances.RunShellInversion.hgTest_vals
#print axioms Midfall.Instances.RunShellInversion.wrap_empty_cd_inhabited

end Midfall.Instances.RunShellInversion

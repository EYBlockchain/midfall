import WP
import P1_Exec
import Lits
set_option autoImplicit false

/-!
WPBridge (scratch, prooftech): the wp engine instantiated at the OPEN Bridge dialect, for ANY call
relation and ANY gas oracle (so it covers `permissive (callsOf product)` with an arbitrary `g`,
which `run_adequacy` and `dialect_deterministic` do not).
-/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering Midfall.LoweringV2 Midfall.Instances.PoseidonValid
open Midfall.Scratch.ProofTech.Lits

/-- The demonic built-in transformer of the open dialect. `staticcall` quantifies over EVERY
    response the relation admits, `gas()` over every oracle word; the other call/create ops are
    refused (the generated verifier never uses them); a local op is one `stepOp` evaluation, and a
    stuck local op is `False`. -/
def Bopen (c : ExternalCalls) (g : ExternalGas) : BT (Bridge.Dialect c g) := fun op args st Q =>
  match op with
  | .staticcall =>
      match args with
      | [gas, target, io, is, oo, os] =>
          ∀ resp, c.Call ⟨.staticcall, gas, target, 0, readBytes st.memory io.toNat is.toNat⟩ st resp →
            Q (.ok [resp.flag] (finishCall .staticcall st resp io.toNat is.toNat oo.toNat os.toNat))
      | _ => False
  | .gas =>
      match args with
      | [] => ∀ w, g.Gas st w → Q (.ok [w] st)
      | _ => False
  | .call | .callcode | .delegatecall | .create | .create2 => False
  | _ =>
      match stepOp op args st with
      | some r => Q r
      | none => False

theorem Bopen_sound (c : ExternalCalls) (g : ExternalGas) :
    BSound (Bridge.Dialect c g) (Bopen c g) := by
  intro op args st Q h r hr
  cases op
  all_goals try (
    have hr' : stepOp _ args st = some r := hr
    simp only [Bopen, hr'] at h
    exact h)
  case staticcall =>
    rcases args with _|⟨a,_|⟨b,_|⟨io,_|⟨is,_|⟨oo,_|⟨os,_|⟨x7,xs⟩⟩⟩⟩⟩⟩⟩
    all_goals simp only [Bopen] at h
    all_goals try exact h.elim
    simp only [builtinWithExternal] at hr
    obtain ⟨resp, hcall, rfl⟩ := hr
    exact h resp hcall
  case gas =>
    cases args with
    | cons a as => simp only [Bopen] at h
    | nil =>
        simp only [Bopen] at h
        simp only [builtinWithExternal] at hr
        obtain ⟨w, hw, rfl⟩ := hr
        exact h w hw
  all_goals (simp only [Bopen] at h)

/-- No call summaries: every user function is inlined. -/
def Cnone (D : Dialect) : CT D := fun _ _ _ _ => none

theorem Cnone_sound (D : Dialect) [DecidableEq D.Value] : CSound D (Cnone D) := by
  intro funs fn argvals st1 T h
  cases h

#print axioms Bopen_sound

end Midfall.Scratch.ProofTech

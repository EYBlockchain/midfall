import WPTac
import Midfall.Lowering.Qvm
set_option autoImplicit false

/-!
WPX (scratch, prooftech): PROPOSED STATEMENTS that are not proved in this session. Every
definition is real; theorem bodies marked `sorry` are work-package deliverables.
-/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering Midfall.LoweringV2

section Exists
variable (D : Dialect) [DecidableEq D.Value] (B : BT D) (C : CT D)

/-- The built-in transformer is LIVE: when it holds, a relational result exists and satisfies `Q`. -/
def BLive : Prop :=
  ∀ op args st Q, B op args st Q → ∃ r, D.Builtin op args st r ∧ Q r

/-- **TOTALITY (a run exists).** With a live transformer and no summaries, `wp` exhibits a run.
    Together with `wp_sound` this is `StmtsTotal` (Blocks.lean:50) from ONE evaluation, and it is
    the non-stuckness guarantee finding C-1 asks for. PROOF: induction on fuel, building the `Step`
    derivation (the mirror image of `wp_sound`; about the same size). NOT PROVED HERE. -/
theorem wpSS_exists (hB : BLive D B) (hC : ∀ funs fn args st, C funs fn args st = none)
    {n : Nat} {funs : FunEnv D} {V : VEnv D} {st : D.State} {ss : Block D.Op}
    {Q : VEnv D → D.State → Outcome → Prop} (h : wpSS D B C n funs V st ss Q) :
    ∃ V' st' o, ExecStmts D funs V st ss V' st' o ∧ Q V' st' o := by
  sorry
end Exists

/-- The FUNCTIONAL transformer of a function-graph dialect (the honest dialect of conjunct 2):
    one evaluation of the executable step. Sound AND live, by `execOf_lawful`. -/
def Bfun (c : ExternalCalls) (g : ExternalGas)
    (cf : EVM.CallRequest → EvmState → Option CallResponse) (gf : EvmState → U256) :
    BT (Bridge.Dialect c g) := fun op args st Q =>
  match execBuiltin cf gf op args st with
  | some r => Q r
  | none => False

theorem Bfun_sound {c : ExternalCalls} {g : ExternalGas}
    {cf : EVM.CallRequest → EvmState → Option CallResponse} {gf : EvmState → U256}
    (hc : ∀ req st resp, c.Call req st resp ↔ cf req st = some resp)
    (hg : ∀ st w, g.Gas st w ↔ w = gf st) :
    BSound (Bridge.Dialect c g) (Bfun c g cf gf) := by
  intro op args st Q h r hr
  have hr' : execBuiltin cf gf op args st = some r := (execOf_lawful hc hg op args st r).mp hr
  simp only [Bfun, hr'] at h
  exact h

theorem Bfun_live {c : ExternalCalls} {g : ExternalGas}
    {cf : EVM.CallRequest → EvmState → Option CallResponse} {gf : EvmState → U256}
    (hc : ∀ req st resp, c.Call req st resp ↔ cf req st = some resp)
    (hg : ∀ st w, g.Gas st w ↔ w = gf st) :
    BLive (Bridge.Dialect c g) (Bfun c g cf gf) := by
  intro op args st Q h
  cases hx : execBuiltin cf gf op args st with
  | none => simp only [Bfun, hx] at h
  | some r =>
      simp only [Bfun, hx] at h
      exact ⟨r, (execOf_lawful hc hg op args st r).mpr hx, h⟩

/-- **PREFIX DETERMINISM without `dialect_deterministic` (finding C-3).** For ANY call relation and
    ANY gas oracle: if `wp` shows every run of a statement list ends at one named endpoint, two runs
    agree. For call-free, gas-free code (the ABI guard, wrapper locals, MF-2 guard, `mainLocals`)
    the `wp` evaluation never consults an oracle, so this applies to
    `permissive (callsOf product)` with an arbitrary `g`. -/
theorem runs_agree_of_wp {c : ExternalCalls} {g : ExternalGas} {n : Nat}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {V₀ : VEnv (Bridge.Dialect c g)} {st₀ : EvmState} {o₀ : Outcome}
    (h : wpSS (Bridge.Dialect c g) (Bopen c g) (Cnone _) n funs V st ss
      fun V' st' o => V' = V₀ ∧ st' = st₀ ∧ o = o₀)
    {V₁ V₂ : VEnv (Bridge.Dialect c g)} {st₁ st₂ : EvmState} {o₁ o₂ : Outcome}
    (h₁ : ExecStmts (Bridge.Dialect c g) funs V st ss V₁ st₁ o₁)
    (h₂ : ExecStmts (Bridge.Dialect c g) funs V st ss V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ := by
  have a := allRuns_of_wp n h V₁ st₁ o₁ h₁
  have b := allRuns_of_wp n h V₂ st₂ o₂ h₂
  exact ⟨a.1.trans b.1.symm, a.2.1.trans b.2.1.symm, a.2.2.trans b.2.2.symm⟩

/-- The memory layer's central missing lemma (statement only): word read over word write at
    non-overlapping or equal 32-byte windows. NOT IN THE TREE (grep `loadWord.*storeWord`: 0 hits). -/
theorem loadWord_storeWord (mem : Nat → UInt8) (p q : Nat) (v : U256) :
    loadWord (storeWord mem p v) q =
      if q = p then v else if q + 32 ≤ p ∨ p + 32 ≤ q then loadWord mem q
      else loadWord (storeWord mem p v) q := by
  sorry

/-- The arithmetic layer's central missing lemma (statement only): EVM `mulmod` at the scalar
    modulus is field multiplication on canonical words. `qvmToFr_mul` (Qvm.lean:148) is the Nat-level
    half that exists. -/
theorem mulmod_toFr (a b : U256) :
    Midfall.Lowering.qvmToFr
        (BitVec.ofNat 256 ((a.toNat * b.toNat) % Midfall.Generator.qvmFrModulus)).toNat =
      Midfall.Lowering.qvmToFr a.toNat * Midfall.Lowering.qvmToFr b.toNat := by
  sorry

#print axioms Bfun_sound
#print axioms Bfun_live
#print axioms runs_agree_of_wp
end Midfall.Scratch.ProofTech

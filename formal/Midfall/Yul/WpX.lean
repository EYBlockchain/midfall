/-
  Midfall.Yul.WpX

  THE WPX EXISTENCE AND LAYER STATEMENTS (T3.1b, PLAN-V3). Ported VERBATIM from the scratch source
  docs/plans/V3-evidence/lean/prooftech/WPX.lean; the only changes are the import paths, the
  namespace (the scratch ProofTech namespace -> Midfall.Yul.WpX) and the deletion of the four
  declarations BLive, Bfun, Bfun_sound and Bfun_live, which T3.1 had ALREADY landed verbatim in
  Midfall/Yul/WpBridge.lean (that file's header names WPX.lean as their source). Restating them here
  would duplicate a proved declaration, so this file uses Midfall.Yul.WpBridge.BLive instead. No
  statement and no proof step was restated.

  WHAT IS HERE. Three registered holes and one proved bridge:

    * wpSS_exists        TOTALITY: with a LIVE transformer and an empty summary table, a wpSS proof
                         exhibits a run. T3.2 owns it (register). Together with wp_sound this is
                         StmtsTotal (Blocks.lean:50) from ONE evaluation, and it is the
                         non-stuckness guarantee finding C-1 asks for.
    * loadWord_storeWord the memory layer's central missing lemma. T3.5 owns it.
    * mulmod_toFr        the arithmetic layer's central missing lemma. T3.8 owns it.
    * runs_agree_of_wp   PROVED here: prefix determinism WITHOUT dialect_deterministic (finding C-3),
                         by two applications of WpTac.allRuns_of_wp.

  D-P71: no native_decide in this file, and none is needed - runs_agree_of_wp is a term-level
  argument over the soundness theorem. The three holes are REGISTERED in SORRY.md, not carried.
-/
import Midfall.Yul.WpTac
import Midfall.Lowering.Qvm
set_option autoImplicit false

namespace Midfall.Yul.WpX
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac

section Exists
variable (D : Dialect) [DecidableEq D.Value] (B : BT D) (C : CT D)

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

#print axioms runs_agree_of_wp
end Midfall.Yul.WpX

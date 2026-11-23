/-
  Midfall.LoweringV3.ScalarInvSummary

  A9 (ROW.PCS): THE `scalar_inv` SUMMARY. The body of `GenAst.emitScalarInvAt pv` is the
  declared list `scalarBody pv` (the guards, the six modexp frame stores, and the read-back).
  Under the honest-permissive precompile relation, every run is either

  * normal, with `inv` bound to the word `(x^{-1} mod blsR)` (`SIPost`), or
  * a revert.

  The proof composes the landed statement contracts: `ScalarInv.guardLt_contract`,
  `ScalarInv.guardNonzero_contract`, `ScalarInv.modexpFrameStores_mxMem`,
  `ModexpGeneral.staticcallGuard_contract`, `ModexpGeneral.returndatasizeGuard_contract` and
  `ModexpGeneral.invAssign_contract`. The staticcall's success answer is identified by
  `ModexpGeneral.callsOf_modexp_returndata` / `mxMem_modexpOutput`; the read-back through
  `ModexpGeneral.loadWord_copyReturn_bytesNatBE`.

  No row is wired here; no hypothesis is added to a row, bundle, root or `ValidV3`.
-/
import Midfall.LoweringV3.ModexpGeneral

set_option autoImplicit false

open Midfall Midfall.Lowering Midfall.Generator Midfall.LoweringV3.PcsRows
open Midfall.LoweringV3.ModexpGeneral Midfall.LoweringV3.ScalarInv
open Midfall.LoweringV2 Midfall.LoweringV2.Blocks.TraceReturn
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {c : ExternalCalls} {g : ExternalGas}

namespace Midfall.LoweringV3.ScalarInvSummary

/-! ## Read-back plumbing: `returndatasize` and `mload` -/

theorem eval_iszero_eq_returndatasize (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.eq
          [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
      (.vals [cv] st')) :
    cv = b2w (b2w (BitVec.ofNat 256 st.returndata.length = BitVec.ofNat 256 32) = 0) ∧
      st' = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hheadEq =>
          cases hrest with
          | argsNil =>
              cases hheadEq with
              | builtinOk hargs2 hbi2 =>
                  cases hargs2 with
                  | argsCons hrest2 hheadRt =>
                      cases hrest2 with
                      | argsCons hrest3 hheadLit =>
                          cases hrest3 with
                          | argsNil =>
                              cases hheadRt with
                              | builtinOk hargs3 hbi3 =>
                                  cases hargs3 with
                                  | argsNil =>
                                      obtain ⟨hv, hstlit⟩ :=
                                        eval_lit_eq funs V (st := _) 32 hheadLit
                                      simp [Bridge.Dialect, builtinWithExternal, stepOp, rd0,
                                        bin, un] at hbi hbi2 hbi3
                                      obtain ⟨hrd, hstrd⟩ := hbi3
                                      obtain ⟨heq, hsteq⟩ := hbi2
                                      obtain ⟨hisz, hstisz⟩ := hbi
                                      refine ⟨?_, hstisz.symm.trans (hsteq.symm.trans
                                        (hstrd.symm.trans hstlit))⟩
                                      rw [← hisz, ← heq, ← hrd, hstlit, hv]
                                      rfl

theorem expr_returndatasize_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.returndatasize []) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsNil => simp [Bridge.Dialect, builtinWithExternal, stepOp, rd0] at hbi
  | builtinArgsHalt hargs => cases hargs

theorem expr_eq_returndatasize_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.eq
        [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)])
      (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hheadRt =>
          cases hrest with
          | argsCons hrest2 hheadLit =>
              cases hrest2 with
              | argsNil =>
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h =>
          cases h with
          | argsRestHalt h' => cases h'
          | argsHeadHalt _ h' => exact trExprLit_ne_halts h'
      | argsHeadHalt _ h' => exact expr_returndatasize_ne_halts funs V h'

theorem expr_iszero_eq_returndatasize_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.eq
          [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
      (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              simp [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h' => exact expr_eq_returndatasize_ne_halts funs V h'


theorem eval_mload_var_vals (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (xv : U256) (hx : VEnv.get V x = some xv) {vs : List U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mload [Expr.var x]) (.vals vs st')) :
    ∃ a, vs = [a] ∧ a = loadWord st.memory xv.toNat ∧ st' = touchMemory st xv.toNat 32 := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              obtain ⟨hxv, hst⟩ := eval_var_eq funs V x xv hx hhead
              rw [hst] at hbi
              rw [← hxv] at ⊢
              simp [Bridge.Dialect, builtinWithExternal, stepOp] at hbi
              exact ⟨loadWord st.memory _, hbi.1.symm, rfl, hbi.2.symm⟩

theorem expr_mload_var_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} (x : String) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.mload [Expr.var x]) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil => simp [Bridge.Dialect, builtinWithExternal, stepOp] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h' => exact trExprVar_ne_halts h'

theorem returndatasizeGuard_contract {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) {cenv : FunEnv (Bridge.Dialect c g)}
    (sv invW selP : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.eq
            [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])])
      (fun V st => VEnv.get V "ERR_PRECOMPILE_FAILED" = some selP ∧
        st.returndata.length = 32 ∧
        loadWord st.memory sv.toNat = invW)
      (fun V st V' st' o =>
        (o = .normal ∧ VEnv.get V' "ERR_PRECOMPILE_FAILED" = some selP ∧
          st'.returndata.length = 32 ∧ loadWord st'.memory sv.toNat = invW ∧
          V' = V ∧ st' = st)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtContractAll.cond ?_ ?_
  · intro V st cv st₁ hpre heval
    obtain ⟨hsel, hlen, hload⟩ := hpre
    obtain ⟨hcv, hst⟩ := eval_iszero_eq_returndatasize funs V heval
    constructor
    · intro hzero
      refine Or.inl ⟨rfl, hsel, ?_, ?_, rfl, hst⟩
      · rw [hst]; exact hlen
      · rw [hst]; exact hload
    · intro hnz V' st' o hbody
      cases hbody with
      | block hb =>
          have hfail' : lookupFun (hoist (Bridge.Dialect c g)
              [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])] :: funs)
              "fail" = some (failFDecl, cenv) := hfail
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
              ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
          · exact absurd (fail_call_reverts hfail' h1).1 (by decide)
          · exact Or.inr (fail_call_reverts hfail' h1)
  · intro V st st₁ hpre heval
    exact absurd heval (expr_iszero_eq_returndatasize_ne_halts funs V)

theorem invAssign_contract {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (sv invW : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.assign ["inv"] (Expr.builtin EVM.Op.mload [Expr.var "p"]))
      (fun V st => VEnv.get V "p" = some sv ∧ loadWord st.memory sv.toNat = invW ∧
        (VEnv.get V "inv").isSome)
      (fun V st V' st' o =>
        (o = .normal ∧ VEnv.get V' "inv" = some invW ∧
          st'.memory = st.memory ∧ st'.halted = st.halted)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hload, hinv⟩ := hpre
  cases hrun with
  | assignVal he hlen =>
      obtain ⟨a, hvs, ha, hst⟩ := eval_mload_var_vals funs V "p" sv hp he
      subst hvs
      refine Or.inl ⟨rfl, ?_, ?_, ?_⟩
      · rw [ha, hload]
        cases hv : VEnv.get V "inv" with
        | none => simp [hv] at hinv
        | some inv0 =>
            simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
              List.foldl_nil]
            exact venv_get_set_same (D := Bridge.Dialect c g) hv
      · rw [hst]; rfl
      · rw [hst]; rfl
  | assignHalt he =>
      exact absurd he (expr_mload_var_ne_halts funs V "p")

abbrev sv (n : Nat) : U256 := BitVec.ofNat 256 n

abbrev SIEnv0 {c : ExternalCalls} {g : ExternalGas} (xv gasv selN selP : U256)
    (V : VEnv (Bridge.Dialect c g)) : Prop :=
  VEnv.get V "x" = some xv ∧
  VEnv.get V "FR_MODULUS" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
  VEnv.get V "MODEXP_GAS" = some gasv ∧
  VEnv.get V "ERR_NON_CANONICAL_SCALAR" = some selN ∧
  VEnv.get V "ERR_PRECOMPILE_FAILED" = some selP ∧
  (VEnv.get V "inv").isSome

abbrev SIEnv {c : ExternalCalls} {g : ExternalGas} (scratch : Nat) (xv gasv selN selP : U256)
    (V : VEnv (Bridge.Dialect c g)) : Prop :=
  VEnv.get V "p" = some (sv scratch) ∧ SIEnv0 xv gasv selN selP V

abbrev SIFrame (scratch : Nat) (xv : U256) (st : EvmState) : Prop :=
  readBytes st.memory (sv scratch).toNat 192 = (modexpInvFrame xv.toNat).data.toList

abbrev SIPost {c : ExternalCalls} {g : ExternalGas} (invW : U256)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  (o = .normal ∧ VEnv.get V' "inv" = some invW) ∨
    (o = .halt ∧ Midfall.LoweringV2.Reverted st')

theorem guards_contract (funs : FunEnv (Bridge.Dialect c g)) {cenv : FunEnv (Bridge.Dialect c g)}
    (scratch : Nat) (xv gasv selN selP : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.lt [Expr.var "x", Expr.var "FR_MODULUS"]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_NON_CANONICAL_SCALAR"])],
        Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "x"])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_NON_CANONICAL_SCALAR"])],
        Stmt.letDecl ["p"] (some (Expr.lit (Literal.number scratch))) ]
      (fun V _ => SIEnv0 xv gasv selN selP V)
      (fun V st V' st' o =>
        (o = .normal ∧ SIEnv scratch xv gasv selN selP V')
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtsContractAll.cons_split (D := Bridge.Dialect c g)
    (mid := fun V _ => SIEnv0 xv gasv selN selP V) ?_ ?_
  · intro V st hpre V' st' o hrun
    obtain ⟨hx, hfr, hgas, hselN, hselP, hinv⟩ := hpre
    have h := guardLt_contract (funs := funs) (cenv := cenv) xv
      (BitVec.ofNat 256 Midfall.Yul.blsR) selN hfail V st ⟨hx, hfr, hselN⟩ V' st' o hrun
    rcases h with ⟨ho, hV, _hm, _he, _hh⟩ | ⟨ho, hrev⟩
    · refine Or.inl ⟨ho, ?_⟩
      subst hV
      exact ⟨hx, hfr, hgas, hselN, hselP, hinv⟩
    · exact Or.inr ⟨by rw [ho]; decide, Or.inr ⟨ho, hrev⟩⟩
  · intro V st hpre
    refine StmtsContractAll.cons_split (D := Bridge.Dialect c g)
      (mid := fun V _ => SIEnv0 xv gasv selN selP V) ?_ ?_
    · intro V1 st1 hpre1 V' st' o hrun
      obtain ⟨hx, hfr, hgas, hselN, hselP, hinv⟩ := hpre1
      have h := guardNonzero_contract (funs := funs) (cenv := cenv) xv selN hfail
        V1 st1 ⟨hx, hselN⟩ V' st' o hrun
      rcases h with ⟨ho, hV, _hm, _he, _hh⟩ | ⟨ho, hrev⟩
      · refine Or.inl ⟨ho, ?_⟩
        subst hV
        exact ⟨hx, hfr, hgas, hselN, hselP, hinv⟩
      · exact Or.inr ⟨by rw [ho]; decide, Or.inr ⟨ho, hrev⟩⟩
    · intro V2 st2 hpre2 V3 st3 hpre3 V' st' o hrun
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
          ⟨Vl, stl, hl, hrestl⟩ | ⟨hl, hne⟩
      · cases hl with
        | letVal he hlen =>
            cases he with
            | lit =>
                cases hrestl
                obtain ⟨hx, hfr, hgas, hselN, hselP, hinv⟩ := hpre3
                refine Or.inl ⟨rfl, ?_⟩
                change SIEnv scratch xv gasv selN selP
                  (("p", (Bridge.Dialect c g).litValue (Literal.number scratch)) :: V3)
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · exact venv_get_cons_self _ _ _
                · exact (venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "x")
                    (by decide)).trans hx
                · exact (venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p")
                    (y := "FR_MODULUS") (by decide)).trans hfr
                · exact (venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p")
                    (y := "MODEXP_GAS") (by decide)).trans hgas
                · exact (venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p")
                    (y := "ERR_NON_CANONICAL_SCALAR") (by decide)).trans hselN
                · exact (venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p")
                    (y := "ERR_PRECOMPILE_FAILED") (by decide)).trans hselP
                · simpa [VEnv.get, List.find?,
                    show decide (("p" : String) = "inv") = false by decide] using hinv
      · cases hl with
        | letVal he hlen => exact absurd rfl hne
        | letHalt he => cases he

theorem stores_contract (funs : FunEnv (Bridge.Dialect c g))
    (scratch : Nat) (xv gasv selN selP : U256)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.var "FR_MODULUS")
        Midfall.Generator.templateConstantsDefault)
      (fun V _ => SIEnv scratch xv gasv selN selP V)
      (fun V st V' st' o =>
        (o = .normal ∧ SIEnv scratch xv gasv selN selP V' ∧ SIFrame scratch xv st')
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩ := hpre
  have h := modexpFrameStores_mxMem (funs := funs) (pv := sv scratch) xv hscratch
    V st ⟨hp, hx, hfr⟩ V' st' o hrun
  rcases h with ⟨ho, hV, hmem, henv, hhalt⟩
  refine Or.inl ⟨ho, ?_, ?_⟩
  · subst hV
    exact ⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩
  · unfold SIFrame
    rw [hmem]
    exact mxMem_frame st.memory (sv scratch).toNat xv

abbrev SIInv (xv : U256) : U256 := BitVec.ofNat 256 ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val

theorem readBack_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch : Nat) (xv gasv selN selP : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      [ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.staticcall
            [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
             Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])],
        Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.eq
            [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])],
        Stmt.assign ["inv"] (Expr.builtin EVM.Op.mload [Expr.var "p"]) ]
      (fun V st => SIEnv scratch xv gasv selN selP V ∧
        0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR ∧ SIFrame scratch xv st)
      (fun V st V' st' o => SIPost (SIInv xv) V' st' o) := by
  refine StmtsContractAll.cons_split (D := Bridge.Dialect (permissive (callsOf product)) g)
    (mid := fun V st => SIEnv scratch xv gasv selN selP V ∧
      st.returndata.length = 32 ∧ loadWord st.memory (sv scratch).toNat = SIInv xv) ?_ ?_
  · intro V st hpre V' st' o hrun
    obtain ⟨hEnv, hx0, hxR, hframe⟩ := hpre
    obtain ⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩ := hEnv
    have h := staticcallGuard_contract (product := product) (funs := funs) (cenv := cenv)
      xv (sv scratch) gasv selP hfail V st
      ⟨hgas, hp, hselP, hx, hx0, hxR, hframe⟩ V' st' o hrun
    rcases h with ⟨ho, hV, resp, hsucc, hcall, hst, hret, hload⟩ | ⟨ho, hrev⟩
    · refine Or.inl ⟨ho, ?_⟩
      refine ⟨?_, ?_, hload⟩
      · rw [hV] at ⊢
        exact ⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩
      · rw [hst]
        show resp.returndata.length = 32
        rw [hret, Array.length_toList, ByteArray.size_data]
        exact Midfall.Assumptions.bytesNatBE_size _ 32
    · exact Or.inr ⟨by rw [ho]; decide, Or.inr ⟨ho, hrev⟩⟩
  · intro V st hpre
    refine StmtsContractAll.cons_split (D := Bridge.Dialect (permissive (callsOf product)) g)
      (mid := fun V st => SIEnv scratch xv gasv selN selP V ∧
        st.returndata.length = 32 ∧ loadWord st.memory (sv scratch).toNat = SIInv xv) ?_ ?_
    · intro V1 st1 hmid V' st' o hrun
      obtain ⟨hEnv, hlen, hload⟩ := hmid
      obtain ⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩ := hEnv
      have h := returndatasizeGuard_contract (funs := funs) (cenv := cenv)
        (sv scratch) (SIInv xv) selP hfail V1 st1 ⟨hselP, hlen, hload⟩ V' st' o hrun
      rcases h with ⟨ho, hselP', hlen', hload', hV, hst⟩ | ⟨ho, hrev⟩
      · refine Or.inl ⟨ho, ?_⟩
        subst hV
        exact ⟨⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩, hlen', hload'⟩
      · exact Or.inr ⟨by rw [ho]; decide, Or.inr ⟨ho, hrev⟩⟩
    · intro V2 st2 hpre2 V3 st3 hpre3 V' st' o hrun
      obtain ⟨hEnv, hlen, hload⟩ := hpre3
      obtain ⟨hp, hx, hfr, hgas, hselN, hselP, hinv⟩ := hEnv
      rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
          ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
      · cases hrest4
        refine Or.inl ⟨rfl, ?_⟩
        have h := invAssign_contract (funs := funs) (sv scratch) (SIInv xv)
          V3 st3 ⟨hp, hload, hinv⟩ _ _ _ h4
        rcases h with ⟨_, hinv', _, _⟩ | ⟨ho, _⟩
        · exact hinv'
        · exact absurd ho (by decide)
      · have h := invAssign_contract (funs := funs) (sv scratch) (SIInv xv)
          V3 st3 ⟨hp, hload, hinv⟩ V' st' o h4
        rcases h with ⟨ho, hinv', _hm, _hh⟩ | ⟨ho, hrev⟩
        · exact absurd ho hne4
        · exact Or.inr ⟨ho, hrev⟩

def scalarBody (pv : PlanView) : Block EVM.Op :=
  match GenAst.emitScalarInvAt pv with
  | [Stmt.funDef _ _ _ body] => body
  | _ => []

theorem scalarBody_eq (pv : PlanView) :
    scalarBody pv =
      [ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.lt [Expr.var "x", Expr.var "FR_MODULUS"]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_NON_CANONICAL_SCALAR"])],
        Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "x"])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_NON_CANONICAL_SCALAR"])],
        Stmt.letDecl ["p"] (some (Expr.lit (Literal.number pv.memory.scalarInvScratchMptr))) ] ++
      GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.var "FR_MODULUS")
        Midfall.Generator.templateConstantsDefault ++
      [ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.staticcall
            [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
             Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])],
        Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.eq
            [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])],
        Stmt.assign ["inv"] (Expr.builtin EVM.Op.mload [Expr.var "p"]) ] := by
  rfl

theorem guardsStores_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch : Nat) (xv gasv selN selP : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv))
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      ([ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.lt [Expr.var "x", Expr.var "FR_MODULUS"]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_NON_CANONICAL_SCALAR"])],
        Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "x"])
          [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_NON_CANONICAL_SCALAR"])],
        Stmt.letDecl ["p"] (some (Expr.lit (Literal.number scratch))) ] ++
        GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.var "FR_MODULUS")
          Midfall.Generator.templateConstantsDefault)
      (fun V _ => SIEnv0 xv gasv selN selP V)
      (fun V st V' st' o =>
        (o = .normal ∧ SIEnv scratch xv gasv selN selP V' ∧ SIFrame scratch xv st')
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtsContractAll.append (D := Bridge.Dialect (permissive (callsOf product)) g)
    (mid := fun V _ => SIEnv scratch xv gasv selN selP V) ?_ ?_
  · intro V st hpre V' st' o hrun
    rcases guards_contract (funs := funs) (cenv := cenv) scratch xv gasv selN selP hfail
      V st hpre V' st' o hrun with ⟨ho, hmid⟩ | ⟨ho, hrev⟩
    · exact Or.inl ⟨ho, hmid⟩
    · exact Or.inr ⟨by rw [ho]; decide, Or.inr ⟨ho, hrev⟩⟩
  · intro V st hpre
    exact stores_contract (funs := funs) scratch xv gasv selN selP hscratch

theorem emitScalarInvAt_body_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (pv : PlanView) (xv gasv selN selP : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv))
    (hscratch : (sv pv.memory.scalarInvScratchMptr).toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (scalarBody pv)
      (fun V _ => SIEnv0 xv gasv selN selP V ∧
        0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR)
      (fun V st V' st' o => SIPost (SIInv xv) V' st' o) := by
  rw [scalarBody_eq]
  refine StmtsContractAll.append (D := Bridge.Dialect (permissive (callsOf product)) g)
    (mid := fun V st =>
      SIEnv pv.memory.scalarInvScratchMptr xv gasv selN selP V ∧
        SIFrame pv.memory.scalarInvScratchMptr xv st) ?_ ?_
  · intro V st hpre V' st' o hrun
    rcases guardsStores_contract (product := product) (funs := funs) (cenv := cenv)
      pv.memory.scalarInvScratchMptr xv gasv selN selP hfail hscratch
      V st hpre.1 V' st' o hrun with ⟨ho, hmid⟩ | ⟨ho, hrev⟩
    · exact Or.inl ⟨ho, hmid⟩
    · exact Or.inr ⟨by rw [ho]; decide, Or.inr ⟨ho, hrev⟩⟩
  · intro V st hpre
    intro V1 st1 hmid1 V2 st2 o hrun
    exact readBack_contract (product := product) (funs := funs) (cenv := cenv)
      pv.memory.scalarInvScratchMptr xv gasv selN selP hfail
      V1 st1 ⟨hmid1.1, hpre.2.1, hpre.2.2, hmid1.2⟩ V2 st2 o hrun



theorem fail_expr_any {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {e : Expr EVM.Op} {r : EResult (Bridge.Dialect c g)}
    (hne : ∀ st₁ st₂, EvalExpr (Bridge.Dialect c g) funs V st₁ e (.halt st₂) → False)
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : Step (Bridge.Dialect c g) funs V st
        (Code.expr (Expr.call "fail" [e])) (Res.eres r)) :
    ∃ st₂, r = .halt st₂ ∧ Midfall.LoweringV2.Reverted st₂ := by
  cases h with
  | callOk hargs hlookup' hlen hbody ho =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts =>
          obtain ⟨ho', hrev⟩ := tr_fail_body hstmts
          cases ho with
          | inl hn => exact absurd (hn.symm.trans ho') (by decide)
          | inr hl => exact absurd (hl.symm.trans ho') (by decide)
  | callHalt hargs hlookup' hlen hbody =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts => exact ⟨_, rfl, (tr_fail_body hstmts).2⟩
  | callArgsHalt hargs =>
      exact (trArgs1_halt_inv hargs (fun st₁ hh => hne st₁ _ hh)).elim

theorem fail_call_any_reverts {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {e : Expr EVM.Op}
    (hne : ∀ st₁ st₂, EvalExpr (Bridge.Dialect c g) funs V st₁ e (.halt st₂) → False)
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.call "fail" [e])) V' st' o) :
    o = .halt ∧ Midfall.LoweringV2.Reverted st' := by
  cases h with
  | exprStmt hex =>
      obtain ⟨st₂, hr, hrev⟩ := fail_expr_any hne hlookup hex
      exact absurd hr (by simp)
  | exprStmtHalt hex =>
      obtain ⟨st₂, hr, hrev⟩ := fail_expr_any hne hlookup hex
      cases hr
      exact ⟨rfl, hrev⟩


theorem eval_iszero_lt_var_lit (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (xv : U256) (n : Nat) (hx : VEnv.get V x = some xv) {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.lt [Expr.var x, Expr.lit (Literal.number n)]])
      (.vals [a] st')) :
    a = b2w (b2w (xv.ult (BitVec.ofNat 256 n)) = 0) ∧ st' = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              cases hhead with
              | builtinOk hargs2 hbi2 =>
                  cases hargs2 with
                  | argsCons hrest2 hheadX =>
                      cases hrest2 with
                      | argsCons hrest3 hheadN =>
                          cases hrest3 with
                          | argsNil =>
                              obtain ⟨hxv, hsx⟩ := eval_var_eq funs V x xv hx hheadX
                              obtain ⟨hn, hsn⟩ := eval_lit_eq funs V (st := _) n hheadN
                              rw [hsn] at hheadX
                              rw [hsx, hsn] at hbi2
                              rw [← hxv, ← hn] at ⊢
                              simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi2
                              rw [← hbi2.2] at hbi
                              simp [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
                              refine ⟨?_, hbi.2.symm⟩
                              rw [← hbi.1, ← hbi2.1]
                              rfl
theorem expr_lt_var_lit_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} (x : String) (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.lt [Expr.var x, Expr.lit (Literal.number n)]) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hheadX =>
          cases hrest with
          | argsCons hrest2 hheadN =>
              cases hrest2 with
              | argsNil =>
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h =>
          cases h with
          | argsRestHalt h' => cases h'
          | argsHeadHalt _ h' => exact trExprLit_ne_halts h'
      | argsHeadHalt _ h' => exact trExprVar_ne_halts h'

theorem expr_iszero_lt_var_lit_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} (x : String) (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.lt [Expr.var x, Expr.lit (Literal.number n)]])
      (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              simp [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h' => exact expr_lt_var_lit_ne_halts funs V x n h'

theorem guardLt_lit_contract (funs : FunEnv (Bridge.Dialect c g))
    {cenv : FunEnv (Bridge.Dialect c g)} (n : Nat) (xv : U256) (sel : Nat)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.lt [Expr.var "x", Expr.lit (Literal.number n)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])])
      (fun V st => VEnv.get V "x" = some xv)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = V ∧ st'.memory = st.memory ∧ st'.env = st.env ∧
          st'.halted = st.halted) ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtContractAll.cond ?_ ?_
  · intro V st cv st₁ hpre heval
    have hx := hpre
    obtain ⟨hcv, hst⟩ := eval_iszero_lt_var_lit funs V "x" xv n hx heval
    constructor
    · intro hzero
      refine Or.inl ⟨rfl, rfl, ?_, ?_, ?_⟩
      · rw [hst]
      · rw [hst]
      · rw [hst]
    · intro hnz V' st' o hbody
      cases hbody with
      | block hb =>
          have hfail' : lookupFun (hoist (Bridge.Dialect c g)
              [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])] :: funs)
              "fail" = some (failFDecl, cenv) := hfail
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
              ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
          · exact absurd (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1).1
              (by decide)
          · exact Or.inr (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1)
  · intro V st st₁ hpre heval
    exact absurd heval (expr_iszero_lt_var_lit_ne_halts funs V "x" n)

theorem guardNonzero_lit_contract (funs : FunEnv (Bridge.Dialect c g))
    {cenv : FunEnv (Bridge.Dialect c g)} (xv : U256) (sel : Nat)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "x"])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])])
      (fun V st => VEnv.get V "x" = some xv)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = V ∧ st'.memory = st.memory ∧ st'.env = st.env ∧
          st'.halted = st.halted) ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtContractAll.cond ?_ ?_
  · intro V st cv st₁ hpre heval
    have hx := hpre
    obtain ⟨hcv, hst⟩ := eval_iszero_var funs V "x" xv hx heval
    constructor
    · intro hzero
      refine Or.inl ⟨rfl, rfl, ?_, ?_, ?_⟩
      · rw [hst]
      · rw [hst]
      · rw [hst]
    · intro hnz V' st' o hbody
      cases hbody with
      | block hb =>
          have hfail' : lookupFun (hoist (Bridge.Dialect c g)
              [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])] :: funs)
              "fail" = some (failFDecl, cenv) := hfail
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
              ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
          · exact absurd (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1).1
              (by decide)
          · exact Or.inr (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1)
  · intro V st st₁ hpre heval
    exact absurd heval (expr_iszero_var_ne_halts funs V "x")

theorem eval_sub_lit_lit (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (m n : Nat) {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.lit (Literal.number m), Expr.lit (Literal.number n)])
      (.vals [a] st')) :
    a = BitVec.ofNat 256 m - BitVec.ofNat 256 n ∧ st' = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hheadM =>
          cases hrest with
          | argsCons hrest2 hheadN =>
              cases hrest2 with
              | argsNil =>
                  obtain ⟨hm, hsm⟩ := eval_lit_eq funs V (st := _) m hheadM
                  obtain ⟨hn, hsn⟩ := eval_lit_eq funs V (st := _) n hheadN
                  rw [hsn] at hheadM
                  rw [hsm, hsn] at hbi
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
                  rw [← hm, ← hn] at ⊢
                  exact ⟨hbi.1.symm, hbi.2.symm⟩


theorem expr_sub_lit_lit_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} (m n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.lit (Literal.number m), Expr.lit (Literal.number n)])
      (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hheadM =>
          cases hrest with
          | argsCons hrest2 hheadN =>
              cases hrest2 with
              | argsNil =>
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h =>
          cases h with
          | argsRestHalt h' => cases h'
          | argsHeadHalt _ h' => exact trExprLit_ne_halts h'
      | argsHeadHalt _ h' => exact trExprLit_ne_halts h'

theorem modexpFrameStores_lit_contract (funs : FunEnv (Bridge.Dialect c g))
    (pv xv : U256) (n : Nat) (hbound : pv.toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.lit (Literal.number n))
        Midfall.Generator.templateConstantsDefault)
      (fun V st => VEnv.get V "p" = some pv ∧ VEnv.get V "x" = some xv)
      (fun V st V' st' o => o = .normal ∧ V' = V ∧
        st'.memory = mxMemFr st.memory pv.toNat xv (BitVec.ofNat 256 n) ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hx⟩ := hpre
  simp only [GenAst.modexpFrameStores, Midfall.Generator.templateConstantsDefault,
    GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit] at hrun
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨hV1, hmem1, henv1, hhalt1⟩ :=
      exec_mstore_state (c := c) (g := g) funs h1
        (fun stV v hv => (eval_lit_eq funs V (st := st) 32 hv).2)
        (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 0 pv hp ha).2)
        (fun stA a ha => (eval_add_var_lit funs V (st := st) "p" 0 pv hp ha).1)
        (fun stV v hv => (eval_lit_eq funs V (st := st) 32 hv).1)
    subst V1
    rw [toNat_add_ofNat pv 0 (by omega)] at hmem1
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
        ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨hV2, hmem2, henv2, hhalt2⟩ :=
        exec_mstore_state (c := c) (g := g) funs h2
          (fun stV v hv => (eval_lit_eq funs V (st := st1) 32 hv).2)
          (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 32 pv hp ha).2)
          (fun stA a ha => (eval_add_var_lit funs V (st := st1) "p" 32 pv hp ha).1)
          (fun stV v hv => (eval_lit_eq funs V (st := st1) 32 hv).1)
      subst V2
      rw [toNat_add_ofNat pv 32 (by omega)] at hmem2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
          ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · obtain ⟨hV3, hmem3, henv3, hhalt3⟩ :=
          exec_mstore_state (c := c) (g := g) funs h3
            (fun stV v hv => (eval_lit_eq funs V (st := st2) 32 hv).2)
            (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 64 pv hp ha).2)
            (fun stA a ha => (eval_add_var_lit funs V (st := st2) "p" 64 pv hp ha).1)
            (fun stV v hv => (eval_lit_eq funs V (st := st2) 32 hv).1)
        subst V3
        rw [toNat_add_ofNat pv 64 (by omega)] at hmem3
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
            ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · obtain ⟨hV4, hmem4, henv4, hhalt4⟩ :=
            exec_mstore_state (c := c) (g := g) funs h4
              (fun stV v hv => (eval_var_eq funs V (st := st3) "x" xv hx hv).2)
              (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 96 pv hp ha).2)
              (fun stA a ha => (eval_add_var_lit funs V (st := st3) "p" 96 pv hp ha).1)
              (fun stV v hv => (eval_var_eq funs V (st := st3) "x" xv hx hv).1)
          subst V4
          rw [toNat_add_ofNat pv 96 (by omega)] at hmem4
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest4 with
              ⟨V5, st5, h5, hrest5⟩ | ⟨h5, hne5⟩
          · obtain ⟨hV5, hmem5, henv5, hhalt5⟩ :=
              exec_mstore_state (c := c) (g := g) funs h5
                (fun stV v hv => (eval_sub_lit_lit funs V (st := st4) n 2 hv).2)
                (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 128 pv hp ha).2)
                (fun stA a ha => (eval_add_var_lit funs V (st := st4) "p" 128 pv hp ha).1)
                (fun stV v hv => (eval_sub_lit_lit funs V (st := st4) n 2 hv).1)
            subst V5
            rw [toNat_add_ofNat pv 128 (by omega)] at hmem5
            rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest5 with
                ⟨V6, st6, h6, hrest6⟩ | ⟨h6, hne6⟩
            · obtain ⟨hV6, hmem6, henv6, hhalt6⟩ :=
                exec_mstore_state (c := c) (g := g) funs h6
                  (fun stV v hv => (eval_lit_eq funs V (st := st5) n hv).2)
                  (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 160 pv hp ha).2)
                  (fun stA a ha => (eval_add_var_lit funs V (st := st5) "p" 160 pv hp ha).1)
                  (fun stV v hv => (eval_lit_eq funs V (st := st5) n hv).1)
              subst V6
              rw [toNat_add_ofNat pv 160 (by omega)] at hmem6
              cases hrest6
              refine ⟨rfl, rfl, ?_, ?_, ?_⟩
              · rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
                simp [mxMemFr]
              · rw [henv6, henv5, henv4, henv3, henv2, henv1]
              · rw [hhalt6, hhalt5, hhalt4, hhalt3, hhalt2, hhalt1]
            · exact absurd (exec_mstore_normal funs h6
                (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 160) hh)
                (fun s₁ s₂ hh => trExprLit_ne_halts hh)) hne6
          · exact absurd (exec_mstore_normal funs h5
              (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 128) hh)
              (fun s₁ s₂ hh => expr_sub_lit_lit_ne_halts funs V n 2 hh)) hne5
        · exact absurd (exec_mstore_normal funs h4
            (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 96) hh)
            (fun s₁ s₂ hh => trExprVar_ne_halts hh)) hne4
      · exact absurd (exec_mstore_normal funs h3
          (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 64) hh)
          (fun s₁ s₂ hh => trExprLit_ne_halts hh)) hne3
    · exact absurd (exec_mstore_normal funs h2
        (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 32) hh)
        (fun s₁ s₂ hh => trExprLit_ne_halts hh)) hne2
  · exact absurd (exec_mstore_normal funs h1
      (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 0) hh)
      (fun s₁ s₂ hh => trExprLit_ne_halts hh)) hne1

theorem eval_staticcall_lit_frame (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g))
    {st st1 : EvmState} {pv a : U256} (n : Nat) (hp : VEnv.get V "p" = some pv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.staticcall
        [Expr.lit (Literal.number n), Expr.lit (Literal.number 5), Expr.var "p",
         Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)])
      (.vals [a] st1)) :
    ∃ resp, c.Call ⟨.staticcall, BitVec.ofNat 256 n, 5, 0,
        readBytes st.memory pv.toNat 192⟩ st resp ∧
      a = resp.flag ∧
      st1 = finishCall .staticcall st resp pv.toNat 192 pv.toNat 32 := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest1 hhead1 =>
        cases hrest1 with
        | argsCons hrest2 hhead2 =>
          cases hrest2 with
          | argsCons hrest3 hhead3 =>
            cases hrest3 with
            | argsCons hrest4 hhead4 =>
              cases hrest4 with
              | argsCons hrest5 hhead5 =>
                cases hrest5 with
                | argsCons hrest6 hhead6 =>
                  cases hrest6 with
                  | argsNil =>
                    obtain ⟨hv6, hs6⟩ := eval_lit_eq funs V (st := st) 32 hhead6
                    obtain ⟨hv5, hs5⟩ := eval_var_eq funs V "p" pv hp hhead5
                    obtain ⟨hv4, hs4⟩ := eval_lit_eq funs V (st := _) 192 hhead4
                    obtain ⟨hv3, hs3⟩ := eval_var_eq funs V "p" pv hp hhead3
                    obtain ⟨hv2, hs2⟩ := eval_lit_eq funs V (st := _) 5 hhead2
                    obtain ⟨hv1, hs1⟩ := eval_lit_eq funs V (st := _) n hhead1
                    rw [hs1, hs2, hs3, hs4, hs5, hs6] at hbi
                    rw [hv1, hv2, hv3, hv4, hv5, hv6] at hbi
                    simp [Bridge.Dialect, builtinWithExternal, externalCall] at hbi
                    rcases hbi with ⟨resp, hcall, hok⟩
                    exact ⟨resp, hcall, hok.1, hok.2⟩

theorem eval_iszero_staticcall_lit_frame (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g))
    {st st1 : EvmState} {pv cv : U256} (n : Nat) (hp : VEnv.get V "p" = some pv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.staticcall
          [Expr.lit (Literal.number n), Expr.lit (Literal.number 5), Expr.var "p",
           Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
      (.vals [cv] st1)) :
    ∃ resp, c.Call ⟨.staticcall, BitVec.ofNat 256 n, 5, 0,
        readBytes st.memory pv.toNat 192⟩ st resp ∧
      cv = b2w (resp.flag = 0) ∧
      st1 = finishCall .staticcall st resp pv.toNat 192 pv.toNat 32 := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              obtain ⟨resp, hcall, hflag, hst⟩ := eval_staticcall_lit_frame funs V n hp hhead
              rw [hst] at hbi
              simp [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
              refine ⟨resp, hcall, ?_, hbi.2.symm⟩
              rw [← hbi.1, hflag]
              rfl

theorem expr_staticcall_lit_frame_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.staticcall
        [Expr.lit (Literal.number n), Expr.lit (Literal.number 5), Expr.var "p",
         Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)])
      (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest1 hhead1 =>
        cases hrest1 with
        | argsCons hrest2 hhead2 =>
          cases hrest2 with
          | argsCons hrest3 hhead3 =>
            cases hrest3 with
            | argsCons hrest4 hhead4 =>
              cases hrest4 with
              | argsCons hrest5 hhead5 =>
                cases hrest5 with
                | argsCons hrest6 hhead6 =>
                  cases hrest6 with
                  | argsNil =>
                    simp [Bridge.Dialect, builtinWithExternal, externalCall] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h =>
        cases h with
        | argsRestHalt h' =>
          cases h' with
          | argsRestHalt h'' =>
            cases h'' with
            | argsRestHalt h3 =>
              cases h3 with
              | argsRestHalt h4 =>
                cases h4 with
                | argsRestHalt h5 => cases h5
                | argsHeadHalt _ hh => exact trExprLit_ne_halts hh
              | argsHeadHalt _ hh => exact trExprVar_ne_halts hh
            | argsHeadHalt _ hh => exact trExprLit_ne_halts hh
          | argsHeadHalt _ hh => exact trExprVar_ne_halts hh
        | argsHeadHalt _ hh => exact trExprLit_ne_halts hh
      | argsHeadHalt _ h' => exact trExprLit_ne_halts h'

theorem expr_iszero_staticcall_lit_frame_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.staticcall
          [Expr.lit (Literal.number n), Expr.lit (Literal.number 5), Expr.var "p",
           Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
      (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              simp [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h' => exact expr_staticcall_lit_frame_ne_halts funs V n h'

theorem staticcallGuard_lit_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (n : Nat) (xv pv : U256) (sel : Nat)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.staticcall
            [Expr.lit (Literal.number n), Expr.lit (Literal.number 5), Expr.var "p",
             Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])])
      (fun V st => VEnv.get V "p" = some pv ∧ VEnv.get V "x" = some xv ∧
        0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR ∧
        readBytes st.memory pv.toNat 192 = (modexpInvFrame xv.toNat).data.toList)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = V ∧
          ∃ resp, resp.success = true ∧
            (permissive (callsOf product)).Call
              ⟨.staticcall, BitVec.ofNat 256 n, 5, 0, readBytes st.memory pv.toNat 192⟩ st resp ∧
            st' = finishCall .staticcall st resp pv.toNat 192 pv.toNat 32 ∧
            resp.returndata =
              (bytesNatBE ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val 32).data.toList ∧
            loadWord st'.memory pv.toNat =
              BitVec.ofNat 256 ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtContractAll.cond ?_ ?_
  · intro V st cv st₁ hpre heval
    obtain ⟨hp, hx, hx0, hxlt, hframe⟩ := hpre
    obtain ⟨resp, hcall, hcv, hst⟩ := eval_iszero_staticcall_lit_frame funs V n hp heval
    constructor
    · intro hzero
      by_cases hs : resp.success = true
      · have hc : (callsOf product).Call
            ⟨.staticcall, BitVec.ofNat 256 n, 5, 0, readBytes st.memory pv.toNat 192⟩ st resp := by
          have h := hcall
          rw [permissive] at h
          exact h.2 hs
        have hbytes : ByteArray.mk (readBytes st.memory pv.toNat 192).toArray =
            ByteArray.mk (readBytes (mxMem st.memory pv.toNat xv) pv.toNat 192).toArray := by
          congr 1
          rw [hframe, mxMem_frame]
        have hout := mxMem_modexpOutput st.memory pv.toNat xv hx0 hxlt
        rw [← hbytes] at hout
        have hvalid := modexpValidInput_of_output_some hout
        have hret := callsOf_modexp_returndata (product := product)
          (req := ⟨.staticcall, BitVec.ofNat 256 n, 5, 0, readBytes st.memory pv.toNat 192⟩)
          (st := st) (resp := resp)
          (out := bytesNatBE ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val 32)
          rfl hvalid hout hc hs
        refine Or.inl ⟨rfl, rfl, resp, hs, hcall, hst, hret, ?_⟩
        rw [hst]
        show loadWord (copyReturn st.memory pv.toNat 32 resp.returndata) pv.toNat = _
        rw [hret]
        have hv256 : ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val < 2 ^ 256 := by
          have h := ZMod.val_lt (a := ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹))
          have hR : Midfall.Yul.blsR < 2 ^ 256 := by norm_num [Midfall.Yul.blsR]
          omega
        exact loadWord_copyReturn_bytesNatBE st.memory pv.toNat _ hv256
      · have hflag : resp.flag = 0 := by simp [CallResponse.flag, hs]
        have h1 : b2w (resp.flag = 0) = 1 := by rw [hflag]; rfl
        have : (1 : U256) = 0 := by
          rw [h1] at hcv
          rw [hcv] at hzero
          exact hzero
        exact absurd this (by decide)
    · intro hnz V' st' o hbody
      cases hbody with
      | block hb =>
          have hfail' : lookupFun (hoist (Bridge.Dialect (permissive (callsOf product)) g)
              [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])] :: funs)
              "fail" = some (failFDecl, cenv) := hfail
          rcases Step.stmts_cons_inv
            (D := Bridge.Dialect (permissive (callsOf product)) g) hb with
              ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
          · exact absurd (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1).1
              (by decide)
          · exact Or.inr (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1)
  · intro V st st₁ hpre heval
    exact absurd heval (expr_iszero_staticcall_lit_frame_ne_halts funs V n)

theorem returndatasizeGuard_lit_contract {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) {cenv : FunEnv (Bridge.Dialect c g)}
    (pv invW : U256) (sel : Nat)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.eq
            [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])])
      (fun V st => st.returndata.length = 32 ∧
        loadWord st.memory pv.toNat = invW)
      (fun V st V' st' o =>
        (o = .normal ∧ st'.returndata.length = 32 ∧
          loadWord st'.memory pv.toNat = invW ∧ V' = V ∧ st' = st)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtContractAll.cond ?_ ?_
  · intro V st cv st₁ hpre heval
    obtain ⟨hlen, hload⟩ := hpre
    obtain ⟨hcv, hst⟩ := eval_iszero_eq_returndatasize funs V heval
    constructor
    · intro hzero
      refine Or.inl ⟨rfl, ?_, ?_, rfl, hst⟩
      · rw [hst]; exact hlen
      · rw [hst]; exact hload
    · intro hnz V' st' o hbody
      cases hbody with
      | block hb =>
          have hfail' : lookupFun (hoist (Bridge.Dialect c g)
              [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number sel)])] :: funs)
              "fail" = some (failFDecl, cenv) := hfail
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
              ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
          · exact absurd (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1).1
              (by decide)
          · exact Or.inr (fail_call_any_reverts (fun _ _ hh => trExprLit_ne_halts hh) hfail' h1)
  · intro V st st₁ hpre heval
    exact absurd heval (expr_iszero_eq_returndatasize_ne_halts funs V)

theorem guardsLit_contract {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) {cenv : FunEnv (Bridge.Dialect c g)}
    (scratch n selN : Nat) (xv : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.lt [Expr.var "x", Expr.lit (Literal.number n)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selN)])],
        Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "x"])
          [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selN)])],
        Stmt.letDecl ["p"] (some (Expr.lit (Literal.number scratch))) ]
      (fun V _ => VEnv.get V "x" = some xv ∧ (VEnv.get V "inv").isSome)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = ("p", sv scratch) :: V ∧
          VEnv.get V' "p" = some (sv scratch) ∧
          VEnv.get V' "x" = some xv ∧ (VEnv.get V' "inv").isSome ∧
          st'.memory = st.memory)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hx, hinv⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne⟩
  · have g1 := guardLt_lit_contract (funs := funs) (cenv := cenv) n xv selN hfail
      V st hx V1 st1 .normal h1
    rcases g1 with ⟨ho1, hV1, hm1, _⟩ | ⟨ho1, hrev1⟩
    · subst V1
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
          ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
      · have g2 := guardNonzero_lit_contract (funs := funs) (cenv := cenv) xv selN hfail
          V st1 hx V2 st2 .normal h2
        rcases g2 with ⟨ho2, hV2, hm2, _⟩ | ⟨ho2, hrev2⟩
        · subst V2
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
              ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
          · cases h3 with
            | letVal he hlen =>
                cases he with
                | lit =>
                    cases hrest3
                    refine Or.inl ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
                    · simp only [List.zip_cons_cons, List.zip_nil_left, List.cons_append,
                        List.nil_append]
                      rfl
                    · change VEnv.get (("p", (Bridge.Dialect c g).litValue
                          (Literal.number scratch)) :: V) "p" = some (sv scratch)
                      exact venv_get_cons_self (D := Bridge.Dialect c g) _ _ _
                    · change VEnv.get (("p", (Bridge.Dialect c g).litValue
                          (Literal.number scratch)) :: V) "x" = some xv
                      exact (venv_get_cons_ne (D := Bridge.Dialect c g) (x := "p") (y := "x")
                        (by decide)).trans hx
                    · change (VEnv.get (("p", (Bridge.Dialect c g).litValue
                          (Literal.number scratch)) :: V) "inv").isSome
                      simpa [VEnv.get, List.find?,
                        show decide (("p" : String) = "inv") = false by decide] using hinv
                    · exact hm2.trans hm1
          · cases h3 with
            | letVal he hlen => exact absurd rfl hne3
            | letHalt he => cases he
        · exact absurd ho2 (by decide)
      · have g2 := guardNonzero_lit_contract (funs := funs) (cenv := cenv) xv selN hfail
          V st1 hx V' st' o h2
        rcases g2 with ⟨ho2, _⟩ | ⟨ho2, hrev2⟩
        · exact absurd ho2 hne2
        · exact Or.inr ⟨ho2, hrev2⟩
    · exact absurd ho1 (by decide)
  · have g1 := guardLt_lit_contract (funs := funs) (cenv := cenv) n xv selN hfail
      V st hx V' st' o h1
    rcases g1 with ⟨ho1, _⟩ | ⟨ho1, hrev1⟩
    · exact absurd ho1 hne
    · exact Or.inr ⟨ho1, hrev1⟩

theorem storesLit_contract {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (scratch n : Nat) (xv : U256)
    (hn : BitVec.ofNat 256 n = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.lit (Literal.number n))
        Midfall.Generator.templateConstantsDefault)
      (fun V _ => VEnv.get V "p" = some (sv scratch) ∧ VEnv.get V "x" = some xv ∧
        (VEnv.get V "inv").isSome)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = V ∧ VEnv.get V' "p" = some (sv scratch) ∧
          VEnv.get V' "x" = some xv ∧ (VEnv.get V' "inv").isSome ∧
          SIFrame scratch xv st' ∧
          st'.memory = mxMem st.memory (sv scratch).toNat xv)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hx, hinv⟩ := hpre
  have h := modexpFrameStores_lit_contract (funs := funs) (pv := sv scratch) xv n hscratch
    V st ⟨hp, hx⟩ V' st' o hrun
  rcases h with ⟨ho, hV, hmem, henv, hhalt⟩
  refine Or.inl ⟨ho, hV, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV]; exact hp
  · rw [hV]; exact hx
  · rw [hV]; exact hinv
  · unfold SIFrame
    rw [hmem, hn, mxMemFr_blsR]
    exact mxMem_frame st.memory (sv scratch).toNat xv
  · rw [hmem, hn, mxMemFr_blsR]

theorem invAssign_lit_contract {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (sv invW : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.assign ["inv"] (Expr.builtin EVM.Op.mload [Expr.var "p"]))
      (fun V st => VEnv.get V "p" = some sv ∧ loadWord st.memory sv.toNat = invW ∧
        (VEnv.get V "inv").isSome)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = VEnv.set V "inv" invW ∧
          VEnv.get V' "inv" = some invW ∧
          st'.memory = st.memory ∧ st'.halted = st.halted)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hload, hinv⟩ := hpre
  cases hrun with
  | assignVal he hlen =>
      obtain ⟨a, hvs, ha, hst⟩ := eval_mload_var_vals funs V "p" sv hp he
      subst hvs
      refine Or.inl ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
          List.foldl_nil]
        rw [ha, hload]
      · rw [ha, hload]
        cases hv : VEnv.get V "inv" with
        | none => simp [hv] at hinv
        | some inv0 =>
            simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
              List.foldl_nil]
            exact venv_get_set_same (D := Bridge.Dialect c g) hv
      · rw [hst]; rfl
      · rw [hst]; rfl
  | assignHalt he => exact absurd he (expr_mload_var_ne_halts funs V "p")


/-- Memory agrees outside the window `[lo, lo + len)`. -/
def MemSameOutside (st st' : EvmState) (lo len : Nat) : Prop :=
  ∀ a, (a < lo ∨ lo + len ≤ a) → st'.memory a = st.memory a

/-- A returned byte range outside `dst..dst+size` is untouched by `copyReturn`. -/
theorem copyReturn_outside (mem : Nat → UInt8) (dst size : Nat) (bytes : List UInt8)
    (a : Nat) (h : a < dst ∨ dst + size ≤ a) :
    copyReturn mem dst size bytes a = mem a := by
  unfold copyReturn
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have hmin : min size bytes.length ≤ size := Nat.min_le_left _ _
  omega

/-- `finishCall` leaves memory outside the output window unchanged. -/
theorem finishCall_memory_outside {kind : EVM.CallKind} {st : EvmState} {resp : CallResponse}
    (io is oo os a : Nat) (h : a < oo ∨ oo + os ≤ a) :
    (finishCall kind st resp io is oo os).memory a = st.memory a := by
  unfold finishCall
  dsimp
  exact copyReturn_outside st.memory oo os resp.returndata a h

theorem readBackLit_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch gasN selN selP : Nat) (xv : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      [ Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.staticcall
            [Expr.lit (Literal.number gasN), Expr.lit (Literal.number 5), Expr.var "p",
             Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selP)])],
        Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.eq
            [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
          [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selP)])],
        Stmt.assign ["inv"] (Expr.builtin EVM.Op.mload [Expr.var "p"]) ]
      (fun V st => VEnv.get V "p" = some (sv scratch) ∧ VEnv.get V "x" = some xv ∧
        (VEnv.get V "inv").isSome ∧
        0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR ∧ SIFrame scratch xv st)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = VEnv.set V "inv" (SIInv xv) ∧
          VEnv.get V' "inv" = some (SIInv xv) ∧
          (∀ a, a < (sv scratch).toNat ∨ (sv scratch).toNat + 192 ≤ a →
            st'.memory a = st.memory a))
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hx, hinv, hx0, hxR, hframe⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
      ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne⟩
  · have sc := staticcallGuard_lit_contract (product := product) (funs := funs) (cenv := cenv)
      gasN xv (sv scratch) selP hfail V st ⟨hp, hx, hx0, hxR, hframe⟩ V1 st1 .normal h1
    rcases sc with ⟨ho1, hV1, resp, hsucc, hcall, hst, hret, hload⟩ | ⟨ho1, hrev1⟩
    · subst V1
      rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest1 with
          ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
      · have hlen : st1.returndata.length = 32 := by
          rw [hst]
          show resp.returndata.length = 32
          rw [hret, Array.length_toList, ByteArray.size_data]
          exact Midfall.Assumptions.bytesNatBE_size _ 32
        have rds := returndatasizeGuard_lit_contract (funs := funs) (cenv := cenv)
          (sv scratch) (SIInv xv) selP hfail V st1 ⟨hlen, hload⟩ V2 st2 .normal h2
        rcases rds with ⟨ho2, hlen2, hload2, hV2, hst2⟩ | ⟨ho2, hrev2⟩
        · subst V2
          rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest2 with
              ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
          · have asg := invAssign_lit_contract (funs := funs) (sv scratch) (SIInv xv)
              V st2 ⟨hp, hload2, hinv⟩ V3 st3 .normal h3
            rcases asg with ⟨ho3, hV3, hget3, hm3, _hh⟩ | ⟨ho3, hrev3⟩
            · cases hrest3
              refine Or.inl ⟨ho3, hV3, hget3, ?_⟩
              intro a ha
              rw [hm3, hst2, hst]
              exact finishCall_memory_outside _ _ _ _ _
                (by omega : a < (sv scratch).toNat ∨ (sv scratch).toNat + 32 ≤ a)
            · cases hrest3
              exact Or.inr ⟨ho3, hrev3⟩
          · cases h3 with
            | assignVal he hlen' => exact absurd rfl hne3
            | assignHalt he => exact absurd he (expr_mload_var_ne_halts funs V "p")
        · exact absurd ho2 (by decide)
      · have rds := returndatasizeGuard_lit_contract (funs := funs) (cenv := cenv)
          (sv scratch) (SIInv xv) selP hfail V st1 ⟨by
            rw [hst]
            show resp.returndata.length = 32
            rw [hret, Array.length_toList, ByteArray.size_data]
            exact Midfall.Assumptions.bytesNatBE_size _ 32, hload⟩ V' st' o h2
        rcases rds with ⟨ho2, _⟩ | ⟨ho2, hrev2⟩
        · exact absurd ho2 hne2
        · exact Or.inr ⟨ho2, hrev2⟩
    · exact absurd ho1 (by decide)
  · have sc := staticcallGuard_lit_contract (product := product) (funs := funs) (cenv := cenv)
      gasN xv (sv scratch) selP hfail V st ⟨hp, hx, hx0, hxR, hframe⟩ V' st' o h1
    rcases sc with ⟨ho1, _⟩ | ⟨ho1, hrev1⟩
    · exact absurd ho1 hne
    · exact Or.inr ⟨ho1, hrev1⟩

/-- **THE INLINED `scalar_inv` BODY.** `GenAst.emitScalarInvAt`'s body after
    `Inline.inlineContractConstants`: the four free constants (`FR_MODULUS`, `MODEXP_GAS`, and the
    two error selectors) are literals. The call rule runs a helper under
    `(params.zip args) ++ bindZeros rets` only, so the function-call summary must use this form:
    the pre-inline body's `Expr.var` sites would be unbound in that environment. -/
def scalarBodyLit (scratch n gasN selN selP : Nat) : Block EVM.Op :=
  ([ Stmt.cond (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.lt [Expr.var "x", Expr.lit (Literal.number n)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selN)])],
      Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "x"])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selN)])],
      Stmt.letDecl ["p"] (some (Expr.lit (Literal.number scratch))) ] ++
    GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.lit (Literal.number n))
      Midfall.Generator.templateConstantsDefault) ++
  [ Stmt.cond (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.staticcall
          [Expr.lit (Literal.number gasN), Expr.lit (Literal.number 5), Expr.var "p",
           Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selP)])],
    Stmt.cond (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.eq
          [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (Literal.number selP)])],
    Stmt.assign ["inv"] (Expr.builtin EVM.Op.mload [Expr.var "p"]) ]

theorem bodyLit_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch n gasN selN selP : Nat) (xv : U256)
    (hn : BitVec.ofNat 256 n = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (scalarBodyLit scratch n gasN selN selP)
      (fun V _ => VEnv.get V "x" = some xv ∧ (VEnv.get V "inv").isSome ∧
        0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = VEnv.set (("p", sv scratch) :: V) "inv" (SIInv xv) ∧
          VEnv.get V' "inv" = some (SIInv xv) ∧
          MemSameOutside st st' scratch 192)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hx, hinv, hx0, hxR⟩ := hpre
  unfold scalarBodyLit at hrun
  rw [List.append_assoc] at hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
      ⟨V1, st1, hg, hrest⟩ | ⟨hg, hne⟩
  · have g := guardsLit_contract (funs := funs) (cenv := cenv) scratch n selN xv hfail
      V st ⟨hx, hinv⟩ V1 st1 .normal hg
    rcases g with ⟨ho1, hV1, hp1, hx1, hinv1, hm1⟩ | ⟨ho1, hrev1⟩
    · rcases Step.stmts_append_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest with
          ⟨V2, st2, hs, hr⟩ | ⟨hs, hne2⟩
      · have s := storesLit_contract (funs := funs) scratch n xv hn hscratch
          V1 st1 ⟨hp1, hx1, hinv1⟩ V2 st2 .normal hs
        rcases s with ⟨ho2, hV2, hp2, hx2, hinv2, hframe, hm2⟩ | ⟨ho2, hrev2⟩
        · have r := readBackLit_contract (product := product) (funs := funs) (cenv := cenv)
            scratch gasN selN selP xv hfail
            V2 st2 ⟨hp2, hx2, hinv2, hx0, hxR, hframe⟩ V' st' o hr
          rcases r with ⟨ho3, hV3, hget3, hfr⟩ | ⟨ho3, hrev3⟩
          · refine Or.inl ⟨ho3, ?_, hget3, ?_⟩
            · rw [hV3, hV2, hV1]
            · have hpv : (sv scratch).toNat = scratch := by
                show (BitVec.ofNat 256 scratch).toNat = scratch
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hscratch256]
              intro a ha
              have ha' : a < (sv scratch).toNat ∨ (sv scratch).toNat + 192 ≤ a := by
                rw [hpv]; exact ha
              rw [hfr a ha', hm2,
                mxMem_outside st1.memory (sv scratch).toNat xv a (by rw [hpv]; exact ha), hm1]
          · exact Or.inr ⟨ho3, hrev3⟩
        · exact absurd ho2 (by decide)
      · have s := storesLit_contract (funs := funs) scratch n xv hn hscratch
          V1 st1 ⟨hp1, hx1, hinv1⟩ V' st' o hs
        rcases s with ⟨ho2, _⟩ | ⟨ho2, hrev2⟩
        · exact absurd ho2 hne2
        · exact Or.inr ⟨ho2, hrev2⟩
    · exact absurd ho1 (by decide)
  · have g := guardsLit_contract (funs := funs) (cenv := cenv) scratch n selN xv hfail
      V st ⟨hx, hinv⟩ V' st' o hg
    rcases g with ⟨ho1, _⟩ | ⟨ho1, hrev1⟩
    · exact absurd ho1 hne
    · exact Or.inr ⟨ho1, hrev1⟩

/-- **THE `scalar_inv` CALL SUMMARY.** Every `Step.callOk`/`callHalt` run of
    `scalar_inv(x)` under a declaration whose body is the inlined `scalarBodyLit` either returns
    the single word `ofNat ((x^{-1} mod blsR).val)` or ends in a revert. The call rule supplies
    the `x` parameter and the zeroed `inv` ret slot; `hcalleePre` shows the body pre holds in that
    environment. -/
theorem scalarInv_call_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch n gasN selN selP : Nat) (xv : U256)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch n gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hn : BitVec.ofNat 256 n = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv')) :
    ∀ (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g)) (st : EvmState)
      (r : EResult (Bridge.Dialect (permissive (callsOf product)) g)),
      VEnv.get V "x" = some xv →
      0 < xv.toNat → xv.toNat < Midfall.Yul.blsR →
      EvalExpr (Bridge.Dialect (permissive (callsOf product)) g) funs V st
        (Expr.call "scalar_inv" [Expr.var "x"]) r →
      (∃ st', r = .vals [SIInv xv] st') ∨
        (∃ st', r = .halt st' ∧ Midfall.LoweringV2.Reverted st') := by
  intro V st r hx hx0 hxR he
  have hbodyC := bodyLit_contract (product := product) (funs := cenv) (cenv := cenv')
    scratch n gasN selN selP xv hn hscratch hscratch256 hfail
  -- the body pre on the callee env for the argument value
  have hcalleePre : ∀ v : U256, v = xv →
      (fun (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g)) _ =>
        VEnv.get V "x" = some xv ∧ (VEnv.get V "inv").isSome ∧
        0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR)
      ((["x"].zip [v]) ++ bindZeros (Bridge.Dialect (permissive (callsOf product)) g) ["inv"]) st := by
    intro v hv
    rw [hv]
    refine ⟨?_, ?_, hx0, hxR⟩
    · simp [VEnv.get, List.find?]
    · simp [bindZeros, VEnv.get, List.find?]
  cases he with
  | callOk hargs hlook' hlen hbodyrun ho =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              cases hhead with
              | var hget =>
                  have hxv : _ = xv := Option.some.inj (hget.symm.trans hx)
                  rw [hlook] at hlook'
                  cases hlook'
                  rw [hparams] at hlen
                  rw [hparams, hrets, hbody] at hbodyrun
                  rw [hrets]
                  cases hbodyrun with
                  | block hstmts =>
                      have hfail' : lookupFun (hoist (Bridge.Dialect (permissive (callsOf product)) g)
                          (scalarBodyLit scratch n gasN selN selP) :: cenv) "fail" =
                          some (failFDecl, cenv') := by
                        have hh : hoist (Bridge.Dialect (permissive (callsOf product)) g)
                            (scalarBodyLit scratch n gasN selN selP) = [] := rfl
                        rw [hh]
                        simpa [lookupFun] using hfail
                      have hbodyC' := bodyLit_contract (product := product)
                        (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
                          (scalarBodyLit scratch n gasN selN selP) :: cenv) (cenv := cenv')
                        scratch n gasN selN selP xv hn hscratch hscratch256 hfail'
                      have hpost := hbodyC' _ _ (hcalleePre _ hxv) _ _ _ hstmts
                      rcases hpost with ⟨hon, hVb, hget⟩ | ⟨hoh, hrev⟩
                      · exact Or.inl ⟨_, by
                          rw [hVb]
                          simp [VEnv.set, restore, VEnv.get, List.find?, bindZeros]
                          rfl⟩
                      · rcases ho with hn | hl
                        · cases hn; cases hoh
                        · cases hl; cases hoh
  | callHalt hargs hlook' hlen hbodyrun =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              cases hhead with
              | var hget =>
                  have hxv : _ = xv := Option.some.inj (hget.symm.trans hx)
                  rw [hlook] at hlook'
                  cases hlook'
                  rw [hparams] at hlen
                  rw [hparams, hrets, hbody] at hbodyrun
                  cases hbodyrun with
                  | block hstmts =>
                      have hfail' : lookupFun (hoist (Bridge.Dialect (permissive (callsOf product)) g)
                          (scalarBodyLit scratch n gasN selN selP) :: cenv) "fail" =
                          some (failFDecl, cenv') := by
                        have hh : hoist (Bridge.Dialect (permissive (callsOf product)) g)
                            (scalarBodyLit scratch n gasN selN selP) = [] := rfl
                        rw [hh]
                        simpa [lookupFun] using hfail
                      have hbodyC' := bodyLit_contract (product := product)
                        (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
                          (scalarBodyLit scratch n gasN selN selP) :: cenv) (cenv := cenv')
                        scratch n gasN selN selP xv hn hscratch hscratch256 hfail'
                      have hpost := hbodyC' _ _ (hcalleePre _ hxv) _ _ _ hstmts
                      simp only [SIPost] at hpost
                      rcases hpost with ⟨hon, hinv⟩ | ⟨hoh, hrev⟩
                      · exact absurd hon (by decide)
                      · exact Or.inr ⟨_, rfl, hrev⟩
  | callArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h' => cases h' 

example (scratch n gasN selN selP : Nat) :
    hoist (Bridge.Dialect c g) (scalarBodyLit scratch n gasN selN selP) = [] := by
  rfl



#assert_axioms Midfall.LoweringV3.ScalarInvSummary.fail_expr_any
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.fail_call_any_reverts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.eval_iszero_lt_var_lit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_lt_var_lit_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_iszero_lt_var_lit_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.guardLt_lit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.guardNonzero_lit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.eval_sub_lit_lit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_sub_lit_lit_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.modexpFrameStores_lit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.eval_staticcall_lit_frame
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.eval_iszero_staticcall_lit_frame
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_staticcall_lit_frame_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_iszero_staticcall_lit_frame_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.staticcallGuard_lit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.returndatasizeGuard_lit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.invAssign_lit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.readBackLit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.bodyLit_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.scalarInv_call_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.eval_iszero_eq_returndatasize
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_returndatasize_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_eq_returndatasize_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_iszero_eq_returndatasize_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.eval_mload_var_vals
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.expr_mload_var_ne_halts
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.returndatasizeGuard_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.invAssign_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.guards_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.stores_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.readBack_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.guardsStores_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.scalarBodyLit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.scalarBody_eq
  [propext] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.emitScalarInvAt_body_contract
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.ScalarInvSummary

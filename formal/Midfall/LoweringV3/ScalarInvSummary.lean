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
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.scalarBody_eq
  [propext] native []
#assert_axioms Midfall.LoweringV3.ScalarInvSummary.emitScalarInvAt_body_contract
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.ScalarInvSummary

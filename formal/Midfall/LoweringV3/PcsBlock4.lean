import Midfall.LoweringV3.PcsRows
import Midfall.LoweringV3.ScalarInvSummary
set_option autoImplicit false
namespace Midfall.LoweringV3.PcsBlock4
open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.Lowering.Stage
open Midfall.LoweringV3.PcsRows Midfall.Lowering.GenAstPcs
open Midfall.LoweringV3.ScalarInvSummary Midfall.LoweringV2 Midfall.LoweringV2.Blocks.TraceReturn
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
variable {c : ExternalCalls} {g : ExternalGas} {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem scalarInv_call_contract_var {g : ExternalGas} (product : PairingProduct)
    (arg : String)
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
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv')) :
    ∀ (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g)) (st : EvmState)
      (r : EResult (Bridge.Dialect (permissive (callsOf product)) g)),
      VEnv.get V arg = some xv →
      0 < xv.toNat → xv.toNat < Midfall.Yul.blsR →
      EvalExpr (Bridge.Dialect (permissive (callsOf product)) g) funs V st
        (Expr.call "scalar_inv" [Expr.var arg]) r →
      (∃ st', r = .vals [SIInv xv] st') ∨
        (∃ st', r = .halt st' ∧ Midfall.LoweringV2.Reverted st') := by
  intro V st r harg hx0 hxR he
  have hbodyC := bodyLit_contract (product := product) (funs := cenv) (cenv := cenv')
    scratch n gasN selN selP xv hn hscratch hfail
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
                  have hxv : _ = xv := Option.some.inj (hget.symm.trans harg)
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
                        scratch n gasN selN selP xv hn hscratch hfail'
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
                  have hxv : _ = xv := Option.some.inj (hget.symm.trans harg)
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
                        scratch n gasN selN selP xv hn hscratch hfail'
                      have hpost := hbodyC' _ _ (hcalleePre _ hxv) _ _ _ hstmts
                      simp only [SIPost] at hpost
                      rcases hpost with ⟨hon, hinv⟩ | ⟨hoh, hrev⟩
                      · exact absurd hon (by decide)
                      · exact Or.inr ⟨_, rfl, hrev⟩
  | callArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h' => cases h'

theorem b3_exec_ylet_scalar_inv_var {g : ExternalGas} (product : PairingProduct)
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
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv')) :
    ∀ (arg x : String) (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g))
      (st : EvmState) (V' : VEnv (Bridge.Dialect (permissive (callsOf product)) g))
      (st' : EvmState) (o : Outcome),
      VEnv.get V arg = some xv →
      0 < xv.toNat → xv.toNat < Midfall.Yul.blsR →
      ExecStmt (Bridge.Dialect (permissive (callsOf product)) g) funs V st
        (GenAst.ylet x (GenAst.ycall "scalar_inv" [GenAst.yvar arg])) V' st' o →
      (o = .normal ∧ V' = (x, SIInv xv) :: V) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st') := by
  intro arg x V st V' st' o harg hx0 hxR hrun
  cases hrun with
  | letVal he hlen =>
      have hc := scalarInv_call_contract_var (product := product) (arg := arg)
        (funs := funs) (decl := decl) (cenv := cenv) (cenv' := cenv')
        scratch n gasN selN selP xv hlook hbody hparams hrets hn hscratch hfail
        V st _ harg hx0 hxR he
      rcases hc with ⟨st1, hev⟩ | ⟨st1, heh, hrev⟩
      · injection hev with hvals hst
        rw [hvals]
        simp [VEnv.setMany]
      · exact absurd heh (by simp)
  | letHalt he =>
      have hc := scalarInv_call_contract_var (product := product) (arg := arg)
        (funs := funs) (decl := decl) (cenv := cenv) (cenv' := cenv')
        scratch n gasN selN selP xv hlook hbody hparams hrets hn hscratch hfail
        V st _ harg hx0 hxR he
      rcases hc with ⟨st1, hev⟩ | ⟨st1, heh, hrev⟩
      · exact absurd hev (by simp)
      · injection heh with hst
        subst hst
        exact Or.inr ⟨rfl, hrev⟩

theorem b1_eval_sub_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y : String}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.sub [GenAst.yvar x, GenAst.yvar y]) (.vals [cv] st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      cv = xv - yv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hy =>
      cases hrest with
      | argsCons hnil hx =>
          cases hnil with
          | argsNil =>
              obtain ⟨hxv, hstx⟩ := b1_eval_var_inv hy
              obtain ⟨hyv, hsty⟩ := b1_eval_var_inv hx
              rw [hstx, hsty] at hbi
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, hxv, hyv, rfl, rfl⟩

theorem b1_eval_addmod_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y z : String}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.addmod [GenAst.yvar x, GenAst.yvar y, GenAst.yvar z])
      (.vals [cv] st')) :
    ∃ xv yv zv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      VEnv.get V z = some zv ∧ cv = wAddmodAt xv yv zv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hrest with
      | argsCons hrest2 hy =>
          cases hrest2 with
          | argsCons hnil hz =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hxv, hstx⟩ := b1_eval_var_inv hx
                  obtain ⟨hyv, hsty⟩ := b1_eval_var_inv hy
                  obtain ⟨hzv, hstz⟩ := b1_eval_var_inv hz
                  rw [hstx, hsty, hstz] at hbi
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨_, _, _, hxv, hyv, hzv, rfl, rfl⟩

theorem b1_eval_sub_from_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y : String}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (subFrom (GenAst.yvar x) (GenAst.yvar y)) (.vals [cv] st')) :
    ∃ xv yv rv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      VEnv.get V "r" = some rv ∧ cv = wAddmodAt xv (rv - yv) rv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hrest with
      | argsCons hrest2 hsub =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨xraw, hxvRaw, hstx⟩ := b1_eval_var_vals hx
                  obtain ⟨rraw, hrvRaw, hstr⟩ := b1_eval_var_vals hr
                  obtain ⟨rsub, yv, hrvSub, hyv, hsubv, hstsub⟩ :=
                    b1_eval_sub_vars_inv hsub
                  have hrEq : rsub = rraw := Option.some.inj (hrvSub.symm.trans hrvRaw)
                  obtain ⟨hrvProj, _⟩ := b1_eval_var_inv hr
                  rw [hrvRaw] at hrvProj
                  cases hrvProj
                  obtain ⟨hxvProj, _⟩ := b1_eval_var_inv hx
                  rw [hxvRaw] at hxvProj
                  cases hxvProj
                  rw [hstx, hstsub, hstr] at hbi
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  refine ⟨_, _, _, hxvRaw, hyv, hrvRaw, ?_, rfl⟩
                  rw [← hrEq, hsubv]
                  rfl

theorem b1_eval_mload_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {p : String} {off : Nat}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mload
        [GenAst.yop EVM.Op.add [GenAst.yvar p, GenAst.ylit off]]) (.vals [cv] st')) :
    ∃ pv, VEnv.get V p = some pv ∧
      cv = loadWord st.memory (pv + BitVec.ofNat 256 off).toNat ∧
      st' = touchMemory st (pv + BitVec.ofNat 256 off).toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil harg =>
      cases hnil with
      | argsNil =>
          obtain ⟨pv, hpv, haddr, hst1⟩ := b1_eval_add_var_lit_inv harg
          rw [hst1] at hbi
          simp only [builtinWithExternal, stepOp] at hbi
          cases hbi
          exact ⟨pv, hpv, by rw [haddr], by rw [haddr]⟩

theorem b1_eval_calldataload_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {p : String} {off : Nat}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.calldataload
        [GenAst.yop EVM.Op.add [GenAst.yvar p, GenAst.ylit off]]) (.vals [cv] st')) :
    ∃ pv, VEnv.get V p = some pv ∧
      cv = wordFrom st.env.calldata (pv + BitVec.ofNat 256 off).toNat ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil harg =>
      cases hnil with
      | argsNil =>
          obtain ⟨pv, hpv, haddr, hst1⟩ := b1_eval_add_var_lit_inv harg
          rw [hst1] at hbi
          simp only [builtinWithExternal, stepOp] at hbi
          cases hbi
          exact ⟨pv, hpv, by rw [haddr], rfl⟩

theorem b1_eval_sub_var_mload_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q : String} {off : Nat}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.sub
        [GenAst.yvar "r",
         GenAst.yop EVM.Op.mload
           [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]]]) (.vals [cv] st')) :
    ∃ rv qv, VEnv.get V "r" = some rv ∧ VEnv.get V q = some qv ∧
      cv = rv - loadWord st.memory (qv + BitVec.ofNat 256 off).toNat ∧
      st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hr =>
      cases hrest with
      | argsCons hnil hmload =>
          cases hnil with
          | argsNil =>
              obtain ⟨qep, hqep, hmloadVal, hstm⟩ :=
                b1_eval_mload_add_var_lit_inv hmload
              obtain ⟨rv, hrv, hstr⟩ := b1_eval_var_vals hr
              obtain ⟨hrvProj, _⟩ := b1_eval_var_inv hr
              rw [hrv] at hrvProj
              cases hrvProj
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              rw [hmloadVal]
              refine ⟨_, qep, hrv, hqep, rfl, ?_, ?_, ?_⟩
              · rw [hstr, hstm, Midfall.Yul.Word.touchMemory_memory]
              · rw [hstr, hstm, Midfall.Yul.Word.touchMemory_env]
              · rw [hstr, hstm, Midfall.Yul.Word.touchMemory_halted]

theorem b1_eval_sub_from_cdl_mload_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {qc qe : String}
    {offc offe : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (subFrom
        (GenAst.yop EVM.Op.calldataload
          [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit offc]])
        (GenAst.yop EVM.Op.mload
          [GenAst.yop EVM.Op.add [GenAst.yvar qe, GenAst.ylit offe]]))
      (.vals [cv] st')) :
    ∃ cptr qep rv cdlv, VEnv.get V qc = some cptr ∧ VEnv.get V qe = some qep ∧
      VEnv.get V "r" = some rv ∧
      cdlv = wordFrom st.env.calldata (cptr + BitVec.ofNat 256 offc).toNat ∧
      cv = wAddmodAt cdlv
        (rv - loadWord st.memory (qep + BitVec.ofNat 256 offe).toNat) rv := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hcdl =>
      cases hrest with
      | argsCons hrest2 hsub =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨rv0, hrv0, hstr⟩ := b1_eval_var_vals hr
                  obtain ⟨rvSub, qep, hrvSub, hqep, hsubVal, hsubMem, hsubEnv, hsubHalt⟩ :=
                    b1_eval_sub_var_mload_add_var_lit_inv hsub
                  obtain ⟨cptr, hcptr, hcdlVal, hstc⟩ :=
                    b1_eval_calldataload_add_var_lit_inv hcdl
                  rw [hstr] at hsubVal hsubMem hsubEnv hsubHalt
                  rw [hsubEnv] at hcdlVal
                  have hrvEq : rvSub = rv0 := Option.some.inj (hrvSub.symm.trans hrv0)
                  obtain ⟨hrvProj, _⟩ := b1_eval_var_inv hr
                  rw [hrv0] at hrvProj
                  cases hrvProj
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  refine ⟨cptr, qep, _, _, hcptr, hqep, hrv0, rfl, ?_⟩
                  have hrvEq2 := Option.some.inj (hrvSub.symm.trans hrv0)
                  rw [hsubVal, hcdlVal, hrvEq2]
                  rfl

theorem b1_eval_mulmod_subfrom_cdl_mload_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {qc qe inv : String}
    {offc offe : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [subFrom
          (GenAst.yop EVM.Op.calldataload
            [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit offc]])
          (GenAst.yop EVM.Op.mload
            [GenAst.yop EVM.Op.add [GenAst.yvar qe, GenAst.ylit offe]]),
         GenAst.yvar inv, GenAst.yvar "r"]) (.vals [cv] st')) :
    ∃ cptr qep rv invv subv,
      VEnv.get V qc = some cptr ∧ VEnv.get V qe = some qep ∧
      VEnv.get V inv = some invv ∧ VEnv.get V "r" = some rv ∧
      subv = wAddmodAt
        (wordFrom st.env.calldata (cptr + BitVec.ofNat 256 offc).toNat)
        (rv - loadWord st.memory (qep + BitVec.ofNat 256 offe).toNat) rv ∧
      cv = wMulmodAt subv invv rv := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hsub =>
      cases hrest with
      | argsCons hrest2 hinv =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨rv0, hrv0, hstr⟩ := b1_eval_var_vals hr
                  obtain ⟨invv, hinvv, hstinv⟩ := b1_eval_var_vals hinv
                  obtain ⟨cptr, qep, rvS, cdlv, hcptr, hqep, hrvS, hcdl, hsubVal⟩ :=
                    b1_eval_sub_from_cdl_mload_inv hsub
                  rw [hstinv, hstr] at hsubVal hcdl
                  have hrvEq := Option.some.inj (hrvS.symm.trans hrv0)
                  obtain ⟨hinvProj, _⟩ := b1_eval_var_inv hinv
                  rw [hinvv] at hinvProj
                  cases hinvProj
                  obtain ⟨hrProj, _⟩ := b1_eval_var_inv hr
                  rw [hrv0] at hrProj
                  cases hrProj
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  refine ⟨cptr, qep, _, _, _, hcptr, hqep, hinvv, hrv0, ?_, rfl⟩
                  rw [hsubVal, hcdl, hrvEq]

theorem b1_eval_addmod_mulmod_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {f x2 ev : String}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.addmod
        [GenAst.yop EVM.Op.mulmod
           [GenAst.yvar f, GenAst.yvar x2, GenAst.yvar "r"],
         GenAst.yvar ev, GenAst.yvar "r"]) (.vals [cv] st')) :
    ∃ fv x2v evv rv, VEnv.get V f = some fv ∧ VEnv.get V x2 = some x2v ∧
      VEnv.get V ev = some evv ∧ VEnv.get V "r" = some rv ∧
      cv = wAddmodAt (wMulmodAt fv x2v rv) evv rv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hf =>
      cases hrest with
      | argsCons hrest2 hev =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨rv0, hrv0, hstr⟩ := b1_eval_var_vals hr
                  obtain ⟨evv, hevv, hstev⟩ := b1_eval_var_vals hev
                  obtain ⟨fv, x2v, rvS, hfv, hx2v, hrvS, hmul, hstmul⟩ :=
                    b1_eval_mulmod_vars_inv hf
                  have hrvEq := Option.some.inj (hrvS.symm.trans hrv0)
                  obtain ⟨hrProj, _⟩ := b1_eval_var_inv hr
                  rw [hrv0] at hrProj
                  cases hrProj
                  obtain ⟨hevProj, _⟩ := b1_eval_var_inv hev
                  rw [hevv] at hevProj
                  cases hevProj
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  refine ⟨fv, x2v, _, _, hfv, hx2v, hevv, hrv0, ?_, ?_⟩
                  · rw [hmul, hrvEq]
                    rfl
                  · rw [hstmul, hstev, hstr]

theorem b1_eval_mload_add_var_lit_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mload
        [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.mload)
    (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_mload hr)
    (fun _ _ hh => b1_eval_add_var_lit_halt hh) h

theorem b1_eval_calldataload_add_var_lit_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.calldataload
        [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := EVM.Op.calldataload)
    (fun _ _ _ hr => Midfall.LoweringV2.Blocks.VkLoading.vk_ok_calldataload hr)
    (fun _ _ hh => b1_eval_add_var_lit_halt hh) h

theorem b1_eval_sub_vars_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.sub [GenAst.yvar x, GenAst.yvar y]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.sub)
    (fun _ _ _ _ hr => by
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h

theorem b1_eval_sub_var_mload_add_var_lit_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.sub
        [GenAst.yvar "r",
         GenAst.yop EVM.Op.mload
           [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]]]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := EVM.Op.sub)
    (fun _ _ _ _ hr => by
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => b1_eval_mload_add_var_lit_halt hh) h

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_subfrom_cdl_mload_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_addmod_mulmod_vars_inv
  [propext, Classical.choice, Quot.sound] native []

set_option maxHeartbeats 1200000 in
theorem b1_eval_sub_from_vars_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (subFrom (GenAst.yvar x) (GenAst.yvar y)) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hx =>
          cases hrest with
          | argsCons hrest2 hsub =>
              cases hrest2 with
              | argsCons hnil hr =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact b1_eval_sub_vars_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

set_option maxHeartbeats 1200000 in
theorem b1_eval_sub_from_cdl_mload_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {qc qe : String}
    {offc offe : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (subFrom
        (GenAst.yop EVM.Op.calldataload
          [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit offc]])
        (GenAst.yop EVM.Op.mload
          [GenAst.yop EVM.Op.add [GenAst.yvar qe, GenAst.ylit offe]]))
      (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hc =>
          cases hrest with
          | argsCons hrest2 hsub =>
              cases hrest2 with
              | argsCons hnil hr =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact b1_eval_calldataload_add_var_lit_halt hh
        · exact b1_eval_sub_var_mload_add_var_lit_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

set_option maxHeartbeats 1200000 in
theorem b1_eval_mulmod_subfrom_cdl_mload_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {qc qe inv : String}
    {offc offe : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [subFrom
          (GenAst.yop EVM.Op.calldataload
            [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit offc]])
          (GenAst.yop EVM.Op.mload
            [GenAst.yop EVM.Op.add [GenAst.yvar qe, GenAst.ylit offe]]),
         GenAst.yvar inv, GenAst.yvar "r"]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hsub =>
          cases hrest with
          | argsCons hrest2 hinv =>
              cases hrest2 with
              | argsCons hnil hr =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact b1_eval_sub_from_cdl_mload_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

set_option maxHeartbeats 1200000 in
theorem b1_eval_addmod_mulmod_vars_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {f x2 ev : String}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.addmod
        [GenAst.yop EVM.Op.mulmod
           [GenAst.yvar f, GenAst.yvar x2, GenAst.yvar "r"],
         GenAst.yvar ev, GenAst.yvar "r"]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hf =>
          cases hrest with
          | argsCons hrest2 hev =>
              cases hrest2 with
              | argsCons hnil hr =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact b1_eval_mulmod_vars_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_from_vars_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_from_cdl_mload_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_subfrom_cdl_mload_halt
  [propext, Classical.choice, Quot.sound] native []
theorem b1_exec_ylet_sub_from_vars {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x a b : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (subFrom (GenAst.yvar a) (GenAst.yvar b))) V' st' o) :
    o = .normal ∧ ∃ av bv rv, VEnv.get V a = some av ∧ VEnv.get V b = some bv ∧
      VEnv.get V "r" = some rv ∧
      V' = (x, wAddmodAt av (rv - bv) rv) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := b2_list_length_one hlen
      obtain ⟨av, bv, rv, ha, hb, hr, hval, hst⟩ := b1_eval_sub_from_vars_inv he
      subst hval; subst hst
      exact ⟨rfl, av, bv, rv, ha, hb, hr, by simp, rfl⟩
  | letHalt he => exact (b1_eval_sub_from_vars_halt he).elim

theorem b1_exec_ylet_mulmod_subfrom {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x qc qe inv : String} {offc offe : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x
        (GenAst.yop EVM.Op.mulmod
          [subFrom
            (GenAst.yop EVM.Op.calldataload
              [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit offc]])
            (GenAst.yop EVM.Op.mload
              [GenAst.yop EVM.Op.add [GenAst.yvar qe, GenAst.ylit offe]]),
           GenAst.yvar inv, GenAst.yvar "r"])) V' st' o) :
    o = .normal ∧ ∃ cptr qep rv invv subv,
      VEnv.get V qc = some cptr ∧ VEnv.get V qe = some qep ∧
      VEnv.get V inv = some invv ∧ VEnv.get V "r" = some rv ∧
      subv = wAddmodAt
        (wordFrom st.env.calldata (cptr + BitVec.ofNat 256 offc).toNat)
        (rv - loadWord st.memory (qep + BitVec.ofNat 256 offe).toNat) rv ∧
      V' = (x, wMulmodAt subv invv rv) :: V := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := b2_list_length_one hlen
      obtain ⟨cptr, qep, rv, invv, subv, hc, hq, hi, hr, hsub, hval⟩ :=
        b1_eval_mulmod_subfrom_cdl_mload_inv he
      subst hval
      exact ⟨rfl, cptr, qep, rv, invv, subv, hc, hq, hi, hr, hsub, by simp⟩
  | letHalt he => exact (b1_eval_mulmod_subfrom_cdl_mload_halt he).elim

theorem b1_exec_yset_f_eval {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {f x2 ev : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.yset f
        (GenAst.yop EVM.Op.addmod
          [GenAst.yop EVM.Op.mulmod
             [GenAst.yvar f, GenAst.yvar x2, GenAst.yvar "r"],
           GenAst.yvar ev, GenAst.yvar "r"])) V' st' o) :
    o = .normal ∧ ∃ fv x2v evv rv, VEnv.get V f = some fv ∧
      VEnv.get V x2 = some x2v ∧ VEnv.get V ev = some evv ∧
      VEnv.get V "r" = some rv ∧
      V' = VEnv.set V f (wAddmodAt (wMulmodAt fv x2v rv) evv rv) ∧ st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨v, rfl⟩ := b2_list_length_one hlen
      obtain ⟨fv, x2v, evv, rv, hf, hx2, hev, hr, hval, hst⟩ :=
        b1_eval_addmod_mulmod_vars_inv he
      subst hval; subst hst
      exact ⟨rfl, fv, x2v, evv, rv, hf, hx2, hev, hr, by simp [VEnv.setMany], rfl⟩
  | assignHalt he => exact (b1_eval_addmod_mulmod_vars_halt he).elim

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mload_add_var_lit_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_calldataload_add_var_lit_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_vars_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_var_mload_add_var_lit_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_ylet_sub_from_vars
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_ylet_mulmod_subfrom
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_yset_f_eval
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_addmod_mulmod_vars_halt
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_from_cdl_mload_inv
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_var_mload_add_var_lit_inv
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mload_add_var_lit_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_calldataload_add_var_lit_inv
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_vars_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_addmod_vars_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_sub_from_vars_inv
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.scalarInv_call_contract_var
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b3_exec_ylet_scalar_inv_var
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.PcsBlock4

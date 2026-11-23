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
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv')) :
    ∀ (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g)) (st : EvmState)
      (r : EResult (Bridge.Dialect (permissive (callsOf product)) g)),
      VEnv.get V arg = some xv →
      0 < xv.toNat → xv.toNat < Midfall.Yul.blsR →
      EvalExpr (Bridge.Dialect (permissive (callsOf product)) g) funs V st
        (Expr.call "scalar_inv" [Expr.var arg]) r →
      (∃ st', r = .vals [SIInv xv] st' ∧ MemSameOutside st st' scratch 192 ∧
        st'.env = st.env) ∨
        (∃ st', r = .halt st' ∧ Midfall.LoweringV2.Reverted st') := by
  intro V st r harg hx0 hxR he
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
                        scratch n gasN selN selP xv hn hscratch hscratch256 hfail'
                      have hpost := hbodyC' _ _ (hcalleePre _ hxv) _ _ _ hstmts
                      rcases hpost with ⟨hon, hVb, hget, hout, houtenv⟩ | ⟨hoh, hrev⟩
                      · refine Or.inl ⟨_, ?_, hout, houtenv⟩
                        rw [hVb]
                        simp [VEnv.set, restore, VEnv.get, List.find?, bindZeros]
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
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv')) :
    ∀ (arg x : String) (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g))
      (st : EvmState) (V' : VEnv (Bridge.Dialect (permissive (callsOf product)) g))
      (st' : EvmState) (o : Outcome),
      VEnv.get V arg = some xv →
      0 < xv.toNat → xv.toNat < Midfall.Yul.blsR →
      ExecStmt (Bridge.Dialect (permissive (callsOf product)) g) funs V st
        (GenAst.ylet x (GenAst.ycall "scalar_inv" [GenAst.yvar arg])) V' st' o →
      (o = .normal ∧ V' = (x, SIInv xv) :: V ∧ MemSameOutside st st' scratch 192 ∧
        st'.env = st.env) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st') := by
  intro arg x V st V' st' o harg hx0 hxR hrun
  cases hrun with
  | letVal he hlen =>
      have hc := scalarInv_call_contract_var (product := product) (arg := arg)
        (funs := funs) (decl := decl) (cenv := cenv) (cenv' := cenv')
        scratch n gasN selN selP xv hlook hbody hparams hrets hn hscratch hscratch256 hfail
        V st _ harg hx0 hxR he
      rcases hc with ⟨st1, hev, hout, houtenv⟩ | ⟨st1, heh, hrev⟩
      · injection hev with hvals hst
        rw [hvals]
        exact Or.inl ⟨rfl, by simp [VEnv.setMany], by simpa [hst] using hout,
          by simpa [hst] using houtenv⟩
      · exact absurd heh (by simp)
  | letHalt he =>
      have hc := scalarInv_call_contract_var (product := product) (arg := arg)
        (funs := funs) (decl := decl) (cenv := cenv) (cenv' := cenv')
        scratch n gasN selN selP xv hlook hbody hparams hrets hn hscratch hscratch256 hfail
        V st _ harg hx0 hxR he
      rcases hc with ⟨st1, hev, _, _⟩ | ⟨st1, heh, hrev⟩
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
        (rv - loadWord st.memory (qep + BitVec.ofNat 256 offe).toNat) rv ∧
      st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
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
                  refine ⟨cptr, qep, _, _, hcptr, hqep, hrv0, rfl, ?_, ?_, ?_, ?_⟩
                  · have hrvEq2 := Option.some.inj (hrvSub.symm.trans hrv0)
                    rw [hsubVal, hcdlVal, hrvEq2]
                    rfl
                  · rw [hstc, hsubMem]
                  · rw [hstc, hsubEnv]
                  · rw [hstc, hsubHalt]

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
      cv = wMulmodAt subv invv rv ∧
      st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
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
                  obtain ⟨cptr, qep, rvS, cdlv, hcptr, hqep, hrvS, hcdl, hsubVal,
                    hsubMem, hsubEnv, hsubHalt⟩ :=
                    b1_eval_sub_from_cdl_mload_inv hsub
                  rw [hstinv, hstr] at hsubVal hcdl hsubMem hsubEnv hsubHalt
                  have hrvEq := Option.some.inj (hrvS.symm.trans hrv0)
                  obtain ⟨hinvProj, _⟩ := b1_eval_var_inv hinv
                  rw [hinvv] at hinvProj
                  cases hinvProj
                  obtain ⟨hrProj, _⟩ := b1_eval_var_inv hr
                  rw [hrv0] at hrProj
                  cases hrProj
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  refine ⟨cptr, qep, _, _, _, hcptr, hqep, hinvv, hrv0, ?_, rfl, ?_, ?_, ?_⟩
                  · rw [hsubVal, hcdl, hrvEq]
                  · exact hsubMem
                  · exact hsubEnv
                  · exact hsubHalt

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

theorem copyReturn_outside (mem : Nat → UInt8) (dst size : Nat) (bytes : List UInt8)
    (a : Nat) (h : a < dst ∨ dst + size ≤ a) :
    copyReturn mem dst size bytes a = mem a :=
  ScalarInvSummary.copyReturn_outside mem dst size bytes a h

theorem finishCall_memory_outside {kind : EVM.CallKind} {st : EvmState} {resp : CallResponse}
    (io is oo os a : Nat) (h : a < oo ∨ oo + os ≤ a) :
    (finishCall kind st resp io is oo os).memory a = st.memory a :=
  ScalarInvSummary.finishCall_memory_outside io is oo os a h

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
      V' = (x, wMulmodAt subv invv rv) :: V ∧
      st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := b2_list_length_one hlen
      obtain ⟨cptr, qep, rv, invv, subv, hc, hq, hi, hr, hsub, hval, hm, hev, hh⟩ :=
        b1_eval_mulmod_subfrom_cdl_mload_inv he
      subst hval
      exact ⟨rfl, cptr, qep, rv, invv, subv, hc, hq, hi, hr, hsub, by simp, hm, hev, hh⟩
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

/-! ### Block 4, `m == 1` arm: the four-statement set body -/

/-- The `dx0` word of the `m == 1` set block (`x3 - rot_pt` in the field). -/
def m1Dx0 (x3v ptv rv : U256) : U256 := wAddmodAt x3v (rv - ptv) rv

/-- The `eval` word of the `m == 1` set block. -/
def m1Eval (cval evv dx0v rv : U256) : U256 :=
  wMulmodAt (wAddmodAt cval (rv - evv) rv) (SIInv dx0v) rv

/-- The `f_eval` update of the `m == 1` set block. -/
def m1FEval (fev x2v evv rv : U256) : U256 :=
  wAddmodAt (wMulmodAt fev x2v rv) evv rv

/-- The `m == 1` set block's four statements, definitionally. -/
theorem pcsSetBlockAst_one (setIdx : Nat) (p0 : Int) (distinctRotations : List Int)
    (off : Nat) :
    GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off =
      [ GenAst.ylet "dx0"
          (GenAstPcs.subFrom (GenAst.yvar "x3")
            (GenAst.yvar ("rot_pt_" ++ toString
              ((distinctRotations.findIdx? (fun r => r == p0)).getD 0)))),
        GenAst.ylet "dx0_inv" (GenAst.ycall "scalar_inv" [GenAst.yvar "dx0"]),
        GenAst.ylet "eval"
          (GenAst.yop EVM.Op.mulmod
            [ GenAstPcs.subFrom
                (GenAst.yop EVM.Op.calldataload
                  [GenAst.yop EVM.Op.add [GenAst.yvar "Q_EVAL_CPTR",
                    GenAst.ylit (setIdx * Midfall.Generator.wordBytes)]])
                (GenAst.yop EVM.Op.mload
                  [GenAst.yop EVM.Op.add [GenAst.yvar "Q_EVAL_SET_MPTR",
                    GenAst.ylit (off * Midfall.Generator.wordBytes)]]),
              GenAst.yvar "dx0_inv", GenAst.yvar "r"]),
        GenAst.yset "f_eval"
          (GenAst.yop EVM.Op.addmod
            [ GenAst.yop EVM.Op.mulmod
                [GenAst.yvar "f_eval", GenAst.yvar "x2", GenAst.yvar "r"],
              GenAst.yvar "eval", GenAst.yvar "r"]) ] := by
  simp [GenAstPcs.pcsSetBlockAst]

/-- `restore` drops the three local bindings of a set scope after an outer `set`. -/
theorem restore_three_cons_set {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {a b c x : Ident} {u v w xv : D.Value} (ha : a ≠ x) (hb : b ≠ x) (hc : c ≠ x) :
    restore V (VEnv.set ((a, u) :: (b, v) :: (c, w) :: V) x xv) = VEnv.set V x xv := by
  rw [venv_set_cons_ne ha, venv_set_cons_ne hb, venv_set_cons_ne hc]
  simp only [restore, venv_set_length, List.length_cons]
  rw [show List.length V + 1 + 1 + 1 - List.length V = 3 by omega]
  rfl

/-- A load survives a memory frame when its 32-byte window is outside the frame. -/
theorem loadWord_eq_of_memSameOutside {st st' : EvmState} {lo len : Nat}
    (h : MemSameOutside st st' lo len) {q : Nat}
    (hq : q + 32 ≤ lo ∨ lo + len ≤ q) :
    loadWord st'.memory q = loadWord st.memory q := by
  refine Midfall.Yul.Word.loadWord_congr _ _ q ?_
  intro i hi
  exact h (q + i) (by
    rcases hq with h1 | h2
    · left; omega
    · right; omega)

/-- The normal arm of a normal-or-halt contract, at a known-normal outcome. -/
theorem normal_arm_of {P Q : Prop} {o : Outcome}
    (h : (o = .normal ∧ P) ∨ (o = .halt ∧ Q)) (ho : o = .normal) : P := by
  rcases h with ⟨_, hP⟩ | ⟨hh, _⟩
  · exact hP
  · exact absurd (ho.symm.trans hh) (by decide)

set_option maxErrors 100 in
set_option maxHeartbeats 1200000 in
/-- **BLOCK 4's `m == 1` SET**. The four statements of a one-point set block
    (`dx0`, `dx0_inv`, `eval`, `f_eval`) run normally and leave `f_eval` at the Horner
    contribution of the set. The `scalar_inv` scratch is outside the eval window, so the
    `mload(Q_EVAL_SET_MPTR + off)` word survives the helper; the block wrapper restores the
    three scope bindings. -/
theorem pcsSetBlock1_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (distinctRotations : List Int) (setIdx off scratch n gasN selN selP : Nat) (p0 : Int)
    (pt : String) (x3v ptv rv cptr qep x2v fev : U256)
    (hpt : pt = "rot_pt_" ++ toString
      ((distinctRotations.findIdx? (fun r => r == p0)).getD 0))
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch n gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hn : BitVec.ofNat 256 n = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv'))
    (hdx0pos : 0 < (m1Dx0 x3v ptv rv).toNat)
    (hdx0lt : (m1Dx0 x3v ptv rv).toNat < Midfall.Yul.blsR)
    (hcptrb : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqepb : qep.toNat + off * Midfall.Generator.wordBytes + 32 < 2 ^ 256)
    (hdisj : qep.toNat + off * Midfall.Generator.wordBytes + 32 ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.block (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off))
      (fun V st =>
        VEnv.get V "x3" = some x3v ∧ VEnv.get V "r" = some rv ∧
        VEnv.get V "x2" = some x2v ∧ VEnv.get V "f_eval" = some fev ∧
        VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
        VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧ VEnv.get V pt = some ptv)
      (fun V st V' st' o =>
        (o = .normal ∧
          V' = VEnv.set V "f_eval"
            (m1FEval fev x2v
              (m1Eval (wordFrom st.env.calldata
                  (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
                (loadWord st.memory
                  (qep.toNat + off * Midfall.Generator.wordBytes))
                (m1Dx0 x3v ptv rv) rv) rv) ∧
          MemSameOutside st st' scratch 192 ∧ st'.env = st.env)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hx3, hrv, hx2, hfe, hcptr, hqep, hptv⟩ := hpre
  subst hpt
  have hlookH : lookupFun (hoist (Bridge.Dialect (permissive (callsOf product)) g)
      (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off) :: funs)
      "scalar_inv" = some (decl, cenv) := by
    have hh : hoist (Bridge.Dialect (permissive (callsOf product)) g)
        (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off) = [] := by
      rw [pcsSetBlockAst_one]; rfl
    rw [hh]; simpa [lookupFun] using hlook
  cases hrun with
  | block hbodyrun =>
    rw [pcsSetBlockAst_one] at hbodyrun
    rcases Step.stmts_cons_inv hbodyrun with ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
    · -- dx0 := subFrom x3 rot_pt
      obtain ⟨ho1, av, bv, rvw, hx3', hpt', hr', hV1, hst1⟩ :=
        b1_exec_ylet_sub_from_vars h1
      have hx3e : av = x3v := Option.some.inj (hx3'.symm.trans hx3)
      have hpte : bv = ptv := Option.some.inj (hpt'.symm.trans hptv)
      have hre : rvw = rv := Option.some.inj (hr'.symm.trans hrv)
      have hV1' : V1 = ("dx0", m1Dx0 x3v ptv rv) :: V := by
        rw [hV1, hx3e, hpte, hre]
        rfl
      rcases Step.stmts_cons_inv hrest1 with ⟨V2, st2, h2, hrest2⟩ | ⟨h2h, hne2h⟩
      · -- dx0_inv := scalar_inv(dx0)
        rw [hV1'] at h2
        rw [hst1] at h2
        have hmain :=
          b3_exec_ylet_scalar_inv_var (product := product)
            (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
              (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off) :: funs)
            (decl := decl) (cenv := cenv) (cenv' := cenv')
            scratch n gasN selN selP (m1Dx0 x3v ptv rv) hlookH hbody hparams hrets hn
            hscratch hscratch256 hfail "dx0" "dx0_inv" _ _ _ _ .normal
            (venv_get_cons_self (D := Bridge.Dialect (permissive (callsOf product)) g)
              V "dx0" (m1Dx0 x3v ptv rv)) hdx0pos hdx0lt h2
        obtain ⟨hV2, hfr2, henv2⟩ := normal_arm_of hmain rfl
        rcases Step.stmts_cons_inv hrest2 with ⟨V3, st3, h3, hrest3⟩ | ⟨h3h, hne3h⟩
        · -- eval := mulmod(subFrom proofEval ev, dx0_inv, r)
          rw [hV2] at h3
          obtain ⟨ho3, cptr', qep', rv3, invv, subv, hc', hq', hinv', hr3, hsubeq,
            hV3, hm3, he3, _hh3⟩ := b1_exec_ylet_mulmod_subfrom h3
          have hcptrEq : cptr' = cptr := by
            have h := hc'
            rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "dx0_inv") (y := "Q_EVAL_CPTR") (by decide),
              venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "dx0") (y := "Q_EVAL_CPTR") (by decide)] at h
            exact Option.some.inj (h.symm.trans hcptr)
          have hqepEq : qep' = qep := by
            have h := hq'
            rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "dx0_inv") (y := "Q_EVAL_SET_MPTR") (by decide),
              venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "dx0") (y := "Q_EVAL_SET_MPTR") (by decide)] at h
            exact Option.some.inj (h.symm.trans hqep)
          have hrvEq : rv3 = rv := by
            have h := hr3
            rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "dx0_inv") (y := "r") (by decide),
              venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "dx0") (y := "r") (by decide)] at h
            exact Option.some.inj (h.symm.trans hrv)
          have hinvEq : invv = SIInv (m1Dx0 x3v ptv rv) := by
            have h1 : VEnv.get (("dx0_inv", SIInv (m1Dx0 x3v ptv rv)) ::
                ("dx0", m1Dx0 x3v ptv rv) :: V) "dx0_inv" =
                some (SIInv (m1Dx0 x3v ptv rv)) :=
              venv_get_cons_self (D := Bridge.Dialect (permissive (callsOf product)) g)
                (("dx0", m1Dx0 x3v ptv rv) :: V) "dx0_inv" (SIInv (m1Dx0 x3v ptv rv))
            exact Option.some.inj (hinv'.symm.trans h1)
          have hcaddr : (cptr' + BitVec.ofNat 256
                (setIdx * Midfall.Generator.wordBytes)).toNat =
              cptr.toNat + setIdx * Midfall.Generator.wordBytes := by
            rw [hcptrEq, BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : setIdx * Midfall.Generator.wordBytes < 2 ^ 256),
              Nat.mod_eq_of_lt hcptrb]
          have hqaddr : (qep' + BitVec.ofNat 256
                (off * Midfall.Generator.wordBytes)).toNat =
              qep.toNat + off * Midfall.Generator.wordBytes := by
            rw [hqepEq, BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : off * Midfall.Generator.wordBytes < 2 ^ 256),
              Nat.mod_eq_of_lt (by omega : qep.toNat + off * Midfall.Generator.wordBytes < 2 ^ 256)]
          have hevEq : loadWord st2.memory
                (qep.toNat + off * Midfall.Generator.wordBytes) =
              loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes) :=
            loadWord_eq_of_memSameOutside hfr2 hdisj
          have hsubv : subv = wAddmodAt (wordFrom st.env.calldata
                (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
              (rv - loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes)) rv := by
            rw [hsubeq, hcaddr, hqaddr, hrvEq, hevEq, henv2]
          rcases Step.stmts_cons_inv hrest3 with ⟨V4, st4, h4, hrest4⟩ | ⟨h4h, hne4h⟩
          · -- f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
            rw [hV3] at h4
            obtain ⟨ho4, fvv, x2v', evv', rv4, hf', hx2', hev', hr4, hval4, hst4⟩ :=
              b1_exec_yset_f_eval h4
            have hfEq : fvv = fev := by
              have h := hf'
              rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "eval") (y := "f_eval") (by decide),
                venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "dx0_inv") (y := "f_eval") (by decide),
                venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "dx0") (y := "f_eval") (by decide)] at h
              exact Option.some.inj (h.symm.trans hfe)
            have hx2Eq : x2v' = x2v := by
              have h := hx2'
              rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "eval") (y := "x2") (by decide),
                venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "dx0_inv") (y := "x2") (by decide),
                venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "dx0") (y := "x2") (by decide)] at h
              exact Option.some.inj (h.symm.trans hx2)
            have hev'Eq : evv' = m1Eval (wordFrom st.env.calldata
                  (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
                (loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes))
                (m1Dx0 x3v ptv rv) rv := by
              have hhead : VEnv.get (("eval", wMulmodAt subv invv rv3) ::
                  ("dx0_inv", SIInv (m1Dx0 x3v ptv rv)) ::
                  ("dx0", m1Dx0 x3v ptv rv) :: V) "eval" =
                  some (wMulmodAt subv invv rv3) :=
                venv_get_cons_self (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (("dx0_inv", SIInv (m1Dx0 x3v ptv rv)) ::
                   ("dx0", m1Dx0 x3v ptv rv) :: V) "eval"
                  (wMulmodAt subv invv rv3)
              have hval : wMulmodAt subv invv rv3 = m1Eval (wordFrom st.env.calldata
                    (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
                  (loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes))
                  (m1Dx0 x3v ptv rv) rv := by
                rw [hsubv, hinvEq, hrvEq]
                rfl
              exact Option.some.inj (hev'.symm.trans hhead) |>.trans hval
            have hrvEq4 : rv4 = rv := by
              have h := hr4
              rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "eval") (y := "r") (by decide),
                venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "dx0_inv") (y := "r") (by decide),
                venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                  (x := "dx0") (y := "r") (by decide)] at h
              exact Option.some.inj (h.symm.trans hrv)
            cases hrest4
            refine Or.inl ⟨ho4, ?_, ?_, ?_⟩
            · rw [hval4, hfEq, hx2Eq, hev'Eq, hrvEq4]
              exact restore_three_cons_set (D := Bridge.Dialect (permissive (callsOf product)) g)
                (a := "eval") (b := "dx0_inv") (c := "dx0") (x := "f_eval")
                (by decide) (by decide) (by decide)
            · rw [hst4]
              intro a ha
              rw [hm3]
              exact hfr2 a ha
            · rw [hst4, he3, henv2]
          · -- a halting f_eval is impossible
            exact absurd (b1_exec_yset_f_eval h4h).1 hne4h
        · -- a halting eval is impossible
          exact absurd (b1_exec_ylet_mulmod_subfrom h3h).1 hne3h
      · -- a halting scalar_inv call reverts
        rw [hV1'] at h2h
        rw [hst1] at h2h
        have hc := b3_exec_ylet_scalar_inv_var (product := product)
          (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
            (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off) :: funs)
          (decl := decl) (cenv := cenv) (cenv' := cenv')
          scratch n gasN selN selP (m1Dx0 x3v ptv rv) hlookH hbody hparams hrets hn
          hscratch hscratch256 hfail "dx0" "dx0_inv" _ _ _ _ o
          (venv_get_cons_self (D := Bridge.Dialect (permissive (callsOf product)) g)
            V "dx0" (m1Dx0 x3v ptv rv)) hdx0pos hdx0lt h2h
        rcases hc with hc | hc
        · exact absurd hc.1 hne2h
        · exact Or.inr hc
    · -- a halting dx0 is impossible
      exact absurd (b1_exec_ylet_sub_from_vars h1).1 hne1

/-! ### Block 4, general arm: variable `mulmod(x, subFrom(y,z), r)` plumbing -/

/-- Value inversion for `mulmod(x, subFrom(y,z), r)`: the middle operand is a field
    subtraction of two variables. -/
theorem b1_eval_mulmod_subfrom_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y z : String}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yvar x, GenAstPcs.subFrom (GenAst.yvar y) (GenAst.yvar z),
         GenAst.yvar "r"]) (.vals [cv] st')) :
    ∃ xv yv zv rv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      VEnv.get V z = some zv ∧ VEnv.get V "r" = some rv ∧
      cv = wMulmodAt xv (wAddmodAt yv (rv - zv) rv) rv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hrest with
      | argsCons hrest2 hsub =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hrStep, hstr⟩ := b1_eval_var_inv hr
                  obtain ⟨rv0, hrv0, _⟩ := b1_eval_var_vals hr
                  have hrvEq0 := Option.some.inj (hrv0.symm.trans hrStep)
                  obtain ⟨yv, zv, rvsub, hyv, hzv, hrvsub, hsubVal, hsubSt⟩ :=
                    b1_eval_sub_from_vars_inv hsub
                  obtain ⟨hxStep, hstx⟩ := b1_eval_var_inv hx
                  obtain ⟨xv, hxv, _⟩ := b1_eval_var_vals hx
                  have hxvEq := Option.some.inj (hxv.symm.trans hxStep)
                  have hrvEq : rvsub = rv0 := Option.some.inj (hrvsub.symm.trans hrv0)
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  refine ⟨xv, yv, zv, rv0, hxv, hyv, hzv, hrv0, ?_, ?_⟩
                  · rw [← hxvEq, ← hrvEq0, hsubVal, hrvEq]
                    rfl
                  · rw [hstx, hsubSt, hstr]

theorem b1_eval_mulmod_subfrom_vars_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y z : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yvar x, GenAstPcs.subFrom (GenAst.yvar y) (GenAst.yvar z),
         GenAst.yvar "r"]) (.halt st')) : False := by
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
        · exact b1_eval_sub_from_vars_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

/-- The exec step of one `lbasis_j` update. -/
theorem b1_exec_yset_mulmod_subfrom_vars {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x y z : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.yset x (GenAst.yop EVM.Op.mulmod
        [GenAst.yvar x, GenAstPcs.subFrom (GenAst.yvar y) (GenAst.yvar z),
         GenAst.yvar "r"])) V' st' o) :
    o = .normal ∧ ∃ xv yv zv rv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      VEnv.get V z = some zv ∧ VEnv.get V "r" = some rv ∧
      V' = VEnv.set V x (wMulmodAt xv (wAddmodAt yv (rv - zv) rv) rv) ∧ st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨xv, yv, zv, rv, hxv, hyv, hzv, hrv, hcv, hst⟩ :=
        b1_eval_mulmod_subfrom_vars_inv he
      subst hcv; subst hst
      exact ⟨rfl, xv, yv, zv, rv, hxv, hyv, hzv, hrv, by simp [VEnv.setMany], rfl⟩
  | assignHalt he => exact (b1_eval_mulmod_subfrom_vars_halt he).elim

/-! ### Block 4, general arm: the point-list folds -/

/-- The `dx_j` name of the general set arm. -/
def pcsDxName (j : Nat) : String := "dx_" ++ toString j

/-- One dx line: `let dx_j := subFrom(x3, rot_pt_j)`. -/
def pcsDxStmt (j : Nat) (pt : String) : Stmt EVM.Op :=
  GenAst.ylet (pcsDxName j) (GenAstPcs.subFrom (GenAst.yvar "x3") (GenAst.yvar pt))

set_option maxHeartbeats 800000 in
/-- **THE `dxLines` FOLD.** Every `dx_j := x3 - rot_pt_j` of a general set arm runs normal and
    leaves exactly the `dx_j` bindings; every other name is untouched (the `dx_*` names are
    disjoint from the rotation names and from `x3`/`r`). -/
theorem pcsDxLines_contract {funs : FunEnv (Bridge.Dialect c g)}
    (xs : List (Nat × String)) (x3v rv : U256) (p : Nat → U256)
    (hx3ne : ∀ q ∈ xs, pcsDxName q.1 ≠ "x3")
    (hrne : ∀ q ∈ xs, pcsDxName q.1 ≠ "r")
    (hrotne : ∀ q ∈ xs, ∀ r ∈ xs, q.2 ≠ pcsDxName r.1)
    (hidx : ∀ q ∈ xs, ∀ r ∈ xs, q.1 ≠ r.1)
    (hdxne : ∀ q ∈ xs, ∀ r ∈ xs, q.1 ≠ r.1 → pcsDxName q.1 ≠ pcsDxName r.1) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (xs.map (fun q => pcsDxStmt q.1 q.2))
      (fun V st => VEnv.get V "x3" = some x3v ∧ VEnv.get V "r" = some rv ∧
        (∀ q ∈ xs, VEnv.get V q.2 = some (p q.1)))
      (fun V st V' st' o => o = .normal ∧
        (∀ q ∈ xs, VEnv.get V' (pcsDxName q.1) =
          some (wAddmodAt x3v (rv - p q.1) rv)) ∧
        (∀ y, (∀ q ∈ xs, y ≠ pcsDxName q.1) → VEnv.get V' y = VEnv.get V y) ∧
        st' = st) := by
  induction xs with
  | nil =>
      intro V st hpre V' st' o hrun
      cases hrun
      refine ⟨rfl, ?_, ?_, rfl⟩
      · intro q hq
        simp at hq
      · intro y _
        rfl
  | cons q rest ih =>
      intro V st hpre V' st' o hrun
      obtain ⟨hx3, hrv, hrot⟩ := hpre
      rw [List.map_cons] at hrun
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
          ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
      · obtain ⟨ho, av, bv, rvw, hx3', hpt', hr', hV1, hst1⟩ :=
          b1_exec_ylet_sub_from_vars hhead
        have hx3e : av = x3v := Option.some.inj (hx3'.symm.trans hx3)
        have hpte : bv = p q.1 := Option.some.inj (hpt'.symm.trans (hrot q (by simp)))
        have hre : rvw = rv := Option.some.inj (hr'.symm.trans hrv)
        have hV1' : V1 = (pcsDxName q.1, wAddmodAt x3v (rv - p q.1) rv) :: V := by
          rw [hV1, hx3e, hpte, hre]
        rw [hV1'] at htail
        rw [hst1] at htail
        have hx3ne' : ∀ r ∈ rest, pcsDxName r.1 ≠ "x3" :=
          fun r hr => hx3ne r (List.mem_cons_of_mem _ hr)
        have hrne' : ∀ r ∈ rest, pcsDxName r.1 ≠ "r" :=
          fun r hr => hrne r (List.mem_cons_of_mem _ hr)
        have hrotne' : ∀ r ∈ rest, ∀ r' ∈ rest, r.2 ≠ pcsDxName r'.1 :=
          fun r hr r' hr' => hrotne r (List.mem_cons_of_mem _ hr) r'
            (List.mem_cons_of_mem _ hr')
        have hidx' : ∀ r ∈ rest, ∀ r' ∈ rest, r.1 ≠ r'.1 :=
          fun r hr r' hr' => hidx r (List.mem_cons_of_mem _ hr) r'
            (List.mem_cons_of_mem _ hr')
        have hdxne' : ∀ r ∈ rest, ∀ r' ∈ rest, r.1 ≠ r'.1 →
            pcsDxName r.1 ≠ pcsDxName r'.1 :=
          fun r hr r' hr' => hdxne r (List.mem_cons_of_mem _ hr) r'
            (List.mem_cons_of_mem _ hr')
        have hx3'' : VEnv.get ((pcsDxName q.1, wAddmodAt x3v (rv - p q.1) rv) :: V)
            "x3" = some x3v := by
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsDxName q.1) (y := "x3")
            (v := wAddmodAt x3v (rv - p q.1) rv) (by
              intro h; exact hx3ne q (by simp) h.symm)]
          exact hx3
        have hrv'' : VEnv.get ((pcsDxName q.1, wAddmodAt x3v (rv - p q.1) rv) :: V)
            "r" = some rv := by
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsDxName q.1) (y := "r")
            (v := wAddmodAt x3v (rv - p q.1) rv) (by
              intro h; exact hrne q (by simp) h.symm)]
          exact hrv
        have hrot'' : ∀ r ∈ rest, VEnv.get ((pcsDxName q.1, wAddmodAt x3v (rv - p q.1) rv)
            :: V) r.2 = some (p r.1) := by
          intro r hr
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsDxName q.1) (y := r.2)
            (v := wAddmodAt x3v (rv - p q.1) rv) (by
              intro h; exact hrotne r (List.mem_cons_of_mem _ hr) q (by simp) h)]
          exact hrot r (List.mem_cons_of_mem _ hr)
        obtain ⟨ho2, hlook2, hout2, hst2⟩ :=
          ih hx3ne' hrne' hrotne' hidx' hdxne'
            _ _ ⟨hx3'', hrv'', hrot''⟩ V' st' o htail
        refine ⟨ho2, ?_, ?_, hst2⟩
        · intro r hr
          rcases List.mem_cons.mp hr with hq | hr'
          · subst hq
            rw [hout2 (pcsDxName r.1) (fun s hs =>
              hdxne r (by simp) s (List.mem_cons_of_mem _ hs)
                (hidx r (by simp) s (List.mem_cons_of_mem _ hs)))]
            rw [venv_get_cons_self (D := Bridge.Dialect c g)]
          · exact hlook2 r hr'
        · intro y hy
          rw [hout2 y (fun r hr => hy r (List.mem_cons_of_mem _ hr))]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsDxName q.1) (y := y)
            (v := wAddmodAt x3v (rv - p q.1) rv) (by
              intro h; exact hy q (by simp) h)]
      · exact absurd (b1_exec_ylet_sub_from_vars hhead).1 hne

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDxName [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDxStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDxLines_contract
  [propext, Classical.choice, Quot.sound] native []

/-- The `lbasis_j` name of the general set arm. -/
def pcsLbasisName (j : Nat) : String := "lbasis_" ++ toString j

/-- One `lbasis_j` update: `lbasis_j := mulmod(lbasis_j, subFrom(rot_pt_j, rot_pt_k), r)`. -/
def pcsLbasisStmt (j : Nat) (ptj ptk : String) : Stmt EVM.Op :=
  GenAst.yset (pcsLbasisName j)
    (GenAst.yop EVM.Op.mulmod
      [GenAst.yvar (pcsLbasisName j), GenAstPcs.subFrom (GenAst.yvar ptj) (GenAst.yvar ptk),
       GenAst.yvar "r"])

/-- The `let lbasis_j := 1` of a group. -/
def pcsLbasisInit (j : Nat) : Stmt EVM.Op :=
  GenAst.ylet (pcsLbasisName j) (GenAst.ylit 1)

/-- The running product of one `lbasis_j` group. -/
def pcsLbasisAcc (rv ptjv : U256) (p : Nat → U256) :
    List (Nat × String) → U256 → U256
  | [], acc => acc
  | k :: rest, acc =>
      pcsLbasisAcc rv ptjv p rest (wMulmodAt acc (wAddmodAt ptjv (rv - p k.1) rv) rv)

/-- The final `lbasis_j` word of a group. -/
def pcsLbasisVal (rv ptjv : U256) (p : Nat → U256) (ks : List (Nat × String)) : U256 :=
  pcsLbasisAcc rv ptjv p ks 1

set_option maxHeartbeats 800000 in
/-- **THE `lbasis_j` SET FOLD.** Starting from `name = acc0`, every update multiplies in one
    `rot_pt_j - rot_pt_k`; the value is `pcsLbasisAcc`, every other name is untouched and the
    state is unchanged. -/
theorem pcsLbasisSetFold_contract {funs : FunEnv (Bridge.Dialect c g)}
    (j : Nat) (ptj : String) (ks : List (Nat × String)) (ptjv rv acc0 : U256)
    (p : Nat → U256)
    (hnameNe : ∀ k ∈ ks, pcsLbasisName j ≠ k.2)
    (hptNe : pcsLbasisName j ≠ ptj)
    (hrNe : pcsLbasisName j ≠ "r") :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (ks.map (fun k => pcsLbasisStmt j ptj k.2))
      (fun V st => VEnv.get V (pcsLbasisName j) = some acc0 ∧
        VEnv.get V ptj = some ptjv ∧ VEnv.get V "r" = some rv ∧
        (∀ k ∈ ks, VEnv.get V k.2 = some (p k.1)))
      (fun V st V' st' o => o = .normal ∧
        V' = VEnv.set V (pcsLbasisName j) (pcsLbasisAcc rv ptjv p ks acc0) ∧
        VEnv.get V' (pcsLbasisName j) = some (pcsLbasisAcc rv ptjv p ks acc0) ∧
        (∀ y, y ≠ pcsLbasisName j → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  induction ks generalizing acc0 with
  | nil =>
      intro V st hpre V' st' o hrun
      cases hrun
      obtain ⟨hacc, hpt, hrv, _⟩ := hpre
      refine ⟨rfl, ?_, hacc, fun y _ => rfl, rfl⟩
      change V = VEnv.set V (pcsLbasisName j) acc0
      rw [venv_set_eq_self (D := Bridge.Dialect c g) hacc]
  | cons k rest ih =>
      intro V st hpre V' st' o hrun
      obtain ⟨hacc, hpt, hrv, hrot⟩ := hpre
      rw [List.map_cons] at hrun
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
          ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
      · obtain ⟨ho, xv, yv, zv, rv', hx, hy, hz, hr, hV1, hst1⟩ :=
          b1_exec_yset_mulmod_subfrom_vars hhead
        have hxe : xv = acc0 := Option.some.inj (hx.symm.trans hacc)
        have hye : yv = ptjv := Option.some.inj (hy.symm.trans hpt)
        have hze : zv = p k.1 := Option.some.inj (hz.symm.trans (hrot k (by simp)))
        have hre : rv' = rv := Option.some.inj (hr.symm.trans hrv)
        have hV1' : V1 = VEnv.set V (pcsLbasisName j)
            (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv) := by
          rw [hV1, hxe, hye, hze, hre]
        rw [hV1'] at htail
        rw [hst1] at htail
        have hnameNe' : ∀ k' ∈ rest, pcsLbasisName j ≠ k'.2 :=
          fun k' hk' => hnameNe k' (List.mem_cons_of_mem _ hk')
        have hacc' : VEnv.get (VEnv.set V (pcsLbasisName j)
            (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)) (pcsLbasisName j) =
            some (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv) :=
          venv_get_set_same (D := Bridge.Dialect c g) hacc
        have hpt' : VEnv.get (VEnv.set V (pcsLbasisName j)
            (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)) ptj = some ptjv := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := ptj)
            (v := _) (fun h => hptNe h.symm)]
          exact hpt
        have hrv' : VEnv.get (VEnv.set V (pcsLbasisName j)
            (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)) "r" = some rv := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := "r")
            (v := _) (fun h => hrNe h.symm)]
          exact hrv
        have hrot' : ∀ k' ∈ rest, VEnv.get (VEnv.set V (pcsLbasisName j)
            (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)) k'.2 = some (p k'.1) := by
          intro k' hk'
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := k'.2)
            (v := _) (fun h => hnameNe k' (List.mem_cons_of_mem _ hk') h.symm)]
          exact hrot k' (List.mem_cons_of_mem _ hk')
        obtain ⟨ho2, hV2, hacc2, hout2, hst2⟩ :=
          ih (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)
            hnameNe' _ _ ⟨hacc', hpt', hrv', hrot'⟩ V' st' o htail
        refine ⟨ho2, ?_, hacc2, ?_, hst2⟩
        · rw [hV2]
          change VEnv.set (VEnv.set V (pcsLbasisName j)
              (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)) (pcsLbasisName j)
              (pcsLbasisAcc rv ptjv p rest
                (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv)) =
            VEnv.set V (pcsLbasisName j)
              (pcsLbasisAcc rv ptjv p rest
                (wMulmodAt acc0 (wAddmodAt ptjv (rv - p k.1) rv) rv))
          rw [venv_set_set (D := Bridge.Dialect c g)]
        · intro y hy
          rw [hout2 y hy]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := y)
            (v := _) hy]
      · exact absurd (b1_exec_yset_mulmod_subfrom_vars hhead).1 hne

set_option maxHeartbeats 800000 in
/-- **ONE `lbasis_j` GROUP.** `let lbasis_j := 1` followed by the update fold; the group binds
    `lbasis_j` at `pcsLbasisVal` and leaves the state and every other name alone. -/
theorem pcsLbasisGroup_contract {funs : FunEnv (Bridge.Dialect c g)}
    (j : Nat) (ptj : String) (ks : List (Nat × String)) (ptjv rv : U256)
    (p : Nat → U256)
    (hnameNe : ∀ k ∈ ks, pcsLbasisName j ≠ k.2)
    (hptNe : pcsLbasisName j ≠ ptj)
    (hrNe : pcsLbasisName j ≠ "r") :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (pcsLbasisInit j :: ks.map (fun k => pcsLbasisStmt j ptj k.2))
      (fun V st => (VEnv.get V (pcsLbasisName j)).isSome = false ∧
        VEnv.get V ptj = some ptjv ∧ VEnv.get V "r" = some rv ∧
        (∀ k ∈ ks, VEnv.get V k.2 = some (p k.1)))
      (fun V st V' st' o => o = .normal ∧
        V' = (pcsLbasisName j, pcsLbasisVal rv ptjv p ks) :: V ∧
        (∀ y, y ≠ pcsLbasisName j → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hfresh, hpt, hrv, hrot⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
  · cases hhead with
    | letVal he hlen =>
        cases he with
        | lit =>
            have hacc : VEnv.get ((pcsLbasisName j, (1 : U256)) :: V) (pcsLbasisName j) =
                some (1 : U256) := venv_get_cons_self (D := Bridge.Dialect c g) V _ _
            have hpt' : VEnv.get ((pcsLbasisName j, (1 : U256)) :: V) ptj = some ptjv := by
              rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := ptj)
                (v := (1 : U256)) (fun h => hptNe h.symm)]
              exact hpt
            have hrv' : VEnv.get ((pcsLbasisName j, (1 : U256)) :: V) "r" = some rv := by
              rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := "r")
                (v := (1 : U256)) (fun h => hrNe h.symm)]
              exact hrv
            have hrot' : ∀ k ∈ ks, VEnv.get ((pcsLbasisName j, (1 : U256)) :: V) k.2 =
                some (p k.1) := by
              intro k hk
              rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := k.2)
                (v := (1 : U256)) (fun h => hnameNe k hk h.symm)]
              exact hrot k hk
            obtain ⟨ho2, hV2, _hacc2, hout2, hst2⟩ :=
              pcsLbasisSetFold_contract (c := c) (g := g) (funs := funs)
                j ptj ks ptjv rv 1 p hnameNe hptNe hrNe
                _ _ ⟨hacc, hpt', hrv', hrot'⟩ V' st' o htail
            refine ⟨ho2, ?_, ?_, hst2⟩
            · rw [hV2, venv_set_cons_same (D := Bridge.Dialect c g)]
              rfl
            · intro y hy
              rw [hout2 y hy]
              rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName j) (y := y)
                (v := (1 : U256)) hy]
  · cases hhead with
    | letVal he hlen => exact absurd rfl hne
    | letHalt he => cases he

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisName [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisInit [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisAcc [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisVal [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisSetFold_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisGroup_contract
  [propext, Classical.choice, Quot.sound] native []

/-- The statement list of one `lbasis` group. -/
def pcsLbasisGroupAst (j : Nat) (ptj : String) (ks : List (Nat × String)) : Block EVM.Op :=
  pcsLbasisInit j :: ks.map (fun k => pcsLbasisStmt j ptj k.2)

set_option maxHeartbeats 1200000 in
/-- **THE `lbasisLines` FOLD.** All groups of a general set arm run normal; every `lbasis_j` ends
    at `pcsLbasisVal`, every other name is untouched and the state is unchanged. Each group's
    name is fresh and the groups' names are pairwise distinct. -/
theorem pcsLbasisLines_contract {funs : FunEnv (Bridge.Dialect c g)}
    (gs : List (Nat × String)) (ks : Nat → List (Nat × String)) (rv : U256)
    (p : Nat → U256)
    (hrNe : ∀ g ∈ gs, pcsLbasisName g.1 ≠ "r")
    (hptNe : ∀ g ∈ gs, pcsLbasisName g.1 ≠ g.2)
    (hnameNe : ∀ g ∈ gs, ∀ k ∈ ks g.1, pcsLbasisName g.1 ≠ k.2)
    (hrotNe : ∀ g ∈ gs, ∀ g' ∈ gs, pcsLbasisName g.1 ≠ g'.2)
    (hrotNe2 : ∀ g ∈ gs, ∀ g' ∈ gs, ∀ k ∈ ks g'.1, pcsLbasisName g.1 ≠ k.2)
    (hdist : ∀ g ∈ gs, ∀ g' ∈ gs, g.1 ≠ g'.1 →
      pcsLbasisName g.1 ≠ pcsLbasisName g'.1)
    (hidx : ∀ g ∈ gs, ∀ g' ∈ gs, g.1 ≠ g'.1) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      ((gs.map (fun g => pcsLbasisGroupAst g.1 g.2 (ks g.1))).flatten)
      (fun V st => VEnv.get V "r" = some rv ∧
        (∀ g ∈ gs, VEnv.get V g.2 = some (p g.1)) ∧
        (∀ g ∈ gs, ∀ k ∈ ks g.1, VEnv.get V k.2 = some (p k.1)) ∧
        (∀ g ∈ gs, VEnv.get V (pcsLbasisName g.1) = none))
      (fun V st V' st' o => o = .normal ∧
        (∀ g ∈ gs, VEnv.get V' (pcsLbasisName g.1) =
          some (pcsLbasisVal rv (p g.1) p (ks g.1))) ∧
        (∀ y, (∀ g ∈ gs, y ≠ pcsLbasisName g.1) → VEnv.get V' y = VEnv.get V y) ∧
        st' = st) := by
  induction gs with
  | nil =>
      intro V st hpre V' st' o hrun
      cases hrun
      obtain ⟨hrv, hpt, hks, hfresh⟩ := hpre
      exact ⟨rfl, (fun g hg => absurd hg (by simp)), (fun y _ => rfl), rfl⟩
  | cons gp rest ih =>
      intro V st hpre V' st' o hrun
      obtain ⟨hrv, hpt, hks, hfresh⟩ := hpre
      rw [List.map_cons, List.flatten_cons] at hrun
      rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
          ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
      · have hgrp := pcsLbasisGroup_contract (c := c) (g := g) (funs := funs)
          gp.1 gp.2 (ks gp.1) (p gp.1) rv p
          (fun k hk => hnameNe gp (by simp) k hk)
          (hptNe gp (by simp)) (hrNe gp (by simp))
          V st ⟨by rw [hfresh gp (by simp)]; rfl, hpt gp (by simp), hrv,
            hks gp (by simp)⟩ V1 st1 .normal hhead
        obtain ⟨ho, hV1, hout1, hst1⟩ := hgrp
        rw [hV1] at htail
        rw [hst1] at htail
        have hrNe' : ∀ g' ∈ rest, pcsLbasisName g'.1 ≠ "r" :=
          fun g' hg' => hrNe g' (List.mem_cons_of_mem _ hg')
        have hptNe' : ∀ g' ∈ rest, pcsLbasisName g'.1 ≠ g'.2 :=
          fun g' hg' => hptNe g' (List.mem_cons_of_mem _ hg')
        have hnameNe' : ∀ g' ∈ rest, ∀ k ∈ ks g'.1, pcsLbasisName g'.1 ≠ k.2 :=
          fun g' hg' => hnameNe g' (List.mem_cons_of_mem _ hg')
        have hrotNe' : ∀ g' ∈ rest, ∀ g'' ∈ rest, pcsLbasisName g'.1 ≠ g''.2 :=
          fun g' hg' g'' hg'' => hrotNe g' (List.mem_cons_of_mem _ hg')
            g'' (List.mem_cons_of_mem _ hg'')
        have hrotNe2' : ∀ g' ∈ rest, ∀ g'' ∈ rest, ∀ k ∈ ks g''.1,
            pcsLbasisName g'.1 ≠ k.2 :=
          fun g' hg' g'' hg'' => hrotNe2 g' (List.mem_cons_of_mem _ hg')
            g'' (List.mem_cons_of_mem _ hg'')
        have hdist' : ∀ g' ∈ rest, ∀ g'' ∈ rest, g'.1 ≠ g''.1 →
            pcsLbasisName g'.1 ≠ pcsLbasisName g''.1 :=
          fun g' hg' g'' hg'' => hdist g' (List.mem_cons_of_mem _ hg')
            g'' (List.mem_cons_of_mem _ hg'')
        have hidx' : ∀ g' ∈ rest, ∀ g'' ∈ rest, g'.1 ≠ g''.1 :=
          fun g' hg' g'' hg'' => hidx g' (List.mem_cons_of_mem _ hg')
            g'' (List.mem_cons_of_mem _ hg'')
        have hrv' : VEnv.get ((pcsLbasisName gp.1, pcsLbasisVal rv (p gp.1) p (ks gp.1)) :: V)
            "r" = some rv := by
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName gp.1) (y := "r")
            (v := _) (fun h => hrNe gp (by simp) h.symm)]
          exact hrv
        have hpt' : ∀ g' ∈ rest, VEnv.get
            ((pcsLbasisName gp.1, pcsLbasisVal rv (p gp.1) p (ks gp.1)) :: V) g'.2 =
            some (p g'.1) := by
          intro g' hg'
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName gp.1) (y := g'.2)
            (v := _) (hrotNe gp (by simp) g' (List.mem_cons_of_mem _ hg')).symm]
          exact hpt g' (List.mem_cons_of_mem _ hg')
        have hks' : ∀ g' ∈ rest, ∀ k ∈ ks g'.1, VEnv.get
            ((pcsLbasisName gp.1, pcsLbasisVal rv (p gp.1) p (ks gp.1)) :: V) k.2 =
            some (p k.1) := by
          intro g' hg' k hk
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName gp.1) (y := k.2)
            (v := _) (hrotNe2 gp (by simp) g' (List.mem_cons_of_mem _ hg') k hk).symm]
          exact hks g' (List.mem_cons_of_mem _ hg') k hk
        have hfresh' : ∀ g' ∈ rest, VEnv.get
            ((pcsLbasisName gp.1, pcsLbasisVal rv (p gp.1) p (ks gp.1)) :: V)
            (pcsLbasisName g'.1) = none := by
          intro g' hg'
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName gp.1)
            (y := pcsLbasisName g'.1) (v := _)
            (hdist gp (by simp) g' (List.mem_cons_of_mem _ hg')
              (hidx gp (by simp) g' (List.mem_cons_of_mem _ hg'))).symm]
          exact hfresh g' (List.mem_cons_of_mem _ hg')
        obtain ⟨ho2, hlook2, hout2, hst2⟩ :=
          ih hrNe' hptNe' hnameNe' hrotNe' hrotNe2' hdist' hidx'
            _ _ ⟨hrv', hpt', hks', hfresh'⟩ V' st' o htail
        refine ⟨ho2, ?_, ?_, hst2⟩
        · intro g' hg'
          rcases List.mem_cons.mp hg' with hg | hg'
          · cases hg
            rw [hout2 (pcsLbasisName gp.1) (fun s hs =>
              hdist gp (by simp) s (List.mem_cons_of_mem _ hs)
                (hidx gp (by simp) s (List.mem_cons_of_mem _ hs)))]
            rw [venv_get_cons_self (D := Bridge.Dialect c g)]
          · exact hlook2 g' hg'
        · intro y hy
          rw [hout2 y (fun g' hg' => hy g' (List.mem_cons_of_mem _ hg'))]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsLbasisName gp.1) (y := y)
            (v := _) (hy gp (by simp))]
      · obtain ⟨ho, _, _, _, _⟩ :=
          pcsLbasisGroup_contract (c := c) (g := g) (funs := funs)
            gp.1 gp.2 (ks gp.1) (p gp.1) rv p
            (fun k hk => hnameNe gp (by simp) k hk)
            (hptNe gp (by simp)) (hrNe gp (by simp))
            V st ⟨by rw [hfresh gp (by simp)]; rfl, hpt gp (by simp), hrv,
              hks gp (by simp)⟩ V' st' o hhead
        exact absurd ho hne

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisGroupAst [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsLbasisLines_contract
  [propext, Classical.choice, Quot.sound] native []

/-- The exec step of one `bp_i := mulmod(bp_{i-1}, input_i, r)` line. -/
theorem b1_exec_ylet_mulmod_vars {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x a b z : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.yop EVM.Op.mulmod
        [GenAst.yvar a, GenAst.yvar b, GenAst.yvar z])) V' st' o) :
    o = .normal ∧ ∃ av bv zv, VEnv.get V a = some av ∧ VEnv.get V b = some bv ∧
      VEnv.get V z = some zv ∧ V' = (x, wMulmodAt av bv zv) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨av, bv, zv, ha, hb, hz, hcv, hst⟩ := b1_eval_mulmod_vars_inv he
      subst hcv; subst hst
      exact ⟨rfl, av, bv, zv, ha, hb, hz, by simp [VEnv.setMany], rfl⟩
  | letHalt he => exact (b1_eval_mulmod_vars_halt he).elim

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_ylet_mulmod_vars
  [propext, Classical.choice, Quot.sound] native []

/-- The `bp_i` name of the general set arm. -/
def pcsBpName (i : Nat) : String := "bp_" ++ toString i

/-- `let bp_0 := batchInputs[0]`. -/
def pcsBpHead (inp : String) : Stmt EVM.Op :=
  GenAst.ylet (pcsBpName 0) (GenAst.yvar inp)

/-- `let bp_i := mulmod(bp_{i-1}, batchInputs[i], r)`. -/
def pcsBpTail (i : Nat) (inp : String) : Stmt EVM.Op :=
  GenAst.ylet (pcsBpName i) (GenAst.yop EVM.Op.mulmod
    [GenAst.yvar (pcsBpName (i - 1)), GenAst.yvar inp, GenAst.yvar "r"])

/-- The head line binds `bp_0` at the first input. -/
theorem pcsBpHead_contract {funs : FunEnv (Bridge.Dialect c g)} (inp : String) (a0 : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs (pcsBpHead inp)
      (fun V st => VEnv.get V inp = some a0)
      (fun V st V' st' o => o = .normal ∧
        V' = (pcsBpName 0, a0) :: V ∧
        VEnv.get V' (pcsBpName 0) = some a0 ∧
        (∀ y, y ≠ pcsBpName 0 → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨ho, yv, hyv, hV, hst⟩ := b1_exec_ylet_var hrun
  have hye : yv = a0 := Option.some.inj (hyv.symm.trans hpre)
  refine ⟨ho, ?_, ?_, ?_, hst⟩
  · rw [hV, hye]
  · rw [hV, hye]
    exact venv_get_cons_self (D := Bridge.Dialect c g) V _ _
  · intro y hy
    rw [hV]
    exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsBpName 0) (y := y)
      (v := yv) hy

/-- One update line binds `bp_i` at `mulmod(bp_{i-1}, input_i, r)`. -/
theorem pcsBpTail_contract {funs : FunEnv (Bridge.Dialect c g)}
    (i : Nat) (inp : String) (prev a rv : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs (pcsBpTail i inp)
      (fun V st => VEnv.get V (pcsBpName (i - 1)) = some prev ∧
        VEnv.get V inp = some a ∧ VEnv.get V "r" = some rv)
      (fun V st V' st' o => o = .normal ∧
        V' = (pcsBpName i, wMulmodAt prev a rv) :: V ∧
        VEnv.get V' (pcsBpName i) = some (wMulmodAt prev a rv) ∧
        (∀ y, y ≠ pcsBpName i → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hprev, hinp, hrv⟩ := hpre
  obtain ⟨ho, av, bv, zv, hp, hi, hr, hV, hst⟩ := b1_exec_ylet_mulmod_vars hrun
  have hae : av = prev := Option.some.inj (hp.symm.trans hprev)
  have hie : bv = a := Option.some.inj (hi.symm.trans hinp)
  have hre : zv = rv := Option.some.inj (hr.symm.trans hrv)
  refine ⟨ho, ?_, ?_, ?_, hst⟩
  · rw [hV, hae, hie, hre]
  · rw [hV, hae, hie, hre]
    exact venv_get_cons_self (D := Bridge.Dialect c g) V _ _
  · intro y hy
    rw [hV]
    exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsBpName i) (y := y)
      (v := _) hy

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpName [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpHead [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpTail [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpHead_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpTail_contract
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.PcsBlock4.copyReturn_outside
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.finishCall_memory_outside
  [propext, Classical.choice, Quot.sound] native []

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

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsSetBlockAst_one
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.restore_three_cons_set
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.loadWord_eq_of_memSameOutside
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.normal_arm_of
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsSetBlock1_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.m1Dx0 [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.m1Eval
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.m1FEval [propext] native []

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

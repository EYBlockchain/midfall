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

/-- The emitted `bpLines`. -/
def pcsBpLines (n : Nat) (nm : Nat → String) : Block EVM.Op :=
  pcsBpHead (nm 0) :: ((List.range n).drop 1).map (fun i => pcsBpTail i (nm i))

/-- The running product `bp_i`. -/
def pcsBpVal (rv : U256) (a : Nat → U256) : Nat → U256
  | 0 => a 0
  | i + 1 => wMulmodAt (pcsBpVal rv a i) (a (i + 1)) rv

theorem pcsBpVal_succ (rv : U256) (a : Nat → U256) (i : Nat) :
    pcsBpVal rv a (i + 1) = wMulmodAt (pcsBpVal rv a i) (a (i + 1)) rv := rfl

set_option maxHeartbeats 1600000 in
/-- **THE `bpLines` FOLD.** -/
theorem pcsBpLines_contract {funs : FunEnv (Bridge.Dialect c g)}
    (n : Nat) (nm : Nat → String) (rv : U256) (a : Nat → U256)
    (hn : 0 < n)
    (hbpNeR : ∀ i < n, pcsBpName i ≠ "r")
    (hbpNeIn : ∀ i < n, ∀ j < n, pcsBpName i ≠ nm j)
    (hbpDist : ∀ i < n, ∀ j < n, i ≠ j → pcsBpName i ≠ pcsBpName j) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (pcsBpLines n nm)
      (fun V st => VEnv.get V "r" = some rv ∧
        (∀ i < n, VEnv.get V (nm i) = some (a i)) ∧
        (∀ i < n, VEnv.get V (pcsBpName i) = none))
      (fun V st V' st' o => o = .normal ∧
        (∀ i < n, VEnv.get V' (pcsBpName i) = some (pcsBpVal rv a i)) ∧
        (∀ y, (∀ i < n, y ≠ pcsBpName i) → VEnv.get V' y = VEnv.get V y) ∧
        st' = st) := by
  induction n with
  | zero => intro V st hpre V' st' o hrun; omega
  | succ n ih =>
      intro V st hpre V' st' o hrun
      obtain ⟨hrv, ha, hfresh⟩ := hpre
      cases n with
      | zero =>
          have hshape : pcsBpLines 1 nm = [pcsBpHead (nm 0)] := by simp [pcsBpLines]
          rw [hshape] at hrun
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
              ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
          · cases htail
            obtain ⟨ho, yv, hyv, hV1, hst1⟩ := b1_exec_ylet_var hhead
            have hye : yv = a 0 := Option.some.inj (hyv.symm.trans (ha 0 (by omega)))
            refine ⟨ho, ?_, ?_, ?_⟩
            · intro i hi
              have hi0 : i = 0 := by omega
              subst hi0
              rw [hV1, hye]
              exact venv_get_cons_self (D := Bridge.Dialect c g) V _ _
            · intro y hy
              rw [hV1]
              exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsBpName 0) (y := y)
                (v := yv) (hy 0 (by omega))
            · simpa [hst1]
          · exact absurd (b1_exec_ylet_var hhead).1 hne
      | succ m =>
          have hshape : pcsBpLines (m + 2) nm =
              pcsBpLines (m + 1) nm ++ [pcsBpTail (m + 1) (nm (m + 1))] := by
            rw [pcsBpLines, pcsBpLines]
            rw [show m + 2 = (m + 1) + 1 by omega, List.range_succ,
              List.drop_append_of_le_length (by simp)]
            rw [List.map_append, List.map_singleton]
            rfl
          rw [hshape] at hrun
          rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
              ⟨V1, st1, hpfx, hlast⟩ | ⟨hpfx, hne⟩
          · obtain ⟨ho1, hlook1, hout1, hst1⟩ :=
              ih (by omega)
                (fun i hi => hbpNeR i (by omega))
                (fun i hi j hj => hbpNeIn i (by omega) j (by omega))
                (fun i hi j hj => hbpDist i (by omega) j (by omega))
                V st ⟨hrv, fun i hi => ha i (by omega), fun i hi => hfresh i (by omega)⟩
                V1 st1 .normal hpfx
            rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hlast with
                ⟨V2, st2, htail, hnil⟩ | ⟨htail, hne2⟩
            · cases hnil
              have hprev : VEnv.get V1 (pcsBpName ((m + 1) - 1)) =
                  some (pcsBpVal rv a ((m + 1) - 1)) := hlook1 (m + 1 - 1) (by omega)
              have hinp : VEnv.get V1 (nm (m + 1)) = some (a (m + 1)) := by
                rw [hout1 (nm (m + 1)) (fun i hi => (hbpNeIn i (by omega) (m + 1) (by omega)).symm)]
                exact ha (m + 1) (by omega)
              have hrv1 : VEnv.get V1 "r" = some rv := by
                rw [hout1 "r" (fun i hi => (hbpNeR i (by omega)).symm)]
                exact hrv
              obtain ⟨ho2, av, bv, zv, hp, hi, hr, hV2, hst2⟩ :=
                b1_exec_ylet_mulmod_vars htail
              have hav : av = pcsBpVal rv a m := by
                have h := Option.some.inj (hp.symm.trans hprev)
                simpa using h
              have hinpe : bv = a (m + 1) := Option.some.inj (hi.symm.trans hinp)
              have hrve : zv = rv := Option.some.inj (hr.symm.trans hrv1)
              refine ⟨ho2, ?_, ?_, by rw [hst2, hst1]⟩
              · intro i hi
                have hile : i ≤ m + 1 := by omega
                rcases Nat.lt_or_eq_of_le hile with hil | rfl
                · rw [hV2]
                  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsBpName (m + 1))
                    (y := pcsBpName i) (v := _)
                    (fun h => hbpDist (m + 1) (by omega) i (by omega) (by omega) h.symm)]
                  exact hlook1 i hil
                · rw [hV2, venv_get_cons_self (D := Bridge.Dialect c g), hav, hinpe, hrve]
                  rw [show pcsBpVal rv a (m + 1) =
                    wMulmodAt (pcsBpVal rv a m) (a (m + 1)) rv from pcsBpVal_succ rv a m]
              · intro y hy
                rw [hV2]
                rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := pcsBpName (m + 1))
                  (y := y) (v := _) (hy (m + 1) (by omega))]
                exact hout1 y (fun i hi => hy i (by omega))
            · exact absurd (b1_exec_ylet_mulmod_vars htail).1 hne2
          · exact absurd (ih (by omega)
              (fun i hi => hbpNeR i (by omega))
              (fun i hi j hj => hbpNeIn i (by omega) j (by omega))
              (fun i hi j hj => hbpDist i (by omega) j (by omega))
              V st ⟨hrv, fun i hi => ha i (by omega), fun i hi => hfresh i (by omega)⟩
              V' st' o hpfx).1 hne

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpLines [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpVal [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpLines_contract
  [propext, Classical.choice, Quot.sound] native []

/-- `let bq := scalar_inv(bp_{n-1})`: the one scalar inverse of the general set arm. -/
def pcsBqStmt (prev : String) : Stmt EVM.Op :=
  GenAst.ylet "bq" (GenAst.ycall "scalar_inv" [GenAst.yvar prev])

/-- The `bq` call: binds `bq` at `SIInv bpv` and preserves memory outside the scratch and the env. -/
theorem pcsBq_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch n gasN selN selP : Nat) (prev : String) (bpv : U256)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch n gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hn : BitVec.ofNat 256 n = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some (failFDecl, cenv')) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (pcsBqStmt prev)
      (fun V st => VEnv.get V prev = some bpv ∧ 0 < bpv.toNat ∧
        bpv.toNat < Midfall.Yul.blsR)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = ("bq", SIInv bpv) :: V ∧
          MemSameOutside st st' scratch 192 ∧ st'.env = st.env) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hprev, h0, hR⟩ := hpre
  exact b3_exec_ylet_scalar_inv_var (product := product) (funs := funs)
    scratch n gasN selN selP bpv
    hlook hbody hparams hrets hn hscratch hscratch256 hfail prev "bq"
    V st V' st' o hprev h0 hR hrun

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBqStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBq_contract
  [propext, Classical.choice, Quot.sound] native []

/-- `SIInv` commutes with `QuotientRows.wMulmodAt` at the field modulus. -/
theorem pcsSIInv_wMulmod_quot (b a : U256) :
    SIInv (Midfall.LoweringV3.QuotientRows.wMulmodAt b a (BitVec.ofNat 256 blsR)) =
      Midfall.LoweringV3.QuotientRows.wMulmodAt (SIInv b) (SIInv a) (BitVec.ofNat 256 blsR) := by
  have hb : blsR < 2 ^ 256 := by decide
  apply BitVec.eq_of_toNat_eq
  have hval (x : U256) : ((x.toNat : ZMod blsR)⁻¹).val < 2 ^ 256 :=
    lt_trans (ZMod.val_lt _) hb
  rw [show (SIInv (Midfall.LoweringV3.QuotientRows.wMulmodAt b a (BitVec.ofNat 256 blsR))).toNat
      = ((Midfall.LoweringV3.QuotientRows.wMulmodAt b a (BitVec.ofNat 256 blsR)).toNat
          : ZMod blsR)⁻¹.val by
    simp only [SIInv, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (hval _)]
  rw [LagrangeRows.wMulmodAt_toNat hb b a]
  rw [LagrangeRows.wMulmodAt_toNat hb (SIInv b) (SIInv a)]
  simp only [SIInv, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (hval b), Nat.mod_eq_of_lt (hval a)]
  rw [← ZMod.val_mul]
  congr 1
  rw [ZMod.natCast_mod]
  push_cast
  rw [mul_inv_rev]
  ring

/-- `SIInv` commutes with `PcsRows.wMulmodAt` at the field modulus. -/
theorem pcsSIInv_wMulmod (b a : U256) :
    SIInv (Midfall.LoweringV3.PcsRows.wMulmodAt b a (BitVec.ofNat 256 blsR)) =
      Midfall.LoweringV3.PcsRows.wMulmodAt (SIInv b) (SIInv a) (BitVec.ofNat 256 blsR) := by
  simpa [Midfall.LoweringV3.PcsRows.wMulmodAt, Midfall.LoweringV3.QuotientRows.wMulmodAt]
    using pcsSIInv_wMulmod_quot b a

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsSIInv_wMulmod_quot
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsSIInv_wMulmod
  [propext, Classical.choice, Quot.sound] native []

/-- The field modulus word is nonzero. -/
theorem pcsR_ne_zero : (BitVec.ofNat 256 Midfall.Yul.blsR : U256) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : Midfall.Yul.blsR < 2 ^ 256)] at this
  exact (Nat.pos_iff_ne_zero.mp (by decide : 0 < Midfall.Yul.blsR)) this

/-- `SIInv x` is a field inverse of `x`. -/
theorem pcsSIInv_mul (x : U256) (hx0 : x.toNat ≠ 0)
    (hx : x.toNat < Midfall.Yul.blsR) :
    wMulmodAt (SIInv x) x (BitVec.ofNat 256 Midfall.Yul.blsR) = 1 :=
  Midfall.LoweringV3.ModexpGeneral.wMulmodAt_zmod_inv x hx0 hx

/-- `wMulmodAt` is associative. -/
theorem pcs_wMulmodAt_assoc {a b cc : U256} :
    wMulmodAt (wMulmodAt a b (BitVec.ofNat 256 Midfall.Yul.blsR)) cc
        (BitVec.ofNat 256 Midfall.Yul.blsR) =
      wMulmodAt a (wMulmodAt b cc (BitVec.ofNat 256 Midfall.Yul.blsR))
        (BitVec.ofNat 256 Midfall.Yul.blsR) :=
  Midfall.LoweringV3.BatchInvert.wMulmodAt_assoc pcsR_ne_zero

/-- `wMulmodAt` is commutative. -/
theorem pcs_wMulmodAt_comm {a b : U256} :
    wMulmodAt a b (BitVec.ofNat 256 Midfall.Yul.blsR) =
      wMulmodAt b a (BitVec.ofNat 256 Midfall.Yul.blsR) :=
  Midfall.LoweringV3.BatchInvert.wMulmodAt_comm pcsR_ne_zero

/-- A field product stays below the modulus. -/
theorem pcs_wMulmodAt_toNat_lt {a b : U256} :
    (wMulmodAt a b (BitVec.ofNat 256 Midfall.Yul.blsR)).toNat < Midfall.Yul.blsR := by
  have h := Midfall.LoweringV3.BatchInvert.wMulmodAt_toNat_lt
    (r := (BitVec.ofNat 256 Midfall.Yul.blsR : U256)) pcsR_ne_zero (a := a) (b := b)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : Midfall.Yul.blsR < 2 ^ 256)] at h
  exact h

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsR_ne_zero
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsSIInv_mul
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_wMulmodAt_assoc
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_wMulmodAt_comm
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_wMulmodAt_toNat_lt
  [propext, Classical.choice, Quot.sound] native []

theorem pcs_blsR_lt : Midfall.Yul.blsR < 2 ^ 256 := by decide

theorem pcs_blsR_ne_zero : Midfall.Yul.blsR ≠ 0 :=
  (Fact.out (p := Nat.Prime Midfall.Yul.blsR)).ne_zero

theorem pcs_ofNat_blsR_toNat :
    (BitVec.ofNat 256 Midfall.Yul.blsR : U256).toNat = Midfall.Yul.blsR := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcs_blsR_lt]

theorem pcs_ofNat_blsR_ne_zero : (BitVec.ofNat 256 Midfall.Yul.blsR : U256) ≠ 0 := by
  intro h
  have this : Midfall.Yul.blsR = 0 := by
    have h' := congrArg BitVec.toNat h
    rw [pcs_ofNat_blsR_toNat] at h'
    simpa using h'
  exact pcs_blsR_ne_zero this

theorem pcs_wAddmodAt_toNat (a b : U256) :
    (wAddmodAt a b (BitVec.ofNat 256 Midfall.Yul.blsR)).toNat =
      (a.toNat + b.toNat) % Midfall.Yul.blsR := by
  rw [wAddmodAt, if_neg pcs_ofNat_blsR_ne_zero, pcs_ofNat_blsR_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le
    (Nat.mod_lt _ (Fact.out (p := Nat.Prime Midfall.Yul.blsR)).pos)
    (Nat.le_of_lt pcs_blsR_lt)

theorem pcs_wMulmodAt_toNat (a b : U256) :
    (wMulmodAt a b (BitVec.ofNat 256 Midfall.Yul.blsR)).toNat =
      (a.toNat * b.toNat) % Midfall.Yul.blsR := by
  rw [wMulmodAt, if_neg pcs_ofNat_blsR_ne_zero, pcs_ofNat_blsR_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le
    (Nat.mod_lt _ (Fact.out (p := Nat.Prime Midfall.Yul.blsR)).pos)
    (Nat.le_of_lt pcs_blsR_lt)

theorem pcs_toNat_sub_of_lt_blsR {a : U256} (ha : a.toNat < Midfall.Yul.blsR) :
    (BitVec.ofNat 256 Midfall.Yul.blsR - a).toNat = Midfall.Yul.blsR - a.toNat := by
  rw [BitVec.toNat_sub, pcs_ofNat_blsR_toNat]
  have hM := pcs_blsR_lt
  have h : 2 ^ 256 - a.toNat + Midfall.Yul.blsR =
      (Midfall.Yul.blsR - a.toNat) + 2 ^ 256 := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega


theorem pcs_nat_key (C E I M : Nat) (hE : E < M) :
    (C * I % M + (M - E * I % M)) % M = ((C + (M - E)) % M * I) % M := by
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hE
  have hB : E * I % M ≤ M := Nat.le_of_lt (Nat.mod_lt _ hMpos)
  haveI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  apply Nat.ModEq.eq_of_lt_of_lt
  · rw [← ZMod.natCast_eq_natCast_iff]
    repeat rw [ZMod.natCast_mod]
    push_cast [Nat.cast_sub (Nat.le_of_lt hE), Nat.cast_sub hB]
    repeat rw [ZMod.natCast_mod]
    rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hE)]
    rw [show ((M : ZMod M) = 0) by simp]
    push_cast
    ring
  · exact Nat.mod_lt _ hMpos
  · exact Nat.mod_lt _ hMpos

theorem pcs_field_distrib (c e inv : U256) (he : e.toNat < Midfall.Yul.blsR) :
    wAddmodAt (wMulmodAt c inv (BitVec.ofNat 256 Midfall.Yul.blsR))
      (BitVec.ofNat 256 Midfall.Yul.blsR -
        wMulmodAt e inv (BitVec.ofNat 256 Midfall.Yul.blsR))
      (BitVec.ofNat 256 Midfall.Yul.blsR) =
    wMulmodAt
      (wAddmodAt c (BitVec.ofNat 256 Midfall.Yul.blsR - e)
        (BitVec.ofNat 256 Midfall.Yul.blsR))
      inv (BitVec.ofNat 256 Midfall.Yul.blsR) := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcs_wAddmodAt_toNat, pcs_wMulmodAt_toNat]
  have hei : (wMulmodAt e inv (BitVec.ofNat 256 Midfall.Yul.blsR)).toNat <
      Midfall.Yul.blsR := by
    rw [pcs_wMulmodAt_toNat]
    exact Nat.mod_lt _ (Fact.out (p := Nat.Prime Midfall.Yul.blsR)).pos
  rw [pcs_toNat_sub_of_lt_blsR hei, pcs_toNat_sub_of_lt_blsR he,
    pcs_wMulmodAt_toNat]
  exact pcs_nat_key c.toNat e.toNat inv.toNat Midfall.Yul.blsR he

/-- Loads from a `pcsWriteWords` image are canonical when every written value is. -/
theorem pcsLoadWord_writeWords_toNat_lt {mem : Nat → UInt8} {D : Nat} {v : Nat → U256}
    {n i : Nat} (hv : ∀ k, k < n → (v k).toNat < blsR) (hi : i < n) :
    (loadWord (pcsWriteWords mem D v n) (D + 32 * i)).toNat < blsR := by
  rw [pcsLoadWord_writeWords_lt mem D v hi]
  exact hv i hi

/-- A `b3FoldAcc` started from a canonical accumulator stays canonical: every update is an
    `addmod`, and untouched entries keep the initial value. -/
theorem b3FoldAcc_toNat_lt {rv : U256} (hrv : rv = BitVec.ofNat 256 blsR)
    {f : FoldPair → U256} {x1 : Nat → U256}
    {xs : List FoldPair} {k : Nat} {acc : U256} (hacc : acc.toNat < blsR) :
    (b3FoldAcc rv f x1 xs k acc).toNat < blsR := by
  subst rv
  induction xs generalizing acc with
  | nil => exact hacc
  | cons q rest ih =>
      rw [b3FoldAcc_cons]
      by_cases hq : q.2.1 = k
      · rw [if_pos hq]
        apply ih
        rw [pcs_wAddmodAt_toNat]
        exact Nat.mod_lt _ (Fact.out (p := Nat.Prime blsR)).pos
      · rw [if_neg hq]
        exact ih hacc

/-- The q_eval offset of a point set: the number of q_eval words in the sets before it. -/
def pcsSetOff (pointSets : List (List Int)) (setIdx : Nat) : Nat :=
  ((pointSets.take setIdx).map List.length).foldl (fun a b => a + b) 0

/-- The memory invariant block 4 needs: every q_eval word of every point set is canonical.
    Block 3 writes these words with `pcsWriteWords` from `addmod`/`mulmod` values. -/
def PcsQEvalCanon (qep : U256) (pointSets : List (List Int)) (st : EvmState) : Prop :=
  ∀ s, s < pointSets.length → ∀ j, j < (pointSets.getD s []).length →
    (loadWord st.memory
      (qep.toNat + (pcsSetOff pointSets s + j) * Midfall.Generator.wordBytes)).toNat < blsR

/-- One block-3 persist chunk: canonical stored values give canonical loads. -/
theorem pcsQEvalCanon_chunk {mem : Nat → UInt8} {R off m : Nat} {v : Nat → U256}
    (hv : ∀ j, j < m → (v j).toNat < blsR) :
    ∀ j, j < m →
      (loadWord (pcsWriteWords mem (R + off * 32) v m)
        (R + (off + j) * 32)).toNat < blsR := by
  intro j hj
  have h := pcsLoadWord_writeWords_toNat_lt (mem := mem) (D := R + off * 32)
    (v := v) (n := m) (i := j) hv hj
  convert h using 1
  ring

/-- Block 3 seeds, with the canonical-seed conjunct carried explicitly. -/
theorem b3_seeds_contract_canon {funs : FunEnv (Bridge.Dialect c g)} (n : Nat)
    (ev : Nat → Midfall.Generator.Word) (val : Nat → U256)
    (hvalLt : ∀ k, k < n → (val k).toNat < blsR) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      ((List.range n).map fun k => b3SeedStmt k (ev k))
      (fun V st => ((∀ k, k < n → b3word st V (ev k) = some (val k)) ∧
        (∀ k, k < n → ∀ (V₁ V₂ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState),
          b3word st₁ V₁ (ev k) = b3word st₁ V₂ (ev k))) ∧
        (∀ k, k < n → (val k).toNat < blsR))
      (fun V st V' st' o => (o = .normal ∧
        (∀ k, k < n → VEnv.get V' (qkey k) = some (val k)) ∧
        (∀ x, (∀ k, k < n → x ≠ qkey k) → VEnv.get V' x = VEnv.get V x) ∧
        st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted) ∧
        (∀ k, k < n → (val k).toNat < blsR)) := by
  intro V st hpre V' st' o hrun
  exact ⟨b3_seeds_contract n ev val V st hpre.1 V' st' o hrun, hpre.2⟩

/-- Block 3 folds, with canonical accumulator values in the pre and post. -/
theorem b3_folds_contract_canon {funs : FunEnv (Bridge.Dialect c g)} (n : Nat)
    (xs : List FoldPair) (init : Nat → U256) (f : FoldPair → U256) (x1 : Nat → U256)
    (pv rv : U256) (hrv : rv = BitVec.ofNat 256 blsR)
    (hinitLt : ∀ k, k < n → (init k).toNat < blsR) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (xs.map b3FoldStmt)
      (fun V st =>
        ((∀ k, k < n → VEnv.get V (qkey k) = some (init k)) ∧
        VEnv.get V "X1_POWERS_MPTR" = some pv ∧
        VEnv.get V "r" = some rv ∧
        (∀ p ∈ xs, b3word st V p.2.2 = some (f p)) ∧
        (∀ p ∈ xs, ∀ (V₁ V₂ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState),
          b3word st₁ V₁ p.2.2 = b3word st₁ V₂ p.2.2) ∧
        (∀ p ∈ xs, p.2.1 < n) ∧
        (∀ i, x1 i = loadWord st.memory (pv + BitVec.ofNat 256 (i * 32)).toNat)) ∧
        (∀ k, k < n → (init k).toNat < blsR))
      (fun V st V' st' o => (o = .normal ∧
        (∀ k, k < n → VEnv.get V' (qkey k) = some (b3FoldAcc rv f x1 xs k (init k))) ∧
        (∀ y, (∀ p ∈ xs, y ≠ qkey p.2.1) → VEnv.get V' y = VEnv.get V y) ∧
        st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted) ∧
        (∀ k, k < n → (b3FoldAcc rv f x1 xs k (init k)).toNat < blsR)) := by
  intro V st hpre V' st' o hrun
  refine ⟨b3_folds_contract n xs init f x1 pv rv V st hpre.1 V' st' o hrun, ?_⟩
  intro k hk
  exact b3FoldAcc_toNat_lt hrv (hinitLt k hk)

/-- Block 3 persist, with canonical stored values in the pre and canonical loads in the post. -/
theorem b3_persist_contract_canon {funs : FunEnv (Bridge.Dialect c g)} (n off R : Nat)
    (v : Nat → U256) (hR : R < 2 ^ 256)
    (hoff : (off + n) * 32 < 2 ^ 256) (hsum : R + (off + n) * 32 < 2 ^ 256)
    (hvLt : ∀ k, k < n → (v k).toNat < blsR) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      ((List.range n).map (b3PersistStmt off))
      (fun V _ =>
        (VEnv.get V "Q_EVAL_SET_MPTR" = some (BitVec.ofNat 256 R) ∧
          ∀ k, k < n → VEnv.get V (qkey k) = some (v k)) ∧
        (∀ k, k < n → (v k).toNat < blsR))
      (fun V st V' st' o => (o = .normal ∧ V' = V ∧
        st'.memory = pcsWriteWords st.memory (R + off * 32) v n ∧
        st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ a, a < R + off * 32 ∨ R + off * 32 + 32 * n ≤ a →
          st'.memory a = st.memory a)) ∧
        (∀ j, j < n →
          (loadWord st'.memory (R + (off + j) * 32)).toNat < blsR)) := by
  intro V st hpre V' st' o hrun
  refine ⟨b3_persist_contract n off R v hR hoff hsum V st hpre.1 V' st' o hrun, ?_⟩
  intro j hj
  rcases b3_persist_contract n off R v hR hoff hsum V st hpre.1 V' st' o hrun with
    ⟨ho, hV, hmem, henv, hhalt, hout⟩
  rw [hmem]
  exact pcsQEvalCanon_chunk (mem := st.memory) (R := R) (off := off) (m := n) (v := v)
    hvLt j hj

/-- `wMulmodAt` by the field one is the identity on canonical words. -/
theorem pcs_wMulmodAt_one_right {a : U256} (ha : a.toNat < blsR) :
    wMulmodAt a 1 (BitVec.ofNat 256 blsR) = a := by
  apply BitVec.eq_of_toNat_eq
  change (Midfall.LoweringV3.QuotientRows.wMulmodAt a 1 (BitVec.ofNat 256 blsR)).toNat
    = a.toNat
  rw [LagrangeRows.wMulmodAt_toNat (by decide) a 1]
  have h1 : (1 : U256).toNat = 1 := by decide
  rw [h1, Nat.mul_one, Nat.mod_eq_of_lt ha]

theorem pcs_wMulmodAt_one_left {a : U256} (ha : a.toNat < blsR) :
    wMulmodAt 1 a (BitVec.ofNat 256 blsR) = a := by
  rw [pcs_wMulmodAt_comm, pcs_wMulmodAt_one_right ha]

/-- A product of two canonical nonzero field words is nonzero. -/
theorem pcs_wMulmodAt_ne_zero {x y : U256}
    (hx : x.toNat < blsR) (hy : y.toNat < blsR)
    (hx0 : x.toNat ≠ 0) (hy0 : y.toNat ≠ 0) :
    wMulmodAt x y (BitVec.ofNat 256 blsR) ≠ 0 := by
  have hp : Nat.Prime (BitVec.ofNat 256 blsR).toNat :=
    Midfall.LoweringV3.ModexpGeneral.prime_BlsR_toNat
  have hxt : x.toNat < (BitVec.ofNat 256 blsR).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; exact hx
  have hyt : y.toNat < (BitVec.ofNat 256 blsR).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; exact hy
  change Midfall.LoweringV3.QuotientRows.wMulmodAt x y (BitVec.ofNat 256 blsR) ≠ 0
  rw [Midfall.LoweringV3.BatchInvert.wMulmodAt_ne_zero_iff hp hxt hyt]
  exact ⟨fun h => hx0 (by rw [h]; rfl), fun h => hy0 (by rw [h]; rfl)⟩

/-- `SIInv` lands in the canonical field range. -/
theorem pcsSIInv_toNat_lt (x : U256) : (SIInv x).toNat < blsR := by
  unfold SIInv
  rw [BitVec.toNat_ofNat]
  have h := ZMod.val_lt ((x.toNat : ZMod blsR)⁻¹)
  rw [Nat.mod_eq_of_lt (lt_trans h (by decide : blsR < 2 ^ 256))]
  exact h

/-- Inverting a product recovers the inverse of the left factor. -/
theorem pcs_inv_mul_left {prev a bp : U256}
    (hbp : bp = wMulmodAt prev a (BitVec.ofNat 256 blsR))
    (hprev : prev.toNat < blsR)
    (hprev0 : prev.toNat ≠ 0) :
    wMulmodAt (SIInv bp) prev (BitVec.ofNat 256 blsR) = SIInv a := by
  have hinv : SIInv bp = wMulmodAt (SIInv prev) (SIInv a) (BitVec.ofNat 256 blsR) := by
    rw [hbp, pcsSIInv_wMulmod]
  rw [hinv, pcs_wMulmodAt_assoc]
  rw [pcs_wMulmodAt_comm (a := SIInv a) (b := prev)]
  rw [← pcs_wMulmodAt_assoc]
  rw [pcsSIInv_mul prev hprev0 hprev]
  exact pcs_wMulmodAt_one_left (pcsSIInv_toNat_lt a)

/-- Inverting a product recovers the inverse of the right factor. -/
theorem pcs_inv_mul_right {prev a bp : U256}
    (hbp : bp = wMulmodAt prev a (BitVec.ofNat 256 blsR))
    (ha : a.toNat < blsR)
    (ha0 : a.toNat ≠ 0) :
    wMulmodAt (SIInv bp) a (BitVec.ofNat 256 blsR) = SIInv prev := by
  have hinv : SIInv bp = wMulmodAt (SIInv prev) (SIInv a) (BitVec.ofNat 256 blsR) := by
    rw [hbp, pcsSIInv_wMulmod]
  rw [hinv, pcs_wMulmodAt_assoc]
  rw [pcsSIInv_mul a ha0 ha]
  exact pcs_wMulmodAt_one_right (pcsSIInv_toNat_lt prev)

/-- The running product `bp_i` stays canonical. -/
theorem pcsBpVal_toNat_lt (a : Nat → U256) (N : Nat)
    (hlt : ∀ i, i ≤ N → (a i).toNat < blsR) :
    ∀ i, i ≤ N → (pcsBpVal (BitVec.ofNat 256 blsR) a i).toNat < blsR
  | 0, _ => by simpa [pcsBpVal] using hlt 0 (by omega)
  | _ + 1, _ => by
      rw [pcsBpVal_succ]
      exact pcs_wMulmodAt_toNat_lt

/-- The running product `bp_i` stays nonzero when every input is. -/
theorem pcsBpVal_ne_zero (a : Nat → U256) (N : Nat)
    (hlt : ∀ i, i ≤ N → (a i).toNat < blsR)
    (h0 : ∀ i, i ≤ N → (a i).toNat ≠ 0) :
    ∀ i, i ≤ N → pcsBpVal (BitVec.ofNat 256 blsR) a i ≠ 0
  | 0, _ => by
      intro h
      have h' : (a 0).toNat = 0 := by
        rw [show a 0 = 0 by simpa [pcsBpVal] using h]
        rfl
      exact h0 0 (by omega) h'
  | i + 1, hi => by
      rw [pcsBpVal_succ]
      exact pcs_wMulmodAt_ne_zero (pcsBpVal_toNat_lt a N hlt i (by omega))
        (hlt (i + 1) hi)
        (fun h => pcsBpVal_ne_zero a N hlt h0 i (by omega)
          (BitVec.eq_of_toNat_eq (by rw [h]; rfl)))
        (h0 (i + 1) hi)

/-- One `bq` step: `let inv_i := mulmod(bq, bp_{i-1}, r)` then `bq := mulmod(bq, input_i, r)`. -/
def pcsBqStep (i : Nat) (prev inp : String) (invName : Nat → String) : Block EVM.Op :=
  [ GenAst.ylet (invName i) (GenAst.yop EVM.Op.mulmod
      [GenAst.yvar "bq", GenAst.yvar prev, GenAst.yvar "r"]),
    GenAst.yset "bq" (GenAst.yop EVM.Op.mulmod
      [GenAst.yvar "bq", GenAst.yvar inp, GenAst.yvar "r"]) ]

/-- The emitted backward `bq` walk. -/
def pcsBqLines (n : Nat) (nm invName : Nat → String) : Block EVM.Op :=
  ((List.range n).drop 1).reverse.flatMap fun i =>
    pcsBqStep i (pcsBpName (i - 1)) (nm i) invName

theorem pcsBqLines_succ (n : Nat) (hn : 1 ≤ n) (nm invName : Nat → String) :
    pcsBqLines (n + 1) nm invName =
      pcsBqStep n (pcsBpName (n - 1)) (nm n) invName ++ pcsBqLines n nm invName := by
  unfold pcsBqLines
  rw [List.range_succ]
  rw [List.drop_append_of_le_length (by simpa using hn)]
  simp only [List.reverse_append, List.reverse_singleton, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Append two chunks when the first cannot halt. -/
theorem pcsStmtsContractAll_append_normal {funs : FunEnv (Bridge.Dialect c g)}
    {ss1 ss2 : Block EVM.Op}
    {pre mid : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop}
    (h1 : StmtsContractAll (D := Bridge.Dialect c g) funs ss1 pre
      (fun V st V' st' o => o = .normal ∧ mid V' st'))
    (h2 : ∀ V st, pre V st → StmtsContractAll (D := Bridge.Dialect c g) funs ss2 mid
      (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (ss1 ++ ss2) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1run, h2run⟩ | ⟨h1run, hne⟩
  · exact h2 V st hpre V1 st1 (h1 V st hpre V1 st1 .normal h1run).2 V' st' o h2run
  · exact absurd (h1 V st hpre V' st' o h1run).1 hne

/-- One backward step runs normally and binds the inverse of the factor. -/
theorem pcsBqStep_contract {funs : FunEnv (Bridge.Dialect c g)}
    (i : Nat) (prev inp : String) (invName : Nat → String)
    (bq0 bpv av rv : U256)
    (h1 : invName i ≠ "bq") (h2 : invName i ≠ prev) (h3 : invName i ≠ inp)
    (h4 : invName i ≠ "r") :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsBqStep i prev inp invName)
      (fun V st => VEnv.get V "bq" = some bq0 ∧ VEnv.get V prev = some bpv ∧
        VEnv.get V inp = some av ∧ VEnv.get V "r" = some rv)
      (fun V st V' st' o => o = .normal ∧
        VEnv.get V' (invName i) = some (wMulmodAt bq0 bpv rv) ∧
        VEnv.get V' "bq" = some (wMulmodAt bq0 av rv) ∧
        (∀ y, y ≠ invName i → y ≠ "bq" → VEnv.get V' y = VEnv.get V y) ∧
        st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hbq, hbp, hinp, hr⟩ := hpre
  unfold pcsBqStep at hrun
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, hhead, hrest⟩ | ⟨hhead, hne⟩
  · obtain ⟨ho1, xv, yv, zv, hx, hy, hz, hV1, hst1⟩ :=
      b1_exec_ylet_mulmod_vars hhead
    have hxe : xv = bq0 := Option.some.inj (hx.symm.trans hbq)
    have hye : yv = bpv := Option.some.inj (hy.symm.trans hbp)
    have hze : zv = rv := Option.some.inj (hz.symm.trans hr)
    rw [hV1] at hrest
    rw [hst1] at hrest
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest with
        ⟨V2, st2, htail, hnil⟩ | ⟨htail, hne2⟩
    · cases hnil
      obtain ⟨ho2, av', bv', zv', ha', hb', hz', hV2, hst2⟩ :=
        b1_exec_yset_mulmod htail
      have hae : av' = bq0 := by
        have h := ha'
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := invName i) (y := "bq")
          (v := wMulmodAt xv yv zv) h1.symm] at h
        exact Option.some.inj (h.symm.trans hbq)
      have hbe : bv' = av := by
        have h := hb'
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := invName i) (y := inp)
          (v := wMulmodAt xv yv zv) h3.symm] at h
        exact Option.some.inj (h.symm.trans hinp)
      have hze' : zv' = rv := by
        have h := hz'
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := invName i) (y := "r")
          (v := wMulmodAt xv yv zv) h4.symm] at h
        exact Option.some.inj (h.symm.trans hr)
      refine ⟨ho2, ?_, ?_, ?_, hst2⟩
      · rw [hV2]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "bq") (y := invName i)
          (v := wMulmodAt av' bv' zv') h1]
        rw [venv_get_cons_self (D := Bridge.Dialect c g)]
        rw [hxe, hye, hze]
      · rw [hV2]
        rw [venv_get_set_same (D := Bridge.Dialect c g)
          (v := bq0) (w := wMulmodAt av' bv' zv')
          (by
            rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := invName i) (y := "bq")
              (v := wMulmodAt xv yv zv) h1.symm]
            exact hbq)]
        rw [hae, hbe, hze']
      · intro y hyinv hybq
        rw [hV2]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "bq") (y := y)
          (v := wMulmodAt av' bv' zv') hybq]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := invName i) (y := y)
          (v := wMulmodAt xv yv zv) hyinv]
    · exact absurd (b1_exec_yset_mulmod htail).1 hne2
  · exact absurd (b1_exec_ylet_mulmod_vars hhead).1 hne

set_option maxHeartbeats 1200000 in
/-- **THE `bqLines` FOLD.** Starting at `bq = bp_{n-1}⁻¹`, the backward walk binds every
    `inv_i = input_i⁻¹` and leaves `bq = input_0⁻¹`; nothing else moves. -/
theorem pcsBqLines_contract {funs : FunEnv (Bridge.Dialect c g)}
    (n : Nat) (nm invName : Nat → String) (a : Nat → U256)
    (hn : 1 ≤ n)
    (hlt : ∀ i, i < n → (a i).toNat < blsR)
    (h0 : ∀ i, i < n → (a i).toNat ≠ 0)
    (hbqNeR : "bq" ≠ "r")
    (hinvBq : ∀ i, 1 ≤ i → i < n → invName i ≠ "bq")
    (hinvPrev : ∀ i, 1 ≤ i → i < n → invName i ≠ pcsBpName (i - 1))
    (hinvInp : ∀ i, 1 ≤ i → i < n → invName i ≠ nm i)
    (hinvR : ∀ i, 1 ≤ i → i < n → invName i ≠ "r")
    (hbqNotBp : ∀ i < n, pcsBpName i ≠ "bq")
    (hbqNotInp : ∀ i < n, nm i ≠ "bq")
    (hinvNotBp : ∀ i, 1 ≤ i → i < n → ∀ j < n, pcsBpName j ≠ invName i)
    (hinvNotInp : ∀ i, 1 ≤ i → i < n → ∀ j < n, nm j ≠ invName i)
    (hrNotInv : ∀ i, 1 ≤ i → i < n → "r" ≠ invName i)
    (hinvDist : ∀ i, 1 ≤ i → i < n → ∀ j, 1 ≤ j → j < n → i ≠ j →
      invName i ≠ invName j) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsBqLines n nm invName)
      (fun V st => VEnv.get V "bq" = some (SIInv (pcsBpVal (BitVec.ofNat 256 blsR) a (n - 1))) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 blsR) ∧
        (∀ i, i < n → VEnv.get V (pcsBpName i) = some (pcsBpVal (BitVec.ofNat 256 blsR) a i)) ∧
        (∀ i, i < n → VEnv.get V (nm i) = some (a i)))
      (fun V st V' st' o => o = .normal ∧
        VEnv.get V' "bq" = some (SIInv (a 0)) ∧
        (∀ i, 1 ≤ i → i < n → VEnv.get V' (invName i) = some (SIInv (a i))) ∧
        (∀ y, y ≠ "bq" → (∀ i, 1 ≤ i → i < n → y ≠ invName i) →
          VEnv.get V' y = VEnv.get V y) ∧
        st' = st) := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          intro V st hpre V' st' o hrun
          have hshape : pcsBqLines 1 nm invName = [] := by
            unfold pcsBqLines
            rfl
          rw [hshape] at hrun
          cases hrun
          obtain ⟨hbq, _hr, _hbp, _hinp⟩ := hpre
          refine ⟨rfl, ?_, ?_, ?_, rfl⟩
          · simpa [pcsBpVal] using hbq
          · intro i hi1 hin
            omega
          · intro y _ _
            rfl
      | succ m =>
          intro V st hpre V' st' o hrun
          obtain ⟨hbq, hr, hbp, hinp⟩ := hpre
          have hshape : pcsBqLines (m + 2) nm invName =
              pcsBqStep (m + 1) (pcsBpName ((m + 1) - 1)) (nm (m + 1)) invName
                ++ pcsBqLines (m + 1) nm invName :=
            pcsBqLines_succ (m + 1) (by omega) nm invName
          rw [hshape] at hrun
          rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
              ⟨V1, st1, hstep, hrest⟩ | ⟨hstep, hne⟩
          · have hbpN : VEnv.get V (pcsBpName ((m + 1) - 1)) =
                some (pcsBpVal (BitVec.ofNat 256 blsR) a ((m + 1) - 1)) := by
              simpa using hbp (m + 1 - 1) (by omega)
            have hinpN : VEnv.get V (nm (m + 1)) = some (a (m + 1)) :=
              hinp (m + 1) (by omega)
            have hstepc := pcsBqStep_contract (c := c) (g := g) (funs := funs)
              (m + 1) (pcsBpName ((m + 1) - 1)) (nm (m + 1)) invName
              (SIInv (pcsBpVal (BitVec.ofNat 256 blsR) a (m + 1)))
              (pcsBpVal (BitVec.ofNat 256 blsR) a ((m + 1) - 1)) (a (m + 1))
              (BitVec.ofNat 256 blsR)
              (hinvBq (m + 1) (by omega) (by omega))
              (hinvPrev (m + 1) (by omega) (by omega))
              (hinvInp (m + 1) (by omega) (by omega))
              (hinvR (m + 1) (by omega) (by omega))
              V st ⟨by simpa using hbq, hbpN, hinpN, hr⟩ V1 st1 .normal hstep
            obtain ⟨ho1, hinvNew, hbqNew, hpres1, hst1⟩ := hstepc
            have hbpSucc : pcsBpVal (BitVec.ofNat 256 blsR) a (m + 1) =
                wMulmodAt (pcsBpVal (BitVec.ofNat 256 blsR) a m) (a (m + 1))
                  (BitVec.ofNat 256 blsR) := by
              simpa using pcsBpVal_succ (BitVec.ofNat 256 blsR) a m
            have hprevEq : pcsBpVal (BitVec.ofNat 256 blsR) a ((m + 1) - 1) =
                pcsBpVal (BitVec.ofNat 256 blsR) a m := by rw [Nat.add_sub_cancel]
            have hvalNew : VEnv.get V1 (invName (m + 1)) = some (SIInv (a (m + 1))) := by
              rw [hinvNew, hprevEq]
              rw [pcs_inv_mul_left hbpSucc
                (pcsBpVal_toNat_lt a (m + 1) (fun i hi => hlt i (by omega)) m (by omega))
                (fun h => pcsBpVal_ne_zero a (m + 1)
                  (fun i hi => hlt i (by omega)) (fun i hi => h0 i (by omega)) m (by omega)
                  (BitVec.eq_of_toNat_eq (by rw [h]; rfl)))]
            have hbqNew' : VEnv.get V1 "bq" =
                some (SIInv (pcsBpVal (BitVec.ofNat 256 blsR) a m)) := by
              rw [hbqNew, pcs_inv_mul_right hbpSucc
                (hlt (m + 1) (by omega)) (h0 (m + 1) (by omega))]
            have hr1 : VEnv.get V1 "r" = some (BitVec.ofNat 256 blsR) := by
              rw [hpres1 "r" (hrNotInv (m + 1) (by omega) (by omega)) hbqNeR.symm]
              exact hr
            have hbp1 : ∀ i, i < m + 1 →
                VEnv.get V1 (pcsBpName i) = some (pcsBpVal (BitVec.ofNat 256 blsR) a i) := by
              intro i hi
              rw [hpres1 (pcsBpName i)
                (hinvNotBp (m + 1) (by omega) (by omega) i (by omega))
                (hbqNotBp i (by omega))]
              exact hbp i (by omega)
            have hinp1 : ∀ i, i < m + 1 → VEnv.get V1 (nm i) = some (a i) := by
              intro i hi
              rw [hpres1 (nm i)
                (hinvNotInp (m + 1) (by omega) (by omega) i (by omega))
                (hbqNotInp i (by omega))]
              exact hinp i (by omega)
            have hrestc := ih (by omega) (fun i hi => hlt i (by omega))
              (fun i hi => h0 i (by omega))
              (fun i hi1 hin => hinvBq i (by omega) (by omega))
              (fun i hi1 hin => hinvPrev i (by omega) (by omega))
              (fun i hi1 hin => hinvInp i (by omega) (by omega))
              (fun i hi1 hin => hinvR i (by omega) (by omega))
              (fun i hi => hbqNotBp i (by omega))
              (fun i hi => hbqNotInp i (by omega))
              (fun i hi1 hin j hj => hinvNotBp i (by omega) (by omega) j (by omega))
              (fun i hi1 hin j hj => hinvNotInp i (by omega) (by omega) j (by omega))
              (fun i hi1 hin => hrNotInv i (by omega) (by omega))
              (fun i hi1 hin j hj1 hjn hij => hinvDist i (by omega) (by omega)
                j (by omega) (by omega) (by omega))
              V1 st1 ⟨hbqNew', hr1, hbp1, hinp1⟩ V' st' o hrest
            obtain ⟨ho2, hbqFinal, hinvRest, hpres2, hst2⟩ := hrestc
            refine ⟨ho2, hbqFinal, ?_, ?_, by rw [hst2, hst1]⟩
            · intro i hi1 hin
              rcases Nat.lt_or_eq_of_le (by omega : i ≤ m + 1) with hilt | rfl
              · exact hinvRest i hi1 hilt
              · rw [hpres2 (invName (m + 1))
                  (hinvBq (m + 1) (by omega) (by omega))
                  (fun j hj1 hjn => hinvDist (m + 1) (by omega) (by omega)
                    j hj1 (by omega) (by omega))]
                exact hvalNew
            · intro y hybq hyinv
              rw [hpres2 y hybq (fun i hi1 hin => hyinv i hi1 (by omega))]
              exact hpres1 y (hyinv (m + 1) (by omega) (by omega)) hybq
          · exact absurd (pcsBqStep_contract (c := c) (g := g) (funs := funs)
              (m + 1) (pcsBpName ((m + 1) - 1)) (nm (m + 1)) invName
              (SIInv (pcsBpVal (BitVec.ofNat 256 blsR) a (m + 1)))
              (pcsBpVal (BitVec.ofNat 256 blsR) a ((m + 1) - 1)) (a (m + 1))
              (BitVec.ofNat 256 blsR)
              (hinvBq (m + 1) (by omega) (by omega))
              (hinvPrev (m + 1) (by omega) (by omega))
              (hinvInp (m + 1) (by omega) (by omega))
              (hinvR (m + 1) (by omega) (by omega))
              V st ⟨by simpa using hbq, hbp (m + 1 - 1) (by omega), hinp (m + 1) (by omega), hr⟩
              V' st' o hstep).1 hne

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_wMulmodAt_one_right
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_wMulmodAt_one_left
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_wMulmodAt_ne_zero
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsSIInv_toNat_lt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_inv_mul_left
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcs_inv_mul_right
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpVal_toNat_lt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBpVal_ne_zero
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBqStep [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBqLines [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBqLines_succ
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsStmtsContractAll_append_normal
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBqStep_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsBqLines_contract
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

theorem pcsStmtsContractAll_append_mid {funs : FunEnv (Bridge.Dialect c g)}
    {ss1 ss2 : Block EVM.Op}
    {pre : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {mid : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop}
    (h1 : StmtsContractAll (D := Bridge.Dialect c g) funs ss1 pre
      (fun V st V' st' o => o = .normal ∧ mid V st V' st' ∧ st' = st))
    (h2 : ∀ V st, pre V st → StmtsContractAll (D := Bridge.Dialect c g) funs ss2
      (fun V' st' => mid V st V' st')
      (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (ss1 ++ ss2) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1run, h2run⟩ | ⟨h1run, hne⟩
  · obtain ⟨_, hmid, hst⟩ := h1 V st hpre V1 st1 .normal h1run
    exact h2 V st hpre V1 st1 hmid V' st' o h2run
  · exact absurd (h1 V st hpre V' st' o h1run).1 hne

def pcsDenInvVal (rv : U256) (f : Nat → U256) : Nat → U256
  | 0 => 1
  | k + 1 => wMulmodAt (pcsDenInvVal rv f k) (f k) rv


theorem pcsSIInv_one : SIInv (1 : U256) = 1 := by
  unfold SIInv
  rw [show (1 : U256).toNat = 1 by decide]
  simp [ZMod.val_one]

theorem pcsDenInvVal_one (f : Nat → U256)
    (hf : (f 0).toNat < blsR) :
    pcsDenInvVal (BitVec.ofNat 256 blsR) f 1 = f 0 := by
  simp [pcsDenInvVal]
  exact pcs_wMulmodAt_one_left hf

def pcsDenInvSetStmt (j : Nat) (invName : Nat → String) : Stmt EVM.Op :=
  GenAst.yset "den_inv" (GenAst.yop EVM.Op.mulmod
    [GenAst.yvar "den_inv", GenAst.yvar (invName j), GenAst.yvar "r"])

def pcsDenInvLines (m : Nat) (invName : Nat → String) : Block EVM.Op :=
  [GenAst.ylet "den_inv" (GenAst.yvar (invName 0))] ++
    ((List.range m).drop 1).map (fun j => pcsDenInvSetStmt j invName)

theorem pcsDenInvLines_succ (m : Nat) (hm : 1 ≤ m) (invName : Nat → String) :
    pcsDenInvLines (m + 1) invName =
      pcsDenInvLines m invName ++ [pcsDenInvSetStmt m invName] := by
  unfold pcsDenInvLines
  rw [List.range_succ]
  rw [List.drop_append_of_le_length (by simpa using hm)]
  simp only [List.map_append, List.map_singleton, List.append_assoc]

theorem pcsDenInvHead_contract {funs : FunEnv (Bridge.Dialect c g)}
    (invName : Nat → String) (inv0 : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (GenAst.ylet "den_inv" (GenAst.yvar (invName 0)))
      (fun V st => VEnv.get V (invName 0) = some inv0)
      (fun V st V' st' o => o = .normal ∧ V' = ("den_inv", inv0) :: V ∧
        VEnv.get V' "den_inv" = some inv0 ∧
        (∀ y, y ≠ "den_inv" → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨ho, yv, hyv, hV, hst⟩ := b1_exec_ylet_var hrun
  have hye : yv = inv0 := Option.some.inj (hyv.symm.trans hpre)
  refine ⟨ho, by rw [hV, hye], by rw [hV, hye]; exact venv_get_cons_self _ _ _,
    ?_, hst⟩
  intro y hy
  rw [hV]
  exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := "den_inv") (y := y)
    (v := yv) hy

theorem pcsDenInvSet_contract {funs : FunEnv (Bridge.Dialect c g)}
    (j : Nat) (invName : Nat → String) (acc invj rv : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs (pcsDenInvSetStmt j invName)
      (fun V st => VEnv.get V "den_inv" = some acc ∧
        VEnv.get V (invName j) = some invj ∧ VEnv.get V "r" = some rv)
      (fun V st V' st' o => o = .normal ∧
        VEnv.get V' "den_inv" = some (wMulmodAt acc invj rv) ∧
        (∀ y, y ≠ "den_inv" → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hacc, hinv, hrv⟩ := hpre
  obtain ⟨ho, av, bv, zv, ha, hb, hz, hV, hst⟩ := b1_exec_yset_mulmod hrun
  have hae : av = acc := Option.some.inj (ha.symm.trans hacc)
  have hbe : bv = invj := Option.some.inj (hb.symm.trans hinv)
  have hze : zv = rv := Option.some.inj (hz.symm.trans hrv)
  refine ⟨ho, ?_, ?_, hst⟩
  · rw [hV, hae, hbe, hze]
    exact venv_get_set_same (D := Bridge.Dialect c g) hacc
  · intro y hy
    rw [hV]
    exact venv_get_set_ne (D := Bridge.Dialect c g) (x := "den_inv") (y := y)
      (v := wMulmodAt av bv zv) hy

set_option maxHeartbeats 1200000 in
theorem pcsDenInvLines_contract {funs : FunEnv (Bridge.Dialect c g)}
    (m : Nat) (invName : Nat → String) (a : Nat → U256) (hm : 1 ≤ m)
    (hne : ∀ j < m, "den_inv" ≠ invName j)
    (hneR : "den_inv" ≠ "r") :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsDenInvLines m invName)
      (fun V st => VEnv.get V "r" = some (BitVec.ofNat 256 blsR) ∧
        (∀ j < m, VEnv.get V (invName j) = some (SIInv (a j))))
      (fun V st V' st' o => o = .normal ∧
        VEnv.get V' "den_inv" =
          some (pcsDenInvVal (BitVec.ofNat 256 blsR) (fun j => SIInv (a j)) m) ∧
        (∀ y, y ≠ "den_inv" → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          intro V st hpre V' st' o hrun
          obtain ⟨hr, hinv⟩ := hpre
          have hshape : pcsDenInvLines 1 invName =
              [GenAst.ylet "den_inv" (GenAst.yvar (invName 0))] := by
            unfold pcsDenInvLines
            rfl
          rw [hshape] at hrun
          obtain ⟨ho, hV, hget, hpres, hst⟩ :=
            stmtsContractAll_singleton
              (pcsDenInvHead_contract (c := c) (g := g) (funs := funs) invName
                (SIInv (a 0))) V st (hinv 0 (by omega)) V' st' o hrun
          refine ⟨ho, ?_, ?_, hst⟩
          · rw [hget]
            congr 1
            show SIInv (a 0) = pcsDenInvVal (BitVec.ofNat 256 blsR) (fun j => SIInv (a j)) 1
            simp only [pcsDenInvVal]
            exact (pcs_wMulmodAt_one_left (pcsSIInv_toNat_lt (a 0))).symm
          · intro y hy
            exact hpres y hy
      | succ m =>
          intro V st hpre V' st' o hrun
          obtain ⟨hr, hinv⟩ := hpre
          have hshape : pcsDenInvLines (m + 2) invName =
              pcsDenInvLines (m + 1) invName ++ [pcsDenInvSetStmt (m + 1) invName] :=
            pcsDenInvLines_succ (m + 1) (by omega) invName
          rw [hshape] at hrun
          have hpre1 : VEnv.get V "r" = some (BitVec.ofNat 256 blsR) ∧
              (∀ j < m + 1, VEnv.get V (invName j) = some (SIInv (a j))) :=
            ⟨hr, fun j hj => hinv j (by omega)⟩
          refine pcsStmtsContractAll_append_mid
            (c := c) (g := g) (funs := funs)
            (ss1 := pcsDenInvLines (m + 1) invName)
            (ss2 := [pcsDenInvSetStmt (m + 1) invName])
            (pre := fun V st => VEnv.get V "r" = some (BitVec.ofNat 256 blsR) ∧
              (∀ j < m + 2, VEnv.get V (invName j) = some (SIInv (a j))))
            (mid := fun V0 st0 V1 st1 => VEnv.get V1 "den_inv" =
                some (pcsDenInvVal (BitVec.ofNat 256 blsR) (fun j => SIInv (a j)) (m + 1)) ∧
              (∀ y, y ≠ "den_inv" → VEnv.get V1 y = VEnv.get V0 y) ∧
              VEnv.get V1 "r" = some (BitVec.ofNat 256 blsR) ∧
              VEnv.get V1 (invName (m + 1)) = some (SIInv (a (m + 1))) ∧
              st1 = st0)
            (post := fun V st V' st' o => o = .normal ∧
              VEnv.get V' "den_inv" =
                some (pcsDenInvVal (BitVec.ofNat 256 blsR) (fun j => SIInv (a j)) (m + 2)) ∧
              (∀ y, y ≠ "den_inv" → VEnv.get V' y = VEnv.get V y) ∧ st' = st)
            ?_ ?_ V st ⟨hr, hinv⟩ V' st' o hrun
          · -- first chunk
            intro V0 st0 h0 V1 st1 o1 h1
            have h0' : VEnv.get V0 "r" = some (BitVec.ofNat 256 blsR) ∧
                (∀ j < m + 1, VEnv.get V0 (invName j) = some (SIInv (a j))) :=
              ⟨h0.1, fun j hj => h0.2 j (by omega)⟩
            have hih := ih (by omega) (fun j hj => hne j (by omega))
              V0 st0 h0' V1 st1 o1 h1
            obtain ⟨ho1, hden1, hpres1, hst1⟩ := hih
            refine ⟨ho1, ?_, hst1⟩
            refine ⟨hden1, hpres1, ?_, ?_, hst1⟩
            · rw [hpres1 "r" hneR.symm]
              exact h0.1
            · rw [hpres1 (invName (m + 1)) (hne (m + 1) (by omega)).symm]
              exact h0.2 (m + 1) (by omega)
          · -- the final set step
            intro V0 st0 _hpre V1 st1 hmid V2 st2 o2 hrun2
            obtain ⟨hden0, hpres0, hr0, hinv0, hst10⟩ := hmid
            have hset := stmtsContractAll_singleton
              (pcsDenInvSet_contract (c := c) (g := g) (funs := funs)
                (m + 1) invName
                (pcsDenInvVal (BitVec.ofNat 256 blsR) (fun j => SIInv (a j)) (m + 1))
                (SIInv (a (m + 1))) (BitVec.ofNat 256 blsR))
              V1 st1 ⟨hden0, hinv0, hr0⟩ V2 st2 o2 hrun2
            obtain ⟨ho2, hden2, hpres2, hst2⟩ := hset
            refine ⟨ho2, ?_, ?_, by rw [hst2, hst10]⟩
            · simpa [pcsDenInvVal] using hden2
            · intro y hy
              rw [hpres2 y hy]
              exact hpres0 y hy

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvVal [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvSetStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvLines [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvLines_succ
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvHead_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvSet_contract
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsDenInvLines_contract
  [propext, Classical.choice, Quot.sound] native []


theorem b1_eval_mulmod_cdl_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {qc x y : String} {off : Nat}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.calldataload
           [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit off]],
         GenAst.yvar x, GenAst.yvar y]) (.vals [cv] st')) :
    ∃ cptr xv yv, VEnv.get V qc = some cptr ∧ VEnv.get V x = some xv ∧
      VEnv.get V y = some yv ∧
      cv = wMulmodAt (wordFrom st.env.calldata (cptr + BitVec.ofNat 256 off).toNat) xv yv ∧
      st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hcdl =>
      cases hrest with
      | argsCons hrest2 hx =>
          cases hrest2 with
          | argsCons hnil hy =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hyv, hsty⟩ := b1_eval_var_inv hy
                  obtain ⟨hxv, hstx⟩ := b1_eval_var_inv hx
                  obtain ⟨cptr, hcptr, hcdlVal, hstc⟩ :=
                    b1_eval_calldataload_add_var_lit_inv hcdl
                  have hstx' : _ = st := hstx.trans hsty
                  have hout : _ = st := hstc.trans hstx'
                  rw [hstx'] at hcdlVal
                  rw [hout] at hbi
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨cptr, _, _, hcptr, hxv, hyv, by rw [hcdlVal, Midfall.LoweringV3.PcsRows.wMulmodAt], rfl⟩

theorem b1_eval_mulmod_cdl_add_var_lit_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {qc x y : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.calldataload
           [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit off]],
         GenAst.yvar x, GenAst.yvar y]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hcdl =>
          cases hrest with
          | argsCons hrest2 hx =>
              cases hrest2 with
              | argsCons hnil hy =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact b1_eval_calldataload_add_var_lit_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

theorem b1_exec_ylet_mulmod_cdl_var {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x qc y z : String} {off : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.calldataload
           [GenAst.yop EVM.Op.add [GenAst.yvar qc, GenAst.ylit off]],
         GenAst.yvar y, GenAst.yvar z])) V' st' o) :
    o = .normal ∧ ∃ cptr yv zv,
      VEnv.get V qc = some cptr ∧ VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      V' = (x, wMulmodAt
        (wordFrom st.env.calldata (cptr + BitVec.ofNat 256 off).toNat) yv zv) :: V ∧
      st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨cptr, yv, zv, hc, hy, hz, hcv, hst⟩ :=
        b1_eval_mulmod_cdl_add_var_lit_inv he
      subst hcv; subst hst
      exact ⟨rfl, cptr, yv, zv, hc, hy, hz, by simp [VEnv.setMany], rfl⟩
  | letHalt he => exact (b1_eval_mulmod_cdl_add_var_lit_halt he).elim

/-- The `eval := proofEval * den_inv` line of the general set arm. -/
def pcsEvalStmt (setIdx : Nat) : Stmt EVM.Op :=
  GenAst.ylet "eval" (GenAst.yop EVM.Op.mulmod
    [GenAst.yop EVM.Op.calldataload
       [GenAst.yop EVM.Op.add
         [GenAst.yvar "Q_EVAL_CPTR", GenAst.ylit (setIdx * Midfall.Generator.wordBytes)]],
     GenAst.yvar "den_inv", GenAst.yvar "r"])

theorem pcsEval_contract {funs : FunEnv (Bridge.Dialect c g)}
    (setIdx : Nat) (den cptr rv : U256)
    (hb : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256) :
    StmtContractAll (D := Bridge.Dialect c g) funs (pcsEvalStmt setIdx)
      (fun V st => VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
        VEnv.get V "den_inv" = some den ∧ VEnv.get V "r" = some rv)
      (fun V st V' st' o => o = .normal ∧
        V' = ("eval", wMulmodAt (wordFrom st.env.calldata
          (cptr.toNat + setIdx * Midfall.Generator.wordBytes)) den rv) :: V ∧
        VEnv.get V' "eval" = some (wMulmodAt (wordFrom st.env.calldata
          (cptr.toNat + setIdx * Midfall.Generator.wordBytes)) den rv) ∧
        (∀ y, y ≠ "eval" → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hcptr, hden, hrv⟩ := hpre
  obtain ⟨ho, cptr', yv, zv, hc, hy, hz, hV, hst⟩ :=
    b1_exec_ylet_mulmod_cdl_var hrun
  have hce : cptr' = cptr := Option.some.inj (hc.symm.trans hcptr)
  have hye : yv = den := Option.some.inj (hy.symm.trans hden)
  have hze : zv = rv := Option.some.inj (hz.symm.trans hrv)
  have haddr : (cptr' + BitVec.ofNat 256
        (setIdx * Midfall.Generator.wordBytes)).toNat =
      cptr.toNat + setIdx * Midfall.Generator.wordBytes := by
    rw [hce, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : setIdx * Midfall.Generator.wordBytes < 2 ^ 256),
      Nat.mod_eq_of_lt hb]
  have hval : wMulmodAt (wordFrom st.env.calldata
        (cptr' + BitVec.ofNat 256 (setIdx * Midfall.Generator.wordBytes)).toNat) yv zv =
      wMulmodAt (wordFrom st.env.calldata
        (cptr.toNat + setIdx * Midfall.Generator.wordBytes)) den rv := by
    rw [haddr, hye, hze]
  refine ⟨ho, ?_, ?_, ?_, hst⟩
  · rw [hV, hval]
  · rw [hV, hval]
    exact venv_get_cons_self (D := Bridge.Dialect c g) V _ _
  · intro y hy
    rw [hV]
    exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := "eval") (y := y)
      (v := _) hy

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_cdl_add_var_lit_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_cdl_add_var_lit_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_ylet_mulmod_cdl_var
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsEvalStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsEval_contract
  [propext, Classical.choice, Quot.sound] native []


theorem b1_eval_mulmod_mload_add_var_lit_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q a z : String} {off : Nat}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.mload
           [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]],
         GenAst.yvar a, GenAst.yvar z]) (.vals [cv] st')) :
    ∃ qv av zv, VEnv.get V q = some qv ∧ VEnv.get V a = some av ∧
      VEnv.get V z = some zv ∧
      cv = wMulmodAt (loadWord st.memory (qv + BitVec.ofNat 256 off).toNat) av zv ∧
      st' = touchMemory st (qv + BitVec.ofNat 256 off).toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hmload =>
      cases hrest with
      | argsCons hrest2 ha =>
          cases hrest2 with
          | argsCons hnil hz =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hzv, hstz⟩ := b1_eval_var_inv hz
                  obtain ⟨hav, hsta⟩ := b1_eval_var_inv ha
                  obtain ⟨qv, hqv, hmloadVal, hstm⟩ :=
                    b1_eval_mload_add_var_lit_inv hmload
                  have hza : _ = st := hstz
                  have haa : _ = st := hsta.trans hza
                  rw [haa] at hmloadVal hstm
                  rw [hstm] at hbi
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨qv, _, _, hqv, hav, hzv, by rw [hmloadVal, Midfall.LoweringV3.PcsRows.wMulmodAt], rfl⟩

theorem b1_eval_mulmod_mload_add_var_lit_var_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q a z : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.mload
           [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]],
         GenAst.yvar a, GenAst.yvar z]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hm =>
          cases hrest with
          | argsCons hrest2 ha =>
              cases hrest2 with
              | argsCons hnil hz =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact b1_eval_args_halt_false (fun e he st0 st1 hh => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact b1_eval_mload_add_var_lit_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

theorem b1_eval_mulmod_nested_mload_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q dx lb : String} {off : Nat}
    {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.mulmod
           [GenAst.yop EVM.Op.mload
              [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]],
            GenAst.yvar dx, GenAst.yvar "r"],
         GenAst.yvar lb, GenAst.yvar "r"]) (.vals [cv] st')) :
    ∃ qv dxv lbv rv, VEnv.get V q = some qv ∧ VEnv.get V dx = some dxv ∧
      VEnv.get V lb = some lbv ∧ VEnv.get V "r" = some rv ∧
      cv = wMulmodAt (wMulmodAt (loadWord st.memory
        (qv + BitVec.ofNat 256 off).toNat) dxv rv) lbv rv ∧
      st' = touchMemory st (qv + BitVec.ofNat 256 off).toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := b2_eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hinner =>
      cases hrest with
      | argsCons hrest2 hlb =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hrv0, hstr⟩ := b1_eval_var_inv hr
                  obtain ⟨hlbv, hstlb⟩ := b1_eval_var_inv hlb
                  obtain ⟨qv, dxv, zv, hq, hdx, hz, hinnerVal, hstinner⟩ :=
                    b1_eval_mulmod_mload_add_var_lit_var_inv hinner
                  have hzv : zv = _ := Option.some.inj (hz.symm.trans hrv0)
                  have hlb_state : _ = st := hstlb.trans hstr
                  rw [hzv] at hinnerVal
                  rw [hlb_state] at hinnerVal hstinner
                  rw [hstinner] at hbi
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨qv, dxv, _, _, hq, hdx, hlbv, hrv0,
                    by rw [hinnerVal, Midfall.LoweringV3.PcsRows.wMulmodAt, Midfall.LoweringV3.PcsRows.wMulmodAt], rfl⟩

theorem b1_eval_mulmod_nested_mload_add_var_lit_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {q dx lb : String} {off : Nat}
    {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.mulmod
           [GenAst.yop EVM.Op.mload
              [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]],
            GenAst.yvar dx, GenAst.yvar "r"],
         GenAst.yvar lb, GenAst.yvar "r"]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hinner =>
          cases hrest with
          | argsCons hrest2 hlb =>
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
        · exact b1_eval_mulmod_mload_add_var_lit_var_halt hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_mload_add_var_lit_var_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_mload_add_var_lit_var_halt
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_nested_mload_add_var_lit_inv
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_eval_mulmod_nested_mload_add_var_lit_halt
  [propext, Classical.choice, Quot.sound] native []


theorem b1_exec_ylet_mulmod_nested {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x q dx lb : String} {off : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.yop EVM.Op.mulmod
        [GenAst.yop EVM.Op.mulmod
           [GenAst.yop EVM.Op.mload
              [GenAst.yop EVM.Op.add [GenAst.yvar q, GenAst.ylit off]],
            GenAst.yvar dx, GenAst.yvar "r"],
         GenAst.yvar lb, GenAst.yvar "r"])) V' st' o) :
    o = .normal ∧ ∃ qv dxv lbv rv,
      VEnv.get V q = some qv ∧ VEnv.get V dx = some dxv ∧
      VEnv.get V lb = some lbv ∧ VEnv.get V "r" = some rv ∧
      V' = (x, wMulmodAt (wMulmodAt (loadWord st.memory
        (qv + BitVec.ofNat 256 off).toNat) dxv rv) lbv rv) :: V ∧
      st' = touchMemory st (qv + BitVec.ofNat 256 off).toNat 32 := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨qv, dxv, lbv, rv, hq, hdx, hlb, hrv, hcv, hst⟩ :=
        b1_eval_mulmod_nested_mload_add_var_lit_inv he
      subst hcv; subst hst
      exact ⟨rfl, qv, dxv, lbv, rv, hq, hdx, hlb, hrv, by simp, rfl⟩
  | letHalt he => exact (b1_eval_mulmod_nested_mload_add_var_lit_halt he).elim

theorem b1_exec_yset_sub_from_vars {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {x a b : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.yset x (GenAstPcs.subFrom (GenAst.yvar a) (GenAst.yvar b))) V' st' o) :
    o = .normal ∧ ∃ av bv rv, VEnv.get V a = some av ∧ VEnv.get V b = some bv ∧
      VEnv.get V "r" = some rv ∧
      V' = VEnv.set V x (wAddmodAt av (rv - bv) rv) ∧ st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨av, bv, rv, ha, hb, hr, hval, hst⟩ := b1_eval_sub_from_vars_inv he
      subst hval; subst hst
      exact ⟨rfl, av, bv, rv, ha, hb, hr, by simp [VEnv.setMany], rfl⟩
  | assignHalt he => exact (b1_eval_sub_from_vars_halt he).elim

#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_ylet_mulmod_nested
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.b1_exec_yset_sub_from_vars
  [propext, Classical.choice, Quot.sound] native []

/-- The field value of one `term_j`. -/
def pcsTermVal (rv ev dxv lbv : U256) : U256 :=
  wMulmodAt (wMulmodAt ev dxv rv) lbv rv

/-- The running `eval` after the term lines `0..k-1`. -/
def pcsEvalAcc (rv : U256) (ev dxv lbv : Nat → U256) : Nat → U256 → U256
  | 0, acc => acc
  | k + 1, acc =>
      wAddmodAt (pcsEvalAcc rv ev dxv lbv k acc)
        (rv - pcsTermVal rv (ev k) (dxv k) (lbv k)) rv

/-- One term line: `let term_j := ...; eval := eval - term_j`. -/
def pcsTermStmt (j evOff : Nat) (dxN lbN : String) : Block EVM.Op :=
  [ GenAst.ylet ("term_" ++ toString j) (GenAst.yop EVM.Op.mulmod
      [ GenAst.yop EVM.Op.mulmod
          [ GenAst.yop EVM.Op.mload
              [GenAst.yop EVM.Op.add
                [GenAst.yvar "Q_EVAL_SET_MPTR", GenAst.ylit (evOff * Midfall.Generator.wordBytes)]],
            GenAst.yvar dxN, GenAst.yvar "r"],
        GenAst.yvar lbN, GenAst.yvar "r"]),
    GenAst.yset "eval" (GenAstPcs.subFrom (GenAst.yvar "eval")
      (GenAst.yvar ("term_" ++ toString j))) ]

def pcsTermLines (m off : Nat) (dxN lbN : Nat → String) : Block EVM.Op :=
  (List.range m).flatMap fun j => pcsTermStmt j (off + j) (dxN j) (lbN j)

theorem pcsTermLines_succ (m off : Nat) (dxN lbN : Nat → String) :
    pcsTermLines (m + 1) off dxN lbN =
      pcsTermLines m off dxN lbN ++ pcsTermStmt m (off + m) (dxN m) (lbN m) := by
  unfold pcsTermLines
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

set_option maxHeartbeats 1200000 in
theorem pcsTermStmt_contract {funs : FunEnv (Bridge.Dialect c g)}
    (j evOff : Nat) (dxN lbN : String) (dxv lbv rv acc qep : U256)
    (haddr : qep.toNat + evOff * Midfall.Generator.wordBytes < 2 ^ 256)
    (hneEval : ("term_" ++ toString j) ≠ "eval")
    (hneR : ("term_" ++ toString j) ≠ "r")
    (hneDx : ("term_" ++ toString j) ≠ dxN)
    (hneLb : ("term_" ++ toString j) ≠ lbN) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsTermStmt j evOff dxN lbN)
      (fun V st => VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
        VEnv.get V dxN = some dxv ∧ VEnv.get V lbN = some lbv ∧
        VEnv.get V "r" = some rv ∧ VEnv.get V "eval" = some acc)
      (fun V st V' st' o => o = .normal ∧
        VEnv.get V' ("term_" ++ toString j) = some (pcsTermVal rv
          (loadWord st.memory (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv) ∧
        VEnv.get V' "eval" = some (wAddmodAt acc (rv - pcsTermVal rv
          (loadWord st.memory (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv) rv) ∧
        (∀ y, y ≠ ("term_" ++ toString j) → y ≠ "eval" →
          VEnv.get V' y = VEnv.get V y) ∧
        st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hqep, hdx, hlb, hrv, heval⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, hhead, hrest⟩ | ⟨hhead, hne⟩
  · obtain ⟨ho1, qv, dxv', lbv', rvw, hq, hdx', hlb', hr', hV1, hst1⟩ :=
      b1_exec_ylet_mulmod_nested hhead
    have hqe : qv = qep := Option.some.inj (hq.symm.trans hqep)
    have hdxe : dxv' = dxv := Option.some.inj (hdx'.symm.trans hdx)
    have hlbe : lbv' = lbv := Option.some.inj (hlb'.symm.trans hlb)
    have hrve : rvw = rv := Option.some.inj (hr'.symm.trans hrv)
    have haddr : (qv + BitVec.ofNat 256 (evOff * Midfall.Generator.wordBytes)).toNat =
        qep.toNat + evOff * Midfall.Generator.wordBytes := by
      rw [hqe, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : evOff * Midfall.Generator.wordBytes < 2 ^ 256),
        Nat.mod_eq_of_lt haddr]
    have hterm : wMulmodAt (wMulmodAt (loadWord st.memory
          (qv + BitVec.ofNat 256 (evOff * Midfall.Generator.wordBytes)).toNat) dxv' rvw) lbv' rvw =
        pcsTermVal rv (loadWord st.memory
          (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv := by
      rw [haddr, hdxe, hlbe, hrve]
      rfl
    have hV1' : V1 = (("term_" ++ toString j),
        pcsTermVal rv (loadWord st.memory
          (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv) :: V := by
      rw [hV1, hterm]
    rw [hV1'] at hrest
    rw [hst1] at hrest
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest with
        ⟨V2, st2, htail, hnil⟩ | ⟨htail, hne2⟩
    · cases hnil
      obtain ⟨ho2, av, bv, rv', ha, hb, hr, hV2, hst2⟩ :=
        b1_exec_yset_sub_from_vars htail
      have hae : av = acc := by
        have h := ha
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "term_" ++ toString j)
          (y := "eval") (v := _) hneEval.symm] at h
        exact Option.some.inj (h.symm.trans heval)
      have hbe : bv = pcsTermVal rv (loadWord st.memory
            (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv := by
        have h1 : VEnv.get (("term_" ++ toString j,
            pcsTermVal rv (loadWord st.memory
              (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv) :: V)
            ("term_" ++ toString j) = some (pcsTermVal rv (loadWord st.memory
              (qep.toNat + evOff * Midfall.Generator.wordBytes)) dxv lbv) :=
          venv_get_cons_self (D := Bridge.Dialect c g) V _ _
        exact Option.some.inj (hb.symm.trans h1)
      have hre : rv' = rv := by
        have h := hr
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "term_" ++ toString j)
          (y := "r") (v := _) hneR.symm] at h
        exact Option.some.inj (h.symm.trans hrv)
      refine ⟨ho2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hV2]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "eval")
          (y := "term_" ++ toString j) (v := _) hneEval]
        rw [venv_get_cons_self (D := Bridge.Dialect c g)]
      · rw [hV2]
        rw [venv_get_set_same (D := Bridge.Dialect c g) (v := acc) (w := _)
          (by
            rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "term_" ++ toString j)
              (y := "eval") (v := _) hneEval.symm]
            exact heval)]
        rw [hae, hbe, hre]
      · intro y hyterm hyeval
        rw [hV2]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "eval") (y := y)
          (v := _) hyeval]
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "term_" ++ toString j)
          (y := y) (v := _) hyterm]
      · simpa [hst2, hst1] using Midfall.Yul.Word.touchMemory_memory st _ 32
      · simpa [hst2, hst1] using Midfall.Yul.Word.touchMemory_env st _ 32
      · simpa [hst2, hst1] using Midfall.Yul.Word.touchMemory_halted st _ 32
    · exact absurd (b1_exec_yset_sub_from_vars htail).1 hne2
  · exact absurd (b1_exec_ylet_mulmod_nested hhead).1 hne

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsTermVal [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsEvalAcc [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsTermStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsTermLines [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsTermLines_succ
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsTermStmt_contract
  [propext, Classical.choice, Quot.sound] native []


theorem pcsStmtsContractAll_append_mid' {funs : FunEnv (Bridge.Dialect c g)}
    {ss1 ss2 : Block EVM.Op}
    {pre : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {mid : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop}
    (h1 : StmtsContractAll (D := Bridge.Dialect c g) funs ss1 pre
      (fun V st V' st' o => o = .normal ∧ mid V st V' st'))
    (h2 : ∀ V st, pre V st → StmtsContractAll (D := Bridge.Dialect c g) funs ss2
      (fun V' st' => mid V st V' st')
      (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (ss1 ++ ss2) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1run, h2run⟩ | ⟨h1run, hne⟩
  · obtain ⟨_, hmid⟩ := h1 V st hpre V1 st1 .normal h1run
    exact h2 V st hpre V1 st1 hmid V' st' o h2run
  · exact absurd (h1 V st hpre V' st' o h1run).1 hne

set_option maxHeartbeats 1600000 in
theorem pcsTermLines_contract {funs : FunEnv (Bridge.Dialect c g)}
    (m off : Nat) (dxN lbN : Nat → String)
    (ev dxv lbv : Nat → U256) (rv acc qep : U256)
    (haddr : ∀ j, j < m →
      qep.toNat + (off + j) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hneEval : ∀ j, j < m → ("term_" ++ toString j) ≠ "eval")
    (hneR : ∀ j, j < m → ("term_" ++ toString j) ≠ "r")
    (hneQ : ∀ j, j < m → ("term_" ++ toString j) ≠ "Q_EVAL_SET_MPTR")
    (htermNotDx : ∀ j, j < m → ∀ k, k < m → ("term_" ++ toString j) ≠ dxN k)
    (htermNotLb : ∀ j, j < m → ∀ k, k < m → ("term_" ++ toString j) ≠ lbN k)
    (htermDist : ∀ i, i < m → ∀ j, j < m → i ≠ j →
      ("term_" ++ toString i) ≠ ("term_" ++ toString j))
    (hdxEval : ∀ k, k < m → dxN k ≠ "eval")
    (hlbEval : ∀ k, k < m → lbN k ≠ "eval")
    (hdxTerm : ∀ k, k < m → ∀ j, j < m → dxN k ≠ ("term_" ++ toString j))
    (hlbTerm : ∀ k, k < m → ∀ j, j < m → lbN k ≠ ("term_" ++ toString j))
    (hrEval : "r" ≠ "eval")
    (hrTerm : ∀ j, j < m → "r" ≠ ("term_" ++ toString j))
    (hqEval : "Q_EVAL_SET_MPTR" ≠ "eval")
    (hqTerm : ∀ j, j < m → "Q_EVAL_SET_MPTR" ≠ ("term_" ++ toString j)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (pcsTermLines m off dxN lbN)
      (fun V st => VEnv.get V "r" = some rv ∧ VEnv.get V "eval" = some acc ∧
        VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
        (∀ j, j < m → VEnv.get V (dxN j) = some (dxv j)) ∧
        (∀ j, j < m → VEnv.get V (lbN j) = some (lbv j)) ∧
        (∀ j, j < m → loadWord st.memory
          (qep.toNat + (off + j) * Midfall.Generator.wordBytes) = ev j))
      (fun V st V' st' o => o = .normal ∧
        VEnv.get V' "eval" = some (pcsEvalAcc rv ev dxv lbv m acc) ∧
        (∀ j, j < m → VEnv.get V' ("term_" ++ toString j) =
          some (pcsTermVal rv (ev j) (dxv j) (lbv j))) ∧
        (∀ y, y ≠ "eval" → (∀ j, j < m → y ≠ ("term_" ++ toString j)) →
          VEnv.get V' y = VEnv.get V y) ∧
        st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted) := by
  induction m with
  | zero =>
      intro V st hpre V' st' o hrun
      cases hrun
      obtain ⟨hr, heval, hq, hdx, hlb, hload⟩ := hpre
      refine ⟨rfl, heval, ?_, ?_, rfl, rfl, rfl⟩
      · intro j hj
        omega
      · intro y _ _
        rfl
  | succ m ih =>
      intro V st hpre V' st' o hrun
      obtain ⟨hr, heval, hq, hdx, hlb, hload⟩ := hpre
      have hshape : pcsTermLines (m + 1) off dxN lbN =
          pcsTermLines m off dxN lbN ++ pcsTermStmt m (off + m) (dxN m) (lbN m) :=
        pcsTermLines_succ m off dxN lbN
      rw [hshape] at hrun
      refine pcsStmtsContractAll_append_mid' (c := c) (g := g) (funs := funs)
        (mid := fun V0 st0 V1 st1 =>
          VEnv.get V1 "eval" = some (pcsEvalAcc rv ev dxv lbv m acc) ∧
          (∀ j, j < m → VEnv.get V1 ("term_" ++ toString j) =
            some (pcsTermVal rv (ev j) (dxv j) (lbv j))) ∧
          VEnv.get V1 "r" = some rv ∧
          VEnv.get V1 "Q_EVAL_SET_MPTR" = some qep ∧
          (∀ j, j < m → VEnv.get V1 (dxN j) = some (dxv j)) ∧
          (∀ j, j < m → VEnv.get V1 (lbN j) = some (lbv j)) ∧
          (∀ y, y ≠ "eval" → (∀ j, j < m → y ≠ ("term_" ++ toString j)) →
            VEnv.get V1 y = VEnv.get V0 y) ∧
          st1.memory = st0.memory ∧ st1.env = st0.env ∧ st1.halted = st0.halted)
        (pre := fun V st => VEnv.get V "r" = some rv ∧ VEnv.get V "eval" = some acc ∧
          VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
          (∀ j, j < m + 1 → VEnv.get V (dxN j) = some (dxv j)) ∧
          (∀ j, j < m + 1 → VEnv.get V (lbN j) = some (lbv j)) ∧
          (∀ j, j < m + 1 → loadWord st.memory
            (qep.toNat + (off + j) * Midfall.Generator.wordBytes) = ev j))
        (post := fun V st V' st' o => o = .normal ∧
          VEnv.get V' "eval" = some (pcsEvalAcc rv ev dxv lbv (m + 1) acc) ∧
          (∀ j, j < m + 1 → VEnv.get V' ("term_" ++ toString j) =
            some (pcsTermVal rv (ev j) (dxv j) (lbv j))) ∧
          (∀ y, y ≠ "eval" → (∀ j, j < m + 1 → y ≠ ("term_" ++ toString j)) →
            VEnv.get V' y = VEnv.get V y) ∧
          st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted)
        ?_ ?_ V st ⟨hr, heval, hq, hdx, hlb, hload⟩ V' st' o hrun
      · -- the recursive chunk
        intro V0 st0 h0 V1 st1 o1 h1
        have h0' : VEnv.get V0 "r" = some rv ∧ VEnv.get V0 "eval" = some acc ∧
            VEnv.get V0 "Q_EVAL_SET_MPTR" = some qep ∧
            (∀ j, j < m → VEnv.get V0 (dxN j) = some (dxv j)) ∧
            (∀ j, j < m → VEnv.get V0 (lbN j) = some (lbv j)) ∧
            (∀ j, j < m → loadWord st0.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes) = ev j) :=
          ⟨h0.1, h0.2.1, h0.2.2.1,
            (fun j hj => h0.2.2.2.1 j (by omega)),
            (fun j hj => h0.2.2.2.2.1 j (by omega)),
            fun j hj => h0.2.2.2.2.2 j (by omega)⟩
        have hih := ih
          (fun j hj => haddr j (by omega))
          (fun j hj => hneEval j (by omega))
          (fun j hj => hneR j (by omega))
          (fun j hj => hneQ j (by omega))
          (fun j hj k hk => htermNotDx j (by omega) k (by omega))
          (fun j hj k hk => htermNotLb j (by omega) k (by omega))
          (fun i hi j hj hij => htermDist i (by omega) j (by omega) hij)
          (fun k hk => hdxEval k (by omega))
          (fun k hk => hlbEval k (by omega))
          (fun k hk j hj => hdxTerm k (by omega) j (by omega))
          (fun k hk j hj => hlbTerm k (by omega) j (by omega))
          (fun j hj => hrTerm j (by omega))
          (fun j hj => hqTerm j (by omega))
          V0 st0 h0' V1 st1 o1 h1
        obtain ⟨ho1, heval1, hterms1, hpres1, hmem1, henv1, hhalt1⟩ := hih
        refine ⟨ho1, heval1, hterms1, ?_, ?_, ?_, ?_, hpres1, hmem1, henv1, hhalt1⟩
        · rw [hpres1 "r" hrEval (fun j hj => hrTerm j (by omega))]
          exact h0.1
        · rw [hpres1 "Q_EVAL_SET_MPTR" hqEval (fun j hj => hqTerm j (by omega))]
          exact h0.2.2.1
        · intro j hj
          rw [hpres1 (dxN j) (hdxEval j (by omega)) (fun k hk => hdxTerm j (by omega) k (by omega))]
          exact h0.2.2.2.1 j (by omega)
        · intro j hj
          rw [hpres1 (lbN j) (hlbEval j (by omega)) (fun k hk => hlbTerm j (by omega) k (by omega))]
          exact h0.2.2.2.2.1 j (by omega)
      · -- the last term line
        intro V0 st0 h0 V1 st1 hmid V2 st2 o2 hrun2
        obtain ⟨heval1, hterms1, hr1, hq1, hdx1, hlb1, hpres1, hmem1, henv1, hhalt1⟩ := hmid
        have hdxm : VEnv.get V1 (dxN m) = some (dxv m) := by
          rw [hpres1 (dxN m) (hdxEval m (by omega))
            (fun j hj => hdxTerm m (by omega) j (by omega))]
          exact h0.2.2.2.1 m (by omega)
        have hlbm : VEnv.get V1 (lbN m) = some (lbv m) := by
          rw [hpres1 (lbN m) (hlbEval m (by omega))
            (fun j hj => hlbTerm m (by omega) j (by omega))]
          exact h0.2.2.2.2.1 m (by omega)
        have hloadm : loadWord st1.memory
            (qep.toNat + (off + m) * Midfall.Generator.wordBytes) = ev m := by
          rw [hmem1]
          exact h0.2.2.2.2.2 m (by omega)
        have hset := pcsTermStmt_contract (c := c) (g := g) (funs := funs)
          m (off + m) (dxN m) (lbN m) (dxv m) (lbv m) rv
          (pcsEvalAcc rv ev dxv lbv m acc) qep
          (haddr m (by omega))
          (hneEval m (by omega)) (hneR m (by omega))
          (htermNotDx m (by omega) m (by omega))
          (htermNotLb m (by omega) m (by omega))
          V1 st1 ⟨hq1, hdxm, hlbm, hr1, heval1⟩ V2 st2 o2 hrun2
        obtain ⟨ho2, hterm2, heval2, hpres2, hmem2, henv2, hhalt2⟩ := hset
        refine ⟨ho2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [heval2, hloadm]
          rfl
        · intro j hj
          rcases Nat.lt_or_eq_of_le (by omega : j ≤ m) with hjm | rfl
          · rw [hpres2 ("term_" ++ toString j)
              (htermDist j (by omega) m (by omega) (by omega)) (hneEval j (by omega))]
            exact hterms1 j hjm
          · rw [hterm2, hloadm]
        · intro y hyeval hyterm
          rw [hpres2 y (hyterm m (by omega)) hyeval]
          exact hpres1 y hyeval (fun j hj => hyterm j (by omega))
        · rw [hmem2, hmem1]
        · rw [henv2, henv1]
        · rw [hhalt2, hhalt1]

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsStmtsContractAll_append_mid'
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsTermLines_contract
  [propext, Classical.choice, Quot.sound] native []


/-- `MemSameOutside` is transitive. -/
theorem pcsMemSameOutside_trans {st1 st2 st3 : EvmState} {lo len : Nat}
    (h12 : MemSameOutside st1 st2 lo len) (h23 : MemSameOutside st2 st3 lo len) :
    MemSameOutside st1 st3 lo len := by
  intro a ha
  rw [h23 a ha, h12 a ha]

/-- A touched-memory state still agrees outside any window. -/
theorem pcsMemSameOutside_touch {st st' : EvmState} {lo len : Nat}
    (h : MemSameOutside st st' lo len) (a n : Nat) :
    MemSameOutside st (touchMemory st' a n) lo len := by
  intro b hb
  rw [Midfall.Yul.Word.touchMemory_memory]
  exact h b hb

/-- The `f_eval` Horner update of the general set arm. -/
def pcsFEvalStmt : Stmt EVM.Op :=
  GenAst.yset "f_eval" (GenAst.yop EVM.Op.addmod
    [GenAst.yop EVM.Op.mulmod
       [GenAst.yvar "f_eval", GenAst.yvar "x2", GenAst.yvar "r"],
     GenAst.yvar "eval", GenAst.yvar "r"])

theorem pcsFEval_contract {funs : FunEnv (Bridge.Dialect c g)}
    (fev x2v evv rv : U256) :
    StmtContractAll (D := Bridge.Dialect c g) funs pcsFEvalStmt
      (fun V st => VEnv.get V "f_eval" = some fev ∧
        VEnv.get V "x2" = some x2v ∧ VEnv.get V "eval" = some evv ∧
        VEnv.get V "r" = some rv)
      (fun V st V' st' o => o = .normal ∧
        V' = VEnv.set V "f_eval" (wAddmodAt (wMulmodAt fev x2v rv) evv rv) ∧
        st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hf, hx, he, hr⟩ := hpre
  obtain ⟨ho, fvv, x2v', evv', rv4, hf', hx', he', hr', hV, hst⟩ :=
    b1_exec_yset_f_eval hrun
  have hfe : fvv = fev := Option.some.inj (hf'.symm.trans hf)
  have hxe : x2v' = x2v := Option.some.inj (hx'.symm.trans hx)
  have hee : evv' = evv := Option.some.inj (he'.symm.trans he)
  have hre : rv4 = rv := Option.some.inj (hr'.symm.trans hr)
  refine ⟨ho, ?_, hst⟩
  rw [hV, hfe, hxe, hee, hre]

#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsMemSameOutside_trans
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsMemSameOutside_touch
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsFEvalStmt [propext] native []
#assert_axioms Midfall.LoweringV3.PcsBlock4.pcsFEval_contract
  [propext, Classical.choice, Quot.sound] native []


def pcsRotPtRef (distinctRotations : List Int) (rot : Int) : String :=
  "rot_pt_" ++ toString ((distinctRotations.findIdx? fun r => r == rot).getD 0)

def pcsPointRefs (points : List Int) (distinctRotations : List Int) : List (Nat × String) :=
  (Midfall.Generator.enumIdx points).map fun q => (q.1, pcsRotPtRef distinctRotations q.2)

def pcsKs (points : List Int) (distinctRotations : List Int) (j : Nat) : List (Nat × String) :=
  (Midfall.Generator.enumIdx points).filterMap fun q =>
    if q.1 == j then none else some (q.1, pcsRotPtRef distinctRotations q.2)

def pcsBatchInputs (m : Nat) : List String :=
  (List.range m).map pcsDxName ++ (List.range m).map pcsLbasisName

def pcsBatchName (m i : Nat) : String := (pcsBatchInputs m).getD i ""

def pcsInvName (m j : Nat) : String :=
  if j < m then "dx_inv_" ++ toString j else "lbasis_inv_" ++ toString (j - m)

/-- The `else` branch of `pcsSetBlockAst`, copied verbatim. -/
def pcsSetBodyGen (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (setEvalOffsetWords : Nat) : Block EVM.Op :=
  let rotPtRef : Int → String := fun rot =>
    "rot_pt_" ++ toString ((distinctRotations.findIdx? fun r => r == rot).getD 0)
  let proofEval := GenAst.yop EVM.Op.calldataload [GenAst.yop EVM.Op.add [GenAst.yvar "Q_EVAL_CPTR",
    GenAst.ylit (setIdx * Midfall.Generator.wordBytes)]]
  let m := points.length
  let dxLines := (Midfall.Generator.enumIdx points).map fun (j, point) =>
    GenAst.ylet ("dx_" ++ toString j) (GenAstPcs.subFrom (GenAst.yvar "x3") (GenAst.yvar (rotPtRef point)))
  let lbasisLines := (Midfall.Generator.enumIdx points).map fun (j, pointJ) =>
    let pj := GenAst.yvar (rotPtRef pointJ)
    let terms := (Midfall.Generator.enumIdx points).filterMap fun (k, pointK) =>
      if k == j then none else some (GenAst.yset ("lbasis_" ++ toString j)
        (GenAst.yop EVM.Op.mulmod [GenAst.yvar ("lbasis_" ++ toString j),
          GenAstPcs.subFrom pj (GenAst.yvar (rotPtRef pointK)), GenAst.yvar "r"]))
    [GenAst.ylet ("lbasis_" ++ toString j) (GenAst.ylit 1)] ++ terms
  let batchInputs := (List.range m).map (fun j => "dx_" ++ toString j)
    ++ (List.range m).map (fun j => "lbasis_" ++ toString j)
  let n := batchInputs.length
  let bpLines := [GenAst.ylet "bp_0" (GenAst.yvar (batchInputs.getD 0 ""))]
    ++ ((Midfall.Generator.enumIdx batchInputs).drop 1).map fun (i, inp) =>
        GenAst.ylet ("bp_" ++ toString i)
          (GenAst.yop EVM.Op.mulmod [GenAst.yvar ("bp_" ++ toString (i - 1)), GenAst.yvar inp, GenAst.yvar "r"])
  let invName : Nat → String := fun idx =>
    if idx < m then "dx_inv_" ++ toString idx else "lbasis_inv_" ++ toString (idx - m)
  let bqLines := ((List.range n).drop 1).reverse.flatMap fun i =>
    [ GenAst.ylet (invName i) (GenAst.yop EVM.Op.mulmod [GenAst.yvar "bq", GenAst.yvar ("bp_" ++ toString (i - 1)), GenAst.yvar "r"]),
      GenAst.yset "bq" (GenAst.yop EVM.Op.mulmod [GenAst.yvar "bq", GenAst.yvar (batchInputs.getD i ""), GenAst.yvar "r"]) ]
  let denInvLines := [GenAst.ylet "den_inv" (GenAst.yvar (invName 0))]
    ++ ((List.range m).drop 1).map fun j =>
        GenAst.yset "den_inv" (GenAst.yop EVM.Op.mulmod [GenAst.yvar "den_inv", GenAst.yvar ("dx_inv_" ++ toString j),
          GenAst.yvar "r"])
  let termLines := (List.range m).flatMap fun j =>
    let evJ := GenAst.yop EVM.Op.mload [GenAst.yop EVM.Op.add [GenAst.yvar "Q_EVAL_SET_MPTR",
      GenAst.ylit ((setEvalOffsetWords + j) * Midfall.Generator.wordBytes)]]
    [ GenAst.ylet ("term_" ++ toString j)
        (GenAst.yop EVM.Op.mulmod [GenAst.yop EVM.Op.mulmod [evJ, GenAst.yvar ("dx_inv_" ++ toString j), GenAst.yvar "r"],
          GenAst.yvar ("lbasis_inv_" ++ toString j), GenAst.yvar "r"]),
      GenAst.yset "eval" (GenAstPcs.subFrom (GenAst.yvar "eval") (GenAst.yvar ("term_" ++ toString j))) ]
  dxLines ++ lbasisLines.flatten ++ bpLines
    ++ [ GenAst.ylet "bq" (GenAst.ycall "scalar_inv" [GenAst.yvar ("bp_" ++ toString (n - 1))]) ]
    ++ bqLines ++ [GenAst.ylet (invName 0) (GenAst.yvar "bq")] ++ denInvLines
    ++ [ GenAst.ylet "eval" (GenAst.yop EVM.Op.mulmod [proofEval, GenAst.yvar "den_inv", GenAst.yvar "r"]) ]
    ++ termLines
    ++ [ GenAst.yset "f_eval" (GenAst.yop EVM.Op.addmod [GenAst.yop EVM.Op.mulmod [GenAst.yvar "f_eval",
          GenAst.yvar "x2", GenAst.yvar "r"], GenAst.yvar "eval", GenAst.yvar "r"]) ]

def pcsGenBody (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off : Nat) : Block EVM.Op :=
  let m := points.length
  let xs := pcsPointRefs points distinctRotations
  let invName := pcsInvName m
  let n := (pcsBatchInputs m).length
  let nm := pcsBatchName m
  xs.map (fun q => pcsDxStmt q.1 q.2)
    ++ (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (pcsKs points distinctRotations q.1))).flatten
    ++ pcsBpLines n nm
    ++ [pcsBqStmt (pcsBpName (n - 1))]
    ++ pcsBqLines n nm invName
    ++ [GenAst.ylet (invName 0) (GenAst.yvar "bq")]
    ++ pcsDenInvLines m invName
    ++ [pcsEvalStmt setIdx]
    ++ pcsTermLines m off (fun j => invName j) (fun j => invName (m + j))
    ++ [pcsFEvalStmt]


theorem list_filterMap_congr {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.filterMap_cons]
      rw [h a (by simp)]
      split <;> simp [ih (fun x hx => h x (by simp [hx]))]

theorem pcsBpMap_gen (l : List String) :
    ((Midfall.Generator.enumIdx l).drop 1).map (fun x =>
        GenAst.ylet ("bp_" ++ toString x.1) (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar ("bp_" ++ toString (x.1 - 1)), GenAst.yvar x.2, GenAst.yvar "r"]))
    = ((List.range l.length).drop 1).map (fun i =>
        GenAst.ylet (pcsBpName i) (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar (pcsBpName (i - 1)), GenAst.yvar (l.getD i ""), GenAst.yvar "r"])) := by
  unfold Midfall.Generator.enumIdx
  apply List.ext_getElem
  · simp only [List.length_map, List.length_drop, List.length_zip, List.length_range]
    rw [Nat.min_self]
  · intro j hj1 hj2
    simp only [List.length_map, List.length_drop, List.length_zip, List.length_range,
      Nat.min_self] at hj1
    simp only [List.getElem_map, List.getElem_drop, List.getElem_zip, List.getElem_range,
      pcsBpName]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem pcsBpLines_gen (batchInputs : List String) :
    [GenAst.ylet "bp_0" (GenAst.yvar (batchInputs.getD 0 ""))]
      ++ ((Midfall.Generator.enumIdx batchInputs).drop 1).map (fun x =>
          GenAst.ylet ("bp_" ++ toString x.1) (GenAst.yop EVM.Op.mulmod
            [GenAst.yvar ("bp_" ++ toString (x.1 - 1)), GenAst.yvar x.2, GenAst.yvar "r"]))
    = pcsBpLines batchInputs.length (fun i => batchInputs.getD i "") := by
  unfold pcsBpLines pcsBpHead pcsBpTail
  rw [pcsBpMap_gen]
  have h0 : (Nat.repr 0 : String) = "0" := by decide
  simp [pcsBpName, h0]

theorem pcsBqLines_gen (batchInputs : List String) (invName : Nat → String) :
    ((List.range batchInputs.length).drop 1).reverse.flatMap (fun i =>
      [ GenAst.ylet (invName i) (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "bq", GenAst.yvar ("bp_" ++ toString (i - 1)), GenAst.yvar "r"]),
        GenAst.yset "bq" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "bq", GenAst.yvar (batchInputs.getD i ""), GenAst.yvar "r"]) ])
    = pcsBqLines batchInputs.length (fun i => batchInputs.getD i "") invName := rfl

theorem pcsDenInvLines_gen (m : Nat) (hm : 1 ≤ m) (invName : Nat → String)
    (hinv0 : invName 0 = "dx_inv_" ++ toString 0)
    (hinv : ∀ j, j < m → invName j = "dx_inv_" ++ toString j) :
    [GenAst.ylet "den_inv" (GenAst.yvar (invName 0))]
      ++ ((List.range m).drop 1).map (fun j =>
          GenAst.yset "den_inv" (GenAst.yop EVM.Op.mulmod
            [GenAst.yvar "den_inv", GenAst.yvar ("dx_inv_" ++ toString j), GenAst.yvar "r"]))
    = pcsDenInvLines m invName := by
  unfold pcsDenInvLines pcsDenInvSetStmt
  rw [hinv0]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjlt : j < m := by
    have := List.mem_range.mp (List.mem_of_mem_drop hj)
    omega
  rw [← hinv j hjlt]

theorem pcsTermLines_gen (m off : Nat) (invName : Nat → String)
    (hinv : ∀ j, j < m → invName j = "dx_inv_" ++ toString j)
    (hinv2 : ∀ j, j < m → invName (m + j) = "lbasis_inv_" ++ toString j) :
    (List.range m).flatMap (fun j =>
      [ GenAst.ylet ("term_" ++ toString j)
          (GenAst.yop EVM.Op.mulmod
            [GenAst.yop EVM.Op.mulmod
                [GenAst.yop EVM.Op.mload
                    [GenAst.yop EVM.Op.add
                      [GenAst.yvar "Q_EVAL_SET_MPTR",
                        GenAst.ylit ((off + j) * Midfall.Generator.wordBytes)]],
                  GenAst.yvar ("dx_inv_" ++ toString j), GenAst.yvar "r"],
              GenAst.yvar ("lbasis_inv_" ++ toString j), GenAst.yvar "r"]),
        GenAst.yset "eval" (GenAstPcs.subFrom (GenAst.yvar "eval")
          (GenAst.yvar ("term_" ++ toString j))) ])
    = pcsTermLines m off (fun j => invName j) (fun j => invName (m + j)) := by
  unfold pcsTermLines
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjlt : j < m := List.mem_range.mp hj
  unfold pcsTermStmt
  rw [← hinv j hjlt, ← hinv2 j hjlt]

theorem pcsDxLines_gen (points : List Int) (distinct : List Int) :
    (Midfall.Generator.enumIdx points).map (fun x =>
        GenAst.ylet ("dx_" ++ toString x.1)
          (GenAstPcs.subFrom (GenAst.yvar "x3")
            (GenAst.yvar ("rot_pt_" ++ toString
              ((List.findIdx? (fun r => r == x.2) distinct).getD 0)))))
    = (pcsPointRefs points distinct).map (fun q => pcsDxStmt q.1 q.2) := by
  simp only [pcsPointRefs, pcsDxStmt, pcsRotPtRef, List.map_map]
  apply List.map_congr_left
  intro q hq
  simp [pcsDxName]

theorem pcsLbasisLines_gen (points : List Int) (distinct : List Int) :
    (Midfall.Generator.enumIdx points).map (fun x =>
        [GenAst.ylet ("lbasis_" ++ toString x.1) (GenAst.ylit 1)]
        ++ (Midfall.Generator.enumIdx points).filterMap (fun x_1 =>
            if x_1.1 == x.1 then none else some (GenAst.yset ("lbasis_" ++ toString x.1)
              (GenAst.yop EVM.Op.mulmod [GenAst.yvar ("lbasis_" ++ toString x.1),
                GenAstPcs.subFrom
                  (GenAst.yvar ("rot_pt_" ++ toString
                    ((List.findIdx? (fun r => r == x.2) distinct).getD 0)))
                  (GenAst.yvar ("rot_pt_" ++ toString
                    ((List.findIdx? (fun r => r == x_1.2) distinct).getD 0))), GenAst.yvar "r"]))))
    = (pcsPointRefs points distinct).map (fun q =>
        pcsLbasisGroupAst q.1 q.2 (pcsKs points distinct q.1)) := by
  simp only [pcsPointRefs, pcsRotPtRef, List.map_map]
  apply List.map_congr_left
  intro q hq
  rw [show ((fun q => pcsLbasisGroupAst q.1 q.2 (pcsKs points distinct q.1)) ∘
      (fun q => (q.1, "rot_pt_" ++ toString
        ((List.findIdx? (fun r => r == q.2) distinct).getD 0)))) q =
      pcsLbasisGroupAst q.1 ("rot_pt_" ++ toString
        ((List.findIdx? (fun r => r == q.2) distinct).getD 0))
        (pcsKs points distinct q.1) from rfl]
  simp only [pcsLbasisGroupAst, pcsLbasisInit, pcsLbasisStmt, pcsLbasisName,
    pcsKs, List.cons_append, List.singleton_append]
  rw [List.map_filterMap, List.nil_append]
  congr 1
  apply list_filterMap_congr
  intro x hx
  by_cases h : (x.1 == q.1) = true <;> simp [h, pcsRotPtRef]

theorem pcsSetBodyGen_eq (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off : Nat) (hm : 1 < points.length) :
    pcsSetBodyGen setIdx points distinctRotations off = pcsGenBody setIdx points distinctRotations off := by
  unfold pcsSetBodyGen pcsGenBody
  dsimp only
  simp only [pcsBatchInputs, pcsBatchName, pcsDxName, pcsLbasisName, pcsInvName]
  set invName : Nat → String := fun idx =>
    if idx < points.length then "dx_inv_" ++ toString idx
    else "lbasis_inv_" ++ toString (idx - points.length) with hinvName
  rw [pcsDxLines_gen, pcsLbasisLines_gen,
    pcsBpLines_gen ((List.range points.length).map (fun j => "dx_" ++ toString j)
      ++ (List.range points.length).map (fun j => "lbasis_" ++ toString j)),
    pcsBqLines_gen ((List.range points.length).map (fun j => "dx_" ++ toString j)
      ++ (List.range points.length).map (fun j => "lbasis_" ++ toString j)) invName,
    pcsDenInvLines_gen points.length (by omega) invName ?_ ?_,
    pcsTermLines_gen points.length off invName ?_ ?_]
  · rw [hinvName]
    unfold pcsBatchName pcsBatchInputs pcsDxName pcsLbasisName pcsInvName pcsBpName
    simp [pcsEvalStmt, pcsFEvalStmt, pcsBqStmt]
  all_goals
    first
    | (intro j hj; simp only [hinvName]; rw [if_pos hj])
    | (simp only [hinvName]; rw [if_pos (by omega)])
    | (intro j hj; simp only [hinvName]
       rw [if_neg (by omega), show points.length + j - points.length = j by omega])


def pcsStmtLocal (locals : List String) : Stmt EVM.Op → Prop
  | .letDecl [x] _ => x ∈ locals
  | .assign [x] _ => x ∈ locals
  | _ => False

def pcsStmtLetName? : Stmt EVM.Op → Option String
  | .letDecl [x] _ => some x
  | _ => none

def pcsAddedNames (ss : Block EVM.Op) : List String :=
  (ss.filterMap pcsStmtLetName?).reverse

theorem pcs_venv_set_map_fst (V : VEnv (Bridge.Dialect c g)) (x : String) (v : U256) :
    (VEnv.set V x v).map Prod.fst = V.map Prod.fst := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

theorem pcsExec_get_of_local {funs : FunEnv (Bridge.Dialect c g)} {ss : Block EVM.Op} {locals : List String}
    (hloc : ∀ s ∈ ss, pcsStmtLocal locals s) {x : String} (hx : x ∉ locals) :
    ∀ {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
      {st' : EvmState} {o : Outcome},
      ExecStmts (Bridge.Dialect c g) funs V st ss V' st' o →
      o = .normal → VEnv.get V' x = VEnv.get V x := by
  induction ss with
  | nil =>
      intro V st V' st' o h ho
      cases h
      rfl
  | cons s rest ih =>
      intro V st V' st' o h ho
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with
          ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
      · have hs := hloc s (by simp)
        have hloc' : ∀ s' ∈ rest, pcsStmtLocal locals s' :=
          fun s' hs' => hloc s' (by simp [hs'])
        cases s with
        | letDecl vars e =>
            cases e with
            | none =>
                cases vars with
                | nil => simp [pcsStmtLocal] at hs
                | cons x' vars =>
                    cases vars with
                    | nil =>
                        cases hhead with
                        | letZero =>
                            have hxne : x ≠ x' := fun h => hx (h ▸ hs)
                            have htail'' : ExecStmts (Bridge.Dialect c g) funs
                                ((x', (Bridge.Dialect c g).zero) :: V) st
                                rest V' st' o := by simpa [bindZeros] using htail
                            rw [ih hloc' htail'' ho]
                            exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := x')
                              (y := x) (v := _) hxne
                    | cons _ _ => simp [pcsStmtLocal] at hs
            | some e =>
                cases vars with
                | nil => simp [pcsStmtLocal] at hs
                | cons x' vars =>
                    cases vars with
                    | nil =>
                        cases hhead with
                        | letVal he hlen =>
                            obtain ⟨v, rfl⟩ := b2_list_length_one hlen
                            have hxne : x ≠ x' := fun h => hx (h ▸ hs)
                            have htail'' : ExecStmts (Bridge.Dialect c g) funs ((x', v) :: V) st1
                                rest V' st' o := by simpa using htail
                            rw [ih hloc' htail'' ho]
                            exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := x')
                              (y := x) (v := v) hxne
                    | cons _ _ => simp [pcsStmtLocal] at hs
        | assign vars e =>
            cases vars with
            | nil => simp [pcsStmtLocal] at hs
            | cons x' vars =>
                cases vars with
                | nil =>
                    cases hhead with
                    | assignVal he hlen =>
                        obtain ⟨v, rfl⟩ := b2_list_length_one hlen
                        have hxne : x ≠ x' := fun h => hx (h ▸ hs)
                        have htail'' : ExecStmts (Bridge.Dialect c g) funs (VEnv.set V x' v) st1
                            rest V' st' o := by simpa [VEnv.setMany] using htail
                        rw [ih hloc' htail'' ho]
                        exact venv_get_set_ne (D := Bridge.Dialect c g) (x := x') (y := x)
                          (v := v) hxne
                | cons _ _ => simp [pcsStmtLocal] at hs
        | _ => simp [pcsStmtLocal] at hs
      · exact absurd ho hne

theorem pcsExec_names {funs : FunEnv (Bridge.Dialect c g)} {ss : Block EVM.Op}
    (hloc : ∀ s ∈ ss, ∃ x e, s = GenAst.ylet x e ∨ s = GenAst.yset x e) :
    ∀ {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
      {st' : EvmState} {o : Outcome},
      ExecStmts (Bridge.Dialect c g) funs V st ss V' st' o →
      o = .normal → V'.map Prod.fst = pcsAddedNames ss ++ V.map Prod.fst := by
  induction ss with
  | nil =>
      intro V st V' st' o h ho
      cases h
      rfl
  | cons s rest ih =>
      intro V st V' st' o h ho
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with
          ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
      · have hloc' : ∀ s' ∈ rest, ∃ x e, s' = GenAst.ylet x e ∨ s' = GenAst.yset x e :=
          fun s' hs' => hloc s' (by simp [hs'])
        obtain ⟨x, e, hlet | hset⟩ := hloc s (by simp)
        · subst hlet
          cases hhead with
          | letVal he hlen =>
              obtain ⟨v, rfl⟩ := b2_list_length_one hlen
              have htail'' : ExecStmts (Bridge.Dialect c g) funs ((x, v) :: V) st1
                  rest V' st' o := by simpa using htail
              rw [ih hloc' htail'' ho]
              simp [pcsAddedNames, pcsStmtLetName?, GenAst.ylet, List.append_assoc, List.map_cons]
        · subst hset
          cases hhead with
          | assignVal he hlen =>
              obtain ⟨v, rfl⟩ := b2_list_length_one hlen
              have htail'' : ExecStmts (Bridge.Dialect c g) funs (VEnv.set V x v) st1
                  rest V' st' o := by simpa [VEnv.setMany] using htail
              have hnone : pcsStmtLetName? (GenAst.yset x e) = none := by
                simp [GenAst.yset, pcsStmtLetName?]
              rw [ih hloc' htail'' ho, pcs_venv_set_map_fst]
              simp [pcsAddedNames, hnone]
      · exact absurd ho hne


structure PcsGenNames (m : Nat) (xs : List (Nat × String))
    (ks : Nat → List (Nat × String)) : Prop where
  dxX3 : ∀ q ∈ xs, pcsDxName q.1 ≠ "x3"
  dxR : ∀ q ∈ xs, pcsDxName q.1 ≠ "r"
  dxRot : ∀ q ∈ xs, ∀ r ∈ xs, q.2 ≠ pcsDxName r.1
  dxIdx : ∀ q ∈ xs, ∀ r ∈ xs, q.1 ≠ r.1
  dxDist : ∀ q ∈ xs, ∀ r ∈ xs, q.1 ≠ r.1 → pcsDxName q.1 ≠ pcsDxName r.1
  lbR : ∀ q ∈ xs, pcsLbasisName q.1 ≠ "r"
  lbPt : ∀ q ∈ xs, pcsLbasisName q.1 ≠ q.2
  lbKs : ∀ q ∈ xs, ∀ k ∈ ks q.1, pcsLbasisName q.1 ≠ k.2
  lbRot : ∀ q ∈ xs, ∀ r ∈ xs, pcsLbasisName q.1 ≠ r.2
  lbRot2 : ∀ q ∈ xs, ∀ r ∈ xs, ∀ k ∈ ks r.1, pcsLbasisName q.1 ≠ k.2
  lbDist : ∀ q ∈ xs, ∀ r ∈ xs, q.1 ≠ r.1 → pcsLbasisName q.1 ≠ pcsLbasisName r.1
  lbIdx : ∀ q ∈ xs, ∀ r ∈ xs, q.1 ≠ r.1
  lbDx : ∀ q ∈ xs, ∀ r ∈ xs, pcsLbasisName q.1 ≠ pcsDxName r.1
  bpR : ∀ i < (pcsBatchInputs m).length, pcsBpName i ≠ "r"
  bpIn : ∀ i < (pcsBatchInputs m).length, ∀ j < (pcsBatchInputs m).length,
    pcsBpName i ≠ pcsBatchName m j
  bpDist : ∀ i < (pcsBatchInputs m).length, ∀ j < (pcsBatchInputs m).length,
    i ≠ j → pcsBpName i ≠ pcsBpName j
  bqR : "bq" ≠ "r"
  invBq : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length → pcsInvName m i ≠ "bq"
  invPrev : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length →
    pcsInvName m i ≠ pcsBpName (i - 1)
  invInp : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length →
    pcsInvName m i ≠ pcsBatchName m i
  invR : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length → pcsInvName m i ≠ "r"
  bqBp : ∀ i < (pcsBatchInputs m).length, pcsBpName i ≠ "bq"
  bqInp : ∀ i < (pcsBatchInputs m).length, pcsBatchName m i ≠ "bq"
  invBp : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length → ∀ j < (pcsBatchInputs m).length,
    pcsBpName j ≠ pcsInvName m i
  invInp2 : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length → ∀ j < (pcsBatchInputs m).length,
    pcsBatchName m j ≠ pcsInvName m i
  rInv : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length → "r" ≠ pcsInvName m i
  invDist : ∀ i, 1 ≤ i → i < (pcsBatchInputs m).length →
    ∀ j, 1 ≤ j → j < (pcsBatchInputs m).length → i ≠ j → pcsInvName m i ≠ pcsInvName m j
  invX2 : ∀ i, pcsInvName m i ≠ "x2"
  invF : ∀ i, pcsInvName m i ≠ "f_eval"
  invQ : ∀ i, pcsInvName m i ≠ "Q_EVAL_CPTR"
  bqBpName : ∀ i < (pcsBatchInputs m).length, "bq" ≠ pcsBpName i
  denInv : ∀ j < m, "den_inv" ≠ pcsInvName m j
  denR : "den_inv" ≠ "r"
  termEval : ∀ j < m, ("term_" ++ toString j) ≠ "eval"
  termR : ∀ j < m, ("term_" ++ toString j) ≠ "r"
  termQ : ∀ j < m, ("term_" ++ toString j) ≠ "Q_EVAL_SET_MPTR"
  termDx : ∀ j < m, ∀ k < m, ("term_" ++ toString j) ≠ pcsInvName m k
  termLb : ∀ j < m, ∀ k < m, ("term_" ++ toString j) ≠ pcsInvName m (m + k)
  termDist : ∀ i < m, ∀ j < m, i ≠ j → ("term_" ++ toString i) ≠ ("term_" ++ toString j)
  dxEval : ∀ k < m, pcsInvName m k ≠ "eval"
  lbEval : ∀ k < m, pcsInvName m (m + k) ≠ "eval"
  dxTerm : ∀ k < m, ∀ j < m, pcsInvName m k ≠ ("term_" ++ toString j)
  lbTerm : ∀ k < m, ∀ j < m, pcsInvName m (m + k) ≠ ("term_" ++ toString j)
  rEval : "r" ≠ "eval"
  rTerm : ∀ j < m, "r" ≠ ("term_" ++ toString j)
  qEval : "Q_EVAL_SET_MPTR" ≠ "eval"
  qTerm : ∀ j < m, "Q_EVAL_SET_MPTR" ≠ ("term_" ++ toString j)

def pcsGenBatchVal (rv x3v : U256) (p : Nat → U256) (ks : Nat → List (Nat × String))
    (m i : Nat) : U256 :=
  if i < m then wAddmodAt x3v (rv - p i) rv
  else pcsLbasisVal rv (p (i - m)) p (ks (i - m))

def pcsGenFEval (rv x2v fev cval : U256) (ev : Nat → U256) (a : Nat → U256) (m : Nat) : U256 :=
  wAddmodAt (wMulmodAt fev x2v rv)
    (pcsEvalAcc rv ev (fun j => SIInv (a j)) (fun j => SIInv (a (m + j))) m
      (wMulmodAt cval (pcsDenInvVal rv (fun j => SIInv (a j)) m) rv)) rv

theorem pcsBatchInputs_length (m : Nat) : (pcsBatchInputs m).length = 2 * m := by
  simp only [pcsBatchInputs, List.length_append, List.length_map, List.length_range]
  omega
theorem pcsGenFEval_one (x2v fev cval : U256) (ev : Nat → U256)
    (a : Nat → U256) (ha1 : a 1 = 1) :
    pcsGenFEval (BitVec.ofNat 256 Midfall.Yul.blsR) x2v fev cval ev a 1 =
      wAddmodAt (wMulmodAt fev x2v (BitVec.ofNat 256 Midfall.Yul.blsR))
        (wAddmodAt
          (wMulmodAt cval (SIInv (a 0)) (BitVec.ofNat 256 Midfall.Yul.blsR))
          (BitVec.ofNat 256 Midfall.Yul.blsR -
            wMulmodAt (ev 0) (SIInv (a 0)) (BitVec.ofNat 256 Midfall.Yul.blsR))
          (BitVec.ofNat 256 Midfall.Yul.blsR))
        (BitVec.ofNat 256 Midfall.Yul.blsR) := by
  unfold pcsGenFEval
  rw [pcsDenInvVal_one (f := fun j => SIInv (a j)) (pcsSIInv_toNat_lt (a 0))]
  unfold pcsEvalAcc pcsTermVal
  rw [ha1, pcsSIInv_one]
  rw [pcs_wMulmodAt_one_right (pcs_wMulmodAt_toNat_lt (a := ev 0) (b := SIInv (a 0)))]
  simp only [Nat.zero_add]
  rfl


theorem pcsM1Value_eq_gen (x2v fev cval : U256) (ev : Nat → U256) (dx0v : U256)
    (a : Nat → U256) (ha0 : a 0 = dx0v) (ha1 : a 1 = 1)
    (hev : (ev 0).toNat < Midfall.Yul.blsR) :
    m1FEval fev x2v (m1Eval cval (ev 0) dx0v (BitVec.ofNat 256 Midfall.Yul.blsR))
      (BitVec.ofNat 256 Midfall.Yul.blsR) =
    pcsGenFEval (BitVec.ofNat 256 Midfall.Yul.blsR) x2v fev cval ev a 1 := by
  rw [pcsGenFEval_one (x2v := x2v) (fev := fev) (cval := cval) (ev := ev) (a := a) ha1]
  rw [ha0]
  unfold m1FEval m1Eval
  rw [pcs_field_distrib cval (ev 0) (SIInv dx0v) hev]


theorem pcsBatchName_dx (m i : Nat) (hi : i < m) : pcsBatchName m i = pcsDxName i := by
  unfold pcsBatchName pcsBatchInputs
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left]
  · simp [List.getElem?_map, List.getElem?_range, hi, pcsDxName]
  · simp only [List.length_map, List.length_range]; exact hi

theorem pcsBatchName_lb (m j : Nat) (hj : j < m) :
    pcsBatchName m (m + j) = pcsLbasisName j := by
  unfold pcsBatchName pcsBatchInputs
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right]
  · simp only [List.length_map, List.length_range]
    rw [show m + j - m = j by omega]
    simp [List.getElem?_map, List.getElem?_range, hj, pcsLbasisName]
  · simp only [List.length_map, List.length_range]; omega


theorem pcsPointRefs_mem (points : List Int) (distinct : List Int) {i : Nat}
    (hi : i < points.length) :
    (i, pcsRotPtRef distinct (points.get ⟨i, hi⟩)) ∈ pcsPointRefs points distinct := by
  unfold pcsPointRefs pcsRotPtRef
  apply List.mem_map.mpr
  have hi' : i < (Midfall.Generator.enumIdx points).length := by
    simp [Midfall.Generator.enumIdx]; exact hi
  refine ⟨(Midfall.Generator.enumIdx points)[i]'hi', List.getElem_mem (l := Midfall.Generator.enumIdx points) hi', ?_⟩
  simp [Midfall.Generator.enumIdx]


theorem pcsStmtsContractAll_append_halt {funs : FunEnv (Bridge.Dialect c g)}
    {ss1 ss2 : Block EVM.Op}
    {pre : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {mid : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop}
    (h1 : StmtsContractAll (D := Bridge.Dialect c g) funs ss1 pre
      (fun V st V' st' o => (o = .normal ∧ mid V' st') ∨
        (o = .halt ∧ post V st V' st' o)))
    (h2 : ∀ V st, pre V st → StmtsContractAll (D := Bridge.Dialect c g) funs ss2 mid
      (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (ss1 ++ ss2) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1run, h2run⟩ | ⟨h1run, hne⟩
  · rcases h1 V st hpre V1 st1 .normal h1run with ⟨_, hmid⟩ | ⟨hh, _⟩
    · exact h2 V st hpre V1 st1 hmid V' st' o h2run
    · cases hh
  · rcases h1 V st hpre V' st' o h1run with ⟨hh, _⟩ | ⟨_, hpost⟩
    · exact absurd hh hne
    · exact hpost



macro "pcs_ne1" : tactic => `(tactic|
  (intro h
   have hc := congrArg (fun s : String => s.toList.take 1) h
   simp [pcsDxName, pcsLbasisName, pcsBpName] at hc))

def PcsGPre (x3v rv x2v fev cptr qep : U256) (p : Nat → U256)
    (xs : List (Nat × String)) (n : Nat) :
    VEnv (Bridge.Dialect c g) → EvmState → Prop :=
  fun V st => VEnv.get V "x3" = some x3v ∧ VEnv.get V "r" = some rv ∧
    VEnv.get V "x2" = some x2v ∧ VEnv.get V "f_eval" = some fev ∧
    VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
    VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
    (∀ q ∈ xs, VEnv.get V q.2 = some (p q.1)) ∧
    (∀ i, i < n → VEnv.get V (pcsBpName i) = none) ∧
    (∀ g ∈ xs, VEnv.get V (pcsLbasisName g.1) = none)

def PcsGP1 (m n : Nat) (rv x2v fev cptr qep : U256) (p : Nat → U256) (a : Nat → U256)
    (xs : List (Nat × String)) :
    VEnv (Bridge.Dialect c g) → EvmState → Prop :=
  fun V st => VEnv.get V "r" = some rv ∧ VEnv.get V "x2" = some x2v ∧
    VEnv.get V "f_eval" = some fev ∧ VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
    VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
    (∀ q ∈ xs, VEnv.get V q.2 = some (p q.1)) ∧
    (∀ i, i < m → VEnv.get V (pcsDxName i) = some (a i)) ∧
    (∀ i, i < n → VEnv.get V (pcsBpName i) = none) ∧
    (∀ g ∈ xs, VEnv.get V (pcsLbasisName g.1) = none)

def PcsGP2 (m n : Nat) (rv x2v fev cptr qep : U256) (a : Nat → U256)
    (xs : List (Nat × String)) :
    VEnv (Bridge.Dialect c g) → EvmState → Prop :=
  fun V st => VEnv.get V "r" = some rv ∧ VEnv.get V "x2" = some x2v ∧
    VEnv.get V "f_eval" = some fev ∧ VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
    VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
    (∀ i, i < m → VEnv.get V (pcsDxName i) = some (a i)) ∧
    (∀ j, j < m → VEnv.get V (pcsLbasisName j) = some (a (m + j))) ∧
    (∀ i, i < n → VEnv.get V (pcsBpName i) = none)

def PcsGP3 (n : Nat) (rv x2v fev cptr qep : U256) (a : Nat → U256)
    (nm : Nat → String) :
    VEnv (Bridge.Dialect c g) → EvmState → Prop :=
  fun V st => VEnv.get V "r" = some rv ∧ VEnv.get V "x2" = some x2v ∧
    VEnv.get V "f_eval" = some fev ∧ VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
    VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
    (∀ i, i < n → VEnv.get V (pcsBpName i) = some (pcsBpVal rv a i)) ∧
    (∀ i, i < n → VEnv.get V (nm i) = some (a i))

theorem pcsStmtsContractAll_append_mid4 {funs : FunEnv (Bridge.Dialect c g)}
    {ss1 ss2 : Block EVM.Op}
    {pre : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {mid : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop}
    (h1 : StmtsContractAll (D := Bridge.Dialect c g) funs ss1 pre
      (fun V st V' st' o => o = .normal ∧ mid V st V' st'))
    (h2 : ∀ V st, pre V st → StmtsContractAll (D := Bridge.Dialect c g) funs ss2
      (fun V' st' => mid V st V' st')
      (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (ss1 ++ ss2) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1run, h2run⟩ | ⟨h1run, hne⟩
  · obtain ⟨_, hmid⟩ := h1 V st hpre V1 st1 .normal h1run
    exact h2 V st hpre V1 st1 hmid V' st' o h2run
  · exact absurd (h1 V st hpre V' st' o h1run).1 hne

set_option maxHeartbeats 30000000 in

theorem pcsSetBlockAst_eq_gen (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off : Nat) (hm : 1 < points.length) :
    GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off =
      pcsSetBodyGen setIdx points distinctRotations off := by
  unfold GenAstPcs.pcsSetBlockAst pcsSetBodyGen
  dsimp only
  split
  · rename_i h
    have h1 : points.length = 1 := by simpa using h
    omega
  · rfl

set_option maxHeartbeats 30000000 in
theorem pcsGenPrefix_contract {funs : FunEnv (Bridge.Dialect c g)}
    (points : List Int) (distinctRotations : List Int)
    (xs : List (Nat × String)) (ks : Nat → List (Nat × String))
    (n : Nat) (nm : Nat → String) (p a : Nat → U256) (x3v rv x2v fev cptr qep : U256)
    (hm : 1 < points.length)
    (hxs : xs = pcsPointRefs points distinctRotations)
    (hks : ks = pcsKs points distinctRotations)
    (hnm : nm = pcsBatchName points.length)
    (hn : n = (pcsBatchInputs points.length).length)
    (hnames : PcsGenNames points.length xs ks)
    (hvalDx : ∀ i, i < points.length → a i = wAddmodAt x3v (rv - p i) rv)
    (hvalLb : ∀ j, j < points.length →
      a (points.length + j) = pcsLbasisVal rv (p j) p (ks j))
    (hks_sub : ∀ g ∈ xs, ∀ k ∈ ks g.1, k ∈ xs) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      ((xs.map (fun q => pcsDxStmt q.1 q.2))
        ++ (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten
        ++ pcsBpLines n nm)
      (PcsGPre x3v rv x2v fev cptr qep p xs n)
      (fun V st V' st' o => o = .normal ∧ PcsGP3 n rv x2v fev cptr qep a nm V' st' ∧
        st' = st) := by
  intro V st hpre V' st' o hrun
  unfold PcsGPre at hpre
  obtain ⟨hx3, hr, hx2, hf, hcptrV, hqepV, hrot, hbpnone, hlbnone⟩ := hpre
  have hmem : ∀ (i : Nat) (hi : i < points.length),
      (i, pcsRotPtRef distinctRotations (points.get ⟨i, hi⟩)) ∈ xs := by
    intro i hi
    rw [hxs]
    exact pcsPointRefs_mem points distinctRotations hi
  -- dx lines
  have hdx : StmtsContractAll (D := Bridge.Dialect c g) funs
      (xs.map (fun q => pcsDxStmt q.1 q.2))
      (fun V st => VEnv.get V "x3" = some x3v ∧ VEnv.get V "r" = some rv ∧
        (∀ q ∈ xs, VEnv.get V q.2 = some (p q.1)))
      (fun V st V' st' o => o = .normal ∧
        (∀ i, i < points.length → VEnv.get V' (pcsDxName i) = some (a i)) ∧
        (∀ y, (∀ q ∈ xs, y ≠ pcsDxName q.1) → VEnv.get V' y = VEnv.get V y) ∧
        st' = st) := by
    intro V0 st0 hp V1 st1 o1 h1
    obtain ⟨hx3', hr', hrot'⟩ := hp
    obtain ⟨ho, hgets, hpres, hst⟩ := pcsDxLines_contract
      (c := c) (g := g) (funs := funs) xs x3v rv p
      hnames.dxX3 hnames.dxR hnames.dxRot hnames.dxIdx hnames.dxDist
      V0 st0 ⟨hx3', hr', hrot'⟩ V1 st1 o1 h1
    refine ⟨ho, ?_, hpres, hst⟩
    intro i hi
    rw [hgets (i, pcsRotPtRef distinctRotations (points.get ⟨i, hi⟩)) (hmem i hi)]
    simpa using (hvalDx i hi).symm
  let P1 := PcsGP1 (c := c) (g := g) points.length n rv x2v fev cptr qep p a xs
  have hdx' : StmtsContractAll (D := Bridge.Dialect c g) funs
      (xs.map (fun q => pcsDxStmt q.1 q.2))
      (PcsGPre x3v rv x2v fev cptr qep p xs n)
      (fun V st V' st' o => o = .normal ∧ P1 V' st' ∧ st' = st) := by
    intro V0 st0 hp V1 st1 o1 h1
    unfold PcsGPre at hp
    obtain ⟨hx3', hr', hx2', hf', hcptr', hqep', hrot', hbp', hlb'⟩ := hp
    obtain ⟨ho, hgets, hpres, hst⟩ := hdx V0 st0 ⟨hx3', hr', hrot'⟩ V1 st1 o1 h1
    refine ⟨ho, ?_, hst⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hgets, ?_, ?_⟩
    · rw [hpres "r" (fun q hq => by
        intro h; exact hnames.dxR q hq h.symm)]
      exact hr'
    · rw [hpres "x2" (fun q hq => by pcs_ne1)]
      exact hx2'
    · rw [hpres "f_eval" (fun q hq => by pcs_ne1)]
      exact hf'
    · rw [hpres "Q_EVAL_CPTR" (fun q hq => by pcs_ne1)]
      exact hcptr'
    · rw [hpres "Q_EVAL_SET_MPTR" (fun q hq => by pcs_ne1)]
      exact hqep'
    · intro q hq
      rw [hpres q.2 (fun r hr => hnames.dxRot q hq r hr)]
      exact hrot' q hq
    · intro i hi
      rw [hpres (pcsBpName i) (fun q hq => by pcs_ne1)]
      exact hbp' i hi
    · intro g hg
      rw [hpres (pcsLbasisName g.1) (fun q hq => by
        intro h; exact (hnames.lbDx g hg q hq) h)]
      exact hlb' g hg
  -- lbasis groups
  let P2 := PcsGP2 (c := c) (g := g) points.length n rv x2v fev cptr qep a xs
  have hlb : StmtsContractAll (D := Bridge.Dialect c g) funs
      (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten
      P1 (fun V st V' st' o => o = .normal ∧ P2 V' st' ∧ st' = st) := by
    intro V0 st0 hp V1 st1 o1 h1
    obtain ⟨hr', hx2', hf', hcptr', hqep', hrot', hdx', hbp', hlb'⟩ := hp
    obtain ⟨ho, hlgets, hpres, hst⟩ := pcsLbasisLines_contract
      (c := c) (g := g) (funs := funs) xs ks rv p
      hnames.lbR hnames.lbPt hnames.lbKs hnames.lbRot hnames.lbRot2
      hnames.lbDist hnames.lbIdx
      V0 st0 ⟨hr', hrot', (fun g hg k hk => hrot' k (hks_sub g hg k hk)), hlb'⟩
      V1 st1 o1 h1
    refine ⟨ho, ?_, hst⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpres "r" (fun g hg => by pcs_ne1)]
      exact hr'
    · rw [hpres "x2" (fun g hg => by pcs_ne1)]
      exact hx2'
    · rw [hpres "f_eval" (fun g hg => by pcs_ne1)]
      exact hf'
    · rw [hpres "Q_EVAL_CPTR" (fun g hg => by pcs_ne1)]
      exact hcptr'
    · rw [hpres "Q_EVAL_SET_MPTR" (fun g hg => by pcs_ne1)]
      exact hqep'
    · intro i hi
      rw [hpres (pcsDxName i) (fun g hg => by
        intro h
        exact (hnames.lbDx g hg (i, pcsRotPtRef distinctRotations (points.get ⟨i, hi⟩))
          (hmem i hi)) h.symm)]
      exact hdx' i hi
    · intro j hj
      rw [hlgets (j, pcsRotPtRef distinctRotations (points.get ⟨j, hj⟩)) (hmem j hj)]
      simpa using (hvalLb j hj).symm
    · intro i hi
      rw [hpres (pcsBpName i) (fun g hg => by pcs_ne1)]
      exact hbp' i hi
  have h12 : StmtsContractAll (D := Bridge.Dialect c g) funs
      ((xs.map (fun q => pcsDxStmt q.1 q.2))
        ++ (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten)
      (PcsGPre x3v rv x2v fev cptr qep p xs n)
      (fun V0 st0 V' st' o => o = .normal ∧ P2 V' st' ∧ st' = st0) :=
    pcsStmtsContractAll_append_mid4 (c := c) (g := g) (funs := funs)
      (ss1 := xs.map (fun q => pcsDxStmt q.1 q.2))
      (ss2 := (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten)
      (pre := PcsGPre x3v rv x2v fev cptr qep p xs n)
      (mid := fun V0 st0 V' st' => P1 V' st' ∧ st' = st0)
      (post := fun V0 st0 V' st' o => o = .normal ∧ P2 V' st' ∧ st' = st0)
      hdx' (fun V0 st0 _hp => by
        intro V1 st1 hmid V2 st2 o2 h2
        obtain ⟨ho, hp2, hst2⟩ := hlb V1 st1 hmid.1 V2 st2 o2 h2
        exact ⟨ho, hp2, hst2.trans hmid.2⟩)
  -- bp lines
  let P3 := PcsGP3 (c := c) (g := g) n rv x2v fev cptr qep a nm
  have hbp : StmtsContractAll (D := Bridge.Dialect c g) funs
      (pcsBpLines n nm) P2 (fun V st V' st' o => o = .normal ∧ P3 V' st' ∧ st' = st) := by
    intro V0 st0 hp V1 st1 o1 h1
    obtain ⟨hr', hx2', hf', hcptr', hqep', hdx', hlb', hbp'⟩ := hp
    have hnmv : ∀ i, i < n → VEnv.get V0 (nm i) = some (a i) := by
      intro i hi
      rw [hn] at hi
      have hi2 : i < 2 * points.length := by
        rw [pcsBatchInputs_length] at hi; exact hi
      by_cases him : i < points.length
      · rw [hnm, pcsBatchName_dx points.length i him]
        exact hdx' i him
      · let j := i - points.length
        have hj : j < points.length := by omega
        have hi_eq : i = points.length + j := by omega
        rw [hi_eq, hnm, pcsBatchName_lb points.length j hj]
        simpa [j] using hlb' j hj
    have hbpR : ∀ i, i < n → pcsBpName i ≠ "r" :=
      fun i hi => hnames.bpR i (by rw [← hn]; exact hi)
    have hbpIn : ∀ i, i < n → ∀ j, j < n → pcsBpName i ≠ nm j :=
      fun i hi j hj => by
        rw [hnm]
        exact hnames.bpIn i (by rw [← hn]; exact hi) j (by rw [← hn]; exact hj)
    have hbpDist : ∀ i, i < n → ∀ j, j < n → i ≠ j → pcsBpName i ≠ pcsBpName j :=
      fun i hi j hj hij => hnames.bpDist i (by rw [← hn]; exact hi) j
        (by rw [← hn]; exact hj) hij
    obtain ⟨ho, hbgets, hpres, hst⟩ := pcsBpLines_contract
      (c := c) (g := g) (funs := funs) n nm rv a (by
        rw [hn, pcsBatchInputs_length]; omega)
      hbpR hbpIn hbpDist
      V0 st0 ⟨hr', hnmv, hbp'⟩ V1 st1 o1 h1
    refine ⟨ho, ?_, hst⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, hbgets, ?_⟩
    · rw [hpres "r" (fun i hi => by pcs_ne1)]
      exact hr'
    · rw [hpres "x2" (fun i hi => by pcs_ne1)]
      exact hx2'
    · rw [hpres "f_eval" (fun i hi => by pcs_ne1)]
      exact hf'
    · rw [hpres "Q_EVAL_CPTR" (fun i hi => by pcs_ne1)]
      exact hcptr'
    · rw [hpres "Q_EVAL_SET_MPTR" (fun i hi => by pcs_ne1)]
      exact hqep'
    · intro i hi
      rw [hpres (nm i) (fun j hj => by
        intro h; exact (hbpIn j hj i hi) h.symm)]
      exact hnmv i hi
  have h123 : StmtsContractAll (D := Bridge.Dialect c g) funs
      ((xs.map (fun q => pcsDxStmt q.1 q.2))
        ++ (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten
        ++ pcsBpLines n nm)
      (PcsGPre x3v rv x2v fev cptr qep p xs n)
      (fun V0 st0 V' st' o => o = .normal ∧ P3 V' st' ∧ st' = st0) :=
    pcsStmtsContractAll_append_mid4 (c := c) (g := g) (funs := funs)
      (ss1 := (xs.map (fun q => pcsDxStmt q.1 q.2))
        ++ (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten)
      (ss2 := pcsBpLines n nm)
      (pre := PcsGPre x3v rv x2v fev cptr qep p xs n)
      (mid := fun V0 st0 V' st' => P2 V' st' ∧ st' = st0)
      (post := fun V0 st0 V' st' o => o = .normal ∧ P3 V' st' ∧ st' = st0)
      (by simpa [List.append_assoc] using h12) (fun V0 st0 _hp => by
        intro V1 st1 hmid V2 st2 o2 h2
        obtain ⟨ho, hp3, hst2⟩ := hbp V1 st1 hmid.1 V2 st2 o2 h2
        exact ⟨ho, hp3, hst2.trans hmid.2⟩)
  exact h123 V st ⟨hx3, hr, hx2, hf, hcptrV, hqepV, hrot, hbpnone, hlbnone⟩ V' st' o hrun


def PcsGP4 (m n : Nat) (rv x2v fev cptr qep : U256) (a : Nat → U256)
    (invName : Nat → String) :
    VEnv (Bridge.Dialect c g) → EvmState → Prop :=
  fun V st => VEnv.get V "r" = some rv ∧ VEnv.get V "x2" = some x2v ∧
    VEnv.get V "f_eval" = some fev ∧ VEnv.get V "Q_EVAL_CPTR" = some cptr ∧
    VEnv.get V "Q_EVAL_SET_MPTR" = some qep ∧
    (∀ i, i < n → VEnv.get V (invName i) = some (SIInv (a i))) ∧
    VEnv.get V "den_inv" = some (pcsDenInvVal rv (fun j => SIInv (a j)) m)

theorem pcsYletBq_contract {funs : FunEnv (Bridge.Dialect c g)}
    (x : String) (bqv : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [GenAst.ylet x (GenAst.yvar "bq")]
      (fun V st => VEnv.get V "bq" = some bqv)
      (fun V st V' st' o => o = .normal ∧ V' = (x, bqv) :: V ∧
        VEnv.get V' x = some bqv ∧
        (∀ y, y ≠ x → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  have hstmt : StmtContractAll (D := Bridge.Dialect c g) funs
      (GenAst.ylet x (GenAst.yvar "bq"))
      (fun V st => VEnv.get V "bq" = some bqv)
      (fun V st V' st' o => o = .normal ∧ V' = (x, bqv) :: V ∧
        VEnv.get V' x = some bqv ∧
        (∀ y, y ≠ x → VEnv.get V' y = VEnv.get V y) ∧ st' = st) := by
    intro V0 st0 hp V1 st1 o1 h1
    obtain ⟨ho, yv, hyv, hV, hst⟩ := b1_exec_ylet_var h1
    have hye : yv = bqv := Option.some.inj (hyv.symm.trans hp)
    refine ⟨ho, by rw [hV, hye], by rw [hV, hye]; exact venv_get_cons_self _ _ _, ?_, hst⟩
    intro y hy
    rw [hV]
    exact venv_get_cons_ne (D := Bridge.Dialect c g) (x := x) (y := y) (v := yv) hy
  exact stmtsContractAll_singleton hstmt V st hpre V' st' o hrun

theorem pcsStmtsContractAll_append_halt' {funs : FunEnv (Bridge.Dialect c g)}
    {ss1 ss2 : Block EVM.Op}
    {pre : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {mid : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop}
    (h1 : StmtsContractAll (D := Bridge.Dialect c g) funs ss1 pre
      (fun V st V' st' o => (o = .normal ∧ mid V st V' st') ∨
        (o = .halt ∧ post V st V' st' o)))
    (h2 : ∀ V st, pre V st → StmtsContractAll (D := Bridge.Dialect c g) funs ss2
      (fun V' st' => mid V st V' st')
      (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (ss1 ++ ss2) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1run, h2run⟩ | ⟨h1run, hne⟩
  · rcases h1 V st hpre V1 st1 .normal h1run with ⟨_, hmid⟩ | ⟨hh, _⟩
    · exact h2 V st hpre V1 st1 hmid V' st' o h2run
    · cases hh
  · rcases h1 V st hpre V' st' o h1run with ⟨hh, _⟩ | ⟨_, hpost⟩
    · exact absurd hh hne
    · exact hpost

set_option maxHeartbeats 30000000 in
theorem pcsGenBatch_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (points : List Int) (distinctRotations : List Int)
    (xs : List (Nat × String)) (ks : Nat → List (Nat × String))
    (n : Nat) (nm invName : Nat → String) (a : Nat → U256)
    (rv x2v fev cptr qep : U256)
    (scratch gasN selN selP : Nat) (hbls : Nat)
    (hm : 1 < points.length)
    (hxs : xs = pcsPointRefs points distinctRotations)
    (hn : n = (pcsBatchInputs points.length).length)
    (hnm : nm = pcsBatchName points.length)
    (hinv : invName = pcsInvName points.length)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hnames : PcsGenNames points.length xs ks)
    (hainlt : ∀ i, i < n → (a i).toNat < blsR)
    (hain0 : ∀ i, i < n → (a i).toNat ≠ 0)
    (hinv0Dist : ∀ j, 1 ≤ j → j < n → invName 0 ≠ invName j)
    (hinvR0 : invName 0 ≠ "r")
    (hinvX2 : ∀ i, invName i ≠ "x2")
    (hinvF : ∀ i, invName i ≠ "f_eval")
    (hinvQ : ∀ i, invName i ≠ "Q_EVAL_CPTR")
    (hrv : rv = BitVec.ofNat 256 blsR)
    (hinvQSet : ∀ i, invName i ≠ "Q_EVAL_SET_MPTR")
    (hinvEval : ∀ i, invName i ≠ "eval")
    (hdenInvAll : ∀ i, i < n → "den_inv" ≠ invName i) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      ([pcsBqStmt (pcsBpName (n - 1))] ++ pcsBqLines n nm invName
        ++ [GenAst.ylet (invName 0) (GenAst.yvar "bq")]
        ++ pcsDenInvLines points.length invName)
      (PcsGP3 (c := permissive (callsOf product)) (g := g)
        n rv x2v fev cptr qep a nm)
      (fun V st V' st' o =>
        (o = .normal ∧ PcsGP4 (c := permissive (callsOf product)) (g := g)
          points.length n rv x2v fev cptr qep a invName V' st' ∧
          MemSameOutside st st' scratch 192 ∧ st'.env = st.env) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  unfold PcsGP3 at hpre
  obtain ⟨hr, hx2, hf, hcptrV, hqepV, hbp, hinp⟩ := hpre
  have hnpos : 0 < n := by rw [hn, pcsBatchInputs_length]; omega
  have hmn : points.length < n := by rw [hn, pcsBatchInputs_length]; omega
  let Mid4 : VEnv (Bridge.Dialect (permissive (callsOf product)) g) → EvmState →
      VEnv (Bridge.Dialect (permissive (callsOf product)) g) → EvmState → Prop :=
    fun V0 st0 V1 st1 => VEnv.get V1 "bq" = some (SIInv (pcsBpVal rv a (n - 1))) ∧
      (∀ i, i < n → VEnv.get V1 (pcsBpName i) = some (pcsBpVal rv a i)) ∧
      (∀ i, i < n → VEnv.get V1 (nm i) = some (a i)) ∧
      VEnv.get V1 "r" = some rv ∧ VEnv.get V1 "x2" = some x2v ∧
      VEnv.get V1 "f_eval" = some fev ∧ VEnv.get V1 "Q_EVAL_CPTR" = some cptr ∧
      VEnv.get V1 "Q_EVAL_SET_MPTR" = some qep ∧
      MemSameOutside st0 st1 scratch 192 ∧ st1.env = st0.env
  have hbq : StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      [pcsBqStmt (pcsBpName (n - 1))] (PcsGP3 n rv x2v fev cptr qep a nm)
      (fun V0 st0 V1 st1 o1 => (o1 = .normal ∧ Mid4 V0 st0 V1 st1) ∨
        (o1 = .halt ∧ Midfall.LoweringV2.Reverted st1)) := by
    intro V0 st0 hp V1 st1 o1 h1
    unfold PcsGP3 at hp
    obtain ⟨hr', hx2', hf', hcptr', hqep', hbp', hinp'⟩ := hp
    have hprev : VEnv.get V0 (pcsBpName (n - 1)) =
        some (pcsBpVal rv a (n - 1)) := hbp' (n - 1) (by omega)
    have hlt : (pcsBpVal rv a (n - 1)).toNat < blsR := by
      rw [hrv]
      exact pcsBpVal_toNat_lt a (n - 1) (fun i hi => hainlt i (by omega)) (n - 1) (by omega)
    have h0 : (pcsBpVal rv a (n - 1)).toNat ≠ 0 := by
      rw [hrv]
      exact fun h => pcsBpVal_ne_zero a (n - 1) (fun i hi => hainlt i (by omega))
        (fun i hi => hain0 i (by omega)) (n - 1) (by omega)
        (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have h0pos : 0 < (pcsBpVal rv a (n - 1)).toNat := Nat.pos_of_ne_zero h0
    rcases stmtsContractAll_singleton (pcsBq_contract (product := product) (funs := funs)
      (decl := decl) (cenv := cenv) (cenv' := cenv')
      scratch hbls gasN selN selP (pcsBpName (n - 1)) (pcsBpVal rv a (n - 1))
      hlook hbody hparams hrets hnbls hscratch hscratch256 hfail)
      V0 st0 ⟨hprev, h0pos, hlt⟩ V1 st1 o1 h1 with
      ⟨ho, hV, hfr, henv⟩ | ⟨ho, hrev⟩
    · refine Or.inl ⟨ho, ?_⟩
      rw [hV] at ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr, henv⟩
      · exact venv_get_cons_self (D := Bridge.Dialect (permissive (callsOf product)) g) V0 _ _
      · intro i hi
        rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := pcsBpName i) (v := SIInv (pcsBpVal rv a (n - 1)))
          (hnames.bqBp i (by rw [← hn]; exact hi))]
        exact hbp' i hi
      · intro i hi
        rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := nm i) (v := SIInv (pcsBpVal rv a (n - 1)))
          (by rw [hnm]; exact hnames.bqInp i (by rw [← hn]; exact hi))]
        exact hinp' i hi
      · rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := "r") (v := SIInv (pcsBpVal rv a (n - 1))) hnames.bqR.symm]
        exact hr'
      · rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := "x2") (v := SIInv (pcsBpVal rv a (n - 1))) (by pcs_ne1)]
        exact hx2'
      · rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := "f_eval") (v := SIInv (pcsBpVal rv a (n - 1))) (by pcs_ne1)]
        exact hf'
      · rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := "Q_EVAL_CPTR") (v := SIInv (pcsBpVal rv a (n - 1))) (by pcs_ne1)]
        exact hcptr'
      · rw [venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
          (x := "bq") (y := "Q_EVAL_SET_MPTR") (v := SIInv (pcsBpVal rv a (n - 1))) (by pcs_ne1)]
        exact hqep'
    · exact Or.inr ⟨ho, hrev⟩
  let Mid5 : VEnv (Bridge.Dialect (permissive (callsOf product)) g) → EvmState →
      VEnv (Bridge.Dialect (permissive (callsOf product)) g) → EvmState → Prop :=
    fun V0 st0 V1 st1 => VEnv.get V1 "bq" = some (SIInv (a 0)) ∧
      (∀ i, 1 ≤ i → i < n → VEnv.get V1 (invName i) = some (SIInv (a i))) ∧
      VEnv.get V1 "r" = some rv ∧ VEnv.get V1 "x2" = some x2v ∧
      VEnv.get V1 "f_eval" = some fev ∧ VEnv.get V1 "Q_EVAL_CPTR" = some cptr ∧
      VEnv.get V1 "Q_EVAL_SET_MPTR" = some qep ∧
      MemSameOutside st0 st1 scratch 192 ∧ st1.env = st0.env
  have hbqlines : StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (pcsBqLines n nm invName)
      (fun V1 st1 => Mid4 V st V1 st1)
      (fun _ _ V1 st1 o1 => o1 = .normal ∧ Mid5 V st V1 st1) := by
    intro V1 st1 hm V2 st2 o2 h2
    obtain ⟨hbq1, hbp1, hinp1, hr1, hx21, hf1, hq1, hqset1, hfr1, henv1⟩ := hm
    have hinvBq' : ∀ i, 1 ≤ i → i < n → invName i ≠ "bq" := by
      intro i hi1 hin; rw [hinv]; exact hnames.invBq i hi1 (by rw [← hn]; exact hin)
    have hinvPrev' : ∀ i, 1 ≤ i → i < n → invName i ≠ pcsBpName (i - 1) := by
      intro i hi1 hin; rw [hinv]; exact hnames.invPrev i hi1 (by rw [← hn]; exact hin)
    have hinvInp' : ∀ i, 1 ≤ i → i < n → invName i ≠ nm i := by
      intro i hi1 hin; rw [hinv, hnm]; exact hnames.invInp i hi1 (by rw [← hn]; exact hin)
    have hinvR' : ∀ i, 1 ≤ i → i < n → invName i ≠ "r" := by
      intro i hi1 hin; rw [hinv]; exact hnames.invR i hi1 (by rw [← hn]; exact hin)
    have hbqBp' : ∀ i, i < n → pcsBpName i ≠ "bq" := by
      intro i hi; exact hnames.bqBp i (by rw [← hn]; exact hi)
    have hbqInp' : ∀ i, i < n → nm i ≠ "bq" := by
      intro i hi; rw [hnm]; exact hnames.bqInp i (by rw [← hn]; exact hi)
    have hinvBp' : ∀ i, 1 ≤ i → i < n → ∀ j, j < n → pcsBpName j ≠ invName i := by
      intro i hi1 hin j hj; rw [hinv]
      exact hnames.invBp i hi1 (by rw [← hn]; exact hin) j (by rw [← hn]; exact hj)
    have hinvInp2' : ∀ i, 1 ≤ i → i < n → ∀ j, j < n → nm j ≠ invName i := by
      intro i hi1 hin j hj; rw [hinv, hnm]
      exact hnames.invInp2 i hi1 (by rw [← hn]; exact hin) j (by rw [← hn]; exact hj)
    have hrInv' : ∀ i, 1 ≤ i → i < n → "r" ≠ invName i := by
      intro i hi1 hin; rw [hinv]; exact hnames.rInv i hi1 (by rw [← hn]; exact hin)
    have hinvDist' : ∀ i, 1 ≤ i → i < n → ∀ j, 1 ≤ j → j < n → i ≠ j →
        invName i ≠ invName j := by
      intro i hi1 hin j hj1 hjn hij; rw [hinv]
      exact hnames.invDist i hi1 (by rw [← hn]; exact hin) j hj1 (by rw [← hn]; exact hjn) hij
    have hbq1' : VEnv.get V1 "bq" =
        some (SIInv (pcsBpVal (BitVec.ofNat 256 blsR) a (n - 1))) := by
      simpa [hrv] using hbq1
    have hr1' : VEnv.get V1 "r" = some (BitVec.ofNat 256 blsR) := by
      simpa [hrv] using hr1
    have hbp1' : ∀ i, i < n →
        VEnv.get V1 (pcsBpName i) = some (pcsBpVal (BitVec.ofNat 256 blsR) a i) :=
      fun i hi => by simpa [hrv] using hbp1 i hi
    obtain ⟨ho, hbqf, hinvf, hpres, hst⟩ := pcsBqLines_contract
      (c := permissive (callsOf product)) (g := g) (funs := funs)
      n nm invName a (by omega)
      (fun i hi => hainlt i hi) (fun i hi => hain0 i hi)
      hnames.bqR hinvBq' hinvPrev' hinvInp' hinvR'
      hbqBp' hbqInp' hinvBp' hinvInp2' hrInv' hinvDist'
      V1 st1 ⟨hbq1', hr1', hbp1', hinp1⟩ V2 st2 o2 h2
    refine ⟨ho, ?_⟩
    refine ⟨hbqf, hinvf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpres "r" hnames.bqR.symm (fun i hi1 hin => hrInv' i hi1 hin)]
      exact hr1
    · rw [hpres "x2" (by pcs_ne1) (fun i hi1 hin => (hinvX2 i).symm)]
      exact hx21
    · rw [hpres "f_eval" (by pcs_ne1) (fun i hi1 hin => (hinvF i).symm)]
      exact hf1
    · rw [hpres "Q_EVAL_CPTR" (by pcs_ne1) (fun i hi1 hin => (hinvQ i).symm)]
      exact hq1
    · rw [hpres "Q_EVAL_SET_MPTR" (by pcs_ne1) (fun i hi1 hin => (hinvQSet i).symm)]
      exact hqset1
    · rw [hst]; exact hfr1
    · rw [hst]; exact henv1
  let Mid6 : VEnv (Bridge.Dialect (permissive (callsOf product)) g) → EvmState →
      VEnv (Bridge.Dialect (permissive (callsOf product)) g) → EvmState → Prop :=
    fun V0 st0 V1 st1 => (∀ i, i < n → VEnv.get V1 (invName i) = some (SIInv (a i))) ∧
      VEnv.get V1 "r" = some rv ∧ VEnv.get V1 "x2" = some x2v ∧
      VEnv.get V1 "f_eval" = some fev ∧ VEnv.get V1 "Q_EVAL_CPTR" = some cptr ∧
      VEnv.get V1 "Q_EVAL_SET_MPTR" = some qep ∧
      MemSameOutside st0 st1 scratch 192 ∧ st1.env = st0.env
  have hlet : StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      [GenAst.ylet (invName 0) (GenAst.yvar "bq")]
      (fun V1 st1 => Mid5 V st V1 st1)
      (fun _ _ V1 st1 o1 => o1 = .normal ∧ Mid6 V st V1 st1) := by
    intro V1 st1 hm V2 st2 o2 h2
    obtain ⟨hbq1, hinv1, hr1, hx21, hf1, hq1, hqset1, hfr1, henv1⟩ := hm
    obtain ⟨ho, hV, hget, hpres, hst⟩ := pcsYletBq_contract (c := permissive (callsOf product))
      (g := g) (funs := funs) (invName 0) (SIInv (a 0)) V1 st1 hbq1 V2 st2 o2 h2
    refine ⟨ho, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hget]
      · rw [hpres (invName i) (fun h => hinv0Dist i hi0 hi h.symm)]
        exact hinv1 i hi0 hi
    · rw [hpres "r" (fun h => hinvR0 h.symm)]
      exact hr1
    · rw [hpres "x2" (fun h => hinvX2 0 h.symm)]
      exact hx21
    · rw [hpres "f_eval" (fun h => hinvF 0 h.symm)]
      exact hf1
    · rw [hpres "Q_EVAL_CPTR" (fun h => hinvQ 0 h.symm)]
      exact hq1
    · rw [hpres "Q_EVAL_SET_MPTR" (fun h => hinvQSet 0 h.symm)]
      exact hqset1
    · rw [hst]; exact hfr1
    · rw [hst]; exact henv1
  have hden : StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (pcsDenInvLines points.length invName)
      (fun V1 st1 => Mid6 V st V1 st1)
      (fun _ _ V1 st1 o1 => o1 = .normal ∧ PcsGP4 (c := permissive (callsOf product)) (g := g)
        points.length n rv x2v fev cptr qep a invName V1 st1 ∧
        MemSameOutside st st1 scratch 192 ∧ st1.env = st.env) := by
    intro V1 st1 hm V2 st2 o2 h2
    obtain ⟨hinv1, hr1, hx21, hf1, hq1, hqset1, hfr1, henv1⟩ := hm
    have hr1' : VEnv.get V1 "r" = some (BitVec.ofNat 256 blsR) := by
      simpa [hrv] using hr1
    have hpre : VEnv.get V1 "r" = some (BitVec.ofNat 256 blsR) ∧
        (∀ j, j < points.length → VEnv.get V1 (invName j) = some (SIInv (a j))) :=
      ⟨hr1', fun j hj => hinv1 j (by omega)⟩
    obtain ⟨ho, hdenv, hpres, hst⟩ := pcsDenInvLines_contract
      (c := permissive (callsOf product)) (g := g) (funs := funs)
      points.length invName a (by omega)
      (fun j hj => hdenInvAll j (by omega)) hnames.denR
      V1 st1 hpre V2 st2 o2 h2
    refine ⟨ho, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simpa [hrv] using hdenv⟩
      · rw [hpres "r" (fun h => hnames.denR h.symm)]
        exact hr1
      · rw [hpres "x2" (by pcs_ne1)]
        exact hx21
      · rw [hpres "f_eval" (by pcs_ne1)]
        exact hf1
      · rw [hpres "Q_EVAL_CPTR" (by pcs_ne1)]
        exact hq1
      · rw [hpres "Q_EVAL_SET_MPTR" (by pcs_ne1)]
        exact hqset1
      · intro i hi
        rw [hpres (invName i) (fun h => (hdenInvAll i hi) h.symm)]
        exact hinv1 i hi
    · rw [hst]; exact hfr1
    · rw [hst]; exact henv1
  have hsuffix : StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (pcsBqLines n nm invName ++ [GenAst.ylet (invName 0) (GenAst.yvar "bq")]
        ++ pcsDenInvLines points.length invName)
      (fun V1 st1 => Mid4 V st V1 st1)
      (fun _ _ V1 st1 o1 => o1 = .normal ∧ PcsGP4 (c := permissive (callsOf product)) (g := g)
        points.length n rv x2v fev cptr qep a invName V1 st1 ∧
        MemSameOutside st st1 scratch 192 ∧ st1.env = st.env) := by
    simpa [List.append_assoc] using
      (pcsStmtsContractAll_append_mid4 (c := permissive (callsOf product)) (g := g) (funs := funs)
      (ss1 := pcsBqLines n nm invName)
      (ss2 := [GenAst.ylet (invName 0) (GenAst.yvar "bq")] ++ pcsDenInvLines points.length invName)
      (pre := fun V1 st1 => Mid4 V st V1 st1)
      (mid := fun _ _ V1 st1 => Mid5 V st V1 st1)
      (post := fun _ _ V1 st1 o1 => o1 = .normal ∧
        PcsGP4 (c := permissive (callsOf product)) (g := g)
          points.length n rv x2v fev cptr qep a invName V1 st1 ∧
        MemSameOutside st st1 scratch 192 ∧ st1.env = st.env)
      hbqlines (fun V1 st1 hm => by
        have hrest : StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
            ([GenAst.ylet (invName 0) (GenAst.yvar "bq")]
              ++ pcsDenInvLines points.length invName)
            (fun V2 st2 => Mid5 V st V2 st2)
            (fun _ _ V2 st2 o2 => o2 = .normal ∧
              PcsGP4 (c := permissive (callsOf product)) (g := g)
                points.length n rv x2v fev cptr qep a invName V2 st2 ∧
              MemSameOutside st st2 scratch 192 ∧ st2.env = st.env) :=
          pcsStmtsContractAll_append_mid4 (c := permissive (callsOf product)) (g := g)
            (funs := funs)
            (ss1 := [GenAst.ylet (invName 0) (GenAst.yvar "bq")])
            (ss2 := pcsDenInvLines points.length invName)
            (pre := fun V2 st2 => Mid5 V st V2 st2)
            (mid := fun _ _ V1 st1 => Mid6 V st V1 st1)
            (post := fun _ _ V2 st2 o2 => o2 = .normal ∧
              PcsGP4 (c := permissive (callsOf product)) (g := g)
                points.length n rv x2v fev cptr qep a invName V2 st2 ∧
              MemSameOutside st st2 scratch 192 ∧ st2.env = st.env)
            hlet (fun V2 st2 hm2 => hden)
        exact hrest))
  have hrun' : ExecStmts (Bridge.Dialect (permissive (callsOf product)) g) funs V st
      ([pcsBqStmt (pcsBpName (n - 1))] ++ (pcsBqLines n nm invName
        ++ ([GenAst.ylet (invName 0) (GenAst.yvar "bq")]
          ++ pcsDenInvLines points.length invName))) V' st' o := by
    simpa [List.append_assoc] using hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun' with
      ⟨V1, st1, hbqrun, hsufrun⟩ | ⟨hbqrun, hne⟩
  · rcases hbq V st ⟨hr, hx2, hf, hcptrV, hqepV, hbp, hinp⟩ V1 st1 .normal hbqrun with
        ⟨ho, hmid⟩ | ⟨hh, _⟩
    · have hsufrun' : ExecStmts (Bridge.Dialect (permissive (callsOf product)) g) funs V1 st1
          (pcsBqLines n nm invName ++ [GenAst.ylet (invName 0) (GenAst.yvar "bq")]
            ++ pcsDenInvLines points.length invName) V' st' o := by
        simpa [List.append_assoc] using hsufrun
      exact Or.inl (hsuffix V1 st1 hmid V' st' o hsufrun')
    · cases hh
  · rcases hbq V st ⟨hr, hx2, hf, hcptrV, hqepV, hbp, hinp⟩ V' st' o hbqrun with
        ⟨hh, _⟩ | ⟨ho, hrev⟩
    · exact absurd hh hne
    · exact Or.inr ⟨ho, hrev⟩



theorem pcsMemSameOutside_of_memory_eq {st st' : EvmState} {lo len : Nat}
    (h : st'.memory = st.memory) : MemSameOutside st st' lo len := by
  intro a _
  rw [h]

def PcsGPost (rv x2v fev : U256) (a : Nat → U256) (m setIdx cptr off scratch : Nat)
    (qep : U256) :
    VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) →
      EvmState → Outcome → Prop :=
  fun V st V' st' o =>
    (o = .normal ∧
      VEnv.get V' "f_eval" = some (pcsGenFEval rv x2v fev
        (wordFrom st.env.calldata (cptr + setIdx * Midfall.Generator.wordBytes))
        (fun j => loadWord st.memory
          (qep.toNat + (off + j) * Midfall.Generator.wordBytes)) a m) ∧
      MemSameOutside st st' scratch 192 ∧ st'.env = st.env) ∨
    (o = .halt ∧ Midfall.LoweringV2.Reverted st')

set_option maxHeartbeats 8000000 in
theorem pcsGenTail_contract {funs : FunEnv (Bridge.Dialect c g)}
    (setIdx : Nat) (m off n scratch : Nat) (a : Nat → U256) (invName : Nat → String)
    (rv x2v fev cptr qep : U256)
    (hm : 0 < m) (hn : n = 2 * m)
    (hcptr : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqep : qep.toNat + (off + m) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hinvEval : ∀ i, invName i ≠ "eval")
    (hinvX2 : ∀ i, invName i ≠ "x2")
    (hinvF : ∀ i, invName i ≠ "f_eval")
    (hinvQ : ∀ i, invName i ≠ "Q_EVAL_CPTR")
    (hinvQSet : ∀ i, invName i ≠ "Q_EVAL_SET_MPTR")
    (htermEval : ∀ j, j < m → ("term_" ++ toString j) ≠ "eval")
    (htermR : ∀ j, j < m → ("term_" ++ toString j) ≠ "r")
    (htermQ : ∀ j, j < m → ("term_" ++ toString j) ≠ "Q_EVAL_SET_MPTR")
    (htermF : ∀ j, j < m → ("term_" ++ toString j) ≠ "f_eval")
    (htermX2 : ∀ j, j < m → ("term_" ++ toString j) ≠ "x2")
    (htermDx : ∀ j, j < m → ∀ k, k < m → ("term_" ++ toString j) ≠ invName k)
    (htermLb : ∀ j, j < m → ∀ k, k < m →
      ("term_" ++ toString j) ≠ invName (m + k))
    (htermDist : ∀ i, i < m → ∀ j, j < m → i ≠ j →
      ("term_" ++ toString i) ≠ ("term_" ++ toString j))
    (hdxEval : ∀ k, k < m → invName k ≠ "eval")
    (hlbEval : ∀ k, k < m → invName (m + k) ≠ "eval")
    (hdxTerm : ∀ k, k < m → ∀ j, j < m → invName k ≠ ("term_" ++ toString j))
    (hlbTerm : ∀ k, k < m → ∀ j, j < m → invName (m + k) ≠ ("term_" ++ toString j))
    (hrEval : "r" ≠ "eval")
    (hrTerm : ∀ j, j < m → "r" ≠ ("term_" ++ toString j))
    (hqEval : "Q_EVAL_SET_MPTR" ≠ "eval")
    (hqTerm : ∀ j, j < m → "Q_EVAL_SET_MPTR" ≠ ("term_" ++ toString j)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      ([pcsEvalStmt setIdx] ++ pcsTermLines m off (fun j => invName j)
        (fun j => invName (m + j)) ++ [pcsFEvalStmt])
      (PcsGP4 m n rv x2v fev cptr qep a invName)
      (fun V st V' st' o =>
        (o = .normal ∧
          VEnv.get V' "f_eval" = some (pcsGenFEval rv x2v fev
            (wordFrom st.env.calldata (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
            (fun j => loadWord st.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes)) a m) ∧
          MemSameOutside st st' scratch 192 ∧ st'.env = st.env) ∨
        (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  intro V st hpre V' st' o hrun
  unfold PcsGP4 at hpre
  obtain ⟨hr, hx2, hf, hcptrV, hqepV, hinvV, hdenV⟩ := hpre
  let cval : U256 := wordFrom st.env.calldata
    (cptr.toNat + setIdx * Midfall.Generator.wordBytes)
  let ev : Nat → U256 := fun j => loadWord st.memory
    (qep.toNat + (off + j) * Midfall.Generator.wordBytes)
  let den : U256 := pcsDenInvVal rv (fun j => SIInv (a j)) m
  have hrun' : ExecStmts (D := Bridge.Dialect c g) funs V st
      ([pcsEvalStmt setIdx] ++ (pcsTermLines m off (fun j => invName j)
        (fun j => invName (m + j)) ++ [pcsFEvalStmt])) V' st' o := by
    simpa [List.append_assoc] using hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun' with
      ⟨V1, st1, hevrun, hrest⟩ | ⟨hevrun, hne⟩
  · -- eval line
    obtain ⟨ho1, hV1, hget1, hpres1, hst1⟩ :=
      stmtsContractAll_singleton (pcsEval_contract (c := c) (g := g) (funs := funs)
        setIdx den cptr rv hcptr)
        V st ⟨hcptrV, by simpa [den] using hdenV, hr⟩ V1 st1 .normal hevrun
    rw [hV1] at hrest hget1 hpres1
    rw [hst1] at hrest
    -- term lines
    have hpreT : VEnv.get (("eval", wMulmodAt cval den rv) :: V) "r" = some rv ∧
        VEnv.get (("eval", wMulmodAt cval den rv) :: V) "eval" =
          some (wMulmodAt cval den rv) ∧
        VEnv.get (("eval", wMulmodAt cval den rv) :: V) "Q_EVAL_SET_MPTR" = some qep ∧
        (∀ j, j < m → VEnv.get (("eval", wMulmodAt cval den rv) :: V) (invName j) =
          some (SIInv (a j))) ∧
        (∀ j, j < m → VEnv.get (("eval", wMulmodAt cval den rv) :: V) (invName (m + j)) =
          some (SIInv (a (m + j)))) ∧
        (∀ j, j < m → loadWord st.memory
          (qep.toNat + (off + j) * Midfall.Generator.wordBytes) = ev j) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpres1 "r" hrEval]
        exact hr
      · exact hget1
      · rw [hpres1 "Q_EVAL_SET_MPTR" hqEval]
        exact hqepV
      · intro j hj
        rw [hpres1 (invName j) (hinvEval j)]
        exact hinvV j (by omega)
      · intro j hj
        rw [hpres1 (invName (m + j)) (hinvEval (m + j))]
        exact hinvV (m + j) (by omega)
      · intro j hj; rfl
    let eval0 : U256 := wMulmodAt cval den rv
    have hrunT' : ExecStmts (D := Bridge.Dialect c g) funs
        (("eval", eval0) :: V) st (pcsTermLines m off (fun j => invName j)
          (fun j => invName (m + j)) ++ [pcsFEvalStmt]) V' st' o := by
      simpa [eval0] using hrest
    rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrunT' with
        ⟨V2, st2, htermrun, hferun⟩ | ⟨htermrun, hne2⟩
    · obtain ⟨ho2, hevalF, hterms, hpres2, hmem2, henv2, _hhalt2⟩ :=
        pcsTermLines_contract (c := c) (g := g) (funs := funs)
        m off (fun j => invName j) (fun j => invName (m + j))
        ev (fun j => SIInv (a j)) (fun j => SIInv (a (m + j))) rv eval0 qep
        (fun j hj => by
          have : (off + j) * Midfall.Generator.wordBytes ≤
              (off + m) * Midfall.Generator.wordBytes := by
            apply Nat.mul_le_mul_right; omega
          omega)
        htermEval htermR htermQ
        (fun j hj k hk => htermDx j hj k hk)
        (fun j hj k hk => htermLb j hj k hk)
        htermDist
        (fun k hk => hdxEval k hk)
        (fun k hk => hlbEval k hk)
        (fun k hk j hj => hdxTerm k hk j hj)
        (fun k hk j hj => hlbTerm k hk j hj)
        hrEval hrTerm hqEval hqTerm
        (("eval", eval0) :: V) st hpreT V2 st2 .normal htermrun
      -- f_eval line
      have hpreF : VEnv.get V2 "f_eval" = some fev ∧ VEnv.get V2 "x2" = some x2v ∧
          VEnv.get V2 "eval" = some (pcsEvalAcc rv ev (fun j => SIInv (a j))
            (fun j => SIInv (a (m + j))) m eval0) ∧ VEnv.get V2 "r" = some rv := by
        refine ⟨?_, ?_, hevalF, ?_⟩
        · rw [hpres2 "f_eval" (by pcs_ne1) (fun j hj => (htermF j hj).symm)]
          rw [hpres1 "f_eval" (by pcs_ne1)]
          exact hf
        · rw [hpres2 "x2" (by pcs_ne1) (fun j hj => (htermX2 j hj).symm)]
          rw [hpres1 "x2" (by pcs_ne1)]
          exact hx2
        · rw [hpres2 "r" (by pcs_ne1) (fun j hj => (htermR j hj).symm)]
          rw [hpres1 "r" hrEval]
          exact hr
      obtain ⟨ho3, hV3, hst3⟩ :=
        stmtsContractAll_singleton (pcsFEval_contract (c := c) (g := g) (funs := funs)
          fev x2v (pcsEvalAcc rv ev (fun j => SIInv (a j))
            (fun j => SIInv (a (m + j))) m eval0) rv)
          V2 st2 hpreF V' st' o hferun
      refine Or.inl ⟨ho3, ?_, ?_, ?_⟩
      · rw [hV3]
        rw [venv_get_set_same (D := Bridge.Dialect c g) hpreF.1]
        simp only [pcsGenFEval, eval0, den, cval, ev]
      · apply pcsMemSameOutside_of_memory_eq
        rw [hst3, hmem2]
      · rw [hst3, henv2]
    · exact absurd (pcsTermLines_contract (c := c) (g := g) (funs := funs)
        m off (fun j => invName j) (fun j => invName (m + j))
        ev (fun j => SIInv (a j)) (fun j => SIInv (a (m + j))) rv eval0 qep
        (fun j hj => by
          have : (off + j) * Midfall.Generator.wordBytes ≤
              (off + m) * Midfall.Generator.wordBytes := by
            apply Nat.mul_le_mul_right; omega
          omega)
        htermEval htermR htermQ
        (fun j hj k hk => htermDx j hj k hk)
        (fun j hj k hk => htermLb j hj k hk)
        htermDist
        (fun k hk => hdxEval k hk)
        (fun k hk => hlbEval k hk)
        (fun k hk j hj => hdxTerm k hk j hj)
        (fun k hk j hj => hlbTerm k hk j hj)
        hrEval hrTerm hqEval hqTerm
        (("eval", eval0) :: V) st hpreT V' st' o htermrun).1 hne2
  · exact absurd (stmtsContractAll_singleton (pcsEval_contract (c := c) (g := g)
      (funs := funs) setIdx den cptr rv hcptr)
      V st ⟨hcptrV, by simpa [den] using hdenV, hr⟩ V' st' o hevrun).1 hne


theorem pcsEvalAcc_congr (rv : U256) (ev1 ev2 dxinv lbinv : Nat → U256) (m : Nat)
    (h : ∀ j, j < m → ev1 j = ev2 j) :
    ∀ k, k ≤ m → ∀ acc,
      pcsEvalAcc rv ev1 dxinv lbinv k acc = pcsEvalAcc rv ev2 dxinv lbinv k acc
  | 0, _, acc => rfl
  | k + 1, hk, acc => by
      rw [pcsEvalAcc, pcsEvalAcc,
        pcsEvalAcc_congr rv ev1 ev2 dxinv lbinv m h k (by omega) acc,
        h k (by omega)]

set_option maxHeartbeats 16000000 in

set_option maxHeartbeats 2000000 in
theorem pcs_find?_append_of_forall_false {α : Type} {xs ys : List α} {p : α → Bool}
    (h : ∀ x ∈ xs, p x = false) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, List.find?_cons, h a (by simp), ite_false]
      exact ih (fun x hx => h x (by simp [hx]))

/-- `restore` keeps an outer binding when the dropped block-local prefix does not bind it. -/
theorem pcs_venv_get_restore_of_names {V V' : VEnv (Bridge.Dialect c g)} {extra : List Ident}
    {x : Ident} {v : U256}
    (hnames : V'.map Prod.fst = extra ++ V.map Prod.fst)
    (hx : x ∉ extra)
    (hget : VEnv.get V' x = some v) :
    VEnv.get (restore V V') x = some v := by
  unfold VEnv.get at hget ⊢
  have hlen : V'.length - V.length = extra.length := by
    have h := congrArg List.length hnames
    simp only [List.length_map, List.length_append] at h
    omega
  rw [show restore V V' = V'.drop (V'.length - V.length) from rfl, hlen]
  have htake : (V'.take extra.length).map Prod.fst = extra := by
    rw [List.map_take, hnames, List.take_left]
  have hpre : ∀ p ∈ V'.take extra.length,
      (fun p : Ident × U256 => decide (p.1 = x)) p = false := by
    intro p hp
    have hp' : p.1 ∈ (V'.take extra.length).map Prod.fst := List.mem_map_of_mem hp
    rw [htake] at hp'
    have hne : p.1 ≠ x := fun hxx => hx (hxx ▸ hp')
    simp [hne]
  have hfind : V'.find? (fun p : Ident × U256 => decide (p.1 = x)) =
      (V'.drop extra.length).find? (fun p => decide (p.1 = x)) := by
    conv_lhs => rw [← List.take_append_drop extra.length V']
    exact pcs_find?_append_of_forall_false hpre
  rw [hfind] at hget
  exact hget

def pcsLetNames (ss : Block EVM.Op) : List String := ss.filterMap pcsStmtLetName?

macro "pcs_ne1" : tactic => `(tactic|
  (intro h
   have hc := congrArg (fun s : String => s.toList.take 1) h
   simp [pcsDxName, pcsLbasisName, pcsBpName] at hc))

theorem pcsLetNames_append (a b : Block EVM.Op) :
    pcsLetNames (a ++ b) = pcsLetNames a ++ pcsLetNames b := by
  simp [pcsLetNames, List.filterMap_append]

theorem pcsLetNames_ylet (x : String) (e : Expr EVM.Op) :
    pcsLetNames [GenAst.ylet x e] = [x] := by
  simp [pcsLetNames, pcsStmtLetName?, GenAst.ylet]

theorem pcsLetNames_yset (x : String) (e : Expr EVM.Op) :
    pcsLetNames [GenAst.yset x e] = [] := by
  simp [pcsLetNames, pcsStmtLetName?, GenAst.yset]

theorem pcsLetNames_dx (xs : List (Nat × String)) :
    pcsLetNames (xs.map (fun q => pcsDxStmt q.1 q.2)) =
      xs.map (fun q => pcsDxName q.1) := by
  induction xs with
  | nil => rfl
  | cons q rest ih =>
      unfold pcsLetNames
      rw [List.map_cons, List.filterMap_cons]
      simp only [pcsStmtLetName?, pcsDxStmt, GenAst.ylet]
      rw [List.map_cons]
      change pcsDxName q.1 :: pcsLetNames
          (List.map (fun q => pcsDxStmt q.1 q.2) rest) =
        pcsDxName q.1 :: List.map (fun q => pcsDxName q.1) rest
      rw [ih]

theorem pcsLetNames_lbasisGroup (j : Nat) (pt : String) (ks : List (Nat × String)) :
    pcsLetNames (pcsLbasisGroupAst j pt ks) = [pcsLbasisName j] := by
  simp [pcsLetNames, pcsLbasisGroupAst, pcsLbasisInit, pcsLbasisStmt, pcsStmtLetName?,
    GenAst.ylet, GenAst.yset]

theorem pcsLetNames_lbasis (xs : List (Nat × String)) (ks : Nat → List (Nat × String)) :
    pcsLetNames ((xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten) =
      xs.map (fun q => pcsLbasisName q.1) := by
  induction xs with
  | nil => rfl
  | cons q rest ih =>
      rw [List.map_cons, List.flatten_cons, pcsLetNames_append,
        pcsLetNames_lbasisGroup]
      rw [List.map_cons, ih]
      rfl

theorem pcsLetNames_bpTail_map (l : List Nat) (nm : Nat → String) :
    pcsLetNames (l.map (fun i => pcsBpTail i (nm i))) = l.map pcsBpName := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      unfold pcsLetNames
      rw [List.map_cons, List.filterMap_cons]
      simp only [pcsStmtLetName?, pcsBpTail, GenAst.ylet]
      rw [List.map_cons]
      change pcsBpName i :: pcsLetNames (List.map (fun i => pcsBpTail i (nm i)) rest) =
        pcsBpName i :: List.map pcsBpName rest
      rw [ih]

theorem pcsLetNames_bp (n : Nat) (nm : Nat → String) :
    pcsLetNames (pcsBpLines n nm) =
      pcsBpName 0 :: ((List.range n).drop 1).map pcsBpName := by
  simp only [pcsBpLines, pcsBpHead, pcsBpTail, pcsLetNames, List.filterMap_cons,
    pcsStmtLetName?, GenAst.ylet]
  change pcsBpName 0 :: pcsLetNames
    (List.map (fun i => pcsBpTail i (nm i)) ((List.range n).drop 1)) =
    pcsBpName 0 :: List.map pcsBpName ((List.range n).drop 1)
  rw [pcsLetNames_bpTail_map]

theorem pcsLetNames_bqStep_map (l : List Nat) (nm : Nat → String) (invName : Nat → String) :
    pcsLetNames (l.flatMap (fun i => pcsBqStep i (pcsBpName (i - 1)) (nm i) invName)) =
      l.map (fun i => invName i) := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      rw [List.flatMap_cons, pcsLetNames_append]
      simp only [pcsBqStep, pcsBqStep, pcsLetNames, List.filterMap_cons, pcsStmtLetName?,
        GenAst.ylet, GenAst.yset, List.filterMap_nil, List.append_nil]
      change [invName i] ++ pcsLetNames
        (List.flatMap (fun i => pcsBqStep i (pcsBpName (i - 1)) (nm i) invName) rest) =
        invName i :: List.map (fun i => invName i) rest
      rw [ih]
      rfl

theorem pcsLetNames_bq (n : Nat) (nm : Nat → String) (invName : Nat → String) :
    pcsLetNames (pcsBqLines n nm invName) =
      ((List.range n).drop 1).reverse.map invName := by
  change pcsLetNames (((List.range n).drop 1).reverse.flatMap
    (fun i => pcsBqStep i (pcsBpName (i - 1)) (nm i) invName)) =
    ((List.range n).drop 1).reverse.map invName
  rw [pcsLetNames_bqStep_map]

theorem pcsLetNames_den (m : Nat) (invName : Nat → String) :
    pcsLetNames (pcsDenInvLines m invName) = ["den_inv"] := by
  simp [pcsLetNames, pcsDenInvLines, pcsDenInvSetStmt, pcsStmtLetName?, GenAst.ylet,
    GenAst.yset]

theorem pcsLetNames_eval (setIdx : Nat) :
    pcsLetNames [pcsEvalStmt setIdx] = ["eval"] := by
  simp [pcsLetNames, pcsEvalStmt, pcsStmtLetName?, GenAst.ylet]

theorem pcsLetNames_termStmt_map (l : List Nat) (off : Nat)
    (invName lbN : Nat → String) :
    pcsLetNames (l.flatMap (fun j => pcsTermStmt j (off + j) (invName j) (lbN j))) =
      l.map (fun j => "term_" ++ toString j) := by
  induction l with
  | nil => rfl
  | cons j rest ih =>
      rw [List.flatMap_cons, pcsLetNames_append]
      simp only [pcsTermStmt, pcsLetNames, List.filterMap_cons, pcsStmtLetName?,
        GenAst.ylet, GenAst.yset, List.filterMap_nil, List.append_nil]
      change ["term_" ++ toString j] ++ pcsLetNames
        (List.flatMap (fun j => pcsTermStmt j (off + j) (invName j) (lbN j)) rest) =
        ("term_" ++ toString j) :: List.map (fun j => "term_" ++ toString j) rest
      rw [ih]
      rfl

theorem pcsLetNames_term (m off : Nat) (invName : Nat → String) :
    pcsLetNames (pcsTermLines m off invName (fun j => invName (m + j))) =
      (List.range m).map (fun j => "term_" ++ toString j) := by
  change pcsLetNames ((List.range m).flatMap
    (fun j => pcsTermStmt j (off + j) (invName j) (invName (m + j)))) =
    (List.range m).map (fun j => "term_" ++ toString j)
  rw [pcsLetNames_termStmt_map (lbN := fun j => invName (m + j))]

theorem pcsLetNames_fe : pcsLetNames [pcsFEvalStmt] = [] := by
  simp [pcsLetNames, pcsFEvalStmt, pcsStmtLetName?, GenAst.yset]


theorem pcsLetNames_bqStmt (prev : String) :
    pcsLetNames [pcsBqStmt prev] = ["bq"] := by
  simp [pcsLetNames, pcsBqStmt, pcsStmtLetName?, GenAst.ylet]

namespace PcsNames

theorem notFEval_append {a b : List String}
    (ha : ∀ x ∈ a, x ≠ "f_eval") (hb : ∀ x ∈ b, x ≠ "f_eval") :
    ∀ x ∈ a ++ b, x ≠ "f_eval" := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with h | h
  · exact ha x h
  · exact hb x h

theorem dx (xs : List (Nat × String)) :
    ∀ x ∈ pcsLetNames (xs.map (fun q => pcsDxStmt q.1 q.2)), x ≠ "f_eval" := by
  rw [pcsLetNames_dx]
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨q, _, rfl⟩
  pcs_ne1

theorem lb (xs : List (Nat × String)) (ks : Nat → List (Nat × String)) :
    ∀ x ∈ pcsLetNames ((xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten),
      x ≠ "f_eval" := by
  rw [pcsLetNames_lbasis]
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨q, _, rfl⟩
  pcs_ne1

theorem bp (n : Nat) (nm : Nat → String) :
    ∀ x ∈ pcsLetNames (pcsBpLines n nm), x ≠ "f_eval" := by
  rw [pcsLetNames_bp]
  intro x hx
  simp only [List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨i, _, rfl⟩
  · pcs_ne1
  · pcs_ne1

theorem bqCall (prev : String) :
    ∀ x ∈ pcsLetNames [pcsBqStmt prev], x ≠ "f_eval" := by
  rw [pcsLetNames_bqStmt]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  pcs_ne1

theorem bq (n m : Nat) (nm : Nat → String) :
    ∀ x ∈ pcsLetNames (pcsBqLines n nm (pcsInvName m)), x ≠ "f_eval" := by
  rw [pcsLetNames_bq]
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨i, _, rfl⟩
  unfold pcsInvName
  split <;> pcs_ne1

theorem inv0 (m : Nat) :
    ∀ x ∈ pcsLetNames [GenAst.ylet (pcsInvName m 0) (GenAst.yvar "bq")], x ≠ "f_eval" := by
  rw [pcsLetNames_ylet]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  unfold pcsInvName
  split <;> pcs_ne1

theorem den (m : Nat) (invName : Nat → String) :
    ∀ x ∈ pcsLetNames (pcsDenInvLines m invName), x ≠ "f_eval" := by
  rw [pcsLetNames_den]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  pcs_ne1

theorem eval (setIdx : Nat) :
    ∀ x ∈ pcsLetNames [pcsEvalStmt setIdx], x ≠ "f_eval" := by
  rw [pcsLetNames_eval]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  pcs_ne1

theorem term (m off : Nat) :
    ∀ x ∈ pcsLetNames (pcsTermLines m off (pcsInvName m) (fun j => pcsInvName m (m + j))),
      x ≠ "f_eval" := by
  rw [pcsLetNames_term]
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨j, _, rfl⟩
  pcs_ne1

theorem fe : ∀ x ∈ pcsLetNames [pcsFEvalStmt], x ≠ "f_eval" := by
  rw [pcsLetNames_fe]
  intro x hx
  simp at hx

end PcsNames

set_option maxHeartbeats 4000000 in
theorem pcsGenBody_fe_notmem (setIdx : Nat) (points : List Int) (distinct : List Int)
    (off : Nat) :
    "f_eval" ∉ pcsLetNames (pcsGenBody setIdx points distinct off) := by
  have hall : ∀ x ∈ pcsLetNames (pcsGenBody setIdx points distinct off), x ≠ "f_eval" := by
    unfold pcsGenBody
    dsimp only
    simp only [pcsLetNames_append, List.append_nil]
    repeat' apply PcsNames.notFEval_append
    all_goals trace_state
    all_goals
      first
      | apply PcsNames.dx
      | apply PcsNames.lb
      | apply PcsNames.bp
      | apply PcsNames.bqCall
      | apply PcsNames.bq
      | apply PcsNames.inv0
      | apply PcsNames.den
      | apply PcsNames.eval
      | apply PcsNames.term
      | apply PcsNames.fe
  intro h
  exact hall "f_eval" h rfl



theorem pcs_mem_addedNames {x : String} {ss : Block EVM.Op} :
    x ∈ pcsAddedNames ss ↔ x ∈ pcsLetNames ss := by
  simp [pcsAddedNames, pcsLetNames]

theorem pcsGenBody_fe_notmem_added (setIdx : Nat) (points : List Int) (distinct : List Int)
    (off : Nat) :
    "f_eval" ∉ pcsAddedNames (pcsGenBody setIdx points distinct off) := by
  intro h
  exact pcsGenBody_fe_notmem setIdx points distinct off ((pcs_mem_addedNames).mp h)

def PcsLetSet (s : Stmt EVM.Op) : Prop :=
  ∃ x e, s = GenAst.ylet x e ∨ s = GenAst.yset x e

theorem pcsLetSet_append {a b : Block EVM.Op}
    (ha : ∀ s ∈ a, PcsLetSet s) (hb : ∀ s ∈ b, PcsLetSet s) :
    ∀ s ∈ a ++ b, PcsLetSet s := by
  intro s hs; rw [List.mem_append] at hs; rcases hs with h|h; exact ha s h; exact hb s h

theorem pcsLetSet_lbasisGroup (j : Nat) (pt : String) (ks : List (Nat × String)) :
    ∀ s ∈ pcsLbasisGroupAst j pt ks, PcsLetSet s := by
  intro s hs
  unfold pcsLbasisGroupAst pcsLbasisInit pcsLbasisStmt at hs
  simp only [List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | ⟨k, _, rfl⟩
  · exact ⟨_, _, Or.inl rfl⟩
  · exact ⟨_, _, Or.inr rfl⟩

theorem pcsLetSet_bqStep (i : Nat) (prev inp : String) (invName : Nat → String) :
    ∀ s ∈ pcsBqStep i prev inp invName, PcsLetSet s := by
  intro s hs
  unfold pcsBqStep at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨_, _, Or.inl rfl⟩
  · exact ⟨_, _, Or.inr rfl⟩

theorem pcsLetSet_termStmt (j evOff : Nat) (dxN lbN : String) :
    ∀ s ∈ pcsTermStmt j evOff dxN lbN, PcsLetSet s := by
  intro s hs
  unfold pcsTermStmt at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨_, _, Or.inl rfl⟩
  · exact ⟨_, _, Or.inr rfl⟩

theorem pcsLetSet_dx (xs : List (Nat × String)) :
    ∀ s ∈ xs.map (fun q => pcsDxStmt q.1 q.2), PcsLetSet s := by
  intro s hs
  simp only [List.mem_map] at hs
  rcases hs with ⟨q, _, rfl⟩
  exact ⟨_, _, Or.inl rfl⟩

theorem pcsLetSet_lb (xs : List (Nat × String)) (ks : Nat → List (Nat × String)) :
    ∀ s ∈ (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten, PcsLetSet s := by
  intro s hs
  simp only [List.mem_flatten] at hs
  rcases hs with ⟨l, hl, hsl⟩
  simp only [List.mem_map] at hl
  rcases hl with ⟨q, _, rfl⟩
  exact pcsLetSet_lbasisGroup q.1 q.2 (ks q.1) s hsl

theorem pcsLetSet_bp (n : Nat) (nm : Nat → String) :
    ∀ s ∈ pcsBpLines n nm, PcsLetSet s := by
  intro s hs
  unfold pcsBpLines pcsBpHead pcsBpTail at hs
  simp only [List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | ⟨i, _, rfl⟩
  · exact ⟨_, _, Or.inl rfl⟩
  · exact ⟨_, _, Or.inl rfl⟩

theorem pcsLetSet_bq (n : Nat) (nm : Nat → String) (invName : Nat → String) :
    ∀ s ∈ pcsBqLines n nm invName, PcsLetSet s := by
  intro s hs
  unfold pcsBqLines at hs
  simp only [List.mem_flatMap] at hs
  rcases hs with ⟨i, _, hi⟩
  exact pcsLetSet_bqStep i (pcsBpName (i - 1)) (nm i) invName s hi

theorem pcsLetSet_bqCall (prev : String) :
    ∀ s ∈ [pcsBqStmt prev], PcsLetSet s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [hs]
  exact ⟨_, _, Or.inl rfl⟩

theorem pcsLetSet_inv0 (m : Nat) :
    ∀ s ∈ [GenAst.ylet (pcsInvName m 0) (GenAst.yvar "bq")], PcsLetSet s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [hs]
  exact ⟨_, _, Or.inl rfl⟩

theorem pcsLetSet_den (m : Nat) (invName : Nat → String) :
    ∀ s ∈ pcsDenInvLines m invName, PcsLetSet s := by
  intro s hs
  unfold pcsDenInvLines pcsDenInvSetStmt at hs
  rw [List.mem_append] at hs
  rcases hs with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst s
    exact ⟨_, _, Or.inl rfl⟩
  · simp only [List.mem_map] at h
    rcases h with ⟨j, _, h⟩
    subst s
    exact ⟨_, _, Or.inr rfl⟩

theorem pcsLetSet_eval (setIdx : Nat) :
    ∀ s ∈ [pcsEvalStmt setIdx], PcsLetSet s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [hs]
  exact ⟨_, _, Or.inl rfl⟩

theorem pcsLetSet_term (m off : Nat) (dxN lbN : Nat → String) :
    ∀ s ∈ pcsTermLines m off dxN lbN, PcsLetSet s := by
  intro s hs
  unfold pcsTermLines at hs
  simp only [List.mem_flatMap] at hs
  rcases hs with ⟨j, _, hj⟩
  exact pcsLetSet_termStmt j (off + j) (dxN j) (lbN j) s hj

theorem pcsLetSet_fe :
    ∀ s ∈ [pcsFEvalStmt], PcsLetSet s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [hs]
  exact ⟨_, _, Or.inr rfl⟩


set_option maxHeartbeats 4000000 in
theorem pcsGenBody_allLetSet (setIdx : Nat) (points : List Int) (distinct : List Int)
    (off : Nat) :
    ∀ s ∈ pcsGenBody setIdx points distinct off, PcsLetSet s := by
  unfold pcsGenBody
  dsimp only
  repeat' apply pcsLetSet_append
  all_goals
    first
    | apply pcsLetSet_dx
    | apply pcsLetSet_lb
    | apply pcsLetSet_bp
    | apply pcsLetSet_bq
    | apply pcsLetSet_bqCall
    | apply pcsLetSet_inv0
    | apply pcsLetSet_den
    | apply pcsLetSet_eval
    | apply pcsLetSet_term
    | apply pcsLetSet_fe
    | (intro s hs
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
       subst s
       exact ⟨_, _, Or.inl rfl⟩)
    | (intro s hs
       simp only [List.mem_map] at hs
       rcases hs with ⟨a, _, h⟩
       subst s
       exact ⟨_, _, Or.inr rfl⟩)
    | (intro s hs; simp at hs)

set_option maxHeartbeats 16000000 in
theorem pcsGenBody_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off scratch hbls gasN selN selP : Nat)
    (p a : Nat → U256) (x3v rv x2v fev cptr qep : U256)
    (hm : 1 < points.length)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hnames : PcsGenNames points.length (pcsPointRefs points distinctRotations)
      (pcsKs points distinctRotations))
    (hainlt : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat < blsR)
    (hain0 : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat ≠ 0)
    (hvalDx : ∀ i, i < points.length → a i = wAddmodAt x3v (rv - p i) rv)
    (hvalLb : ∀ j, j < points.length →
      a (points.length + j) = pcsLbasisVal rv (p j) p (pcsKs points distinctRotations j))
    (hks_sub : ∀ g ∈ pcsPointRefs points distinctRotations,
      ∀ k ∈ pcsKs points distinctRotations g.1, k ∈ pcsPointRefs points distinctRotations)
    (hinv0Dist : ∀ j, 1 ≤ j → j < (pcsBatchInputs points.length).length →
      pcsInvName points.length 0 ≠ pcsInvName points.length j)
    (hinvEvalAll : ∀ i, pcsInvName points.length i ≠ "eval")
    (hinvQSetAll : ∀ i, pcsInvName points.length i ≠ "Q_EVAL_SET_MPTR")
    (hinvR0 : pcsInvName points.length 0 ≠ "r")
    (htermF : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "f_eval")
    (htermX2 : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "x2")
    (hdenInvAll : ∀ i, i < (pcsBatchInputs points.length).length →
      "den_inv" ≠ pcsInvName points.length i)
    (hrv : rv = BitVec.ofNat 256 blsR)
    (hcptr : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqep : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hdisj : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (pcsGenBody setIdx points distinctRotations off)
      (PcsGPre (c := permissive (callsOf product)) (g := g)
        x3v rv x2v fev cptr qep p (pcsPointRefs points distinctRotations)
        (pcsBatchInputs points.length).length)
      (PcsGPost (c := permissive (callsOf product)) (g := g)
        rv x2v fev a points.length setIdx cptr.toNat off scratch qep) := by
  let xs := pcsPointRefs points distinctRotations
  let ks := pcsKs points distinctRotations
  let invName := pcsInvName points.length
  let n := (pcsBatchInputs points.length).length
  let nm := pcsBatchName points.length
  let pre0 := PcsGPre (c := permissive (callsOf product)) (g := g)
    x3v rv x2v fev cptr qep p xs n
  let dxL := xs.map (fun q => pcsDxStmt q.1 q.2)
  let lbL := (xs.map (fun q => pcsLbasisGroupAst q.1 q.2 (ks q.1))).flatten
  let bpL := pcsBpLines n nm
  let bqCall := [pcsBqStmt (pcsBpName (n - 1))]
  let bqL := pcsBqLines n nm invName
  let inv0 := [GenAst.ylet (invName 0) (GenAst.yvar "bq")]
  let denL := pcsDenInvLines points.length invName
  let evalL := [pcsEvalStmt setIdx]
  let termL := pcsTermLines points.length off (fun j => invName j) (fun j => invName (points.length + j))
  let feL := [pcsFEvalStmt]
  have hbodyEq : pcsGenBody setIdx points distinctRotations off =
      ((dxL ++ lbL) ++ bpL) ++ (bqCall ++ bqL ++ inv0 ++ denL) ++ (evalL ++ termL ++ feL) := by
    simp [pcsGenBody, dxL, lbL, bpL, bqCall, bqL, inv0, denL, evalL, termL, feL,
      xs, ks, invName, n, nm, List.append_assoc]
  intro V st hpre V' st' o hrun
  rw [hbodyEq, List.append_assoc] at hrun
  have hpfxC := pcsGenPrefix_contract (c := permissive (callsOf product)) (g := g)
    (funs := funs) points distinctRotations xs ks n nm p a x3v rv x2v fev cptr qep
    hm rfl rfl rfl rfl hnames hvalDx hvalLb hks_sub
  have hbatchFn := pcsGenBatch_contract (g := g) (product := product) (funs := funs)
    (decl := decl) (cenv := cenv) (cenv' := cenv')
    points distinctRotations xs ks n nm invName a rv x2v fev cptr qep
    scratch gasN selN selP hbls hm rfl rfl rfl rfl hlook hbody hparams hrets hnbls
    hscratch hscratch256 hfail hnames
    (fun i hi => hainlt i hi)
    (fun i hi => hain0 i hi)
    hinv0Dist hinvR0 hnames.invX2 hnames.invF hnames.invQ hrv
    (fun i => hinvQSetAll i) (fun i => hinvEvalAll i)
    (fun i hi => hdenInvAll i hi)
  rcases Step.stmts_append_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
      ⟨V1, st1, hpfx, hrest⟩ | ⟨hpfx, hne⟩
  · obtain ⟨ho1, hp3, hst1⟩ := hpfxC V st hpre V1 st1 .normal hpfx
    rcases Step.stmts_append_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest with
        ⟨V2, st2, hbatch, htail⟩ | ⟨hbatch, hne2⟩
    · -- batch
      have hbatchC := hbatchFn V1 st1 hp3 V2 st2 .normal
        (by simpa [bqCall, bqL, inv0, denL, List.append_assoc] using hbatch)
      rcases hbatchC with ⟨ho2, hp4, hfr2, henv2⟩ | ⟨ho2, hrev2⟩
      · -- tail
        have htailC := pcsGenTail_contract (c := permissive (callsOf product)) (g := g)
          (funs := funs) setIdx points.length off n scratch a invName rv x2v fev cptr qep
          (by omega) (by simp [n, pcsBatchInputs_length]) hcptr hqep
          (fun i => hinvEvalAll i) hnames.invX2 hnames.invF hnames.invQ
          (fun i => hinvQSetAll i)
          hnames.termEval hnames.termR hnames.termQ htermF htermX2
          (fun j hj k hk => hnames.termDx j hj k hk)
          (fun j hj k hk => hnames.termLb j hj k hk)
          hnames.termDist hnames.dxEval hnames.lbEval hnames.dxTerm hnames.lbTerm
          hnames.rEval hnames.rTerm hnames.qEval hnames.qTerm
          V2 st2 hp4 V' st' o (by simpa [evalL, termL, feL, List.append_assoc] using htail)
        rcases htailC with ⟨ho3, hfget, hfr3, henv3⟩ | ⟨ho3, hrev3⟩
        have hfr12 : MemSameOutside st st2 scratch 192 := by
          rw [← hst1]; exact hfr2
        have henv12 : st2.env = st.env := by rw [henv2, hst1]
        have hload (j : Nat) (hj : j < points.length) :
            loadWord st2.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes) =
            loadWord st.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes) := by
          have hwb : Midfall.Generator.wordBytes = 32 := rfl
          rw [hwb]
          have hdisj' := hdisj
          rw [hwb] at hdisj'
          apply loadWord_eq_of_memSameOutside hfr12
          have hstep : (off + j + 1) * 32 ≤ (off + points.length) * 32 :=
            Nat.mul_le_mul_right 32 (by omega)
          have hstep' : (off + j) * 32 + 32 = (off + j + 1) * 32 := by ring
          have hbase : (off + 0) * 32 ≤ (off + j) * 32 :=
            Nat.mul_le_mul_right 32 (by omega)
          rcases hdisj' with h1 | h2
          · left; omega
          · right; omega
        refine Or.inl ⟨ho3, ?_, ?_, ?_⟩
        · rw [hfget]
          congr 1
          unfold pcsGenFEval
          rw [henv12]
          congr 1
          exact pcsEvalAcc_congr rv
            (fun j => loadWord st2.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes))
            (fun j => loadWord st.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes))
            (fun j => SIInv (a j)) (fun j => SIInv (a (points.length + j)))
            points.length hload points.length le_rfl _
        · exact pcsMemSameOutside_trans hfr12 hfr3
        · rw [henv3, henv12]
        · exact Or.inr ⟨ho3, hrev3⟩
      · exfalso; cases ho2
    · -- batch halted
      have hbatchC := hbatchFn V1 st1 hp3 V' st' o
        (by simpa [bqCall, bqL, inv0, denL, List.append_assoc] using hbatch)
      rcases hbatchC with ⟨ho2, _⟩ | ⟨ho2, hrev2⟩
      · exact absurd ho2 hne2
      · exact Or.inr ⟨ho2, hrev2⟩
  · exact absurd (hpfxC V st hpre V' st' o hpfx).1 hne


def pcsSetBlockLocals (points distinct : List Int) : List String :=
  "f_eval" :: "bq" :: "eval" :: "den_inv" :: pcsInvName points.length 0 ::
    (pcsPointRefs points distinct).map (fun q => pcsDxName q.1) ++
    (pcsPointRefs points distinct).map (fun q => pcsLbasisName q.1) ++
    (List.range (pcsBatchInputs points.length).length).map pcsBpName ++
    (List.range (pcsBatchInputs points.length).length).map (pcsInvName points.length) ++
    (List.range points.length).map (fun j => "term_" ++ toString j)

theorem pcsGenBody_eq_chunks (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off : Nat) :
    pcsGenBody setIdx points distinctRotations off =
      (((pcsPointRefs points distinctRotations).map (fun q => pcsDxStmt q.1 q.2))
        ++ ((pcsPointRefs points distinctRotations).map (fun q =>
            pcsLbasisGroupAst q.1 q.2 (pcsKs points distinctRotations q.1))).flatten
        ++ pcsBpLines (pcsBatchInputs points.length).length (pcsBatchName points.length))
      ++ ([pcsBqStmt (pcsBpName ((pcsBatchInputs points.length).length - 1))]
        ++ pcsBqLines (pcsBatchInputs points.length).length (pcsBatchName points.length)
          (pcsInvName points.length)
        ++ [GenAst.ylet (pcsInvName points.length 0) (GenAst.yvar "bq")]
        ++ pcsDenInvLines points.length (pcsInvName points.length))
      ++ ([pcsEvalStmt setIdx]
        ++ pcsTermLines points.length off (fun j => pcsInvName points.length j)
          (fun j => pcsInvName points.length (points.length + j))
        ++ [pcsFEvalStmt]) := by
  simp [pcsGenBody, List.append_assoc]

theorem pcsGenBody_pcsStmtLocal_explicit (setIdx : Nat) (points distinct : List Int) (off : Nat)
    (hm : 0 < points.length) :
    ∀ s ∈ pcsGenBody setIdx points distinct off,
      pcsStmtLocal (pcsSetBlockLocals points distinct) s := by
  intro s hs
  rw [pcsGenBody_eq_chunks] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with hdx | hlb | hbp | hbqc | hbq | hinv0 | hden | hev | hterm | hfe
  · simp only [List.mem_map] at hdx
    rcases hdx with ⟨q, hq, rfl⟩
    simp only [pcsDxStmt, pcsStmtLocal, GenAst.ylet]
    have hmem : pcsDxName q.1 ∈
        (pcsPointRefs points distinct).map (fun q => pcsDxName q.1) :=
      List.mem_map_of_mem hq
    simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
    tauto
  · simp only [List.mem_flatten, List.mem_map] at hlb
    rcases hlb with ⟨l, ⟨q, hq, rfl⟩, hsl⟩
    simp only [pcsLbasisGroupAst, pcsLbasisInit, pcsLbasisStmt,
      List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | ⟨k, hk, rfl⟩
    · simp only [pcsStmtLocal, GenAst.ylet]
      have hmem : pcsLbasisName q.1 ∈
          (pcsPointRefs points distinct).map (fun q => pcsLbasisName q.1) :=
        List.mem_map_of_mem hq
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
    · simp only [pcsStmtLocal, GenAst.yset]
      have hmem : pcsLbasisName q.1 ∈
          (pcsPointRefs points distinct).map (fun q => pcsLbasisName q.1) :=
        List.mem_map_of_mem hq
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
  · simp only [pcsBpLines, pcsBpHead, pcsBpTail, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at hbp
    rcases hbp with rfl | ⟨i, hi, rfl⟩
    · simp only [pcsStmtLocal, GenAst.ylet]
      have hmem : pcsBpName 0 ∈
          (List.range (pcsBatchInputs points.length).length).map pcsBpName :=
        List.mem_map_of_mem (List.mem_range.mpr (by
          rw [pcsBatchInputs_length]; omega))
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
    · simp only [pcsStmtLocal, GenAst.ylet]
      have hmem : pcsBpName i ∈
          (List.range (pcsBatchInputs points.length).length).map pcsBpName :=
        List.mem_map_of_mem (List.mem_of_mem_drop hi)
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
  · subst hbqc
    simp only [pcsBqStmt, pcsStmtLocal, GenAst.ylet]
    have hmem : "bq" ∈ pcsSetBlockLocals points distinct := by
      simp only [pcsSetBlockLocals, List.mem_cons]; tauto
    simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
    tauto
  · simp only [pcsBqLines, List.mem_flatMap] at hbq
    rcases hbq with ⟨i, hi, hsl⟩
    simp only [pcsBqStep, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl
    · simp only [pcsStmtLocal, GenAst.ylet]
      have hmem : pcsInvName points.length i ∈
          (List.range (pcsBatchInputs points.length).length).map (pcsInvName points.length) :=
        List.mem_map_of_mem (List.mem_of_mem_drop (List.mem_reverse.mp hi))
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
    · simp only [pcsStmtLocal, GenAst.yset]
      have hmem : "bq" ∈ pcsSetBlockLocals points distinct := by
        simp only [pcsSetBlockLocals, List.mem_cons]; tauto
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
  · subst hinv0
    simp only [pcsStmtLocal, GenAst.ylet]
    have hmem : pcsInvName points.length 0 ∈ pcsSetBlockLocals points distinct := by
      simp only [pcsSetBlockLocals, List.mem_cons]; tauto
    simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
    tauto
  · simp only [pcsDenInvLines, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, false_or, or_false] at hden
    rcases hden with h | ⟨j, hj, h⟩
    · subst h
      simp only [pcsStmtLocal, GenAst.ylet]
      have hmem : "den_inv" ∈ pcsSetBlockLocals points distinct := by
        simp only [pcsSetBlockLocals, List.mem_cons]; tauto
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
    · subst h
      simp only [pcsDenInvSetStmt, pcsStmtLocal, GenAst.yset]
      have hmem : "den_inv" ∈ pcsSetBlockLocals points distinct := by
        simp only [pcsSetBlockLocals, List.mem_cons]; tauto
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
  · subst hev
    simp only [pcsEvalStmt, pcsStmtLocal, GenAst.ylet]
    have hmem : "eval" ∈ pcsSetBlockLocals points distinct := by
      simp only [pcsSetBlockLocals, List.mem_cons]; tauto
    simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
    tauto
  · simp only [pcsTermLines, List.mem_flatMap] at hterm
    rcases hterm with ⟨j, hj, hsl⟩
    simp only [pcsTermStmt, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl
    · simp only [pcsStmtLocal, GenAst.ylet]
      have hmem : ("term_" ++ toString j) ∈
          (List.range points.length).map (fun j => "term_" ++ toString j) :=
        List.mem_map_of_mem hj
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
    · simp only [pcsStmtLocal, GenAst.yset]
      have hmem : "eval" ∈ pcsSetBlockLocals points distinct := by
        simp only [pcsSetBlockLocals, List.mem_cons]; tauto
      simp only [pcsSetBlockLocals, List.mem_cons, List.mem_append]
      tauto
  · subst hfe
    simp only [pcsFEvalStmt, pcsStmtLocal, GenAst.yset, pcsSetBlockLocals]
    exact List.mem_cons_self

theorem pcsAddedNames_subset_locals (setIdx : Nat) (points distinct : List Int) (off : Nat)
    (hm : 0 < points.length) :
    ∀ y ∈ pcsAddedNames (pcsGenBody setIdx points distinct off),
      y ∈ pcsSetBlockLocals points distinct := by
  intro y hy
  simp only [pcsAddedNames, pcsLetNames, List.mem_reverse] at hy
  obtain ⟨s, hs, hsome⟩ := List.mem_filterMap.mp hy
  have hloc := pcsGenBody_pcsStmtLocal_explicit setIdx points distinct off hm s hs
  cases s with
  | letDecl vars e =>
      cases vars with
      | nil => simp [pcsStmtLetName?] at hsome
      | cons x vars =>
          cases vars with
          | nil =>
              simp only [pcsStmtLetName?, Option.some.injEq] at hsome
              simp only [pcsStmtLocal] at hloc
              exact hsome ▸ hloc
          | cons _ _ => simp [pcsStmtLetName?] at hsome
  | _ => simp [pcsStmtLetName?] at hsome

theorem pcs_venv_get_none_of_map_fst {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {V W : YulSemantics.VEnv D} {x : YulSemantics.Ident}
    (h : W.map Prod.fst = V.map Prod.fst)
    (hV : YulSemantics.VEnv.get V x = none) :
    YulSemantics.VEnv.get W x = none := by
  unfold YulSemantics.VEnv.get at hV ⊢
  rw [Option.map_eq_none_iff] at hV ⊢
  rw [List.find?_eq_none] at hV ⊢
  intro p hp
  have hp' : p.1 ∈ W.map Prod.fst := List.mem_map_of_mem hp
  rw [h] at hp'
  rcases List.mem_map.mp hp' with ⟨q, hq, hq1⟩
  intro hpx
  exact hV q hq (by simpa [hq1] using hpx)
theorem pcs_restore_map_fst {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {V W : YulSemantics.VEnv D} {extra : List YulSemantics.Ident}
    (h : W.map Prod.fst = extra ++ V.map Prod.fst) :
    (YulSemantics.restore V W).map Prod.fst = V.map Prod.fst := by
  unfold YulSemantics.restore
  rw [List.map_drop, h]
  have hlen : W.length - V.length = extra.length := by
    have hh := congrArg List.length h
    simp only [List.length_map, List.length_append] at hh
    omega
  rw [hlen, List.drop_left]
def pcsSetBlockLocalsAll (points distinct : List Int) : List String :=
  pcsSetBlockLocals points distinct ++ ["dx0", "dx0_inv"]

theorem pcsSetBlockLocals_subset_all (points distinct : List Int) {x : String}
    (h : x ∈ pcsSetBlockLocals points distinct) :
    x ∈ pcsSetBlockLocalsAll points distinct :=
  List.mem_append_left _ h

theorem pcsStmtLocal_mono {locals locals' : List String}
    (hsub : ∀ x ∈ locals, x ∈ locals') {s : Stmt EVM.Op}
    (h : pcsStmtLocal locals s) : pcsStmtLocal locals' s := by
  cases s with
  | letDecl vars e =>
      cases vars with
      | nil => simp [pcsStmtLocal] at h
      | cons x vars =>
          cases vars with
          | nil => simp [pcsStmtLocal] at h ⊢; exact hsub x h
          | cons _ _ => simp [pcsStmtLocal] at h
  | assign vars e =>
      cases vars with
      | nil => simp [pcsStmtLocal] at h
      | cons x vars =>
          cases vars with
          | nil => simp [pcsStmtLocal] at h ⊢; exact hsub x h
          | cons _ _ => simp [pcsStmtLocal] at h
  | _ => simp [pcsStmtLocal] at h

theorem pcs_exec_frame_of_locals {funs : FunEnv (Bridge.Dialect c g)} {body : Block EVM.Op}
    {locals : List String}
    (hns : ∀ s ∈ body, ∃ x e, s = GenAst.ylet x e ∨ s = GenAst.yset x e)
    (hloc : ∀ s ∈ body, pcsStmtLocal locals s)
    (hsub : ∀ y ∈ pcsAddedNames body, y ∈ locals)
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome}
    (hrun : ExecStmts (Bridge.Dialect c g) funs V st body V' st' o)
    (ho : o = .normal) :
    (∀ x, x ∉ locals → VEnv.get (restore V V') x = VEnv.get V x) ∧
    (∀ y, VEnv.get V y = none → VEnv.get (restore V V') y = none) := by
  have hnamesExec := pcsExec_names (funs := funs) (ss := body) hns hrun ho
  have hrestore : (restore V V').map Prod.fst = V.map Prod.fst :=
    pcs_restore_map_fst hnamesExec
  constructor
  · intro x hx
    have hxExtra : x ∉ pcsAddedNames body := fun h => hx (hsub x h)
    have hinner : VEnv.get V' x = VEnv.get V x :=
      pcsExec_get_of_local (funs := funs) (ss := body) (locals := locals)
        hloc hx hrun ho
    cases hv : VEnv.get V x with
    | none =>
        exact pcs_venv_get_none_of_map_fst (D := Bridge.Dialect c g) hrestore hv
    | some v =>
        have hget' : VEnv.get V' x = some v := by rw [hinner, hv]
        exact pcs_venv_get_restore_of_names hnamesExec hxExtra hget'
  · intro y hy
    exact pcs_venv_get_none_of_map_fst (D := Bridge.Dialect c g) hrestore hy


set_option maxHeartbeats 16000000 in
theorem pcsSetBlock_multi_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off scratch hbls gasN selN selP : Nat)
    (p a : Nat → U256) (x3v rv x2v fev cptr qep : U256)
    (hm : 1 < points.length)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hnames : PcsGenNames points.length (pcsPointRefs points distinctRotations)
      (pcsKs points distinctRotations))
    (hainlt : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat < blsR)
    (hain0 : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat ≠ 0)
    (hvalDx : ∀ i, i < points.length → a i = wAddmodAt x3v (rv - p i) rv)
    (hvalLb : ∀ j, j < points.length →
      a (points.length + j) = pcsLbasisVal rv (p j) p (pcsKs points distinctRotations j))
    (hks_sub : ∀ g ∈ pcsPointRefs points distinctRotations,
      ∀ k ∈ pcsKs points distinctRotations g.1, k ∈ pcsPointRefs points distinctRotations)
    (hinv0Dist : ∀ j, 1 ≤ j → j < (pcsBatchInputs points.length).length →
      pcsInvName points.length 0 ≠ pcsInvName points.length j)
    (hinvEvalAll : ∀ i, pcsInvName points.length i ≠ "eval")
    (hinvQSetAll : ∀ i, pcsInvName points.length i ≠ "Q_EVAL_SET_MPTR")
    (hinvR0 : pcsInvName points.length 0 ≠ "r")
    (htermF : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "f_eval")
    (htermX2 : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "x2")
    (hdenInvAll : ∀ i, i < (pcsBatchInputs points.length).length →
      "den_inv" ≠ pcsInvName points.length i)
    (hrv : rv = BitVec.ofNat 256 blsR)
    (hcptr : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqep : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hdisj : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.block (GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off))
      (PcsGPre (c := permissive (callsOf product)) (g := g)
        x3v rv x2v fev cptr qep p (pcsPointRefs points distinctRotations)
        (pcsBatchInputs points.length).length)
      (fun V st V' st' o =>
        PcsGPost (c := permissive (callsOf product)) (g := g)
          rv x2v fev a points.length setIdx cptr.toNat off scratch qep V st V' st' o) := by
  apply StmtsContractAll.block
  intro V st hpre V' st' o hrun
  have hbodyEq : GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off =
      pcsGenBody setIdx points distinctRotations off := by
    rw [pcsSetBlockAst_eq_gen setIdx points distinctRotations off hm,
      pcsSetBodyGen_eq setIdx points distinctRotations off hm]
  have hhoistGen : hoist (Bridge.Dialect (permissive (callsOf product)) g)
      (pcsGenBody setIdx points distinctRotations off) = [] := by
    unfold hoist
    rw [List.filterMap_eq_nil_iff]
    intro s hs
    rcases pcsGenBody_allLetSet setIdx points distinctRotations off s hs with ⟨x, e, h | h⟩
    · subst s; simp [GenAst.ylet]
    · subst s; simp [GenAst.yset]
  rw [hbodyEq, hhoistGen] at hrun
  have hlook' : lookupFun ([] :: funs) "scalar_inv" = some (decl, cenv) := by
    simpa [lookupFun] using hlook
  have hb := pcsGenBody_contract (g := g) (product := product)
    (funs := [] :: funs)
    (decl := decl) (cenv := cenv) (cenv' := cenv')
    setIdx points distinctRotations off scratch hbls gasN selN selP p a
    x3v rv x2v fev cptr qep hm hlook' hbody hparams hrets hnbls hscratch hscratch256
    hfail hnames hainlt hain0 hvalDx hvalLb hks_sub hinv0Dist hinvEvalAll
    hinvQSetAll hinvR0 htermF htermX2 hdenInvAll hrv hcptr hqep hdisj
    V st hpre V' st' o hrun
  rcases hb with ⟨ho, hfget, hfr, henv⟩ | hh
  · refine Or.inl ⟨ho, ?_, hfr, henv⟩
    have hnamesExec := pcsExec_names (funs := [] :: funs)
      (ss := pcsGenBody setIdx points distinctRotations off)
      (pcsGenBody_allLetSet setIdx points distinctRotations off) hrun ho
    exact pcs_venv_get_restore_of_names hnamesExec
      (pcsGenBody_fe_notmem_added setIdx points distinctRotations off) hfget
  · exact Or.inr hh


set_option maxHeartbeats 8000000 in
theorem pcsSetBlock_one_contract_gen {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (setIdx : Nat) (p0 : Int) (distinctRotations : List Int)
    (off scratch hbls gasN selN selP : Nat)
    (p a : Nat → U256) (x3v rv x2v fev cptr qep : U256)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hvalDx0 : a 0 = wAddmodAt x3v (rv - p 0) rv)
    (hvalLb0 : a 1 = 1)
    (hdx0pos : 0 < (m1Dx0 x3v (p 0) rv).toNat)
    (hdx0lt : (m1Dx0 x3v (p 0) rv).toNat < Midfall.Yul.blsR)
    (hrv : rv = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hcptr : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqep : qep.toNat + (off + 1) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hdisj : qep.toNat + (off + 1) * Midfall.Generator.wordBytes ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.block (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off))
      (fun V st =>
        PcsGPre (c := permissive (callsOf product)) (g := g)
          x3v rv x2v fev cptr qep p [(0, pcsRotPtRef distinctRotations p0)] 2 V st ∧
        (loadWord st.memory
          (qep.toNat + off * Midfall.Generator.wordBytes)).toNat < Midfall.Yul.blsR)
      (fun V st V' st' o =>
        PcsGPost (c := permissive (callsOf product)) (g := g)
          rv x2v fev a 1 setIdx cptr.toNat off scratch qep V st V' st' o) := by
  intro V st hpre V' st' o hrun
  subst rv
  obtain ⟨hpreG, hev⟩ := hpre
  obtain ⟨hx3, hrv', hx2, hfe, hcptrV, hqepV, hpts, _, _⟩ := hpreG
  have hmem : (0, pcsRotPtRef distinctRotations p0) ∈
      pcsPointRefs [p0] distinctRotations := by
    simp [pcsPointRefs, Midfall.Generator.enumIdx]
  have hptv : VEnv.get V (pcsRotPtRef distinctRotations p0) = some (p 0) := hpts _ hmem
  have hqep' : qep.toNat + off * Midfall.Generator.wordBytes +
      Midfall.Generator.wordBytes < 2 ^ 256 := by
    have h := hqep
    have hwb : Midfall.Generator.wordBytes = 32 := rfl
    rw [hwb] at h ⊢
    have h' : (off + 1) * 32 = off * 32 + 32 := by ring
    omega
  have hdisj' : qep.toNat + off * Midfall.Generator.wordBytes + 32 ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes := by
    rcases hdisj with h | h
    · left
      have hwb : Midfall.Generator.wordBytes = 32 := rfl
      rw [hwb] at h
      have h' : (off + 1) * 32 = off * 32 + 32 := by ring
      rw [h'] at h
      exact h
    · right
      have h' : Midfall.Generator.wordBytes = 32 := rfl
      rw [h'] at h ⊢
      exact h
  have hqepb : qep.toNat + off * Midfall.Generator.wordBytes + 32 < 2 ^ 256 := by
    have h := hqep'
    rwa [show Midfall.Generator.wordBytes = 32 from rfl] at h
  have hmain := pcsSetBlock1_contract (g := g) (product := product) (funs := funs)
    (decl := decl) (cenv := cenv) (cenv' := cenv')
    distinctRotations setIdx off scratch hbls gasN selN selP p0
    (pcsRotPtRef distinctRotations p0) x3v (p 0) (BitVec.ofNat 256 Midfall.Yul.blsR) cptr qep x2v fev
    rfl hlook hbody hparams hrets hnbls hscratch hscratch256 hfail
    hdx0pos hdx0lt hcptr hqepb hdisj'
    V st ⟨hx3, hrv', hx2, hfe, hcptrV, hqepV, hptv⟩ V' st' o hrun
  rcases hmain with ⟨ho, hV', hfr, henv⟩ | ⟨ho, hrev⟩
  · refine Or.inl ⟨ho, ?_, hfr, henv⟩
    rw [hV']
    have hget : VEnv.get (VEnv.set V "f_eval" (m1FEval fev x2v
        (m1Eval (wordFrom st.env.calldata
          (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
          (loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes))
          (m1Dx0 x3v (p 0) (BitVec.ofNat 256 Midfall.Yul.blsR))
          (BitVec.ofNat 256 Midfall.Yul.blsR))
        (BitVec.ofNat 256 Midfall.Yul.blsR))) "f_eval" =
        some (m1FEval fev x2v
        (m1Eval (wordFrom st.env.calldata
          (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
          (loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes))
          (m1Dx0 x3v (p 0) (BitVec.ofNat 256 Midfall.Yul.blsR))
          (BitVec.ofNat 256 Midfall.Yul.blsR))
        (BitVec.ofNat 256 Midfall.Yul.blsR)) :=
      venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g)
        (V := V) (x := "f_eval") (v := fev)
        (w := m1FEval fev x2v
          (m1Eval (wordFrom st.env.calldata
            (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
            (loadWord st.memory (qep.toNat + off * Midfall.Generator.wordBytes))
            (m1Dx0 x3v (p 0) (BitVec.ofNat 256 Midfall.Yul.blsR))
            (BitVec.ofNat 256 Midfall.Yul.blsR))
          (BitVec.ofNat 256 Midfall.Yul.blsR)) hfe
    rw [hget]
    have hval := pcsM1Value_eq_gen x2v fev
      (wordFrom st.env.calldata (cptr.toNat + setIdx * Midfall.Generator.wordBytes))
      (fun j => loadWord st.memory
        (qep.toNat + (off + j) * Midfall.Generator.wordBytes))
      (m1Dx0 x3v (p 0) (BitVec.ofNat 256 Midfall.Yul.blsR)) a
      hvalDx0 hvalLb0 (by
        simpa [Midfall.Generator.wordBytes] using hev)
    simpa [Nat.add_zero] using congrArg some hval
  · exact Or.inr ⟨ho, hrev⟩



set_option maxHeartbeats 16000000 in
theorem pcsSetBlock_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off scratch hbls gasN selN selP : Nat)
    (p a : Nat → U256) (x3v rv x2v fev cptr qep : U256)
    (hm : 0 < points.length)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hnames : PcsGenNames points.length (pcsPointRefs points distinctRotations)
      (pcsKs points distinctRotations))
    (hainlt : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat < blsR)
    (hain0 : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat ≠ 0)
    (hvalDx : ∀ i, i < points.length → a i = wAddmodAt x3v (rv - p i) rv)
    (hvalLb : ∀ j, j < points.length →
      a (points.length + j) = pcsLbasisVal rv (p j) p (pcsKs points distinctRotations j))
    (hks_sub : ∀ g ∈ pcsPointRefs points distinctRotations,
      ∀ k ∈ pcsKs points distinctRotations g.1, k ∈ pcsPointRefs points distinctRotations)
    (hinv0Dist : ∀ j, 1 ≤ j → j < (pcsBatchInputs points.length).length →
      pcsInvName points.length 0 ≠ pcsInvName points.length j)
    (hinvEvalAll : ∀ i, pcsInvName points.length i ≠ "eval")
    (hinvQSetAll : ∀ i, pcsInvName points.length i ≠ "Q_EVAL_SET_MPTR")
    (hinvR0 : pcsInvName points.length 0 ≠ "r")
    (htermF : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "f_eval")
    (htermX2 : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "x2")
    (hdenInvAll : ∀ i, i < (pcsBatchInputs points.length).length →
      "den_inv" ≠ pcsInvName points.length i)
    (hrv : rv = BitVec.ofNat 256 blsR)
    (hcptr : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqep : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hdisj : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.block (GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off))
      (fun V st =>
        PcsGPre (c := permissive (callsOf product)) (g := g)
          x3v rv x2v fev cptr qep p (pcsPointRefs points distinctRotations)
          (pcsBatchInputs points.length).length V st ∧
        (∀ j, j < points.length → (loadWord st.memory
          (qep.toNat + (off + j) * Midfall.Generator.wordBytes)).toNat < blsR))
      (fun V st V' st' o =>
        PcsGPost (c := permissive (callsOf product)) (g := g)
          rv x2v fev a points.length setIdx cptr.toNat off scratch qep V st V' st' o) := by
  by_cases h1 : 1 < points.length
  · intro V st hpre V' st' o hrun
    exact pcsSetBlock_multi_contract (g := g) (product := product) (funs := funs)
      (decl := decl) (cenv := cenv) (cenv' := cenv')
      setIdx points distinctRotations off scratch hbls gasN selN selP p a
      x3v rv x2v fev cptr qep h1 hlook hbody hparams hrets hnbls hscratch
      hscratch256 hfail hnames hainlt hain0 hvalDx hvalLb hks_sub hinv0Dist
      hinvEvalAll hinvQSetAll hinvR0 htermF htermX2 hdenInvAll hrv hcptr
      hqep hdisj V st hpre.1 V' st' o hrun
  · have hlen : points.length = 1 := by omega
    obtain ⟨p0, hp⟩ := List.length_eq_one_iff.mp hlen
    subst hp
    intro V st hpre V' st' o hrun
    have hvalDx0 : a 0 = wAddmodAt x3v (rv - p 0) rv := hvalDx 0 (by simp)
    have hvalLb0 : a 1 = 1 := by
      have h := hvalLb 0 (by simp)
      simpa [pcsKs, Midfall.Generator.enumIdx, pcsLbasisVal, pcsLbasisAcc,
        Nat.add_zero] using h
    have hdx0pos : 0 < (m1Dx0 x3v (p 0) rv).toNat := by
      have h := hain0 0 (by simp [pcsBatchInputs])
      rw [hvalDx0] at h
      simpa [m1Dx0] using Nat.pos_of_ne_zero h
    have hdx0lt : (m1Dx0 x3v (p 0) rv).toNat < blsR := by
      have h := hainlt 0 (by simp [pcsBatchInputs])
      rw [hvalDx0] at h
      simpa [m1Dx0] using h
    have hpre1 : PcsGPre (c := permissive (callsOf product)) (g := g)
        x3v rv x2v fev cptr qep p
        [(0, pcsRotPtRef distinctRotations p0)] 2 V st ∧
        (loadWord st.memory
          (qep.toNat + off * Midfall.Generator.wordBytes)).toNat < blsR := by
      constructor
      · simpa [pcsPointRefs, Midfall.Generator.enumIdx, pcsBatchInputs] using hpre.1
      · simpa [Nat.add_zero] using hpre.2 0 (by simp)
    have hmain := pcsSetBlock_one_contract_gen (g := g) (product := product)
      (funs := funs) (decl := decl) (cenv := cenv) (cenv' := cenv')
      setIdx p0 distinctRotations off scratch hbls gasN selN selP p a
      x3v rv x2v fev cptr qep hlook hbody hparams hrets hnbls hscratch
      hscratch256 hfail hvalDx0 hvalLb0 hdx0pos hdx0lt hrv hcptr
      (by simpa using hqep) (by simpa using hdisj) V st hpre1 V' st' o hrun
    simpa using hmain


set_option maxHeartbeats 16000000 in
theorem pcsSetBlock_contract_frame {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (setIdx : Nat) (points : List Int) (distinctRotations : List Int)
    (off scratch hbls gasN selN selP : Nat)
    (p a : Nat → U256) (x3v rv x2v fev cptr qep : U256)
    (hm : 0 < points.length)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hnames : PcsGenNames points.length (pcsPointRefs points distinctRotations)
      (pcsKs points distinctRotations))
    (hainlt : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat < blsR)
    (hain0 : ∀ i, i < (pcsBatchInputs points.length).length → (a i).toNat ≠ 0)
    (hvalDx : ∀ i, i < points.length → a i = wAddmodAt x3v (rv - p i) rv)
    (hvalLb : ∀ j, j < points.length →
      a (points.length + j) = pcsLbasisVal rv (p j) p (pcsKs points distinctRotations j))
    (hks_sub : ∀ g ∈ pcsPointRefs points distinctRotations,
      ∀ k ∈ pcsKs points distinctRotations g.1, k ∈ pcsPointRefs points distinctRotations)
    (hinv0Dist : ∀ j, 1 ≤ j → j < (pcsBatchInputs points.length).length →
      pcsInvName points.length 0 ≠ pcsInvName points.length j)
    (hinvEvalAll : ∀ i, pcsInvName points.length i ≠ "eval")
    (hinvQSetAll : ∀ i, pcsInvName points.length i ≠ "Q_EVAL_SET_MPTR")
    (hinvR0 : pcsInvName points.length 0 ≠ "r")
    (htermF : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "f_eval")
    (htermX2 : ∀ j, j < points.length → ("term_" ++ toString j) ≠ "x2")
    (hdenInvAll : ∀ i, i < (pcsBatchInputs points.length).length →
      "den_inv" ≠ pcsInvName points.length i)
    (hrv : rv = BitVec.ofNat 256 blsR)
    (hcptr : cptr.toNat + setIdx * Midfall.Generator.wordBytes < 2 ^ 256)
    (hqep : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes < 2 ^ 256)
    (hdisj : qep.toNat + (off + points.length) * Midfall.Generator.wordBytes ≤ scratch ∨
      scratch + 192 ≤ qep.toNat + off * Midfall.Generator.wordBytes) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.block (GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off))
      (fun V st =>
        PcsGPre (c := permissive (callsOf product)) (g := g)
          x3v rv x2v fev cptr qep p (pcsPointRefs points distinctRotations)
          (pcsBatchInputs points.length).length V st ∧
        (∀ j, j < points.length → (loadWord st.memory
          (qep.toNat + (off + j) * Midfall.Generator.wordBytes)).toNat < blsR))
      (fun V st V' st' o =>
        PcsGPost (c := permissive (callsOf product)) (g := g)
          rv x2v fev a points.length setIdx cptr.toNat off scratch qep V st V' st' o ∧
        (o = .normal →
          (∀ x, x ∉ pcsSetBlockLocalsAll points distinctRotations →
            VEnv.get V' x = VEnv.get V x) ∧
          (∀ y, VEnv.get V y = none → VEnv.get V' y = none))) := by
  apply StmtsContractAll.block
  intro V st hpre V' st' o hrun
  have hblockrun : ExecStmt (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      V st (Stmt.block (GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off))
      (restore V V') st' o := Step.block hrun
  have hcontract := pcsSetBlock_contract (g := g) (product := product) (funs := funs)
    (decl := decl) (cenv := cenv) (cenv' := cenv')
    setIdx points distinctRotations off scratch hbls gasN selN selP p a
    x3v rv x2v fev cptr qep hm hlook hbody hparams hrets hnbls hscratch
    hscratch256 hfail hnames hainlt hain0 hvalDx hvalLb hks_sub hinv0Dist
    hinvEvalAll hinvQSetAll hinvR0 htermF htermX2 hdenInvAll hrv hcptr
    hqep hdisj V st hpre (restore V V') st' o hblockrun
  refine ⟨hcontract, ?_⟩
  intro ho
  by_cases h1 : 1 < points.length
  · have hbodyEq : GenAstPcs.pcsSetBlockAst setIdx points distinctRotations off =
        pcsGenBody setIdx points distinctRotations off := by
      rw [pcsSetBlockAst_eq_gen setIdx points distinctRotations off h1,
        pcsSetBodyGen_eq setIdx points distinctRotations off h1]
    have hhoistGen : hoist (Bridge.Dialect (permissive (callsOf product)) g)
        (pcsGenBody setIdx points distinctRotations off) = [] := by
      unfold hoist
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      rcases pcsGenBody_allLetSet setIdx points distinctRotations off s hs with ⟨x, e, h | h⟩
      · subst s; simp [GenAst.ylet]
      · subst s; simp [GenAst.yset]
    rw [hbodyEq, hhoistGen] at hrun
    have hns : ∀ s ∈ pcsGenBody setIdx points distinctRotations off,
        ∃ x e, s = GenAst.ylet x e ∨ s = GenAst.yset x e :=
      pcsGenBody_allLetSet setIdx points distinctRotations off
    have hloc : ∀ s ∈ pcsGenBody setIdx points distinctRotations off,
        pcsStmtLocal (pcsSetBlockLocalsAll points distinctRotations) s := by
      intro s hs
      exact pcsStmtLocal_mono
        (fun x hx => pcsSetBlockLocals_subset_all points distinctRotations hx)
        (pcsGenBody_pcsStmtLocal_explicit setIdx points distinctRotations off
          (by omega) s hs)
    have hsub : ∀ y ∈ pcsAddedNames (pcsGenBody setIdx points distinctRotations off),
        y ∈ pcsSetBlockLocalsAll points distinctRotations := by
      intro y hy
      exact pcsSetBlockLocals_subset_all points distinctRotations
        (pcsAddedNames_subset_locals setIdx points distinctRotations off (by omega) y hy)
    exact pcs_exec_frame_of_locals (funs := [] :: funs) hns hloc hsub hrun ho
  · have hlen : points.length = 1 := by omega
    obtain ⟨p0, hp⟩ := List.length_eq_one_iff.mp hlen
    subst hp
    have hns : ∀ s ∈ GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off,
        ∃ x e, s = GenAst.ylet x e ∨ s = GenAst.yset x e := by
      intro s hs
      rw [pcsSetBlockAst_one] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact ⟨_, _, Or.inl rfl⟩
      · exact ⟨_, _, Or.inl rfl⟩
      · exact ⟨_, _, Or.inl rfl⟩
      · exact ⟨_, _, Or.inr rfl⟩
    have hloc : ∀ s ∈ GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off,
        pcsStmtLocal (pcsSetBlockLocalsAll [p0] distinctRotations) s := by
      intro s hs
      rw [pcsSetBlockAst_one] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;>
        simp [pcsStmtLocal, GenAst.ylet, GenAst.yset, pcsSetBlockLocalsAll,
          pcsSetBlockLocals]
    have hsub : ∀ y ∈ pcsAddedNames (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off),
        y ∈ pcsSetBlockLocalsAll [p0] distinctRotations := by
      intro y hy
      rw [pcsSetBlockAst_one] at hy
      simp only [pcsAddedNames, pcsLetNames, List.mem_reverse, pcsStmtLetName?,
        GenAst.ylet, GenAst.yset, List.filterMap_cons, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · simp [pcsSetBlockLocalsAll, pcsSetBlockLocals]
      · simp [pcsSetBlockLocalsAll, pcsSetBlockLocals]
      · simp [pcsSetBlockLocalsAll, pcsSetBlockLocals]
    exact pcs_exec_frame_of_locals (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
      (GenAstPcs.pcsSetBlockAst setIdx [p0] distinctRotations off) :: funs)
      hns hloc hsub hrun ho



theorem b1_exec_ylet_lit {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {x : String} {n : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.ylit n)) V' st' o) :
    o = .normal ∧ V' = (x, BitVec.ofNat 256 n) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨hcv, hst⟩ := b2_eval_lit_inv he
      subst hcv; subst hst
      exact ⟨rfl, rfl, rfl⟩
  | letHalt he => exact (by
      cases he with
      )

theorem b1_exec_ylet_mload_add_var {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x p : String} {off : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (GenAst.ylet x (GenAst.yop EVM.Op.mload
        [GenAst.yop EVM.Op.add [GenAst.yvar p, GenAst.ylit off]])) V' st' o) :
    o = .normal ∧ ∃ pv, VEnv.get V p = some pv ∧
      V' = (x, loadWord st.memory (pv + BitVec.ofNat 256 off).toNat) :: V ∧
      st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
  cases h with
  | letVal he hlen =>
      obtain ⟨cv, rfl⟩ := b2_list_length_one hlen
      obtain ⟨pv, hpv, hcv, hst⟩ := b1_eval_mload_add_var_lit_inv he
      subst hcv
      refine ⟨rfl, pv, hpv, rfl, ?_, ?_, ?_⟩
      · rw [hst, Midfall.Yul.Word.touchMemory_memory]
      · rw [hst, Midfall.Yul.Word.touchMemory_env]
      · rw [hst, Midfall.Yul.Word.touchMemory_halted]
  | letHalt he => exact (b1_eval_mload_add_var_lit_halt he).elim


theorem pcsBlock4_header_contract {funs : FunEnv (Bridge.Dialect c g)}
    (x2p x3p cptrp x2v x3v cptr : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [ GenAst.ylet "x2" (GenAst.yop EVM.Op.mload [GenAst.yvar "X2_MPTR"]),
        GenAst.ylet "x3" (GenAst.yop EVM.Op.mload [GenAst.yvar "X3_MPTR"]),
        GenAst.ylet "f_eval" (GenAst.ylit 0),
        GenAst.ylet "Q_EVAL_CPTR" (GenAst.yop EVM.Op.mload [GenAst.yvar "Q_EVAL_CPTR_MPTR"]) ]
      (fun V st => VEnv.get V "X2_MPTR" = some x2p ∧
        VEnv.get V "X3_MPTR" = some x3p ∧
        VEnv.get V "Q_EVAL_CPTR_MPTR" = some cptrp ∧
        loadWord st.memory x2p.toNat = x2v ∧
        loadWord st.memory x3p.toNat = x3v ∧
        loadWord st.memory cptrp.toNat = cptr)
      (fun V st V' st' o => o = .normal ∧
        V' = ("Q_EVAL_CPTR", cptr) :: ("f_eval", 0) :: ("x3", x3v) :: ("x2", x2v) :: V ∧
        st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hx2, hx3, hcp, hv2, hv3, hvc⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨_, p1, hp1, hV1, hst1⟩ :=
      b1_exec_ylet_mload_var (x := "x2") (p := "X2_MPTR") h1
    rw [hx2] at hp1
    have hp1' : p1 = x2p := (Option.some.inj hp1).symm
    rw [hp1'] at hV1
    rw [hst1] at hrest1
    have hm1 : (touchMemory st x2p.toNat 32).memory = st.memory := by
      rw [Midfall.Yul.Word.touchMemory_memory]
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨_, p2, hp2, hV2, hst2⟩ :=
        b1_exec_ylet_mload_var (x := "x3") (p := "X3_MPTR") h2
      rw [hV1] at hp2
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x2") (y := "X3_MPTR") (by decide)] at hp2
      rw [hx3] at hp2
      have hp2' : p2 = x3p := (Option.some.inj hp2).symm
      rw [hp2'] at hV2
      rw [hst2] at hrest2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · obtain ⟨_, hV3, hst3⟩ := b1_exec_ylet_lit (x := "f_eval") (n := 0) h3
        rw [hV2] at hV3
        rw [hst3] at hrest3
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · obtain ⟨_, p4, hp4, hV4, hst4⟩ :=
            b1_exec_ylet_mload_var (x := "Q_EVAL_CPTR") (p := "Q_EVAL_CPTR_MPTR") h4
          rw [hV3] at hp4
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "f_eval") (y := "Q_EVAL_CPTR_MPTR") (by decide)] at hp4
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x3") (y := "Q_EVAL_CPTR_MPTR") (by decide)] at hp4
          rw [hV1] at hp4
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x2") (y := "Q_EVAL_CPTR_MPTR") (by decide)] at hp4
          rw [hcp] at hp4
          have hp4' : p4 = cptrp := (Option.some.inj hp4).symm
          rw [hp4'] at hV4
          subst p1
          subst p2
          subst p4
          have hm2 : (touchMemory (touchMemory st x2p.toNat 32) x3p.toNat 32).memory = st.memory := by
            rw [Midfall.Yul.Word.touchMemory_memory, Midfall.Yul.Word.touchMemory_memory]
          cases hrest4
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · rw [hV4, hV3, hV1]
            simp [hm1, hm2, hv2, hv3, hvc]
          · simp [hst4, hst3, hst2, hst1, Midfall.Yul.Word.touchMemory_memory]
          · simp [hst4, hst3, hst2, hst1, Midfall.Yul.Word.touchMemory_env]
          · simp [hst4, hst3, hst2, hst1, Midfall.Yul.Word.touchMemory_halted]
        · exact absurd (b1_exec_ylet_mload_var h4).1 hne4
      · exact absurd (b1_exec_ylet_lit h3).1 hne3
    · exact absurd (b1_exec_ylet_mload_var h2).1 hne2
  · exact absurd (b1_exec_ylet_mload_var h1).1 hne1


def pcsBlock4ASet (rv x3v : U256) (pointSets : List (List Int)) (distinct : List Int)
    (pSet : Nat → Nat → U256) (s i : Nat) : U256 :=
  pcsGenBatchVal rv x3v (pSet s) (pcsKs (pointSets.getD s []) distinct)
    (pointSets.getD s []).length i

def pcsBlock4Fold (rv x2v x3v : U256) (cval : Nat → U256) (ev : Nat → Nat → U256)
    (pointSets : List (List Int)) (distinct : List Int) (pSet : Nat → Nat → U256) :
    Nat → U256 → U256
  | 0, fev => fev
  | k + 1, fev =>
      let points := pointSets.getD k []
      pcsBlock4Fold rv x2v x3v cval ev pointSets distinct pSet k
        (pcsGenFEval rv x2v fev (cval k) (ev k)
          (pcsBlock4ASet rv x3v pointSets distinct pSet k) points.length)

structure PcsBlock4WalkEnv (x3v rv x2v cptr qep fp : U256)
    (pointSets : List (List Int)) (distinct : List Int) (pSet : Nat → Nat → U256)
    (k : Nat) (V : VEnv (Bridge.Dialect c g)) : Prop where
  x3 : VEnv.get V "x3" = some x3v
  r : VEnv.get V "r" = some rv
  x2 : VEnv.get V "x2" = some x2v
  cptr : VEnv.get V "Q_EVAL_CPTR" = some cptr
  qep : VEnv.get V "Q_EVAL_SET_MPTR" = some qep
  fp : VEnv.get V "F_EVAL_MPTR" = some fp
  rot : ∀ s, s < k → ∀ q ∈ pcsPointRefs (pointSets.getD s []) distinct,
    VEnv.get V q.2 = some (pSet s q.1)
  bpNone : ∀ s, s < k → ∀ i, i < (pcsBatchInputs (pointSets.getD s []).length).length →
    VEnv.get V (pcsBpName i) = none
  lbNone : ∀ s, s < k → ∀ q ∈ pcsPointRefs (pointSets.getD s []) distinct,
    VEnv.get V (pcsLbasisName q.1) = none

structure PcsBlock4WalkPre (scratch : Nat) (qep : U256)
    (pointSets : List (List Int)) (x3v rv x2v cptr fp : U256)
    (distinct : List Int) (pSet : Nat → Nat → U256)
    (k : Nat) (fev : U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop where
  env : PcsBlock4WalkEnv x3v rv x2v cptr qep fp pointSets distinct pSet k V
  fev : VEnv.get V "f_eval" = some fev
  canon : PcsQEvalCanon qep pointSets st
  mem : MemSameOutside st0 st scratch 192
  stateEnv : st.env = st0.env

def PcsBlock4WalkPost (scratch : Nat) (qep : U256) (pointSets : List (List Int))
    (x3v rv x2v cptr fp : U256) (distinct : List Int) (pSet : Nat → Nat → U256)
    (k : Nat) (fev : U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  (o = .normal ∧
    VEnv.get V' "f_eval" =
      some (pcsBlock4Fold rv x2v x3v
        (fun s => wordFrom st0.env.calldata
          (cptr.toNat + s * Midfall.Generator.wordBytes))
        (fun s j => loadWord st0.memory
          (qep.toNat + (pcsSetOff pointSets s + j) * Midfall.Generator.wordBytes))
        pointSets distinct pSet k fev) ∧
    PcsBlock4WalkEnv x3v rv x2v cptr qep fp pointSets distinct pSet 0 V' ∧
    MemSameOutside st0 st' scratch 192 ∧ st'.env = st0.env) ∨
  (o = .halt ∧ Midfall.LoweringV2.Reverted st')


structure PcsBlock4SetFacts (rv x2v x3v cptr qep : U256) (scratch : Nat)
    (pointSets : List (List Int)) (distinct : List Int) (pSet : Nat → Nat → U256) : Prop where
  hm : ∀ s, s < pointSets.length → 0 < (pointSets.getD s []).length
  names : ∀ s, s < pointSets.length →
    PcsGenNames (pointSets.getD s []).length
      (pcsPointRefs (pointSets.getD s []) distinct)
      (pcsKs (pointSets.getD s []) distinct)
  aLt : ∀ s, s < pointSets.length →
    ∀ i, i < (pcsBatchInputs (pointSets.getD s []).length).length →
      (pcsBlock4ASet rv x3v pointSets distinct pSet s i).toNat < blsR
  aNe : ∀ s, s < pointSets.length →
    ∀ i, i < (pcsBatchInputs (pointSets.getD s []).length).length →
      (pcsBlock4ASet rv x3v pointSets distinct pSet s i).toNat ≠ 0
  valDx : ∀ s, s < pointSets.length →
    ∀ i, i < (pointSets.getD s []).length →
      pcsBlock4ASet rv x3v pointSets distinct pSet s i =
        wAddmodAt x3v (rv - pSet s i) rv
  valLb : ∀ s, s < pointSets.length →
    ∀ j, j < (pointSets.getD s []).length →
      pcsBlock4ASet rv x3v pointSets distinct pSet s
        ((pointSets.getD s []).length + j) =
        pcsLbasisVal rv (pSet s j) (pSet s)
          (pcsKs (pointSets.getD s []) distinct j)
  ksSub : ∀ s, s < pointSets.length →
    ∀ gk ∈ pcsPointRefs (pointSets.getD s []) distinct,
      ∀ kk ∈ pcsKs (pointSets.getD s []) distinct gk.1,
        kk ∈ pcsPointRefs (pointSets.getD s []) distinct
  inv0Dist : ∀ s, s < pointSets.length →
    ∀ j, 1 ≤ j → j < (pcsBatchInputs (pointSets.getD s []).length).length →
      pcsInvName (pointSets.getD s []).length 0 ≠
        pcsInvName (pointSets.getD s []).length j
  invEvalAll : ∀ s, s < pointSets.length →
    ∀ i, pcsInvName (pointSets.getD s []).length i ≠ "eval"
  invQSetAll : ∀ s, s < pointSets.length →
    ∀ i, pcsInvName (pointSets.getD s []).length i ≠ "Q_EVAL_SET_MPTR"
  invR0 : ∀ s, s < pointSets.length →
    pcsInvName (pointSets.getD s []).length 0 ≠ "r"
  termF : ∀ s, s < pointSets.length →
    ∀ j, j < (pointSets.getD s []).length → ("term_" ++ toString j) ≠ "f_eval"
  termX2 : ∀ s, s < pointSets.length →
    ∀ j, j < (pointSets.getD s []).length → ("term_" ++ toString j) ≠ "x2"
  denInvAll : ∀ s, s < pointSets.length →
    ∀ i, i < (pcsBatchInputs (pointSets.getD s []).length).length →
      "den_inv" ≠ pcsInvName (pointSets.getD s []).length i
  cptrLt : ∀ s, s < pointSets.length →
    cptr.toNat + s * Midfall.Generator.wordBytes < 2 ^ 256
  qepLt : ∀ s, s < pointSets.length →
    qep.toNat + (pcsSetOff pointSets s + (pointSets.getD s []).length) *
      Midfall.Generator.wordBytes < 2 ^ 256
  disj : ∀ s, s < pointSets.length →
    qep.toNat + (pcsSetOff pointSets s + (pointSets.getD s []).length) *
      Midfall.Generator.wordBytes ≤ scratch ∨
    scratch + 192 ≤ qep.toNat + pcsSetOff pointSets s * Midfall.Generator.wordBytes
  rotLocal : ∀ s, s < pointSets.length → ∀ t, t < pointSets.length →
    ∀ q ∈ pcsPointRefs (pointSets.getD t []) distinct,
      q.2 ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct
  x3Local : ∀ s, s < pointSets.length →
    "x3" ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct
  rLocal : ∀ s, s < pointSets.length →
    "r" ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct
  x2Local : ∀ s, s < pointSets.length →
    "x2" ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct
  cptrLocal : ∀ s, s < pointSets.length →
    "Q_EVAL_CPTR" ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct
  qepLocal : ∀ s, s < pointSets.length →
    "Q_EVAL_SET_MPTR" ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct
  fpLocal : ∀ s, s < pointSets.length →
    "F_EVAL_MPTR" ∉ pcsSetBlockLocalsAll (pointSets.getD s []) distinct

set_option maxHeartbeats 16000000 in
theorem pcsBlock4_walk_contract {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (pointSets : List (List Int)) (distinct : List Int) (pSet : Nat → Nat → U256)
    (rv x2v x3v cptr qep fp : U256) (scratch hbls gasN selN selP : Nat)
    (st0 : EvmState) (k : Nat) (fev : U256)
    (hk : k ≤ pointSets.length)
    (hfacts : PcsBlock4SetFacts rv x2v x3v cptr qep scratch pointSets distinct pSet)
    (hlook : lookupFun funs "scalar_inv" = some (decl, cenv))
    (hbody : decl.body = scalarBodyLit scratch hbls gasN selN selP)
    (hparams : decl.params = ["x"])
    (hrets : decl.rets = ["inv"])
    (hnbls : BitVec.ofNat 256 hbls = BitVec.ofNat 256 Midfall.Yul.blsR)
    (hscratch : (sv scratch).toNat + 192 < 2 ^ 256)
    (hscratch256 : scratch < 2 ^ 256)
    (hfail : lookupFun cenv "fail" = some
      ((failFDecl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)), cenv'))
    (hrv : rv = BitVec.ofNat 256 blsR) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (((List.range k).reverse).flatMap fun s =>
        [Stmt.block (GenAstPcs.pcsSetBlockAst s (pointSets.getD s []) distinct
          (pcsSetOff pointSets s))])
      (PcsBlock4WalkPre (c := permissive (callsOf product)) (g := g)
        scratch qep pointSets x3v rv x2v cptr fp distinct pSet k fev st0)
      (PcsBlock4WalkPost (c := permissive (callsOf product)) (g := g)
        scratch qep pointSets x3v rv x2v cptr fp distinct pSet k fev st0) := by
  induction k generalizing fev with
  | zero =>
      intro V st hpre V' st' o hrun
      cases hrun
      exact Or.inl ⟨rfl, hpre.fev, hpre.env, hpre.mem, hpre.stateEnv⟩
  | succ k ih =>
      let points := pointSets.getD k []
      let off := pcsSetOff pointSets k
      let aSet := pcsBlock4ASet rv x3v pointSets distinct pSet k
      let cval0 : Nat → U256 := fun s => wordFrom st0.env.calldata
        (cptr.toNat + s * Midfall.Generator.wordBytes)
      let ev0 : Nat → Nat → U256 := fun s j => loadWord st0.memory
        (qep.toNat + (pcsSetOff pointSets s + j) * Midfall.Generator.wordBytes)
      let setFev := pcsGenFEval rv x2v fev (cval0 k) (ev0 k) aSet points.length
      have hAST : (((List.range (k + 1)).reverse).flatMap fun s =>
          [Stmt.block (GenAstPcs.pcsSetBlockAst s (pointSets.getD s []) distinct
            (pcsSetOff pointSets s))]) =
          [Stmt.block (GenAstPcs.pcsSetBlockAst k points distinct off)] ++
          (((List.range k).reverse).flatMap fun s =>
            [Stmt.block (GenAstPcs.pcsSetBlockAst s (pointSets.getD s []) distinct
              (pcsSetOff pointSets s))]) := by
        rw [List.range_succ, List.reverse_append, List.reverse_singleton]
        simp only [List.singleton_append, List.flatMap_cons]
        rfl
      rw [hAST]
      refine StmtsContractAll.append
        (mid := PcsBlock4WalkPre (c := permissive (callsOf product)) (g := g)
          scratch qep pointSets x3v rv x2v cptr fp distinct pSet k setFev st0) ?h1 ?h2
      · -- head
        intro V st hpre V' st' o hrun
        have hklt : k < pointSets.length := by omega
        have hmpos : 0 < points.length := hfacts.hm k hklt
        have hg : PcsGPre (c := permissive (callsOf product)) (g := g)
            x3v rv x2v fev cptr qep (pSet k) (pcsPointRefs points distinct)
            (pcsBatchInputs points.length).length V st := by
          refine ⟨hpre.env.x3, hpre.env.r, hpre.env.x2, hpre.fev, hpre.env.cptr,
            hpre.env.qep, ?_, ?_, ?_⟩
          · intro q hq
            exact hpre.env.rot k (by omega) q hq
          · intro i hi
            exact hpre.env.bpNone k (by omega) i hi
          · intro q hq
            exact hpre.env.lbNone k (by omega) q hq
        have hcanonSet : ∀ j, j < points.length →
            (loadWord st.memory
              (qep.toNat + (off + j) * Midfall.Generator.wordBytes)).toNat < blsR := by
          intro j hj
          simpa [off, points] using hpre.canon k hklt j hj
        have hset := pcsSetBlock_contract_frame (g := g) (product := product)
          (funs := funs) (decl := decl) (cenv := cenv) (cenv' := cenv')
          k points distinct off scratch hbls gasN selN selP (pSet k) aSet
          x3v rv x2v fev cptr qep hmpos hlook hbody hparams hrets hnbls hscratch
          hscratch256 hfail (hfacts.names k hklt) (hfacts.aLt k hklt)
          (hfacts.aNe k hklt) (hfacts.valDx k hklt) (hfacts.valLb k hklt)
          (hfacts.ksSub k hklt) (hfacts.inv0Dist k hklt)
          (fun i => hfacts.invEvalAll k hklt i) (fun i => hfacts.invQSetAll k hklt i)
          (hfacts.invR0 k hklt) (hfacts.termF k hklt) (hfacts.termX2 k hklt)
          (hfacts.denInvAll k hklt) hrv (hfacts.cptrLt k hklt)
          (by simpa [off, points] using hfacts.qepLt k hklt)
          (by simpa [off, points] using hfacts.disj k hklt)
          V st ⟨hg, hcanonSet⟩ V' st' o (b1_stmt_of_singleton hrun)
        obtain ⟨hpost, hframe⟩ := hset
        rcases hpost with ⟨ho, hfget, hfr, henv⟩ | ⟨ho, hrev⟩
        · left
          refine ⟨ho, ?_⟩
          have hloadEq : ∀ j, j < points.length →
              loadWord st.memory
                (qep.toNat + (off + j) * Midfall.Generator.wordBytes) =
              loadWord st0.memory
                (qep.toNat + (off + j) * Midfall.Generator.wordBytes) := by
            intro j hj
            apply loadWord_eq_of_memSameOutside hpre.mem
            dsimp only [off, points] at *
            rcases hfacts.disj k hklt with h | h
            · left
              have hoff : (pcsSetOff pointSets k + j) * 32 + 32 ≤
                  (pcsSetOff pointSets k + (pointSets.getD k []).length) * 32 := by
                calc
                  (pcsSetOff pointSets k + j) * 32 + 32 =
                      (pcsSetOff pointSets k + j + 1) * 32 := by ring
                  _ ≤ (pcsSetOff pointSets k + (pointSets.getD k []).length) * 32 :=
                    Nat.mul_le_mul_right 32 (by omega)
              calc
                qep.toNat + (pcsSetOff pointSets k + j) * 32 + 32
                    = qep.toNat + ((pcsSetOff pointSets k + j) * 32 + 32) := by ring
                _ ≤ qep.toNat + (pcsSetOff pointSets k + (pointSets.getD k []).length) * 32 :=
                  Nat.add_le_add_left hoff _
                _ ≤ scratch := h
            · right
              have hle : pcsSetOff pointSets k * 32 ≤
                  (pcsSetOff pointSets k + j) * 32 :=
                Nat.mul_le_mul_right 32 (by omega)
              exact le_trans h (Nat.add_le_add_left hle qep.toNat)
          have hFE : pcsGenFEval rv x2v fev
              (wordFrom st.env.calldata
                (cptr.toNat + k * Midfall.Generator.wordBytes))
              (fun j => loadWord st.memory
                (qep.toNat + (off + j) * Midfall.Generator.wordBytes)) aSet points.length =
              pcsGenFEval rv x2v fev (cval0 k) (ev0 k) aSet points.length := by
            unfold pcsGenFEval
            rw [hpre.stateEnv]
            congr 1
            exact pcsEvalAcc_congr rv
              (fun j => loadWord st.memory
                (qep.toNat + (off + j) * Midfall.Generator.wordBytes))
              (ev0 k) (fun j => SIInv (aSet j)) (fun j => SIInv (aSet (points.length + j)))
              points.length (fun j hj => hloadEq j hj) points.length le_rfl _
          have henv' : st'.env = st0.env := by rw [henv, hpre.stateEnv]
          have hframe1 := (hframe ho).1
          have hframe2 := (hframe ho).2
          have hcanon' : PcsQEvalCanon qep pointSets st' := by
            intro s hs j hj
            rw [loadWord_eq_of_memSameOutside hfr ?_]
            · exact hpre.canon s hs j hj
            · rcases hfacts.disj s hs with h | h
              · left
                have hoff : (pcsSetOff pointSets s + j) * 32 + 32 ≤
                    (pcsSetOff pointSets s + (pointSets.getD s []).length) * 32 := by
                  calc
                    (pcsSetOff pointSets s + j) * 32 + 32 =
                        (pcsSetOff pointSets s + j + 1) * 32 := by ring
                    _ ≤ (pcsSetOff pointSets s + (pointSets.getD s []).length) * 32 :=
                      Nat.mul_le_mul_right 32 (by omega)
                calc
                  qep.toNat + (pcsSetOff pointSets s + j) * 32 + 32
                      = qep.toNat + ((pcsSetOff pointSets s + j) * 32 + 32) := by ring
                  _ ≤ qep.toNat + (pcsSetOff pointSets s + (pointSets.getD s []).length) * 32 :=
                    Nat.add_le_add_left hoff _
                  _ ≤ scratch := h
              · right
                have hle : pcsSetOff pointSets s * 32 ≤
                    (pcsSetOff pointSets s + j) * 32 :=
                  Nat.mul_le_mul_right 32 (by omega)
                exact le_trans h (Nat.add_le_add_left hle qep.toNat)
          refine ⟨?_, ?_, hcanon', pcsMemSameOutside_trans hpre.mem hfr, henv'⟩
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hframe1 "x3" (hfacts.x3Local k hklt)]; exact hpre.env.x3
            · rw [hframe1 "r" (hfacts.rLocal k hklt)]; exact hpre.env.r
            · rw [hframe1 "x2" (hfacts.x2Local k hklt)]; exact hpre.env.x2
            · rw [hframe1 "Q_EVAL_CPTR" (hfacts.cptrLocal k hklt)]; exact hpre.env.cptr
            · rw [hframe1 "Q_EVAL_SET_MPTR" (hfacts.qepLocal k hklt)]; exact hpre.env.qep
            · rw [hframe1 "F_EVAL_MPTR" (hfacts.fpLocal k hklt)]; exact hpre.env.fp
            · intro s hs q hq
              rw [hframe1 q.2 (hfacts.rotLocal k (by omega) s (by omega) q hq)]
              exact hpre.env.rot s (by omega) q hq
            · intro s hs i hi
              rw [hframe2 (pcsBpName i) (hpre.env.bpNone s (by omega) i hi)]
            · intro s hs q hq
              rw [hframe2 (pcsLbasisName q.1) (hpre.env.lbNone s (by omega) q hq)]
          · rw [hfget, hFE]
        · right
          refine ⟨?_, Or.inr ⟨ho, hrev⟩⟩
          rw [ho]; decide
      · -- tail
        have ih' := ih setFev (by omega)
        intro V st _hpre V' st' hmid V'' st'' o hrun
        have htail := ih' V' st' hmid V'' st'' o hrun
        simpa [PcsBlock4WalkPost, pcsBlock4Fold, points, off, aSet, cval0, ev0, setFev, List.getD_eq_getElem?_getD] using htail


end Midfall.LoweringV3.PcsBlock4

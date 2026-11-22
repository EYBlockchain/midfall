-- |
-- Midfall.LoweringV3.ModexpGeneral
--
-- The MEMORY-LEVEL half of the modexp bridge for `batch_invert_summary` (HLP.1.c): the 32-byte
-- store/read frame is A9's `PcsRows.readBytes_storeWord_32`; here are the two fold facts that turn
-- the six stored words into the precompile's frame values, and the `bytesToNatBE`/`loadWord`
-- equality the staticcall step needs.
import Midfall.LoweringV3.PcsRows
import Midfall.LoweringV3.BatchInvert
import Midfall.LoweringV3.ScalarInv
import Midfall.Assumptions.Eip2537

set_option autoImplicit false

open Midfall Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3.QuotientRows Midfall.LoweringV3.LagrangeRows
open Midfall.LoweringV3.BatchInvert Midfall.LoweringV3.PcsRows

namespace Midfall.LoweringV3.ModexpGeneral

theorem shift_or_toNat {acc : U256} {b : UInt8} (h : acc.toNat < 2 ^ 248) :
    ((acc <<< 8) ||| BitVec.ofNat 256 b.toNat).toNat = acc.toNat * 256 + b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  have hshift : (acc <<< 8).toNat = acc.toNat * 256 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hor : (acc.toNat * 256) ||| b.toNat = acc.toNat * 256 + b.toNat := by
    rw [show acc.toNat * 256 = acc.toNat <<< 8 from by rw [Nat.shiftLeft_eq]]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (b := b.toNat) (by omega) acc.toNat,
      Nat.shiftLeft_eq]
  rw [BitVec.toNat_or, hshift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hor

theorem foldl_shift_or_toNat (l : List UInt8) (acc : U256)
    (hl : l.length ≤ 32) (h : acc.toNat < 256 ^ (32 - l.length)) :
    (l.foldl (fun (acc : U256) (b : UInt8) => (acc <<< 8) ||| BitVec.ofNat 256 b.toNat) acc).toNat =
      l.foldl (fun (acc : Nat) (b : UInt8) => acc * 256 + b.toNat) acc.toNat := by
  induction l generalizing acc with
  | nil => rfl
  | cons b t ih =>
      simp only [List.foldl_cons]
      have hlen : (b :: t).length = t.length + 1 := rfl
      rw [hlen] at h
      have hlen2 : t.length ≤ 31 := by simp at hl; omega
      have hexp : 32 - (t.length + 1) = 31 - t.length := by omega
      rw [hexp] at h
      have h248 : acc.toNat < 2 ^ 248 := by
        have hle : (256 : Nat) ^ (31 - t.length) ≤ 2 ^ 248 := by
          rw [show (2 : Nat) ^ 248 = 256 ^ 31 from by
            rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hstep : ((acc <<< 8) ||| BitVec.ofNat 256 b.toNat).toNat < 256 ^ (32 - t.length) := by
        rw [shift_or_toNat h248]
        have hb : b.toNat < 256 := b.toNat_lt
        have hacc : acc.toNat + 1 ≤ (256 : Nat) ^ (31 - t.length) := by omega
        calc acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
          _ ≤ (256 : Nat) ^ (31 - t.length) * 256 := Nat.mul_le_mul_right 256 hacc
          _ = (256 : Nat) ^ (32 - t.length) := by
            rw [show 32 - t.length = (31 - t.length) + 1 by omega, Nat.pow_succ]
      rw [show acc.toNat * 256 + b.toNat = ((acc <<< 8) ||| BitVec.ofNat 256 b.toNat).toNat
        from (shift_or_toNat h248).symm]
      exact ih (acc := (acc <<< 8) ||| BitVec.ofNat 256 b.toNat) (by omega) hstep


theorem bytesToNatBE_readBytes (mem : Nat → UInt8) (p : Nat) :
    bytesToNatBE (ByteArray.mk (readBytes mem p 32).toArray) = (loadWord mem p).toNat := by
  have hlen : (readBytes mem p 32).length = 32 := by simp [readBytes]
  rw [bytesToNatBE_toList]
  show (ByteArray.mk (readBytes mem p 32).toArray).data.toList.foldl
      (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0 = _
  rw [show (ByteArray.mk (readBytes mem p 32).toArray).data.toList = readBytes mem p 32 from rfl]
  have hword : (loadWord mem p).toNat =
      ((readBytes mem p 32).foldl
        (fun (acc : U256) (b : UInt8) => (acc <<< 8) ||| BitVec.ofNat 256 b.toNat) 0).toNat := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hword]
  exact (foldl_shift_or_toNat (readBytes mem p 32) 0 (by omega)
    (by rw [hlen]; norm_num)).symm

theorem readBytes_append (mem : Nat → UInt8) (p n m : Nat) :
    readBytes mem p (n + m) = readBytes mem p n ++ readBytes mem (p + n) m := by
  unfold readBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  show mem (p + (n + x)) = mem (p + n + x)
  rw [Nat.add_assoc]

theorem readBytes_storeWord_disjoint (mem : Nat → UInt8) (p q n : Nat) (v : U256)
    (h : q + n ≤ p ∨ p + 32 ≤ q) :
    readBytes (storeWord mem p v) q n = readBytes mem q n := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  show storeWord mem p v (q + i) = mem (q + i)
  unfold storeWord
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  rcases h with h | h <;> omega

theorem bytesAppend_toList (a b : Bytes) :
    (bytesAppend a b).data.toList = a.data.toList ++ b.data.toList := by
  unfold bytesAppend
  show (ByteArray.mk (a.data ++ b.data)).data.toList = _
  simp


/-! ## The batch frame as `modexpInvFrame` and its honest output -/

/-- The six stores of the batch frame (base `x`, modulus `blsR`) as a `ByteArray` are exactly
`modexpInvFrame x.toNat`: the list equality is A9's `ScalarInv.mxMem_frame`, lifted through
`Array.toArray_toList`/`ByteArray.ext`. -/
theorem mxMem_frame_byteArray (mem : Nat → UInt8) (p : Nat) (x : U256) :
    ByteArray.mk (readBytes (Midfall.LoweringV3.ScalarInv.mxMem mem p x) p 192).toArray =
      modexpInvFrame x.toNat := by
  rw [Midfall.LoweringV3.ScalarInv.mxMem_frame]

theorem mxMem_modexpOutput (mem : Nat → UInt8) (p : Nat) (x : U256)
    (hx0 : 0 < x.toNat) (hx : x.toNat < Midfall.Yul.blsR) :
    modexpOutput (ByteArray.mk (readBytes (Midfall.LoweringV3.ScalarInv.mxMem mem p x) p 192).toArray) =
      some (bytesNatBE ((x.toNat : ZMod Midfall.Yul.blsR)⁻¹).val 32) := by
  rw [mxMem_frame_byteArray]
  exact modexpInv_correct x.toNat hx0 hx



/-! ## The honest modexp answer at address `5` -/

/-- The `honestOf` fold at target `5` picks `modexpRelation`: the three other precompiles'
addresses do not hit. -/
theorem honestOf_modexp_find (product : PairingProduct) (req : YulSemantics.EVM.CallRequest)
    (h : req.target = Midfall.Yul.modexpAddress) :
    List.find? (fun r => Midfall.Yul.Bridge.hits r req)
      (Midfall.Yul.honestRelations product) = some Midfall.Yul.modexpRelation := by
  rw [Midfall.Yul.honestRelations]
  rw [List.find?_cons_of_neg (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.g1AddRelation,
      Midfall.Yul.g1AddAddress, Midfall.Yul.modexpAddress, h])]
  rw [List.find?_cons_of_neg (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.g1MsmRelation,
      Midfall.Yul.g1MsmAddress, Midfall.Yul.modexpAddress, h])]
  rw [List.find?_cons_of_neg (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.pairingRelation,
      Midfall.Yul.pairingAddress, Midfall.Yul.modexpAddress, h])]
  rw [List.find?_cons_of_pos (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.modexpRelation,
      Midfall.Yul.modexpAddress, h])]

/-- **THE HONEST MODEXP RESPONSE**: a successful `callsOf` call at target `5` with a valid input
returns exactly that input's `modexpOutput`. This is the `permissive` success inversion the
staticcall step needs. -/
theorem callsOf_modexp_returndata
    {product : PairingProduct} {req : YulSemantics.EVM.CallRequest}
    {st : EvmState} {resp : CallResponse} {out : Bytes}
    (htarget : req.target = Midfall.Yul.modexpAddress)
    (hvalid : modexpValidInput (ByteArray.mk req.input.toArray) = true)
    (hout : modexpOutput (ByteArray.mk req.input.toArray) = some out)
    (hcall : (callsOf product).Call req st resp) (hsucc : resp.success = true) :
    resp.returndata = out.data.toList := by
  rcases hcall with h | ⟨_, hf⟩
  · unfold honestOf at h
    rw [honestOf_modexp_find product req htarget] at h
    simp only [Midfall.Yul.modexpRelation, ExternalCallRelation.respond, toYulReq,
      hvalid, hout, htarget, Bool.not_true, ite_false, Option.map_some,
      Option.some.injEq] at h
    subst h
    rfl
  · exact absurd hf (by simp)

/-- A successful `modexpOutput` implies the input is within the EIP-7823 limits, i.e. the
precompile accepts it. (`modexpParse?` returns `none` exactly when the limits fail.) -/
theorem modexpValidInput_of_output_some {input : Bytes} {out : Bytes}
    (h : modexpOutput input = some out) : modexpValidInput input = true := by
  by_contra hv
  have hv' : modexpWithinLimits input = false := by
    by_cases hh : modexpWithinLimits input = true
    · exact absurd hh hv
    · cases hc : modexpWithinLimits input <;> simp_all
  unfold modexpOutput at h
  have hparse : modexpParse? input = none := by
    unfold modexpParse?
    rw [if_neg (by rw [hv']; decide)]
  rw [hparse] at h
  cases h



/-! ## The 8-statement staticcall segment, with the inliner's gas lookup explicit -/

/-- The segment 21–28 of the helper body, at EVERY table: the staticcall's gas argument is the
inliner's lookup term `match consts.lookup "MODEXP_GAS" with …`. PROVED by kernel reduction; the
caller rewrites it with `hgas`. -/
theorem bi_staticcall_segment_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 21 8 =
      [ GenAst.yset "ret" (GenAst.yop EVM.Op.staticcall
          [ (match consts.lookup "MODEXP_GAS" with
              | some v => Expr.lit (Literal.number v)
              | none => Expr.var "MODEXP_GAS")
          , GenAst.ylit 5, GenAst.yvar "gp_mptr", GenAst.ylit 192,
            GenAst.yvar "gp_mptr", GenAst.ylit 32 ])
      , GenAst.yset "ret" (GenAst.yop EVM.Op.and
          [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
            [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]])
      , GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"])
      , GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]) [Stmt.leave]
      , GenAst.ylet "all_inv" (GenAst.yop EVM.Op.mload [GenAst.yvar "gp_mptr"])
      , GenAst.ylet "first_mptr" (GenAst.yvar "mptr_start")
      , GenAst.ylet "second_mptr" (GenAst.yop EVM.Op.add [GenAst.yvar "first_mptr", GenAst.ylit 32])
      , GenAst.yset "gp_mptr" (GenAst.yop EVM.Op.sub [GenAst.yvar "gp_mptr", GenAst.ylit 32]) ] := by
  kernel_rfl

theorem readBytes_getD (bs : List UInt8) (h : bs.length = 32) :
    readBytes (fun i => bs.getD i 0) 0 32 = bs := by
  unfold readBytes
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rfl

theorem wordFrom_bytesNatBE (v : Nat) (hv : v < 2 ^ 256) :
    wordFrom (bytesNatBE v 32).data.toList 0 = BitVec.ofNat 256 v := by
  have hlen : (bytesNatBE v 32).data.toList.length = 32 := by
    rw [Array.length_toList, ByteArray.size_data]
    exact Midfall.Assumptions.bytesNatBE_size v 32
  have hread : readBytes (fun i => (bytesNatBE v 32).data.toList.getD i 0) 0 32
      = (bytesNatBE v 32).data.toList := readBytes_getD _ hlen
  have h := bytesToNatBE_readBytes (mem := fun i => (bytesNatBE v 32).data.toList.getD i 0) 0
  rw [hread] at h
  have harr : ByteArray.mk ((bytesNatBE v 32).data.toList.toArray) = bytesNatBE v 32 := by
    rw [Array.toArray_toList]
  rw [harr, bytesToNatBE_bytesNatBE, show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num,
    Nat.mod_eq_of_lt hv] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  show (loadWord (fun i => (bytesNatBE v 32).data.toList.getD i 0) 0).toNat = v
  exact h.symm

theorem loadWord_copyReturn_bytesNatBE (mem : Nat → UInt8) (p : Nat) (v : Nat)
    (hv : v < 2 ^ 256) :
    loadWord (copyReturn mem p 32 (bytesNatBE v 32).data.toList) p = BitVec.ofNat 256 v := by
  have hlen : (bytesNatBE v 32).data.toList.length = 32 := by
    rw [Array.length_toList, ByteArray.size_data]
    exact Midfall.Assumptions.bytesNatBE_size v 32
  rw [Midfall.Yul.Word.loadWord_copyReturn mem p 32 p _ (by
    constructor
    · omega
    · rw [hlen]; omega)]
  rw [show p - p = 0 by omega]
  exact wordFrom_bytesNatBE v hv


/-! ## The staticcall walk's statement inversions (21-28) -/

open Midfall.LoweringV2.Blocks.VkLoading Midfall.LoweringV3.ScalarInv

theorem eval_args_litvar_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (l : List (Expr EVM.Op))
    (hl : ∀ e ∈ l, (∃ n, e = Expr.lit (Literal.number n)) ∨ (∃ x, e = Expr.var x))
    {st' : EvmState} (h : EvalArgs (Bridge.Dialect c g) funs V st l (.halt st')) : False := by
  induction l generalizing st' with
  | nil => cases h
  | cons e rest ih =>
      cases h with
      | argsRestHalt h' =>
          exact ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) h'
      | argsHeadHalt hrest hhead =>
          rcases hl e (by simp) with ⟨n, rfl⟩ | ⟨x, rfl⟩ <;> cases hhead

theorem eval_staticcall_args {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {gas : Nat} {vp : U256} (hgp : VEnv.get V "gp_mptr" = some vp)
    {vs : List U256} {st' : EvmState}
    (h : EvalArgs (Bridge.Dialect c g) funs V st
      [Expr.lit (Literal.number gas), Expr.lit (Literal.number 5), Expr.var "gp_mptr",
       Expr.lit (Literal.number 192), Expr.var "gp_mptr", Expr.lit (Literal.number 32)]
      (.vals vs st')) :
    vs = [BitVec.ofNat 256 gas, BitVec.ofNat 256 5, vp, BitVec.ofNat 256 192, vp,
      BitVec.ofNat 256 32] ∧ st' = st := by
  cases h with
  | argsCons hrest hgas =>
      cases hgas with | lit =>
      cases hrest with
      | argsCons hrest h5 =>
          cases h5 with | lit =>
          cases hrest with
          | argsCons hrest hgp1 =>
              cases hgp1 with
              | var hget =>
                  rw [hgp] at hget
                  injection hget with hvp
                  subst hvp
                  cases hrest with
                  | argsCons hrest h192 =>
                      cases h192 with | lit =>
                      cases hrest with
                      | argsCons hrest hgp2 =>
                          cases hgp2 with
                          | var hget2 =>
                              rw [hgp] at hget2
                              injection hget2 with hvp2
                              subst hvp2
                              cases hrest with
                              | argsCons hrest h32 =>
                                  cases h32 with | lit =>
                                  cases hrest with
                                  | argsNil => exact ⟨rfl, rfl⟩

theorem exec_assign_staticcall_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {gas : Nat} {vp : U256}
    (hgp : VEnv.get V "gp_mptr" = some vp)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["ret"] (Expr.builtin EVM.Op.staticcall
        [Expr.lit (Literal.number gas), Expr.lit (Literal.number 5), Expr.var "gp_mptr",
         Expr.lit (Literal.number 192), Expr.var "gp_mptr", Expr.lit (Literal.number 32)]))
      V' st' o) :
    ∃ resp, o = .normal ∧ c.Call
      { kind := .staticcall, gas := BitVec.ofNat 256 gas, target := BitVec.ofNat 256 5,
        value := 0, input := readBytes st.memory vp.toNat 192 } st resp ∧
      V' = VEnv.set V "ret" resp.flag ∧
      st' = finishCall .staticcall st resp vp.toNat 192 vp.toNat 32 := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv he
      obtain ⟨hvs, hst⟩ := eval_staticcall_args hgp hargs
      subst hvs
      subst hst
      simp only [builtinWithExternal] at hbi
      obtain ⟨resp, hcall, heq⟩ := hbi
      cases heq
      refine ⟨resp, rfl, hcall, ?_, ?_⟩
      · simp [VEnv.setMany]
      · norm_num
  | assignHalt he =>
      cases he with
      | builtinHalt hargs hbi =>
          obtain ⟨hvs, -⟩ := eval_staticcall_args hgp hargs
          subst hvs
          simp only [builtinWithExternal] at hbi
          obtain ⟨resp, hcall, heq⟩ := hbi
          cases heq
      | builtinArgsHalt hargs =>
          exact (eval_args_litvar_no_halt _ (by
            intro e he
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl ⟨gas, rfl⟩
            · exact Or.inl ⟨5, rfl⟩
            · exact Or.inr ⟨"gp_mptr", rfl⟩
            · exact Or.inl ⟨192, rfl⟩
            · exact Or.inr ⟨"gp_mptr", rfl⟩
            · exact Or.inl ⟨32, rfl⟩) hargs).elim


theorem eval_returndatasize_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.returndatasize []) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_nullary (op := .returndatasize)
    (by
      intro st r hr
      simp only [builtinWithExternal, stepOp, rd0] at hr
      cases hr
      exact ⟨_, _, rfl⟩) h

theorem eval_eq32_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.eq [Expr.builtin EVM.Op.returndatasize [],
        Expr.lit (Literal.number 32)]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .eq)
    (by
      intro a b st r hr
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => eval_returndatasize_no_halt hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh)
    h

theorem eval_ret_and_eq32_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.and [Expr.var "ret", Expr.builtin EVM.Op.eq
        [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
      (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .and)
    (by
      intro a b st r hr
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => eval_eq32_no_halt hh)
    h

theorem eval_ret_and_eq32_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    {vals : List U256} {rv : U256}
    (hrv : VEnv.get V "ret" = some rv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.and [Expr.var "ret", Expr.builtin EVM.Op.eq
        [Expr.builtin EVM.Op.returndatasize [], Expr.lit (Literal.number 32)]])
      (.vals vals st')) :
    st' = st ∧
      vals = [rv &&& b2w (BitVec.ofNat 256 st.returndata.length = BitVec.ofNat 256 32)] := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      obtain ⟨hget, rfl⟩ := eval_var_inv hhead
      rw [hrv] at hget
      injection hget with hveq
      subst hveq
      cases hrest with
      | argsCons hnil heq =>
          cases hnil with
          | argsNil =>
              obtain ⟨argvals2, st2, hargs2, hbi2⟩ := eval_builtin_vals_inv heq
              cases hargs2 with
              | argsCons hrest2 hrd =>
                  cases hrest2 with
                  | argsCons hnil hlit =>
                      cases hnil with
                      | argsNil =>
                          obtain ⟨hv32, rfl⟩ := eval_lit_inv hlit
                          subst hv32
                          obtain ⟨argvals0, st0, hargs0, hbi0⟩ := eval_builtin_vals_inv hrd
                          cases hargs0 with
                          | argsNil =>
                              simp only [builtinWithExternal, stepOp, rd0] at hbi0
                              cases hbi0
                              simp only [builtinWithExternal, stepOp, bin] at hbi2
                              cases hbi2
                              simp only [builtinWithExternal, stepOp, bin] at hbi
                              cases hbi
                              exact ⟨rfl, rfl⟩

theorem ret_and_eq32_stmt {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) :
    StmtContractAll (D := Bridge.Dialect c g) funs
      (Stmt.assign ["ret"] (Expr.builtin EVM.Op.and [Expr.var "ret",
        Expr.builtin EVM.Op.eq [Expr.builtin EVM.Op.returndatasize [],
          Expr.lit (Literal.number 32)]]))
      (fun V st => ∃ rv, VEnv.get V "ret" = some rv ∧
        (rv = 0 ∨ (rv = 1 ∧ st.returndata.length = 32)))
      (fun V st V' st' o => o = .normal ∧
        ∃ rv, VEnv.get V "ret" = some rv ∧ V' = VEnv.set V "ret" rv ∧ st' = st) := by
  intro V st hpre V' st' o hrun
  obtain ⟨rv, hrv, hcases⟩ := hpre
  cases hrun with
  | assignVal he hlen =>
      obtain ⟨hst, hvals⟩ := eval_ret_and_eq32_inv hrv he
      subst hst
      have hcv' : rv &&& b2w (BitVec.ofNat 256 st'.returndata.length = BitVec.ofNat 256 32) = rv := by
        rcases hcases with rfl | ⟨rfl, hlen32⟩
        · exact BitVec.zero_and
        · have hlen' : BitVec.ofNat 256 st'.returndata.length = BitVec.ofNat 256 32 := by
            rw [hlen32]
          rw [hlen']
          show (1 : U256) &&& b2w (decide (BitVec.ofNat 256 32 = BitVec.ofNat 256 32)) = 1
          decide
      refine ⟨rfl, rv, hrv, ?_, rfl⟩
      rw [hvals]
      rw [hcv']
      rfl
  | assignHalt he =>
      exact (eval_ret_and_eq32_no_halt he).elim


theorem eval_iszero_ret_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    {vals : List U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero [Expr.var "ret"]) (.vals vals st')) :
    ∃ rv, VEnv.get V "ret" = some rv ∧ st' = st ∧ vals = [b2w (rv = 0)] := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hvar =>
      cases hnil with
      | argsNil =>
          obtain ⟨hrv, rfl⟩ := eval_var_inv hvar
          simp only [builtinWithExternal, stepOp, un] at hbi
          cases hbi
          exact ⟨_, hrv, rfl, rfl⟩

theorem eval_iszero_ret_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero [Expr.var "ret"]) (.halt st')) : False :=
  vk_nh_unary (op := .iszero)
    (by
      intro a st r hr
      simp only [builtinWithExternal, stepOp, un] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => vkVar_ne_halts hh) h

theorem exec_assign_iszero_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {rv : U256}
    (hrv : VEnv.get V "ret" = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["precompile_failed"] (Expr.builtin EVM.Op.iszero [Expr.var "ret"]))
      V' st' o) :
    o = .normal ∧ V' = VEnv.set V "precompile_failed" (b2w (rv = 0)) ∧ st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨cv, hcv, hst, hvals⟩ := eval_iszero_ret_inv he
      rw [hrv] at hcv
      injection hcv with hcveq
      subst hcveq
      subst hst
      refine ⟨rfl, ?_, rfl⟩
      rw [hvals]
      simp only [VEnv.setMany]
      rfl
  | assignHalt he => exact (eval_iszero_ret_no_halt he).elim

theorem exec_assign_iszero_one {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome}
    (hrv : VEnv.get V "ret" = some 1)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["precompile_failed"] (Expr.builtin EVM.Op.iszero [Expr.var "ret"]))
      V' st' o) :
    o = .normal ∧ V' = VEnv.set V "precompile_failed" 0 ∧ st' = st := by
  have h' := exec_assign_iszero_inv (rv := 1) hrv h
  rw [show b2w ((1 : U256) = 0) = 0 from rfl] at h'
  exact h'

theorem exec_assign_iszero_zero {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome}
    (hrv : VEnv.get V "ret" = some 0)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["precompile_failed"] (Expr.builtin EVM.Op.iszero [Expr.var "ret"]))
      V' st' o) :
    o = .normal ∧ V' = VEnv.set V "precompile_failed" 1 ∧ st' = st := by
  have h' := exec_assign_iszero_inv (rv := 0) hrv h
  rw [show b2w ((0 : U256) = 0) = 1 from rfl] at h'
  exact h'

theorem exec_guard_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {rv : U256}
    (hrv : VEnv.get V "ret" = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var "ret"]) [Stmt.leave]) V' st' o) :
    (rv = 1 → o = .normal ∧ V' = V ∧ st' = st) ∧
      (rv = 0 → o = .leave ∧ V' = V ∧ st' = st) := by
  constructor
  · intro hr1
    subst hr1
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨rv, hrv', hst, hcv⟩ := eval_iszero_ret_inv hc
        rw [hrv] at hrv'
        injection hrv' with hveq
        subst hveq
        subst hst
        injection hcv with hcv'; subst hcv'
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨rv, hrv', hst, hcv⟩ := eval_iszero_ret_inv hc
        rw [hrv] at hrv'
        injection hrv' with hveq
        subst hveq
        subst hst
        injection hcv with hcv'; subst hcv'
        exact ⟨rfl, rfl, rfl⟩
    | ifHalt hc => exact (eval_iszero_ret_no_halt hc).elim
  · intro hr0
    subst hr0
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨rv, hrv', hst, hcv⟩ := eval_iszero_ret_inv hc
        rw [hrv] at hrv'
        injection hrv' with hveq
        subst hveq
        subst hst
        injection hcv with hcv'; subst hcv'
        cases hbody with
        | block hb =>
            cases hb with
            | seqCons hleave hrest => cases hleave
            | seqStop hleave hne =>
                cases hleave
                refine ⟨rfl, ?_, rfl⟩
                simp [restore]
    | ifFalse hc hz =>
        obtain ⟨rv, hrv', hst, hcv⟩ := eval_iszero_ret_inv hc
        rw [hrv] at hrv'
        injection hrv' with hveq
        subst hveq
        subst hst
        injection hcv with hcv'; subst hcv'
        exact absurd hz (by decide : ¬ (b2w ((0 : U256) = 0) = (0 : U256)))
    | ifHalt hc => exact (eval_iszero_ret_no_halt hc).elim


theorem eval_sub_var_lit_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {y : String} {k : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.var y, Expr.lit (Literal.number k)]) (.vals [cv] st')) :
    ∃ a, VEnv.get V y = some a ∧ cv = a - BitVec.ofNat 256 k ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil hlit =>
          cases hnil with
          | argsNil =>
              obtain ⟨hk, rfl⟩ := eval_lit_inv hlit
              obtain ⟨ha, rfl⟩ := eval_var_inv hhead
              simp only [builtinWithExternal, stepOp, bin, hk] at hbi
              cases hbi
              exact ⟨_, ha, rfl, rfl⟩

theorem eval_sub_var_lit_no_halt {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {y : String} {k : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.var y, Expr.lit (Literal.number k)]) (.halt st')) : False :=
  vk_nh_binary (op := .sub)
    (by
      intro a b st r hr
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => vkVar_ne_halts hh)
    (fun _ _ hh => vkLit_ne_halts hh) h

theorem exec_let_mload_var_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {x : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.builtin EVM.Op.mload [Expr.var "gp_mptr"]))) V' st' o) :
    ∃ p v, VEnv.get V "gp_mptr" = some p ∧ v = loadWord st.memory p.toNat ∧
      o = .normal ∧ V' = (x, v) :: V ∧ st' = touchMemory st p.toNat 32 := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      obtain ⟨p, hget, hv, hrfl⟩ := eval_mload_var_inv he
      subst hrfl
      refine ⟨p, v, hget, hv, rfl, ?_, rfl⟩
      rfl
  | letHalt he => exact (eval_mload_var_halt_false he).elim

theorem exec_let_var_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {x y : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.var y))) V' st' o) :
    ∃ v, VEnv.get V y = some v ∧ o = .normal ∧ V' = (x, v) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      obtain ⟨hv, rfl⟩ := eval_var_inv he
      exact ⟨v, hv, rfl, rfl, rfl⟩
  | letHalt he => exact (vkVar_ne_halts he).elim

theorem exec_let_add_var_lit_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {x y : String} {k : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.builtin EVM.Op.add
        [Expr.var y, Expr.lit (Literal.number k)]))) V' st' o) :
    ∃ v, VEnv.get V y = some v ∧ o = .normal ∧
      V' = (x, v + BitVec.ofNat 256 k) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      obtain ⟨a, ha, hv, rfl⟩ := eval_add_var_lit_inv he
      exact ⟨a, ha, rfl, congrArg (fun z => (x, z) :: V) hv ▸ rfl, rfl⟩
  | letHalt he =>
      exact (vk_nh_binary (op := .add)
        (by
          intro a b st r hr
          simp only [builtinWithExternal, stepOp, bin] at hr
          cases hr
          exact ⟨_, _, rfl⟩)
        (fun _ _ hh => vkVar_ne_halts hh)
        (fun _ _ hh => vkLit_ne_halts hh) he).elim

theorem exec_assign_sub_var_lit_inv {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {x : String} {k : Nat}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign [x] (Expr.builtin EVM.Op.sub
        [Expr.var x, Expr.lit (Literal.number k)])) V' st' o) :
    ∃ v, VEnv.get V x = some v ∧ o = .normal ∧
      V' = VEnv.set V x (v - BitVec.ofNat 256 k) ∧ st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      obtain ⟨a, ha, hv, rfl⟩ := eval_sub_var_lit_inv he
      subst hv
      exact ⟨a, ha, rfl, rfl, rfl⟩
  | assignHalt he => exact (eval_sub_var_lit_no_halt he).elim


theorem finishCall_staticcall_memory (st : EvmState) (resp : CallResponse)
    (io is oo os : Nat) :
    (finishCall .staticcall st resp io is oo os).memory =
      copyReturn st.memory oo os resp.returndata := rfl

theorem touchMemory_memory (st : EvmState) (p n : Nat) :
    (touchMemory st p n).memory = st.memory := rfl

theorem finishCall_staticcall_env (st : EvmState) (resp : CallResponse)
    (io is oo os : Nat) :
    (finishCall .staticcall st resp io is oo os).env = st.env := by
  simp [finishCall, touchMemory2, touchMemory]

/-- `ofNat a + 32` is `ofNat (a+32)` when the sum fits. -/
theorem ofNat_add_32 (a : Nat) (h : a + 32 < 2 ^ 256) :
    ((BitVec.ofNat 256 a : U256) + BitVec.ofNat 256 32) = BitVec.ofNat 256 (a + 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 256), Nat.mod_eq_of_lt (by omega : a < 2 ^ 256),
    Nat.mod_eq_of_lt h]

/-- `ofNat p - 32` is `ofNat (p-32)` when `p` fits and `32 ≤ p`. -/
theorem ofNat_sub_32 (p : Nat) (hp : p < 2 ^ 256) (hp32 : 32 ≤ p) :
    ((BitVec.ofNat 256 p : U256) - BitVec.ofNat 256 32) = BitVec.ofNat 256 (p - 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 256), Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (by omega : p - 32 < 2 ^ 256)]
  omega

theorem bi_staticcall_tail_lets {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g))
    (M : Nat → UInt8) (p a : Nat) (v : Nat) (hp : p < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [ GenAst.ylet "all_inv" (GenAst.yop EVM.Op.mload [GenAst.yvar "gp_mptr"]),
        GenAst.ylet "first_mptr" (GenAst.yvar "mptr_start"),
        GenAst.ylet "second_mptr" (GenAst.yop EVM.Op.add
          [GenAst.yvar "first_mptr", GenAst.ylit 32]),
        GenAst.yset "gp_mptr" (GenAst.yop EVM.Op.sub
          [GenAst.yvar "gp_mptr", GenAst.ylit 32])]
      (fun V st =>
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        st.memory = M ∧
        loadWord M p = BitVec.ofNat 256 v)
      (fun Vpre st V' st' o => o = .normal ∧
        VEnv.get V' "all_inv" = some (BitVec.ofNat 256 v) ∧
        VEnv.get V' "first_mptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V' "second_mptr" = some (BitVec.ofNat 256 a + 32) ∧
        VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 p - 32) ∧
        VEnv.get V' "mptr_start" = some (BitVec.ofNat 256 a) ∧
        st' = touchMemory st (BitVec.ofNat 256 p).toNat 32 ∧
        V' = VEnv.set (("second_mptr", BitVec.ofNat 256 a + 32) ::
          ("first_mptr", BitVec.ofNat 256 a) :: ("all_inv", BitVec.ofNat 256 v) :: Vpre)
          "gp_mptr" (BitVec.ofNat 256 p - 32)) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hgp, hmstart, hmem, hv⟩ := hpre
  -- s1 mload
  rcases Step.stmts_cons_inv hrun with ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨pp, vv, hgetpp, hvval, ho1, hV1, hst1⟩ :=
      exec_let_mload_var_inv (x := "all_inv") h1
    rw [hgp] at hgetpp
    injection hgetpp with hpp
    subst hpp
    subst hV1
    subst hst1
    rw [hmem] at hvval
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] at hvval
    rw [hv] at hvval
    -- s2 first
    rcases Step.stmts_cons_inv hrest1 with ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨vms, hgetms, ho2, hV2, hst2⟩ :=
        exec_let_var_inv (x := "first_mptr") (y := "mptr_start") h2
      subst hV2
      subst hst2
      rw [Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "mptr_start")
        (by decide)] at hgetms
      rw [hmstart] at hgetms
      injection hgetms with hvms
      have hvms' : vms = BitVec.ofNat 256 a := hvms.symm
      -- s3 second
      rcases Step.stmts_cons_inv hrest2 with ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · obtain ⟨vfm, hgetfm, ho3, hV3, hst3⟩ :=
          exec_let_add_var_lit_inv (x := "second_mptr") (y := "first_mptr") (k := 32) h3
        subst hV3
        subst hst3
        simp [VEnv.get, List.find?] at hgetfm
        have hvfm : vfm = vms := hgetfm.symm
        -- s4 gp_mptr
        rcases Step.stmts_cons_inv hrest3 with ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · obtain ⟨vgp, hgetgp, ho4, hV4, hst4⟩ :=
            exec_assign_sub_var_lit_inv (x := "gp_mptr") (k := 32) h4
          subst hV4
          subst hst4
          cases hrest4
          -- read gp_mptr through the two lets and the ret/pf sets
          rw [Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "second_mptr") (y := "gp_mptr") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "first_mptr") (y := "gp_mptr") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "all_inv") (y := "gp_mptr") (by decide)] at hgetgp
          rw [hgp] at hgetgp
          have hvgp : vgp = BitVec.ofNat 256 p := Option.some.inj hgetgp.symm
          subst hvgp
          have hgetpre : VEnv.get (("second_mptr", vfm + BitVec.ofNat 256 32) ::
                ("first_mptr", vms) :: ("all_inv", vv) :: V) "gp_mptr" =
              some (BitVec.ofNat 256 p) := by
            rw [Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "second_mptr") (y := "gp_mptr") (by decide),
                Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "first_mptr") (y := "gp_mptr") (by decide),
                Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "all_inv") (y := "gp_mptr") (by decide)]
            exact hgp
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
          · -- all_inv
            rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "all_inv") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "second_mptr") (y := "all_inv") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "first_mptr") (y := "all_inv") (by decide)]
            simp [VEnv.get, List.find?]
            rw [hvval]
          · -- first_mptr
            rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "first_mptr") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "second_mptr") (y := "first_mptr") (by decide)]
            simp [VEnv.get, List.find?]
            rw [hvms]
          · -- second_mptr
            rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "second_mptr") (by decide)]
            simp [VEnv.get, List.find?]
            rw [hvfm, hvms]
          · -- gp_mptr
            rw [Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hgetpre]
            rfl
          · -- mptr_start
            rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr_start") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "second_mptr") (y := "mptr_start") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "first_mptr") (y := "mptr_start") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "mptr_start") (by decide)]
            exact hmstart
          · -- exact tail environment
            rw [← hvms', ← hvfm, ← hvval]
            rfl
        · cases h4 with
          | assignVal he hl => exact absurd rfl hne4
          | assignHalt he => exact (eval_sub_var_lit_no_halt he).elim
      · cases h3 with
        | letVal he hl => exact absurd rfl hne3
        | letHalt he =>
            exact (Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .add)
              (by intro a b st r hr
                  simp only [builtinWithExternal, stepOp, bin] at hr
                  cases hr
                  exact ⟨_, _, rfl⟩)
              (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
              (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) he).elim
    · cases h2 with
      | letVal he hl => exact absurd rfl hne2
      | letHalt he => exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts he).elim
  · cases h1 with
    | letVal he hl => exact absurd rfl hne1
    | letHalt he => exact (eval_mload_var_halt_false he).elim


/-- The inverse's value fits in a word. -/
theorem zmod_inv_val_lt (x : U256) : ((x.toNat : ZMod blsR)⁻¹).val < 2 ^ 256 := by
  have hR : blsR < 2 ^ 256 := by decide
  have h := ZMod.val_lt ((x.toNat : ZMod blsR)⁻¹)
  omega

open Midfall.LoweringV3.ScalarInv Midfall.LoweringV2.Blocks.TraceReturn

variable {c : ExternalCalls} {g : ExternalGas}

/-! ## The `scalar_inv` staticcall arm: evaluation, no-halt, and the guard contract -/

theorem eval_staticcall_frame (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st1 : EvmState} {gasv pv a : U256}
    (hgas : VEnv.get V "MODEXP_GAS" = some gasv) (hp : VEnv.get V "p" = some pv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.staticcall
        [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
         Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)])
      (.vals [a] st1)) :
    ∃ resp, c.Call ⟨.staticcall, gasv, 5, 0, readBytes st.memory pv.toNat 192⟩ st resp ∧
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
                    obtain ⟨hv1, hs1⟩ := eval_var_eq funs V "MODEXP_GAS" gasv hgas hhead1
                    rw [hs1, hs2, hs3, hs4, hs5, hs6] at hbi
                    rw [hv1, hv2, hv3, hv4, hv5, hv6] at hbi
                    simp [Bridge.Dialect, builtinWithExternal, externalCall] at hbi
                    rcases hbi with ⟨resp, hcall, hok⟩
                    exact ⟨resp, hcall, hok.1, hok.2⟩
theorem eval_iszero_staticcall_frame (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g))
    {st st1 : EvmState} {gasv pv cv : U256}
    (hgas : VEnv.get V "MODEXP_GAS" = some gasv) (hp : VEnv.get V "p" = some pv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.staticcall
          [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
           Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
      (.vals [cv] st1)) :
    ∃ resp, c.Call ⟨.staticcall, gasv, 5, 0, readBytes st.memory pv.toNat 192⟩ st resp ∧
      cv = b2w (resp.flag = 0) ∧
      st1 = finishCall .staticcall st resp pv.toNat 192 pv.toNat 32 := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsNil =>
              obtain ⟨resp, hcall, hflag, hst⟩ := eval_staticcall_frame funs V hgas hp hhead
              rw [hst] at hbi
              simp [Bridge.Dialect, builtinWithExternal, stepOp, un] at hbi
              refine ⟨resp, hcall, ?_, hbi.2.symm⟩
              rw [← hbi.1, hflag]
              rfl

theorem expr_staticcall_frame_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.staticcall
        [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
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
      | argsHeadHalt _ h' => exact trExprVar_ne_halts h'

theorem expr_iszero_staticcall_frame_ne_halts (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) {st st' : EvmState} :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.staticcall
          [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
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
      | argsHeadHalt _ h' => exact expr_staticcall_frame_ne_halts funs V h'

theorem staticcallGuard_contract (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {cenv : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (xv pv gasv sel : U256)
    (hfail : lookupFun funs "fail" = some (failFDecl, cenv)) :
    StmtContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (Stmt.cond (Expr.builtin EVM.Op.iszero
          [Expr.builtin EVM.Op.staticcall
            [Expr.var "MODEXP_GAS", Expr.lit (Literal.number 5), Expr.var "p",
             Expr.lit (Literal.number 192), Expr.var "p", Expr.lit (Literal.number 32)]])
        [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])])
      (fun V st => VEnv.get V "MODEXP_GAS" = some gasv ∧ VEnv.get V "p" = some pv ∧
        VEnv.get V "ERR_PRECOMPILE_FAILED" = some sel ∧
        VEnv.get V "x" = some xv ∧ 0 < xv.toNat ∧ xv.toNat < Midfall.Yul.blsR ∧
        readBytes st.memory pv.toNat 192 = (modexpInvFrame xv.toNat).data.toList)
      (fun V st V' st' o =>
        (o = .normal ∧ V' = V ∧
          ∃ resp, resp.success = true ∧
            (permissive (callsOf product)).Call
              ⟨.staticcall, gasv, 5, 0, readBytes st.memory pv.toNat 192⟩ st resp ∧
            st' = finishCall .staticcall st resp pv.toNat 192 pv.toNat 32 ∧
            resp.returndata =
              (bytesNatBE ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val 32).data.toList ∧
            loadWord st'.memory pv.toNat =
              BitVec.ofNat 256 ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val)
        ∨ (o = .halt ∧ Midfall.LoweringV2.Reverted st')) := by
  refine StmtContractAll.cond ?_ ?_
  · intro V st cv st₁ hpre heval
    obtain ⟨hgas, hp, hsel, hx, hx0, hxlt, hframe⟩ := hpre
    obtain ⟨resp, hcall, hcv, hst⟩ := eval_iszero_staticcall_frame funs V hgas hp heval
    constructor
    · intro hzero
      by_cases hs : resp.success = true
      · have hc : (callsOf product).Call
            ⟨.staticcall, gasv, 5, 0, readBytes st.memory pv.toNat 192⟩ st resp := by
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
          (req := ⟨.staticcall, gasv, 5, 0, readBytes st.memory pv.toNat 192⟩)
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
              [Stmt.exprStmt (Expr.call "fail" [Expr.var "ERR_PRECOMPILE_FAILED"])] :: funs)
              "fail" = some (failFDecl, cenv) := hfail
          rcases Step.stmts_cons_inv
            (D := Bridge.Dialect (permissive (callsOf product)) g) hb with
              ⟨V1, st1, h1, hrest⟩ | ⟨h1, hne⟩
          · exact absurd (fail_call_reverts hfail' h1).1 (by decide)
          · exact Or.inr (fail_call_reverts hfail' h1)
  · intro V st st₁ hpre heval
    exact absurd heval (expr_iszero_staticcall_frame_ne_halts funs V)


#assert_axioms shift_or_toNat [propext, Classical.choice, Quot.sound]
#assert_axioms foldl_shift_or_toNat [propext, Classical.choice, Quot.sound]
#assert_axioms bytesToNatBE_readBytes [propext, Classical.choice, Quot.sound]
#assert_axioms readBytes_append [propext, Classical.choice, Quot.sound]
#assert_axioms readBytes_storeWord_disjoint [propext, Classical.choice, Quot.sound]
#assert_axioms bytesAppend_toList [propext, Classical.choice, Quot.sound]
theorem readBytes_six (mem : Nat → UInt8) (p : Nat) (w0 w1 w2 w3 w4 w5 : U256) :
    readBytes (storeWord (storeWord (storeWord (storeWord (storeWord (storeWord mem p w0)
      (p + 32) w1) (p + 64) w2) (p + 96) w3) (p + 128) w4) (p + 160) w5) p 192 =
    (bytesNatBE w0.toNat 32).data.toList ++ (bytesNatBE w1.toNat 32).data.toList ++
      (bytesNatBE w2.toNat 32).data.toList ++ (bytesNatBE w3.toNat 32).data.toList ++
      (bytesNatBE w4.toNat 32).data.toList ++ (bytesNatBE w5.toNat 32).data.toList := by
  simp only [show 192 = 32 + 32 + 32 + 32 + 32 + 32 by norm_num, readBytes_append]
  simp only [show p + (32 + 32) = p + 64 by omega,
    show p + (32 + 32 + 32) = p + 96 by omega,
    show p + (32 + 32 + 32 + 32) = p + 128 by omega,
    show p + (32 + 32 + 32 + 32 + 32) = p + 160 by omega]
  rw [readBytes_storeWord_disjoint _ (p + 160) p 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) p 32 w4 (by omega),
    readBytes_storeWord_disjoint _ (p + 96) p 32 w3 (by omega),
    readBytes_storeWord_disjoint _ (p + 64) p 32 w2 (by omega),
    readBytes_storeWord_disjoint _ (p + 32) p 32 w1 (by omega),
    readBytes_storeWord_32 _ p w0,
    readBytes_storeWord_disjoint _ (p + 160) (p + 32) 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) (p + 32) 32 w4 (by omega),
    readBytes_storeWord_disjoint _ (p + 96) (p + 32) 32 w3 (by omega),
    readBytes_storeWord_disjoint _ (p + 64) (p + 32) 32 w2 (by omega),
    readBytes_storeWord_32 _ (p + 32) w1,
    readBytes_storeWord_disjoint _ (p + 160) (p + 64) 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) (p + 64) 32 w4 (by omega),
    readBytes_storeWord_disjoint _ (p + 96) (p + 64) 32 w3 (by omega),
    readBytes_storeWord_32 _ (p + 64) w2,
    readBytes_storeWord_disjoint _ (p + 160) (p + 96) 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) (p + 96) 32 w4 (by omega),
    readBytes_storeWord_32 _ (p + 96) w3,
    readBytes_storeWord_disjoint _ (p + 160) (p + 128) 32 w5 (by omega),
    readBytes_storeWord_32 _ (p + 128) w4,
    readBytes_storeWord_32 _ (p + 160) w5]

#assert_axioms readBytes_six [propext, Classical.choice, Quot.sound]
#assert_axioms mxMem_frame_byteArray [propext, Classical.choice, Quot.sound]
#assert_axioms mxMem_modexpOutput [propext, Classical.choice, Quot.sound]
#assert_axioms honestOf_modexp_find [propext, Classical.choice, Quot.sound]
#assert_axioms callsOf_modexp_returndata [propext, Classical.choice, Quot.sound]
#assert_axioms modexpValidInput_of_output_some [propext, Classical.choice, Quot.sound]
#assert_axioms bi_staticcall_segment_form [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_add_32 [propext, Classical.choice, Quot.sound]
#assert_axioms finishCall_staticcall_memory [propext, Classical.choice, Quot.sound]
#assert_axioms touchMemory_memory [propext, Classical.choice, Quot.sound]
#assert_axioms finishCall_staticcall_env [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_sub_32 [propext, Classical.choice, Quot.sound]
#assert_axioms zmod_inv_val_lt [propext, Classical.choice, Quot.sound]
#assert_axioms bi_staticcall_tail_lets [propext, Classical.choice, Quot.sound]
#assert_axioms eval_args_litvar_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms eval_staticcall_args [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_staticcall_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_returndatasize_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms eval_eq32_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms eval_ret_and_eq32_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms eval_ret_and_eq32_inv [propext, Classical.choice, Quot.sound]
#assert_axioms ret_and_eq32_stmt [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_ret_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_ret_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_iszero_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_iszero_one [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_iszero_zero [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_sub_var_lit_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_sub_var_lit_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_let_mload_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_let_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_let_add_var_lit_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_sub_var_lit_inv [propext, Classical.choice, Quot.sound]
#assert_axioms readBytes_getD [propext, Classical.choice, Quot.sound]
#assert_axioms wordFrom_bytesNatBE [propext, Classical.choice, Quot.sound]
#assert_axioms loadWord_copyReturn_bytesNatBE [propext, Classical.choice, Quot.sound]
#assert_axioms eval_staticcall_frame [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_staticcall_frame [propext, Classical.choice, Quot.sound]
#assert_axioms expr_staticcall_frame_ne_halts [propext, Classical.choice, Quot.sound]
#assert_axioms expr_iszero_staticcall_frame_ne_halts [propext, Classical.choice, Quot.sound]
#assert_axioms staticcallGuard_contract [propext, Classical.choice, Quot.sound]

end Midfall.LoweringV3.ModexpGeneral
